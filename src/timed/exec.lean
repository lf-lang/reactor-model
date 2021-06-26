import timed.basic
import inst.exec.run
import data.seq.seq
open reactor
open reactor.ports
open inst.network

open_locale classical

-- Cf. timed/basic.lean
variables {υ : Type*} [decidable_eq υ]

namespace timed
namespace network

  -- The events contained in the OAPs of the given network, represented as an event-map.
  -- This property is really only sensible for post-instantaneous networks.  
  -- 
  -- Obtaining this map is non-trivial, because each IAP may have multiple OAPs which contain
  -- a tag-value pair for any given tag. Hence the (tag → value) map associated with a given IAP
  -- has to return the value of the OAP with the lowest priority (the OAP that was written to *last*),
  -- where the value for the tag is not `none`.
  noncomputable def new_events (τ : timed.network υ) : event_map υ := 
    λ iap t, ((τ.oaps_for_iap' iap).sort oap_le).mfirst (λ oap, (τ.σ.η.port role.output oap) >>= (λ o, o.map t))

  -- 
  def is_time_step_aux (τ τ' : timed.network υ) (events' : event_map υ) : option tag → Prop 
    | none            := ⊥ 
    | (some next_tag) := 
      τ'.time = next_tag ∧ 
      τ'.events = events' ∧ 
      (∀ p, τ'.σ.port' role.output p = if (τ.σ.port' role.output p).is_some then some none else none) ∧
      (∀ p, τ'.σ.port' role.input  p = if (τ.σ.port' role.input  p).is_some then (tpa.maybe τ'.time (τ'.events p τ'.time)) else none) ∧
      τ'.actions = τ.actions ∧
      τ'.σ ≈ τ.σ ∧ 
      (∀ r, (τ.σ.rtr r).state = (τ'.σ.rtr r).state)

  -- A pair of timed networks is a *time step*, if the latter network is a (pre-instantaneous) version of the former
  -- with a time matching the next
  def is_time_step (τ τ' : timed.network υ) : Prop := 
    is_time_step_aux τ τ' (λ p t, τ.new_events p t <|> τ.events p t) τ.next_tag

  notation τ `→ₜ` τ' := is_time_step τ τ'

  theorem unique_time_step {τ τ₁ τ₂ : timed.network υ} (h₁ : τ →ₜ τ₁) (h₂ : τ →ₜ τ₂) : τ₁ = τ₂ :=
    begin
      simp only [(→ₜ)] at h₁ h₂,
      cases τ.next_tag,
        {
          exfalso,
          unfold is_time_step_aux at h₁,
          exact h₁
        },
        {
          obtain ⟨ht₁, he₁, ⟨ho₁, hi₁, ha₁, ⟨hg₁, hn₁, hq₁⟩, hs₁⟩⟩ := h₁,
          obtain ⟨ht₂, he₂, ⟨ho₂, hi₂, ha₂, ⟨hg₂, hn₂, hq₂⟩, hs₂⟩⟩ := h₂,
          have ht, from eq.trans ht₁ (symm ht₂),
          have he, from eq.trans he₁ (symm he₂),
          {
            ext1,
            {
              ext1, ext1,
              { exact (eq.trans hn₁ (symm hn₂)) },
              { 
                ext1 rtr,
                replace hs₁ := hs₁ rtr, 
                replace hs₂ := hs₂ rtr, 
                obtain ⟨hp₁, hr₁⟩ := hq₁ rtr,
                obtain ⟨hp₂, hr₂⟩ := hq₂ rtr,
                unfold inst.network.port' inst.network.graph.port' reactor.port' at ho₁ ho₂ hi₁ hi₂,
                unfold inst.network.rtr inst.network.graph.rtr at hp₁ hp₂ hr₁ hr₂ hs₁ hs₂ hi₁ hi₂ ho₁ ho₂,          
                ext1,
                  { 
                    apply list.ext,
                    intro prt,
                    rw [ht, he] at hi₁,
                    exact eq.trans (hi₁ ⟨rtr, prt⟩) (symm (hi₂ ⟨rtr, prt⟩))
                  },
                  { 
                    apply list.ext,
                    intro prt,
                    exact eq.trans (ho₁ ⟨rtr, prt⟩) (symm (ho₂ ⟨rtr, prt⟩))
                  },
                  { exact eq.trans (symm hs₁) hs₂ },
                  { exact eq.trans hp₁ (symm hp₂) },
                  { exact eq.trans hr₁ (symm hr₂) }
              },
              { exact (eq.trans hg₁ (symm hg₂)) },
            },
            repeat { assumption },
            { exact eq.trans ha₁ (symm ha₂) }
          }
        }
    end

  -- A pair of timed networks is an *execution step*, if ...
  def is_execution_step : option (timed.network υ) → option (timed.network υ) → Prop 
    | (some τ) none      := τ.next_tag = none
    | none     none      := ⊤
    | none     (some _)  := ⊥
    | (some τ) (some τ') := ∃ τₜ, (τ →ₜ τₜ) ∧ -- τₜ is a time-progressed version of τ
      (τ'.σ = τₜ.σ.run') ∧                   -- τ' must be an executed version of τₜ
      (τ'.time = τₜ.time) ∧                  -- τ' must be at the time of the "next action" (given by τₜ)
      (τ'.events = τₜ.events) ∧              -- τ' must inherit all future events (given by τₜ) [in this case, past events are also inherited]
      (τ'.actions = τₜ.actions)              -- τ' must still have the same actions (action ports and edges) as τ 

  notation τ `→ₑ` τ' := is_execution_step τ τ'

  -- If `τ` and `τ'` form an execution step, and are both non-`none`, then `τ` must have a next tag.
  lemma some_exection_step_next_tag {τ τ' : timed.network υ} (h : (some τ) →ₑ (some τ')) : τ.next_tag ≠ none :=
    begin
      obtain ⟨t, h', _⟩ := h,
      by_cases (τ.next_tag = none),
        { 
          simp only [(→ₜ), h, is_time_step_aux] at h',
          exfalso,
          exact h'
        },
        { simp [h] }
    end

  theorem unique_execution_step {τ τ₁ τ₂ : option (timed.network υ)} (h₁ : τ →ₑ τ₁) (h₂ : τ →ₑ τ₂) : τ₁ = τ₂ :=
    begin
      cases τ; cases τ₁; cases τ₂,
        { refl },
        { exfalso, assumption },
        { exfalso, assumption },
        { exfalso, assumption },
        { refl },
        {
          exfalso,
          have h', from some_exection_step_next_tag h₂,
          simp only [(→ₑ)] at h₁,
          contradiction
        },
        {
          exfalso,
          have h', from some_exection_step_next_tag h₁,
          simp only [(→ₑ)] at h₂,
          contradiction
        },
        {
          apply option.some_inj.mpr,
          obtain ⟨t₁, hs₁, hσ₁, ht₁, he₁, ha₁⟩ := h₁,
          obtain ⟨t₂, hs₂, h₂'⟩ := h₂,
          have hs, from unique_time_step hs₁ hs₂,
          rw ←hs at h₂',
          obtain ⟨hσ₂, ht₂, he₂, ha₂⟩ := h₂',
          ext1 ; transitivity,
            exact hσ₁, exact symm hσ₂,
            exact ht₁, exact symm ht₂,
            exact he₁, exact symm he₂,
            exact ha₁, exact symm ha₂
        }
    end

  @[ext]
  structure execution (τ : timed.network υ) :=
    (steps : seq (timed.network υ))
    (head : steps.head = τ)
    (succ : ∀ i, steps.nth i →ₑ steps.nth (i + 1))

  -- We're explicitly not proving that there exists an algorithm, that produces an execution.
  theorem determinism (τ : timed.network υ) (e e' : execution τ) : e = e' :=
    begin
      ext1,
      apply seq.ext,
      intro n,
      induction n with n' hᵢ,
        { 
          change e.steps.head = e'.steps.head,
          rw [e.head, e'.head]
        },
        { 
          have h, from e.succ n',
          have h', from e'.succ n',
          rw hᵢ at h,
          exact unique_execution_step h h'
        }
    end

end network
end timed