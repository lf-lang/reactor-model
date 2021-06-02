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

  -- A pair of timed networks is an *action progression*, if the IAPs of the latter network hold the values 
  -- determined by a given set of events and (current) tag, the OAPs are all cleared, and the remaining parts
  -- of the networks are all equal.
  def is_action_progression (σ σ' : inst.network (tpa υ)) (events: port.id → tag → option υ) (t : tag) : Prop :=
    σ'.ids = σ.ids ∧ 
    σ'.edges = σ.edges ∧
    (∀ r, σ.rtr r ≈ₛ σ'.rtr r) ∧
    (∀ p, σ'.port role.output p = none) ∧
    (∀ p, σ'.port role.input  p = tpa.input t (events p t))

  -- If `σ₁` and `σ₂` are action progressions of `σ`, then `σ₁ = σ₂`.
  theorem unique_action_progression 
    (σ σ₁ σ₂ : inst.network (tpa υ)) (events: port.id → tag → option υ) (t : tag) 
    (h₁ : is_action_progression σ σ₁ events t) (h₂ : is_action_progression σ σ₂ events t) : 
    σ₁ = σ₂ :=
    begin
      sorry
    end
    
  -- The events contained in the OAPs of the given network, represented as an event-function. 
  -- That is, a mapping of IAPs to a function (tag → value).
  -- 
  -- Obtaining this mapping is non-trivial, because each IAP may have multiple OAPs which contain
  -- a tag-value-pair for any given tag. Hence the (tag → value) map associated with a given IAP
  -- has to return the value of the OAP with the highest priority (where the value for the tag is not `none`).
  noncomputable def new_events (τ : timed.network υ) : port.id → tag → option υ := 
    λ iap t, ((τ.oaps_for_iap' iap).sort oap_lt).mfirst (λ oap, (τ.σ.η.port role.output oap) >>= (λ o, o.map' t))

  def is_time_step_aux (τ τ' : timed.network υ) : option tag → Prop 
    | none            := ⊥ 
    | (some next_tag) := 
        let events' := (λ p t, τ.new_events p t <|> τ.events p t) in
          (∃ σ', τ'.σ = σ' ∧ (is_action_progression τ.σ σ' events' next_tag)) ∧ 
          τ'.time = next_tag ∧
          τ'.actions = τ.actions ∧
          τ'.events = events'

  -- A pair of timed networks is a *time step*, if ...
  def is_time_step (τ τ' : timed.network υ) : Prop := is_time_step_aux τ τ' τ.next_tag

  notation τ `→ₜ` τ' := is_time_step τ τ'

  theorem unique_time_step {τ τ₁ τ₂ : timed.network υ} (h₁ : τ →ₜ τ₁) (h₂ : τ →ₜ τ₂) : τ₁ = τ₂ :=
    begin
      sorry
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
          have H, from e.succ n',
          rw hᵢ at H,
          exact unique_execution_step H (e'.succ n')
        }
    end

end network
end timed