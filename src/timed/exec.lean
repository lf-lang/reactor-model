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

  -- If a given network (τ) has a next event tag, then its successor (τ') must have that tag as its time, as well as:
  -- * be pre-instantaneous.
  -- * have all OAP-local events (those contained in the OAPs) integrated into its event map.
  -- * have all ports set to the values dictated by that event map.
  def is_time_step_aux (τ τ' : timed.network υ) : option tag → Prop 
    | none            := ⊥ 
    | (some next_tag) := 
      τ'.time = next_tag ∧ 
      τ'.μ = τ.all_events ∧ 
      (∀ p, τ'.σ.port' role.output p = if (τ.σ.port' role.output p).is_some then some none else none) ∧
      (∀ p, τ'.σ.port' role.input  p = if (τ.σ.port' role.input  p).is_some then (tpa.maybe τ'.time (τ'.μ p τ'.time)) else none) ∧
      τ'.actions = τ.actions ∧
      τ'.σ ≈ τ.σ ∧ 
      (∀ r, (τ.σ.rtr r).state = (τ'.σ.rtr r).state)

  -- A pair of timed networks is a *time step*, if the latter network can be derived from the former by advancing its
  -- time to the tag of the next scheduled event. This implies that the properties defined by `is_time_step_aux` 
  -- (cf. its documentation).
  def is_time_step (τ τ' : timed.network υ) : Prop := is_time_step_aux τ τ' τ.next_tag

  notation τ `→ₜ` τ' := is_time_step τ τ'

  -- If there exists a time step from a network, then the successor is uniquely defined.
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
                    exact eq.trans (hi₁ (port.id.mk rtr prt)) (symm (hi₂ (port.id.mk rtr prt)))
                  },
                  { 
                    apply list.ext,
                    intro prt,
                    exact eq.trans (ho₁ (port.id.mk rtr prt)) (symm (ho₂ (port.id.mk rtr prt)))
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

  -- A pair of timed networks is an *execution step*, if the latter network can be derived from the
  -- former network by progressing the former to the next pre-instantaneous network, i.e. progressing its
  -- time (cf. `is_time_step`), and performing instantaneous execution on that network.
  def is_execution_step : option (timed.network υ) → option (timed.network υ) → Prop 
    | (some τ) none      := τ.next_tag = none
    | none     none      := ⊤
    | none     (some _)  := ⊥
    | (some τ) (some τ') := ∃ τₜ, (τ →ₜ τₜ) ∧ -- τₜ is a pre-instantaneous, time-progressed version of τ
      (τ'.σ = τₜ.σ.run') ∧                   -- τ' must be an executed version of τₜ
      (τ'.time = τₜ.time) ∧                  
      (τ'.μ = τₜ.μ) ∧                        
      (τ'.actions = τₜ.actions)              

  notation τ `→ₑ` τ' := is_execution_step τ τ'

  -- If some network `τ` can execute to some other network `τ'`, then `τ` must have a next tag.
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

  -- If there exists an execution step from a network, then the successor is uniquely defined.
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

  -- An execution of a timed network is a sequence of timed networks, where each instance in the
  -- sequence represents a valid "execution step" (cf. `is_execution_step`) from its predecessor.
  -- The sequence must start on the given network (`τ`) and can be non-terminating (if execution
  -- continues indefinitely). If execution does terminate, this is indicated in the sequence by
  -- indefinite `none`s after the last execution step (i.e. timed network).
  -- All networks in the sequence are "post-instantaneous" (cf. `docs/Timed Execution`). 
  -- Hence the initial network is also interpreted as being post-instantaneous.
  @[ext]
  structure execution (τ : timed.network υ) :=
    (steps : seq (timed.network υ))
    (head : steps.head = τ)
    (succ : ∀ i, steps.nth i →ₑ steps.nth (i + 1))

  -- Execution of a timed network is always unique - i.e. there's only one possible sequence of
  -- execution steps.
  -- 
  -- We're explicitly not proving that there exists an algorithm, that produces such an execution.
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