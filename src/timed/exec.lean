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

  def is_action_progression (σ σ' : inst.network (tpa υ)) (events: port.id → tag → option υ) (t : tag) : Prop :=
    sorry
    
  -- The events contained in the OAPs of the given network, represented as an event-function. 
  -- That is, a mapping of IAPs to a function (tag → value).
  -- 
  -- Obtaining this mapping is non-trivial, because each IAP may have multiple OAPs which contain
  -- a tag-value-pair for any given tag. Hence the (tag → value) map associated with a given IAP
  -- has to return the value of the OAP with the highest priority (where the value for the tag is not `none`).
  noncomputable def new_events (τ : timed.network υ) : port.id → tag → option υ := 
    λ iap t, ((τ.oaps_for_iap' iap).sort oap_lt).mfirst (λ oap, (τ.σ.η.port role.output oap) >>= (λ o, o.map t))

  -- A pair of timed networks is a *time step*, if ...
  def is_time_step (τ τ' : timed.network υ) : Prop :=
    match τ.next_tag with
      | none            := ⊥
      | (some next_tag) := 
        let events' := (λ p t, τ.new_events p t <|> τ.events p t) in
          (∃ σ', τ'.σ = σ' ∧ (is_action_progression τ.σ σ' events' next_tag)) ∧ 
          τ'.time = next_tag ∧
          τ'.actions = τ.actions ∧
          τ'.events = events'
    end

  notation t `→ₜ` t' := is_time_step t t'

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

  notation t `→ₑ` t' := is_execution_step t t'

  structure execution (τ : timed.network υ) :=
    (steps : seq (timed.network υ))
    (head : steps.head = τ)
    (succ : ∀ i, steps.nth i →ₑ steps.nth (i + 1))

  -- We're explicitly not proving that there exists an algorithm, that produces an execution.

  theorem determinism (τ : timed.network υ) (e e' : execution τ) : e = e' :=
    sorry -- every step strictly determines its successor

end network
end timed