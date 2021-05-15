import timed.basic
import inst.exec.run
import data.seq.seq
open reactor
open reactor.ports
open inst.network

-- Cf. timed/basic.lean
variables {υ : Type*} [decidable_eq υ]

namespace timed
namespace network

  -- Propagates a TPA from its OAP to its IAP, by merging it into the IAP.
  -- In this context propagation implies *consuming* the source value, i.e. setting it to `none` once copied.
  noncomputable def propagate_tpa (σ : inst.network (tpa υ)) (e : action_edge) : inst.network (tpa υ) :=
    (σ.update_port role.input e.iap (tpa.merge (σ.η.port role.input e.iap) (σ.η.port role.output e.oap)))
    .update_port role.output e.oap none

  -- Propagating a TPA produces an equivalent instantanteous network.
  lemma propagate_tpa_equiv (σ : inst.network (tpa υ)) (e : action_edge) : propagate_tpa σ e ≈ σ :=
    begin
      unfold propagate_tpa,
      transitivity,
        exact update_port_equiv (σ.update_port role.input e.iap (tpa.merge (σ.η.port role.input e.iap) (σ.η.port role.output e.oap))) _ _ _,
        exact update_port_equiv σ _ _ _
    end

  -- Propagates the TPAs from all of the OAPs connected to a given IAP into the IAP.
  -- The signature of this function is a little strange, as to allow it to work for the fold in `propagate_actions`.
  noncomputable def gather_iap (as : finset action_edge) (σ : inst.network (tpa υ)) (iap : port.id) : inst.network (tpa υ) :=
    ((as.filter (λ a : action_edge, a.iap = iap)).val.to_list
        .merge_sort (action_priority_ge σ))
        .foldl propagate_tpa σ

  -- Gathering a IAP produces an equivalent instantanteous network.
  lemma gather_iap_equiv (as : finset action_edge) (σ : inst.network (tpa υ)) (iap : port.id) :
    gather_iap as σ iap ≈ σ :=
    begin
      unfold gather_iap,
      induction (as.filter (λ a : action_edge, a.iap = iap)).val.to_list.merge_sort (action_priority_ge σ) generalizing σ,
        case list.nil { simp },
        case list.cons {
          rw list.foldl_cons,
          transitivity,
            exact ih (propagate_tpa σ hd),
            exact propagate_tpa_equiv σ hd
        }
    end

  -- Propagates the TPAs from all OAPs to their respective IAPs.
  noncomputable def propagate_actions (σ : inst.network (tpa υ)) (iaps : finset port.id) (as : finset action_edge) : inst.network (tpa υ) :=
    iaps.val.to_list.foldl (gather_iap as) σ

  -- Propagating actions produces an equivalent instantanteous network.
  lemma propagate_actions_equiv (σ : inst.network (tpa υ)) (iaps : finset port.id) (as : finset action_edge) : 
    propagate_actions σ iaps as ≈ σ :=
    begin
      unfold propagate_actions,
      induction iaps.val.to_list generalizing σ,
        case list.nil { simp },
        case list.cons {
          rw list.foldl_cons,
          transitivity,
            exact ih (gather_iap as σ hd),
            exact gather_iap_equiv as σ hd
        }
    end

  -- Removes all tag-value pairs that are not at a given tag from a given IAP.
  -- The signature of this function is a little strange, as to allow it to work for the fold in `at_tag`.
  noncomputable def reduce_iap_to_tag (t : tag) (σ : inst.network (tpa υ)) (iap : port.id) : inst.network (tpa υ) :=
    σ.update_port role.input iap (tpa.at_tag (σ.η.port role.input iap) t)

  -- Reducing a IAP to a given tag produces an equivalent instantanteous network.
  lemma reduce_iap_to_tag_equiv (t : tag) (σ : inst.network (tpa υ)) (iap : port.id) : reduce_iap_to_tag t σ iap ≈ σ :=
    by { unfold reduce_iap_to_tag, exact update_port_equiv _ _ _ _ }

  -- Removes all tag-value pairs that are not at a given tag from all IAPs.
  noncomputable def at_tag (σ : inst.network (tpa υ)) (iaps : finset port.id) (t : tag) : inst.network (tpa υ) :=  
    iaps.val.to_list.foldl (reduce_iap_to_tag t) σ 

  -- Getting a network at a set tag produces an equivalent instantanteous network.
  lemma at_tag_equiv (σ : inst.network (tpa υ)) (iaps : finset port.id) (t : tag) : at_tag σ iaps t ≈ σ :=
    begin
      unfold at_tag,
      induction iaps.val.to_list generalizing σ,
        case list.nil { simp },
        case list.cons {
          rw list.foldl_cons,
          transitivity,
            exact ih (reduce_iap_to_tag t σ hd),
            exact reduce_iap_to_tag_equiv _ _ _
        }
    end

  -- Gets all of the tags contained in the TPAs of given ports.
  noncomputable def tags_in (σ : inst.network (tpa υ)) (ps : finset port.id) (r : ports.role) : finset tag :=
    ps.bUnion (λ p, (σ.η.port r p).elim ∅ (finset.image prod.fst))

  def new_events (τ : timed.network υ) : port.id → tag → option (tpa υ) := 
    λ p t,
      (τ.oaps_for_iap p)

  -- A pair of timed networks is a *time step*, if ...
  def is_time_step (τ τ' : timed.network υ) : Prop :=
    match τ.next_tag with
      | none            := ⊥
      | (some next_tag) := 
        τ'.σ = sorry ∧
        τ'.time = next_tag ∧
        τ'.actions = τ.actions ∧
        τ'.events = (λ p t, τ.new_events p t <|> τ.events p t)
    end

  notation t `→ₜ` t' := is_time_step t t'

  -- A pair of timed networks is an *execution step*, if ...
  def is_execution_step : option (timed.network υ) → option (timed.network υ) → Prop 
    | (some τ) none      := τ.next_tag = none
    | none     none      := ⊤
    | none     (some _)  := ⊥
    | (some τ) (some τ') := ∃ τₜ, (τ →ₜ τₜ) ∧ -- τₜ is a time-progressed version of τ
      (τ'.σ = τₜ.σ.run sorry sorry) ∧ -- Cf. IDEAS: use the (to be) new definition of `run`.
      (τ'.time = τₜ.time) ∧                  -- τ' must be at the time of the "next action" (given by τₜ)
      (τ'.events = τₜ.events) ∧              -- τ' must inherit all future events (given by τₜ) [in this case, past events are also inherited]
      (τ'.actions = τₜ.actions)              -- τ' must still have the same actions as τ 

  notation t `→ₑ` t' := is_execution_step t t'

  structure execution (τ : timed.network υ) :=
    (steps : seq (timed.network υ))
    (head : steps.head = τ)
    (succ : ∀ i, steps.nth i →ₑ steps.nth (i + 1))

  -- We're explicitly not proving that there exists an algorithm, that produces an execution.

  theorem determinism (τ : timed.network υ) (e e' : execution τ) : e = e' :=
    sorry

end network
end timed