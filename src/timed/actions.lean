import inst.network.basic
import timed.primitives
open reactor
open reactor.ports

open_locale classical

-- The type of opaque values that underlie TPAs.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables {υ : Type*} [decidable_eq υ]

-- An action edge connects an output action port (OAP) to an input action port (IAP).
@[ext]
structure timed.network.action_edge := 
  (oap : port.id)
  (iap : port.id)

open timed.network

-- Action edges' equality is non-constructively decidable.
noncomputable instance timed.network.action_edge_dec_eq : decidable_eq action_edge := classical.dec_eq _

-- The proposition that there can be at most one action edge per OAP.
def finset.are_many_to_one (es : finset action_edge) : Prop :=
  ∀ e e' : action_edge, e ∈ es → e' ∈ es → e.oap = e'.oap → e = e'

-- The proposition that action edges don't connect between different reactors.
def finset.are_local (es : finset action_edge) : Prop :=
  ∀ e : action_edge, e ∈ es → e.oap.rtr = e.iap.rtr

-- The proposition that an OAP has exactly one incoming connection.
def finset.have_one_src_in (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ e : action_edge, e ∈ es → 
  ∃! r : reaction.id, 
    (e.oap ∈ σ.η.deps r role.output)

-- The proposition that a reaction can not connect to the same IAP through multiple OAPs.
def finset.are_functionally_unique_in (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ (e e' : action_edge) (r : reaction.id), e ∈ es → e' ∈ es → 
    (e.oap ∈ σ.η.deps r role.output) → (e'.oap ∈ σ.η.deps r role.output) → 
    e.iap = e'.iap → e.oap = e'.oap

-- The proposition that action ports do not also behave as regular ports (by being connected
-- with network graph edges).
def finset.are_separate_from (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  ∀ (ae : action_edge) (ne : inst.network.graph.edge), ae ∈ es → ne ∈ σ.η.edges → 
    ae.iap ≠ ne.dst ∧ ae.oap ≠ ne.src

-- A given set of action edges (and by extension action ports) is well-formed for a given
-- instantaneous network, if all of the properties above hold.
def finset.are_well_formed_for (es : finset action_edge) (σ : inst.network (tpa υ)) : Prop :=
  es.are_many_to_one ∧ 
  es.are_local ∧
  es.have_one_src_in σ ∧ 
  es.are_functionally_unique_in σ ∧
  es.are_separate_from σ

-- Well-formedness of action edges is retained under equivalence of instantaneous reactor networks.
lemma timed.network.equiv_inst_network_wf (es : finset action_edge) {σ σ' : inst.network (tpa υ)} (hq : σ' ≈ σ) (hw : es.are_well_formed_for σ) : 
  es.are_well_formed_for σ' :=
  begin
    unfold finset.are_well_formed_for at hw ⊢,
    simp only [(≈)] at hq,
    repeat { split },
      simp [hw],
      simp [hw],
      {
        unfold finset.have_one_src_in inst.network.graph.deps inst.network.graph.rcn at ⊢ hw,
        intros e hₑ,
        obtain ⟨i, hᵢ⟩ := hw.right.right.left e hₑ,
        rw exists_unique,
        existsi i,
        split,
          { 
            rw (hq.right.right i.rtr).right,
            exact hᵢ.left
          },
          { 
            intro x,
            rw (hq.right.right x.rtr).right,
            exact hᵢ.right x
          }
      },
      {
        unfold finset.are_functionally_unique_in inst.network.graph.deps inst.network.graph.rcn,
        intros e e' i,
        rw (hq.right.right i.rtr).right,
        exact hw.right.right.right.left e e' i
      },
      {
        unfold finset.are_separate_from,
        rw hq.left,
        exact hw.right.right.right.right
      }
  end