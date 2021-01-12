import nondet
import primitives
import reaction

open reactor
open reaction

-- It would be nice to declare reactors in a similar fashion to reactions.
-- I.e. reactions in themselves declare what they connect to (dᵢ and dₒ).
-- The difference is that reactions themselves are just a single "connection point",
-- so the mapping is a many-to-one (dependencies to reaction).
-- For reactors the mapping would have to be a many to many mapping (other reactors'
-- ports to own ports). This would on the one hand require the number of other reactors
-- to become part of a reactor's type, which seems inelegant. And further the mapping
-- would have to be implemented as a relation between another reactor's ports and the
-- self-reactor's ports. This would in turn also require nᵢ and nₒ to move into a 
-- reactor's type.

structure reactor :=
  (input : ports)
  (output : ports)
  (state : state_vars)
  (priorities : finset ℕ)
  (reactions : ℕ → reaction)

@[reducible]
instance : has_mem reaction reactor := {mem := λ rcn rtr, ∃ p, rtr.reactions p = rcn}

noncomputable instance : decidable_eq reactor := classical.dec_eq _

namespace reactor 

  -- A reactor is deterministic iff all of it's reactions are deterministic.
  def is_det (r : reactor) : Prop :=
    ∀ rcn : reaction, rcn ∈ r → rcn.is_det

  -- A list of a given reactor's reactions, ordered by their priority.
  def ordered_rcns (r : reactor) : list reaction :=
    (r.priorities.sort (≥)).map r.reactions

  -- A reaction is a member of a reactor's list of `ordered_reactions` iff it is also a member of
  -- the reactor itself.
  theorem ord_rcns_mem_rtr (rtr : reactor) :
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns ↔ rcn ∈ rtr :=
    begin
      intro rcn,
      rw ordered_rcns,
      split,
        { 
          simp,
          intros p _ h,
          exact ⟨p, h⟩
        },
        {
          simp,
          intros p h,
          sorry -- exact ⟨p, fintype.complete p, h⟩
        }
    end

  -- If a given reactor is deterministic, then all of its ordered reactions are deterministic.
  theorem ord_rcns_det (rtr : reactor) (h : rtr.is_det) :
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns → rcn.is_det :=
    begin
      intros rcn hₘ,
      apply h,
      apply (ord_rcns_mem_rtr rtr rcn).mp hₘ
    end

  noncomputable def priority_of (rtr : reactor) (rcn : reaction) (h : rcn ∈ rtr) : priority rtr.nᵣ := 
    h.some

  private def run_func_aux_main (r : reaction) (i : ports) (ps : ports × state_vars) : set (ports × state_vars) :=
    if r.fires_on i 
    then (r.body (i, ps.2)).image (λ ⟨p', s'⟩, (ps.1.merge p', s'))
    else {(ports.empty ps.1.length, ps.2)}

  private def run_func_aux (rs : list reaction) (i : ports) (s : state_vars) (nₒ : ℕ): set (ports × state_vars) :=
    list.rec_on rs.attach
      {(ports.empty nₒ, s)}
      (λ rₕ _ psₜ, (psₜ.image (run_func_aux_main rₕ i)).sUnion)
 
  private def run_func : reactor ~?> reactor := λ r,
    let ps := run_func_aux r.ordered_rcns r.input r.state r.output.length in
    ps.image (λ ⟨p, s⟩, {input := ports.empty r.input.length, output := p, state := s, ..r})

  private lemma run_func_is_total : 
    partial_nondet_func.is_total run_func :=
    begin
      rw partial_nondet_func.is_total,
      intro r,
      rw run_func,
      simp,
      rw run_func_aux,
      simp,
      induction r.ordered_rcns.attach,
        simp,
        {
          sorry
        }
    end

  def run : reactor ~> reactor := 
    {func := run_func, total := run_func_is_total}

  theorem rtr_det_run_det {r : reactor} :
    r.is_det → run.is_det :=
    begin
      rw is_det,
      intro h,
      rw total_nondet_func.is_det,
      intro r,
      rw exists_unique,
      sorry
    end

  theorem volatile_input (r : reactor) (h : r.is_det) : 
    (run.det (rtr_det_run_det h) r).input = (ports.empty r.input.length) :=
    sorry

  --? Prove the same for state.
  theorem no_in_no_out (r : reactor) (h : r.is_det) : 
    r.input = (ports.empty r.input.length) → (run.det (rtr_det_run_det h) r).output = (ports.empty r.output.length) :=
    sorry

  -- Running a single unconnected deterministic reactor on equal initial states leads to equal end
  -- states. 
  protected theorem determinism (r₁ r₂ : reactor) (h₁ : r₁.is_det) (h₂ : r₂.is_det) : 
    r₁ = r₂ → run.det (rtr_det_run_det h₁) r₁ = run.det (rtr_det_run_det h₂) r₂ :=
    begin
      intro h,
      subst h,
    end

end reactor
