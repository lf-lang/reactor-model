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
  {nᵢ nₒ nᵣ : ℕ}
  (input : ports nᵢ)
  (output : ports nₒ)
  (state : state_vars)
  (reactions : priority nᵣ → reaction)
  (rcn_dims : ∀ r, (∃ p, reactions p = r) → r.dims = (nᵢ, nₒ)) -- The ∃-term is just the explicit way of writing `r ∈ reactions`.

@[reducible]
instance : has_mem reaction reactor := {mem := λ rcn rtr, ∃ p, rtr.reactions p = rcn}

namespace reactor 

  -- The characteristic dimensions of a given reactor.
  def dims (r : reactor) : ℕ × ℕ :=
    (r.nᵢ, r.nₒ)

  -- A reactor is deterministic iff all of it's reactions are deterministic.
  def is_det (r : reactor) : Prop :=
    ∀ rcn : reaction, rcn ∈ r → rcn.is_det

  -- A list of a given reactors reactions, ordered by their priority.
  def ordered_rcns (r : reactor) : list reaction :=
    let priorities := (fintype.elems (priority r.nᵣ)).sort (<) in
    priorities.map r.reactions

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
          exact ⟨p, fintype.complete p, h⟩
        }
    end

  -- The dimensions of the reactions in a reactor's list of `ordered_reactions` are the same as the
  -- dimensions of the reactor itself.
  theorem ord_rcns_dims_eq_rtr_dims (rtr : reactor) : 
    ∀ rcn : reaction, rcn ∈ rtr.ordered_rcns → rcn.dims = (rtr.nᵢ, rtr.nₒ) :=
    begin
      intros rcn h,
      suffices hₘ : rcn ∈ rtr, from rtr.rcn_dims rcn hₘ,
      apply (ord_rcns_mem_rtr rtr rcn).mp h
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

  private def run_func_aux_main {nₒ : ℕ} (r : reaction) (h : nₒ = r.nₒ) (i : ports r.nᵢ) (ps : ports nₒ × state_vars) : set (ports nₒ × state_vars) :=
    if r.fires_on i (refl _) then 
      let psᵣ := r.body (i, ps.2) in
      let ps' := psᵣ.image (λ ⟨pᵣ, sᵣ⟩, (pᵣ.cast h, sᵣ)) in 
      ps'.image (λ ⟨p', s'⟩, (ps.1.merge p', s'))
    else 
      {(ports.empty, ps.2)}

  private def run_func_aux {nᵢ nₒ : ℕ} (rs : list reaction) (h : ∀ r : reaction, r ∈ rs → r.dims = (nᵢ, nₒ)) (i : ports nᵢ) (s : state_vars) : set (ports nₒ × state_vars) :=
    list.rec_on rs.attach
      {(ports.empty, s)}
      (
        λ rₕ _ psₜ,
          let ⟨hᵢ, hₒ⟩ := prod.mk.inj (h rₕ rₕ.property) in 
          let ps' := psₜ.image (run_func_aux_main rₕ (symm hₒ) (i.cast hᵢ)) in
          ps'.sUnion
      )
 
  private def run_func : reactor ~?> reactor := λ r,
    let ps := run_func_aux r.ordered_rcns (ord_rcns_dims_eq_rtr_dims r) r.input r.state in
    ps.image (λ e, {input := ports.empty, output := e.1, state := e.2, ..r})

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
    (run.det (rtr_det_run_det h) r).input = ports.empty :=
    sorry

  --? Prove the same for state.
  theorem no_in_no_out (r : reactor) (h : r.is_det) : 
    r.input = ports.empty → (run.det (rtr_det_run_det h) r).output = ports.empty :=
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
