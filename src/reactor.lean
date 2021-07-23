import lgraph
-- import reaction
import primitives
open reactor
open reactor.ports
-- open mutation

open_locale classical

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Mutual.20inductive.20families

-- Cf. `primitives.lean`.
variables (ι : Type*) (υ : Type*) [decidable_eq ι] [value υ]

namespace reactor 

  variables {ι υ} {d : ℕ}

  def rcn_ids (rtr : reactor ι υ d) : finset ι := rtr.rcns.keys

  noncomputable def reactions (rtr : reactor υ) : finset (reaction υ) := rtr.rcns.values 

  noncomputable def rcn (rtr : reactor υ) {i : rcn_id} (h : i ∈ rtr.rcn_ids) : reaction υ :=
    (finmap.mem_iff.mp h).some

  lemma wf_rcn_deps' (rtr : reactor υ) {i : rcn_id} (h : i ∈ rtr.rcn_ids) (r : ports.role) : 
    (rtr.rcn h).deps r ⊆ (rtr.prts r).ids :=
    begin
      suffices hv : (rtr.rcn h) ∈ rtr.rcns.values, from rtr.wf_rcn_deps hv r,
      simp only [set.finite.mem_to_finset, finmap.values, set.mem_set_of_eq],
      existsi i,
      existsi h,
      unfold rcn,
      generalize_proofs h',
      obtain ⟨x, hx⟩ := h',
      simp [hx],
      generalize_proofs h'',
      apply classical.some_spec
    end

  -- Alternative formalization: 
  -- `(rtr.rcns.lookup p).elim ∅ (λ rcn, rcn.deps r)`
  noncomputable def prts_for_rcn (rtr : reactor υ) (i : rcn_id) (r : ports.role) : finset (prt_id r) :=
    if h : i ∈ rtr.rcn_ids then (rtr.rcn h).deps r else ∅

  noncomputable def rcns_for_prt {r : ports.role} (rtr : reactor υ) (p : prt_id r) : finset rcn_id :=
    let description := { i | ∃ (h' : i ∈ rtr.rcn_ids), p ∈ ((rtr.rcn h').deps r) } in
    have is_finite : description.finite, 
      begin
        let f := (rtr.rcn_ids.attach.filter (λ i : { x // x ∈ rtr.rcn_ids }, p ∈ ((rtr.rcn i.property).deps r))).image subtype.val,
        suffices h : ↑f = description, by simp only [←h, finset.finite_to_set],
        simp only [description, f],
        ext,
        simp
      end,
    is_finite.to_finset

  lemma has_rcns_impl_valid_prt {rtr : reactor υ} {r : ports.role} {p : prt_id r} (h : (rtr.rcns_for_prt p).nonempty) : 
    p ∈ (rtr.prts r).ids :=
    begin
      simp only [reactor.rcns_for_prt, set.finite.to_finset.nonempty, set.nonempty] at h,
      obtain ⟨i, h⟩ := h,
      simp only [set.mem_set_of_eq] at h,
      obtain ⟨hi, hp⟩ := h,
      have h, from rtr.wf_rcn_deps' hi r,
      tauto
    end

  -- Reactors are equivalent if they are structurally the same.
  instance equiv : has_equiv (reactor υ) := ⟨λ rtr rtr', 
    (rtr.prts role.in).ids  = (rtr'.prts role.in).ids ∧
    (rtr.prts role.out).ids = (rtr'.prts role.out).ids ∧
    rtr.rcns = rtr'.rcns
  ⟩

  -- Reactor equivalence is reflexive.
  @[refl] 
  lemma equiv_refl (rtr : reactor υ) : rtr ≈ rtr := by simp [(≈)]

  -- Reactor equivalence is symmetric.
  @[symm]
  lemma equiv_symm {rtr rtr' : reactor υ} (h : rtr ≈ rtr') : rtr' ≈ rtr :=
    begin
      simp only [(≈)] at ⊢ h,
      obtain ⟨h1, h2, h3⟩ := h, 
      repeat { split, symmetry, assumption },
      symmetry, assumption
    end

  -- Reactor equivalence is transitive.
  @[trans]
  lemma equiv_trans {rtr₁ rtr₂ rtr₃ : reactor υ} (h₁₂ : rtr₁ ≈ rtr₂) (h₂₃ : rtr₂ ≈ rtr₃) : 
    rtr₁ ≈ rtr₃ :=
    begin 
      simp only [(≈)] at ⊢ h₁₂ h₂₃,
      obtain ⟨h121, h122, h123⟩ := h₁₂,
      obtain ⟨h231, h232, h233⟩ := h₂₃,
      repeat { split, transitivity, assumption },
      exact h231, exact h232,
      transitivity ; assumption
    end

  def executes_on_rcn_to (rtr : reactor υ) (i : rcn_id) (rtr' : reactor υ) : Prop :=
    if h : i ∈ rtr.rcn_ids then
      if (rtr.rcn h).triggers_on (rtr.prts role.in) then
        let output := (rtr.rcn h) (rtr.prts role.in) rtr.state in
        rtr'.rcns = rtr.rcns ∧
        rtr'.prts role.in = rtr.prts role.in ∧
        rtr'.prts role.out = (output.prt_vals).merge_onto (rtr.prts role.out) ∧
        rtr'.state = output.state
      else
        rtr' = rtr
    else
      false

  notation r `-` i `→ₑ` s := r.executes_on_rcn_to i s
   
  theorem executes_on_rcn_to_unique {src dst₁ dst₂ : reactor υ} {i : rcn_id} (h₁ : src -i→ₑ dst₁) (h₂ : src -i→ₑ dst₂) :
    dst₁ = dst₂ :=
    begin
      simp only [executes_on_rcn_to] at h₁ h₂,
      by_cases hm : i ∈ src.rcn_ids,
        {
          simp only [dif_pos, hm] at h₁ h₂,
          by_cases ht : (src.rcn hm).triggers_on (src.prts role.in),
            {
              simp only [if_true, ht] at h₁ h₂,
              ext1,
                repeat { simp only [h₁, h₂] },
                ext1 r,
                cases r 
                  ; simp only [h₁, h₂]    
            },
            {
              simp only [if_false, ht] at h₁ h₂,
              simp only [h₁, h₂]
            }
        },
        {
          exfalso,
          simp only [hm, dif_neg, not_false_iff] at h₁,
          exact h₁
        }
    end

end reactor