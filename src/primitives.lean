import data.finset
import mathlib

class reactor.value (α : Type*) := 
  (absent : α)
  (dec_eq : decidable_eq α)

notation `⊥` := reactor.value.absent

instance reactor.value.decidable_eq {υ : Type*} [reactor.value υ] : decidable_eq υ := reactor.value.dec_eq

/-instance reactor.value.has_orelse {υ : Type*} [y : reactor.value υ] : has_orelse (λ _, υ) := 
  ⟨λ _ v v', if v = ⊥ then v' else v⟩-/

variables (ι υ : Type*) [decidable_eq ι] [reactor.value υ]

namespace reactor

  def state_vars := ι ⇀ υ

  def ports := ι ⇀ υ

  namespace ports

    variables {ι υ}

    inductive role
      | «in» : role
      | out : role

    @[reducible]
    def role.opposite : role → role 
      | role.in := role.out
      | role.out := role.in
 
    def at' (p : ports ι υ) (i : ι) : option υ := 
      p.lookup i

    def «at» (p : ports ι υ) (i : ι) : option υ := 
      p.at' i >>= (λ v, if v = ⊥ then none else v)

    lemma at'_to_at {p p' : ports ι υ} {i : ι} (h : p.at' i = p'.at' i) :
      p.at i = p'.at i :=
      by simp only [«at», h]

    lemma at'_absent_at_none {p : ports ι υ} {i : ι} (h : p.at' i = some ⊥) :
      p.at i = none :=
      by simp [«at», h]

    @[reducible]
    def eq_at (is : finset ι) (p p' : ports ι υ) : Prop := 
      ∀ i ∈ is, p.at' i = p'.at' i

    notation p =i= q := eq_at i p q

    instance eq_at.setoid (is : finset ι) : setoid (ports ι υ) := { 
      r := eq_at is,
      iseqv := ⟨
        by tauto,
        by tauto,
        by { simp only [transitive, eq_at], finish }
      ⟩
    }

    noncomputable def merge_onto («from» «to» : ports ι υ) : ports ι υ :=
      let description := ∃ result : ports ι υ, result.ids = to.ids ∧ (∀ i ∈ result.ids, result.at i = (from.at i <|> to.at i)) in
      have existence : description, 
      from sorry,
      existence.some

    noncomputable def inhabited_ids (p : ports ι υ) : finset ι :=
      let description := { i | p.at i ≠ none } in
      have is_finite : description.finite,
        begin
          let f : finset ι := p.ids.filter (λ i, p.at i ≠ none),
          suffices h : ↑f = description, by simp only [←h, finset.finite_to_set],
          ext,
          split,
            {
              intro h,
              simp only [set.mem_sep_eq, finset.mem_range, finset.mem_coe, finset.coe_filter] at h,
              simp only [h, ne.def, not_false_iff, set.mem_set_of_eq]
            },
            {
              intro h,
              simp only [set.mem_set_of_eq] at h,
              have h', from h,
              simp only [«at», option.ne_none_iff_exists] at h',
              obtain ⟨_, h'⟩ := h',
              replace h' := eq.symm h',
              simp [option.bind_eq_some] at h',
              obtain ⟨_, ⟨h', _⟩⟩ := h',
              simp only [at'] at h',
              have h'', from finmap.mem_of_lookup_eq_some h',
              simp only [set.mem_sep_eq, finset.mem_coe, finset.coe_filter],
              exact ⟨h'', h ⟩
            }
        end,
      is_finite.to_finset

  lemma inhabited_ids_none {p : ports ι υ} {i : ι} (h : p.at i = none) : i ∉ p.inhabited_ids :=
    by simp [inhabited_ids, h]

  end ports

end reactor

