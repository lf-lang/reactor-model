import data.finset
import primitives
open reactor
open reactor.ports

-- Cf. primitives.lean
variables (ι υ : Type*) [decidable_eq ι] [reactor.value υ]

structure mutation.output := 
  (prt_vals : ports ι υ)
  (state    : state_vars ι υ)
  (new_cns  : list (ι × ι))
  (del_cns  : list (ι × ι))
  (new_rtrs : list empty)
  (del_rtrs : finset ι)

open mutation

structure mutation :=
  (deps : ports.role → finset ι) 
  (triggers : finset ι)
  (body : ports ι υ → state_vars ι υ → output ι υ)
  (ts_sub_in_deps : triggers ⊆ deps role.in)
  (in_dep_only : ∀ {i i'} s, (i =(deps role.in)= i') → body i s = body i' s)
  (out_prt_vals_dep_only : ∀ i s {o}, (o ∉ deps role.out) → (body i s).prt_vals.at o = none) 

namespace mutation

  variables {ι υ}

  instance coe_to_fun : has_coe_to_fun (mutation ι υ) := ⟨_, (λ m, m.body)⟩

  lemma out_prt_vals_sub_out_deps (m : mutation ι υ) (i : ports ι υ) (s : state_vars ι υ) :
    (m i s).prt_vals.inhabited_ids ⊆ m.deps role.out :=
    begin
      simp only [(⊆)],
      intro o,
      rw ←not_imp_not,
      intro h,
      have hₙ, from m.out_prt_vals_dep_only i s h,
      exact ports.inhabited_ids_none hₙ
    end

  def triggers_on (m : mutation ι υ) (p : ports ι υ) : Prop :=
    ∃ (t ∈ m.triggers) (v : υ), p.at t = some v

  lemma eq_input_eq_triggering {m : mutation ι υ} {p p' : ports ι υ} (h : p =(m.deps role.in)= p') :
    m.triggers_on p ↔ m.triggers_on p' :=
    begin
      simp [triggers_on, ports.eq_at] at h ⊢,
      split ; { 
        intro hₑ,
        obtain ⟨t, r, v, h'⟩ := hₑ,
        existsi t,
        existsi r,
        existsi v,
        have hₜ, from finset.mem_of_subset m.ts_sub_in_deps r,
        replace h := at'_to_at (h t hₜ),
        simp only [←h', h]
      }
    end

end mutation