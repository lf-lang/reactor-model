import primitives
import reactor.primitives
import reaction

open reactor
open reaction

structure reactor :=
  {nᵢ nₒ nₛ : ℕ}
  (inputs : ports nᵢ)
  (outputs : ports nₒ)
  (st : state nₛ)
  (rs : list (reaction nᵢ nₒ nₛ))

namespace reactor 

  instance ports_to_input {n : ℕ} {dᵢ : finset (fin n)} : has_lift (ports n) (input dᵢ) :=
    ⟨λ p, λ i : {d // d ∈ dᵢ}, p i⟩

  instance output_to_ports {n : ℕ} {dₒ : finset (fin n)} : has_lift (output dₒ) (ports n) :=
    ⟨λ o, λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none⟩

  -- TEMPORARY (ports_to_input)
  private def lift_ {n : ℕ} {dᵢ : finset (fin n)} : (ports n) → (input dᵢ) :=
    λ p, λ i : {d // d ∈ dᵢ}, p i
  -- TEMPORARY (output_to_ports)
  private def lift_ {n : ℕ} {dₒ : finset (fin n)} : (output dₒ) → (ports n) :=
    λ o, λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none

  private def merge_ports {n : ℕ} (first last : ports n) : ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

  instance {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) (is : reactor.ports nᵢ) : decidable (is_triggered_by r is) := sorry

  private def run' {nᵢ nₒ nₛ : ℕ} : (ports nᵢ) → (state nₛ) → (list (reaction nᵢ nₒ nₛ)) → (ports nₒ × state nₛ)
    | i s [] := ⟨ports.absent, s⟩ 
    | i s (rₕ :: rₜ) := 
      let osₕ : ports nₒ × state nₛ := 
        if rₕ.is_triggered_by i
        then let os := rₕ.body (lift_ i) s in ⟨(lift_ os.1), os.2⟩ 
        else ⟨ports.absent, s⟩ in
      let osₜ := run' i osₕ.2 rₜ in
      ⟨merge_ports osₕ.1 osₜ.1, osₜ.2⟩

  def run (r : reactor) : reactor :=
    let os := run' r.inputs r.st r.rs in
    ⟨ports.absent, os.1, os.2, r.rs⟩ 

  protected theorem volatile_input (r : reactor) : 
    (run r).inputs = ports.absent :=
    refl (run r).inputs

  -- This is part of the Mathlib docs, but not available here for some reason.
  -- https://github.com/leanprover-community/mathlib/blob/44400c995cc2d05af149832c694ef7bd097ec636/src/data/finset/basic.lean#L1473
  private lemma finset.nonempty.map {α : Type*} {β : Type*} [decidable_eq α] (s : finset α) (h : s.nonempty) (f : α ↪ β) : (s.map f).nonempty :=
    let ⟨a, ha⟩ := h in ⟨f a, (finset.mem_map' f).mpr ha⟩

  private lemma no_in_no_trig {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) :
    r.is_triggered_by ports.absent = false :=
    begin 
      rw reaction.is_triggered_by,
      simp,
      by_cases r.triggers.nonempty,
        {
          rw ports.absent,
          rw finset.image_const,
          apply finset.not_nonempty_empty,
          apply finset.nonempty.map r.triggers h,
        },
        {
          -- r.triggers is empty ->
          -- finset.map on r.triggers produces something empty ->
          -- finset.image produces something empty ->
          -- erasing from something empty is empty ->
          -- the result is not nonempty

          -- apply finset.image_empty ports.absent,

          sorry
        }
    end

      --? Prove the same for state.
  protected theorem no_in_no_out (r : reactor) : 
    r.inputs = ports.absent → (run r).outputs = ports.absent :=
    begin 
      assume h,
      rw run,
      simp,
      rw h,
      induction r.rs,
        rw run',
        {
          rw run',
          simp,
          have no_trig : hd.is_triggered_by ports.absent = false := no_in_no_trig hd,
          -- rw no_trig,
          sorry
        }
    end

  private lemma merge_absent_is_neutral {n : ℕ} (first last : ports n) :
    last = ports.absent → (merge_ports first last) = first := 
    begin
      assume h,
      rw merge_ports,
      simp,
      rw h,
      rw ports.absent,
      simp,
    end

  private lemma merge_skips_absent {n : ℕ} (first last : ports n) (i : fin n):
    (last i) = none → (merge_ports first last) i = (first i) := 
    begin
      assume h,
      rw merge_ports,
      simp,
      rw h,
      simp,
    end

  -- Running a single unconnected reactor is deterministic, if equal initial states lead to equal
  -- end states.
  -- Since `reactor.run` is a function, determinism is trivially fulfilled.
  protected theorem determinism (r₁ r₂ : reactor) : 
    r₁ = r₂ → run r₁ = run r₂ :=
    assume h, congr_arg run h

end reactor
