import reactor

variables (υ : Type*) [decidable_eq υ]

structure reactor.diff :=
  (Δᵢ : finset ℕ)
  (Δₒ : finset ℕ)
  (δᵢ : {n // n ∈ Δᵢ} → option υ)
  (δₒ : {n // n ∈ Δₒ} → option υ)
  (δₛ : option (list υ))

open reactor

def reactor.diff.applied_to {υ} [decidable_eq υ] (d : diff υ) (rtr : reactor υ) : reactor υ :=
  sorry

notation d ∘ r := (reactor.diff.applied_to d r)

def reactor.diff.compose {υ} [decidable_eq υ] (second first : diff υ) : diff υ :=
  { diff . 
    Δᵢ := first.Δᵢ ∪ second.Δᵢ,
    Δₒ := first.Δₒ ∪ second.Δₒ,
    δᵢ := λ n, 
      if h : ↑n ∈ first.Δᵢ 
      then first.δᵢ ⟨n, h⟩ 
      else second.δᵢ ⟨n, or.resolve_left (finset.mem_union.mp n.property) h⟩,
    δₒ := λ n,
      if h : ↑n ∈ first.Δₒ 
      then first.δₒ ⟨n, h⟩ 
      else second.δₒ ⟨n, or.resolve_left (finset.mem_union.mp n.property) h⟩,
    δₛ := first.δₛ <|> second.δₛ
  }

notation s ∘ f := (reactor.diff.compose s f)

structure network.graph.diff :=
  (Δ : finset reactor.id)
  (δ : {n // n ∈ Δ} → reactor υ)