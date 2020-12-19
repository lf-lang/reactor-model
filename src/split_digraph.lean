-- Inspired by: https://gist.github.com/MonoidMusician/1c8cc2ec787ebaf91b95d67cbc5c3498

import data.rel

structure split_digraph (Nₛ Nₑ : Type*) :=
  (conn : rel Nₛ Nₑ) 
  (same : rel Nₑ Nₛ)
  (paired : ∀ nₑ : Nₑ, ∃ nₛ : Nₛ, same nₑ nₛ)
  (unique : ∀ (nₑ : Nₑ) (nₛ nₛ' : Nₛ), same nₑ nₛ ∧ same nₑ nₛ' → nₛ = nₛ')

namespace split_digraph

  def edge {Nₛ Nₑ : Type*} (g : split_digraph Nₛ Nₑ) (nₛ : Nₛ) (nₑ : Nₑ) := g.conn nₛ nₑ
  def entity {Nₛ Nₑ : Type*} (g : split_digraph Nₛ Nₑ) (nₑ : Nₑ) (nₛ : Nₛ) := g.same nₑ nₛ

  inductive path {Nₛ Nₑ : Type} (g : split_digraph Nₛ Nₑ) : Nₛ → Nₑ → Type
    | direct {nₛ : Nₛ } {nₑ : Nₑ} : (edge g nₛ nₑ) → path nₛ nₑ
    | composit {nₛ nₛ' : Nₛ } {nₑ nₑ' : Nₑ} : (edge g nₛ nₑ') → (entity g nₑ' nₛ') → (path nₛ' nₑ) → path nₛ nₑ

  namespace path 

    def vertices {Nₛ Nₑ : Type*} {g : split_digraph Nₛ Nₑ} {nₛ : Nₛ} {nₑ : Nₑ} : path g nₛ nₑ → list (Nₛ × Nₑ) :=
    begin
      intro p, 
      induction p,
        exact ⟨p_nₛ, p_nₑ⟩ :: [],
        exact ⟨p_nₛ, p_nₑ'⟩ :: p_ih,
    end

  end path

  -- If there is a path from nₛ nₑ, they can not belong to the same entity.
  def is_acyclic {Nₛ Nₑ : Type*} (g : split_digraph Nₛ Nₑ) := 
    ∀ (nₛ : Nₛ) (nₑ : Nₑ), path g nₛ nₑ → ¬(g.same nₑ nₛ)

end split_digraph