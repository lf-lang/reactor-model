-- Inspired by: https://gist.github.com/MonoidMusician/1c8cc2ec787ebaf91b95d67cbc5c3498

import data.rel

structure split_digraph (O I : Type*) :=
  (conn : rel O I) 
  (same : rel I O)
  (paired : ∀ i : I, ∃ o : O, same i o)
  (unique : ∀ (i : I) (o o' : O), same i o ∧ same i o' → o = o')

namespace split_digraph

  def edge {O I : Type*} (g : split_digraph O I) (o : O) (i : I) := g.conn o i
  def entity {O I : Type*} (g : split_digraph O I) (i : I) (o : O) := g.same i o

  inductive path {O I : Type} (g : split_digraph O I) : O → I → Type
    | direct {o : O } {i : I} : (edge g o i) → path o i
    | composit {o o' : O } {i i' : I} : (edge g o i') → (entity g i' o') → (path o' i) → path o i

  namespace path 

    def vertices {O I : Type*} {g : split_digraph O I} {o : O} {i : I} : path g o i → list (O × I) :=
    begin
      intro p, 
      induction p,
        case direct   : { exact ⟨p_o, p_i ⟩ :: []   },
        case composit : { exact ⟨p_o, p_i'⟩ :: p_ih }
    end

  end path

  -- If there is a path from o i, they can not belong to the same entity.
  def is_acyclic {O I : Type*} (g : split_digraph O I) := 
    ∀ (o : O) (i : I), path g o i → ¬(g.same i o)
    
  def is_input_unique {O I : Type*} (g : split_digraph O I) :=
    ∀ (o₁ o₂ : O) (i : I), (edge g o₁ i) ∧ (edge g o₂ i) → o₁ = o₂

end split_digraph