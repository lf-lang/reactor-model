import basic
import data.vector

namespace hidden 

  variables i o s i' o' s' : ℕ 

  -- CONTAINER

  def inputs := vector value i
  def outputs := vector value o
  def state := vector value s
  def container := (inputs i) × (outputs o) × (state s)

  -- REACTION

  def reaction := (container i o s) → (container i o s)
  
  namespace reaction

    def determinism {i o s : ℕ} (r : reaction i o s) : Prop := 
      ∀ c₁ c₂ : (container i o s), c₁ = c₂ → r c₁ = r c₂

    theorem deterministic (r : reaction i o s) : determinism r :=
      assume c₁ c₂ : container i o s,
      assume h : c₁ = c₂,
      show r c₁ = r c₂,
      from congr_arg r h

  end reaction

  -- BODY

  -- The order produced by a body only describes the *priority* of the reactions, not their connections.
  inductive body
    | single (r : reaction i o s) : body
    | composed (head : reaction i o s) (tail : body) : body

  namespace body

    def process {i o s : ℕ} : (container i o s) → (body i o s) → (container i o s)
      | c (body.single r) := r c
      | c (body.composed h t) := process (h c) t

    def determinism {i o s : ℕ} (b : body i o s) : Prop := 
      ∀ c₁ c₂ : (container i o s), c₁ = c₂ → process c₁ b = process c₂ b

    theorem deterministic (b : body i o s) : determinism b :=
      assume e₁ e₂ : container i o s,
      assume h : e₁ = e₂,
      show process e₁ b = process e₂ b,
      from congr (congr_arg process h) (refl b)

  end body

  -- BODY SEQUENCE

  namespace body'
    
    -- Given a list of port assignments, an initial state and a body, `process` outputs the environment after the body has
    -- processed the list of inputs. The `state` output of one reaction is fed as input to the next.
    def process {i o s : ℕ} : list (inputs i × outputs o) → (state s) → (body i o s) → list (container i o s)
      | [] _ _ := []
      | (list.cons io_h io_t) s b := let c' := body.process ⟨io_h.1, io_h.2, s⟩ b in list.cons c' (process io_t c'.2.2 b) 

    def determinism {i o s : ℕ} (b : body i o s) : Prop := 
      ∀ (io₁ io₂ : list (inputs i × outputs o)) (s₁ s₂ : state s), 
      (io₁ = io₂ ∧ s₁ = s₂) → (process io₁ s₁ b) = (process io₂ s₂ b)

    theorem deterministic (b : body i o s) : determinism b :=
      assume io₁ io₂ : list (inputs i × outputs o),
      assume s₁ s₂ : state s,
      assume h : io₁ = io₂ ∧ s₁ = s₂,
      show process io₁ s₁ b = process io₂ s₂ b, 
      from congr (congr (congr_arg process h.left) h.right) (refl b)

  end body'

  structure reactor :=
    (d : identifier)
    (c : container i o s)
    (b : body i o s)

end hidden
