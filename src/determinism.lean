import basic
import data.vector

namespace hidden 

  variables i o : ℕ 

  def inputs := vector value i
  def outputs := vector value o
  def state := list value

  -- REACTION

  -- The output vector produced by a reaction contains ε for all of those ports which should remain unaffected.
  def reaction := (inputs i × state) → (outputs o × state)
  
  namespace reaction

    def determinism {i o : ℕ} (r : reaction i o) : Prop := 
      ∀ is₁ is₂ : (inputs i × state), is₁ = is₂ → r is₁ = r is₂

    theorem deterministic (r : reaction i o) : determinism r :=
      assume is₁ is₂ : (inputs i × state),
      assume h : is₁ = is₂,
      show r is₁ = r is₂,
      from congr_arg r h

  end reaction

  -- BODY

  -- The order produced by a body only describes the *priority* of the reactions, not their connections.
  inductive body
    | single (r : reaction i o) : body
    | composed (head : reaction i o) (tail : body) : body

  namespace body

    private def merge {o : ℕ} (o₁ o₂ : outputs o) : outputs o := sorry

    private def process' {i o : ℕ} : (inputs i × outputs o × state) → (body i o) → (outputs o × state)
      | ios (body.single r)     := let os := r ⟨ios.1, ios.2.2⟩ in ⟨merge os.1 ios.2.1, os.2⟩ 
      | ios (body.composed r t) := let os := r ⟨ios.1, ios.2.2⟩ in let os' := process' ⟨ios.1, os.1, os.2⟩ t in ⟨merge os.1 os'.1, os'.2⟩ 

    def process {i o : ℕ} : (inputs i × state) → (body i o) → (outputs o × state)
      | is (body.single r)     := r is
      | is (body.composed r t) := let os := r is in process' ⟨is.1, os.1, os.2⟩ t

    def determinism {i o : ℕ} (b : body i o) : Prop := 
      ∀ is₁ is₂ : (inputs i × state), is₁ = is₂ → (process is₁ b) = (process is₂ b)

    theorem deterministic (b : body i o) : determinism b :=
      assume is₁ is₂ : (inputs i × state),
      assume h : is₁ = is₂,
      show process is₁ b = process is₂ b,
      from congr (congr_arg process h) (refl b)

  end body

  -- SEQUENCE

  namespace sequence
    
    -- Given a list of inputs, an initial state and a body, `process` computes the resulting state and outputs.
    def process {i o : ℕ} : list (inputs i) → (state) → (body i o) → list (outputs o × state)
      | [] _ _ := []
      | (list.cons i_h i_t) s b := let os' := body.process ⟨i_h, s⟩ b in list.cons os' (process i_t os'.2 b) 

    def determinism {i o : ℕ} (b : body i o) : Prop := 
      ∀ (i₁ i₂ : list (inputs i)) (s₁ s₂ : state), 
      (i₁ = i₂ ∧ s₁ = s₂) → (process i₁ s₁ b) = (process i₂ s₂ b)

    theorem deterministic (b : body i o) : determinism b :=
      assume i₁ i₂ : list (inputs i),
      assume s₁ s₂ : state,
      assume h : i₁ = i₂ ∧ s₁ = s₂,
      show process i₁ s₁ b = process i₂ s₂ b, 
      from congr (congr (congr_arg process h.left) h.right) (refl b)

  end sequence

  -- REACTOR

  structure reactor :=
    (in_ports : inputs i)
    (out_ports : outputs o)
    (s : state)
    (b : body i o)

  -- NETWORK

  -- By defining the `reactors` as a list instead of a set, we can again drop the need for identifiers and use the index
  -- into the list as a reactor's identifier.
  --
  -- The list needs to be homogenous over the type of rectors wrt. `i o`. Is this possible?
  structure network :=
    (reactors : list (reactor i o))
    (connections : (reactor i o) × ℕ → (reactor i o) × ℕ)

end hidden
