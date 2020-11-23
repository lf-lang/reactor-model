import basic

namespace determinism 
  
  def state := identifier → value  
  def ports := identifier → value 
  def env := state × ports

  -- REACTION

  def reaction := env → env
  
  namespace reaction

    def determinism (r : reaction) : Prop := ∀ e₁ e₂ : env, e₁ = e₂ → r e₁ = r e₂

    theorem deterministic (r : reaction) : determinism r :=
      assume (e₁ e₂ : env) (h : e₁ = e₂),
      show r e₁ = r e₂, from congr_arg r h

  end reaction

  -- NETWORK

  -- The order produced by a network only describes the *priority* of the reactions, not their connections.
  inductive network
    | single (r : reaction) : network
    | composed (head : reaction) (tail : network) : network

  namespace network

    def process : env → network → env
      | e (network.single r) := r e
      | e (network.composed h t) := process (h e) t

    def determinism (n : network) : Prop := ∀ e₁ e₂ : env, e₁ = e₂ → process e₁ n = process e₂ n

    theorem deterministic (n : network) : determinism n :=
      assume (e₁ e₂ : env) (h : e₁ = e₂),
      show process e₁ n = process e₂ n, from congr (congr_arg process h) (refl n)

  end network

  -- SEQUENCE NETWORK

  namespace network'
    
    -- Given a list of port assignments, an initial state and a network, `process'` ouputs the environment after the networked has
    -- processed the list of inputs. The `state` output of one reaction is fed as input to the next.
    def process : (list ports) → state → network → (list env)
      | [] _ _ := []
      | (list.cons p t) s n := let e' := (network.process ⟨p, s⟩ n) in list.cons e' (process t e'.1 n) 

    def determinism (n : network) : Prop := 
      ∀ (p₁ p₂ : list ports) (s₁ s₂ : state), (p₁ = p₂ ∧ s₁ = s₂) → (process p₁ s₁ n) = (process p₂ s₂ n)

    theorem deterministic (n : network) : determinism n :=
      assume (p₁ p₂ : list ports) (s₁ s₂ : state) (h : p₁ = p₂ ∧ s₁ = s₂),
      show process p₁ s₁ n = process p₂ s₂ n, from congr (congr (congr_arg process h.left) h.right) (refl n)

  end network'

  

end determinism
