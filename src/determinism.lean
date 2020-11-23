import basic

namespace determinism 
  
  def state := identifier → value  
  def ports := identifier → value 
  
  def reaction := (state × ports) → (state × ports)
  
  def reaction_determinism (r : reaction) : Prop := ∀ i₁ i₂ : (state × ports), i₁ = i₂ → r i₁ = r i₂
  theorem reaction_deterministic (r : reaction) : reaction_determinism r :=
    assume i₁ i₂ : (state × ports),
    assume h : i₁ = i₂,
    show r i₁ = r i₂, from congr_arg r h

  def network := list reaction
  def send : (state × ports) → network → (state × ports)
    | i []              := i
    | i (list.cons r n) := send (r i) n

  def network_determinism (n : network) : Prop := ∀ i₁ i₂ : (state × ports), i₁ = i₂ → send i₁ n = send i₂ n
  theorem network_deterministic (n : network) : network_determinism n :=
    assume i₁ i₂ : (state × ports),
    assume h : i₁ = i₂,
    show send i₁ n = send i₂ n, from congr (congr_arg send h) (refl n)

end determinism
