import reactor.basic

namespace reactor

  namespace sequential
    
    private def run' : Π r : reactor, list (ports r.nᵢ) → list (ports r.nₒ) → reactor × list (ports r.nₒ) 
      | r [] o := ⟨reactor.run r, o⟩ 
      | r (iₕ :: iₜ) o := 
        let rₕ := reactor.run r in
        let rₜ : reactor := ⟨iₕ, ports.empty, rₕ.st, rₕ.reactions⟩ in 
        run' rₜ iₜ (o ++ [rₕ.outputs])

    -- The first input is already within the given reactor, and the last output will also be part
    -- of the output reactor.
    protected def run (r : reactor) (i : list (ports r.nᵢ)) : reactor × list (ports r.nₒ) :=
       run' r i []

    -- Passing a finite sequence of inputs through a single unconnected reactor is deterministic,
    -- if equal sequences lead to equal outputs and end states.
    -- Since `reactor.sequence.run` is a function, determinism is trivially fulfilled.
    theorem deterministic (r : reactor) (i₁ i₂ : list (ports r.nᵢ)) : 
      i₁ = i₂ → (sequential.run r i₁) = (sequential.run r i₂) :=
      assume h, h ▸ refl _

  end sequential

end reactor
