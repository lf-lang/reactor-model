import primitives
import reaction

open reactor

-- It would be nice to declare reactors in a similar fashion to reactions.
-- I.e. reactions in themselves declare what they connect to (dᵢ and dₒ).
-- The difference is that reactions themselves are just a single "connection point",
-- so the mapping is a many-to-one (dependencies to reaction).
-- For reactors the mapping would have to be a many to many mapping (other reactors'
-- ports to own ports). This would on the one hand require the number of other reactors
-- to become part of a reactor's type, which seems inelegant. And further the mapping
-- would have to be implemented as a relation between another reactor's ports and the
-- self-reactor's ports. This would in turn also require nᵢ and nₒ to move into a 
-- reactor's type.

structure reactor :=
  {nᵢ nₒ nₛ nᵣ : ℕ}
  (input : ports nᵢ)
  (output : ports nₒ)
  (state : vars nₛ)
  (reactions : vector (reaction.fixed nᵢ nₒ nₛ) nᵣ)

namespace reactor 

  private def merge_ports {n : ℕ} (first last : ports n) : ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

  private def run' {nᵢ nₒ nₛ nᵣ : ℕ} (rs : vector (reaction.fixed nᵢ nₒ nₛ) nᵣ) (i : ports nᵢ) (s : vars nₛ) : ports nₒ × vars nₛ :=
    -- this is not a list anymore, but rather a vector
    list.rec_on rs
      (ports.empty, s)
      (
        λ head tail tail_output,
          let ⟨i_eq, o_eq, s_eq⟩ := head.property in 
          let rₕ : reaction := ↑head in
          let i' := i↑i_eq in
          let s' := s↑s_eq in
          let osₕ : ports nₒ × state nₛ := 
            if rₕ.fires_on i' then 
              let os := rₕ.body ↑i' s' in
              let os'ₒ := (↑os.1)↑(symm o_eq) in
              let os'ₛ := os.2↑(symm s_eq) in
              ⟨os'ₒ, os'ₛ⟩
            else 
              ⟨ports.empty, s⟩ 
          in
            ⟨merge_ports osₕ.1 tail_output.1, tail_output.2⟩
      )

  def run (r : reactor) : reactor :=
    let os := run' r.reactions r.input r.state in
    ⟨ports.empty, os.1, os.2, r.reactions⟩  

  protected theorem volatile_input (r : reactor) : 
    (run r).input = ports.empty :=
    refl (run r).input

  --? Prove the same for state.
  protected theorem no_in_no_out (r : reactor) : 
    r.input = ports.empty → (run r).output = ports.empty :=
    begin 
      assume h,
      rw run,
      simp,
      rw h,
      induction r.reactions,
        rw run',
        {
          rw run',
          simp,
          have no_fire : hd.fires_on ports.empty = false := no_in_no_fire hd,
          -- rw no_fire,
          sorry
        }
    end

  private lemma merge_empty_is_neutral {n : ℕ} (first last : ports n) :
    last = ports.empty → (merge_ports first last) = first := 
    begin
      assume h,
      rw merge_ports,
      simp,
      rw [h, ports.empty],
      simp,
    end

  private lemma merge_skips_empty {n : ℕ} (first last : ports n) (i : fin n) :
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
