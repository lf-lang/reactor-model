import primitives
import reactor.primitives
import reaction

namespace reactor

  def uniform_reactions (nᵢ nₒ nₛ nᵣ : ℕ) := vector { r : reaction // r.nᵢ = nᵢ ∧ r.nₒ = nₒ ∧ r.nₛ = nₛ } nᵣ

  def ports_to_input {n : ℕ} {dᵢ : finset (fin n)} (p : ports n) : reaction.input dᵢ :=
    λ i : {d // d ∈ dᵢ}, p i

  def output_to_ports {n : ℕ} {dₒ : finset (fin n)} (o : reaction.output dₒ) : ports n :=
    λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none

end reactor

open reactor

--? It would be nice to declare reactors in a similar fashion to reactions.
--? I.e. reactions in themselves declare what they connect to (dᵢ and dₒ).
--? The difference is that reactions themselves are just a single "connection point",
--? so the mapping is a many-to-one (dependencies to reaction).
--? For reactors the mapping would have to be a many to many mapping (other reactors'
--? ports to own ports). This would on the one hand require the number of other reactors
--? to become part of a reactor's type, which seems inelegant. And further the mapping
--? would have to be implemented as a relation between another reactor's ports and the
--? self-reactor's ports. This would in turn also require nᵢ and nₒ to move into a 
--? reactor's type.
structure reactor :=
  {nᵢ nₒ nₛ nᵣ : ℕ}
  (inputs : ports nᵢ)
  (outputs : ports nₒ)
  (st : state nₛ)
  (reactions : uniform_reactions nᵢ nₒ nₛ nᵣ)

namespace reactor 

  private def merge_ports {n : ℕ} (first last : ports n) : ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

  private def run' {nᵢ nₒ nₛ nᵣ: ℕ} (rs : uniform_reactions nᵢ nₒ nₛ nᵣ) (i : ports nᵢ) (s : state nₛ) : ports nₒ × state nₛ :=
    -- this is not a list anymore, but rather a vector
    list.rec_on rs
      (ports.absent, s)
      (
        λ head tail tail_output,
          let ⟨i_eq, o_eq, s_eq⟩ := head.property in 
          let rₕ : reaction := ↑head in
          let i' := convert i i_eq in
          let s' := convert s s_eq in
          let osₕ : ports nₒ × state nₛ := 
            if rₕ.fires_on i' then 
              let os := rₕ.body (ports_to_input i') s' in
              let os'ₒ := convert (output_to_ports os.1) (symm o_eq) in
              let os'ₛ := convert os.2 (symm s_eq) in
              ⟨os'ₒ, os'ₛ⟩
            else 
              ⟨ports.absent, s⟩ 
          in
            ⟨merge_ports osₕ.1 tail_output.1, tail_output.2⟩
      )

  def run (r : reactor) : reactor :=
    let os := run' r.reactions r.inputs r.st in
    ⟨ports.absent, os.1, os.2, r.reactions⟩  

  protected theorem volatile_input (r : reactor) : 
    (run r).inputs = ports.absent :=
    refl (run r).inputs

  --? Prove the same for state.
  protected theorem no_in_no_out (r : reactor) : 
    r.inputs = ports.absent → (run r).outputs = ports.absent :=
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
          have no_fire : hd.fires_on ports.absent = false := no_in_no_fire hd,
          -- rw no_fire,
          sorry
        }
    end

  private lemma merge_absent_is_neutral {n : ℕ} (first last : ports n) :
    last = ports.absent → (merge_ports first last) = first := 
    begin
      assume h,
      rw merge_ports,
      simp,
      rw [h, ports.absent],
      simp,
    end

  private lemma merge_skips_absent {n : ℕ} (first last : ports n) (i : fin n) :
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
