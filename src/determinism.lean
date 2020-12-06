import data.finset
import data.set.finite

-- open classical
-- local attribute [instance, priority 0] prop_decidable

/- Reactor Primitives -/

-- A reactor's state fields and ports are represented as maps from (a fixed set of) indices to
-- (possibly absent) values. Single ports and state fields can therefore be identified by values
-- of these maps' domains (i.e. indices).
--
--? It should be possible to extract the "core" of these definitions into a single definition and
--? then just have `ports` and `state` be typealiases for that core.
namespace reactor

  inductive value : Type*
  instance : decidable_eq value := sorry

  def ports (n : ℕ) := (fin n) → (option value)
  def state (n : ℕ) := (fin n) → (option value)

  def ports.absent {n : ℕ} : ports n := λ _, none

end reactor
open reactor

/- Reaction -/

-- Mappings from *exactly* a given set of {in,out}put dependency-indices to (possibly absent)
-- values.
--? It should be possible to extract the "core" of these definitions into a single definition and
--? then just have `input` and `output` be typealiases for that core.
namespace reaction 

  def input  {nᵢ : ℕ} (dᵢ : finset (fin nᵢ)) := {i // i ∈ dᵢ} → (option value)
  def output {nₒ : ℕ} (dₒ : finset (fin nₒ)) := {o // o ∈ dₒ} → (option value)

end reaction
open reaction

-- Reactions consist of a set of input dependencies `dᵢ`, output dependencies `dₒ`, `triggers` and
-- a function `body` that transforms a given input map and state to an output map and a new state.
-- Since *actions* are not defined in this simplified model of reactors, the set of `triggers` is
-- simply a subset of the input dependencies `dᵢ`.
--
--? Define the body as a relation, define what determinism means for reactions (namely that the
--? relation is actually a function), and then prove that determinism holds for more complex
--? objects if the reactions themselves are deterministic.
--? That way it would be more clear what is actually being shown: reactors are deterministic, if
--? the underlying reaction body (the foreign code) behaves like a function.
--
--? Define a coercion from reactions with smaller bounds to ones with higher bounds, if necessary.
structure reaction (nᵢ nₒ nₛ : ℕ) :=
  (dᵢ : finset (fin nᵢ)) 
  (dₒ : finset (fin nₒ))
  (triggers : finset {i // i ∈ dᵢ})
  (body : input dᵢ → state nₛ → (output dₒ × state nₛ)) 

namespace reaction

  -- (1) Get R's triggers T.
  -- (2) Coerce the elements in T to be the input type of P.
  -- (3) Get the codomain C of (T through P).
  -- (4) Erase the absent value (`none`) from C.
  -- (4) If C is empty (contained nothing but the absent value), R is not triggered by P.
  def is_triggered_by {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) (is : ports nᵢ) : Prop :=
    let ts : finset (fin nᵢ) := r.triggers.map ⟨λ i, ↑i, subtype.coe_injective⟩ in
    let i : finset (option value) := ts.image is in
    let vs := i.erase none in
    vs.nonempty

  instance {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) (is : ports nᵢ) : decidable (is_triggered_by r is) := sorry

  -- A reaction is deterministic, if given equal inputs and states, running the body produces equal
  -- outputs and states. 
  -- Since a reaction's body is a function, determinism is trivially fulfilled.
  theorem determinism {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) (i₁ i₂ : input r.dᵢ) (s₁ s₂ : state nₛ) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body i₁ s₁) = (r.body i₂ s₂) := 
    assume h, congr (congr_arg r.body h.left) h.right

end reaction

/- Reactor -/

structure reactor (nᵢ nₒ nₛ : ℕ) :=
  (inputs : ports nᵢ)
  (outputs : ports nₒ)
  (st : state nₛ)
  (rs : list (reaction nᵢ nₒ nₛ))

namespace reactor 

  instance ports_to_input {n : ℕ} {dᵢ : finset (fin n)} : has_lift (ports n) (input dᵢ) :=
    ⟨λ p, λ i : {d // d ∈ dᵢ}, p i⟩

  instance output_to_ports {n : ℕ} {dₒ : finset (fin n)} : has_lift (output dₒ) (ports n) :=
    ⟨λ o, λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none⟩

  -- TEMPORARY (ports_to_input)
  private def lift_ {n : ℕ} {dᵢ : finset (fin n)} : (ports n) → (input dᵢ) :=
    λ p, λ i : {d // d ∈ dᵢ}, p i
  -- TEMPORARY (output_to_ports)
  private def lift_ {n : ℕ} {dₒ : finset (fin n)} : (output dₒ) → (ports n) :=
    λ o, λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none

  private def merge_ports {n : ℕ} (first : ports n) (last : ports n) : ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

  private def run' {nᵢ nₒ nₛ : ℕ} : (ports nᵢ) → (state nₛ) → (list (reaction nᵢ nₒ nₛ)) → (ports nₒ × state nₛ)
    | i s [] := ⟨ports.absent, s⟩ 
    | i s (rₕ :: rₜ) := 
      let osₕ : ports nₒ × state nₛ := 
        if rₕ.is_triggered_by i
        then let os := rₕ.body (lift_ i) s in ⟨(lift_ os.1), os.2⟩ 
        else ⟨ports.absent, s⟩ in
      let osₜ := run' i osₕ.2 rₜ in
      ⟨merge_ports osₕ.1 osₜ.1, osₜ.2⟩

  --? Prove some theorems about `run` to show that it has desired behavior.
  def run {nᵢ nₒ nₛ : ℕ} (r : reactor nᵢ nₒ nₛ) : reactor nᵢ nₒ nₛ :=
    let os := run' r.inputs r.st r.rs in
    ⟨ports.absent, os.1, os.2, r.rs⟩ 

  -- Running a single unconnected reactor is deterministic, if equal initial states lead to equal
  -- end states.
  -- Since `reactor.run` is a function, determinism is trivially fulfilled.
  theorem deterministic {nᵢ nₒ nₛ : ℕ} (r₁ r₂ : reactor nᵢ nₒ nₛ) : 
    r₁ = r₂ → run r₁ = run r₂ :=
    assume h, congr_arg run h

end reactor

/- Sequential -/

namespace reactor

  namespace sequential
    
    private def run' {nᵢ nₒ nₛ : ℕ} : (reactor nᵢ nₒ nₛ) → list (ports nᵢ) → list (ports nₒ) → (reactor nᵢ nₒ nₛ) × list (ports nₒ) 
      | r [] o := ⟨reactor.run r, o⟩ 
      | r (iₕ :: iₜ) o := 
        let rₕ := reactor.run r in
        let rₜ : (reactor nᵢ nₒ nₛ) := ⟨iₕ, ports.absent, rₕ.st, rₕ.rs⟩ in 
        run' rₜ iₜ (o ++ [rₕ.outputs])

    -- The first input is already within the given reactor, and the last output will also be part
    -- of the output reactor.
    protected def run {nᵢ nₒ nₛ : ℕ} (r : reactor nᵢ nₒ nₛ) (i : list (ports nᵢ)) : (reactor nᵢ nₒ nₛ) × list (ports nₒ) :=
       run' r i []

    -- Passing a finite sequence of inputs through a single unconnected reactor is deterministic,
    -- if equal sequences lead to equal outputs and end states.
    -- Since `reactor.sequence.run` is a function, determinism is trivially fulfilled.
    theorem deterministic {nᵢ nₒ nₛ : ℕ} (r : reactor nᵢ nₒ nₛ) (i₁ i₂ : list (ports nᵢ)) : 
      i₁ = i₂ → (sequential.run r i₁) = (sequential.run r i₂) :=
      assume h, congr (congr_arg sequential.run (refl r)) h 

  end sequential

end reactor

/- Reactor Network -/

namespace reactor 

  namespace network

    class node :=
      (nᵢ nₒ : ℕ)
      (inputs : ports nᵢ)
      (outputs : ports nₒ)
      -- (run : node → node)

    -- Reactors are nodes.
    instance {nᵢ nₒ nₛ : ℕ} {r : reactor nᵢ nₒ nₛ} : node := ⟨nᵢ, nₒ, r.inputs, r.outputs⟩

  end network
  open network

  -- By defining the `reactors` as a list instead of a set, we remove the need for identifiers and
  -- use the index into the list as a reactor's identifier.
  structure network {c : ℕ} :=
    (nodes : vector node c)
    --? have this be a digraph of (ℕ × ℕ) instead (where each vertex can have at most one incoming edge)
    (connections (si di : fin nodes.length) : (fin (vector.nth nodes si).output_count) → (fin (vector.nth nodes di).input_count)) 

  namespace network

    -- reactor.network.process should use the fixed-point approach from *dataflow with firing*.
    -- reaching a fixed point is equivalent to the global reaction-queue being computed until it is empty
    -- (which would then induce the next time-stamp to be run. without actions a reactor system will only have
    -- one time stamp (because there are no actions to increase them), so the fixed point is a static final state?)

    -- order.basic contains a definition of `monotone`
    -- order.directed contains a definition of `directed`

  end network

end reactor
