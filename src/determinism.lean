import data.finset
import data.set.finite

/- Reactor Primitives -/

-- A reactor's state fields and ports are represented as maps from (a fixed set of) indices to
-- (possibly absent) values. Single ports and state fields can therefore be identified by values
-- of these maps' domains (i.e. indices).
namespace reactor

  inductive value : Type*
  instance : decidable_eq value := sorry

  def ports (n : ℕ) := (fin n) → (option value)
  def state (n : ℕ) := (fin n) → (option value)

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

  -- A reaction is deterministic, if given equal inputs and states, running the body produces equal
  -- outputs and states. 
  -- Since a reaction's body is a function, determinism is trivially fulfilled.
  theorem determinism {nᵢ nₒ nₛ : ℕ } (r : reaction nᵢ nₒ nₛ) (i₁ i₂ : input r.dᵢ) (s₁ s₂ : state nₛ) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body i₁ s₁) = (r.body i₂ s₂) := 
    assume h, congr (congr_arg r.body h.left) h.right

end reaction

/- Reactions -/

namespace reactor 

  -- The `reactions` type describes a non-empty list of reactions, which are thereby given an
  -- implicit order.
  -- In this simplified model of reactors, precendece between reactions arises *only* from an
  -- *explicit* ordering. The precedence *graph* of reactions therefore collapses to a *list*.
  inductive reactions (nᵢ nₒ nₛ : ℕ)
    | just  (r : reaction nᵢ nₒ nₛ) : reactions
    | chain (head : reaction nᵢ nₒ nₛ) (tail : reactions) : reactions

end reactor
open reactor

/- Reactor -/

structure reactor {nᵢ nₒ nₛ : ℕ} :=
  (inputs : ports nᵢ)
  (outputs : ports nₒ)
  (st : state nₛ)
  (rs : reactions nᵢ nₒ nₛ)

namespace reactor 

  private def input_from_ports {n : ℕ} (dᵢ : finset (fin n)) (p : ports n) : input dᵢ :=
    λ i : {d // d ∈ dᵢ}, p i

  private def ports_from_output {n : ℕ} {dₒ : finset (fin n)} (o: output dₒ) : ports n :=
    λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none

  private def merge_ports {n : ℕ} (first : ports n) (last : ports n) : ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

  private lemma lt_le_trans {n₁ n₂ n₃ : ℕ} : (n₁ < n₂ ∧ n₂ ≤ n₃) → n₁ < n₃ := sorry
  private lemma fn {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : fin n₁ → fin n₂ := λ i, ⟨↑i, lt_le_trans ⟨i.is_lt, h⟩⟩
  private lemma fn_inj {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : function.injective (fn h) := sorry
  private lemma exp_ind {nᵢ : ℕ} (is : finset (fin nᵢ)) (n : ℕ) (h : nᵢ ≤ n) : finset (fin n) := is.map ⟨fn h, fn_inj h⟩  

  private def run' {nᵢ nₒ nₛ : ℕ} : (ports nᵢ) → (state nₛ) → (reactions nᵢ nₒ nₛ) → (ports nₒ × state nₛ)
    | p s (reactions.just r) :=
      let normed_trigs : finset (fin nᵢ) := finset.map (λ t, ↑t) r.triggers in
      let vs := normed_trigs.image p in
      if vs = ⟨none, refl⟩  
      then let os := r.body (input_from_ports r.dᵢ p) s in 
           ⟨ports_from_output os.1, os.2⟩ 
      else ⟨(λ _, none), s⟩ 
      
    | p s (reactions.chain h t)
      := let fos := h.body (input_from_ports h.dᵢ p) s in
         let tps := run' p fos.2 t in
         ⟨merge_ports (ports_from_output fos.1) tps.1, tps.2⟩ 

  def run {nᵢ nₒ nₛ : ℕ} (r : @reactor nᵢ nₒ nₛ) : @reactor nᵢ nₒ nₛ :=
     
  --? Prove some theorems about `run` to show that it has desired behavior.

end reactor

/--

/- Reactor Precedence List -/

namespace reactor

  -- In this simple model of reactors, precendece between reactions arises *only* from an explicit
  -- ordering (not reactor-internal dependencies). The precedence *graph* therefore collapses to a
  -- *list* which codifies the order implicitly.
  -- The list is also used as the means of collecting all of the reactions of a reactor.
  -- An own type is chosen over `list`, to disallow empty lists.
  inductive precedence_list
    | single (r : reaction) : precedence_list
    | chain (first : reaction) (later : precedence_list) : precedence_list

  namespace precedence_list

    -- Merges two outputs in such a way that all of the non-`ε` values of `o₁` override the values
    -- in `o₂`.
    --? Require proof that lengths of o1/2 are equal and equal o.
    private def merge (o₁ o₂ : output) : output := sorry

    -- Cf. `process`.
    private def process' : (input × output × state) → (precedence_list) → (output × state)
      | ios (single r)  := let os := r ⟨ios.1, ios.2.2⟩ in 
                           ⟨merge os.1 ios.2.1, os.2⟩ 
      | ios (chain f l) := let os := f ⟨ios.1, ios.2.2⟩ in
                           let os' := process' ⟨ios.1, os.1, os.2⟩ l in
                           ⟨merge os.1 os'.1, os'.2⟩ 

    -- Basic reactions process their input directly, since they are functions. A collection 
    -- (precedence-list) of reactions uses the following mechanism, to go from input to singular
    -- final output.
    -- Reactions were defined as functions that only change the state or return outputs different
    -- from `ε`s (cf. `reaction`) *if* they consider themselves to be dependent on the given input.
    -- In turn, to compute the result of a collection of reactions for a given input, the input can
    -- simply be fed through the precendence list, from one reaction to the next.
    -- If a reaction changes the state, this updated state will be passed along to the next
    -- reaction.
    -- If a reaction produces output, this output will be merged onto a cumulative outputs-value
    -- that is carried along the processing-chain (cf. `process'`).
    -- If a reaction is definitionally considered to not trigger on the given input, its output
    -- will change neither the state- nor outputs-value that is carried along the processing-chain.
    -- To implement this functionality, a seperate `process'` function is used, that can carry the
    -- outputs.
    def process : (input × state) → (precedence_list) → (output × state)
      | is (single r)  := r is
      | is (chain f l) := let os := f is in
                          process' ⟨is.1, os.1, os.2⟩ l

    -- A collection (precendence-list) of reactions is deterministic, if given equal inputs, the
    -- results of processing them is equal. 
    -- Since `process` is a function, determinism is trivially fulfilled.
    theorem deterministic (p : precedence_list) (is₁ is₂ : input × state) : 
      is₁ = is₂ → (process is₁ p) = (process is₂ p) :=
      assume h : is₁ = is₂, 
      congr (congr_arg process h) (refl p)

  end precedence_list

/- Sequential Processing -/

namespace reactor

  namespace sequential
    
    -- Given a list of inputs, an initial state and a collection of reactions, `process` computes the
    -- result (state and outputs) of processing the inputs sequentially, starting in the given state.
    -- Any outputs and changes to the state produced along the way. are captured in the resulting
    -- list.
    -- This is akin to `reactor.precedence_list.process`, with the difference being that (a) the
    -- basic unit of processing is now an entire precende-list (that is used repeatedly) instead of
    -- just single reactions and (b) the outputs are listed individually rather than merged. The 
    -- state is passed along from iteration to iteration though, just like before.
    def process : list input → state → precedence_list → list (output × state)
      | []        _ _ := []
      | (iₕ :: iₜ) s p := let os' := precedence_list.process ⟨iₕ, s⟩ p in
                         os' :: (process iₜ os'.2 p) 

    -- Processing a sequential input to a collection of reactions is deterministic, if given equal 
    -- inputs, the results of processing them is equal. 
    -- Since `process` is a function, determinism is trivially fulfilled.
    theorem deterministic (p : precedence_list) (i₁ i₂ : list input) (s₁ s₂ : state) :
      (i₁ = i₂ ∧ s₁ = s₂) → (process i₁ s₁ p) = (process i₂ s₂ p) :=
      assume h : i₁ = i₂ ∧ s₁ = s₂,
      congr (congr (congr_arg process h.left) h.right) (refl p)

  end sequential

end reactor

/- Reactor -/

-- At any given time a reactor has values (or lack thereof via `ε`) for its input and output ports
-- as well as its state. The processing of values is performed by its reactions, which should only
-- ever receive the reactor's own input values and state as input. The result of processing should
-- only ever be written back to the reactor itself.
structure old_reactor :=
  (input_count : ℕ)
  (output_count : ℕ)
  («input» : vector value input_count)
  («output» : vector value output_count)
  («state» : state)
  (reactions : precedence_list)

namespace reactor 

  -- Processing a computation for a single unconnected reactor consists of (1) processing its input
  -- and state through its reactions (2) writing the resulting output and state back to the reactor
  -- and (3) wiping the reactor's input (setting them all to `ε`).
  def process (r : reactor) : reactor :=
    let os := precedence_list.process ⟨r.input, r.state⟩ r.reactions in
    let i' := sorry in -- Make a list of `r.input.length` many `ε`s.
    ⟨i', os.1, os.2, r.reactions⟩ 

  -- Processing a computation of a single unconnected reactor is deterministic, if given equal
  -- inputs, the resulting reactors are equal. 
  -- Since `process` is a function, determinism is trivially fulfilled.
  theorem deterministic (r₁ r₂ : reactor) : 
    r₁ = r₂ → process r₁ = process r₂ :=
    assume h : r₁ = r₂,
    congr_arg process h

end reactor

/- Reactor Network -/

namespace reactor 

  -- By defining the `reactors` as a list instead of a set, we remove the need for identifiers and
  -- use the index into the list as a reactor's identifier.
  structure network { rc : ℕ } :=
    (reactors : vector reactor rc)
    --? have this be a digraph of (ℕ × ℕ) instead (where each vertex can have at most one incoming edge)
    (connections (si di : fin reactors.length) : (fin (vector.nth reactors si).output_count) → (fin (vector.nth reactors di).input_count)) 

  namespace network

    -- reactor.network.process should use the fixed-point approach from *dataflow with firing*.
    -- reaching a fixed point is equivalent to the global reaction-queue being computed until it is empty
    -- (which would then induce the next time-stamp to be run. without actions a reactor system will only have
    -- one time stamp (because there are no actions to increase them), so the fixed point is a static final state?)

    -- order.basic contains a definition of `monotone`
    -- order.directed contains a definition of `directed`

  end network

end reactor

-/