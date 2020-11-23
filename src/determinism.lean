import basic
import data.vector

/- Reactor Primitives -/

-- A reactor's state fields and in-/output-ports are represented as lists of values with a fixed
-- length. Single ports and state values can then be identified by an index into these lists.
--! Using a `vector` makes reactors with different numbers of ports heterogenous, and therefore 
--! un`list`able. Therefore `list` is currently used, which is not optimal.
namespace reactor

  def input  := list value
  def output := list value
  def state  := list value

end reactor

/- Reaction -/

open reactor

-- Given the current state and inputs, a reaction computes a new state and resulting outputs. 
-- 
-- Normally reactions are triggered upon a change to one of the input ports they depend on. In the
-- current definition, this behavior is implicit (i.e. is moved into the reactions themselves).
-- If a reaction wants to declare itself as non-dependent on the given inputs, it should output
-- only `ε`s for the `outputs`, and keep the `state` unchanged. This will then be equivalent to not
-- firing for the given input. 
-- If the reaction *does* change `outputs` or `state`, it is considered to be dependent on the
-- inputs that it used, and was therefore supposed to fire on their changing anyway. 
-- The `outputs` produced by a reaction should contain `ε` for all ports which should remain 
-- unaffected.
--! Can a reaction write `ε` to an output port on purpose, to delete values written there by other
--! reactions?
def reaction := (input × state) → (output × state)

namespace reaction

  -- A reaction is deterministic, if given equal inputs, it produces equal outputs.
  -- Since reactions are functions, determinism is trivially fulfilled.
  theorem deterministic (r : reaction) (is₁ is₂ : input × state) :
    is₁ = is₂ → r is₁ = r is₂ := 
    assume h : is₁ = is₂,
    congr_arg r h

end reaction

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
      | [] _ _ := []
      | (list.cons i_h i_t) s b := let os' := precedence_list.process ⟨i_h, s⟩ b in
                                   list.cons os' (process i_t os'.2 b) 

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
structure reactor :=
  («input» : input)
  («output» : output)
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
  structure network :=
    (reactors : list reactor)
    (connections: (ℕ × ℕ) → (ℕ × ℕ))

end reactor