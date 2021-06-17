# Timed Execution

*Timed reactor networks and timed execution as presented here, build upon the formalization described in [Provable Determinism in Reactors (PDiR)](https://github.com/marcusrossel/bachelors-thesis/blob/main/Thesis/Thesis.pdf) Section 5, but contain significant changes. Notably `timed.network` no longer has an `event_queue` and the execution model is entirely new.*

---

A *timed execution*, i.e. an execution of a timed network, is a sequence of timed networks such that each network follows as a valid execution step of its predecessor. The main challenge in formalizing this notion is the formalization of what constitutes a *valid execution step*.

## Approach

Timed networks are built upon instantaneous networks:

```lean
structure timed.network :=
  (σ : inst.network (tpa υ))
  (time : tag)
  (events : event_map υ)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)
```

Hence, it'd be useful for the timed execution model to be built upon the instantaneous execution model, as well.
Instantaneous execution is described algorithmically by `inst.network.run'` (a parameter-free version of `inst.network.run` not present in *PDiR*).
This is somewhat unfortunate in that it would be more desirable to have a *descriptive* rather than *algorithmic* formalization of execution (cf. *PDiR* Section 3.6). 
One of the goals in the formalization of timed execution is to make it descriptive.

The connection point between timed and instantaneous execution is *actions*. 
As described in *PDiR*, they are formalized as special ports (cf. `timed.network.actions` and `timed.network.well_formed`).
As a result, if we want to use `inst.network.run'` as part of the timed execution model, we need to provide it with precisely those networks as input that represent the network graph at the given time/execution step --- that is, with all action ports correctly populated, etc.
In turn, a large part of this formalization is a result of interfacing between the descriptive and the algorithmic world --- that is, having to create precise descriptions of specific networks, to be used by `inst.network.run'`.

## Execution Steps

A `timed.execution` is a potentially infinite sequence of timed networks with two rules:

```lean
structure execution (τ : timed.network υ) :=
  (steps : seq (timed.network υ))
  (head : steps.head = τ)
  (succ : ∀ i, steps.nth i →ₑ steps.nth (i + 1))
```

1. `head`: Execution starts on the given network `τ`.
2. `succ`: Each network in the sequence must be a valid execution step (`→ₑ`) of its predecessor.

The interesting part is what constitutes a valid execution step, i.e. how `→ₑ` is formalized.

In Lean `seq`s are sequences that can be finite or infinite.
This is achieved by elements in the sequence being optional with the rule that if any element is `option.none` all of its successors are, too.
Hence, the formalization of `→ₑ` (`is_execution_step`) is a proposition over *optional* networks:

```lean
def is_execution_step : option (timed.network υ) → option (timed.network υ) → Prop 
  | (some τ) none      := τ.next_tag = none
  | none     none      := ⊤
  | none     (some _)  := ⊥
  | (some τ) (some τ') := ∃ τₜ, (τ →ₜ τₜ) ∧ -- τₜ is a time-progressed version of τ
    (τ'.σ = τₜ.σ.run') ∧                   -- τ' must be an executed version of τₜ
    (τ'.time = τₜ.time) ∧                  -- τ' must be at the time of the "next action" (given by τₜ)
    (τ'.events = τₜ.events) ∧              -- τ' must inherit all future events (given by τₜ) [in this case, past events are also inherited]
    (τ'.actions = τₜ.actions)              -- τ' must still have the same actions (action ports and edges) as τ 
```

The first three cases are a formality for dealing with the optionality:

1. The way we handle finite execution in this `seq`-based model is by ending the sequence once the network's execution is complete. 
That is, if there are no more events (actions) to be processed, we require the next element in the sequence to be `none`.
This is formalized by stating that `none` is a valid successor of `some τ` iff `τ` does not have a `next_tag` (more on `next_tag` later).
2. If both elements are `none`, then we've already reached the part of the sequence where execution has ended. 
So `none` is considered a valid successor of `none`.
3. Since `seq`s can never contain `some _` after `none`, this third case can never occur.
 
The only case in which we *really* describe timed execution is when we have to describe whether two timed networks form a valid execution step.
This is also where we have to decide on the following detail of the formalization:

Say we have a timed network `τ` with `τ.time = t` for some tag `t`.
Despite having a fixed current time `t`, there's actually two possible states for `τ`:
Its underlying instantaneous network `τ.σ` could be in the state *before* instantaneous execution, or *after* instantaneous execution for time `t`.
For our formalization we have to decide whether a timed execution sequence should contain pre-instantaneous or post-instantaneous timed networks.  
Here we opt for post-instantaneous timed networks, so that every network in the sequence represents a new time step (this isn't actually important though).

Hence, for `τ'` to be a valid successor of `τ`, `τ'` needs to be the post-instantaneous version of `τ` at the next event's tag.
We call the time-progressed but **pre**-instantaneous version of `τ`, `τₜ` --- the definition of "time-progressed" (`→ₜ`) is covered in the next section.

[../images/execution-step]

Hence, the definition of `is_execution_step` states that `τ'` must be equal to `τₜ` is all aspects (`actions`, `events`, etc.) except that `τ'.σ = τₜ.σ.run'`.

## Time Steps



----

TODO:
* Describe `next_tag`