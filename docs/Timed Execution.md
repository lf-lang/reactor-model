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
As a result, if we want to use `inst.network.run'` as part of the timed execution model, we need to provide it with precisely those networks as input that represent the network graph at the given time/execution step - that is, with all action ports correctly populated, etc.
In turn, a large part of this formalization is a result of interfacing between the descriptive and the algorithmic world - that is, having to create precise descriptions of specific networks, to be used by `inst.network.run'`.

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
We call the time-progressed but **pre**-instantaneous version of `τ`, `τₜ` - the definition of "time-progressed" (`→ₜ`) is covered in the next section.

![Execution Step Visualization](images/execution-step.png)

Hence, the definition of `is_execution_step` states that `τ'` must be equal to `τₜ` is all aspects (`actions`, `events`, etc.) except that `τ'.σ = τₜ.σ.run'`.

## Time Steps

The definition of `→ₜ` (`is_time_step`) is broken up into two parts.
This is a result of Lean's unfortunate property that `match` expressions aren't really usable in proofs.
The workaround is to define auxiliary definitions:

```lean
def is_time_step_aux (τ τ' : timed.network υ) : option tag → Prop 
  | none            := ⊥ 
  | (some next_tag) := 
    τ'.time = next_tag ∧ 
    τ'.events = (λ p t, τ.new_events p t <|> τ.events p t) ∧ 
    (τ →ₐ τ')  

def is_time_step (τ τ' : timed.network υ) : Prop := is_time_step_aux τ τ' τ.next_tag
```

A network `τ'` is a time step of a network `τ`, if `τ'` is a pre-instantaneous version of the network that we get by progressing `τ` to the "next event"'s time. To understand this definition, we first need to consider what "event" means in this context.

### Events

In the context of `timed.network` (i.e. a purely *logically* timed network), the only possible events that can occur are the manifestations of logical actions. Logical actions are scheduled by reactions writing corresponding TPAs to OAPs (cf. *PDiR* Section 5).
To achieve a more descriptive view on the entirety of scheduled actions (than scanning OAPs for that information), we define:

```lean
def timed.network.event_map := port.id → tag → option υ

structure timed.network :=
  ...
  (events : event_map υ)
  ...
```

The `event_map` tells us which port is assigned which value at which tag (note that this map is partial). This map will be populated and updated according to the actions scheduled during execution (more on that later). Hence, this map assigns values only to *IAPs* - no other kind of port. 
From this map we can extract useful information like:

```lean
-- The tags for which the given timed network has events scheduled.
-- Note that this set also contains all tags from past events.
def event_tags (τ : timed.network υ) : set tag :=
  { t | ∃ (m : tag → option υ) (h : m ∈ τ.oaps.image τ.events), m t ≠ none }
```

From this we can derive what it means to be the "next tag":

```lean
-- The proposition that a given tag is the next tag for which a given network has a scheduled event.
-- This is the case if the given tag comes after the networks current tag, but is smaller or equal to
-- the tags of all other scheduled events.
def tag_is_next (τ : timed.network υ) (t : tag) : Prop :=
  t ∈ τ.event_tags ∧ (t > τ.time) ∧ (∀ t' ∈ τ.event_tags, t' > τ.time → t ≤ t')
```

Since there can only ever be one next tag, we can also directly define a `next_tag` property on a timed network.
The approach used for this definition is employed a couple of times throughout this formalization:

1. Define a proposition (here: `tag_is_next`).
2. Prove that this proposition is fulfilled by exactly/at most one object (here: `next_tags_subsingleton`).
3. Define that object by extracting it (using `classical`) from the previous proof (here: `next_tag`).

```lean
-- There can only ever be at most one next tag.
lemma next_tags_subsingleton (τ : timed.network υ) : { t | τ.tag_is_next t }.subsingleton := ...

-- The next tag at which an event occurs.
noncomputable def next_tag (τ : timed.network υ) : option tag :=
  (next_tags_subsingleton τ)
    .eq_empty_or_singleton
    .by_cases (λ _, none) (λ s, s.some)
```

The drawback of this approach is that the definition of `next_tag` is pretty opaque, since it only consists of technicalities. 
But the benefit is that we've managed to define it purely descriptively, as a result of `tag_is_next` and `next_tags_subsingleton`.

### Back to `→ₜ`

We use `next_tag` in the definition of `is_time_step` by passing it directly to `is_time_step_aux`: 

```lean
def is_time_step (τ τ' : timed.network υ) : Prop := is_time_step_aux τ τ' τ.next_tag
```

There we split our definition depending on whether `next_tag` is `none` or not. 

```lean
def is_time_step_aux (τ τ' : timed.network υ) : option tag → Prop 
  | none            := ⊥ 
  | (some next_tag) := 
    τ'.time = next_tag ∧ 
    τ'.events = (λ p t, τ.new_events p t <|> τ.events p t) ∧ 
    (τ →ₐ τ')  
```

If it is `none`, then `τ` does not have a next event (i.e. execution has completed), so `τ'` can't be the time progressed version of `τ`. If, on the other hand, we do have `some next_tag`, then we need to make sure that:

1. `τ'`'s time is `next_tag`
2. `τ'`'s event map is up to date
3. all of `τ'`'s ports have values matching the ones defined by the event map

Much like `→ₜ` is a sub-step of `→ₑ`, the `→ₐ` predicate defines the next "lower" layer for `→ₜ` (more on that later). 
A crucial step we're going to consider here first though, is how the updated event map is defined.
Recall that `τ` is post-instantaneous. Hence, its OAPs will contain TPAs that declare events, which are not yet part of the event map.
If we want to make sure that all of `τ'`'s ports have values matching the ones defined by the event map, we first need to update the event map with the information contained in those TPAs. This updated event map is defined as:

```lean
(λ p t, τ.new_events p t <|> τ.events p t)
```

What this definition states is that new events (more on that in a moment) override previously scheduled events. That is, if `τ.new_events` and `τ.events` *both* define a (non-`none`) value for port `p` at tag `t`, then `τ.new_events` takes precedence.

The `new_events` are also an `event_map` which captures exactly those events contained in the given network's OAPs' TPAs:

```lean
noncomputable def new_events (τ : timed.network υ) : event_map υ := 
  λ iap t, ((τ.oaps_for_iap' iap).sort oap_le).mfirst (λ oap, (τ.σ.η.port role.output oap) >>= (λ o, o.map' t))
```

This definition is really opaque, but we can explain it by answering the following question.
Given some IAP `iap` and tag `t`, as well as a set of OAPs: which value should be assigned to `iap` at tag `t` according to the OAPs?
Since IAPs can only be affected by actions from *connected* OAPs, we can focus on only those OAPs connected to `iap`: `(τ.oaps_for_iap' iap)`.
The TPAs in those OAPs will contain tag-value pairs which may or may not have a tag of `t`. That is, there may be none or *multiple* OAPs declaring a value for `iap` at tag `t`. We want to choose the one that was scheduled *last*, as this fits the semantics of reactors by having later "writes" (for lack of a better term) override earlier writes. The OAP written to last will be the one with the lowest priority - so we sort the list of OAPs by priority using the `oap_le` predicate. In this list of OAPs, we still don't know which one will actually contain a tag-value pair where the tag is `t`. So we run through them until we find the first one where this is the case, and use its tag-value pair value as the return value. This concept of "iterate until non-`none`" is performed by `list.mfirst`. The input function to `list.mfirst` simply describes what the "value" for each instance should be. So here we provide a map from an OAP to the value of its tag-value pair with tag `t`, if there is one (the details of this map aren't really important).

## Action Progression

> Much like `→ₜ` is a sub-step of `→ₑ`, the `→ₐ` predicate defines the next "lower" layer for `→ₜ`. 

The purpose of `→ₐ` (`is_action_progression`) is to ensure that as a timed network progresses from one tag to another, its underlying instantaneous network's ports reflect the values defined by the event map (i.e. by scheduled actions).
