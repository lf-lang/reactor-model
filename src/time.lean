-- Let Σ be a set. 
-- We refer to the elements of Σ as identifiers.
-- There is no need to further define the structure of identifiers.
--
-- Will be called I.

-- Let 𝔙 be a set, which we refer to as the set of values.
-- We do not assume any structure in the values, i.e., reactors are untyped.
-- We define one distinguished element in the value set: ε ∈ 𝔙 is called the absent value.
--
-- Will be called V.

-- Each tag is denoted by a pair,
-- of which the first element is a time value -
-- an integer representation of time in some predefined unit (e.g., milliseconds or nanoseconds) -
-- and the second element denotes a microstep index.

namespace tag

-- Definition 0
structure T := (time_val : ℕ) (microstep_index : ℕ)
variables t₁ t₂ : T

protected def lt : Prop := 
(t₁.time_val < t₂.time_val) ∨ 
(t₁.time_val = t₂.time_val ∧ t₁.microstep_index < t₂.microstep_index)

instance : has_lt T := ⟨tag.lt⟩ 

-- Definition 0
protected def plus : T := 
⟨t₁.time_val + t₂.time_val, t₁.microstep_index + t₂.microstep_index⟩

instance : has_add T := ⟨tag.plus⟩ 

end tag

namespace event

-- Definition 1
--? V has to have the "absent value" ε, which is currently handled by `option`'s `none`.
--? The names V and I are originally 𝔙 and Σ.
structure Event (I V : Type*) := 
(event_trigger : I) 
(trigger_value : option V)
(event_tag : tag.T)

--? There would also be the option here to define e₂ : Event I' V'
-- Definition 1
protected def lt {I V : Type*} (e₁ e₂ : Event I V) : Prop := 
e₁.event_tag < e₂.event_tag

instance {I V : Type*} : has_lt (Event I V) := ⟨event.lt⟩ 

--! Definition 2
--! The name queue is actually 𝒬*sub*E.
protected def queue {I V : Type*} : list (Event I V) := sorry

end event

