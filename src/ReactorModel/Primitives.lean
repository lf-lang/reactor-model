import ReactorModel.Extensions

-- A `PresentValue` is a non-absent value.
-- We use this is `Value` to define the complete type of values.
private opaque PresentValue : Type

-- `Value`s are the objects that are consumed and produced by reactions
-- and passed along via ports and actions.
-- The `absent` value is a special value which is used with ports to 
-- represent that a given port is not populated with a value.
inductive Value 
  | absent 
  | present (val : PresentValue)

-- We use IDs to reference various kinds of components like ports, reactions, actions, etc.
-- The precise nature of IDs is not relevant, which is why we define the type as `opaque`.
opaque ID : Type

-- Note: This approach is also used in the implementation of Lean:
--       https://github.com/leanprover/lean4/blob/b81cff/src/Lean/Environment.lean#L18
opaque PrioritySpec : (p : Type) × (PartialOrder p) := ⟨Unit, inferInstance⟩ 

-- The `Priority` type is used to impose a (potentially partial) order on reactions.
def Priority := PrioritySpec.fst

instance : PartialOrder Priority := PrioritySpec.snd

-- The `Kind` type is used to generically distinguish between things which
-- have an "input" and "output" variant. This is the case for ports as well
-- as ports' dependencies. 
inductive Kind
  | «in» 
  | out
deriving DecidableEq

-- When writing functions that are generic over a kind,
-- it is sometimes convenient to talk about the "opposite" kind.
abbrev Kind.opposite : Kind → Kind
  | .in => .out
  | .out => .in

def Time := Nat
deriving LinearOrder

instance : OfNat Time 0 where
  ofNat := .zero

-- A `Time.Tag` is used to represent a logical time tag.
-- The order of these tags is lexicographical with the `time` taking priority.
structure Time.Tag where 
  time : Time
  microstep : Nat
  
instance : OfNat Time.Tag 0 where
  ofNat := ⟨0, 0⟩ 

-- TODO: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Lexicographical.20LinearOrder
instance : LinearOrder Time.Tag := sorry

abbrev Action := Finmap fun _ : Time.Tag => Value

def Action.tags (a : Action) : Finset Time.Tag := a.keys