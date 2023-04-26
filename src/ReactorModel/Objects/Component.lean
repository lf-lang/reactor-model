import ReactorModel.Primitives

inductive Component.Valued
  | inp -- Input port
  | out -- Output port
  | stv -- State variable
  | act -- Action

-- An enumeration of the different *kinds* of components that are addressable by ids in a reactor.
inductive Component (ε) [CoeSort ε Type]
  | val (v : Component.Valued)
  | rcn         -- Reactions
  | rtr         -- Nested reactors
  | ext (e : ε) -- Extensions

namespace Component

abbrev Valued.type : Valued → Type
  | inp => Value
  | out => Value
  | stv => Value 
  | act => Action -- TODO: Change the way events are handled.

variable [CoeSort ε Type]

@[match_pattern] abbrev inp : Component ε := val .inp
@[match_pattern] abbrev out : Component ε := val .out
@[match_pattern] abbrev act : Component ε := val .act
@[match_pattern] abbrev stv : Component ε := val .stv

instance : Coe Component.Valued (Component ε) where
  coe := val 

-- The type of `WithTop ID`s extends the type of `ID`s with a `⊤` ID witch is used to refer to a/the
-- top level reactor. We don't include the `⊤` ID in the normal `ID` type, as most contexts require
-- that the `⊤` ID cannot not be used. For example, it should not be possible for a reaction to be
-- identified by the `⊤` ID. 
abbrev idType : Component ε → Type
  | rtr => WithTop ID
  | _   => ID

instance {cpt : Component ε} : Coe ID cpt.idType where
  coe i :=
    match cpt with 
    | .val _ | .rcn | .rtr | .ext _ => i
  
end Component