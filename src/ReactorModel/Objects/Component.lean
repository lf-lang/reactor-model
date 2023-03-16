import ReactorModel.Primitives

namespace Reactor

inductive Component.Valued
  | prt (k : Kind) -- Ports
  | act            -- Actions
  | stv            -- State variables 

-- An enumeration of the different *kinds* of components that are addressable by ids in a reactor.
inductive Component
  | val (v : Component.Valued)
  | rtr -- Nested reactors
  | rcn -- Reactions

namespace Component

abbrev Valued.type : Valued → Type
  | prt _ => Value
  | act   => Action
  | stv   => Value 

@[match_pattern] abbrev prt (k) := Component.val (.prt k)
@[match_pattern] abbrev act     := Component.val .act
@[match_pattern] abbrev stv     := Component.val .stv

instance : Coe Component.Valued Component where
  coe := val 

abbrev idType : Component → Type
  | rtr => RootedID
  | _   => ID

instance {cmp : Component} : Coe ID cmp.idType where
  coe i :=
    match cmp with
    | .rtr => .nest i
    | .rcn | .val _ => i

end Component
end Reactor