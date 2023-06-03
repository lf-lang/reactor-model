import ReactorModel.Primitives

inductive Component.Writable
  | inp -- Input port
  | out -- Output port
  | stv -- State variable
  | log -- Logical action

inductive Component.Valued
  | wrt (s : Component.Writable)
  | phy -- Physical action

-- An enumeration of the different *kinds* of components that are addressable by ids in a reactor.
inductive Component
  | val (v : Component.Valued)
  | rtr -- Nested reactors
  | rcn -- Reactions

namespace Component

@[match_pattern] abbrev Valued.inp := Valued.wrt .inp
@[match_pattern] abbrev Valued.out := Valued.wrt .out
@[match_pattern] abbrev Valued.stv := Valued.wrt .stv
@[match_pattern] abbrev Valued.log := Valued.wrt .log

@[match_pattern] abbrev inp := Component.val .inp
@[match_pattern] abbrev out := Component.val .out
@[match_pattern] abbrev stv := Component.val .stv
@[match_pattern] abbrev log := Component.val .log
@[match_pattern] abbrev phy := Component.val .phy

instance : Coe Writable Valued where
  coe := Valued.wrt 

instance : Coe Valued Component where
  coe := val 

-- The type of `WithTop ID`s extends the type of `ID`s with a `⊤` ID witch is used to refer to a/the
-- top level reactor. We don't include the `⊤` ID in the normal `ID` type, as most contexts require
-- that the `⊤` ID cannot not be used. For example, it should not be possible for a reaction to be
-- identified by the `⊤` ID. 
abbrev idType : Component → Type
  | rtr => WithTop ID
  | _   => ID

instance {cpt : Component} : Coe ID cpt.idType where
  coe i :=
    match cpt with 
    | .rtr | .rcn | .val _ => i

end Component