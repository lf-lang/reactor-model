import ReactorModel.Primitives

inductive Component.Valued
  | inp -- Input port
  | out -- Output port
  | stv -- State variable
  | act -- Action

-- An enumeration of the different *kinds* of components that are addressable by ids in a reactor.
inductive Component
  | val (v : Component.Valued)
  | rtr -- Nested reactors
  | rcn -- Reactions

namespace Component

@[match_pattern] abbrev inp := Component.val .inp
@[match_pattern] abbrev out := Component.val .out
@[match_pattern] abbrev act := Component.val .act
@[match_pattern] abbrev stv := Component.val .stv

instance : Coe Component.Valued Component where
  coe := val

-- The type of `WithTop α`s extends the `Identifiable.Id` type of `α` with a `⊤` ID which is used to
-- refer to a/the top level reactor. We don't include the `⊤` ID in the `Identifiable` type class,
-- as most contexts require that the `⊤` ID cannot not be used. For example, it should not be
-- possible for a reaction to be identified by the `⊤` ID.
abbrev idType (α : Type) [Identifiable α] : Component → Type
  | rtr => WithTop α✦
  | _   => α✦

notation:max α:100 "✦" cpt:100 => Component.idType α cpt

instance [Identifiable α] {cpt : Component} : Coe (α✦) α✦cpt where
  coe i :=
    match cpt with
    | .rtr | .rcn | .val _ => i

end Component
