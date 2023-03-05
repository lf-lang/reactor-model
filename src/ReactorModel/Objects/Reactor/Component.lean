import ReactorModel.Objects.Reaction

namespace Reactor

-- An enumeration of the different *kinds* of components that are addressable by IDs in a reactor.
inductive Component
  | rtr -- Nested reactors
  | rcn -- Reactions
  | prt -- Ports
  | act -- Actions
  | stv -- State variables

namespace Component

abbrev idType : Component → Type _
  | rtr => RootedID
  | _   => ID

instance {cmp : Component} : Coe ID cmp.idType where
  coe i :=
    match cmp with
    | .rtr => .nest i
    | .rcn | .prt | .act | .stv => i

end Component
end Reactor