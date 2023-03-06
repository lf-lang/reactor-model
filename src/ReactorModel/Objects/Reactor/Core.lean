import ReactorModel.Objects.Reactor.TypeClasses.Basic

namespace Reactor

protected inductive Core 
  | mk 
    (ports : ID ⇀ Port)
    (acts :  ID ⇀ Time.Tag ⇀ Value)
    (state : ID ⇀ Value)
    (rcns :  ID ⇀ Reaction)
    (nest :  ID → Option Reactor.Core)

namespace Core

instance : ReactorType Reactor.Core where
  ports | mk p _ _ _ _ => p
  acts  | mk _ a _ _ _ => a
  state | mk _ _ s _ _ => s 
  rcns  | mk _ _ _ r _ => r
  nest  | mk _ _ _ _ n => n

open ReactorType in 
instance : ReactorType.Extensional Reactor.Core where
  ext_iff := by intro (mk ..) (mk ..); simp [ports, state, rcns, acts, nest]

end Core
end Reactor