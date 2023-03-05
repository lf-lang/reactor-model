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

open Reactor (Component)

class ReactorType (α : Type _) where
  ports : α → ID ⇀ Port             
  acts :  α → ID ⇀ Time.Tag ⇀ Value 
  state : α → ID ⇀ Value            
  rcns :  α → ID ⇀ Reaction         
  nest :  α → ID ⇀ α      

abbrev ReactorType.componentType [ReactorType α] : Component → Type _
  | .rtr => α 
  | .rcn => Reaction
  | .prt => Port
  | .act => Time.Tag ⇀ Value
  | .stv => Value

abbrev ReactorType.cmp? [inst : ReactorType α] : (cmp : Component) → α → ID ⇀ inst.componentType cmp
  | .rtr => nest 
  | .rcn => rcns
  | .prt => ports
  | .act => acts
  | .stv => state

open ReactorType

inductive Lineage [ReactorType α] (cmp : Component) (i : ID) : α → Type _ 
  | final : i ∈ (cmp? cmp rtr).ids → Lineage cmp i rtr
  | nest : (nest rtr₁ j = some rtr₂) → (Lineage cmp i rtr₂) → Lineage cmp i rtr₁
  
def Lineage.container [ReactorType α] {cmp} {rtr : α} : Lineage cmp i rtr → Identified α
  | nest _ (nest h l)              => container (nest h l)
  | nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
  | _                              => { id := ⊤, obj := rtr }

class ReactorType.Indexable (α) extends ReactorType α where
  uniqueIDs : ∀ {rtr : α} {cmp i}, Subsingleton (Lineage cmp i rtr)

namespace ReactorType.Indexable

open Classical in
noncomputable def con? 
    [ReactorType.Indexable α] (rtr : α) (cmp : Component) (i : ID) : Option (Identified α) := 
  if l : Nonempty (Lineage cmp i rtr) then l.some.container else none

noncomputable def obj? [inst : ReactorType.Indexable α] (rtr : α) : 
    (cmp : Component) → cmp.idType ⇀ inst.componentType cmp
  | .rcn, i       => con? rtr .rcn i >>= (cmp? .rcn ·.obj i)
  | .prt, i       => con? rtr .prt i >>= (cmp? .prt ·.obj i)
  | .act, i       => con? rtr .act i >>= (cmp? .act ·.obj i)
  | .stv, i       => con? rtr .stv i >>= (cmp? .stv ·.obj i)
  | .rtr, .nest i => con? rtr .rtr i >>= (cmp? .rtr ·.obj i)
  | .rtr, ⊤       => rtr

notation rtr "[" cmp "][" i "]" => ReactorType.Indexable.obj? rtr cmp i
notation rtr "[" cmp "][" i "]&" => ReactorType.Indexable.con? rtr cmp i

end ReactorType.Indexable

open ReactorType.Indexable

-- About the `↔`-condition in `prio`:  We want to establish a dependency between mutations with 
-- priorities  as well normal reactions with priorities, but not between normal reactions and
-- mutations. Otherwise a normal reaction might take precedence over a mutation. Also the precedence
-- of mutations over normal reactions is handled by `mutNorm` - so this would potentially just 
-- create  a redundancy.
inductive Dependency [ReactorType.Indexable α] (rtr : α) : ID → ID → Prop
  | prio :
    (rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) → (rtr[.rcn][i₁] = some rcn₁) → 
    (rtr[.rcn][i₂] = some rcn₂) → (rcn₁.Mutates ↔ rcn₂.Mutates) → (rcn₁.prio > rcn₂.prio) → 
    Dependency rtr i₁ i₂
  | mutNorm : 
    (rtr[.rcn][iₘ]& = rtr[.rcn][iₙ]&) → (rtr[.rcn][iₘ] = some m) → (rtr[.rcn][iₙ] = some n) →
    (m.Mutates) → (n.Normal) → Dependency rtr iₘ iₙ
  | depOverlap :
    (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) →
    (rcn₁.deps .out ∩ rcn₂.deps .in).Nonempty → Dependency rtr i₁ i₂
  | mutNest :
    (rtr[.rcn][iₘ] = some m) → (m.Mutates) → (rtr[.rcn][iₘ]& = some rtr₁) →
    (nest rtr₁.obj j = some rtr₂) → (iᵣ ∈ (rcns rtr₂).ids) → Dependency rtr iₘ iᵣ
  | trans : 
    Dependency rtr i₁ i₂ → Dependency rtr i₂ i₃ → Dependency rtr i₁ i₃

def Dependency.Acyclic [ReactorType.Indexable α] (rtr : α) : Prop :=
  ∀ i, ¬Dependency rtr i i 

variable [ReactorType.Indexable α]

theorem Dependency.Acyclic.nested {rtr₁ : α} (a : Acyclic rtr₁) (h : nest rtr₁ i = some rtr₂) : 
    Acyclic rtr₂ :=
  sorry

theorem obj?_lift {rtr₁ : α} {cmp o} {j : ID} 
    (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[cmp][j] = some o) : rtr₁[cmp][j] = some o := by
  sorry

-- Note: By `ho` we get `rtr₂ = rtr₃`.
theorem obj?_lift_root {rtr₁ : α} (h : nest rtr₁ i = some rtr₂) (ho : rtr₂[.rtr][⊤] = some rtr₃) : 
    ∃ j, rtr₁[.rtr][j] = some rtr₃ := by
  sorry

namespace ReactorType.Wellformed

inductive NormalDependency (rtr : α) (i : ID) (k : Kind) : Prop
  | act  (h : i ∈ (acts rtr).ids)
  | prt  (h : ports rtr i = some ⟨v, k⟩)
  | nest (c : nest rtr j = some con) (h : ports con i = some ⟨v, k.opposite⟩)

inductive MutationDependency (rtr : α) (i : ID) : Kind → Prop
  | act  : (i ∈ (acts rtr).ids)                                    → MutationDependency rtr i k
  | prt  : (ports rtr i = some ⟨v, k⟩)                             → MutationDependency rtr i k
  | nest : (nest rtr j = some con) → (ports con i = some ⟨v, .in⟩) → MutationDependency rtr i .out

structure _root_.ReactorType.Wellformed (rtr : α) : Prop where
  uniqueInputs : (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → (rtr[.prt][i] = some ⟨v, .in⟩) → (i ∈ rcn₁.deps .out) → (i ∉ rcn₂.deps .out)  
  overlapPrio  : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.deps .out ∩ rcn₂.deps .out).Nonempty → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  impurePrio   : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (¬rcn₁.Pure) → (¬rcn₂.Pure)                → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  mutationPrio : (rtr[.rtr][i] = some con) → (rcns con i₁ = some rcn₁) → (rcns con i₂ = some rcn₂) → (i₁ ≠ i₂) → (rcn₁.Mutates) → (rcn₂.Mutates)            → (rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio)
  normalDeps   : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Normal)  → (d ∈ rcn.deps k) → (NormalDependency con d k) 
  mutationDeps : (rtr[.rtr][i] = some con) → (rcns con j = some rcn) → (rcn.Mutates) → (d ∈ rcn.deps k) → (MutationDependency con d k) 
  acyclicDeps  : Dependency.Acyclic rtr

open Lean in set_option hygiene false in
scoped macro "wf_nested_proof " name:ident : term => `(
  @fun
  | .nest i => ($(mkIdentFrom name $ `wf ++ name.getId) $ obj?_lift h ·)
  | .root   => ($(mkIdentFrom name $ `wf ++ name.getId) <| obj?_lift_root h · |>.choose_spec)
)

theorem nested {rtr₁ : α} (wf : Wellformed rtr₁) (h : nest rtr₁ i = some rtr₂) : Wellformed rtr₂ where
  uniqueInputs h₁ h₂ h₃ h₄ := wf.uniqueInputs (obj?_lift h h₁) (obj?_lift h h₂) h₃ (obj?_lift h h₄) 
  overlapPrio              := wf_nested_proof overlapPrio
  impurePrio               := wf_nested_proof impurePrio
  mutationPrio             := wf_nested_proof mutationPrio
  normalDeps               := wf_nested_proof normalDeps
  mutationDeps             := wf_nested_proof mutationDeps
  acyclicDeps              := wf.acyclicDeps.nested h

end ReactorType.Wellformed

class ReactorType.Proper (α) extends ReactorType.Indexable α where
  wellformed : ∀ rtr : α, Wellformed rtr