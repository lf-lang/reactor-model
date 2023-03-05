import ReactorModel.Objects.Reactor.Core

namespace Reactor

protected structure Raw where
  core : Reactor.Core
  private coreUniqueIDs : ∀ {cmp i} (l₁ l₂ : Core.Lineage cmp i core), l₁ = l₂ 

namespace Raw

protected def ports : Reactor.Raw → ID ⇀ Port             := (·.core.ports)
protected def acts  : Reactor.Raw → ID ⇀ Time.Tag ⇀ Value := (·.core.acts)
protected def state : Reactor.Raw → ID ⇀ Value            := (·.core.state)
protected def rcns  : Reactor.Raw → ID ⇀ Reaction         := (·.core.rcns)

protected def nest (rtr : Reactor.Raw) : ID ⇀ Reactor.Raw :=
  rtr.core.nest.attach.map fun ⟨core, h⟩ => {
    core := core
    coreUniqueIDs := by
      intro _ _ l₁ l₂
      injection rtr.coreUniqueIDs (.nest h.choose_spec l₁) (.nest h.choose_spec l₂)
  }

open Lean in set_option hygiene false in
macro "def_lineage_accessors " ns:ident : command => 
  let namespaced name := mkIdentFrom ns $ ns.getId ++ name
  let reactorType := if ns.getId = `Reactor then ns else mkIdentFrom ns $ `Reactor ++ ns.getId
  let lineageType := mkIdentFrom reactorType $ reactorType.getId ++ `Lineage
  `(
    open Classical in section
    
    def Lineage.container {cmp} : $lineageType cmp i rtr → Identified $reactorType 
    | nest _ (nest h l)              => container (nest h l)
    | nest (rtr₁ := con) (j := j) .. => { id := j, obj := con }
    | _                              => { id := ⊤, obj := rtr }

    noncomputable def con? (rtr : $reactorType ) (cmp : Component) (i : ID) : 
        Option (Identified $reactorType) := 
      if l : Nonempty ($lineageType cmp i rtr) then l.some.container else none

    noncomputable def obj? (rtr : $reactorType) : 
        (cmp : Component) → cmp.idType ⇀ $(namespaced `componentType) cmp
      | .rtr, .nest i => rtr.con? .rtr i >>= (·.obj.cmp? .rtr i)
      | .rtr, ⊤       => rtr
      | .rcn, i       => rtr.con? .rcn i >>= (·.obj.cmp? .rcn i)
      | .prt, i       => rtr.con? .prt i >>= (·.obj.cmp? .prt i)
      | .act, i       => rtr.con? .act i >>= (·.obj.cmp? .act i)
      | .stv, i       => rtr.con? .stv i >>= (·.obj.cmp? .stv i)

    end
  )

def_lineage_type Raw      -- defines `componentType`, `cmp?` and `Lineage`
def_lineage_accessors Raw -- defines `Lineage.container`, `con?` and `obj?`

scoped notation rtr "[" cmp "][" i "]" => Reactor.Raw.obj? rtr cmp i

theorem obj?_lift {cmp o} {j : ID} (h : rtr₁.nest i = some rtr₂) (ho : rtr₂[cmp][j] = some o) :
    rtr₁[cmp][j] = some o := by
  sorry

-- Note: By `ho` we get `rtr₂ = rtr₃`.
theorem obj?_lift_root (h : rtr₁.nest i = some rtr₂) (ho : rtr₂[.rtr][⊤] = some rtr₃) :
    ∃ j, rtr₁[.rtr][j] = some rtr₃ := by
  sorry

-- The lifted version of `coreUniqueIDs`.
theorem uniqueIDs {cmp} (rtr : Reactor.Raw) (l₁ l₂ : Raw.Lineage cmp i rtr) : l₁ = l₂ := by
  sorry

private theorem nest_core_comm (rtr : Reactor.Raw) : 
    rtr.core.nest = rtr.nest.map Raw.core := by
  simp [Raw.nest, Partial.map_map, Function.comp, Partial.attach_map_val]

private theorem ext_iff_core : {rtr₁ rtr₂ : Reactor.Raw} → (rtr₁ = rtr₂ ↔ rtr₁.core = rtr₂.core)
  | mk .., mk .. => by simp

theorem ext_iff {rtr₁ rtr₂ : Reactor.Raw} : 
    rtr₁ = rtr₂ ↔ 
    rtr₁.ports = rtr₂.ports ∧ rtr₁.acts = rtr₂.acts ∧ rtr₁.state = rtr₂.state ∧ 
    rtr₁.rcns = rtr₂.rcns ∧ rtr₁.nest  = rtr₂.nest := by
  simp [ext_iff_core, Reactor.Core.ext_iff, Raw.ports, Raw.state, Raw.rcns, Raw.acts, nest_core_comm]
  intros
  exact {
    mp := Partial.map_inj (by simp [Function.Injective, ext_iff_core])
    mpr := by simp_all
  }

end Raw
end Reactor
