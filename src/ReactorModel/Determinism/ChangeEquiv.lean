import ReactorModel.Execution

open Classical

def PortChangeEquiv (cs₁ cs₂ : List $ Identified Change) : Prop :=
  ∀ i, cs₁.lastSome? (·.obj.portValue? i) = cs₂.lastSome? (·.obj.portValue? i)

infix:50 " ⋈ₚ " => PortChangeEquiv

theorem PortChangeEquiv.refl (cs) : cs ⋈ₚ cs := by simp [PortChangeEquiv]

def StateChangeEquiv (cs₁ cs₂ : List $ Identified Change) : Prop :=
  ∀ i, cs₁.lastSome? (·.obj.stateValue? i) = cs₂.lastSome? (·.obj.stateValue? i)

infix:50 " ⋈ₛ " => StateChangeEquiv

theorem StateChangeEquiv.refl (cs) : cs ⋈ₛ cs := by simp [StateChangeEquiv]

def ActionChangeEquiv (cs₁ cs₂ : List $ Identified Change) : Prop :=
  ∀ i t, cs₁.filterMap (·.obj.actionValue? i t) = cs₂.filterMap (·.obj.actionValue? i t)

infix:50 " ⋈ₐ " => ActionChangeEquiv

theorem ActionChangeEquiv.refl (cs) : cs ⋈ₐ cs := by simp [ActionChangeEquiv]

-- Note: Mutations are currently noops, and can therefore be ignored.
structure ChangeEquiv (cs₁ cs₂ : List $ Identified Change) : Prop where
  ports   : cs₁ ⋈ₚ cs₂
  state   : cs₁ ⋈ₛ cs₂ 
  actions : cs₁ ⋈ₐ cs₂ 

infix:50 " ⋈ " => ChangeEquiv

theorem ChangeEquiv.refl (cs) : cs ⋈ cs where 
  ports   := PortChangeEquiv.refl _
  state   := StateChangeEquiv.refl _
  actions := ActionChangeEquiv.refl _