import ReactorModel.Components.Reactor

open Reactor
open Reactor.Ports

variable {ι υ} [ID ι] [Value υ]

def List.isNetIDPathFor (i : ι) (ctx : ι ▸ Reactor ι υ) : List ι → Prop
  | [] => false
  | hd :: tl => ∃ rtr, ctx hd = some rtr ∧ (tl *ᵣ[rtr.raw] i)

notation p " *ₙ[" n "] " i => List.isNetIDPathFor i n p

noncomputable def Finmap.portIDs (rtrs : ι ▸ Reactor ι υ) (r : Ports.Role) : Finset ι :=
  rtrs.values.bUnion (λ x => (x.ports r).ids)

variable (ι υ)

structure Network where
  rtrs : ι ▸ Reactor ι υ
  cns : Finset (Connection ι) 
  wfCns : ∀ c, c ∈ cns → (c.src ∈ rtrs.portIDs Role.out) ∧ (c.dst ∈ rtrs.portIDs Role.in)
  uniquePortIns : ∀ c₁ c₂, c₁ ∈ cns → c₂ ∈ cns → c₁.dst = c₂.dst → c₁ = c₂
  wfIDs : ∀ i₁ i₂ p₁ p₂, (p₁ *ₙ[rtrs] i₁) → (p₂ *ₙ[rtrs] i₂) → i₁ = i₂ → p₁ = p₂ --⚡️ References `Raw` -> Wrap this with a theorem

variable {ι υ}

def Reactor.nest (rtr : Reactor ι υ) : Network ι υ := 
  let rawRtrs : Finmap ι (Raw.Reactor ι υ) := {lookup := rtr.raw.nest.rtrs, finite := rtr.wf.nestFiniteRtrs}
  {
    rtrs := rawRtrs.map (λ r => {raw := r, wf := sorry}),
    cns := rtr.raw.nest.cns,
    wfCns := sorry,
    uniquePortIns := sorry,
    wfIDs := sorry
  }