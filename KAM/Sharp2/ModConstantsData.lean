/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModConstants

/-!
# Admissible step inputs and the `let`s of `stepConsts`

`StepIn.Ok` (nonnegative data, `n ≥ 1`, ratios in `[0, 1)`), `StepIn.Le` (the order in which the
engine varies the inputs: small-divisor constants `c`, `c¹`, `c̄`, bite `δ`, caps, weights, `γ̄`
increase; exponent, ratios, strip and step kind are fixed), and one definition per `let` of
`stepConsts` (`stepConsts_eq` in `ModConstantsMono` is `rfl`).
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

/-- The step inputs are admissible: nonnegative data, `n ≥ 1`, ratios in `[0, 1)`. -/
structure StepIn.Ok (p : StepIn) : Prop where
  n1 : 1 ≤ p.n
  κ0 : 0 ≤ p.κ
  r0 : 0 < p.r
  δ0 : 0 ≤ p.δ
  M1 : 0 ≤ p.M1
  M2 : 0 ≤ p.M2
  sK : 0 ≤ p.sK
  sLt : 0 ≤ p.sLt
  sB : 0 ≤ p.sB
  sN : 0 ≤ p.sN
  sNt : 0 ≤ p.sNt
  sT : 0 ≤ p.sT
  t : 0 ≤ p.t
  c : 0 ≤ p.c
  c1 : 0 ≤ p.c1
  cbar : 0 ≤ p.cbar
  θ0 : 0 ≤ p.θ
  θ1 : p.θ < 1
  θξ0 : 0 ≤ p.θξ
  θΩ0 : 0 ≤ p.θΩ
  q0 : 0 ≤ p.q
  q1 : p.q < 1
  lam : 0 ≤ p.lam
  γb : 0 ≤ p.γb
  Θ : 0 ≤ p.Θ
  y0 : 0 ≤ p.y0
  Mh2 : 0 ≤ p.Mh2
  lamW : 0 ≤ p.lamW

/-- `p ≼ p'`: same exponent, ratios, strip and step kind; every other input is larger. -/
structure StepIn.Le (p p' : StepIn) : Prop where
  n : p'.n = p.n
  κ : p'.κ = p.κ
  r : p'.r = p.r
  θ : p'.θ = p.θ
  θξ : p'.θξ = p.θξ
  θΩ : p'.θΩ = p.θΩ
  q : p'.q = p.q
  iso : p'.iso = p.iso
  M1 : p.M1 ≤ p'.M1
  M2 : p.M2 ≤ p'.M2
  sK : p.sK ≤ p'.sK
  sLt : p.sLt ≤ p'.sLt
  sB : p.sB ≤ p'.sB
  sN : p.sN ≤ p'.sN
  sNt : p.sNt ≤ p'.sNt
  sT : p.sT ≤ p'.sT
  t : p.t ≤ p'.t
  c : p.c ≤ p'.c
  c1 : p.c1 ≤ p'.c1
  cbar : p.cbar ≤ p'.cbar
  lam : p.lam ≤ p'.lam
  γb : p.γb ≤ p'.γb
  δ : p.δ ≤ p'.δ
  Θ : p.Θ ≤ p'.Θ
  y0 : p.y0 ≤ p'.y0
  Mh2 : p.Mh2 ≤ p'.Mh2
  lamW : p.lamW ≤ p'.lamW

theorem StepIn.Le.refl (p : StepIn) : p.Le p :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem StepIn.Ok.mono {p p' : StepIn} (h : p.Ok) (hl : p.Le p') : p'.Ok where
  n1 := by rw [hl.n]; exact h.n1
  κ0 := by rw [hl.κ]; exact h.κ0
  r0 := by rw [hl.r]; exact h.r0
  δ0 := h.δ0.trans hl.δ
  M1 := h.M1.trans hl.M1
  M2 := h.M2.trans hl.M2
  sK := h.sK.trans hl.sK
  sLt := h.sLt.trans hl.sLt
  sB := h.sB.trans hl.sB
  sN := h.sN.trans hl.sN
  sNt := h.sNt.trans hl.sNt
  sT := h.sT.trans hl.sT
  t := h.t.trans hl.t
  c := h.c.trans hl.c
  c1 := h.c1.trans hl.c1
  cbar := h.cbar.trans hl.cbar
  θ0 := by rw [hl.θ]; exact h.θ0
  θ1 := by rw [hl.θ]; exact h.θ1
  θξ0 := by rw [hl.θξ]; exact h.θξ0
  θΩ0 := by rw [hl.θΩ]; exact h.θΩ0
  q0 := by rw [hl.q]; exact h.q0
  q1 := by rw [hl.q]; exact h.q1
  lam := h.lam.trans hl.lam
  γb := h.γb.trans hl.γb
  Θ := h.Θ.trans hl.Θ
  y0 := h.y0.trans hl.y0
  Mh2 := h.Mh2.trans hl.Mh2
  lamW := h.lamW.trans hl.lamW

/-- `0 ≤ x p ≤ x p'`. -/
def Bd (x : StepIn → ℝ) (p p' : StepIn) : Prop := 0 ≤ x p ∧ x p ≤ x p'

/-! ### One definition per `let` of `stepConsts` -/

/-- `γ̄ δ^κ`. -/
def og (p : StepIn) : ℝ := p.γb * p.δ ^ p.κ
def oKt (p : StepIn) : ℝ := (1 + p.θ) * p.sK
def oCΩ (p : StepIn) : ℝ := 2 * ((p.n : ℝ) - 1) * p.c1
def oCEL (p : StepIn) : ℝ := (p.sK + p.sN * p.q) / (1 - p.q ^ 2)
def oCEN (p : StepIn) : ℝ := (p.sN + p.sK * p.q) / (1 - p.q ^ 2)
def oCE (p : StepIn) : ℝ := p.lam * oCEL p + og p * oCEN p
def oCDE (p : StepIn) : ℝ :=
  (p.n : ℝ) * (p.sK + p.sN) * (max p.lam (og p) + (p.sLt + p.sNt) * oCE p) / (1 - p.q)
def oCNN (p : StepIn) : ℝ := (p.n : ℝ) * (p.lam + p.sNt * oCE p)
def sAvgB (p : StepIn) : ℝ := p.cbar * (p.δ / p.r) ^ p.κ
def oC0 (p : StepIn) : ℝ :=
  if p.iso then p.sT * max (p.lam + p.t * sAvgB p) (p.lamW + p.y0 * sAvgB p)
  else p.sT * (p.lam + p.t * sAvgB p)
def oCxiN (p : StepIn) : ℝ := oC0 p + p.c
def oCKt (p : StepIn) : ℝ := p.sN * oCxiN p
def oCDLt (p : StepIn) : ℝ := (p.n : ℝ) * p.sN * (oC0 p + p.c1)
def oCDLtT (p : StepIn) : ℝ := 2 * (p.n : ℝ) * p.sN * (oC0 p + p.c1)
def oCdN (p : StepIn) : ℝ :=
  (p.M1 * p.sK + p.n) * p.sB +
    p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB
def oCXN (p : StepIn) : ℝ := p.M1 * p.sN + oCdN p
def oCEt (p : StepIn) : ℝ :=
  oCE p + oCXN p * oCxiN p + p.sN * og p + p.M2 / 2 * oCKt p +
    (if p.iso then oKt p * p.Θ * oC0 p else 0)
def oQtN (p : StepIn) : ℝ :=
  oCDLtT p * oCEt p + oCNN p * oCxiN p + p.δ * p.sLt * (p.M2 / 2) * oCKt p ^ 2
def oCgL (p : StepIn) : ℝ := p.lam + p.t * oCxiN p + (if p.iso then p.Θ * oC0 p else 0)
def oCxiL (p : StepIn) : ℝ := p.c * oCgL p
def oCDK (p : StepIn) : ℝ := oKt p * oCxiL p + og p * oCKt p
def oCEb (p : StepIn) : ℝ := oCEt p + oKt p * oCgL p
def oCG (p : StepIn) : ℝ := (p.n : ℝ) * p.sLt + 2 * (p.n : ℝ) * p.sK
def oCBb (p : StepIn) : ℝ := p.sB ^ 2 * oCG p * oCDK p / (1 - p.θ)
def oCNb (p : StepIn) : ℝ := (p.n : ℝ) * oCDK p * p.sB + p.sK * oCBb p
def oCNbT (p : StepIn) : ℝ := oCBb p * p.sLt + 2 * (p.n : ℝ) * oCDK p * p.sB
def ow (p : StepIn) : ℝ := 2 * p.M1 * p.sLt * p.sK + 2 * (p.n : ℝ) * p.sK + (p.n : ℝ) * p.sLt
def sCDT0 (p : StepIn) : ℝ :=
  2 * p.M1 * (oCNbT p * p.sN + p.sNt * oCNb p) + 2 * p.M2 * p.sNt * p.sN * oCDK p * p.δ +
    og p * (2 * p.sNt * p.sB * oCDE p + 2 * p.sB ^ 3 * ow p * oCΩ p)
def sCDT (p : StepIn) : ℝ :=
  if p.iso then max (sCDT0 p + p.Θ * oC0 p * (og p * p.δ))
    ((p.n : ℝ) * p.Θ * oC0 p * (og p * p.δ) + 2 * (p.n : ℝ) * (og p * p.δ)) else sCDT0 p
def oQbN (p : StepIn) : ℝ :=
  (1 + (p.n : ℝ) * p.θξ) * (1 + p.θΩ) * oQtN p +
    (if p.iso then (1 + (p.n : ℝ) * p.θξ) * p.Θ * oCΩ p * oQtN p * oC0 p * p.θξ / oCxiL p else 0)
def sQL0 (p : StepIn) : ℝ :=
  p.sNt * (p.M2 / 2) * oCKt p ^ 2 * (og p * p.δ) + p.sB ^ 2 * oCΩ p * og p ^ 2 +
    (p.n : ℝ) * p.sNt * oCEt p * oCxiL p +
    p.sNt * oCgL p * ((p.n : ℝ) * oKt p * oCxiL p + og p * oCDLt p) + oCNbT p * oCEb p
def oQL (p : StepIn) : ℝ :=
  if p.iso then max (sQL0 p + oC0 p * oCgL p * (og p * p.δ) + oC0 p * p.sNt * oCDLt p * p.Θ * og p)
    (p.Mh2 / 2 * oCKt p ^ 2 * (og p * p.δ) +
      (p.n : ℝ) * oQtN p * p.θξ * (p.Θ * oCΩ p + og p * p.δ)) else sQL0 p


end KAM.Sharp2

end
