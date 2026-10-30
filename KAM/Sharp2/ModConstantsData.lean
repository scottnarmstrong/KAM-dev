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
def sg (p : StepIn) : ℝ := p.γb * p.δ ^ p.κ
def sKt (p : StepIn) : ℝ := (1 + p.θ) * p.sK
def sCΩ (p : StepIn) : ℝ := 2 * ((p.n : ℝ) - 1) * p.c1
def sCEL (p : StepIn) : ℝ := (p.sK + p.sN * p.q) / (1 - p.q ^ 2)
def sCEN (p : StepIn) : ℝ := (p.sN + p.sK * p.q) / (1 - p.q ^ 2)
def sCE (p : StepIn) : ℝ := p.lam * sCEL p + sg p * sCEN p
def sCDE (p : StepIn) : ℝ :=
  (p.n : ℝ) * (p.sK + p.sN) * (max p.lam (sg p) + (p.sLt + p.sNt) * sCE p) / (1 - p.q)
def sCNN (p : StepIn) : ℝ := (p.n : ℝ) * (p.lam + p.sNt * sCE p)
def sAvgB (p : StepIn) : ℝ := p.cbar * (p.δ / p.r) ^ p.κ
def sC0 (p : StepIn) : ℝ :=
  if p.iso then p.sT * max (p.lam + p.t * sAvgB p) (p.lamW + p.y0 * sAvgB p)
  else p.sT * (p.lam + p.t * sAvgB p)
def sCxiN (p : StepIn) : ℝ := sC0 p + p.c
def sCKt (p : StepIn) : ℝ := p.sN * sCxiN p
def sCDLt (p : StepIn) : ℝ := (p.n : ℝ) * p.sN * (sC0 p + p.c1)
def sCDLtT (p : StepIn) : ℝ := 2 * (p.n : ℝ) * p.sN * (sC0 p + p.c1)
def sCdN (p : StepIn) : ℝ :=
  (p.M1 * p.sK + p.n) * p.sB +
    p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB
def sCXN (p : StepIn) : ℝ := p.M1 * p.sN + sCdN p
def sCEt (p : StepIn) : ℝ :=
  sCE p + sCXN p * sCxiN p + p.sN * sg p + p.M2 / 2 * sCKt p +
    (if p.iso then sKt p * p.Θ * sC0 p else 0)
def sQtN (p : StepIn) : ℝ :=
  sCDLtT p * sCEt p + sCNN p * sCxiN p + p.δ * p.sLt * (p.M2 / 2) * sCKt p ^ 2
def sCgL (p : StepIn) : ℝ := p.lam + p.t * sCxiN p + (if p.iso then p.Θ * sC0 p else 0)
def sCxiL (p : StepIn) : ℝ := p.c * sCgL p
def sCDK (p : StepIn) : ℝ := sKt p * sCxiL p + sg p * sCKt p
def sCEb (p : StepIn) : ℝ := sCEt p + sKt p * sCgL p
def sCG (p : StepIn) : ℝ := (p.n : ℝ) * p.sLt + 2 * (p.n : ℝ) * p.sK
def sCBb (p : StepIn) : ℝ := p.sB ^ 2 * sCG p * sCDK p / (1 - p.θ)
def sCNb (p : StepIn) : ℝ := (p.n : ℝ) * sCDK p * p.sB + p.sK * sCBb p
def sCNbT (p : StepIn) : ℝ := sCBb p * p.sLt + 2 * (p.n : ℝ) * sCDK p * p.sB
def sw (p : StepIn) : ℝ := 2 * p.M1 * p.sLt * p.sK + 2 * (p.n : ℝ) * p.sK + (p.n : ℝ) * p.sLt
def sCDT0 (p : StepIn) : ℝ :=
  2 * p.M1 * (sCNbT p * p.sN + p.sNt * sCNb p) + 2 * p.M2 * p.sNt * p.sN * sCDK p * p.δ +
    sg p * (2 * p.sNt * p.sB * sCDE p + 2 * p.sB ^ 3 * sw p * sCΩ p)
def sCDT (p : StepIn) : ℝ :=
  if p.iso then max (sCDT0 p + p.Θ * sC0 p * (sg p * p.δ))
    ((p.n : ℝ) * p.Θ * sC0 p * (sg p * p.δ) + 2 * (p.n : ℝ) * (sg p * p.δ)) else sCDT0 p
def sQbN (p : StepIn) : ℝ :=
  (1 + (p.n : ℝ) * p.θξ) * (1 + p.θΩ) * sQtN p +
    (if p.iso then (1 + (p.n : ℝ) * p.θξ) * p.Θ * sCΩ p * sQtN p * sC0 p * p.θξ / sCxiL p else 0)
def sQL0 (p : StepIn) : ℝ :=
  p.sNt * (p.M2 / 2) * sCKt p ^ 2 * (sg p * p.δ) + p.sB ^ 2 * sCΩ p * sg p ^ 2 +
    (p.n : ℝ) * p.sNt * sCEt p * sCxiL p +
    p.sNt * sCgL p * ((p.n : ℝ) * sKt p * sCxiL p + sg p * sCDLt p) + sCNbT p * sCEb p
def sQL (p : StepIn) : ℝ :=
  if p.iso then max (sQL0 p + sC0 p * sCgL p * (sg p * p.δ) + sC0 p * p.sNt * sCDLt p * p.Θ * sg p)
    (p.Mh2 / 2 * sCKt p ^ 2 * (sg p * p.δ) +
      (p.n : ℝ) * sQtN p * p.θξ * (p.Θ * sCΩ p + sg p * p.δ)) else sQL0 p


end KAM.Sharp2

end
