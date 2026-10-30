/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constants of the modified step (v2)

Definition `bp:p2s2:constantsB` (`blueprint/parts/p2s2-modified.tex`, `blueprint-I/parts/p2s2-iso-modified.tex`),
verbatim from `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt`; the exact mirror is `stageB` of
`scripts/apost_sharp/thresholds_v2.py`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2

/-- The inputs of one modified step: caps, Hamiltonian bounds, small-divisor constants, ratios, the bite, the strip,
the weight `λ`, and `ḡ = γ̄`. -/
structure StepIn where
  n : ℕ
  κ : ℝ
  M1 : ℝ
  M2 : ℝ
  sK : ℝ
  sLt : ℝ
  sB : ℝ
  sN : ℝ
  sNt : ℝ
  sT : ℝ
  t : ℝ
  c : ℝ
  c1 : ℝ
  cbar : ℝ
  θ : ℝ
  θξ : ℝ
  θΩ : ℝ
  q : ℝ
  lam : ℝ
  γb : ℝ
  δ : ℝ
  r : ℝ
  /-- isoenergetic step (`bpI:p2s2:constants`): frequency bound, energy-row bound, `|D²H|`, energy weight -/
  iso : Bool := false
  Θ : ℝ := 0
  y0 : ℝ := 0
  Mh2 : ℝ := 0
  lamW : ℝ := 1

/-- The constants of `bp:p2s2:constantsB` (verbatim; mirror `stageB` of `thresholds_v2.py`). -/
structure StepConsts where
  CΩ : ℝ
  CE : ℝ
  CDE : ℝ
  CNN : ℝ
  C0 : ℝ
  CxiN : ℝ
  CKt : ℝ
  CDLt : ℝ
  CDLtT : ℝ
  CEt : ℝ
  QtN : ℝ
  CgL : ℝ
  CxiL : ℝ
  CDK : ℝ
  CEb : ℝ
  CG : ℝ
  CBb : ℝ
  CNb : ℝ
  CNbT : ℝ
  CDT : ℝ
  QbN : ℝ
  QL : ℝ
  Q : ℝ

/-- Blueprint `bp:p2s2:constantsB`. -/
def stepConsts (p : StepIn) : StepConsts :=
  let n : ℝ := p.n
  let g := p.γb * p.δ ^ p.κ
  let g1 := g * p.δ
  let sKt := (1 + p.θ) * p.sK
  let CΩ := 2 * (n - 1) * p.c1
  let CEL := (p.sK + p.sN * p.q) / (1 - p.q ^ 2)
  let CEN := (p.sN + p.sK * p.q) / (1 - p.q ^ 2)
  let CE := p.lam * CEL + g * CEN
  let CDE := n * (p.sK + p.sN) * (max p.lam g + (p.sLt + p.sNt) * CE) / (1 - p.q)
  let CNN := n * (p.lam + p.sNt * CE)
  let avgB := p.cbar * (p.δ / p.r) ^ p.κ
  let C0 := if p.iso then p.sT * max (p.lam + p.t * avgB) (p.lamW + p.y0 * avgB) else p.sT * (p.lam + p.t * avgB)
  let CxiN := C0 + p.c
  let CKt := p.sN * CxiN
  let CDLt := n * p.sN * (C0 + p.c1)
  let CDLtT := 2 * n * p.sN * (C0 + p.c1)
  let CdN := (p.M1 * p.sK + n) * p.sB + p.sN * ((p.sLt * p.M1 + 2 * n) * p.sK + p.sLt * (p.M1 * p.sK + n)) * p.sB
  let CXN := p.M1 * p.sN + CdN
  let CEt := CE + CXN * CxiN + p.sN * g + p.M2 / 2 * CKt + (if p.iso then sKt * p.Θ * C0 else 0)
  let QtN := CDLtT * CEt + CNN * CxiN + p.δ * p.sLt * (p.M2 / 2) * CKt ^ 2
  let CgL := p.lam + p.t * CxiN + (if p.iso then p.Θ * C0 else 0)
  let CxiL := p.c * CgL
  let CDK := sKt * CxiL + g * CKt
  let CEb := CEt + sKt * CgL
  let CG := n * p.sLt + 2 * n * p.sK
  let CBb := p.sB ^ 2 * CG * CDK / (1 - p.θ)
  let CNb := n * CDK * p.sB + p.sK * CBb
  let CNbT := CBb * p.sLt + 2 * n * CDK * p.sB
  let w := 2 * p.M1 * p.sLt * p.sK + 2 * n * p.sK + n * p.sLt
  let CDT0 := 2 * p.M1 * (CNbT * p.sN + p.sNt * CNb) + 2 * p.M2 * p.sNt * p.sN * CDK * p.δ +
    g * (2 * p.sNt * p.sB * CDE + 2 * p.sB ^ 3 * w * CΩ)
  let CDT := if p.iso then max (CDT0 + p.Θ * C0 * g1) (n * p.Θ * C0 * g1 + 2 * n * g1) else CDT0
  let QbN := (1 + n * p.θξ) * (1 + p.θΩ) * QtN +
    (if p.iso then (1 + n * p.θξ) * p.Θ * CΩ * QtN * C0 * p.θξ / CxiL else 0)
  let QL0 := p.sNt * (p.M2 / 2) * CKt ^ 2 * g1 + p.sB ^ 2 * CΩ * g ^ 2 + n * p.sNt * CEt * CxiL +
    p.sNt * CgL * (n * sKt * CxiL + g * CDLt) + CNbT * CEb
  let QL := if p.iso then max (QL0 + C0 * CgL * g1 + C0 * p.sNt * CDLt * p.Θ * g)
      (p.Mh2 / 2 * CKt ^ 2 * g1 + n * QtN * p.θξ * (p.Θ * CΩ + g1)) else QL0
  ⟨CΩ, CE, CDE, CNN, C0, CxiN, CKt, CDLt, CDLtT, CEt, QtN, CgL, CxiL, CDK, CEb, CG, CBb, CNb, CNbT, CDT, QbN, QL,
    max QL (2 ^ p.κ * QbN)⟩

/-- The step conditions of `bp:p2s2:constantsB` at the normalised weighted error `X`. -/
def stepCond (p : StepIn) (X : ℝ) : Prop :=
  let k := stepConsts p
  let g := p.γb * p.δ ^ p.κ
  max 1 (p.sB ^ 2) * k.CΩ * g * X ≤ p.q ∧ k.CDE * g * X ≤ p.n ∧ k.CxiL * X ≤ p.θξ ∧
    k.CΩ * k.CgL * X ≤ p.θΩ ∧ k.CKt * (g * p.δ) * X ≤ 1 ∧ k.CDLt * g * X ≤ p.θ * p.sK ∧
    k.CDLtT * g * X ≤ p.θ * p.sLt ∧ p.sB * k.CG * k.CDK * X ≤ p.θ ∧ p.sT * k.CDT * X ≤ p.θ ∧
    2 ^ (p.κ + 1) * k.Q * X ≤ 1

end KAM.Sharp2
