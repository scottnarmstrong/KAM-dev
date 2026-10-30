/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constants of the repaired modified step (v2, route B)

Definition `bp:p2s2:constantsB` and `bpI:p2s2:constants` (`blueprint/parts/p2s2-modified.tex`,
`blueprint-I/parts/p2s2-iso-modified.tex`), verbatim from
`docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt` (lines wrapped to 100 characters); the
exact mirror is `stageB` of `scripts/apost_sharp/thresholds_v2.py`. The theorems are in
`ModConstantsB`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2


/-- The inputs of one repaired modified step (`bp:p2s2:constantsB`): caps, Hamiltonian data `M₁ M₂
c_Th c_DTh`, the
torsion slack `ts` (so `t = c_Th σ_{Nᵀ} σ_N + ts`), the local torsion budget `bF`, the
small-divisor constants `c`
(bite `δ`), `c1` (Rüssmann-Cauchy, from the split bite), `cavg` (average constant), the ratios, the
schedule ratio `a`,
the weight `λ`, `ḡ = γ̄`, the bite value `δ` used in the constants (the actual bite may be any `δ'
≤ δ`), and the options
L10 (`selfcons`), stage-0 (`stage0`, `ePer = e/μ₀`) and iso. -/
structure StepInB where
  n : ℕ
  κ : ℝ
  M1 : ℝ
  M2 : ℝ
  cTh : ℝ
  cDTh : ℝ
  sK : ℝ
  sLt : ℝ
  sB : ℝ
  sN : ℝ
  sNt : ℝ
  sT : ℝ
  ts : ℝ
  bF : ℝ
  c : ℝ
  c1 : ℝ
  cavg : ℝ
  θ : ℝ
  θξ : ℝ
  θΩ : ℝ
  q : ℝ
  θN : ℝ
  θω : ℝ
  a : ℝ
  lam : ℝ
  γb : ℝ
  δ : ℝ
  selfcons : Bool := false
  stage0 : Bool := false
  ePer : ℝ := 0
  iso : Bool := false
  Θ : ℝ := 0
  y0 : ℝ := 0
  Mh2 : ℝ := 0
  lamW : ℝ := 1

/-- The constants of the repaired step; mirror: `stageB` of `scripts/apost_sharp/thresholds_v2.py`.
-/
structure StepConstsB where
  CΩ : ℝ
  CEL : ℝ
  CEN : ℝ
  CE : ℝ
  CDE : ℝ
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
  Cab : ℝ
  Bsup : ℝ
  Bloc : ℝ
  QbN : ℝ
  QL : ℝ
  Q : ℝ
  Cnu : ℝ

/-- Blueprint `bp:p2s2:constantsB` and `bpI:p2s2:constants` (repaired: torsion against the initial
torus, iso factor
`a_ω = 1 + θ_ω`, polynomial `Q̄_N`, option L10, schedule ratio `a`). -/
def stepConstsB (p : StepInB) : StepConstsB :=
  let n : ℝ := p.n
  let g := p.γb * p.δ ^ p.κ
  let g1 := g * p.δ
  let sKt := (1 + p.θ) * p.sK
  let t := p.cTh * p.sNt * p.sN + p.ts
  let aw : ℝ := if p.iso then 1 + p.θω else 1
  let CΩ := 2 * (n - 1) * p.c1
  let CEL := (p.sK + p.sN * p.q) / (1 - p.q ^ 2)
  let CEN := (p.sN + p.sK * p.q) / (1 - p.q ^ 2)
  let CE0 := p.lam * CEL + g * CEN
  let CE := if p.stage0 then min CE0 p.ePer else CE0
  let CDE0 := n * (p.sK + p.sN) * (max p.lam g + (p.sLt + p.sNt) * CE) / (1 - p.q)
  let CDE := if p.stage0 then min CDE0 (n * p.ePer) else CDE0
  let CNN := n * (p.lam + p.sNt * CE)
  let C0 := if p.iso then p.sT * max (p.lam + t * p.cavg) (p.lamW + p.y0 * p.cavg) else p.sT
      * (p.lam + t * p.cavg)
  let CxiN := C0 + p.c
  let CKt := p.sN * CxiN
  let CDLt := n * p.sN * (C0 + p.c1)
  let CDLtT := 2 * n * p.sN * (C0 + p.c1)
  let CdN := (p.M1 * p.sK + n) * p.sB + p.sN * ((p.sLt * p.M1 + 2 * n) * p.sK + p.sLt * (p.M1
      * p.sK + n)) * p.sB
  let CXN := p.M1 * p.sN + CdN
  let CEt := CE + CXN * CxiN + p.sN * g + p.M2 / 2 * CKt + (if p.iso then sKt * p.Θ * C0 else 0)
  let QtN := CDLtT * CEt + CNN * CxiN + p.δ * p.sLt * (p.M2 / 2) * CKt ^ 2
  let CgL := p.lam + t * CxiN + (if p.iso then p.Θ * C0 else 0)
  let CxiL := p.c * CgL
  let CDK := sKt * CxiL + g * CKt
  let CEb := CEt + aw * sKt * CgL
  let CG := n * p.sLt + 2 * n * p.sK
  let CBb := p.sB ^ 2 * CG * CDK / (1 - p.θ)
  let CNb := n * CDK * p.sB + p.sK * CBb
  let CNbT := CBb * p.sLt + 2 * n * CDK * p.sB
  let w := 2 * p.M1 * p.sLt * p.sK + 2 * n * p.sK + n * p.sLt
  let Cab0 := p.cTh * (CNbT * p.sN + p.sNt * CNb) + p.cDTh * p.sNt * p.sN * CDK * p.δ
  let Cab := if p.iso then max (Cab0 + p.Θ * C0 * g1) (n * p.Θ * C0 * g1) else Cab0
  let Bsup := (p.sNt * p.sB * CDE + p.sB ^ 3 * w * CΩ) * g
  let Bloc := if p.iso then max Bsup (n * g1) else Bsup
  let QbN := if p.iso then (1 + n * p.θξ) * (1 + (1 + aw) * p.θΩ) * QtN else (1 + n * p.θξ) * (1
      + p.θΩ) * QtN
  let QL1 := p.sNt * (p.M2 / 2) * CKt ^ 2 * g1 + p.sB ^ 2 * CΩ * g ^ 2 + n * p.sNt * CEt * CxiL +
    aw * p.sNt * CgL * (n * sKt * CxiL + g * CDLt) +
    (if p.iso then C0 * CgL * g1 + C0 * p.sNt * CDLt * p.Θ * g else 0)
  let QLc := QL1 + CNbT * CEb
  let QLs := if p.selfcons then min QLc ((QL1 + p.θN * (CEN / CEL) * QbN * g) / (1 - p.θN)) else QLc
  let Qw := p.Mh2 / 2 * CKt ^ 2 * g1 + n * QtN * p.θξ * (p.Θ * CΩ + g1)
  let QL := if p.iso then max QLs Qw else QLs
  ⟨CΩ, CEL, CEN, CE, CDE, C0, CxiN, CKt, CDLt, CDLtT, CEt, QtN, CgL, CxiL, CDK, CEb, CG, CBb, CNb,
      CNbT, Cab, Bsup,
    Bloc, QbN, QL, max QL (p.a ^ p.κ * QbN), if p.iso then p.Θ * C0 else 0⟩

/-- The step conditions (`bp:p2s2:constantsB`); every one is `coef · X^p ≤ b` with `coef ≥ 0`. No
Neumann condition
for `⟨T̄⟩` and no local contraction premise (`bp:p2s2:torsion-ref`). -/
def stepCondB (p : StepInB) (X : ℝ) : Prop :=
  let k := stepConstsB p
  let g := p.γb * p.δ ^ p.κ
  max 1 (p.sB ^ 2) * k.CΩ * g * X ≤ p.q ∧ k.CDE * g * X ≤ p.n ∧ k.CxiL * X ≤ p.θξ ∧
    k.CΩ * k.CgL * X ≤ p.θΩ ∧ k.CKt * (g * p.δ) * X ≤ 1 ∧ k.CDLt * g * X ≤ p.θ * p.sK ∧
    k.CDLtT * g * X ≤ p.θ * p.sLt ∧ p.sB * k.CG * k.CDK * X ≤ p.θ ∧ k.Bsup * X ≤ p.ts ∧ k.Bloc * X
        ≤ p.bF ∧
    (p.iso = true → k.C0 * (g * p.δ) * X ≤ p.θω) ∧
    (p.selfcons = true → k.CNbT * k.CEL * X ≤ p.θN ∧
      max 1 (p.sB ^ 2) * (1 + p.n * p.θξ) ^ 2 * k.CΩ * k.QtN * g * X ^ 2 ≤ p.q)

/-- Admissible inputs (`bp:p2s2:data-ok`, audit F1). -/
structure StepInB.Ok (p : StepInB) : Prop where
  one_le_n : 1 ≤ p.n
  one_le_κ : 1 ≤ p.κ
  nonneg : 0 ≤ p.M1 ∧ 0 ≤ p.M2 ∧ 0 ≤ p.cTh ∧ 0 ≤ p.cDTh ∧ 0 ≤ p.Θ ∧ 0 ≤ p.y0 ∧ 0 ≤ p.Mh2 ∧ 0
      ≤ p.ePer
  caps : 0 < p.sK ∧ 0 < p.sLt ∧ 0 < p.sB ∧ 0 < p.sN ∧ 0 < p.sNt ∧ 0 < p.sT
  budgets : 0 < p.ts ∧ 0 < p.bF
  sd : 0 < p.c ∧ 0 < p.c1 ∧ 0 ≤ p.cavg
  ratios : 0 < p.θ ∧ p.θ < 1 ∧ 0 < p.θξ ∧ p.θξ < 1 ∧ 0 < p.θΩ ∧ p.θΩ < 1 ∧ 0 < p.q ∧ p.q < 1 ∧
    0 < p.θN ∧ p.θN < 1 ∧ 0 < p.θω ∧ p.θω < 1
  a_gt : 1 < p.a
  lam : 0 < p.lam ∧ p.lam ≤ 1 ∧ 0 < p.lamW ∧ p.lamW ≤ 1
  γb_pos : 0 < p.γb
  δ_pos : 0 < p.δ
  δ_le : p.δ ≤ 1

/-- `p'` dominates `p` at the tail: same caps and ratios, larger bite, constants and weights. -/
structure StepInB.Dom (p p' : StepInB) : Prop where
  same : p.n = p'.n ∧ p.κ = p'.κ ∧ p.M1 = p'.M1 ∧ p.M2 = p'.M2 ∧ p.cTh = p'.cTh ∧ p.cDTh = p'.cDTh
      ∧ p.sK = p'.sK ∧
    p.sLt = p'.sLt ∧ p.sB = p'.sB ∧ p.sN = p'.sN ∧ p.sNt = p'.sNt ∧ p.sT = p'.sT ∧ p.ts = p'.ts
        ∧ p.bF = p'.bF ∧
    p.θ = p'.θ ∧ p.θξ = p'.θξ ∧ p.θΩ = p'.θΩ ∧ p.q = p'.q ∧ p.θN = p'.θN ∧ p.θω = p'.θω
        ∧ p.a = p'.a ∧ p.γb = p'.γb ∧
    p.selfcons = p'.selfcons ∧ p.iso = p'.iso ∧ p.Θ = p'.Θ ∧ p.y0 = p'.y0 ∧ p.Mh2 = p'.Mh2
  le : p.δ ≤ p'.δ ∧ p.c ≤ p'.c ∧ p.c1 ≤ p'.c1 ∧ p.cavg ≤ p'.cavg ∧ p.lam ≤ p'.lam ∧ p.lamW ≤ p'.lamW
  stage0 : p.stage0 = false ∧ p'.stage0 = false

end KAM.Sharp2

end
