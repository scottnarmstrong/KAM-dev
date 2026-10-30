/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The constants of route A (v2)

Definition `bp:p2s2:constantsA` (`blueprint/parts/p2s2-modified.tex`), the additive step with the
levers L1–L3 and L8; the mirror is `stageA` of `scripts/apost_sharp/thresholds_v2.py` with the
options
`L1, torsion_cap, omega_eta, avg_full_bite, keep_delta, caps_tilde` (row A7 of the design document).

`StepInA` holds the inputs of one bite. `δ` is the value of the bite *used in the constants*: the
step
lemmas apply to every actual bite `≤ δ`, so one record serves a stage of the prefix (`δ = δ_s`) and
all
of the tail (`δ = δ_k`). The exponent is `a = 2κ`, and `g = γ̄ δ^κ`.
-/

@[expose] public noncomputable section

namespace KAM.Sharp2.RouteA

/-- The inputs of one additive step: dimension, exponent, Hamiltonian bounds, caps, torsion cap `t`,
small-divisor constant `c` of the bite, average constant `ca`, `γ̄`, the bite, the ratio `ϑ`; the
last
four fields are the isoenergetic inputs (`Θ ≥ |ω|`, the energy-row bound `HY`, `|D²H| ≤ Mh2`). -/
structure StepInA where
  n : ℕ
  κ : ℝ
  M1 : ℝ
  M2 : ℝ
  sK : ℝ
  sB : ℝ
  sT : ℝ
  sLt : ℝ
  sN : ℝ
  sNt : ℝ
  t : ℝ
  c : ℝ
  ca : ℝ
  γb : ℝ
  δ : ℝ
  th : ℝ
  iso : Bool := false
  Θ : ℝ := 0
  HY : ℝ := 0
  Mh2 : ℝ := 0

namespace StepInA

variable (p : StepInA)

/-- `g = γ̄ δ^κ`. -/
def g : ℝ := p.γb * p.δ ^ p.κ
/-- `C_Ω = 2(n - 1) c σ_{Lᵀ}` (`bp:p2s2:omega` with the Cauchy bite `δ`). -/
def COm : ℝ := 2 * ((p.n : ℝ) - 1) * p.c * p.sLt
/-- `C_sym = max {1, σ_B²} C_Ω`. -/
def CSym : ℝ := max 1 (p.sB ^ 2) * p.COm
/-- `C_red = n max {σ_{Nᵀ}, σ_{Lᵀ} + 2σ_N}`. -/
def CRed : ℝ := p.n * max p.sNt (p.sLt + 2 * p.sN)
/-- `w = 2 M₁ σ_{Lᵀ} σ_K + 2n σ_K + n σ_{Lᵀ}`. -/
def w : ℝ := 2 * p.M1 * p.sLt * p.sK + (2 * p.n * p.sK + p.n * p.sLt)
/-- `C_S`: the constant of `ξᴺ₀` (and of `ξ^ω`). -/
def CS : ℝ :=
  if p.iso then p.sT * max (p.sNt * p.g + p.t * p.ca * p.sLt) (p.g + p.ca * p.HY * p.sLt)
  else p.sT * (p.sNt * p.g + p.t * p.ca * p.sLt)
/-- `C_ξᴺ = C_S + c σ_{Lᵀ}`. -/
def CXiN : ℝ := p.CS + p.c * p.sLt
/-- `C_g = t C_ξᴺ + Θ C_S + σ_{Nᵀ} g`. -/
def CG : ℝ := p.t * p.CXiN + p.Θ * p.CS + p.sNt * p.g
/-- `C_∂ξ = max {C_g, σ_{Lᵀ} g}`. -/
def CDXi : ℝ := max p.CG (p.sLt * p.g)
/-- `C_ξ = max {c C_g, g C_ξᴺ}`. -/
def CXi : ℝ := max (p.c * p.CG) (p.g * p.CXiN)
/-- `C_ΔK = σ_K c C_g + σ_N g C_ξᴺ`. -/
def CDK : ℝ := p.sK * p.c * p.CG + p.sN * p.g * p.CXiN
/-- `C_lin = C_red C_ξ + C_sym C_∂ξ + Θ C_Ω C_S`. -/
def CLin : ℝ := p.CRed * p.CXi + p.CSym * p.CDXi + p.Θ * p.COm * p.CS
/-- `|P| ≤ σ_K + σ_N`. -/
def P : ℝ := p.sK + p.sN
/-- `C_Δω = Θ g C_S`. -/
def CDw : ℝ := p.Θ * p.g * p.CS
/-- `C_P ≥ |∂_ω P|`. -/
def CFr : ℝ := (p.M1 * p.sK + p.n) * (1 + p.sB) +
  p.sN * ((p.sLt * p.M1 + 2 * p.n) * p.sK + p.sLt * (p.M1 * p.sK + p.n)) * p.sB
/-- `C_∂K = C_P C_ξ + |P| g C_∂ξ`. -/
def CdK : ℝ := p.CFr * p.CXi + p.P * p.g * p.CDXi
/-- `C_E`, the invariance branch. -/
def CE1 : ℝ := 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * p.CLin + p.M2 / 2 * p.CDK ^ 2 +
  (if p.iso then p.g * p.CS * p.CdK else 0)
/-- `C_E`, the energy branch. -/
def CE2 : ℝ := p.γb * p.δ ^ (p.κ - 1) * p.n * (p.sLt * p.g + p.Θ * p.COm) * p.c * p.CG +
  p.Mh2 / 2 * p.CDK ^ 2
/-- `C_E`: the new error is `≤ C_E ε²/(γ⁴ δ^{2a})`. -/
def CE : ℝ := if p.iso then max p.CE1 p.CE2 else p.CE1
/-- `C_G = n σ_{Lᵀ} + 2n σ_K` (caps for the barred factors, L8). -/
def CGr : ℝ := p.n * p.sLt + 2 * p.n * p.sK
/-- `C_B = σ_B² C_G / (1 - ϑ)`. -/
def CB : ℝ := p.sB ^ 2 * p.CGr / (1 - p.th)
/-- `C_N̄ = n σ_B + σ_K C_B`. -/
def CNd : ℝ := p.n * p.sB + p.sK * p.CB
/-- `C_N̄ᵀ = C_B σ_{Lᵀ} + 2n σ_B`. -/
def CNtd : ℝ := p.CB * p.sLt + 2 * p.n * p.sB
/-- `C_Δab = 2 M₁ (C_N̄ᵀ σ_N + σ_{Nᵀ} C_N̄) + 2 M₂ σ_{Nᵀ} σ_N δ`. -/
def CDab : ℝ := 2 * p.M1 * (p.CNtd * p.sN + p.sNt * p.CNd) + 2 * p.M2 * p.sNt * p.sN * p.δ
/-- `C_Δc = σ_B³ w (2n σ_K + n σ_{Lᵀ})`. -/
def CDc : ℝ := p.sB ^ 3 * p.w * (2 * p.n * p.sK + p.n * p.sLt)
/-- The torsion rate `C_ΔT`. -/
def CDT0 : ℝ := (p.CDab + p.CDc) * p.CDK + 2 * p.n * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ)) +
  2 * p.sB ^ 3 * p.w * p.COm * p.g
/-- The rate of the (bordered) averaged torsion. -/
def CDT : ℝ := if p.iso then
    max (p.CDT0 + p.CDw * p.δ) (p.n * p.CDw * p.δ + 2 * p.n * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ)))
  else p.CDT0
/-- The rate of `⟨T⟩⁻¹`. -/
def rT : ℝ := p.sT ^ 2 / (1 - p.th) * p.CDT

/-- The step conditions at the normalised error `x = ε/(γ⁴ δ^{2a})`: `ε ≤ δ`, `|E_sym| ≤ 1/2`,
`ε̄ ≤ ε`, and the Neumann conditions of `⟨T⟩` and of `G`. -/
structure Cond (x : ℝ) : Prop where
  err : p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x ≤ 1
  sym : p.CSym * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x ≤ 1 / 2
  quad : p.CE * x ≤ 1
  twist : p.sT * p.CDT * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th
  gram : p.sB * p.CGr * p.CDK * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th

end StepInA

end KAM.Sharp2.RouteA

end
