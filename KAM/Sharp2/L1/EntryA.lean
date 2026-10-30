/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Norms
public import KAM.Sharp2.RouteA.Data
public import KAM.Strip.CohomologicalL1Sup
public import KAM.Torus.Objects
public import KAM.Frozen.Defs.Torsion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The ℓ¹ entry of route A: data and constants (package B10c)

Blueprint `bp:p2s2l1:data`, `bp:p2s2l1:constA` of `blueprint/parts/p2s2-l1hybrid.tex`; the repaired
signatures of `docs/campaign/design/APOST-SHARP-V2-L1-SIGNATURES.lean.txt` (AUDIT-B10D-1, F1–F6).

* `FrameL1`, `EntryA`, `EntryA.Wf`, `EntryHypA`: the entry numbers, their well-formedness (an
  enabled frame option has positive caps) and the hypotheses on the explicit objects of
  `(h, K, ω)`;
* `EntryConstsA`, `entryConsts`: the constants of the entry stage on B9's `StepInA`;
* `EntryCond`, `entryStageA`, `stageL1`, `condL1`, `xSL1`: the entry stage in B9's engine.

These declarations are the repaired signatures, verbatim. The namespace `Ent` names the
intermediate constants of `entryConsts` (`Ent.CS`, `Ent.CXiN`, …); `entryConsts_eq` identifies the
record with them by `rfl`. `Ent.Nonneg` collects their nonnegativity from `StepInA.Pos` and
`EntryA.Wf`; `EntryCond.down` is the downward closure.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix KAM.Sharp.Engine

namespace KAM.Sharp2.L1

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2.RouteA

/-- The optional ℓ¹ frame certificate: caps of `‖L‖_{1,ρ}`, `‖N‖_{1,ρ}` (AUDIT-B10D-1, F1). -/
structure FrameL1 where
  nuK : ℝ
  nuN : ℝ

/-- The ℓ¹ entry numbers of route A: `‖ηᴺ‖_{1,ρ} ≤ aN e`, `‖ηᴸ‖_{1,ρ} ≤ aL e`, `‖T‖_{1,ρ-δ₀} ≤ t1`,
`sup_ℝ |T| ≤ tR`, `Γ_∞(ω, δ₀) ≤ G0`, `Γ_∞(ω, ρ) ≤ Gρ`, and the optional frame certificate. -/
structure EntryA where
  aN : ℝ
  aL : ℝ
  t1 : ℝ
  tR : ℝ
  G0 : ℝ
  Gρ : ℝ
  frame : Option FrameL1 := none

/-- Well-formedness of the entry numbers; an enabled frame option has positive caps (F1). -/
structure EntryA.Wf (E : EntryA) : Prop where
  aN : 0 ≤ E.aN
  aL : 0 ≤ E.aL
  t1 : 0 ≤ E.t1
  tR : 0 ≤ E.tR
  G0 : 0 ≤ E.G0
  Gρ : 0 ≤ E.Gρ
  frame : ∀ F, E.frame = some F → 0 < F.nuK ∧ 0 < F.nuN

/-- The entry hypotheses on explicit objects of `(h, K, ω)` at the frozen sup bound `e` (a
certificate checks them); the frame bounds are required exactly when the option is enabled (F1). -/
structure EntryHypA (N : NumA) (E : EntryA) (h : (Fin N.n → ℂ) × (Fin N.n → ℂ) → ℂ)
    (K : (Fin N.n → ℂ) → (Fin N.n → ℂ) × (Fin N.n → ℂ)) (ω : Fin N.n → ℝ) (e : ℝ) : Prop where
  l1EtaN : L1Vec N.ρ (etaN h K ω) (E.aN * e)
  l1EtaL : L1Vec N.ρ (etaL h K ω) (E.aL * e)
  l1Torsion : L1Mat (N.ρ - N.δ 0) (torsion h K ω) E.t1
  realTorsion : ∀ x : Fin N.n → ℝ, ‖torsion h K ω (fun i => (x i : ℂ))‖ ≤ E.tR
  gam0 : smallDivisorSup ω (N.δ 0) ≤ E.G0
  gamρ : smallDivisorSup ω N.ρ ≤ E.Gρ
  frame : ∀ F, E.frame = some F → L1Mat N.ρ (tangentMat K) F.nuK ∧ L1Mat N.ρ (normalMat K) F.nuN

/-- The constants of the entry stage. -/
structure EntryConstsA where
  CS : ℝ
  CXiN : ℝ
  CXiN1 : ℝ
  CG : ℝ
  CXiL : ℝ
  CXiL1 : ℝ
  CDK : ℝ
  COmK : ℝ
  CE : ℝ
  dL : ℝ
  dLt : ℝ
  rB : ℝ
  rN : ℝ
  rNt : ℝ
  CDT : ℝ
  rT : ℝ
  CDw : ℝ
  gram : ℝ

/-- Blueprint `bp:p2s2l1:constA`, rebased on B9's `StepInA` (stage `0` inputs `N.inp 0`): each
ingredient is the smaller of its sup bound (B9's formula) and its ℓ¹ bound; the frame increments are
products, with no division (F1); the average uses `min t tR` (F6). For `E.frame = none` and the sup
branches of every minimum the constants equal B9's (`rateV`, `Cond`) as real numbers (by `ring`, not
definitionally). -/
def entryConsts (p : StepInA) (E : EntryA) : EntryConstsA :=
  let n : ℝ := p.n
  let einv := (Real.exp 1)⁻¹
  let tavg := min p.t E.tR
  let cavg := min (p.ca * p.sLt) (E.Gρ * E.aN * p.g)
  let CS := if p.iso then p.sT * max (p.sNt * p.g + tavg * cavg) (p.g + cavg * p.HY)
    else p.sT * (p.sNt * p.g + tavg * cavg)
  let cN1 := E.G0 * E.aN * p.g
  let CXiN := CS + min (p.c * p.sLt) cN1
  let CXiN1 := CS + cN1
  let CG := p.t * CXiN + p.Θ * CS + p.sNt * p.g
  let CXiL1 := E.G0 * p.g * (E.t1 * CXiN1 + p.Θ * CS + E.aL * p.g)
  let CXiL := min (p.c * CG) CXiL1
  let CXi := max CXiL (p.g * CXiN)
  let CDK := p.sK * CXiL + p.sN * p.g * CXiN
  let COmK := min p.COm (n * einv * E.G0 * E.aN * p.g)
  let CSym := max 1 (p.sB ^ 2) * COmK
  let CDXi := max CG (p.sLt * p.g)
  let CLin := p.CRed * CXi + CSym * CDXi + p.Θ * COmK * CS
  let CdK := p.CFr * CXi + p.P * p.g * CDXi
  let CE1 := 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * CLin + p.M2 / 2 * CDK ^ 2 +
    (if p.iso then p.g * CS * CdK else 0)
  let CE2 := p.γb * p.δ ^ (p.κ - 1) * n * (p.sLt * p.g + p.Θ * COmK) * CXiL + p.Mh2 / 2 * CDK ^ 2
  let CE := if p.iso then max CE1 CE2 else CE1
  let dL := match E.frame with
    | some F => min (n * CDK) (einv * (F.nuK * CXiL1 + F.nuN * p.g * CXiN1))
    | none => n * CDK
  let dLt := match E.frame with
    | some F => min (2 * n * CDK) (2 * n * einv * (F.nuK * CXiL1 + F.nuN * p.g * CXiN1))
    | none => 2 * n * CDK
  let rB := p.sB ^ 2 * (p.sLt * dL + p.sK * dLt) / (1 - p.th)
  let rN := p.sB * dL + p.sK * rB
  let rNt := rB * p.sLt + p.sB * dLt
  let CDw := p.Θ * p.g * CS
  let CDT0 := 2 * p.M1 * (rNt * p.sN + p.sNt * rN) + 2 * p.M2 * p.sNt * p.sN * p.δ * CDK +
    p.sB ^ 3 * p.w * (p.sK * dLt + p.sLt * dL) +
    2 * n * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ)) +
    p.sB ^ 3 * p.w * (p.COm + COmK) * p.g
  let CDT := if p.iso then
      max (CDT0 + CDw * p.δ) (n * CDw * p.δ + 2 * n * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ)))
    else CDT0
  ⟨CS, CXiN, CXiN1, CG, CXiL, CXiL1, CDK, COmK, CE, dL, dLt, rB, rN, rNt, CDT,
    p.sT ^ 2 / (1 - p.th) * CDT, CDw, p.sB * (p.sLt * dL + p.sK * dLt)⟩

/-- The entry step conditions at `x = ε/(γ⁴ δ₀^{2a})` (B9's `StepInA.Cond` with the entry
constants). -/
structure EntryCond (p : StepInA) (E : EntryA) (x : ℝ) : Prop where
  err : p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x ≤ 1
  sym : max 1 (p.sB ^ 2) * (entryConsts p E).COmK * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x ≤ 1 / 2
  quad : (entryConsts p E).CE * x ≤ 1
  twist : p.sT * (entryConsts p E).CDT * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th
  gram : (entryConsts p E).gram * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th

/-- The entry stage (fixed frequency; B9's rate order: ball, DK, B, ⟨T⟩⁻¹, Lᵀ, N, Nᵀ, T). -/
def entryStageA (p : StepInA) (E : EntryA) : StageA 8 where
  CE := (entryConsts p E).CE
  CD := (entryConsts p E).CDK
  Cp := 0
  rate := ![(entryConsts p E).CDK, (entryConsts p E).dL, (entryConsts p E).rB, (entryConsts p E).rT,
    (entryConsts p E).dLt, (entryConsts p E).rN, (entryConsts p E).rNt, (entryConsts p E).CDT]

/-- The stages of a run with the ℓ¹ entry: stage `0` is the entry, every later stage is B9's. -/
def stageL1 (N : NumA) (E : EntryA) (s : ℕ) : StageA 8 :=
  if s = 0 then entryStageA (N.inp 0) E else N.stage s

/-- The conditions of a run with the ℓ¹ entry. -/
def condL1 (N : NumA) (E : EntryA) (s : ℕ) (x : ℝ) : Prop :=
  if s = 0 then EntryCond (N.inp 0) E x else (N.inp s).Cond x

/-- The normalised errors of a run with the ℓ¹ entry. -/
def xSL1 (N : NumA) (E : EntryA) (Xs : ℝ) : ℕ → ℝ := xA (2 * N.τ) (fun s => (stageL1 N E s).CE) Xs

/-! ### The intermediate constants -/

namespace Ent

variable (p : StepInA) (E : EntryA)

/-- `e⁻¹`. -/
def einv : ℝ := (Real.exp 1)⁻¹
/-- The torsion factor of the average, `min {t, t_ℝ}`. -/
def tavg : ℝ := min p.t E.tR
/-- The average factor, `min {c_a σ_{Lᵀ}, G_ρ a_N g}`. -/
def cavg : ℝ := min (p.ca * p.sLt) (E.Gρ * E.aN * p.g)
/-- `C_S`. -/
def CS : ℝ := if p.iso then p.sT * max (p.sNt * p.g + tavg p E * cavg p E) (p.g + cavg p E * p.HY)
  else p.sT * (p.sNt * p.g + tavg p E * cavg p E)
/-- The ℓ¹ constant of `𝓡ηᴺ`, `G₀ a_N g`. -/
def cN1 : ℝ := E.G0 * E.aN * p.g
/-- `C_ξᴺ`. -/
def CXiN : ℝ := CS p E + min (p.c * p.sLt) (cN1 p E)
/-- `C¹_ξᴺ`, the ℓ¹ constant of `ξᴺ`. -/
def CXiN1 : ℝ := CS p E + cN1 p E
/-- `C_g`. -/
def CG : ℝ := p.t * CXiN p E + p.Θ * CS p E + p.sNt * p.g
/-- `C¹_ξᴸ`. -/
def CXiL1 : ℝ := E.G0 * p.g * (E.t1 * CXiN1 p E + p.Θ * CS p E + E.aL * p.g)
/-- `C_ξᴸ`. -/
def CXiL : ℝ := min (p.c * CG p E) (CXiL1 p E)
/-- `C_ξ`. -/
def CXi : ℝ := max (CXiL p E) (p.g * CXiN p E)
/-- `C_ΔK`. -/
def CDK : ℝ := p.sK * CXiL p E + p.sN * p.g * CXiN p E
/-- `C^K_Ω`. -/
def COmK : ℝ := min p.COm ((p.n : ℝ) * einv * E.G0 * E.aN * p.g)
/-- `C_sym`. -/
def CSym : ℝ := max 1 (p.sB ^ 2) * COmK p E
/-- `C_∂ξ`. -/
def CDXi : ℝ := max (CG p E) (p.sLt * p.g)
/-- `C_lin`. -/
def CLin : ℝ := p.CRed * CXi p E + CSym p E * CDXi p E + p.Θ * COmK p E * CS p E
/-- `C_∂K`. -/
def CdK : ℝ := p.CFr * CXi p E + p.P * p.g * CDXi p E
/-- `C_E`, the invariance branch. -/
def CE1 : ℝ := 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * CLin p E + p.M2 / 2 * CDK p E ^ 2 +
  (if p.iso then p.g * CS p E * CdK p E else 0)
/-- `C_E`, the energy branch. -/
def CE2 : ℝ := p.γb * p.δ ^ (p.κ - 1) * (p.n : ℝ) * (p.sLt * p.g + p.Θ * COmK p E) * CXiL p E +
  p.Mh2 / 2 * CDK p E ^ 2
/-- `C_E`. -/
def CE : ℝ := if p.iso then max (CE1 p E) (CE2 p E) else CE1 p E
/-- `C¹_ΔK` of a frame certificate. -/
def CDK1 (F : FrameL1) : ℝ := F.nuK * CXiL1 p E + F.nuN * p.g * CXiN1 p E
/-- The `|DK|` increment rate. -/
def dL : ℝ := match E.frame with
  | some F => min ((p.n : ℝ) * CDK p E) (einv * (F.nuK * CXiL1 p E + F.nuN * p.g * CXiN1 p E))
  | none => (p.n : ℝ) * CDK p E
/-- The `|Lᵀ|` increment rate. -/
def dLt : ℝ := match E.frame with
  | some F => min (2 * (p.n : ℝ) * CDK p E)
      (2 * (p.n : ℝ) * einv * (F.nuK * CXiL1 p E + F.nuN * p.g * CXiN1 p E))
  | none => 2 * (p.n : ℝ) * CDK p E
/-- The Gram increment factor `σ_{Lᵀ} d_L + σ_K d_{Lᵀ}`. -/
def GrK : ℝ := p.sLt * dL p E + p.sK * dLt p E
/-- The `|B|` rate. -/
def rB : ℝ := p.sB ^ 2 * (p.sLt * dL p E + p.sK * dLt p E) / (1 - p.th)
/-- The `|N|` rate. -/
def rN : ℝ := p.sB * dL p E + p.sK * rB p E
/-- The `|Nᵀ|` rate. -/
def rNt : ℝ := rB p E * p.sLt + p.sB * dLt p E
/-- `C_Δω`. -/
def CDw : ℝ := p.Θ * p.g * CS p E
/-- The fixed-frequency torsion rate. -/
def CDT0 : ℝ := 2 * p.M1 * (rNt p E * p.sN + p.sNt * rN p E) +
  2 * p.M2 * p.sNt * p.sN * p.δ * CDK p E + p.sB ^ 3 * p.w * (p.sK * dLt p E + p.sLt * dL p E) +
  2 * (p.n : ℝ) * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ)) +
  p.sB ^ 3 * p.w * (p.COm + COmK p E) * p.g
/-- The torsion rate. -/
def CDT : ℝ := if p.iso then
    max (CDT0 p E + CDw p E * p.δ)
      ((p.n : ℝ) * CDw p E * p.δ + 2 * (p.n : ℝ) * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ)))
  else CDT0 p E
/-- The `|⟨T⟩⁻¹|` rate. -/
def rT : ℝ := p.sT ^ 2 / (1 - p.th) * CDT p E

end Ent

/-- The record of entry constants is the record of the named intermediate constants. -/
theorem entryConsts_eq (p : StepInA) (E : EntryA) :
    entryConsts p E = ⟨Ent.CS p E, Ent.CXiN p E, Ent.CXiN1 p E, Ent.CG p E, Ent.CXiL p E,
      Ent.CXiL1 p E, Ent.CDK p E, Ent.COmK p E, Ent.CE p E, Ent.dL p E, Ent.dLt p E, Ent.rB p E,
      Ent.rN p E, Ent.rNt p E, Ent.CDT p E, Ent.rT p E, Ent.CDw p E,
      p.sB * (p.sLt * Ent.dL p E + p.sK * Ent.dLt p E)⟩ := by
  obtain ⟨aN, aL, t1, tR, G0, Gρ, _ | F⟩ := E <;> rfl

namespace Ent

variable {p : StepInA} {E : EntryA}

@[simp] theorem CS_eq : (entryConsts p E).CS = CS p E := by rw [entryConsts_eq]
@[simp] theorem CXiN_eq : (entryConsts p E).CXiN = CXiN p E := by rw [entryConsts_eq]
@[simp] theorem CXiN1_eq : (entryConsts p E).CXiN1 = CXiN1 p E := by rw [entryConsts_eq]
@[simp] theorem CG_eq : (entryConsts p E).CG = CG p E := by rw [entryConsts_eq]
@[simp] theorem CXiL_eq : (entryConsts p E).CXiL = CXiL p E := by rw [entryConsts_eq]
@[simp] theorem CXiL1_eq : (entryConsts p E).CXiL1 = CXiL1 p E := by rw [entryConsts_eq]
@[simp] theorem CDK_eq : (entryConsts p E).CDK = CDK p E := by rw [entryConsts_eq]
@[simp] theorem COmK_eq : (entryConsts p E).COmK = COmK p E := by rw [entryConsts_eq]
@[simp] theorem CE_eq : (entryConsts p E).CE = CE p E := by rw [entryConsts_eq]
@[simp] theorem dL_eq : (entryConsts p E).dL = dL p E := by rw [entryConsts_eq]
@[simp] theorem dLt_eq : (entryConsts p E).dLt = dLt p E := by rw [entryConsts_eq]
@[simp] theorem rB_eq : (entryConsts p E).rB = rB p E := by rw [entryConsts_eq]
@[simp] theorem rN_eq : (entryConsts p E).rN = rN p E := by rw [entryConsts_eq]
@[simp] theorem rNt_eq : (entryConsts p E).rNt = rNt p E := by rw [entryConsts_eq]
@[simp] theorem CDT_eq : (entryConsts p E).CDT = CDT p E := by rw [entryConsts_eq]
@[simp] theorem rT_eq : (entryConsts p E).rT = rT p E := by rw [entryConsts_eq]
@[simp] theorem CDw_eq : (entryConsts p E).CDw = CDw p E := by rw [entryConsts_eq]
@[simp] theorem gram_eq : (entryConsts p E).gram = p.sB * GrK p E := by
  rw [entryConsts_eq]; rfl

/-- The nonnegativity of the intermediate entry constants. -/
structure Nonneg (p : StepInA) (E : EntryA) : Prop where
  tavg : 0 ≤ tavg p E
  cavg : 0 ≤ cavg p E
  CS : 0 ≤ CS p E
  cN1 : 0 ≤ cN1 p E
  CXiN : 0 ≤ CXiN p E
  CXiN1 : 0 ≤ CXiN1 p E
  CG : 0 ≤ CG p E
  CXiL1 : 0 ≤ CXiL1 p E
  CXiL : 0 ≤ CXiL p E
  CXi : 0 ≤ CXi p E
  CDK : 0 ≤ CDK p E
  COmK : 0 ≤ COmK p E
  CSym : 0 ≤ CSym p E
  CDXi : 0 ≤ CDXi p E
  CLin : 0 ≤ CLin p E
  CdK : 0 ≤ CdK p E
  CE : 0 ≤ CE p E
  dL : 0 ≤ dL p E
  dLt : 0 ≤ dLt p E
  GrK : 0 ≤ GrK p E
  rB : 0 ≤ rB p E
  rN : 0 ≤ rN p E
  rNt : 0 ≤ rNt p E
  CDw : 0 ≤ CDw p E
  CDT0 : 0 ≤ CDT0 p E
  CDT : 0 ≤ CDT p E
  rT : 0 ≤ rT p E

theorem einv_pos : 0 < einv := inv_pos.2 (Real.exp_pos 1)

/-- Every intermediate entry constant is nonnegative. -/
theorem nonneg (hp : p.Pos) (hE : E.Wf) : Nonneg p E := by
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hg := hp.g
  have he := einv_pos.le
  have hδ := hp.δ
  have hγ := hp.γb
  have htv : 0 ≤ tavg p E := le_min hp.t hE.tR
  have hcv : 0 ≤ cavg p E := le_min (mul_nonneg hp.ca hp.sLt) (by
    have := hE.Gρ; have := hE.aN; positivity)
  have hCS : 0 ≤ CS p E := by
    unfold CS
    have := hp.sT; have := hp.sNt; have := hp.HY
    split_ifs
    · exact mul_nonneg hp.sT (le_max_of_le_left (by positivity))
    · positivity
  have hcN : 0 ≤ cN1 p E := by unfold cN1; have := hE.G0; have := hE.aN; positivity
  have hXN : 0 ≤ CXiN p E := add_nonneg hCS (le_min (mul_nonneg hp.c hp.sLt) hcN)
  have hXN1 : 0 ≤ CXiN1 p E := add_nonneg hCS hcN
  have hCG : 0 ≤ CG p E := by
    unfold CG; have := hp.t; have := hp.Θ; have := hp.sNt; positivity
  have hXL1 : 0 ≤ CXiL1 p E := by
    unfold CXiL1; have := hE.G0; have := hE.t1; have := hE.aL; have := hp.Θ; positivity
  have hXL : 0 ≤ CXiL p E := le_min (mul_nonneg hp.c hCG) hXL1
  have hXi : 0 ≤ CXi p E := le_max_of_le_left hXL
  have hDK : 0 ≤ CDK p E := by unfold CDK; have := hp.sK; have := hp.sN; positivity
  have hOm : 0 ≤ COmK p E := le_min hp.COm (by
    unfold einv; have := hE.G0; have := hE.aN; positivity)
  have hSym : 0 ≤ CSym p E := mul_nonneg (le_max_of_le_left zero_le_one) hOm
  have hDXi : 0 ≤ CDXi p E := le_max_of_le_left hCG
  have hLin : 0 ≤ CLin p E := by
    unfold CLin; have := hp.CRed; have := hp.Θ; positivity
  have hdK : 0 ≤ CdK p E := by unfold CdK; have := hp.CFr; have := hp.P; positivity
  have hE1 : 0 ≤ CE1 p E := by
    unfold CE1
    have := hp.P; have := hp.M2
    have h3 : 0 ≤ p.δ ^ (2 * p.κ - 1) := Real.rpow_nonneg hδ.le _
    have h4 : 0 ≤ (if p.iso then p.g * CS p E * CdK p E else 0) := by
      split_ifs <;> positivity
    positivity
  have hE2 : 0 ≤ CE2 p E := by
    unfold CE2
    have := hp.Mh2; have := hp.Θ; have := hp.sLt
    have h3 : 0 ≤ p.δ ^ (p.κ - 1) := Real.rpow_nonneg hδ.le _
    positivity
  have hCE : 0 ≤ CE p E := by
    unfold CE; split_ifs
    · exact le_max_of_le_left hE1
    · exact hE1
  have hfr : ∀ F, E.frame = some F → 0 ≤ F.nuK * CXiL1 p E + F.nuN * p.g * CXiN1 p E := by
    intro F hF
    obtain ⟨h1, h2⟩ := hE.frame F hF
    positivity
  have hdL : 0 ≤ dL p E := by
    unfold dL
    rcases hF : E.frame with _ | F
    · positivity
    · exact le_min (by positivity) (mul_nonneg he (hfr F hF))
  have hdLt : 0 ≤ dLt p E := by
    unfold dLt
    rcases hF : E.frame with _ | F
    · positivity
    · exact le_min (by positivity) (mul_nonneg (by positivity) (hfr F hF))
  have hGr : 0 ≤ GrK p E := by unfold GrK; have := hp.sLt; have := hp.sK; positivity
  have hth := hp.one_sub_th
  have hrB : 0 ≤ rB p E := by
    unfold rB; have := hp.sLt; have := hp.sK; positivity
  have hrN : 0 ≤ rN p E := by unfold rN; have := hp.sB; have := hp.sK; positivity
  have hrNt : 0 ≤ rNt p E := by unfold rNt; have := hp.sB; have := hp.sLt; positivity
  have hDw : 0 ≤ CDw p E := by unfold CDw; have := hp.Θ; positivity
  have hDT0 : 0 ≤ CDT0 p E := by
    unfold CDT0
    have := hp.M1; have := hp.M2; have := hp.sN; have := hp.sNt; have := hp.sB; have := hp.w
    have := hp.sK; have := hp.sLt; have := hp.COm
    positivity
  have hDT : 0 ≤ CDT p E := by
    unfold CDT; split_ifs
    · exact le_max_of_le_left (by positivity)
    · exact hDT0
  have hrT : 0 ≤ rT p E := by unfold rT; have := hp.sT; positivity
  exact ⟨htv, hcv, hCS, hcN, hXN, hXN1, hCG, hXL1, hXL, hXi, hDK, hOm, hSym, hDXi, hLin, hdK, hCE,
    hdL, hdLt, hGr, hrB, hrN, hrNt, hDw, hDT0, hDT, hrT⟩

end Ent

open Ent in
/-- The entry conditions are downward closed on nonnegative errors. -/
theorem EntryCond.down {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf) {x y : ℝ}
    (hxy : x ≤ y) (h : EntryCond p E y) : EntryCond p E x := by
  have hw : ∀ {a b : ℝ}, 0 ≤ a → a * y ≤ b → a * x ≤ b := fun ha h1 =>
    (mul_le_mul_of_nonneg_left hxy ha).trans h1
  have hk := Ent.nonneg hp hE
  have hδ := hp.δ
  have hγ := hp.γb
  have hD4 : 0 ≤ p.δ ^ (2 * (2 * p.κ) - 1) := Real.rpow_nonneg hδ.le _
  have hD3 : 0 ≤ p.δ ^ (3 * p.κ - 1) := Real.rpow_nonneg hδ.le _
  have hD2 : 0 ≤ p.δ ^ (2 * p.κ - 1) := Real.rpow_nonneg hδ.le _
  have hT := hp.sT
  have hB := hp.sB
  have h1 : 0 ≤ (entryConsts p E).COmK := by rw [COmK_eq]; exact hk.COmK
  have h2 : 0 ≤ (entryConsts p E).CE := by rw [CE_eq]; exact hk.CE
  have h3 : 0 ≤ (entryConsts p E).CDT := by rw [CDT_eq]; exact hk.CDT
  have h4 : 0 ≤ (entryConsts p E).gram := by rw [gram_eq]; exact mul_nonneg hB hk.GrK
  have hm : (0 : ℝ) ≤ max 1 (p.sB ^ 2) := le_max_of_le_left zero_le_one
  exact ⟨hw (by positivity) h.err, hw (by positivity) h.sym, hw h2 h.quad,
    hw (by positivity) h.twist,
    hw (by positivity) h.gram⟩

/-- The rates of the entry stage are nonnegative. -/
theorem entryStageA_rate_nonneg {p : StepInA} {E : EntryA} (hp : p.Pos) (hE : E.Wf) (i : Fin 8) :
    0 ≤ (entryStageA p E).rate i := by
  have hk := Ent.nonneg hp hE
  simp only [entryStageA, Ent.CDK_eq, Ent.dL_eq, Ent.rB_eq, Ent.rT_eq, Ent.dLt_eq, Ent.rN_eq,
    Ent.rNt_eq, Ent.CDT_eq]
  fin_cases i
  · exact hk.CDK
  · exact hk.dL
  · exact hk.rB
  · exact hk.rT
  · exact hk.dLt
  · exact hk.rN
  · exact hk.rNt
  · exact hk.CDT

end KAM.Sharp2.L1

end
