/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAQ
public import KAM.Sharp2.Examples.MirrorL1
public import KAM.Iso.Sharp2.L1.G1A
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rational mirror of the isoenergetic ℓ¹ entry (package C6L1)

The constants of the entry stage `KAM.Sharp2.L1.entryConsts` at the isoenergetic inputs of C6's
`StepQ` (any `κ ∈ ℕ`), with an upper bound `ei ≥ e⁻¹` (the record
`KAM.Sharp2.Examples.EntryQ` of package B10C) in place of the irrational `e⁻¹`:

* `eCS`, …, `eCDT`: the mirrors; `ecast_*`: the exact casts of the constants in which `e⁻¹` does
  not enter; `le_*`: the bounds of the others (every constant is nondecreasing in `e⁻¹`);
* `econd`, `econd_sound`: the entry conditions `EntryCond`;
* `erate`, `le_erate`: the nine rates of `entryStageIA`;
* `einv_le`: `e⁻¹ ≤ 0.3679`.

The run (stage `0` the entry, every later stage C6's `StepQ`) is in `V2/RouteAL1Run.lean`. All
names are in the namespace `KAM.CertificateSharp.V2.L1`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.L1

open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp.Engine KAM.Sharp2.L1
open KAM.Sharp2.Examples (EntryQ)

variable (p : StepQ) (E : EntryQ)

/-- `min {t, t_ℝ}`. -/
def eTavg : ℚ := min p.t E.tR
/-- `min {c_a σ_{Lᵀ}, G_ρ a_N g}`. -/
def eCavg : ℚ := min (p.ca * p.sLt) (E.Gρ * E.aN * p.g)
/-- `C_S` (isoenergetic). -/
def eCS : ℚ := p.sT * max (p.sNt * p.g + eTavg p E * eCavg p E) (p.g + eCavg p E * p.HY)
/-- `G₀ a_N g`. -/
def ecN1 : ℚ := E.G0 * E.aN * p.g
/-- `C_ξᴺ`. -/
def eCXiN : ℚ := eCS p E + min (p.c * p.sLt) (ecN1 p E)
/-- `C¹_ξᴺ`. -/
def eCXiN1 : ℚ := eCS p E + ecN1 p E
/-- `C_g`. -/
def eCG : ℚ := p.t * eCXiN p E + p.Θ * eCS p E + p.sNt * p.g
/-- `C¹_ξᴸ`. -/
def eCXiL1 : ℚ := E.G0 * p.g * (E.t1 * eCXiN1 p E + p.Θ * eCS p E + E.aL * p.g)
/-- `C_ξᴸ`. -/
def eCXiL : ℚ := min (p.c * eCG p E) (eCXiL1 p E)
/-- `C_ξ`. -/
def eCXi : ℚ := max (eCXiL p E) (p.g * eCXiN p E)
/-- `C_ΔK`. -/
def eCDK : ℚ := p.sK * eCXiL p E + p.sN * p.g * eCXiN p E
/-- `C^K_Ω`, with `ei` for `e⁻¹`. -/
def eCOmK : ℚ := min p.COm ((p.n : ℚ) * E.ei * E.G0 * E.aN * p.g)
/-- `C_sym`. -/
def eCSym : ℚ := max 1 (p.sB ^ 2) * eCOmK p E
/-- `C_∂ξ`. -/
def eCDXi : ℚ := max (eCG p E) (p.sLt * p.g)
/-- `C_lin`. -/
def eCLin : ℚ := p.CRed * eCXi p E + eCSym p E * eCDXi p E + p.Θ * eCOmK p E * eCS p E
/-- `C_∂K`. -/
def eCdK : ℚ := p.CFr * eCXi p E + p.P * p.g * eCDXi p E
/-- `C_E`, the invariance branch. -/
def eCE1 : ℚ := 2 * p.P * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * eCLin p E + p.M2 / 2 * eCDK p E ^ 2 +
  p.g * eCS p E * eCdK p E
/-- `C_E`, the energy branch. -/
def eCE2 : ℚ := p.γb * p.δ ^ (p.κ - 1) * p.n * (p.sLt * p.g + p.Θ * eCOmK p E) * eCXiL p E +
  p.Mh2 / 2 * eCDK p E ^ 2
/-- `C_E`. -/
def eCE : ℚ := max (eCE1 p E) (eCE2 p E)
/-- The `|DK|` increment rate. -/
def edL : ℚ := match E.frame with
  | some f => min ((p.n : ℚ) * eCDK p E) (E.ei * (f.1 * eCXiL1 p E + f.2 * p.g * eCXiN1 p E))
  | none => (p.n : ℚ) * eCDK p E
/-- The `|Lᵀ|` increment rate. -/
def edLt : ℚ := match E.frame with
  | some f => min (2 * (p.n : ℚ) * eCDK p E)
      (2 * (p.n : ℚ) * E.ei * (f.1 * eCXiL1 p E + f.2 * p.g * eCXiN1 p E))
  | none => 2 * (p.n : ℚ) * eCDK p E
/-- `σ_{Lᵀ} d_L + σ_K d_{Lᵀ}`. -/
def eGrK : ℚ := p.sLt * edL p E + p.sK * edLt p E
/-- The `|B|` rate. -/
def erB : ℚ := p.sB ^ 2 * (p.sLt * edL p E + p.sK * edLt p E) / (1 - p.th)
/-- The `|N|` rate. -/
def erN : ℚ := p.sB * edL p E + p.sK * erB p E
/-- The `|Nᵀ|` rate. -/
def erNt : ℚ := erB p E * p.sLt + p.sB * edLt p E
/-- `C_Δω`. -/
def eCDw : ℚ := p.Θ * p.g * eCS p E
/-- The torsion rate, before the frequency terms. -/
def eCDT0 : ℚ := 2 * p.M1 * (erNt p E * p.sN + p.sNt * erN p E) +
  2 * p.M2 * p.sNt * p.sN * p.δ * eCDK p E + p.sB ^ 3 * p.w * (p.sK * edLt p E + p.sLt * edL p E) +
  2 * (p.n : ℚ) * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ (2 * p.κ)) +
  p.sB ^ 3 * p.w * (p.COm + eCOmK p E) * p.g
/-- The torsion rate (isoenergetic). -/
def eCDT : ℚ := max (eCDT0 p E + eCDw p E * p.δ)
  ((p.n : ℚ) * eCDw p E * p.δ + 2 * (p.n : ℚ) * p.sNt * (p.γb ^ 2 * p.δ ^ (2 * p.κ)))
/-- The `|⟨T⟩⁻¹|` rate. -/
def erT : ℚ := p.sT ^ 2 / (1 - p.th) * eCDT p E

/-- The nine rates of the isoenergetic entry stage. -/
def erate : Fin 9 → ℚ :=
  ![eCDK p E, edL p E, erB p E, erT p E, edLt p E, erN p E, erNt p E, eCDT p E, eCDw p E]

/-- The entry conditions at the normalised error `x`. -/
def econd (x : ℚ) : Bool :=
  decide (p.γb ^ 4 * p.δ ^ (2 * (2 * p.κ) - 1) * x ≤ 1) &&
    decide (max 1 (p.sB ^ 2) * eCOmK p E * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x ≤ 1 / 2) &&
    decide (eCE p E * x ≤ 1) &&
    decide (p.sT * eCDT p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th) &&
    decide (p.sB * eGrK p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x ≤ p.th)

/-! ### The exact casts -/

theorem ecast_tavg : Ent.tavg p.toStep E.toA = (eTavg p E : ℝ) := by
  simp [Ent.tavg, eTavg, StepQ.toStep, EntryQ.toA]

theorem ecast_cavg : Ent.cavg p.toStep E.toA = (eCavg p E : ℝ) := by
  simp only [Ent.cavg, StepQ.cast_g]
  simp [eCavg, StepQ.toStep, EntryQ.toA]

theorem ecast_CS : Ent.CS p.toStep E.toA = (eCS p E : ℝ) := by
  simp only [Ent.CS, ecast_tavg, ecast_cavg, StepQ.cast_g]
  simp [eCS, StepQ.toStep]

theorem ecast_cN1 : Ent.cN1 p.toStep E.toA = (ecN1 p E : ℝ) := by
  simp only [Ent.cN1, StepQ.cast_g]
  simp [ecN1, EntryQ.toA]

theorem ecast_CXiN : Ent.CXiN p.toStep E.toA = (eCXiN p E : ℝ) := by
  simp only [Ent.CXiN, ecast_CS, ecast_cN1]
  simp [eCXiN, StepQ.toStep]

theorem ecast_CXiN1 : Ent.CXiN1 p.toStep E.toA = (eCXiN1 p E : ℝ) := by
  simp only [Ent.CXiN1, ecast_CS, ecast_cN1]
  simp [eCXiN1]

theorem ecast_CG : Ent.CG p.toStep E.toA = (eCG p E : ℝ) := by
  simp only [Ent.CG, ecast_CXiN, ecast_CS, StepQ.cast_g]
  simp [eCG, StepQ.toStep]

theorem ecast_CXiL1 : Ent.CXiL1 p.toStep E.toA = (eCXiL1 p E : ℝ) := by
  simp only [Ent.CXiL1, ecast_CXiN1, ecast_CS, StepQ.cast_g]
  simp [eCXiL1, EntryQ.toA, StepQ.toStep]

theorem ecast_CXiL : Ent.CXiL p.toStep E.toA = (eCXiL p E : ℝ) := by
  simp only [Ent.CXiL, ecast_CG, ecast_CXiL1]
  simp [eCXiL, StepQ.toStep]

theorem ecast_CXi : Ent.CXi p.toStep E.toA = (eCXi p E : ℝ) := by
  simp only [Ent.CXi, ecast_CXiL, ecast_CXiN, StepQ.cast_g]
  simp [eCXi]

theorem ecast_CDK : Ent.CDK p.toStep E.toA = (eCDK p E : ℝ) := by
  simp only [Ent.CDK, ecast_CXiL, ecast_CXiN, StepQ.cast_g]
  simp [eCDK, StepQ.toStep]

theorem ecast_CDXi : Ent.CDXi p.toStep E.toA = (eCDXi p E : ℝ) := by
  simp only [Ent.CDXi, ecast_CG, StepQ.cast_g]
  simp [eCDXi, StepQ.toStep]

theorem ecast_CdK : Ent.CdK p.toStep E.toA = (eCdK p E : ℝ) := by
  simp only [Ent.CdK, ecast_CXi, ecast_CDXi, StepQ.cast_CFr, StepQ.cast_P, StepQ.cast_g]
  simp [eCdK]

theorem ecast_CDw : Ent.CDw p.toStep E.toA = (eCDw p E : ℝ) := by
  simp only [Ent.CDw, ecast_CS, StepQ.cast_g]
  simp [eCDw, StepQ.toStep]

/-! ### The bounds through `e⁻¹ ≤ ei` -/

variable {p E}

theorem toStep_iso : p.toStep.iso = true := rfl

/-- `e⁻¹ ≤ 0.3679`. -/
theorem einv_le : Ent.einv ≤ ((3679 / 10000 : ℚ) : ℝ) := by
  have h := Real.exp_one_gt_d9
  unfold Ent.einv
  rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  norm_num
  linarith

theorem le_COmK (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.COmK p.toStep E.toA ≤ (eCOmK p E : ℝ) := by
  have hg := hp.g
  have hG := hE.G0
  have haN := hE.aN
  unfold Ent.COmK
  have e : ((eCOmK p E : ℚ) : ℝ) =
      min p.toStep.COm ((p.toStep.n : ℝ) * E.ei * E.toA.G0 * E.toA.aN * p.toStep.g) := by
    rw [StepQ.cast_COm, StepQ.cast_g]
    simp [eCOmK, StepQ.toStep, EntryQ.toA]
  rw [e]
  refine min_le_min le_rfl ?_
  have hn : (0 : ℝ) ≤ p.toStep.n := Nat.cast_nonneg _
  gcongr

theorem le_CSym (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CSym p.toStep E.toA ≤ (eCSym p E : ℝ) := by
  have e : ((eCSym p E : ℚ) : ℝ) = max 1 (p.toStep.sB ^ 2) * (eCOmK p E : ℝ) := by
    simp [eCSym, StepQ.toStep]
  rw [Ent.CSym, e]
  exact mul_le_mul_of_nonneg_left (le_COmK hp hE hei) (le_max_of_le_left zero_le_one)

theorem le_CLin (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CLin p.toStep E.toA ≤ (eCLin p E : ℝ) := by
  have hk := Ent.nonneg hp hE
  have e : ((eCLin p E : ℚ) : ℝ) = p.toStep.CRed * (eCXi p E : ℝ) +
      (eCSym p E : ℝ) * (eCDXi p E : ℝ) + p.toStep.Θ * (eCOmK p E : ℝ) * (eCS p E : ℝ) := by
    rw [StepQ.cast_CRed]
    simp [eCLin, StepQ.toStep]
  rw [Ent.CLin, e, ecast_CXi, ecast_CDXi, ecast_CS]
  have h1 := le_CSym hp hE hei
  have h2 := le_COmK hp hE hei
  have hD : (0 : ℝ) ≤ eCDXi p E := by have := hk.CDXi; rwa [ecast_CDXi] at this
  have hS : (0 : ℝ) ≤ eCS p E := by have := hk.CS; rwa [ecast_CS] at this
  have hΘ := hp.Θ
  gcongr

theorem le_CE (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CE p.toStep E.toA ≤ (eCE p E : ℝ) := by
  have hk := Ent.nonneg hp hE
  have hκ : (1 : ℝ) ≤ (p.κ : ℝ) := hp.κ_ge
  have hκ' : 1 ≤ p.κ := by exact_mod_cast hκ
  have e1 : ((2 * (p.κ : ℝ) - 1 : ℝ)) = ((2 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (((p.κ : ℝ) - 1 : ℝ)) = ((p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hκ']; push_cast; ring
  have hC1 : ((eCE1 p E : ℚ) : ℝ) = 2 * p.toStep.P *
      (p.toStep.γb ^ 2 * p.toStep.δ ^ (2 * p.toStep.κ - 1)) * (eCLin p E : ℝ) +
      p.toStep.M2 / 2 * (eCDK p E : ℝ) ^ 2 + p.toStep.g * (eCS p E : ℝ) * (eCdK p E : ℝ) := by
    rw [StepQ.cast_P, StepQ.cast_g]
    simp only [StepQ.toStep, StepQ.rpow_nat p.δ e1]
    simp [eCE1]
  have hC2 : ((eCE2 p E : ℚ) : ℝ) = p.toStep.γb * p.toStep.δ ^ (p.toStep.κ - 1) *
      (p.toStep.n : ℝ) * (p.toStep.sLt * p.toStep.g + p.toStep.Θ * (eCOmK p E : ℝ)) *
      (eCXiL p E : ℝ) + p.toStep.Mh2 / 2 * (eCDK p E : ℝ) ^ 2 := by
    rw [StepQ.cast_g]
    simp only [StepQ.toStep, StepQ.rpow_nat p.δ e2]
    simp [eCE2]
  have e : ((eCE p E : ℚ) : ℝ) = max (eCE1 p E : ℝ) (eCE2 p E : ℝ) := by
    simp [eCE]
  rw [e, hC1, hC2]
  simp only [Ent.CE, Ent.CE1, Ent.CE2, toStep_iso, ite_true, ecast_CDK, ecast_CS, ecast_CdK,
    ecast_CXiL]
  have hP := hp.P
  have hδ := hp.δ
  have hγ := hp.γb
  have hg := hp.g
  have hΘ := hp.Θ
  have hLt := hp.sLt
  have hS : (0 : ℝ) ≤ eCS p E := by have := hk.CS; rwa [ecast_CS] at this
  have hXL : (0 : ℝ) ≤ eCXiL p E := by have := hk.CXiL; rwa [ecast_CXiL] at this
  have hw1 := Real.rpow_nonneg hδ.le (2 * p.toStep.κ - 1)
  have hw2 := Real.rpow_nonneg hδ.le (p.toStep.κ - 1)
  have hn : (0 : ℝ) ≤ p.toStep.n := Nat.cast_nonneg _
  have hL := le_CLin hp hE hei
  have hO := le_COmK hp hE hei
  refine max_le_max ?_ ?_
  · gcongr
  · gcongr

theorem le_dL (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.dL p.toStep E.toA ≤ (edL p E : ℝ) ∧ Ent.dLt p.toStep E.toA ≤ (edLt p E : ℝ) := by
  have hk := Ent.nonneg hp hE
  unfold Ent.dL Ent.dLt edL edLt
  rcases hfr : E.frame with _ | f
  · have hfa : E.toA.frame = none := by simp [EntryQ.toA, hfr]
    simp only [hfa, ecast_CDK]
    exact ⟨by simp [StepQ.toStep], by simp [StepQ.toStep]⟩
  · have hfa : E.toA.frame = some ⟨f.1, f.2⟩ := by simp [EntryQ.toA, hfr]
    obtain ⟨h1, h2⟩ := hE.frame _ hfa
    simp only [hfa, ecast_CDK, ecast_CXiL1, ecast_CXiN1, StepQ.cast_g]
    have hA : (0 : ℝ) ≤ (f.1 : ℝ) * eCXiL1 p E + f.2 * p.g * eCXiN1 p E := by
      have a := hk.CXiL1; have b := hk.CXiN1; have c := hp.g
      rw [ecast_CXiL1] at a; rw [ecast_CXiN1] at b; rw [StepQ.cast_g] at c
      have : (0 : ℝ) ≤ (f.1 : ℝ) := h1.le
      have : (0 : ℝ) ≤ (f.2 : ℝ) := h2.le
      positivity
    constructor
    · push_cast
      exact min_le_min (by simp [StepQ.toStep]) (mul_le_mul_of_nonneg_right hei hA)
    · push_cast
      refine min_le_min (by simp [StepQ.toStep]) ?_
      have : (2 : ℝ) * p.toStep.n * Ent.einv ≤ 2 * p.n * E.ei := by
        rw [show (p.toStep.n : ℝ) = p.n from rfl]
        exact mul_le_mul_of_nonneg_left hei (by positivity)
      exact mul_le_mul_of_nonneg_right this hA

theorem le_rates (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.GrK p.toStep E.toA ≤ (eGrK p E : ℝ) ∧ Ent.rB p.toStep E.toA ≤ (erB p E : ℝ) ∧
      Ent.rN p.toStep E.toA ≤ (erN p E : ℝ) ∧ Ent.rNt p.toStep E.toA ≤ (erNt p E : ℝ) := by
  obtain ⟨h1, h2⟩ := le_dL hp hE hei
  have hLt := hp.sLt
  have hK := hp.sK
  have hB := hp.sB
  have hth := hp.one_sub_th
  have hrB : Ent.rB p.toStep E.toA ≤ (erB p E : ℝ) := by
    have e : ((erB p E : ℚ) : ℝ) = p.toStep.sB ^ 2 * (p.toStep.sLt * (edL p E : ℝ) +
        p.toStep.sK * (edLt p E : ℝ)) / (1 - p.toStep.th) := by
      simp [erB, StepQ.toStep]
    rw [Ent.rB, e]
    gcongr
  refine ⟨?_, hrB, ?_, ?_⟩
  · have e : ((eGrK p E : ℚ) : ℝ) = p.toStep.sLt * (edL p E : ℝ) +
        p.toStep.sK * (edLt p E : ℝ) := by
      simp [eGrK, StepQ.toStep]
    rw [Ent.GrK, e]
    gcongr
  · have e : ((erN p E : ℚ) : ℝ) = p.toStep.sB * (edL p E : ℝ) + p.toStep.sK * (erB p E : ℝ) := by
      simp [erN, StepQ.toStep]
    rw [Ent.rN, e]
    gcongr
  · have e : ((erNt p E : ℚ) : ℝ) = (erB p E : ℝ) * p.toStep.sLt +
        p.toStep.sB * (edLt p E : ℝ) := by
      simp [erNt, StepQ.toStep]
    rw [Ent.rNt, e]
    gcongr

theorem le_CDT (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CDT p.toStep E.toA ≤ (eCDT p E : ℝ) ∧ Ent.rT p.toStep E.toA ≤ (erT p E : ℝ) := by
  obtain ⟨h1, h2⟩ := le_dL hp hE hei
  obtain ⟨-, -, h4, h5⟩ := le_rates hp hE hei
  have h6 := le_COmK hp hE hei
  have hM1 := hp.M1
  have hM2 := hp.M2
  have hN := hp.sN
  have hNt := hp.sNt
  have hB := hp.sB
  have hK := hp.sK
  have hLt := hp.sLt
  have hw := hp.w
  have hg := hp.g
  have hδ := hp.δ
  have hk := Ent.nonneg hp hE
  have e2 : ((2 * (p.κ : ℝ) : ℝ)) = ((2 * p.κ : ℕ) : ℝ) := by push_cast; ring
  have hD0 : Ent.CDT0 p.toStep E.toA ≤ (eCDT0 p E : ℝ) := by
    have e : ((eCDT0 p E : ℚ) : ℝ) =
        2 * p.toStep.M1 * ((erNt p E : ℝ) * p.toStep.sN + p.toStep.sNt * (erN p E : ℝ)) +
        2 * p.toStep.M2 * p.toStep.sNt * p.toStep.sN * p.toStep.δ * (eCDK p E : ℝ) +
        p.toStep.sB ^ 3 * p.toStep.w * (p.toStep.sK * (edLt p E : ℝ) +
          p.toStep.sLt * (edL p E : ℝ)) +
        2 * (p.toStep.n : ℝ) * p.toStep.sNt * p.toStep.sB *
          (p.toStep.γb ^ 2 * p.toStep.δ ^ (2 * p.toStep.κ)) +
        p.toStep.sB ^ 3 * p.toStep.w * (p.toStep.COm + (eCOmK p E : ℝ)) * p.toStep.g := by
      rw [StepQ.cast_w, StepQ.cast_COm, StepQ.cast_g]
      simp only [StepQ.toStep, StepQ.rpow_nat p.δ e2]
      simp [eCDT0]
    rw [e]
    simp only [Ent.CDT0, ecast_CDK]
    gcongr
  have hDT : Ent.CDT p.toStep E.toA ≤ (eCDT p E : ℝ) := by
    have e : ((eCDT p E : ℚ) : ℝ) = max ((eCDT0 p E : ℝ) + (eCDw p E : ℝ) * p.toStep.δ)
        ((p.toStep.n : ℝ) * (eCDw p E : ℝ) * p.toStep.δ + 2 * (p.toStep.n : ℝ) * p.toStep.sNt *
          (p.toStep.γb ^ 2 * p.toStep.δ ^ (2 * p.toStep.κ))) := by
      simp only [StepQ.toStep, StepQ.rpow_nat p.δ e2]
      simp [eCDT]
    rw [e]
    simp only [Ent.CDT, toStep_iso, ite_true, ecast_CDw]
    exact max_le_max (add_le_add hD0 le_rfl) le_rfl
  refine ⟨hDT, ?_⟩
  have e : ((erT p E : ℚ) : ℝ) = p.toStep.sT ^ 2 / (1 - p.toStep.th) * (eCDT p E : ℝ) := by
    simp [erT, StepQ.toStep]
  rw [Ent.rT, e]
  have hth := hp.one_sub_th
  have hT := hp.sT
  exact mul_le_mul_of_nonneg_left hDT (by positivity)

/-- Soundness of the rational entry conditions. -/
theorem econd_sound (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) {x : ℚ}
    (hx : 0 ≤ x) (h : econd p E x = true) : EntryCond p.toStep E.toA (x : ℝ) := by
  simp only [econd, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hκ1 : (1 : ℝ) ≤ (p.κ : ℝ) := hp.κ_ge
  have hκ' : 1 ≤ p.κ := by exact_mod_cast hκ1
  have e4 : ((2 * (2 * (p.κ : ℝ)) - 1 : ℝ)) = ((2 * (2 * p.κ) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : ((3 * (p.κ : ℝ) - 1 : ℝ)) = ((3 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((2 * (p.κ : ℝ) - 1 : ℝ)) = ((2 * p.κ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hδ := hp.δ
  have hγ := hp.γb
  have hB := hp.sB
  have hT := hp.sT
  have hCO := le_COmK hp hE hei
  have hCE := le_CE hp hE hei
  have hCDT := (le_CDT hp hE hei).1
  have hGr := (le_rates hp hE hei).1
  have hδ' : (p.toStep.δ : ℝ) = p.δ := rfl
  have hγ' : (p.toStep.γb : ℝ) = p.γb := rfl
  have hκ0 : (p.toStep.κ : ℝ) = p.κ := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hκ0, hδ', hγ', StepQ.rpow_nat p.δ e4]
    exact_mod_cast h1
  · have h2' : ((max 1 (p.sB ^ 2) * eCOmK p E * (p.γb ^ 3 * p.δ ^ (3 * p.κ - 1)) * x : ℚ) : ℝ) ≤
        ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    push_cast at h2'
    rw [Ent.COmK_eq, hκ0, hδ', hγ', StepQ.rpow_nat p.δ e3]
    refine le_trans ?_ (le_of_le_of_eq h2' (by norm_num))
    have : (max 1 (p.toStep.sB ^ 2)) = max 1 ((p.sB : ℝ) ^ 2) := rfl
    rw [this]
    have hw : (0 : ℝ) ≤ (p.γb : ℝ) ^ 3 * ((p.δ ^ (3 * p.κ - 1) : ℚ) : ℝ) := by
      have : (0 : ℝ) < p.γb := hγ
      have : (0 : ℝ) < p.δ := hδ
      push_cast
      positivity
    have hm : (0 : ℝ) ≤ max 1 ((p.sB : ℝ) ^ 2) := le_max_of_le_left zero_le_one
    push_cast at hw ⊢
    gcongr
  · have h3' : ((eCE p E * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h3
    push_cast at h3'
    rw [Ent.CE_eq]
    exact (mul_le_mul_of_nonneg_right hCE hx').trans h3'
  · have h4' : ((p.sT * eCDT p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x : ℚ) : ℝ) ≤ (p.th : ℝ) :=
      Rat.cast_le.mpr h4
    push_cast at h4'
    rw [Ent.CDT_eq, hκ0, hδ', hγ', StepQ.rpow_nat p.δ e2]
    have hT' : (p.toStep.sT : ℝ) = p.sT := rfl
    rw [hT']
    refine le_trans ?_ h4'
    have : (0 : ℝ) ≤ (p.sT : ℝ) := hT
    have hw : (0 : ℝ) ≤ (p.γb : ℝ) ^ 2 * (p.δ : ℝ) ^ (2 * p.κ - 1) := by
      have : (0 : ℝ) < p.δ := hδ
      have : (0 : ℝ) < p.γb := hγ
      positivity
    push_cast
    gcongr
  · have h5' : ((p.sB * eGrK p E * (p.γb ^ 2 * p.δ ^ (2 * p.κ - 1)) * x : ℚ) : ℝ) ≤ (p.th : ℝ) :=
      Rat.cast_le.mpr h5
    push_cast at h5'
    rw [Ent.gram_eq, hκ0, hδ', hγ', StepQ.rpow_nat p.δ e2]
    have hB' : (p.toStep.sB : ℝ) = p.sB := rfl
    rw [hB']
    refine le_trans ?_ h5'
    have : (0 : ℝ) ≤ (p.sB : ℝ) := hB
    have hw : (0 : ℝ) ≤ (p.γb : ℝ) ^ 2 * (p.δ : ℝ) ^ (2 * p.κ - 1) := by
      have : (0 : ℝ) < p.δ := hδ
      have : (0 : ℝ) < p.γb := hγ
      positivity
    push_cast
    gcongr

theorem le_erate (hp : p.toStep.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) (i : Fin 9) :
    (KAM.Iso.Sharp2.L1.entryStageIA p.toStep E.toA).rate i ≤ (erate p E i : ℝ) := by
  obtain ⟨h1, h2⟩ := le_dL hp hE hei
  obtain ⟨-, h3, h4, h5⟩ := le_rates hp hE hei
  obtain ⟨h6, h7⟩ := le_CDT hp hE hei
  simp only [KAM.Iso.Sharp2.L1.entryStageIA, Ent.CDK_eq, Ent.dL_eq, Ent.rB_eq, Ent.rT_eq,
    Ent.dLt_eq, Ent.rN_eq, Ent.rNt_eq, Ent.CDT_eq, Ent.CDw_eq]
  fin_cases i <;> simp [erate, ecast_CDK, ecast_CDw, h1, h2, h3, h4, h5, h6, h7]

end KAM.CertificateSharp.V2.L1

end
