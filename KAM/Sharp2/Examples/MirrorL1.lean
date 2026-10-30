/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Examples.MirrorQ
public import KAM.Sharp2.L1.EntryScheme
public import KAM.Sharp2.RouteA.Mono
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The rational mirror of the ℓ¹ entry (package B10c)

The entry constants of `KAM.Sharp2.L1.entryConsts` involve `e⁻¹`, which is not rational. `EntryQ`
carries the rational entry numbers and an upper bound `ei ≥ e⁻¹`; `StepQ.eCS`, …, `StepQ.eCDT` are
the entry constants at `τ = 1`, fixed frequency, with `ei` in place of `e⁻¹`. Each real constant is
the cast of its mirror (`cast_*`) when `e⁻¹` does not enter, and at most the cast (`le_*`) when it
does: every constant is nondecreasing in `e⁻¹`.

`NumQ.okL1` is the Boolean form of (J0)–(J3) of `routeAOkL1`; `NumQ.okL1_sound` is its soundness:
the conditions are downward closed and the errors and the cap sums are monotone in the constants.
-/

@[expose] public section

namespace KAM.Sharp2.Examples

open KAM.Sharp.Engine KAM.Sharp2.RouteA KAM.Sharp2.L1

/-- The rational entry numbers and an upper bound `ei` of `e⁻¹`. -/
structure EntryQ where
  aN : ℚ
  aL : ℚ
  t1 : ℚ
  tR : ℚ
  G0 : ℚ
  Gρ : ℚ
  frame : Option (ℚ × ℚ)
  ei : ℚ

namespace EntryQ

variable (E : EntryQ)

/-- The real entry record. -/
noncomputable def toA : EntryA :=
  { aN := E.aN, aL := E.aL, t1 := E.t1, tR := E.tR, G0 := E.G0, Gρ := E.Gρ,
    frame := E.frame.map fun f => ⟨f.1, f.2⟩ }

/-- Well-formedness, as a Boolean. -/
def wfB : Bool :=
  decide (0 ≤ E.aN) && decide (0 ≤ E.aL) && decide (0 ≤ E.t1) && decide (0 ≤ E.tR) &&
    decide (0 ≤ E.G0) && decide (0 ≤ E.Gρ) && decide (0 ≤ E.ei) &&
    (match E.frame with
      | some f => decide (0 < f.1) && decide (0 < f.2)
      | none => true)

variable {E}

theorem wf_of (h : E.wfB = true) : E.toA.Wf ∧ 0 ≤ (E.ei : ℝ) := by
  simp only [wfB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨⟨by simp only [toA]; exact_mod_cast h1, by simp only [toA]; exact_mod_cast h2,
    by simp only [toA]; exact_mod_cast h3, by simp only [toA]; exact_mod_cast h4,
    by simp only [toA]; exact_mod_cast h5, by simp only [toA]; exact_mod_cast h6, fun F hF => ?_⟩,
    by exact_mod_cast h7⟩
  rcases hfr : E.frame with _ | f
  · simp [toA, hfr] at hF
  · simp only [toA, hfr, Option.map_some, Option.some.injEq] at hF
    subst hF
    rw [hfr] at h8
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h8
    exact ⟨by simp only; exact_mod_cast h8.1, by simp only; exact_mod_cast h8.2⟩

end EntryQ

namespace StepQ

variable (p : StepQ) (E : EntryQ)

def eTavg : ℚ := min p.t E.tR
def eCavg : ℚ := min (p.ca * p.sLt) (E.Gρ * E.aN * p.g)
def eCS : ℚ := p.sT * (p.sNt * p.g + p.eTavg E * p.eCavg E)
def ecN1 : ℚ := E.G0 * E.aN * p.g
def eCXiN : ℚ := p.eCS E + min (p.c * p.sLt) (p.ecN1 E)
def eCXiN1 : ℚ := p.eCS E + p.ecN1 E
def eCG : ℚ := p.t * p.eCXiN E + p.sNt * p.g
def eCXiL1 : ℚ := E.G0 * p.g * (E.t1 * p.eCXiN1 E + E.aL * p.g)
def eCXiL : ℚ := min (p.c * p.eCG E) (p.eCXiL1 E)
def eCXi : ℚ := max (p.eCXiL E) (p.g * p.eCXiN E)
def eCDK : ℚ := p.sK * p.eCXiL E + p.sN * p.g * p.eCXiN E
def eCOmK : ℚ := min p.COm ((p.n : ℚ) * E.ei * E.G0 * E.aN * p.g)
def eCSym : ℚ := max 1 (p.sB ^ 2) * p.eCOmK E
def eCDXi : ℚ := max (p.eCG E) (p.sLt * p.g)
def eCLin : ℚ := p.CRed * p.eCXi E + p.eCSym E * p.eCDXi E
def eCE : ℚ := 2 * p.P * (p.γb ^ 2 * p.δ) * p.eCLin E + p.M2 / 2 * p.eCDK E ^ 2
def edL : ℚ := match E.frame with
  | some f => min ((p.n : ℚ) * p.eCDK E) (E.ei * (f.1 * p.eCXiL1 E + f.2 * p.g * p.eCXiN1 E))
  | none => (p.n : ℚ) * p.eCDK E
def edLt : ℚ := match E.frame with
  | some f => min (2 * (p.n : ℚ) * p.eCDK E)
      (2 * (p.n : ℚ) * E.ei * (f.1 * p.eCXiL1 E + f.2 * p.g * p.eCXiN1 E))
  | none => 2 * (p.n : ℚ) * p.eCDK E
def eGrK : ℚ := p.sLt * p.edL E + p.sK * p.edLt E
def erB : ℚ := p.sB ^ 2 * (p.sLt * p.edL E + p.sK * p.edLt E) / (1 - p.th)
def erN : ℚ := p.sB * p.edL E + p.sK * p.erB E
def erNt : ℚ := p.erB E * p.sLt + p.sB * p.edLt E
def eCDT : ℚ := 2 * p.M1 * (p.erNt E * p.sN + p.sNt * p.erN E) +
  2 * p.M2 * p.sNt * p.sN * p.δ * p.eCDK E + p.sB ^ 3 * p.w * (p.sK * p.edLt E + p.sLt * p.edL E) +
  2 * (p.n : ℚ) * p.sNt * p.sB * (p.γb ^ 2 * p.δ ^ 2) + p.sB ^ 3 * p.w * (p.COm + p.eCOmK E) * p.g
def erT : ℚ := p.sT ^ 2 / (1 - p.th) * p.eCDT E

/-- The entry rates. -/
def erate : Fin 8 → ℚ :=
  ![p.eCDK E, p.edL E, p.erB E, p.erT E, p.edLt E, p.erN E, p.erNt E, p.eCDT E]

/-- The entry conditions at the normalised error `x`. -/
def econd (x : ℚ) : Bool :=
  decide (p.γb ^ 4 * p.δ ^ 3 * x ≤ 1) &&
    decide (max 1 (p.sB ^ 2) * p.eCOmK E * (p.γb ^ 3 * p.δ ^ 2) * x ≤ 1 / 2) &&
    decide (p.eCE E * x ≤ 1) && decide (p.sT * p.eCDT E * (p.γb ^ 2 * p.δ) * x ≤ p.th) &&
    decide (p.sB * p.eGrK E * (p.γb ^ 2 * p.δ) * x ≤ p.th)

/-! ### The exact casts -/

theorem toA_iso : p.toA.iso = false := rfl
theorem toA_Θ : p.toA.Θ = 0 := rfl

theorem ecast_tavg : Ent.tavg p.toA E.toA = (p.eTavg E : ℝ) := by
  simp [Ent.tavg, eTavg, toA, EntryQ.toA]
theorem ecast_cavg : Ent.cavg p.toA E.toA = (p.eCavg E : ℝ) := by
  simp only [Ent.cavg, cast_g]
  simp [eCavg, toA, EntryQ.toA]
theorem ecast_CS : Ent.CS p.toA E.toA = (p.eCS E : ℝ) := by
  simp only [Ent.CS, toA_iso, Bool.false_eq_true, ite_false, ecast_tavg, ecast_cavg, cast_g]
  simp [eCS, toA]
theorem ecast_cN1 : Ent.cN1 p.toA E.toA = (p.ecN1 E : ℝ) := by
  simp only [Ent.cN1, cast_g]
  simp [ecN1, EntryQ.toA]
theorem ecast_CXiN : Ent.CXiN p.toA E.toA = (p.eCXiN E : ℝ) := by
  simp only [Ent.CXiN, ecast_CS, ecast_cN1]
  simp [eCXiN, toA]
theorem ecast_CXiN1 : Ent.CXiN1 p.toA E.toA = (p.eCXiN1 E : ℝ) := by
  simp only [Ent.CXiN1, ecast_CS, ecast_cN1]
  simp [eCXiN1]
theorem ecast_CG : Ent.CG p.toA E.toA = (p.eCG E : ℝ) := by
  simp only [Ent.CG, ecast_CXiN, ecast_CS, cast_g, toA_Θ, zero_mul, add_zero]
  simp [eCG, toA]
theorem ecast_CXiL1 : Ent.CXiL1 p.toA E.toA = (p.eCXiL1 E : ℝ) := by
  simp only [Ent.CXiL1, ecast_CXiN1, ecast_CS, cast_g, toA_Θ, zero_mul, add_zero]
  simp [eCXiL1, EntryQ.toA]
theorem ecast_CXiL : Ent.CXiL p.toA E.toA = (p.eCXiL E : ℝ) := by
  simp only [Ent.CXiL, ecast_CG, ecast_CXiL1]
  simp [eCXiL, toA]
theorem ecast_CXi : Ent.CXi p.toA E.toA = (p.eCXi E : ℝ) := by
  simp only [Ent.CXi, ecast_CXiL, ecast_CXiN, cast_g]
  simp [eCXi]
theorem ecast_CDK : Ent.CDK p.toA E.toA = (p.eCDK E : ℝ) := by
  simp only [Ent.CDK, ecast_CXiL, ecast_CXiN, cast_g]
  simp [eCDK, toA]
theorem ecast_CDXi : Ent.CDXi p.toA E.toA = (p.eCDXi E : ℝ) := by
  simp only [Ent.CDXi, ecast_CG, cast_g]
  simp [eCDXi, toA]

/-! ### The bounds through `e⁻¹ ≤ ei` -/

variable {p E}

theorem einv_le_one : Ent.einv ≤ 1 := by
  unfold Ent.einv
  rw [inv_le_one₀ (Real.exp_pos 1)]
  exact Real.one_le_exp zero_le_one

theorem le_COmK (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.COmK p.toA E.toA ≤ (p.eCOmK E : ℝ) := by
  have hg := hp.g
  have hG := hE.G0
  have haN := hE.aN
  unfold Ent.COmK
  have e : ((p.eCOmK E : ℚ) : ℝ) =
      min p.toA.COm ((p.toA.n : ℝ) * E.ei * E.toA.G0 * E.toA.aN * p.toA.g) := by
    rw [cast_COm, cast_g]
    simp [eCOmK, toA, EntryQ.toA]
  rw [e]
  refine min_le_min le_rfl ?_
  have hn : (0 : ℝ) ≤ p.toA.n := Nat.cast_nonneg _
  gcongr

theorem le_CSym (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CSym p.toA E.toA ≤ (p.eCSym E : ℝ) := by
  have e : ((p.eCSym E : ℚ) : ℝ) = max 1 (p.toA.sB ^ 2) * (p.eCOmK E : ℝ) := by
    simp [eCSym, toA]
  rw [Ent.CSym, e]
  exact mul_le_mul_of_nonneg_left (le_COmK hp hE hei) (le_max_of_le_left zero_le_one)

theorem le_CLin (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CLin p.toA E.toA ≤ (p.eCLin E : ℝ) := by
  have hk := Ent.nonneg hp hE
  have e : ((p.eCLin E : ℚ) : ℝ) =
      p.toA.CRed * (p.eCXi E : ℝ) + (p.eCSym E : ℝ) * (p.eCDXi E : ℝ) := by
    rw [cast_CRed]
    simp [eCLin]
  rw [Ent.CLin, e, toA_Θ, zero_mul, zero_mul, add_zero, ecast_CXi, ecast_CDXi]
  have := le_CSym hp hE hei
  have hD : (0 : ℝ) ≤ p.eCDXi E := by
    have := hk.CDXi; rwa [ecast_CDXi] at this
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right this hD)

theorem le_CE (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CE p.toA E.toA ≤ (p.eCE E : ℝ) := by
  have e : ((p.eCE E : ℚ) : ℝ) = 2 * p.toA.P * (p.toA.γb ^ 2 * p.toA.δ ^ (2 * p.toA.κ - 1)) *
      (p.eCLin E : ℝ) + p.toA.M2 / 2 * (p.eCDK E : ℝ) ^ 2 := by
    rw [cast_P, toA_κ, rpow_one_nat]
    simp [eCE, toA]
  rw [e]
  simp only [Ent.CE, Ent.CE1, toA_iso, Bool.false_eq_true, ite_false, add_zero, ecast_CDK]
  have hP := hp.P
  have hδ := hp.δ
  have hγ := hp.γb
  have h1 : 0 ≤ 2 * p.toA.P * (p.toA.γb ^ 2 * p.toA.δ ^ (2 * p.toA.κ - 1)) := by
    have := Real.rpow_nonneg hδ.le (2 * p.toA.κ - 1)
    positivity
  exact add_le_add (mul_le_mul_of_nonneg_left (le_CLin hp hE hei) h1) le_rfl

theorem le_dL (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.dL p.toA E.toA ≤ (p.edL E : ℝ) ∧ Ent.dLt p.toA E.toA ≤ (p.edLt E : ℝ) := by
  have hk := Ent.nonneg hp hE
  unfold Ent.dL Ent.dLt edL edLt
  rcases hfr : E.frame with _ | f
  · have hfa : E.toA.frame = none := by simp [EntryQ.toA, hfr]
    simp only [hfa, ecast_CDK]
    exact ⟨by simp [toA], by simp [toA]⟩
  · have hfa : E.toA.frame = some ⟨f.1, f.2⟩ := by simp [EntryQ.toA, hfr]
    obtain ⟨h1, h2⟩ := hE.frame _ hfa
    simp only [hfa, ecast_CDK, ecast_CXiL1, ecast_CXiN1, cast_g]
    have hA : (0 : ℝ) ≤ (f.1 : ℝ) * p.eCXiL1 E + f.2 * p.g * p.eCXiN1 E := by
      have a := hk.CXiL1; have b := hk.CXiN1; have c := hp.g
      rw [ecast_CXiL1] at a; rw [ecast_CXiN1] at b; rw [cast_g] at c
      have : (0 : ℝ) ≤ (f.1 : ℝ) := h1.le
      have : (0 : ℝ) ≤ (f.2 : ℝ) := h2.le
      positivity
    have hn : (0 : ℝ) ≤ p.toA.n := Nat.cast_nonneg _
    constructor
    · push_cast
      refine min_le_min (by simp [toA]) (mul_le_mul_of_nonneg_right hei hA)
    · push_cast
      refine min_le_min (by simp [toA]) ?_
      have : (2 : ℝ) * p.toA.n * Ent.einv ≤ 2 * p.n * E.ei := by
        rw [show (p.toA.n : ℝ) = p.n from rfl]
        exact mul_le_mul_of_nonneg_left hei (by positivity)
      exact mul_le_mul_of_nonneg_right this hA

theorem le_rates (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.GrK p.toA E.toA ≤ (p.eGrK E : ℝ) ∧ Ent.rB p.toA E.toA ≤ (p.erB E : ℝ) ∧
      Ent.rN p.toA E.toA ≤ (p.erN E : ℝ) ∧ Ent.rNt p.toA E.toA ≤ (p.erNt E : ℝ) := by
  obtain ⟨h1, h2⟩ := le_dL hp hE hei
  have hLt := hp.sLt
  have hK := hp.sK
  have hB := hp.sB
  have hth := hp.one_sub_th
  have hrB : Ent.rB p.toA E.toA ≤ (p.erB E : ℝ) := by
    have e : ((p.erB E : ℚ) : ℝ) = p.toA.sB ^ 2 * (p.toA.sLt * (p.edL E : ℝ) +
        p.toA.sK * (p.edLt E : ℝ)) / (1 - p.toA.th) := by
      simp [erB, toA]
    rw [Ent.rB, e]
    gcongr
  refine ⟨?_, hrB, ?_, ?_⟩
  · have e : ((p.eGrK E : ℚ) : ℝ) = p.toA.sLt * (p.edL E : ℝ) + p.toA.sK * (p.edLt E : ℝ) := by
      simp [eGrK, toA]
    rw [Ent.GrK, e]
    gcongr
  · have e : ((p.erN E : ℚ) : ℝ) = p.toA.sB * (p.edL E : ℝ) + p.toA.sK * (p.erB E : ℝ) := by
      simp [erN, toA]
    rw [Ent.rN, e]
    gcongr
  · have e : ((p.erNt E : ℚ) : ℝ) = (p.erB E : ℝ) * p.toA.sLt + p.toA.sB * (p.edLt E : ℝ) := by
      simp [erNt, toA]
    rw [Ent.rNt, e]
    gcongr

theorem le_CDT (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) :
    Ent.CDT p.toA E.toA ≤ (p.eCDT E : ℝ) ∧ Ent.rT p.toA E.toA ≤ (p.erT E : ℝ) := by
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
  have hDT : Ent.CDT p.toA E.toA ≤ (p.eCDT E : ℝ) := by
    have e : ((p.eCDT E : ℚ) : ℝ) =
        2 * p.toA.M1 * ((p.erNt E : ℝ) * p.toA.sN + p.toA.sNt * (p.erN E : ℝ)) +
        2 * p.toA.M2 * p.toA.sNt * p.toA.sN * p.toA.δ * (p.eCDK E : ℝ) +
        p.toA.sB ^ 3 * p.toA.w * (p.toA.sK * (p.edLt E : ℝ) + p.toA.sLt * (p.edL E : ℝ)) +
        2 * (p.toA.n : ℝ) * p.toA.sNt * p.toA.sB * (p.toA.γb ^ 2 * p.toA.δ ^ (2 * p.toA.κ)) +
        p.toA.sB ^ 3 * p.toA.w * (p.toA.COm + (p.eCOmK E : ℝ)) * p.toA.g := by
      rw [cast_w, cast_COm, cast_g, toA_κ, rpow_two_nat]
      simp [eCDT, toA]
    rw [e]
    simp only [Ent.CDT, Ent.CDT0, toA_iso, Bool.false_eq_true, ite_false, ecast_CDK]
    gcongr
  refine ⟨hDT, ?_⟩
  have e : ((p.erT E : ℚ) : ℝ) = p.toA.sT ^ 2 / (1 - p.toA.th) * (p.eCDT E : ℝ) := by
    simp [erT, toA]
  rw [Ent.rT, e]
  have hth := hp.one_sub_th
  have hT := hp.sT
  exact mul_le_mul_of_nonneg_left hDT (by positivity)

/-- Soundness of the rational entry conditions. -/
theorem econd_sound (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) {x : ℚ}
    (hx : 0 ≤ x) (h : p.econd E x = true) : EntryCond p.toA E.toA (x : ℝ) := by
  simp only [econd, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hδ := hp.δ
  have hγ := hp.γb
  have hB := hp.sB
  have hT := hp.sT
  have hCO := le_COmK hp hE hei
  have hCE := le_CE hp hE hei
  have hCDT := (le_CDT hp hE hei).1
  have hGr := (le_rates hp hE hei).1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : ((p.γb ^ 4 * p.δ ^ 3 * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h1
    simp only [toA_κ, rpow_three_nat]
    simpa [toA] using this
  · have h2' : ((max 1 (p.sB ^ 2) * p.eCOmK E * (p.γb ^ 3 * p.δ ^ 2) * x : ℚ) : ℝ) ≤
        ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr h2
    push_cast at h2'
    rw [Ent.COmK_eq]
    simp only [toA_κ, rpow_two_nat']
    refine le_trans ?_ (le_of_le_of_eq h2' (by norm_num))
    have hm : (0 : ℝ) ≤ max 1 (p.sB ^ 2 : ℝ) := le_max_of_le_left zero_le_one
    have : (max 1 (p.toA.sB ^ 2)) = max 1 ((p.sB : ℝ) ^ 2) := rfl
    rw [this]
    have hw : (0 : ℝ) ≤ (p.γb : ℝ) ^ 3 * (p.δ : ℝ) ^ 2 := by
      have : (0 : ℝ) < p.γb := hγ
      positivity
    have hγ' : (p.toA.γb : ℝ) = p.γb := rfl
    have hδ' : (p.toA.δ : ℝ) = p.δ := rfl
    rw [hγ', hδ']
    gcongr
  · have h3' : ((p.eCE E * x : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := Rat.cast_le.mpr h3
    push_cast at h3'
    rw [Ent.CE_eq]
    exact (mul_le_mul_of_nonneg_right hCE hx').trans h3'
  · have h4' : ((p.sT * p.eCDT E * (p.γb ^ 2 * p.δ) * x : ℚ) : ℝ) ≤ (p.th : ℝ) :=
      Rat.cast_le.mpr h4
    push_cast at h4'
    rw [Ent.CDT_eq]
    simp only [toA_κ, rpow_one_nat]
    have hγ' : (p.toA.γb : ℝ) = p.γb := rfl
    have hδ' : (p.toA.δ : ℝ) = p.δ := rfl
    have hT' : (p.toA.sT : ℝ) = p.sT := rfl
    rw [hγ', hδ', hT']
    refine le_trans ?_ h4'
    have : (0 : ℝ) ≤ (p.sT : ℝ) := hT
    have hw : (0 : ℝ) ≤ (p.γb : ℝ) ^ 2 * (p.δ : ℝ) := by
      have : (0 : ℝ) < p.δ := hδ
      have : (0 : ℝ) < p.γb := hγ
      positivity
    gcongr
  · have h5' : ((p.sB * p.eGrK E * (p.γb ^ 2 * p.δ) * x : ℚ) : ℝ) ≤ (p.th : ℝ) :=
      Rat.cast_le.mpr h5
    push_cast at h5'
    rw [Ent.gram_eq]
    simp only [toA_κ, rpow_one_nat]
    have hγ' : (p.toA.γb : ℝ) = p.γb := rfl
    have hδ' : (p.toA.δ : ℝ) = p.δ := rfl
    have hB' : (p.toA.sB : ℝ) = p.sB := rfl
    rw [hγ', hδ', hB']
    refine le_trans ?_ h5'
    have : (0 : ℝ) ≤ (p.sB : ℝ) := hB
    have hw : (0 : ℝ) ≤ (p.γb : ℝ) ^ 2 * (p.δ : ℝ) := by
      have : (0 : ℝ) < p.δ := hδ
      have : (0 : ℝ) < p.γb := hγ
      positivity
    gcongr

theorem le_erate (hp : p.toA.Pos) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) (i : Fin 8) :
    (entryStageA p.toA E.toA).rate i ≤ (p.erate E i : ℝ) := by
  obtain ⟨h1, h2⟩ := le_dL hp hE hei
  obtain ⟨-, h3, h4, h5⟩ := le_rates hp hE hei
  obtain ⟨h6, h7⟩ := le_CDT hp hE hei
  simp only [entryStageA, Ent.CDK_eq, Ent.dL_eq, Ent.rB_eq, Ent.rT_eq, Ent.dLt_eq, Ent.rN_eq,
    Ent.rNt_eq, Ent.CDT_eq]
  fin_cases i <;> simp [erate, ecast_CDK, h1, h2, h3, h4, h5, h6, h7]

end StepQ


namespace NumQ

/-- `sumA` is monotone in the rates and in the errors (nonnegative data). -/
theorem l1_sumA_le {a lam ρ ρinf γb b : ℝ} {x x' c c' : ℕ → ℝ} {kp : ℕ}
    (hd : ∀ t, 0 ≤ deltaSeq lam ρ ρinf t) (hc : ∀ t, 0 ≤ c t ∧ c t ≤ c' t)
    (hx : ∀ t, 0 ≤ x t ∧ x t ≤ x' t) :
    sumA a lam ρ ρinf γb x c b kp ≤ sumA a lam ρ ρinf γb x' c' b kp := by
  have hw : ∀ t, 0 ≤ γb ^ 2 * deltaSeq lam ρ ρinf t ^ (2 * a - b) := fun t =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hd t) _)
  have hcx : ∀ t, c t * x t ≤ c' t * x' t := fun t =>
    mul_le_mul (hc t).2 (hx t).2 (hx t).1 ((hc t).1.trans (hc t).2)
  unfold sumA
  refine add_le_add (Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (hcx t) (hw t)) ?_
  have := mul_le_mul_of_nonneg_right (hcx kp) (hw kp)
  nlinarith [hw kp, mul_nonneg (hc kp).1 (hx kp).1]

variable (Q : NumQ) (E : EntryQ)

/-- The error constant of stage `s` (the entry at `s = 0`). -/
def stCE (s : ℕ) : ℚ := if s = 0 then (Q.inp 0).eCE E else (Q.inp s).CE

/-- The rates of stage `s`. -/
def stRate (s : ℕ) (i : Fin 8) : ℚ := if s = 0 then (Q.inp 0).erate E i else (Q.inp s).rate i

/-- The closeness constant of stage `s`. -/
def stCD (s : ℕ) : ℚ := if s = 0 then (Q.inp 0).eCDK E else (Q.inp s).CDK

/-- `x₀ = X⋆`, `x_{s+1} = 2⁴ C_{E,s} x_s²`, with the entry at `s = 0`. -/
def xL1 (Xs : ℚ) : ℕ → ℚ
  | 0 => Xs
  | s + 1 => 16 * Q.stCE E s * xL1 Xs s ^ 2

/-- The sum of (J3) for the rate `i`. -/
def sumL1 (Xs : ℚ) (i : Fin 8) : ℚ :=
  (∑ t ∈ Finset.range Q.kp, Q.stRate E t i * Q.xL1 E Xs t * (Q.γb ^ 2 * Q.δ t ^ (2 - jA i))) +
    2 * Q.stRate E Q.kp i * Q.xL1 E Xs Q.kp * (Q.γb ^ 2 * Q.δ Q.kp ^ (2 - jA i))

/-- The sum of the closeness estimate. -/
def sumDL1 (Xs : ℚ) : ℚ :=
  (∑ t ∈ Finset.range Q.kp, Q.stCD E t * Q.xL1 E Xs t * (1 ^ 2 * Q.δ t ^ 2)) +
    2 * Q.stCD E Q.kp * Q.xL1 E Xs Q.kp * (1 ^ 2 * Q.δ Q.kp ^ 2)

/-- (J0)–(J3) with the entry, as one Boolean. -/
def okL1 (σ m₀ : Fin 8 → ℚ) (Xs : ℚ) : Bool :=
  decide (0 ≤ Xs) && decide (1 ≤ Q.kp) && E.wfB && (Q.inp 0).econd E Xs &&
    (List.range Q.kp).all (fun s => decide (s = 0) || (Q.inp s).cond (Q.xL1 E Xs s)) &&
    (Q.inp Q.kp).cond (Q.xL1 E Xs Q.kp) && decide (16 * (Q.inp Q.kp).CE * Q.xL1 E Xs Q.kp ≤ 1) &&
    decide (∀ i, m₀ i + Q.sumL1 E Xs i ≤ σ i)

variable {Q E}

theorem l1_four_rpow : (2 : ℝ) ^ (2 * (2 * (1 : ℝ))) = 16 := by
  rw [show (2 * (2 * (1 : ℝ))) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The real stage constants against their mirrors. -/
theorem l1_stage_bounds (hQ : Q.toA.Wf) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) (s : ℕ) :
    (0 ≤ (stageL1 Q.toA E.toA s).CE ∧ (stageL1 Q.toA E.toA s).CE ≤ (Q.stCE E s : ℝ)) ∧
    (∀ i, 0 ≤ (stageL1 Q.toA E.toA s).rate i ∧
      (stageL1 Q.toA E.toA s).rate i ≤ (Q.stRate E s i : ℝ)) ∧
    (stageL1 Q.toA E.toA s).CD = (Q.stCD E s : ℝ) := by
  have hp0 : (Q.inp 0).toA.Pos := by rw [← Q.cast_inp]; exact hQ.pos 0
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have hst : stageL1 Q.toA E.toA 0 = entryStageA (Q.inp 0).toA E.toA := by
      simp [stageL1, Q.cast_inp]
    have hk := Ent.nonneg hp0 hE
    rw [hst]
    refine ⟨⟨?_, ?_⟩, fun i => ⟨entryStageA_rate_nonneg hp0 hE i, ?_⟩, ?_⟩
    · simp only [entryStageA, Ent.CE_eq]; exact hk.CE
    · simp only [entryStageA, Ent.CE_eq, stCE, ite_true]; exact StepQ.le_CE hp0 hE hei
    · simp only [stRate, ite_true]; exact StepQ.le_erate hp0 hE hei i
    · simp only [entryStageA, Ent.CDK_eq, stCD, ite_true]; exact StepQ.ecast_CDK _ _
  · have hs0 : s ≠ 0 := hs.ne'
    have hst : stageL1 Q.toA E.toA s = Q.toA.stage s := by simp [stageL1, hs0]
    rw [hst]
    refine ⟨⟨(hQ.pos s).CE, ?_⟩, fun i => ⟨NumA.rateV_nonneg (hQ.pos s) i, ?_⟩, ?_⟩
    · show (Q.toA.inp s).CE ≤ _
      simp only [stCE, hs0, ite_false]
      rw [Q.cast_inp, StepQ.cast_CE]
    · show NumA.rateV (Q.toA.inp s) i ≤ _
      simp only [stRate, hs0, ite_false]
      rw [Q.cast_inp, StepQ.cast_rate]
    · show (Q.toA.inp s).CDK = _
      simp only [stCD, hs0, ite_false]
      rw [Q.cast_inp, StepQ.cast_CDK]

/-- The real errors are bounded by their mirrors. -/
theorem l1_x_bounds (hQ : Q.toA.Wf) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) {Xs : ℚ}
    (hX : 0 ≤ Xs) (s : ℕ) :
    0 ≤ xSL1 Q.toA E.toA (Xs : ℝ) s ∧ xSL1 Q.toA E.toA (Xs : ℝ) s ≤ (Q.xL1 E Xs s : ℝ) := by
  induction s with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (0 : ℝ) ≤ (Xs : ℝ)
      exact_mod_cast hX
    · show (Xs : ℝ) ≤ ((Q.xL1 E Xs 0 : ℚ) : ℝ)
      simp [xL1]
  | succ s ih =>
    obtain ⟨⟨hc0, hc⟩, -, -⟩ := l1_stage_bounds hQ hE hei s
    have e1 : xSL1 Q.toA E.toA (Xs : ℝ) (s + 1) =
        2 ^ (2 * (2 * Q.toA.τ)) * (stageL1 Q.toA E.toA s).CE * xSL1 Q.toA E.toA (Xs : ℝ) s ^ 2 :=
      rfl
    have hτ : Q.toA.τ = 1 := rfl
    rw [e1, hτ, l1_four_rpow]
    have e2 : ((Q.xL1 E Xs (s + 1) : ℚ) : ℝ) =
        16 * (Q.stCE E s : ℝ) * (Q.xL1 E Xs s : ℝ) ^ 2 := by
      simp [xL1]
    rw [e2]
    refine ⟨by positivity, ?_⟩
    have h1 : (stageL1 Q.toA E.toA s).CE * xSL1 Q.toA E.toA (Xs : ℝ) s ^ 2 ≤
        (Q.stCE E s : ℝ) * (Q.xL1 E Xs s : ℝ) ^ 2 :=
      mul_le_mul hc (pow_le_pow_left₀ ih.1 ih.2 2) (by positivity) (hc0.trans hc)
    nlinarith

/-- **Soundness of the rational check with the ℓ¹ entry.** -/
theorem okL1_sound (hQ : Q.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) {σ m₀ : Fin 8 → ℚ} {Xs : ℚ}
    (h : Q.okL1 E σ m₀ Xs = true) :
    E.toA.Wf ∧
      routeAOkL1 Q.toA E.toA (fun i => (σ i : ℝ)) (fun i => (m₀ i : ℝ)) (Xs : ℝ) := by
  simp only [okL1, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, hkp⟩, hwf⟩, hJ0⟩, hJ1⟩, hJ1t⟩, hJ2⟩, hJ3⟩ := h
  obtain ⟨hE, -⟩ := EntryQ.wf_of hwf
  have hp0 : (Q.inp 0).toA.Pos := by rw [← Q.cast_inp]; exact hQ.pos 0
  have hx := l1_x_bounds hQ hE hei h0
  refine ⟨hE, ⟨hkp, by exact_mod_cast h0, ?_, fun s hs1 hs => ?_, ?_, ?_, fun i => ?_⟩⟩
  · rw [Q.cast_inp]
    exact StepQ.econd_sound hp0 hE hei h0 hJ0
  · have hc : (Q.inp s).cond (Q.xL1 E Xs s) = true := by
      rcases hJ1 s hs with h1 | h1
      · omega
      · exact h1
    have := StepQ.cond_sound hc
    rw [← Q.cast_inp] at this
    exact this.down (hQ.pos s) (hx s).2
  · have := StepQ.cond_sound hJ1t
    rw [← Q.cast_inp] at this
    exact this.down (hQ.pos _) (hx _).2
  · have hτ : Q.toA.τ = 1 := rfl
    have hk : Q.toA.kp = Q.kp := rfl
    rw [hτ, l1_four_rpow, hk]
    have hC : (Q.toA.stage Q.kp).CE = ((Q.inp Q.kp).CE : ℝ) := by
      show (Q.toA.inp Q.kp).CE = _
      rw [Q.cast_inp, StepQ.cast_CE]
    rw [hC]
    have h3 : ((16 * (Q.inp Q.kp).CE * Q.xL1 E Xs Q.kp : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hJ2
    push_cast at h3
    have hCE0 : (0 : ℝ) ≤ (Q.inp Q.kp).CE := by
      rw [← StepQ.cast_CE, ← Q.cast_inp]; exact (hQ.pos _).CE
    refine le_trans ?_ h3
    exact mul_le_mul_of_nonneg_left (hx _).2 (by positivity)
  · have hd : ∀ t, 0 ≤ deltaSeq 3 Q.toA.ρ Q.toA.ρinf t := fun t => (hQ.δ_pos t).le
    have hle := l1_sumA_le (a := 2 * Q.toA.τ) (γb := Q.toA.γb) (b := 2 * Q.toA.τ + (jA i : ℝ))
      (kp := Q.toA.kp) hd (fun t => (l1_stage_bounds hQ hE hei t).2.1 i) hx
    have hcast : sumA (2 * Q.toA.τ) 3 Q.toA.ρ Q.toA.ρinf Q.toA.γb
        (fun t => (Q.xL1 E Xs t : ℝ)) (fun t => (Q.stRate E t i : ℝ))
        (2 * Q.toA.τ + (jA i : ℝ)) Q.toA.kp = (Q.sumL1 E Xs i : ℝ) := by
      have hd' : ∀ t, deltaSeq 3 Q.toA.ρ Q.toA.ρinf t = (Q.δ t : ℝ) := Q.cast_δ
      have hτ : Q.toA.τ = 1 := rfl
      have hk : Q.toA.kp = Q.kp := rfl
      have hγ : Q.toA.γb = (Q.γb : ℝ) := rfl
      simp only [sumA, hτ, hk, hγ, hd', rpow_sum, sumL1]
      push_cast
      rfl
    have h4 : ((m₀ i + Q.sumL1 E Xs i : ℚ) : ℝ) ≤ (σ i : ℝ) := Rat.cast_le.mpr (hJ3 i)
    push_cast at h4
    exact (add_le_add le_rfl (hle.trans hcast.le)).trans h4

/-- The closeness constant of the entry branch, in rational form. -/
theorem sumDL1_le (hQ : Q.toA.Wf) (hE : E.toA.Wf) (hei : Ent.einv ≤ (E.ei : ℝ)) {Xs : ℚ}
    (hX : 0 ≤ Xs) :
    sumA (2 * Q.toA.τ) 3 Q.toA.ρ Q.toA.ρinf 1 (xSL1 Q.toA E.toA (Xs : ℝ))
      (fun s => (stageL1 Q.toA E.toA s).CD) (2 * Q.toA.τ) Q.toA.kp ≤
    (Q.sumDL1 E Xs : ℝ) := by
  have hd : ∀ t, 0 ≤ deltaSeq 3 Q.toA.ρ Q.toA.ρinf t := fun t => (hQ.δ_pos t).le
  have hc : ∀ t, 0 ≤ (stageL1 Q.toA E.toA t).CD ∧
      (stageL1 Q.toA E.toA t).CD ≤ (Q.stCD E t : ℝ) := fun t => by
    rw [(l1_stage_bounds hQ hE hei t).2.2]
    refine ⟨?_, le_rfl⟩
    rw [← (l1_stage_bounds hQ hE hei t).2.2]
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht
      have hp0 : (Q.inp 0).toA.Pos := by rw [← Q.cast_inp]; exact hQ.pos 0
      have hst : stageL1 Q.toA E.toA 0 = entryStageA (Q.inp 0).toA E.toA := by
        simp [stageL1, Q.cast_inp]
      rw [hst]
      simp only [entryStageA, Ent.CDK_eq]
      exact (Ent.nonneg hp0 hE).CDK
    · have hst : stageL1 Q.toA E.toA t = Q.toA.stage t := by simp [stageL1, ht.ne']
      rw [hst]
      exact (hQ.pos t).CDK
  have hle := l1_sumA_le (a := 2 * Q.toA.τ) (γb := 1) (b := 2 * Q.toA.τ) (kp := Q.toA.kp) hd hc
    (l1_x_bounds hQ hE hei hX)
  refine hle.trans (le_of_eq ?_)
  have hd' : ∀ t, deltaSeq 3 Q.toA.ρ Q.toA.ρinf t = (Q.δ t : ℝ) := Q.cast_δ
  have hτ : Q.toA.τ = 1 := rfl
  have hk : Q.toA.kp = Q.kp := rfl
  have hp : ∀ y : ℝ, y ^ (2 * (2 * (1 : ℝ)) - 2 * (1 : ℝ)) = y ^ 2 := fun y => by
    rw [show (2 * (2 * (1 : ℝ)) - 2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [sumA, hτ, hk, hd', hp, sumDL1]
  push_cast
  rfl

end NumQ

end KAM.Sharp2.Examples

end
