/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.Threshold

/-!
# HD 11964: the action box, the threshold `B = Λ_c` and the data of LP-LIFT

Design `docs/campaign/design/HD11964-PILOT.md` §2 and §5; the numbers are those of the pinned data
`applications/hd11964/data/hd11964-pilot.json` and of `validation/threshold.json` (decided there in
exact rationals by `scripts/threshold.py`; here by `norm_num`).

Model: LP's `movingHamiltonian 1 1 ν μ`, planets `0 = c` (inner), `1 = b` (outer), minimum masses
(`m sin i`), coplanar. `ν = (m_c / m_b, 1)` and `μ = m_b / M⋆` are the exact rationals of the pinned
catalogue decimals.

* `actionBox = [Λlo - r, Λhi + r]` is the shared compact action set `U` of LP-LIFT.
* `actionBox_subset_chamber`, `strongThreshold_eq_on_box`: `U` lies in the chamber and the strong
  threshold is the star threshold of planet c, `B(I) = I_c`, on all of `U` (the pair threshold is at
  least `0.785 > 0.0626 ≥ I_c`, by the monotone bound `pairThreshold_ge_of_axis`).
* `liftData`: every initial state with actions in `[Λlo, Λhi]`, strong AMD `C ≤ 1/100` and `L > 0`
  gives `LiftData ν U z₀ δ r` with `δ = Λlo_c - 1/100` and `r = 1/250`.
-/

@[expose] public noncomputable section

open Set KAM.Planetary KAM.Planetary.StrongAMD KAM.Application.LambdaDrift

namespace HD11964

/-- Masses: `ν = (m_c / m_b, 1)` (minimum masses; exact rational of the pinned decimals). -/
def nu : Fin 2 → ℝ := ![1217282799 / 10027486241, 1]

/-- The mass parameter `μ = m_b / M⋆` (minimum mass of b; exact rational of the pinned decimals). -/
def mu : ℝ := 2005497248200 / 3833351025484041

/-- Lower corner of the initial action box (`Λ̂ - (10⁻⁴, 3·10⁻³)`, rounded outward). -/
def lamLo : Fin 2 → ℝ := ![116621 / 2000000, 4454241 / 2500000]

/-- Upper corner of the initial action box (`Λ̂ + (10⁻⁴, 3·10⁻³)`, rounded outward). -/
def lamHi : Fin 2 → ℝ := ![292553 / 5000000, 3575393 / 2000000]

/-- The initial strong-AMD bound `Cbar` (nominal `Ĉ = 0.009455`, plus 6 %). -/
def cBar : ℝ := 1 / 100

/-- The tube radius `r` of LP-LIFT. -/
def rTube : ℝ := 1 / 250

/-- The AMD margin `δ = Λlo_c - Cbar`. -/
def delta : ℝ := 96621 / 2000000

/-- The shared compact action set `U = [Λlo - r, Λhi + r]`. -/
def actionBox : Set (Fin 2 → ℝ) := Icc (fun i => lamLo i - rTube) (fun i => lamHi i + rTube)

theorem nu_pos : ∀ i, 0 < nu i := by
  intro i; fin_cases i <;> norm_num [nu]

theorem delta_eq : delta = lamLo 0 - cBar := by norm_num [delta, lamLo, cBar]

theorem delta_pos : 0 < delta := by norm_num [delta]

theorem rTube_pos : 0 < rTube := by norm_num [rTube]

theorem isCompact_actionBox : IsCompact actionBox := isCompact_Icc

/-- The coordinates of a point of the box, against the rational corners. -/
theorem bounds_of_mem {I : Fin 2 → ℝ} (hI : I ∈ actionBox) :
    108621 / 2000000 ≤ I 0 ∧ I 0 ≤ 312553 / 5000000 ∧
      4444241 / 2500000 ≤ I 1 ∧ I 1 ≤ 3583393 / 2000000 := by
  have h0 := hI.1 0
  have h1 := hI.1 1
  have h2 := hI.2 0
  have h3 := hI.2 1
  simp only [lamLo, lamHi, rTube, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- `I_c / ν_c < 0.515 < I_b` on the box: the outer axis dominates. -/
theorem axis_bounds {I : Fin 2 → ℝ} (hI : I ∈ actionBox) :
    0 ≤ I 0 / nu 0 ∧ I 0 / nu 0 ≤ 103 / 200 := by
  obtain ⟨h0, h1, -, -⟩ := bounds_of_mem hI
  have hnu : nu 0 = 1217282799 / 10027486241 := by simp [nu]
  rw [hnu]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by norm_num)]
  linarith

theorem actionBox_subset_chamber : actionBox ⊆ chamber nu := by
  intro I hI
  obtain ⟨h0, -, h2, -⟩ := bounds_of_mem hI
  obtain ⟨hx0, hx1⟩ := axis_bounds hI
  have hnu1 : nu 1 = 1 := by simp [nu]
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i
    · show 0 < I 0; linarith
    · show 0 < I 1; linarith
  · fin_cases i <;> fin_cases j
    · exact absurd hij (lt_irrefl _)
    · show (I 0 / nu 0) ^ 2 < (I 1 / nu 1) ^ 2
      rw [hnu1, div_one]
      nlinarith
    · exact absurd hij (by decide)
    · exact absurd hij (lt_irrefl _)

/-- The pair threshold of (c, b) is at least `I_c` on the box (`pairThreshold_ge_of_axis` with
`v₀ = 0.83`, `s = 0.558`: it is at least `0.442 I_b ≥ 0.785`). -/
theorem le_pairThreshold {I : Fin 2 → ℝ} (hI : I ∈ actionBox) : I 0 ≤ pairThreshold nu I 0 1 := by
  obtain ⟨h0, h1, h2, -⟩ := bounds_of_mem hI
  obtain ⟨hx0, hx1⟩ := axis_bounds hI
  have hnu1 : nu 1 = 1 := by simp [nu]
  have ha1 : actionAxis nu I 1 = I 1 ^ 2 := by simp [actionAxis, hnu1]
  have ha0 : actionAxis nu I 0 = (I 0 / nu 0) ^ 2 := rfl
  have key := pairThreshold_ge_of_axis (ν := nu) (I := I) (i := 0) (j := 1) (by linarith)
    (by linarith) (by rw [ha1]; positivity) (v₀ := 83 / 100) (s := 558 / 1000) (by norm_num)
    (by
      rw [ha0, ha1]
      nlinarith [mul_le_mul hx1 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 103 / 200),
        mul_le_mul h2 h2 (by norm_num : (0 : ℝ) ≤ 4444241 / 2500000) (by linarith)])
    (by norm_num) (by norm_num)
  linarith

/-- **`B = Λ_c` on the box** (design §5): the strong threshold is the star threshold of planet c. -/
theorem strongThreshold_eq_on_box {I : Fin 2 → ℝ} (hI : I ∈ actionBox) :
    strongThreshold nu I = I 0 := by
  obtain ⟨-, h1, h2, -⟩ := bounds_of_mem hI
  refine strongThreshold_eq_of_le le_rfl (fun i => ?_) (fun a => ?_)
  · fin_cases i
    · exact le_rfl
    · show I 0 ≤ I 1; linarith
  · have ha1 : a.1 = 0 := Fin.ext (by rw [Fin.val_zero]; have := a.2; omega)
    have ha2 : a.upperIdx = 1 := Fin.ext (by
      show a.1.val + 1 = 1
      rw [ha1]; rfl)
    rw [ha1, ha2]
    exact le_pairThreshold hI

/-- **The data of LP-LIFT for HD 11964.** Every physical initial state with actions in `[Λlo, Λhi]`,
strong AMD at most `Cbar = 1/100` and positive angular momentum satisfies
`LiftData ν U z₀ δ r` with `U = [Λlo - r, Λhi + r]`, `δ = Λlo_c - Cbar` and `r = 1/250`. -/
theorem liftData {z₀ : KAM.Planetary.Phase (2 * 2)} (hphys : IsPhysicalState nu z₀)
    (hbox : ∀ i, lamLo i ≤ keplerAction nu z₀ i ∧ keplerAction nu z₀ i ≤ lamHi i)
    (hC : strongAMD nu z₀ ≤ cBar) (hL : 0 < totalMomentum z₀) :
    LiftData nu actionBox z₀ delta rTube := by
  have hΛ : actionVector nu z₀ ∈ Icc lamLo lamHi :=
    ⟨fun i => (hbox i).1, fun i => (hbox i).2⟩
  refine liftData_of_star nu_pos le_rfl isCompact_actionBox actionBox_subset_chamber (k := 0)
    (fun I hI => strongThreshold_eq_on_box hI) delta_pos rTube_pos ?_ hphys
    (fun I hI => mem_Icc_of_norm_sub_le hΛ hI) ?_ hL
  · norm_num [rTube, delta]
  · have := (hbox 0).1
    rw [delta_eq]
    linarith

end HD11964

end
