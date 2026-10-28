/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Swap
public import KAM.Planetary.SecularForm.Quartic.Coefficients
public import KAM.Planetary.SecularForm.Quartic.Taylor
public import KAM.Planetary.SecularForm.Quartic.Defs
public import KAM.Planetary.SecularForm.DiagonalJet

/-!
# Secular form: the exact diagonal quartic coefficients

Blueprint P, Part 8, `stepP:p8:q4-b`: the coefficients of `|uᵢ|⁴` and `|uⱼ|⁴` in the quartic jet
of the pair average, read off from the circular-partner expansion `pairSlowSecular_diag_jet`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ}

theorem planeSq_smul_e1 (s : ℝ) : planeSq (s • (![1, 0] : Fin 2 → ℝ)) = s ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

theorem planeLength_smul_e1 (s : ℝ) : planeLength (s • (![1, 0] : Fin 2 → ℝ)) = |s| := by
  rw [planeLength, planeSq_smul_e1, Real.sqrt_sq_eq_abs]

variable (D : Data n) (i j : Fin n) {I0 J0 : ℝ} (hI : 0 < I0) (hJ : 0 < J0)
  (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))

include hI hJ hab in
/-- The fourth derivative along a ray, read off from an `O(s⁶)` expansion. -/
theorem pairQuartic_of_ray (w : PairW) {A B Cc K r : ℝ} (hr : 0 < r)
    (h : ∀ s : ℝ, |s| < r →
      |pairSlowSecular D i j I0 J0 (s • w) - (A + B * s ^ 2 + Cc * s ^ 4)| ≤ K * |s| ^ 6) :
    pairQuartic D i j I0 J0 w = Cc := by
  obtain ⟨U, hU, h0, hcd⟩ := pair_contDiffOn D i j hI hJ hab
  let ℓ : ℝ →L[ℝ] PairW := ContinuousLinearMap.toSpanSingleton ℝ w
  have hℓ : ∀ s, ℓ s = s • w := fun s => rfl
  have hψ : AnalyticAt ℝ (fun s : ℝ => pairSlowSecular D i j I0 J0 (s • w)) 0 := by
    have h1 := analyticAt_pairSlowSecular D i j hI hJ hab
    have h2 : AnalyticAt ℝ (fun s : ℝ => (((I0, J0) : ℝ × ℝ), s • w)) 0 :=
      analyticAt_const.prod (analyticAt_id.smul analyticAt_const)
    have hg : AnalyticAt ℝ (fun p : (ℝ × ℝ) × PairW => pairSlowSecular D i j p.1.1 p.1.2 p.2)
        (((I0, J0) : ℝ × ℝ), (0 : ℝ) • w) := by
      rw [zero_smul]; exact h1
    have hcomp := AnalyticAt.comp (f := fun s : ℝ => (((I0, J0) : ℝ × ℝ), s • w)) hg h2
    exact hcomp
  have h4 := iteratedDeriv_four_of_expansion hψ hr h
  have key := iteratedFDeriv_comp_clm_of_isOpen hU hcd ℓ (x := 0)
    (by rw [map_zero]; exact h0) (le_refl 4)
  have e : iteratedDeriv 4 (fun s : ℝ => pairSlowSecular D i j I0 J0 (s • w)) 0 =
      iteratedFDeriv ℝ 4 (fun w' : PairW => pairSlowSecular D i j I0 J0 w') 0 (fun _ => w) := by
    rw [iteratedDeriv_eq_iteratedFDeriv]
    have : (fun s : ℝ => pairSlowSecular D i j I0 J0 (s • w)) =
        (fun w' : PairW => pairSlowSecular D i j I0 J0 w') ∘ ℓ := rfl
    rw [this, key]
    simp [hℓ]
  unfold pairQuartic
  rw [← e, h4]
  ring

end SecularForm
end KAM.Planetary
end
