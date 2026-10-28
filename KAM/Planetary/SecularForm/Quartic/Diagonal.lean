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

include hI hJ hab in
/-- `stepP:p8:q4-b`: the exact coefficient of `|uᵢ|⁴`. -/
theorem quarticCoeff_zero :
    quarticCoeff D i j (I0, J0) 0 = -D.G * D.m i * D.m j *
      (iteratedDeriv 4 (radialH (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
        (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))) 0 / 64 -
       iteratedDeriv 2 (radialH (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
        (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))) 0 / 16) / I0 ^ 2 := by
  obtain ⟨r, C, hr, hC, hjet⟩ := pairSlowSecular_diag_jet D i j hI hJ hab.ne
  have h0 : quarticCoeff D i j (I0, J0) 0 = pairQuartic D i j I0 J0 (testPt 0) := by
    simp [quarticCoeff]
  rw [h0]
  set H := radialH (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0))) (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))
    with hH
  refine pairQuartic_of_ray D i j hI hJ hab (testPt 0)
    (A := -D.G * D.m i * D.m j * H 0)
    (B := -D.G * D.m i * D.m j * (iteratedDeriv 2 H 0 / 4 / I0))
    (Cc := -D.G * D.m i * D.m j * (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) / I0 ^ 2)
    (K := C) (r := r) hr fun s hs => ?_
  have hu : planeLength (s • (![1, 0] : Fin 2 → ℝ)) < r := by
    rw [planeLength_smul_e1]; exact hs
  have e1 : s • testPt 0 = (s • (![1, 0] : Fin 2 → ℝ), (0 : Fin 2 → ℝ)) := by
    refine Prod.ext rfl ?_
    ext k; fin_cases k <;> simp [testPt]
  have h := hjet _ hu
  rw [planeLength_smul_e1, planeSq_smul_e1] at h
  rw [e1]
  have e : -D.G * D.m i * D.m j * H 0 +
      -D.G * D.m i * D.m j * (iteratedDeriv 2 H 0 / 4 / I0) * s ^ 2 +
      -D.G * D.m i * D.m j * (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) / I0 ^ 2 *
        s ^ 4 =
      -D.G * D.m i * D.m j * (H 0 + iteratedDeriv 2 H 0 / 4 * (s ^ 2 / I0) +
        (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) * (s ^ 2 / I0) ^ 2) := by
    ring
  rw [e]
  exact h

include hI hJ hab in
/-- `stepP:p8:q4-b`: the exact coefficient of `|uⱼ|⁴`. -/
theorem quarticCoeff_one :
    quarticCoeff D i j (I0, J0) 1 = -D.G * D.m i * D.m j *
      (iteratedDeriv 4 (radialH (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))
        (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))) 0 / 64 -
       iteratedDeriv 2 (radialH (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))
        (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))) 0 / 16) / J0 ^ 2 := by
  obtain ⟨r, C, hr, hC, hjet⟩ := pairSlowSecular_diag_jet D j i hJ hI hab.ne'
  obtain ⟨N, hN, h0, -, -, -, hcont⟩ := pair_secular_nbhd D i j hI hJ hab
  have hmapc : Continuous fun s : ℝ => (((I0, J0) : ℝ × ℝ),
      ((0 : Fin 2 → ℝ), s • (![1, 0] : Fin 2 → ℝ))) := by fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (((I0, J0) : ℝ × ℝ),
      ((0 : Fin 2 → ℝ), s • (![1, 0] : Fin 2 → ℝ))) ∈ N :=
    (hN.preimage hmapc).mem_nhds (by
      show (((I0, J0) : ℝ × ℝ), ((0 : Fin 2 → ℝ), (0 : ℝ) • (![1, 0] : Fin 2 → ℝ))) ∈ N
      rw [zero_smul]; exact h0)
  obtain ⟨r1, hr1, hr1N⟩ := Metric.eventually_nhds_iff.1 hev
  have h1 : quarticCoeff D i j (I0, J0) 1 = pairQuartic D i j I0 J0 (testPt 1) := by
    simp [quarticCoeff]
  rw [h1]
  set H := radialH (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)))
    with hH
  refine pairQuartic_of_ray D i j hI hJ hab (testPt 1)
    (A := -D.G * D.m i * D.m j * H 0)
    (B := -D.G * D.m i * D.m j * (iteratedDeriv 2 H 0 / 4 / J0))
    (Cc := -D.G * D.m i * D.m j * (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) / J0 ^ 2)
    (K := C) (r := min r r1) (lt_min hr hr1) fun s hs => ?_
  have hsr : |s| < r := lt_of_lt_of_le hs (min_le_left _ _)
  have hsr1 : |s| < r1 := lt_of_lt_of_le hs (min_le_right _ _)
  have hu : planeLength (s • (![1, 0] : Fin 2 → ℝ)) < r := by
    rw [planeLength_smul_e1]; exact hsr
  have e1 : s • testPt 1 = ((0 : Fin 2 → ℝ), s • (![1, 0] : Fin 2 → ℝ)) := by
    refine Prod.ext ?_ rfl
    ext k; fin_cases k <;> simp [testPt]
  have hmem := hr1N (y := s) (by simpa [Real.dist_eq] using hsr1)
  have hc : Continuous fun q : ℝ × ℝ => quarticPairKernel D i j I0 J0
      ((0 : Fin 2 → ℝ), s • (![1, 0] : Fin 2 → ℝ)) q.1 q.2 := by
    have := hcont _ hmem
    simpa only [pairKernel_eq_quarticPairKernel] using this
  have hsw := pairSlowSecular_swap D i j I0 J0 (s • (![1, 0] : Fin 2 → ℝ)) hc
  have h := hjet _ hu
  rw [planeLength_smul_e1, planeSq_smul_e1] at h
  rw [e1, ← hsw]
  have e : -D.G * D.m i * D.m j * H 0 +
      -D.G * D.m i * D.m j * (iteratedDeriv 2 H 0 / 4 / J0) * s ^ 2 +
      -D.G * D.m i * D.m j * (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) / J0 ^ 2 *
        s ^ 4 =
      -D.G * D.m j * D.m i * (H 0 + iteratedDeriv 2 H 0 / 4 * (s ^ 2 / J0) +
        (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) * (s ^ 2 / J0) ^ 2) := by
    ring
  rw [e]
  exact h

end SecularForm
end KAM.Planetary
end
