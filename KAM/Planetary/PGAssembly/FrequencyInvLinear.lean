/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib

/-!
# P Part 5: elementary estimates for the inverse of the frequency derivative

`lower_of_hasFDerivAt`: a lower Lipschitz bound on an open set passes to the derivative.
`inv_apriori`: the a priori estimate of the block system (`stepP:p5:fi-blk`, `fi-inv`) as
an inequality between the norms of the two blocks of a vector and of its image.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FI.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace KAM.Planetary

/-- A lower Lipschitz bound on an open set bounds the derivative from below. -/
theorem lower_of_hasFDerivAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {U : Set E} (hU : IsOpen U) {c : ℝ}
    (hc : ∀ z ∈ U, ∀ z' ∈ U, c * ‖z - z'‖ ≤ ‖f z - f z'‖) {z : E} (hz : z ∈ U)
    {L : E →L[ℂ] F} (hf : HasFDerivAt f L z) (u : E) : c * ‖u‖ ≤ ‖L u‖ := by
  have hline : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
  have hg : HasDerivAt (fun t : ℝ => f (z + t • u)) (L u) 0 := by
    have hf' : HasFDerivAt f (L.restrictScalars ℝ) (z + (0 : ℝ) • u) := by
      simpa using hf.restrictScalars ℝ
    exact hf'.comp_hasDerivAt (0 : ℝ) hline
  have hT := hg.tendsto_slope_zero_right
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, c * ‖u‖ ≤ ‖t⁻¹ • (f (z + (0 + t) • u) - f (z + (0 : ℝ) • u))‖ := by
    have hcont : ContinuousAt (fun t : ℝ => z + t • u) 0 := by fun_prop
    have h1 : ∀ᶠ t : ℝ in 𝓝 0, z + t • u ∈ U :=
      hcont.eventually (hU.mem_nhds (by simpa using hz))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with t ht htpos
    have htpos : 0 < t := htpos
    have := hc _ ht z hz
    simp only [zero_add, zero_smul, add_zero] at this ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 htpos)]
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] at this
    rw [inv_mul_eq_div, le_div_iff₀ htpos]
    linarith
  exact ge_of_tendsto hT.norm hev

/-- The a priori estimate of the block system `[[A, mu B], [mu C, mu D]] v = w`. -/
theorem inv_apriori {mu c0 AN LB X Y Wf Ws : ℝ} (hmu0 : 0 < mu) (hc0 : 0 < c0)
    (hAN : 1 ≤ AN) (hLB : 1 ≤ LB) (h3 : mu * AN ≤ c0 / 2) (h4 : 4 * mu * AN ^ 2 * LB ≤ c0)
    (hX : 0 ≤ X) (hWf : 0 ≤ Wf)
    (h1 : c0 * X ≤ Wf + mu * AN * X + mu * AN * Y) (h2 : mu * Y ≤ LB * (Ws + mu * AN * X)) :
    X ≤ (4 * (AN + 1) ^ 2 * LB / c0 + 4) * max Wf Ws ∧ Y ≤ (8 * LB + 4) / mu * max Wf Ws := by
  set W := max Wf Ws with hW
  have hWf' : Wf ≤ W := le_max_left _ _
  have hWs' : Ws ≤ W := le_max_right _ _
  have hW0 : 0 ≤ W := hWf.trans hWf'
  have hAN0 : 0 ≤ AN := by linarith
  have hLB0 : 0 ≤ LB := by linarith
  -- mu * Y ≤ LB * W + LB * mu * AN * X
  have h2' : mu * Y ≤ LB * W + LB * (mu * AN) * X := by
    have : LB * Ws ≤ LB * W := mul_le_mul_of_nonneg_left hWs' hLB0
    nlinarith
  have h1' : c0 * X ≤ W + mu * AN * X + AN * (LB * W + LB * (mu * AN) * X) := by
    have : AN * (mu * Y) ≤ AN * (LB * W + LB * (mu * AN) * X) := mul_le_mul_of_nonneg_left h2' hAN0
    nlinarith
  have hq : 4 * (mu * AN ^ 2 * LB) ≤ c0 := by nlinarith
  have hmaX : mu * AN ^ 2 * LB * X ≤ c0 / 4 * X := mul_le_mul_of_nonneg_right (by linarith) hX
  have hmX : mu * AN * X ≤ c0 / 2 * X := mul_le_mul_of_nonneg_right h3 hX
  have hX1 : c0 / 4 * X ≤ (1 + AN * LB) * W := by nlinarith
  have hX2 : X ≤ 4 * (AN + 1) ^ 2 * LB / c0 * W := by
    have hb : (1 + AN * LB) * W ≤ (AN + 1) ^ 2 * LB * W := by
      apply mul_le_mul_of_nonneg_right _ hW0
      nlinarith [mul_nonneg hAN0 hLB0, mul_nonneg hAN0 hAN0, mul_nonneg (mul_nonneg hAN0 hAN0) hLB0]
    rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
    nlinarith
  refine ⟨?_, ?_⟩
  · have : 0 ≤ 4 * (AN + 1) ^ 2 * LB / c0 := by positivity
    nlinarith
  · -- LB * (mu * AN) * X ≤ 3 * LB * W
    have h5 : LB * (mu * AN) * X ≤ 3 * LB * W := by
      have e1 : c0 / 4 * (LB * (mu * AN) * X) ≤ LB * (mu * AN) * ((1 + AN * LB) * W) := by
        have := mul_le_mul_of_nonneg_left hX1 (mul_nonneg hLB0 (mul_nonneg hmu0.le hAN0))
        nlinarith
      have e2 : LB * (mu * AN) * ((1 + AN * LB) * W) ≤ 3 / 4 * c0 * LB * W := by
        have : LB * (mu * AN) * (1 + AN * LB) = LB * (mu * AN) + LB * (mu * AN ^ 2 * LB) := by ring
        have h6 : LB * (mu * AN) ≤ LB * (c0 / 2) := mul_le_mul_of_nonneg_left h3 hLB0
        have h7 : LB * (mu * AN ^ 2 * LB) ≤ LB * (c0 / 4) :=
          mul_le_mul_of_nonneg_left (by linarith) hLB0
        calc LB * (mu * AN) * ((1 + AN * LB) * W) = (LB * (mu * AN) * (1 + AN * LB)) * W := by ring
          _ ≤ (3 / 4 * c0 * LB) * W := by
            apply mul_le_mul_of_nonneg_right _ hW0
            rw [this]; nlinarith
          _ = _ := by ring
      have e3 : c0 / 4 * (LB * (mu * AN) * X) ≤ c0 / 4 * (3 * LB * W) := by nlinarith
      exact le_of_mul_le_mul_left e3 (by positivity)
    have hy : mu * Y ≤ (8 * LB + 4) * W := by nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hmu0]
    nlinarith

end KAM.Planetary

end
