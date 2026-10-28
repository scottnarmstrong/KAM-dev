/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyInvDeriv
public import KAM.Planetary.PGAssembly.FrequencyInvLinear

/-!
# P Part 5: blocks of the complex frequency map and of its derivative (`stepP:p5:fi-blk`)

The fast block of `complexFrequency` is `complexFast + mu G`, the slow block is `mu Θ`
(`blockFast_complexFrequency`, `blockSlow_complexFrequency`). For a derivative `T0` of the map the
fast row is `∂complexFast x + mu (Hessian row)` and the slow row is `mu (Hessian row)`, with the
slow-slow Hessian block equal to `jetBeta` (`jac_fast_eq`, `jac_slow_eq`, `jac_slow_slow`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FI.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem norm_blockFast_le_norm (u : Fin (a + b) → ℂ) : ‖blockFast u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact norm_le_pi_norm u (Fin.castAdd b i)

theorem norm_blockSlow_le_norm (u : Fin (a + b) → ℂ) : ‖blockSlow u‖ ≤ ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact norm_le_pi_norm u (Fin.natAdd a i)

theorem norm_le_max_blocks (u : Fin (a + b) → ℂ) : ‖u‖ ≤ max ‖blockFast u‖ ‖blockSlow u‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact (norm_le_pi_norm (blockFast u) j).trans (le_max_left _ _)
  · exact (norm_le_pi_norm (blockSlow u) j).trans (le_max_right _ _)

theorem norm_partialsCLM_apply_le (n : ℕ) (L : (Fin n → ℂ) →L[ℂ] ℂ) :
    ‖partialsCLM n L‖ ≤ ‖L‖ :=
  ((partialsCLM n).le_opNorm L).trans
    (mul_le_of_le_one_left (norm_nonneg _) (norm_partialsCLM_le n))

theorem blockFast_partialsCLM (L : (Fin (a + b) → ℂ) →L[ℂ] ℂ) :
    blockFast (partialsCLM (a + b) L) = fun k => L (embFast a b (Pi.single k 1)) := by
  funext k
  simp [blockFast, partialsCLM, single_castAdd]

theorem blockSlow_partialsCLM (L : (Fin (a + b) → ℂ) →L[ℂ] ℂ) :
    blockSlow (partialsCLM (a + b) L) = fun k => L (embSlow a b (Pi.single k 1)) := by
  funext k
  simp [blockSlow, partialsCLM, single_natAdd]

theorem blockFast_complexFrequency (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    blockFast (complexFrequency d mu J) = complexFast d (blockFast J) +
      (mu : ℂ) • jpGrad d mu (blockSlow J) (blockFast J) := by
  have hJe : (Fin.append (blockFast J) (blockSlow J) : Fin (a + b) → ℂ) = J :=
    Fin.append_castAdd_natAdd
  rw [complexFrequency_eq d hmu hJ]
  funext k
  have h := jpGrad_eq d hmu (blockSlow J) hJ k
  rw [hJe] at h
  simp only [blockFast, Pi.add_apply, Pi.smul_apply, partialsCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.apply_apply, single_castAdd, embFast_apply, Fin.append_left, h]

theorem blockSlow_complexFrequency (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    blockSlow (complexFrequency d mu J) = (mu : ℂ) • jpTheta d mu (blockSlow J) (blockFast J) := by
  have hJe : (Fin.append (blockFast J) (blockSlow J) : Fin (a + b) → ℂ) = J :=
    Fin.append_castAdd_natAdd
  rw [complexFrequency_eq d hmu hJ]
  funext k
  have h := fderiv_jp_embSlow d hmu hJ (blockSlow J) (Pi.single k 1)
  rw [hJe, dotProduct_single, mul_one] at h
  simp only [blockSlow, Pi.add_apply, Pi.smul_apply, partialsCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.apply_apply, single_natAdd, embFast_apply, Fin.append_right, h]
  simp

/-- The fast row of the derivative of the frequency map. -/
theorem jac_fast_eq (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))
    {T0 : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)}
    (hT0 : HasFDerivAt (complexFrequency d mu) T0 J) (v : Fin (a + b) → ℂ) :
    blockFast (T0 v) = fderiv ℂ (complexFast d) (blockFast J) (blockFast v) +
      (mu : ℂ) • fun k => fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J v
        (embFast a b (Pi.single k 1)) := by
  rw [hT0.unique (hasFDerivAt_complexFrequency d hmu hJ)]
  funext k
  simp [blockFast, partialsCLM, single_castAdd, embFast_apply, bfCLM_apply]

/-- The slow row of the derivative of the frequency map. -/
theorem jac_slow_eq (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))
    {T0 : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)}
    (hT0 : HasFDerivAt (complexFrequency d mu) T0 J) (v : Fin (a + b) → ℂ) :
    blockSlow (T0 v) = (mu : ℂ) • fun k => fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J v
        (embSlow a b (Pi.single k 1)) := by
  rw [hT0.unique (hasFDerivAt_complexFrequency d hmu hJ)]
  funext k
  simp [blockSlow, partialsCLM, single_natAdd, embFast_apply]

/-- The slow-slow Hessian block is `jetBeta`. -/
theorem jac_slow_slow (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {J : Fin (a + b) → ℂ}
    (hJ : blockFast J ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))
    (y : Fin b → ℂ) :
    (fun k => fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J (embSlow a b y)
        (embSlow a b (Pi.single k 1))) = (jetBeta d mu (blockFast J)).mulVec y := by
  have hJe : (Fin.append (blockFast J) (blockSlow J) : Fin (a + b) → ℂ) = J :=
    Fin.append_castAdd_natAdd
  funext k
  have h := hessian_embSlow d hmu hJ (blockSlow J) y (Pi.single k 1)
  rw [hJe, dotProduct_single, mul_one] at h
  exact h

end KAM.Planetary

end
