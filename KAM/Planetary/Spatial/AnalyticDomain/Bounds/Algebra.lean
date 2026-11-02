/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Vector
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Algebra

/-!
# Complex 3-vector algebra for the spatial denominators

Source: `LP:MAIN L18 (595)` with `LP:MAIN L8 (266–268)`, track LP, non-frozen.

Twins of the analytic-domain bounds' `Bounds.Algebra` for bodies with `Fin 3` blocks:

* `cBody3`, `cDot3`: body block of a complex coordinate vector and the bilinear `v · v = ∑ v_k²`;
* `cDot3_cpow_ofReal`: on real vectors the principal root is `spaceLength`;
* `re_cDot3_ge`: coordinatewise perturbation estimate `Re (w · w) ≥ |u|² − 3ε(ε + 2Q)`;
* `differentiableOn_inv_sqrt_cDot3`: holomorphy of the reciprocal principal root.

The scalar estimate `norm_inv_sqrt_le` is dimension-free and reused from the analytic-domain bounds.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD

/-- Body `i`'s `Fin 3` block of a complex coordinate vector (complexified `bodyVector3`). -/
def cBody3 {n : ℕ} (q : Fin (n * 3) → ℂ) (i : Fin n) : Fin 3 → ℂ :=
  fun k => q (finProdFinEquiv (i, k))

/-- The bilinear complex dot product `v · v = ∑ v_k²` on `Fin 3 → ℂ`. -/
def cDot3 (v : Fin 3 → ℂ) : ℂ := ∑ k, v k ^ 2

theorem cDot3_ofReal (u : Fin 3 → ℝ) : cDot3 (fun k => (u k : ℂ)) = (spaceSq u : ℂ) := by
  simp [cDot3, spaceSq]

/-- On a real vector the principal square root of `v · v` is the Euclidean length. -/
theorem cDot3_cpow_ofReal (u : Fin 3 → ℝ) :
    (cDot3 (fun k => (u k : ℂ))) ^ (1 / 2 : ℂ) = (spaceLength u : ℂ) := by
  have h0 : 0 ≤ spaceSq u := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h := Complex.ofReal_cpow h0 (1 / 2)
  rw [cDot3_ofReal]
  unfold spaceLength
  rw [Real.sqrt_eq_rpow]
  push_cast at h ⊢
  exact h.symm

/-- Coordinatewise perturbation estimate: `Re (w · w) ≥ |u|² - 3 (ε (ε + 2Q))`. -/
theorem re_cDot3_ge {w : Fin 3 → ℂ} {u : Fin 3 → ℝ} {ε Q : ℝ}
    (hw : ∀ k, ‖w k - (u k : ℂ)‖ ≤ ε) (hu : ∀ k, |u k| ≤ Q) :
    spaceSq u - 3 * (ε * (ε + 2 * Q)) ≤ (cDot3 w).re := by
  have key : ∀ k, (u k) ^ 2 - ε * (ε + 2 * Q) ≤ (w k ^ 2).re := by
    intro k
    have h1 : ‖w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2‖ ≤ ε * (ε + 2 * Q) := by
      have e : w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2 = (w k - u k) * (w k + u k) := by ring
      rw [e, norm_mul]
      have h2 : ‖w k + (u k : ℂ)‖ ≤ ε + 2 * Q := by
        have : w k + (u k : ℂ) = (w k - u k) + 2 * (u k : ℂ) := by ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        have h3 : ‖(2 : ℂ) * (u k : ℂ)‖ ≤ 2 * Q := by
          rw [norm_mul, Complex.norm_real]
          simpa using mul_le_mul_of_nonneg_left (hu k) (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add (hw k) h3
      exact mul_le_mul (hw k) h2 (norm_nonneg _) ((norm_nonneg _).trans (hw k))
    have h4 : |(w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2).re| ≤ ‖w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2‖ :=
      Complex.abs_re_le_norm _
    have h5 : (w k ^ 2 - ((u k : ℝ) : ℂ) ^ 2).re = (w k ^ 2).re - (u k) ^ 2 := by
      simp [← Complex.ofReal_pow]
    rw [h5] at h4
    linarith [(abs_le.1 (h4.trans h1)).1]
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  simp only [cDot3, spaceSq, Fin.sum_univ_three, Complex.add_re]
  linarith

/-- Along a holomorphic family `W` of complex 3-vectors with `Re (W·W) > 0`, the reciprocal of
the principal square root of `W · W` is holomorphic. -/
theorem differentiableOn_inv_sqrt_cDot3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : Set E} {W : E → Fin 3 → ℂ} (hW : ∀ k, DifferentiableOn ℂ (fun z => W z k) T)
    (hre : ∀ z ∈ T, 0 < (cDot3 (W z)).re) :
    DifferentiableOn ℂ (fun z => ((cDot3 (W z)) ^ (1 / 2 : ℂ))⁻¹) T := by
  have hD : DifferentiableOn ℂ (fun z => cDot3 (W z)) T := by
    unfold cDot3
    exact DifferentiableOn.fun_sum fun k _ => (hW k).pow 2
  have hslit : ∀ z ∈ T, cDot3 (W z) ∈ Complex.slitPlane := fun z hz =>
    Complex.mem_slitPlane_iff.2 (Or.inl (hre z hz))
  refine DifferentiableOn.inv (hD.cpow (differentiableOn_const _) hslit) fun z hz => ?_
  have : cDot3 (W z) ≠ 0 := fun h => by simpa [h] using hre z hz
  simp [Complex.cpow_eq_zero_iff, this]

end KAM.Planetary.Spatial

end
