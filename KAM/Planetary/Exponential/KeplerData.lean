/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.RealPart
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Planetary.Exponential.Setting
public import KAM.Planetary.Exponential.Enlargement
public import KAM.Planetary.Exponential.LocalComplexification

/-!
# P14 package E4: the Kepler data `h_data`

Blueprint P, Part 14 (`bpP:p14:h-data`, steps `hd-i`, `hd-ii`, `hd-iv`, `hd-v`): the
complexified Kepler part `planetaryKeplerC m I = -∑ m_i³ / (2 I_i²)` on the complex collar of the
enlarged action box is holomorphic, `C²`, real on real points, has Hessian bounded by
`M = ∑ 3 m_i³ / (5 lower_i / 8)⁴`, and has a definite fast Hessian and nonvanishing frequency
with the explicit constants `g`, `v` (attained minima), for `h` and `-h`.

The calculus is done once over `𝕜 = ℝ, ℂ` for `keplerSumGen`, on the open set of nowhere-zero
coordinates.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators ContDiff

namespace KAM.Planetary

variable {n : ℕ}

/-- The Kepler sum `-∑ m_i³ / (2 z_i²)` over a scalar field `𝕜`. -/
def keplerSumGen (𝕜 : Type*) [RCLike 𝕜] (m : Fin n → ℝ) (z : Fin n → 𝕜) : 𝕜 :=
  -∑ i, (m i : 𝕜)^3 / (2 * z i ^ 2)

section Calculus

variable {𝕜 : Type*} [RCLike 𝕜]

theorem keplerSumGen_contDiffOn (m : Fin n → ℝ) (k : WithTop ℕ∞) :
    ContDiffOn 𝕜 k (keplerSumGen 𝕜 m) {z | ∀ i, z i ≠ 0} := by
  unfold keplerSumGen
  refine ContDiffOn.neg (ContDiffOn.sum fun i _ => ?_)
  refine contDiffOn_const.div (contDiffOn_const.mul ?_) fun z hz => ?_
  · exact ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜) i).contDiff.pow 2).contDiffOn
  · exact mul_ne_zero two_ne_zero (pow_ne_zero 2 (hz i))

private theorem hasDerivAt_inv_sq (c w : 𝕜) (hw : w ≠ 0) :
    HasDerivAt (fun w : 𝕜 => c / (2 * w ^ 2)) (-c / w ^ 3) w := by
  have h := (hasDerivAt_const w c).div ((hasDerivAt_pow 2 w).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hw))
  convert h using 1
  field_simp
  ring

private theorem hasDerivAt_inv_cube (c w : 𝕜) (hw : w ≠ 0) :
    HasDerivAt (fun w : 𝕜 => c / w ^ 3) (-3 * c / w ^ 4) w := by
  have h := (hasDerivAt_const w c).div (hasDerivAt_pow 3 w) (pow_ne_zero 3 hw)
  convert h using 1
  field_simp
  ring

/-- The first derivative of `keplerSumGen` as a continuous linear map. -/
def keplerSumGenD (m : Fin n → ℝ) (z : Fin n → 𝕜) : (Fin n → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, ((m i : 𝕜)^3 / z i ^ 3) • (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)

theorem keplerSumGen_hasFDerivAt (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    HasFDerivAt (keplerSumGen 𝕜 m) (keplerSumGenD m z) z := by
  unfold keplerSumGen keplerSumGenD
  have h : HasFDerivAt (fun z : Fin n → 𝕜 => ∑ i, (m i : 𝕜)^3 / (2 * z i ^ 2))
      (∑ i, ((-(m i : 𝕜)^3) / z i ^ 3) • (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜))
      z := by
    have key : ∀ i, HasFDerivAt (fun z : Fin n → 𝕜 => (m i : 𝕜)^3 / (2 * z i ^ 2))
        (((-(m i : 𝕜)^3) / z i ^ 3) •
          (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)) z := fun i =>
      (hasDerivAt_inv_sq ((m i : 𝕜)^3) (z i) (hz i)).comp_hasFDerivAt
        (f := fun z : Fin n → 𝕜 => z i) z (hasFDerivAt_apply i z)
    exact HasFDerivAt.fun_sum fun i _ => key i
  refine h.neg.congr_fderiv ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [neg_div]
  ext w
  simp

theorem keplerSumGen_fderiv_eq (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    fderiv 𝕜 (keplerSumGen 𝕜 m) z = keplerSumGenD m z :=
  (keplerSumGen_hasFDerivAt m hz).fderiv

theorem keplerSumGenD_hasFDerivAt (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0) :
    HasFDerivAt (keplerSumGenD m)
      (∑ i, ((-3 * (m i : 𝕜)^3 / z i ^ 4) •
        (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)).smulRight
        (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)) z := by
  unfold keplerSumGenD
  have key : ∀ i, HasFDerivAt (fun z : Fin n → 𝕜 => ((m i : 𝕜)^3 / z i ^ 3) •
        (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜))
        (((-3 * (m i : 𝕜)^3 / z i ^ 4) •
          (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)).smulRight
          (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)) z := fun i =>
    ((hasDerivAt_inv_cube ((m i : 𝕜)^3) (z i) (hz i)).comp_hasFDerivAt
      (f := fun z : Fin n → 𝕜 => z i) z (hasFDerivAt_apply i z)).smul_const
      (ContinuousLinearMap.proj i : (Fin n → 𝕜) →L[𝕜] 𝕜)
  exact HasFDerivAt.fun_sum fun i _ => key i

/-- The second derivative of `keplerSumGen` is the diagonal form `-3 m_i³ / z_i⁴`. -/
theorem keplerSumGen_fderiv2_apply (m : Fin n → ℝ) {z : Fin n → 𝕜} (hz : ∀ i, z i ≠ 0)
    (w v : Fin n → 𝕜) :
    fderiv 𝕜 (fderiv 𝕜 (keplerSumGen 𝕜 m)) z w v =
      ∑ i, (-3 * (m i : 𝕜)^3 / z i ^ 4) * (w i * v i) := by
  have hS : {z : Fin n → 𝕜 | ∀ i, z i ≠ 0} ∈ nhds z := by
    have hopen : IsOpen (Set.pi Set.univ (fun _ : Fin n => ({0}ᶜ : Set 𝕜))) :=
      isOpen_set_pi (Set.toFinite _) fun _ _ => isOpen_compl_singleton
    have hset : {z : Fin n → 𝕜 | ∀ i, z i ≠ 0} = Set.pi Set.univ (fun _ : Fin n => ({0}ᶜ : Set 𝕜)) := by
      ext y; simp [Set.mem_pi]
    rw [hset]
    exact hopen.mem_nhds (by simpa [Set.mem_pi] using hz)
  have hev : fderiv 𝕜 (keplerSumGen 𝕜 m) =ᶠ[nhds z] keplerSumGenD m :=
    Filter.eventuallyEq_of_mem hS fun y hy => keplerSumGen_fderiv_eq m hy
  rw [hev.fderiv_eq, (keplerSumGenD_hasFDerivAt m hz).fderiv]
  simp [mul_assoc]

end Calculus

end KAM.Planetary

end
