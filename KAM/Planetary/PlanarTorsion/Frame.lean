/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.SpectralAdapter
public import KAM.Planetary.SecularForm.Coefficients

/-!
# Planar quartic torsion: the global eigenframe and the rotation lift (P11C, package T14)

Blueprint P, Part 11b (`bpP:p11b:bt-rot`, `bt-rot#lift`): the explicit oriented eigenframe
`p11c_frame` built from the nonzero vector `(-Q₁₂, Q₁₁ - σ₁)`, and `global_planar_frame`, which
proves that it is analytic on the axis cone, special orthogonal and sorts the diagonalisation of
`p11c_Q`.  Positivity of `Q₁₂` gives non-vanishing on the whole cone, so no covering-space or
angle-lifting argument is needed.  `p11c_rotationLift` is the concrete inverse rotation lift of
Part 9 in the frozen assembled coordinates.
-/

@[expose] public noncomputable section
open Set Metric Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler

def p11c_rotateSlow (U : Matrix (Fin 2) (Fin 2) ℝ) (z : Phase 2) : Phase 2 :=
  (U.mulVec z.1, U.mulVec z.2)

/-- Exact explicit global SO(2) eigenframe avoids the unpaid covering-space argument. -/
def p11c_frame (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let Q := p11c_Q p a
  let s := p11c_sigma p a 0
  let v : Fin 2 → ℝ := ![-Q 0 1, Q 0 0 - s]
  let e := (sqrt (∑ i, v i ^ 2))⁻¹ • v
  !![e 0, -e 1; e 1, e 0]

/-! ### Positivity and the eigenvector -/

theorem p11c_Q_off_pos (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    0 < p11c_Q p a 0 1 := by
  rw [← p11c_Q_symm, p11c_Q_eq_coeffs p hp ha]
  have hax := p11c_axes_mem ha
  set D := p11cSecularData p hp
  rw [SecularSpectrum.coeffs_two_off10]
  have := SecularSpectrum.pairB_pos D hax (j := 0) (k := 1) (by decide)
  have := SecularSpectrum.action_pos D hax 0
  have := SecularSpectrum.action_pos D hax 1
  positivity

theorem p11c_frame_norm_pos (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) :
    0 < (-p11c_Q p a 0 1) ^ 2 + (p11c_Q p a 0 0 - p11c_sigma p a 0) ^ 2 := by
  have h := p11c_Q_off_pos p hp ha
  nlinarith [mul_pos h h, sq_nonneg (p11c_Q p a 0 0 - p11c_sigma p a 0)]

/-- The unnormalised eigenvector `(-Q₁₂, Q₁₁ - σ₁)` is a `σ₁`-eigenvector. -/
theorem p11c_frame_eigen (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    (p11c_Q p a).mulVec ![-p11c_Q p a 0 1, p11c_Q p a 0 0 - p11c_sigma p a 0] =
      p11c_sigma p a 0 • ![-p11c_Q p a 0 1, p11c_Q p a 0 0 - p11c_sigma p a 0] := by
  obtain ⟨hs, hd⟩ := p11c_sigma_sum_prod p hp ha
  have hq := p11c_Q_symm p a
  funext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hq]
    linear_combination p11c_sigma p a 0 * hs - hd

/-! ### Analyticity on the axis cone -/

theorem p11c_axes_isOpen : IsOpen p11c_axes := by
  have h0 : IsOpen {a : Fin 2 → ℝ | 0 < a 0} := isOpen_lt continuous_const (by fun_prop)
  have h1 : IsOpen {a : Fin 2 → ℝ | a 0 < a 1} := isOpen_lt (by fun_prop) (by fun_prop)
  exact h0.inter h1

theorem p11c_Q_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (i j : Fin 2) : AnalyticAt ℝ (fun b => p11c_Q p b i j) a := by
  have h := SecularForm.coeffs_analytic (p11cSecularData p hp) a (p11c_axes_mem ha)
  have h' := analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h i) j
  refine h'.congr ?_
  filter_upwards [p11c_axes_isOpen.mem_nhds ha] with b hb
  exact (congrFun (congrFun (p11c_Q_eq_coeffs p hp hb) i) j).symm

theorem p11c_sigma0_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) : AnalyticAt ℝ (fun b => p11c_sigma p b 0) a := by
  have h00 := p11c_Q_analyticAt p hp ha 0 0
  have h11 := p11c_Q_analyticAt p hp ha 1 1
  have h01 := p11c_Q_analyticAt p hp ha 0 1
  have hpos : 0 < (p11c_Q p a 0 0 - p11c_Q p a 1 1) ^ 2 + 4 * p11c_Q p a 0 1 ^ 2 := by
    have := p11c_Q_off_pos p hp ha
    nlinarith [sq_nonneg (p11c_Q p a 0 0 - p11c_Q p a 1 1), mul_pos this this]
  have hin : AnalyticAt ℝ (fun b => (p11c_Q p b 0 0 - p11c_Q p b 1 1) ^ 2 +
      4 * p11c_Q p b 0 1 ^ 2) a := ((h00.sub h11).pow 2).add (analyticAt_const.mul (h01.pow 2))
  have hsq := (hin.contDiffAt.sqrt hpos.ne').analyticAt
  exact (((h00.add h11).sub hsq).div analyticAt_const two_ne_zero).congr
    (Eventually.of_forall fun b => by simp [p11c_sigma])

theorem p11c_frame_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) (i j : Fin 2) :
    AnalyticAt ℝ (fun b => p11c_frame p b i j) a := by
  have h01 := p11c_Q_analyticAt p hp ha 0 1
  have h00 := p11c_Q_analyticAt p hp ha 0 0
  have hs := p11c_sigma0_analyticAt p hp ha
  have hv1 : AnalyticAt ℝ (fun b => -p11c_Q p b 0 1) a := h01.neg
  have hv2 : AnalyticAt ℝ (fun b => p11c_Q p b 0 0 - p11c_sigma p b 0) a := h00.sub hs
  have hN : AnalyticAt ℝ (fun b => (-p11c_Q p b 0 1) ^ 2 +
      (p11c_Q p b 0 0 - p11c_sigma p b 0) ^ 2) a := (hv1.pow 2).add (hv2.pow 2)
  have hc : AnalyticAt ℝ (fun b => (sqrt ((-p11c_Q p b 0 1) ^ 2 +
      (p11c_Q p b 0 0 - p11c_sigma p b 0) ^ 2))⁻¹) a := by
    have hNp := p11c_frame_norm_pos p hp ha
    exact (hN.contDiffAt.sqrt hNp.ne').analyticAt.inv (Real.sqrt_pos.2 hNp).ne'
  have e0 := hc.mul hv1
  have e1 := hc.mul hv2
  fin_cases i <;> fin_cases j
  · exact e0.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])
  · exact e1.neg.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])
  · exact e1.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])
  · exact e0.congr (Eventually.of_forall fun b => by simp [p11c_frame, Fin.sum_univ_two])

end KAM.Planetary

end
