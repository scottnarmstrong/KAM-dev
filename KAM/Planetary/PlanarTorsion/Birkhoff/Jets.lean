/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Quartic
public import KAM.Planetary.PlanarTorsion.Beta
public import KAM.Planetary.PlanarTorsion.Birkhoff.Diag
public import KAM.Planetary.SecularForm.Symmetry

/-!
# Planar quartic torsion: the rotated secular function and its sixth-order remainder (T16)

Blueprint P, Part 11b (`stepP:p11b:bt-K`).  `p11cB_K p I z` is the fixed secular average at the
rotated slow point `U(I) z`, with `U` the global frame.  Writing it as
`C + n₀ + (rotated quartic) + R`, the remainder `p11cB_R` is jointly analytic at `(I, 0)` and has
vanishing five-jet: the diagonal derivatives of `S = ⟨f̂_fix⟩(I, ·)` at `0` are `S 0`, `2 Q`, and
`24 · quartic` in orders `0`, `2`, `4` (`quadratic_physical_bridge`, `qe_fix_jet`) and vanish in odd
order by evenness (`SecularForm.evenness`), while `UᵀQU = diag σ` identifies the quadratic part
with `n₀`.
-/

@[expose] public noncomputable section

open Set Metric Real Function Filter
open scoped Topology ContDiff

namespace KAM.Planetary

open KAM KAM.Kepler

/-- The fixed secular average at the frame-rotated slow point. -/
def p11cB_K (p : PlanarData) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  p11c_secular (p11c_hatFix p) I (p11c_rotateSlow (p11c_frame p (p.axes I)) z)

/-- The action-only constant of the secular average. -/
def p11cB_C (p : PlanarData) (I : Fin 2 → ℝ) : ℝ := p11c_secular (p11c_hatFix p) I 0

/-- The frequency vector `2 σ`. -/
def p11cB_freq (p : PlanarData) (I : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun j => 2 * p11c_sigma p (p.axes I) j

/-- The remainder: secular average minus constant, quadratic and rotated quartic. -/
def p11cB_R (p : PlanarData) (I : Fin 2 → ℝ) (z : Phase 2) : ℝ :=
  p11cB_K p I z - p11cB_C p I - p11c_n0 (p11cB_freq p) I z -
    p11c_quartic (p11c_coeffs p (p.axes I)) (p11c_rotateSlow (p11c_frame p (p.axes I)) z)

theorem p11cB_actions_axes (p : PlanarData) (hp : p.Valid) {I : Fin 2 → ℝ}
    (hpos : ∀ i, 0 < I i) : p.actions (p.axes I) = I := by
  funext i
  have hm := hp.2.2 i
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hi := hpos i
  unfold PlanarData.actions PlanarData.axes
  have : p.kappa * (I i ^ 2 / (p.m i ^ 2 * p.kappa)) = (I i / p.m i) ^ 2 := by
    field_simp
  rw [this, Real.sqrt_sq (by positivity)]
  field_simp

/-- `p11c_secular` is the `SecularForm.secular` of the fixed perturbation. -/
theorem p11cB_secular_eq (p : PlanarData) (hp : p.Valid) (I : Fin 2 → ℝ) (z : Phase 2) :
    p11c_secular (p11c_hatFix p) I z =
      SecularForm.secular (p11cSecularData p hp) false (z.1, I, z.2) := rfl

theorem p11cB_rotate_analyticAt (p : PlanarData) (hp : p.Valid) {I0 : Fin 2 → ℝ}
    (hI0 : I0 ∈ p11c_frameActionDomain p) :
    AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2) (I0, 0) := by
  have hU := p11c_frameFamily_analyticOnNhd p hp I0 hI0
  have hU' : ∀ i j, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      p11c_frame p (p.axes u.1) i j) (I0, 0) := fun i j =>
    ((analyticAt_pi_iff.1 (analyticAt_pi_iff.1 hU i) j)).comp_of_eq
      (analyticAt_fst (𝕜 := ℝ)) rfl
  have h1 : ∀ k, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => u.2.1 k) (I0, 0) := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).analyticAt _).comp
      ((analyticAt_fst (𝕜 := ℝ)).comp (analyticAt_snd (𝕜 := ℝ)))
  have h2 : ∀ k, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => u.2.2 k) (I0, 0) := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).analyticAt _).comp
      ((analyticAt_snd (𝕜 := ℝ)).comp (analyticAt_snd (𝕜 := ℝ)))
  refine AnalyticAt.prod ?_ ?_
  · refine analyticAt_pi_iff.2 fun i => ?_
    simp only [p11c_rotateSlow, Matrix.mulVec, dotProduct]
    exact Finset.analyticAt_fun_sum _ fun j _ => (hU' i j).mul (h1 j)
  · refine analyticAt_pi_iff.2 fun i => ?_
    simp only [p11c_rotateSlow, Matrix.mulVec, dotProduct]
    exact Finset.analyticAt_fun_sum _ fun j _ => (hU' i j).mul (h2 j)

/-- Joint analyticity of the fixed secular average at a point of the cylinder. -/
theorem p11cB_secular_analyticAt (p : PlanarData) (hp : p.Valid) {I0 : Fin 2 → ℝ}
    (hI0 : I0 ∈ p11c_frameActionDomain p) (hpos : ∀ i, 0 < I0 i) :
    AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11c_secular (p11c_hatFix p) u.1 u.2)
      (I0, 0) := by
  set D := p11cSecularData p hp with hD
  have ha : p.axes I0 ∈ SecularForm.axes 2 := p11c_axes_mem hI0
  obtain ⟨r, hr, -, -, h⟩ := SecularForm.perturbation_analytic D ha
  have hA := (h false).2.2.2.2.1
  have hact : SecularForm.action D (p.axes I0) = I0 := p11cB_actions_axes p hp hpos
  have hx0 : ((0 : Fin 2 → ℝ), I0, (0 : Fin 2 → ℝ)) ∈ SecularForm.realDisc D (p.axes I0) r := by
    intro i
    simp [SecularForm.inclusion, hact, hr]
  have hφ : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => (u.2.1, u.1, u.2.2)) (I0, 0) :=
    (analyticAt_fst (𝕜 := ℝ)).comp (analyticAt_snd (𝕜 := ℝ)) |>.prod
      ((analyticAt_fst (𝕜 := ℝ)).prod ((analyticAt_snd (𝕜 := ℝ)).comp (analyticAt_snd (𝕜 := ℝ))))
  exact (hA _ hx0).comp_of_eq hφ rfl

end KAM.Planetary

end
