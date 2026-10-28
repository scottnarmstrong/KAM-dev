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
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.analyticAt_fun_sum _ fun j _ => (hU' i j).mul (h1 j)
  · refine analyticAt_pi_iff.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
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
  have hc : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      SecularForm.secular D false (u.2.1, u.1, u.2.2)) (I0, 0) :=
    AnalyticAt.comp_of_eq (g := SecularForm.secular D false)
      (f := fun u : (Fin 2 → ℝ) × Phase 2 => ((u.2.1, u.1, u.2.2) : SecularForm.Slow 2))
      (hA _ hx0) hφ rfl
  exact hc.congr (Eventually.of_forall fun u => (p11cB_secular_eq p hp u.1 u.2).symm)

theorem p11cB_rotate_smul (U : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (z : Phase 2) :
    p11c_rotateSlow U (t • z) = t • p11c_rotateSlow U z := by
  simp [p11c_rotateSlow, Matrix.mulVec_smul]

theorem p11cB_rotate_zero (U : Matrix (Fin 2) (Fin 2) ℝ) : p11c_rotateSlow U 0 = 0 := by
  simp [p11c_rotateSlow]

theorem p11cB_sigma_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) (j : Fin 2) : AnalyticAt ℝ (fun b => p11c_sigma p b j) a := by
  fin_cases j
  · exact p11c_sigma0_analyticAt p hp ha
  · have hQ := p11c_Q_analyticAt p hp ha
    have h := ((hQ 0 0).add (hQ 1 1)).sub (p11c_sigma0_analyticAt p hp ha)
    refine h.congr (Eventually.of_forall fun b => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, p11c_sigma, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring

theorem p11cB_R_analyticAt (p : PlanarData) (hp : p.Valid) {I0 : Fin 2 → ℝ}
    (hI0 : I0 ∈ p11c_frameActionDomain p) (hpos : ∀ i, 0 < I0 i) :
    AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11cB_R p u.1 u.2) (I0, 0) := by
  have hJ := p11cB_secular_analyticAt p hp hI0 hpos
  have hrot := p11cB_rotate_analyticAt p hp hI0
  have hax : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p.axes u.1) (I0, 0) :=
    (p11c_axes_map_analyticAt p hp I0).comp_of_eq (analyticAt_fst (𝕜 := ℝ)) rfl
  have hK : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11cB_K p u.1 u.2) (I0, 0) := by
    have hf : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
        (u.1, p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2)) (I0, 0) :=
      (analyticAt_fst (𝕜 := ℝ)).prod hrot
    have h0 : (fun u : (Fin 2 → ℝ) × Phase 2 =>
        (u.1, p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2)) (I0, 0) = (I0, 0) := by
      simp [p11cB_rotate_zero]
    have := hJ.comp_of_eq hf h0
    exact this
  have hC : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11cB_C p u.1) (I0, 0) := by
    have hf : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => (u.1, (0 : Phase 2))) (I0, 0) :=
      (analyticAt_fst (𝕜 := ℝ)).prod analyticAt_const
    have := hJ.comp_of_eq hf rfl
    exact this
  have hsig : ∀ j, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => p11cB_freq p u.1 j) (I0, 0) :=
    fun j => analyticAt_const.mul
      ((p11cB_sigma_analyticAt p hp hI0 j).comp_of_eq hax rfl)
  have h1 : ∀ k, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => u.2.1 k) (I0, 0) := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).analyticAt _).comp
      ((analyticAt_fst (𝕜 := ℝ)).comp (analyticAt_snd (𝕜 := ℝ)))
  have h2 : ∀ k, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 => u.2.2 k) (I0, 0) := fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).analyticAt _).comp
      ((analyticAt_snd (𝕜 := ℝ)).comp (analyticAt_snd (𝕜 := ℝ)))
  have hn0 : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      p11c_n0 (p11cB_freq p) u.1 u.2) (I0, 0) := by
    unfold p11c_n0 oscillatorAction
    exact Finset.analyticAt_fun_sum _ fun j _ =>
      (hsig j).mul ((((h2 j).pow 2).add ((h1 j).pow 2)).div_const)
  have hc : ∀ k, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      p11c_coeffs p (p.axes u.1) k) (I0, 0) := fun k =>
    (analyticAt_pi_iff.1 (((quartic_explicit p hp).1 _ hI0)) k).comp_of_eq hax rfl
  have hr1 : ∀ i, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2).1 i) (I0, 0) := fun i =>
    analyticAt_pi_iff.1 ((analyticAt_fst (𝕜 := ℝ)).comp hrot) i
  have hr2 : ∀ i, AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2).2 i) (I0, 0) := fun i =>
    analyticAt_pi_iff.1 ((analyticAt_snd (𝕜 := ℝ)).comp hrot) i
  have hq : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
      p11c_quartic (p11c_coeffs p (p.axes u.1))
        (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2)) (I0, 0) := by
    have hA : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
        (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2).1 0 ^ 2 +
          (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2).2 0 ^ 2) (I0, 0) :=
      ((hr1 0).pow 2).add ((hr2 0).pow 2)
    have hB : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
        (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2).1 1 ^ 2 +
          (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2).2 1 ^ 2) (I0, 0) :=
      ((hr1 1).pow 2).add ((hr2 1).pow 2)
    have hD : AnalyticAt ℝ (fun u : (Fin 2 → ℝ) × Phase 2 =>
        p11c_pairDot (p11c_rotateSlow (p11c_frame p (p.axes u.1)) u.2)) (I0, 0) :=
      ((hr1 0).mul (hr1 1)).add ((hr2 0).mul (hr2 1))
    simp only [p11c_quartic]
    exact (((((hc 0).mul (hA.pow 2)).add ((hc 1).mul (hB.pow 2))).add
      (((hc 2).mul hA).mul hB)).add ((hc 3).mul (hD.pow 2))).add (((hc 4).mul hA).mul hD) |>.add
      (((hc 5).mul hB).mul hD)
  have := ((hK.sub hC).sub hn0).sub hq
  exact this

/-- `UᵀQU = diag σ` identifies the rotated quadratic form with the action sum. -/
theorem p11cB_quad_rot (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (z : Phase 2) :
    (∑ i, ∑ j, (p11c_rotateSlow (p11c_frame p a) z).1 i * p11c_Q p a i j *
        (p11c_rotateSlow (p11c_frame p a) z).1 j) +
      (∑ i, ∑ j, (p11c_rotateSlow (p11c_frame p a) z).2 i * p11c_Q p a i j *
        (p11c_rotateSlow (p11c_frame p a) z).2 j) =
      ∑ j, p11c_sigma p a j * (z.1 j ^ 2 + z.2 j ^ 2) := by
  have h := ((global_planar_frame p hp).2 a ha).2.2
  have e : ∀ k l, ((p11c_frame p a).transpose * p11c_Q p a * p11c_frame p a) k l =
      (Matrix.diagonal (p11c_sigma p a)) k l := fun k l => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.transpose_apply]
    at e00 e01 e10 e11
  simp only [p11c_rotateSlow, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  simp at e00 e01 e10 e11
  linear_combination (z.1 0 * z.1 0 + z.2 0 * z.2 0) * e00 + (z.1 0 * z.1 1 + z.2 0 * z.2 1) * e01 +
    (z.1 1 * z.1 0 + z.2 1 * z.2 0) * e10 + (z.1 1 * z.1 1 + z.2 1 * z.2 1) * e11

/-- Evenness of the secular average near the origin. -/
theorem p11cB_secular_even (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (hpos : ∀ i, 0 < p.actions a i) :
    ∀ᶠ w in 𝓝 (0 : Phase 2), p11c_secular (p11c_hatFix p) (p.actions a) (-w) =
      p11c_secular (p11c_hatFix p) (p.actions a) w := by
  filter_upwards [qe_eventually_small p hp ha] with w hw
  set D := p11cSecularData p hp
  have hx : ((w.1, p.actions a, w.2) : SecularForm.Slow 2) ∈ SecularForm.slowDom D := by
    rw [SecularForm.mem_slowDom_iff]
    exact fun i => ⟨hpos i, hw i⟩
  have := (SecularForm.evenness D hx false 0).1
  simpa [p11cB_secular_eq p hp] using this

theorem p11cB_R_jetEq (p : PlanarData) (hp : p.Valid) {I0 : Fin 2 → ℝ}
    (hI0 : I0 ∈ p11c_frameActionDomain p) (hpos : ∀ i, 0 < I0 i) :
    p11c_JetEq 5 (fun z => p11cB_R p I0 z) 0 := by
  have ha : p.axes I0 ∈ p11c_axes := hI0
  have hact : p.actions (p.axes I0) = I0 := p11cB_actions_axes p hp hpos
  set a := p.axes I0 with ha_def
  set U := p11c_frame p a with hU
  set S : Phase 2 → ℝ := p11c_secular (p11c_hatFix p) I0 with hS
  have hSa : AnalyticAt ℝ S 0 := by
    have h := (p11cB_secular_analyticAt p hp hI0 hpos).comp_of_eq
      (f := fun z : Phase 2 => (I0, z))
      (analyticAt_const.prod (analyticAt_id (𝕜 := ℝ))) rfl
    exact h
  have hSL : AnalyticAt ℝ (fun z => S (p11c_rotateSlow U z)) 0 := by
    have hL : (fun z => S (p11c_rotateSlow U z)) = S ∘ (p11cB_rotCLM U) := by
      funext w; simp [p11cB_rotCLM_apply]
    rw [hL]
    exact hSa.comp_of_eq ((p11cB_rotCLM U).analyticAt 0) (map_zero _)
  have hRa : AnalyticAt ℝ (fun z => p11cB_R p I0 z) 0 := by
    have h := (p11cB_R_analyticAt p hp hI0 hpos).comp_of_eq
      (f := fun z : Phase 2 => (I0, z))
      (analyticAt_const.prod (analyticAt_id (𝕜 := ℝ))) rfl
    exact h
  have hev : ∀ᶠ w in 𝓝 (0 : Phase 2), S (-w) = S w := by
    rw [hS, ← hact]
    exact p11cB_secular_even p hp ha (by rw [hact]; exact hpos)
  refine p11cPJ_jetEq_of_diag (g := fun _ => (0 : ℝ)) hRa analyticAt_const 5 fun j hj z => ?_
  have hz0 : iteratedFDeriv ℝ j (fun _ : Phase 2 => (0 : ℝ)) 0 (fun _ => z) = 0 := by
    rw [iteratedFDeriv_fun_zero]; rfl
  rw [hz0, p11cB_diag hRa]
  set w := p11c_rotateSlow U z with hw
  have hfun : (fun t : ℝ => p11cB_R p I0 (t • z)) = fun t : ℝ =>
      S (t • w) - (S 0 + p11c_n0 (p11cB_freq p) I0 z * t ^ 2 +
        p11c_quartic (p11c_coeffs p a) w * t ^ 4) := by
    funext t
    simp only [p11cB_R, p11cB_K, p11cB_C, ← ha_def, ← hU, ← hS, p11cB_rotate_smul, ← hw,
      qe_quartic_smul]
    have : p11c_n0 (p11cB_freq p) I0 (t • z) = t ^ 2 * p11c_n0 (p11cB_freq p) I0 z := by
      unfold p11c_n0 oscillatorAction
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    ring
  rw [hfun]
  have hsa : ContDiffAt ℝ j (fun t : ℝ => S (t • w)) 0 := by
    have : AnalyticAt ℝ (fun t : ℝ => S (t • w)) 0 :=
      hSa.comp_of_eq (f := fun t : ℝ => t • w) (analyticAt_id.smul analyticAt_const) (by simp)
    exact this.contDiffAt
  have hpa : ContDiffAt ℝ j (fun t : ℝ => S 0 + p11c_n0 (p11cB_freq p) I0 z * t ^ 2 +
      p11c_quartic (p11c_coeffs p a) w * t ^ 4) 0 := by fun_prop
  rw [iteratedDeriv_fun_sub hsa hpa, ← p11cB_diag hSa]
  have hpoly := p11cB_iteratedDeriv_poly (S 0) (p11c_n0 (p11cB_freq p) I0 z)
    (p11c_quartic (p11c_coeffs p a) w) j hj
  rw [hpoly]
  have hSact : S = p11c_secular (p11c_hatFix p) (p.actions a) := by rw [hS, hact]
  have hn0 : p11c_n0 (p11cB_freq p) I0 z = ∑ j, p11c_sigma p a j * (z.1 j ^ 2 + z.2 j ^ 2) := by
    unfold p11c_n0 oscillatorAction p11cB_freq
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [← ha_def]
    ring
  have hD2 : iteratedFDeriv ℝ 2 S 0 (fun _ => w) = 2 * p11c_n0 (p11cB_freq p) I0 z := by
    have h1 := quadratic_physical_bridge p hp a ha w
    rw [← hSact] at h1
    unfold p11c_homogeneousPart at h1
    have h2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2] at h1
    have h3 := p11cB_quad_rot p hp ha z
    rw [hn0, ← h3, ← h1]
    ring
  have hD4 : iteratedFDeriv ℝ 4 S 0 (fun _ => w) = 24 * p11c_quartic (p11c_coeffs p a) w := by
    rw [hSact]; exact qe_fix_jet p hp ha w
  interval_cases j
  · simp
  · rw [p11cB_diag_odd hSa hev (by decide) w]; simp
  · rw [hD2]; simp
  · rw [p11cB_diag_odd hSa hev (by decide) w]; simp
  · rw [hD4]; simp
  · rw [p11cB_diag_odd hSa hev (by decide) w]; simp

end KAM.Planetary
