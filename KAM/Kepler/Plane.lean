/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Frozen.Planetary.Defs.PlaneSq
public import KAM.Frozen.Planetary.Defs.PlaneLength
public import KAM.Frozen.Planetary.Defs.PlaneDot
public import KAM.Frozen.Planetary.Defs.PlaneCross
public import KAM.Frozen.Planetary.Defs.QuarterTurn
public import KAM.Frozen.Iso.Defs.Radius
public import KAM.Frozen.Iso.Defs.RadiusSq

/-!
# Planar geometry on the frozen lengths

Algebra, rotations and calculus of the frozen `planeSq`, `planeLength`, `planeDot`, `planeCross`.
The helpers `norm_le_planeLength`, `planeLength_le_sqrt_two_mul_norm`, `planeLength_add_le` and
`radius_eq_planeLength` are imported by the ODE layer.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Kepler

open KAM KAM.Planetary

section Plane

private theorem planeSq_def (v : Fin 2 → ℝ) : planeSq v = v 0 ^ 2 + v 1 ^ 2 := by
  simp [planeSq, Fin.sum_univ_two]

private theorem planeDot_def (v w : Fin 2 → ℝ) : planeDot v w = v 0 * w 0 + v 1 * w 1 := by
  simp [planeDot, Fin.sum_univ_two]

private theorem planeCross_def' (v w : Fin 2 → ℝ) : planeCross v w = v 0 * w 1 - v 1 * w 0 := rfl

theorem planeSq_eq_planeDot (v : Fin 2 → ℝ) : planeSq v = planeDot v v := by
  simp [planeSq_def, planeDot_def, sq]

private theorem planeSq_nonneg (v : Fin 2 → ℝ) : 0 ≤ planeSq v := by
  rw [planeSq_def]; positivity

theorem planeLength_sq (v : Fin 2 → ℝ) : planeLength v ^ 2 = planeSq v :=
  Real.sq_sqrt (planeSq_nonneg v)

theorem planeLength_nonneg (v : Fin 2 → ℝ) : 0 ≤ planeLength v := Real.sqrt_nonneg _

private theorem planeSq_eq_zero_iff {v : Fin 2 → ℝ} : planeSq v = 0 ↔ v = 0 := by
  rw [planeSq_def]
  constructor
  · intro h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    ext i; fin_cases i <;> simp [h0, h1]
  · rintro rfl; simp

theorem planeLength_eq_zero_iff {v : Fin 2 → ℝ} : planeLength v = 0 ↔ v = 0 := by
  unfold planeLength
  rw [Real.sqrt_eq_zero (planeSq_nonneg v), planeSq_eq_zero_iff]

theorem planeLength_pos_iff {v : Fin 2 → ℝ} : 0 < planeLength v ↔ v ≠ 0 := by
  rw [(planeLength_nonneg v).lt_iff_ne, ne_comm, Ne, planeLength_eq_zero_iff]

theorem planeLength_neg (v : Fin 2 → ℝ) : planeLength (-v) = planeLength v := by
  simp [planeLength, planeSq_def]

theorem planeLength_sub_comm (v w : Fin 2 → ℝ) : planeLength (v - w) = planeLength (w - v) := by
  rw [← neg_sub, planeLength_neg]

theorem planeLength_smul (c : ℝ) (v : Fin 2 → ℝ) : planeLength (c • v) = |c| * planeLength v := by
  unfold planeLength
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
  congr 1
  simp [planeSq_def]; ring

/-- Lagrange's identity `|q|²|p|² = (q·p)² + cr(q,p)²`. -/
theorem planeSq_mul_planeSq (q p : Fin 2 → ℝ) :
    planeSq q * planeSq p = planeDot q p ^ 2 + planeCross q p ^ 2 := by
  simp only [planeSq_def, planeDot_def, planeCross_def']; ring

theorem abs_planeDot_le (v w : Fin 2 → ℝ) : |planeDot v w| ≤ planeLength v * planeLength w := by
  unfold planeLength
  rw [← Real.sqrt_mul (planeSq_nonneg v)]
  apply Real.abs_le_sqrt
  rw [planeSq_mul_planeSq]; nlinarith [sq_nonneg (planeCross v w)]

theorem planeLength_add_le (v w : Fin 2 → ℝ) :
    planeLength (v + w) ≤ planeLength v + planeLength w := by
  have h1 := abs_planeDot_le v w
  have h2 := (abs_le.mp h1).2
  have hv := planeLength_sq v
  have hw := planeLength_sq w
  have hvw : planeSq (v + w) = planeSq v + 2 * planeDot v w + planeSq w := by
    simp only [planeSq_def, planeDot_def, Pi.add_apply]; ring
  apply le_of_sq_le_sq _ (add_nonneg (planeLength_nonneg v) (planeLength_nonneg w))
  rw [planeLength_sq, hvw, ← hv, ← hw]
  nlinarith

theorem abs_planeLength_sub_le (v w : Fin 2 → ℝ) :
    |planeLength v - planeLength w| ≤ planeLength (v - w) := by
  rw [abs_le]
  have h1 := planeLength_add_le (v - w) w
  have h2 := planeLength_add_le (w - v) v
  rw [sub_add_cancel] at h1 h2
  rw [planeLength_sub_comm w v] at h2
  constructor <;> linarith

/-- `bpP:p6:plane` (b), sup norm against the Euclidean length (the factor `√2` is sharp). -/
theorem norm_le_planeLength (v : Fin 2 → ℝ) : ‖v‖ ≤ planeLength v := by
  rw [pi_norm_le_iff_of_nonneg (planeLength_nonneg v)]
  intro i
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  rw [planeSq_def]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

theorem planeLength_le_sqrt_two_mul_norm (v : Fin 2 → ℝ) : planeLength v ≤ √2 * ‖v‖ := by
  unfold planeLength
  rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  rw [planeSq_def]
  have := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  nlinarith

/-- A vector is determined by its dot and cross product with a nonzero vector. -/
theorem eq_of_planeDot_planeCross_eq {q v w : Fin 2 → ℝ} (hq : q ≠ 0)
    (hd : planeDot q v = planeDot q w) (hc : planeCross q v = planeCross q w) : v = w := by
  simp only [planeDot_def, planeCross_def'] at hd hc
  have hs : q 0 ^ 2 + q 1 ^ 2 ≠ 0 := by
    rw [← planeSq_def]; exact fun h => hq (planeSq_eq_zero_iff.mp h)
  have h0 : (q 0 ^ 2 + q 1 ^ 2) * v 0 = (q 0 ^ 2 + q 1 ^ 2) * w 0 := by
    linear_combination q 0 * hd - q 1 * hc
  have h1 : (q 0 ^ 2 + q 1 ^ 2) * v 1 = (q 0 ^ 2 + q 1 ^ 2) * w 1 := by
    linear_combination q 1 * hd + q 0 * hc
  ext i; fin_cases i
  · exact mul_left_cancel₀ hs h0
  · exact mul_left_cancel₀ hs h1

theorem planeLength_rot (g : ℝ) (v : Fin 2 → ℝ) : planeLength (rot g v) = planeLength v := by
  unfold planeLength
  congr 1
  have := Real.sin_sq_add_cos_sq g
  simp only [planeSq_def, rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 ^ 2 + v 1 ^ 2) * this

theorem planeDot_rot (g : ℝ) (v w : Fin 2 → ℝ) : planeDot (rot g v) (rot g w) = planeDot v w := by
  have := Real.sin_sq_add_cos_sq g
  simp only [planeDot_def, rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 * w 0 + v 1 * w 1) * this

theorem planeCross_rot (g : ℝ) (v w : Fin 2 → ℝ) :
    planeCross (rot g v) (rot g w) = planeCross v w := by
  have := Real.sin_sq_add_cos_sq g
  simp only [planeCross_def', rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (v 0 * w 1 - v 1 * w 0) * this

theorem rot_rot (g h : ℝ) (v : Fin 2 → ℝ) : rot g (rot h v) = rot (g + h) v := by
  ext i; fin_cases i <;> simp [rot, Real.cos_add, Real.sin_add] <;> ring

theorem rot_two_pi_int (k : ℤ) (g : ℝ) (v : Fin 2 → ℝ) : rot (g + 2 * π * k) v = rot g v := by
  have : g + 2 * π * k = g + k * (2 * π) := by ring
  rw [this]
  simp [rot, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem rot_quarterTurn (g : ℝ) (v : Fin 2 → ℝ) :
    rot g (quarterTurn v) = quarterTurn (rot g v) := by
  ext i; fin_cases i <;> simp [rot, quarterTurn] <;> ring

theorem rot_ex (g h : ℝ) : rot g (ex h) = ex (g + h) := by
  ext i; fin_cases i <;> simp [rot, ex, Real.cos_add, Real.sin_add]

/-- `(q, p)` is determined by `(g, ξ, π)` in the orbit frame: the rotation is onto the plane. -/
theorem exists_rot_eq {u v : Fin 2 → ℝ} (h : planeLength u = planeLength v) :
    ∃ g : ℝ, rot g u = v := by
  by_cases hu : u = 0
  · refine ⟨0, ?_⟩
    have : v = 0 := by rw [← planeLength_eq_zero_iff, ← h, planeLength_eq_zero_iff]; exact hu
    subst hu; subst this
    ext i; fin_cases i <;> simp [rot]
  · have hv : v ≠ 0 := fun hv => hu (by
      rw [← planeLength_eq_zero_iff, h, planeLength_eq_zero_iff]; exact hv)
    obtain ⟨a, ha⟩ : ∃ a : ℂ, a = ⟨u 0, u 1⟩ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℂ, b = ⟨v 0, v 1⟩ := ⟨_, rfl⟩
    have hare : a.re = u 0 := by rw [ha]
    have haim : a.im = u 1 := by rw [ha]
    have hbre : b.re = v 0 := by rw [hb]
    have hbim : b.im = v 1 := by rw [hb]
    have hna : ‖a‖ = planeLength u := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hare, haim, planeLength, planeSq_def]
    have hnb : ‖b‖ = planeLength v := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hbre, hbim, planeLength, planeSq_def]
    have ha0 : a ≠ 0 := by
      intro h0; apply hu
      rw [h0] at hare haim
      ext i; fin_cases i
      · exact hare.symm
      · exact haim.symm
    have hb0 : b ≠ 0 := by
      intro h0; apply hv
      rw [h0] at hbre hbim
      ext i; fin_cases i
      · exact hbre.symm
      · exact hbim.symm
    have hr : 0 < planeLength u := planeLength_pos_iff.mpr hu
    have ca := Complex.cos_arg ha0
    have sa := Complex.sin_arg a
    have cb := Complex.cos_arg hb0
    have sb := Complex.sin_arg b
    rw [hna, hare] at ca
    rw [hna, haim] at sa
    rw [hnb, ← h, hbre] at cb
    rw [hnb, ← h, hbim] at sb
    refine ⟨Complex.arg b - Complex.arg a, ?_⟩
    set r := planeLength u
    have hu0 : u 0 = r * Real.cos (Complex.arg a) := by rw [ca]; field_simp
    have hu1 : u 1 = r * Real.sin (Complex.arg a) := by rw [sa]; field_simp
    have hv0 : v 0 = r * Real.cos (Complex.arg b) := by rw [cb]; field_simp
    have hv1 : v 1 = r * Real.sin (Complex.arg b) := by rw [sb]; field_simp
    have := Real.sin_sq_add_cos_sq (Complex.arg a)
    ext i; fin_cases i
    · simp only [rot, Matrix.cons_val_zero, Fin.zero_eta]
      rw [hu0, hu1, hv0, Real.cos_sub, Real.sin_sub]
      linear_combination (r * Real.cos (Complex.arg b)) * this
    · simp only [rot, Matrix.cons_val_one, Fin.mk_one, Matrix.cons_val_zero]
      rw [hu0, hu1, hv1, Real.cos_sub, Real.sin_sub]
      linear_combination (r * Real.sin (Complex.arg b)) * this

/-- `bpP:p6:plane` (c): `ℓ` is real analytic off `0`; so are `1/ℓ`, `1/ℓ³` and `v ↦ ℓ(v)⁻³ • v`. -/
theorem analyticAt_planeLength {v : Fin 2 → ℝ} (hv : v ≠ 0) : AnalyticAt ℝ planeLength v := by
  have hne : planeSq v ≠ 0 := fun h => hv (planeSq_eq_zero_iff.mp h)
  have hpoly : ContDiffAt ℝ ω planeSq v := by
    have : planeSq = fun w : Fin 2 → ℝ => w 0 ^ 2 + w 1 ^ 2 := funext planeSq_def
    rw [this]
    have h0 : ContDiff ℝ ω (fun w : Fin 2 → ℝ => w 0) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).contDiff
    have h1 : ContDiff ℝ ω (fun w : Fin 2 → ℝ => w 1) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).contDiff
    exact ((h0.pow 2).add (h1.pow 2)).contDiffAt
  exact (hpoly.sqrt hne).analyticAt

theorem analyticAt_inv_planeLength {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    AnalyticAt ℝ (fun w => (planeLength w)⁻¹) v :=
  (analyticAt_planeLength hv).inv (planeLength_pos_iff.mpr hv).ne'

theorem analyticAt_inv_cube_smul {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    AnalyticAt ℝ (fun w => ((planeLength w) ^ 3)⁻¹ • w) v :=
  (((analyticAt_planeLength hv).pow 3).inv (pow_ne_zero 3 (planeLength_pos_iff.mpr hv).ne')).smul
    analyticAt_id

/-- `D ℓ(v) h = v·h / ℓ(v)`. -/
theorem hasFDerivAt_planeLength {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    HasFDerivAt planeLength
      (((planeLength v)⁻¹) •
        ∑ k, v k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k) v := by
  have hne : planeSq v ≠ 0 := fun h => hv (planeSq_eq_zero_iff.mp h)
  have hpos := planeLength_pos_iff.mpr hv
  have hsq : HasFDerivAt planeSq
      ((2 : ℝ) • ∑ k, v k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k) v := by
    have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k).hasFDerivAt (x := v)).pow 2)
    refine h.congr_fderiv ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext w
    simp [smul_smul]
  have := hsq.sqrt hne
  refine this.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  unfold planeLength
  have : Real.sqrt (planeSq v) ≠ 0 := hpos.ne'
  field_simp

/-- `D (1/ℓ)(v) h = - v·h / ℓ(v)³`. -/
theorem hasFDerivAt_inv_planeLength {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    HasFDerivAt (fun w => (planeLength w)⁻¹)
      (-((planeLength v ^ 3)⁻¹) •
        ∑ k, v k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) k) v := by
  have hpos := planeLength_pos_iff.mpr hv
  have h1 := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt v (hasFDerivAt_planeLength hv)
  refine h1.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  field_simp

/-- `KAM.Iso.radius` is the frozen planar length (`rfl`); likewise `radiusSq` is `planeSq`. These
and the three helpers `norm_le_planeLength`, `planeLength_le_sqrt_two_mul_norm`,
`planeLength_add_le` above are the forms imported by
`KAM.ODE.NewtonDefs`. -/
theorem radius_eq_planeLength : KAM.Iso.radius = planeLength := rfl
theorem radiusSq_eq_planeSq : KAM.Iso.radiusSq = planeSq := rfl

end Plane

end KAM.Kepler

end
