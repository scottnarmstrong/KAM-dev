/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic
public import KAM.Planetary.SecularForm.ModelTransfer
public import KAM.Planetary.SecularForm.Symmetry
public import KAM.Planetary.SecularSpectrum.Definiteness
public import KAM.Planetary.SecularSpectrum.Lift

/-!
# Secular spectrum: diagonalization of the secular quadratic form

Blueprint P, Part 9 (`bpP:p9:diagonalize`, `stepP:p9:d-a`, `d-b`, `d-c`, `bpP:p9:dict`; package
S9-Q). For an analytic family `R` of rotations diagonalizing `coeffs D (axis D I)` on an open set
`W` of actions, `diagonalize` exports the exact quadratic identity in the rotated variables, the
matched average identity under the lift `liftInv R` (with the model parameter `b` appearing once),
the negativity `2 σ_j < 0`, and the locally uniform fourth-order bound of the rotated average.

The average identity is the translation invariance of the torus average (`cell_integral_add`): in
the lift only the fast angles are shifted, by a constant vector. The uniform bound combines
`quadratic_form` (S8-Q), the model difference `identification` (S8-M) and the elementary rotation
estimate `‖R x‖ ≤ n ‖x‖` of the max norm.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

/-- The quadratic form of a conjugated diagonal matrix. -/
theorem rotDiag_quad_conj (R : Mat n) (s x : Vec n) :
    quad (R * Matrix.diagonal s * R.transpose) x = ∑ j, s j * (R.transpose.mulVec x j) ^ 2 := by
  have h1 : quad (R * Matrix.diagonal s * R.transpose) x =
      x ⬝ᵥ (R * Matrix.diagonal s * R.transpose).mulVec x := by
    simp only [quad, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mulVec_transpose]
  ring

/-- Conjugation of the quadratic form by a rotation in the rotated variable. -/
theorem rotDiag_quad_rot {R : Mat n} (h : R.transpose * R = 1) (s x : Vec n) :
    quad (R * Matrix.diagonal s * R.transpose) (R.mulVec x) = ∑ j, s j * x j ^ 2 := by
  rw [rotDiag_quad_conj, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- A rotation moves the max norm by at most the factor `n`. -/
theorem rotDiag_norm_le {R : Mat n} (h : R * R.transpose = 1) (x : Vec n) :
    ‖R.mulVec x‖ ≤ n * ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hrow : ∑ j, R i j * R i j = 1 := by
    have := congrFun (congrFun h i) i
    simpa [Matrix.mul_apply] using this
  have hR : ∀ j, |R i j| ≤ 1 := fun j => by
    have h1 : R i j * R i j ≤ 1 := hrow ▸ Finset.single_le_sum
      (f := fun j => R i j * R i j) (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
    have h2 : |R i j| * |R i j| ≤ 1 := by rwa [← abs_mul, abs_mul_self]
    nlinarith [abs_nonneg (R i j)]
  rw [Real.norm_eq_abs]
  calc |R.mulVec x i| = |∑ j, R i j * x j| := rfl
    _ ≤ ∑ j, |R i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ‖x‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        calc |R i j| * |x j| ≤ 1 * ‖x‖ :=
              mul_le_mul (hR j) (by simpa using norm_le_pi_norm x j) (abs_nonneg _) zero_le_one
          _ = ‖x‖ := one_mul _
    _ = n * ‖x‖ := by simp

/-- A slow point with the action in a small ball and small slow coordinates lies in `realDisc`. -/
theorem rotDiag_mem_realDisc (D : Data n) (a : Vec n) {r : ℝ} {I ξ η : Vec n}
    (hI : ∀ i, |I i - action D a i| < r) (hξ : ‖ξ‖ < r) (hη : ‖η‖ < r) :
    ((ξ, I, η) : Slow n) ∈ realDisc D a r := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  · change ‖((ξ i : ℝ) : ℂ)‖ < r
    rw [Complex.norm_real]
    exact (norm_le_pi_norm ξ i).trans_lt hξ
  · change ‖((I i : ℝ) : ℂ) - (action D a i : ℂ)‖ < r
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hI i
  · change ‖((η i : ℝ) : ℂ)‖ < r
    rw [Complex.norm_real]
    exact (norm_le_pi_norm η i).trans_lt hη

/-- The lift only shifts the fast angles, by a constant vector. -/
theorem rotDiag_liftInv_assemble (R : Vec n → Mat n) (I t η ξ : Vec n) :
    liftInv R (assemble I t η ξ) = assemble I
      (t + fun l => ∑ i, η i * (((R I).transpose * fderiv ℝ R I (Pi.single l 1)).mulVec ξ) i)
      ((R I).mulVec η) ((R I).mulVec ξ) := by
  simp only [liftInv, fast_fst_assemble, slow_fst_assemble, fast_snd_assemble,
    slow_snd_assemble, Pi.add_def]

/-- The average of a fast-angle-shifted integrand is the secular function. -/
theorem rotDiag_avg_shift (D : Data n) (b : Bool) {x : Slow n} (hx : x ∈ slowDom D) (c : Vec n) :
    avg (fun t => perturbation D b (assemble x.2.1 (t + c) x.2.2 x.1)) = secular D b x := by
  have h := cell_integral_add (g := fun φ => perturbation D b (assemble x.2.1 φ x.2.2 x.1))
    (fun k t => perturbation_periodic D b hx k t) c
  unfold avg secular secularAverage
  rw [smul_eq_mul]
  exact congrArg (HMul.hMul _) h

/-- The matched average at one action, for a small rotated slow point. -/
theorem rotDiag_avg_lift (D : Data n) (b : Bool) (R : Vec n → Mat n) {I ξ η : Vec n}
    (hx : ((R I).mulVec ξ, I, (R I).mulVec η) ∈ slowDom D) :
    avg (fun t => perturbation D b (liftInv R (assemble I t η ξ))) =
      secular D b ((R I).mulVec ξ, I, (R I).mulVec η) := by
  simp only [rotDiag_liftInv_assemble]
  exact rotDiag_avg_shift D b (x := ((R I).mulVec ξ, I, (R I).mulVec η)) hx _

/-- Matched model parameter b appears once, in both average and secular function. -/
theorem diagonalize (D : Data n) (hn : 2 ≤ n) {W : Set (Vec n)} (hW : IsOpen W)
    (hWI : W ⊆ actionDomain D) {R : Vec n → Mat n}
    (hAn : AnalyticOnNhd ℝ R W) (hR : ∀ I ∈ W, isSO (R I))
    (hDiag : ∀ I ∈ W, coeffs D (axis D I) =
      R I * Matrix.diagonal (sigma D (axis D I)) * (R I).transpose) :
    (∀ I ∈ W, ∀ ξ η : Vec n,
      quad (coeffs D (axis D I)) ξ + quad (coeffs D (axis D I)) η =
      ∑ j, (2*sigma D (axis D I) j) *
        oscillatorAction ((R I).transpose.mulVec η) ((R I).transpose.mulVec ξ) j) ∧
    (∀ b : Bool, ∀ I ∈ W, ∃ r : ℝ, 0 < r ∧ ∀ ξ η : Vec n,
      ‖(ξ,η)‖ < r →
      avg (fun t => perturbation D b (liftInv R (assemble I t η ξ))) =
        secular D b ((R I).mulVec ξ,I,(R I).mulVec η)) ∧
    (∀ I ∈ W, ∀ j, 2*sigma D (axis D I) j < 0) ∧
    (∀ I0 ∈ W, ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      Metric.ball I0 r ⊆ W ∧
      ∀ b : Bool, ∀ I ∈ Metric.ball I0 r, ∀ ξ η : Vec n,
        ‖(ξ,η)‖ < r →
        |avg (fun t => perturbation D b (liftInv R (assemble I t η ξ))) -
          (constantTerm D (axis D I) + (if b then modelDelta D I else 0) +
            ∑ j, (2*sigma D (axis D I) j) * oscillatorAction η ξ j)| ≤
          C * ‖(ξ,η)‖^4) := by
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hax : ∀ I ∈ W, axis D I ∈ axes n ∧ action D (axis D I) = I := fun I hI => by
    obtain ⟨a, ha, rfl⟩ := hWI hI
    rw [axis_action D ha]
    exact ⟨ha, rfl⟩
  have hRR : ∀ I ∈ W, R I * (R I).transpose = 1 := fun I hI => isSO_mul_transpose (hR I hI)
  have hRtR : ∀ I ∈ W, (R I).transpose * R I = 1 := fun I hI => (hR I hI).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro I hI ξ η
    rw [hDiag I hI, rotDiag_quad_conj, rotDiag_quad_conj, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [oscillatorAction]
    ring
  · intro b I hI
    obtain ⟨hIa, hIact⟩ := hax I hI
    obtain ⟨r1, hr1, hr1rho, -, -⟩ := perturbation_analytic D hIa
    refine ⟨r1 / n, by positivity, fun ξ η hξη => ?_⟩
    have hlt : ∀ x : Vec n, ‖x‖ < r1 / n → ‖(R I).mulVec x‖ < r1 := fun x hx => by
      calc ‖(R I).mulVec x‖ ≤ n * ‖x‖ := rotDiag_norm_le (hRR I hI) x
        _ < n * (r1 / n) := by gcongr
        _ = r1 := by field_simp
    refine rotDiag_avg_lift D b R ?_
    refine realDisc_subset_slowDom D hIa hr1rho (rotDiag_mem_realDisc D _ (fun i => ?_)
      (hlt ξ (lt_of_le_of_lt (le_max_left _ _) hξη))
      (hlt η (lt_of_le_of_lt (le_max_right _ _) hξη)))
    rw [hIact, sub_self, abs_zero]
    exact hr1
  · intro I hI j
    obtain ⟨hIa, -⟩ := hax I hI
    have h := definite D hn hIa
    have h1 : 0 < coercivity D (axis D I) := h.2.2.1
    have h2 : sigma D (axis D I) j ≤ -coercivity D (axis D I) := h.2.2.2.2.1 j
    linarith
  · intro I0 hI0
    obtain ⟨ha0, hact0⟩ := hax I0 hI0
    obtain ⟨r1, hr1, hr1rho, -, hb⟩ := perturbation_analytic D ha0
    obtain ⟨r2, C2, hr2, -, hC2, -, hbound⟩ := quadratic_form D ha0
    obtain ⟨ρ0, hρ0, hball⟩ := Metric.isOpen_iff.1 hW I0 hI0
    set s : ℝ := min r1 (min r2 ρ0) with hs
    have hspos : 0 < s := lt_min hr1 (lt_min hr2 hρ0)
    have hs1 : s ≤ r1 := min_le_left _ _
    have hs2 : s ≤ r2 := (min_le_right _ _).trans (min_le_left _ _)
    have hs3 : s ≤ ρ0 := (min_le_right _ _).trans (min_le_right _ _)
    have hrs : s / n ≤ s := div_le_self hspos.le hnR
    have hpos : 0 < s / n := by positivity
    refine ⟨s / n, C2 * n ^ 4, hpos, by positivity,
      (Metric.ball_subset_ball (hrs.trans hs3)).trans hball, ?_⟩
    intro b I hI ξ η hξη
    have hIW : I ∈ W := (Metric.ball_subset_ball (hrs.trans hs3)).trans hball hI
    have hlt : ∀ x : Vec n, ‖x‖ < s / n → ‖(R I).mulVec x‖ < s := fun x hx => by
      calc ‖(R I).mulVec x‖ ≤ n * ‖x‖ := rotDiag_norm_le (hRR I hIW) x
        _ < n * (s / n) := by gcongr
        _ = s := by field_simp
    have hξ := lt_of_le_of_lt (le_max_left _ _) hξη
    have hη := lt_of_le_of_lt (le_max_right _ _) hξη
    have hdist : ∀ i, |I i - action D (axis D I0) i| < s := fun i => by
      rw [hact0]
      have := dist_pi_lt_iff (by positivity : 0 < s / n) |>.1 (Metric.mem_ball.1 hI) i
      rw [Real.dist_eq] at this
      exact this.trans_le hrs
    have hx : ((R I).mulVec ξ, I, (R I).mulVec η) ∈ realDisc D (axis D I0) s :=
      rotDiag_mem_realDisc D _ hdist (hlt ξ hξ) (hlt η hη)
    have hx1 := realDisc_mono D (axis D I0) hs1 hx
    have hx2 := realDisc_mono D (axis D I0) hs2 hx
    have hxdom : ((R I).mulVec ξ, I, (R I).mulVec η) ∈ slowDom D :=
      realDisc_subset_slowDom D ha0 (hs1.trans_lt hr1rho) hx
    rw [rotDiag_avg_lift D b R hxdom]
    have hsec : secular D b ((R I).mulVec ξ, I, (R I).mulVec η) =
        secular D false ((R I).mulVec ξ, I, (R I).mulVec η) +
          (if b then modelDelta D I else 0) := by
      cases b
      · simp
      · have hid := (identification D hxdom).2.2.2
          ((hb false).2.2.2.2.2.2 _ hx1)
        simpa using hid
    have hq := hbound _ hx2
    have hquad : quad (coeffs D (axis D I)) ((R I).mulVec ξ) +
        quad (coeffs D (axis D I)) ((R I).mulVec η) =
        ∑ j, (2 * sigma D (axis D I) j) * oscillatorAction η ξ j := by
      rw [hDiag I hIW, rotDiag_quad_rot (hRtR I hIW), rotDiag_quad_rot (hRtR I hIW),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [oscillatorAction]
      ring
    have hnorm : ‖((R I).mulVec ξ, (R I).mulVec η)‖ ≤ n * ‖(ξ, η)‖ := by
      rw [Prod.norm_def, max_le_iff]
      exact ⟨(rotDiag_norm_le (hRR I hIW) ξ).trans (by gcongr; exact le_max_left _ _),
        (rotDiag_norm_le (hRR I hIW) η).trans (by gcongr; exact le_max_right _ _)⟩
    have hrem : |secular D false ((R I).mulVec ξ, I, (R I).mulVec η) -
        (constantTerm D (axis D I) + ∑ j, (2 * sigma D (axis D I) j) * oscillatorAction η ξ j)| ≤
        C2 * ‖((R I).mulVec ξ, (R I).mulVec η)‖ ^ 4 := by
      rw [← hquad]
      convert hq using 2
      ring
    rw [hsec]
    calc |secular D false ((R I).mulVec ξ, I, (R I).mulVec η) + (if b then modelDelta D I else 0) -
          (constantTerm D (axis D I) + (if b then modelDelta D I else 0) +
            ∑ j, (2 * sigma D (axis D I) j) * oscillatorAction η ξ j)|
        = |secular D false ((R I).mulVec ξ, I, (R I).mulVec η) -
          (constantTerm D (axis D I) + ∑ j, (2 * sigma D (axis D I) j) *
            oscillatorAction η ξ j)| := by congr 1; ring
      _ ≤ C2 * ‖((R I).mulVec ξ, (R I).mulVec η)‖ ^ 4 := hrem
      _ ≤ C2 * (n * ‖(ξ, η)‖) ^ 4 := by gcongr
      _ = C2 * n ^ 4 * ‖(ξ, η)‖ ^ 4 := by ring

/-- A rotation preserves the Euclidean length. -/
theorem rotDiag_length2_mulVec {R : Mat n} (h : R.transpose * R = 1) (x : Vec n) :
    length2 (R.mulVec x) = length2 x := by
  have key : ∑ i, (R.mulVec x) i ^ 2 = ∑ i, x i ^ 2 := by
    have h1 : ∑ i, (R.mulVec x) i ^ 2 = R.mulVec x ⬝ᵥ R.mulVec x := by
      simp only [dotProduct, sq]
    have h2 : ∑ i, x i ^ 2 = x ⬝ᵥ x := by simp only [dotProduct, sq]
    rw [h1, h2, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h,
      Matrix.one_mulVec]
  unfold length2
  rw [key]

/-- Domain adapter of `stepP:p9:d-c`: if `δ₀ > 0` and `ξ̃_j² + η̃_j² < δ₀²` for all `j`,
`√n δ₀ ≤ r` (the oscillator-disc guard, `r = ρ_*`) and the action lies within `r` of that of `a`
(the action-distance guard), then the rotated slow point `(R ξ̃, I, R η̃)` lies in
`realDisc D a r`. -/
theorem diagonalize_mem_realDisc (D : Data n) (hn : 0 < n) (a : Vec n) {R : Mat n}
    (hR : R.transpose * R = 1) {δ₀ r : ℝ} (hδ0 : 0 < δ₀) (hδ : √n * δ₀ ≤ r) {I ξ η : Vec n}
    (hosc : ∀ j, ξ j ^ 2 + η j ^ 2 < δ₀ ^ 2) (hI : ∀ i, |I i - action D a i| < r) :
    ((R.mulVec ξ, I, R.mulVec η) : Slow n) ∈ realDisc D a r := by
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hcoord : ∀ x : Vec n, (∀ j, x j ^ 2 < δ₀ ^ 2) → ‖R.mulVec x‖ < r := by
    intro x hx
    have hx' : ‖x‖ < δ₀ := by
      refine (pi_norm_lt_iff hδ0).2 fun j => ?_
      rw [Real.norm_eq_abs]
      exact abs_lt_of_sq_lt_sq (hx j) hδ0.le
    calc ‖R.mulVec x‖ ≤ length2 (R.mulVec x) := norm_le_length2 _
      _ = length2 x := rotDiag_length2_mulVec hR x
      _ ≤ √n * ‖x‖ := length2_le_sqrt_mul_norm x
      _ < √n * δ₀ := mul_lt_mul_of_pos_left hx' hsn
      _ ≤ r := hδ
  exact rotDiag_mem_realDisc D a hI
    (hcoord ξ fun j => by nlinarith [hosc j, sq_nonneg (η j)])
    (hcoord η fun j => by nlinarith [hosc j, sq_nonneg (ξ j)])

end SecularSpectrum
end KAM.Planetary
end
