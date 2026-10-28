/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularSpectrum.Definiteness
public import KAM.Planetary.SecularSpectrum.LocalAnalytic
public import KAM.Planetary.SecularSpectrum.GoodPolynomial

/-!
# Secular spectrum: two planets

Blueprint P, Part 9 (`bpP:p9:n2`, `stepP:p9:n2-mat`, `stepP:p9:n2-res`): for two planets the
secular matrix `coeffs D a` is an explicit `2 × 2` symmetric matrix.  `n2` gives its determinant,
the positivity of the determinant and of the discriminant, the strict order of the two eigenvalues
and the two characterisations of `nr4` (by the eigenvalue ratio and by trace and determinant);
`n2_global_frame` gives one analytic `SO(2)` eigenframe on all of `axes 2`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

section Entries

lemma pairB_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) {j k : Fin n} (h : j ≠ k) :
    0 < pairB D a j k := by
  unfold pairB
  have h1 := ha.1 (min j k)
  have h2 := ha.1 (max j k)
  have h3 := D.hm (min j k)
  have h4 := D.hm (max j k)
  have h5 := D.hG
  have := (laplace (s := 3/2) (by norm_num) 2 (ratio_mem ha h).1.le (ratio_mem ha h).2).2.2.2.1
    (ratio_mem ha h).1
  have h6 : (0:ℝ) < laplace_def (3/2) 2 (a (min j k) / a (max j k)) := by simpa using this
  positivity

lemma pairA_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) {j k : Fin n} (h : j ≠ k) :
    0 < pairA D a j k := by
  have := pairA_sub_pairB_pos D ha h
  have := pairB_pos D ha h
  linarith

lemma pairA_swap (D : Data n) (a : Vec n) (i j : Fin n) : pairA D a i j = pairA D a j i := by
  simp only [pairA, min_comm i j, max_comm i j]

lemma action_nonneg (D : Data n) (a : Vec n) (i : Fin n) : 0 ≤ action D a i :=
  mul_nonneg (D.hm i).le (Real.sqrt_nonneg _)

variable (D : Data 2) {a : Vec 2}

lemma coeffs_two_diag0 (a : Vec 2) :
    coeffs D a 0 0 = -pairA D a 0 1 / action D a 0 := by
  have : Finset.univ.erase (0 : Fin 2) = {1} := by decide
  simp only [coeffs, qhat, ite_true, this, Finset.sum_singleton]
  rw [Real.mul_self_sqrt (action_nonneg D a 0)]

lemma coeffs_two_diag1 (a : Vec 2) :
    coeffs D a 1 1 = -pairA D a 0 1 / action D a 1 := by
  have : Finset.univ.erase (1 : Fin 2) = {0} := by decide
  simp only [coeffs, qhat, ite_true, this, Finset.sum_singleton]
  rw [Real.mul_self_sqrt (action_nonneg D a 1), pairA_swap]

lemma coeffs_two_off01 (a : Vec 2) :
    coeffs D a 0 1 = pairB D a 0 1 / (√(action D a 0) * √(action D a 1)) := by
  simp [coeffs, qhat]

lemma coeffs_two_off10 (a : Vec 2) :
    coeffs D a 1 0 = pairB D a 0 1 / (√(action D a 0) * √(action D a 1)) := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp only [coeffs, qhat, h, ↓reduceIte, pairB_comm D a 1 0]
  rw [mul_comm (√(action D a 1))]

end Entries

section Spectrum

lemma sorted_two_sum (M : Mat 2) (hM : M.IsHermitian) :
    sorted M hM 0 + sorted M hM 1 = M.trace := by
  have h := charpoly_eq_prod_sorted hM
  rw [Matrix.charpoly_fin_two, Fin.prod_univ_two] at h
  have h1 := congrArg (fun p => p.coeff 1) h
  simp [Polynomial.coeff_X, Polynomial.coeff_C, sub_mul, mul_sub] at h1
  linarith

lemma sorted_two_prod (M : Mat 2) (hM : M.IsHermitian) :
    sorted M hM 0 * sorted M hM 1 = M.det := by
  have h := charpoly_eq_prod_sorted hM
  rw [Matrix.charpoly_fin_two, Fin.prod_univ_two] at h
  have h1 := congrArg (fun p => p.coeff 0) h
  simp [Polynomial.coeff_X, Polynomial.coeff_C, sub_mul, mul_sub] at h1
  linarith

lemma eq_of_sum_prod {s0 s1 t0 t1 : ℝ} (hs : s0 < s1) (ht : t0 < t1) (h1 : s0 + s1 = t0 + t1)
    (h2 : s0 * s1 = t0 * t1) : s0 = t0 ∧ s1 = t1 := by
  have h : (s1 - s0 - (t1 - t0)) * (s1 - s0 + (t1 - t0)) = 0 := by
    have : (s1 - s0)^2 = (t1 - t0)^2 := by
      have e1 : (s1 - s0)^2 = (s0 + s1)^2 - 4 * (s0 * s1) := by ring
      have e2 : (t1 - t0)^2 = (t0 + t1)^2 - 4 * (t0 * t1) := by ring
      rw [e1, e2, h1, h2]
    nlinarith
  rcases mul_eq_zero.1 h with h | h <;> constructor <;> nlinarith

variable (D : Data 2) {a : Vec 2}

lemma trace_two (a : Vec 2) :
    (coeffs D a).trace = -pairA D a 0 1 / action D a 0 + -pairA D a 0 1 / action D a 1 := by
  rw [Matrix.trace_fin_two, coeffs_two_diag0, coeffs_two_diag1]

lemma det_two (ha : a ∈ axes 2) :
    (coeffs D a).det = ((pairA D a 0 1)^2 - (pairB D a 0 1)^2) /
      (action D a 0 * action D a 1) := by
  have h0 := action_pos D ha 0
  have h1 := action_pos D ha 1
  have e0 := Real.mul_self_sqrt h0.le
  have e1 := Real.mul_self_sqrt h1.le
  have p0 : 0 < √(action D a 0) := Real.sqrt_pos.2 h0
  have p1 : 0 < √(action D a 1) := Real.sqrt_pos.2 h1
  rw [Matrix.det_fin_two, coeffs_two_diag0, coeffs_two_diag1, coeffs_two_off01,
    coeffs_two_off10]
  set x := √(action D a 0)
  set y := √(action D a 1)
  clear_value x y
  rw [← e0, ← e1]
  field_simp

lemma det_two_pos (ha : a ∈ axes 2) : 0 < (coeffs D a).det := by
  rw [det_two D ha]
  have h0 := action_pos D ha 0
  have h1 := action_pos D ha 1
  have hd := pairA_sub_pairB_pos D ha (j := 0) (k := 1) (by decide)
  have hB := pairB_pos D ha (j := 0) (k := 1) (by decide)
  have hA := pairA_pos D ha (j := 0) (k := 1) (by decide)
  refine div_pos ?_ (mul_pos h0 h1)
  nlinarith

lemma disc_two_pos (ha : a ∈ axes 2) : 0 < (coeffs D a).trace^2 - 4 * (coeffs D a).det := by
  have h0 := action_pos D ha 0
  have h1 := action_pos D ha 1
  have hB := pairB_pos D ha (j := 0) (k := 1) (by decide)
  have key : (coeffs D a).trace^2 - 4 * (coeffs D a).det =
      (pairA D a 0 1 / action D a 0 - pairA D a 0 1 / action D a 1)^2 +
        4 * (pairB D a 0 1)^2 / (action D a 0 * action D a 1) := by
    rw [trace_two, det_two D ha]
    field_simp
    ring
  rw [key]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)

lemma sigma_two_lt (ha : a ∈ axes 2) : sigma D a 0 < sigma D a 1 := by
  have hle : sigma D a 0 ≤ sigma D a 1 :=
    sorted_monotone (coeffs_hermitian D a) (by decide : (0 : Fin 2) ≤ 1)
  refine lt_of_le_of_ne hle fun h => ?_
  have h1 := sorted_two_sum (coeffs D a) (coeffs_hermitian D a)
  have h2 := sorted_two_prod (coeffs D a) (coeffs_hermitian D a)
  have := disc_two_pos D ha
  change sigma D a 0 + sigma D a 1 = _ at h1
  change sigma D a 0 * sigma D a 1 = _ at h2
  rw [← h1, ← h2, h] at this
  nlinarith

lemma sigma_two_neg (ha : a ∈ axes 2) (j : Fin 2) : sigma D a j < 0 := by
  have h := (definite D (le_refl 2) ha).2.2.2.2.1 j
  have := (definite D (le_refl 2) ha).2.2.1
  linarith

lemma sigma_two_inj (ha : a ∈ axes 2) : Function.Injective (sigma D a) := by
  have h := sigma_two_lt D ha
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

lemma nr4_two_iff (ha : a ∈ axes 2) :
    nr4 (sigma D a) ↔ sigma D a 0 / sigma D a 1 ≠ 2 ∧ sigma D a 0 / sigma D a 1 ≠ 3 := by
  have hlt := sigma_two_lt D ha
  have n1 := sigma_two_neg D ha 1
  have hdiv : ∀ c : ℝ, sigma D a 0 / sigma D a 1 = c ↔ sigma D a 0 = c * sigma D a 1 :=
    fun c => by rw [div_eq_iff n1.ne]
  rw [ne_eq, ne_eq, hdiv, hdiv]
  constructor
  · rintro ⟨-, hk⟩
    refine ⟨fun h => hk ![1, -2] ⟨?_, ?_⟩ ?_, fun h => hk ![1, -3] ⟨?_, ?_⟩ ?_⟩ <;>
      simp [Fin.sum_univ_two] <;> linarith
  · rintro ⟨h2, h3⟩
    refine ⟨sigma_two_inj D ha, fun k hk => ?_⟩
    obtain ⟨hk0, hk4⟩ := hk
    simp only [Fin.sum_univ_two, Fin.isValue] at hk0 hk4 ⊢
    have b0 := abs_le.1 ((le_add_of_nonneg_right (abs_nonneg (k 1))).trans hk4)
    have b1 := abs_le.1 ((le_add_of_nonneg_left (abs_nonneg (k 0))).trans hk4)
    intro hs
    generalize k 0 = k0 at *
    generalize k 1 = k1 at *
    generalize sigma D a 0 = s0 at *
    generalize sigma D a 1 = s1 at *
    obtain ⟨b0l, b0u⟩ := b0
    obtain ⟨b1l, b1u⟩ := b1
    interval_cases k0 <;> interval_cases k1 <;>
      first | (exfalso; revert hk0 hk4; norm_num; done) | (push_cast at hs; exact h2 (by linarith)) |
        (push_cast at hs; exact h3 (by linarith))

lemma two_trace_det_iff (ha : a ∈ axes 2) :
    nr4 (sigma D a) ↔
      (2 * (coeffs D a).trace^2 - 9 * (coeffs D a).det) *
        (3 * (coeffs D a).trace^2 - 16 * (coeffs D a).det) ≠ 0 := by
  have hlt := sigma_two_lt D ha
  have n1 := sigma_two_neg D ha 1
  have n0 := sigma_two_neg D ha 0
  have hdiv : ∀ c : ℝ, sigma D a 0 / sigma D a 1 = c ↔ sigma D a 0 = c * sigma D a 1 :=
    fun c => by rw [div_eq_iff n1.ne]
  rw [nr4_two_iff D ha, ← sorted_two_sum (coeffs D a) (coeffs_hermitian D a),
    ← sorted_two_prod (coeffs D a) (coeffs_hermitian D a), ne_eq, ne_eq, hdiv, hdiv]
  change ¬ _ ∧ ¬ _ ↔ ¬ (2 * (sigma D a 0 + sigma D a 1)^2 - 9 * (sigma D a 0 * sigma D a 1)) *
    (3 * (sigma D a 0 + sigma D a 1)^2 - 16 * (sigma D a 0 * sigma D a 1)) = 0
  have e : (2 * (sigma D a 0 + sigma D a 1)^2 - 9 * (sigma D a 0 * sigma D a 1)) *
      (3 * (sigma D a 0 + sigma D a 1)^2 - 16 * (sigma D a 0 * sigma D a 1)) =
      (sigma D a 0 - 2 * sigma D a 1) * (2 * sigma D a 0 - sigma D a 1) *
        ((sigma D a 0 - 3 * sigma D a 1) * (3 * sigma D a 0 - sigma D a 1)) := by ring
  rw [e]
  simp only [mul_eq_zero, sub_eq_zero]
  have f1 : ¬ 2 * sigma D a 0 = sigma D a 1 := by intro h; linarith
  have f2 : ¬ 3 * sigma D a 0 = sigma D a 1 := by intro h; linarith
  tauto

end Spectrum

theorem n2 (D : Data 2) {a : Vec 2} (ha : a ∈ axes 2) :
    (coeffs D a).det = ((pairA D a 0 1)^2-(pairB D a 0 1)^2) /
      (action D a 0*action D a 1) ∧
    0 < (coeffs D a).det ∧
    0 < (coeffs D a).trace^2-4*(coeffs D a).det ∧
    sigma D a 0 < sigma D a 1 ∧
    (nr4 (sigma D a) ↔ sigma D a 0/sigma D a 1 ≠ 2 ∧ sigma D a 0/sigma D a 1 ≠ 3) ∧
    (nr4 (sigma D a) ↔
      (2*(coeffs D a).trace^2-9*(coeffs D a).det) *
      (3*(coeffs D a).trace^2-16*(coeffs D a).det) ≠ 0) :=
  ⟨det_two D ha, det_two_pos D ha, disc_two_pos D ha, sigma_two_lt D ha, nr4_two_iff D ha,
    two_trace_det_iff D ha⟩

section Frame

lemma isOpen_axes (n : ℕ) : IsOpen (axes n) := by
  have : axes n = (⋂ i, {a : Vec n | 0 < a i}) ∩
      ⋂ i, ⋂ j, ⋂ (_ : i < j), {a : Vec n | a i < a j} := by
    ext a; simp [axes, StrictMono]
  rw [this]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j))

lemma eigenvalues_injective_of_sorted {M : Mat n} (hM : M.IsHermitian)
    (h : Function.Injective (sorted M hM)) : Function.Injective hM.eigenvalues := by
  obtain ⟨τ, hτ, hs⟩ := sorted_eq_eigenvalues_comp hM
  intro i j hij
  obtain ⟨i', rfl⟩ := hτ.2 i
  obtain ⟨j', rfl⟩ := hτ.2 j
  rw [← hs, ← hs] at hij
  rw [h hij]

lemma isSO_neg (R : Mat 2) (hR : isSO R) : isSO (-R) := by
  refine ⟨by simpa [Matrix.transpose_neg] using hR.1, ?_⟩
  rw [Matrix.det_neg]
  simpa using hR.2

lemma neg_conj (R : Mat 2) (s : Vec 2) :
    (-R) * Matrix.diagonal s * (-R).transpose = R * Matrix.diagonal s * R.transpose := by
  simp [Matrix.transpose_neg]

variable (D : Data 2) {a : Vec 2}

/-- Any frame with strictly increasing spectrum carries the sorted spectrum `sigma`. -/
lemma frame_sigma (ha : a ∈ axes 2) {R : Mat 2} {s : Vec 2} (hR : isSO R) (hs : StrictMono s)
    (h : coeffs D a = R * Matrix.diagonal s * R.transpose) : s = sigma D a := by
  have hRR : R.transpose * R = 1 := hR.1
  have ht : (coeffs D a).trace = s 0 + s 1 := by
    rw [h, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.one_mul,
      Matrix.trace_diagonal, Fin.sum_univ_two]
  have hd : (coeffs D a).det = s 0 * s 1 := by
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hR.2, Matrix.det_diagonal,
      Fin.prod_univ_two]
    ring
  have h1 := sorted_two_sum (coeffs D a) (coeffs_hermitian D a)
  have h2 := sorted_two_prod (coeffs D a) (coeffs_hermitian D a)
  obtain ⟨e0, e1⟩ := eq_of_sum_prod (hs (by decide : (0 : Fin 2) < 1)) (sigma_two_lt D ha)
    (by rw [← ht, ← h1]; rfl) (by rw [← hd, ← h2]; rfl)
  funext i
  fin_cases i
  · exact e0
  · exact e1

/-- A frame of `coeffs D a` has a nonvanishing `(1,1)` entry, as the off-diagonal term is positive. -/
lemma frame_entry_ne (ha : a ∈ axes 2) {R : Mat 2} (hR : isSO R)
    (h : coeffs D a = R * Matrix.diagonal (sigma D a) * R.transpose) : R 1 1 ≠ 0 := by
  have hRR : R.transpose * R = 1 := hR.1
  have hMR : coeffs D a * R = R * Matrix.diagonal (sigma D a) := by
    rw [h, Matrix.mul_assoc, Matrix.mul_assoc, hRR, Matrix.mul_one]
  have e := congrFun (congrFun hMR 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, mul_ite, mul_zero,
    ite_true] at e
  have hq : 0 < coeffs D a 1 0 := by
    rw [coeffs_two_off10]
    have := pairB_pos D ha (j := 0) (k := 1) (by decide)
    have := action_pos D ha 0
    have := action_pos D ha 1
    positivity
  intro h11
  rw [h11] at e
  simp at e
  have h01 : R 0 1 = 0 := by
    rcases e with e | e
    · exact absurd e hq.ne'
    · exact e
  have := congrFun (congrFun hRR 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h11] at this

/-- The normalised frame: special orthogonal, diagonalising, with positive `(1,1)` entry. -/
def NormFrame (D : Data 2) (a : Vec 2) (R : Mat 2) : Prop :=
  isSO R ∧ coeffs D a = R * Matrix.diagonal (sigma D a) * R.transpose ∧ 0 < R 1 1

lemma normFrame_unique (ha : a ∈ axes 2) {R S : Mat 2} (hR : NormFrame D a R)
    (hS : NormFrame D a S) : R = S := by
  obtain ⟨q, -, hq, hqp, hSq⟩ := frame_eq_signs hR.1 hS.1 (sigma_two_inj D ha)
    (by rw [← hR.2.1, ← hS.2.1])
  rw [Fin.prod_univ_two] at hqp
  have h11 : S 1 1 = R 1 1 * q 1 := by
    rw [hSq]; simp [Matrix.mul_apply, Matrix.diagonal_apply]
  have hq1 : q 1 = 1 := by
    rcases hq 1 with h | h
    · exact h
    · have := hS.2.2; have := hR.2.2
      rw [h11, h] at *; linarith
  have hq0 : q 0 = 1 := by
    rcases hq 0 with h | h
    · exact h
    · rw [h, hq1] at hqp; norm_num at hqp
  have : q = 1 := by
    funext i; fin_cases i
    · exact hq0
    · exact hq1
  rw [hSq, this]
  simp

lemma normFrame_smul {b : Vec 2} {R : Mat 2} {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hR : isSO R)
    (hc : coeffs D b = R * Matrix.diagonal (sigma D b) * R.transpose) (hp : 0 < ε * R 1 1) :
    NormFrame D b (ε • R) := by
  rcases hε with rfl | rfl
  · exact ⟨by simpa using hR, by simpa using hc, by simpa using hp⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa using isSO_neg R hR
    · simpa [neg_conj] using hc
    · simpa using hp

lemma sign_const {B : Set (Vec 2)} (hB : IsPreconnected B) {f : Vec 2 → ℝ}
    (hf : ContinuousOn f B) (hne : ∀ x ∈ B, f x ≠ 0) {x y : Vec 2} (hx : x ∈ B) (hy : y ∈ B)
    (hfx : 0 < f x) : 0 < f y := by
  by_contra hneg
  have hy0 : f y < 0 := lt_of_le_of_ne (not_lt.1 hneg) (hne y hy)
  obtain ⟨c, hc, hc0⟩ := hB.intermediate_value hy hx hf ⟨hy0.le, hfx.le⟩
  exact hne c hc hc0

lemma local_normFrame (ha : a ∈ axes 2) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ axes 2 ∧ ∃ F : Vec 2 → Mat 2,
      AnalyticOnNhd ℝ F (Metric.ball a r) ∧ ∀ b ∈ Metric.ball a r, NormFrame D b (F b) := by
  obtain ⟨r, hr, hball, s, R, -, hR, hfr⟩ := local_analytic (isOpen_axes 2)
    (fun x _ => coeffs_hermitian D x) (coeffs_analytic D) ha
    (eigenvalues_injective_of_sorted _ (sigma_two_inj D ha))
  have hfrm : ∀ b ∈ Metric.ball a r, isSO (R b) ∧
      coeffs D b = R b * Matrix.diagonal (sigma D b) * (R b).transpose := fun b hb => by
    obtain ⟨hSO, hmono, hM⟩ := hfr b hb
    have := frame_sigma D (hball hb) hSO hmono hM
    exact ⟨hSO, by rw [← this]; exact hM⟩
  have hne : ∀ b ∈ Metric.ball a r, (fun x => R x 1 1) b ≠ 0 := fun b hb =>
    frame_entry_ne D (hball hb) (hfrm b hb).1 (hfrm b hb).2
  have hcont : ContinuousOn (fun x => R x 1 1) (Metric.ball a r) := fun b hb =>
    (analyticAt_mat_entry (hR b hb) 1 1).continuousAt.continuousWithinAt
  have hpre : IsPreconnected (Metric.ball a r) := (convex_ball a r).isPreconnected
  have hamem : a ∈ Metric.ball a r := Metric.mem_ball_self hr
  have key : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ b ∈ Metric.ball a r, 0 < ε * R b 1 1 := by
    rcases lt_or_gt_of_ne (hne a hamem) with h | h
    · refine ⟨-1, Or.inr rfl, fun b hb => ?_⟩
      have := sign_const hpre (f := fun x => -R x 1 1) hcont.neg (fun x hx => neg_ne_zero.2 (hne x hx))
        hamem hb (by simpa using h)
      simpa using this
    · refine ⟨1, Or.inl rfl, fun b hb => ?_⟩
      simpa using sign_const hpre hcont hne hamem hb h
  obtain ⟨ε, hε, hεp⟩ := key
  refine ⟨r, hr, hball, fun x => ε • R x, fun b hb => (analyticAt_const (v := ε)).smul (hR b hb) |>.congr
    (Filter.Eventually.of_forall fun x => rfl), ?_⟩
  intro b hb
  exact normFrame_smul D hε (hfrm b hb).1 (hfrm b hb).2 (hεp b hb)

end Frame

theorem n2_global_frame (D : Data 2) : ∃ R : Vec 2 → Mat 2,
    AnalyticOnNhd ℝ R (axes 2) ∧ ∀ a ∈ axes 2,
      isSO (R a) ∧ coeffs D a = R a * Matrix.diagonal (sigma D a) * (R a).transpose := by
  have hex : ∀ a ∈ axes 2, ∃ R, NormFrame D a R := fun a ha => by
    obtain ⟨r, hr, -, F, -, hF⟩ := local_normFrame D ha
    exact ⟨F a, hF a (Metric.mem_ball_self hr)⟩
  classical
  let R : Vec 2 → Mat 2 := fun a => if h : a ∈ axes 2 then (hex a h).choose else 0
  have hR : ∀ a (h : a ∈ axes 2), NormFrame D a (R a) := fun a h => by
    simpa only [R, h, dite_true] using (hex a h).choose_spec
  refine ⟨R, fun a ha => ?_, fun a ha => ⟨(hR a ha).1, (hR a ha).2.1⟩⟩
  obtain ⟨r, hr, hball, F, hF, hFn⟩ := local_normFrame D ha
  refine (hF a (Metric.mem_ball_self hr)).congr ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with b hb
  exact normFrame_unique D (hball hb) (hFn b hb) (hR b (hball hb))

end SecularSpectrum

end KAM.Planetary
