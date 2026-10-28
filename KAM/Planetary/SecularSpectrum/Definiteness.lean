/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Coefficients
public import KAM.Planetary.SecularSpectrum.Norms
public import KAM.Planetary.SecularSpectrum.Definiteness.Hadamard
public import KAM.Planetary.SecularSpectrum.Definiteness.Laplace

/-!
# Secular spectrum: negative definiteness of the secular quadratic form

Blueprint P, Part 9 (`bpP:p9:definite`, `stepP:p9:p73-dom`, `stepP:p9:p73-had`,
`stepP:p9:p73-cong`): the Hadamard identity `l75` and bound `l75_bound` and the Laplace-coefficient
difference `l74` live in `Definiteness.Hadamard` and `Definiteness.Laplace`; this module exports
`coercivity` and `definite` (Fejoz Proposition 73).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

def coercivity (D : Data n) (a : Vec n) : ℝ :=
  (⨅ j, ∑ k ∈ Finset.univ.erase j, (pairA D a j k - pairB D a j k)) /
    (⨆ i, action D a i)

lemma ratio_mem {a : Vec n} (ha : a ∈ axes n) {j k : Fin n} (h : j ≠ k) :
    0 < a (min j k) / a (max j k) ∧ a (min j k) / a (max j k) < 1 :=
  ⟨div_pos (ha.1 _) (ha.1 _), (div_lt_one (ha.1 _)).2 (ha.2 (min_lt_max.2 h))⟩

lemma pairA_sub_pairB_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) {j k : Fin n} (h : j ≠ k) :
    0 < pairA D a j k - pairB D a j k := by
  unfold pairA pairB
  rw [← mul_sub]
  have h1 := ha.1 (min j k)
  have h2 := ha.1 (max j k)
  have h3 := D.hm (min j k)
  have h4 := D.hm (max j k)
  have h5 := D.hG
  exact mul_pos (by positivity)
    (l74 (by norm_num : (0:ℝ) < 3/2) (ratio_mem ha h).1 (ratio_mem ha h).2).2

lemma pairB_nonneg (D : Data n) {a : Vec n} (ha : a ∈ axes n) {j k : Fin n} (h : j ≠ k) :
    0 ≤ pairB D a j k := by
  unfold pairB
  have h1 := ha.1 (min j k)
  have h2 := ha.1 (max j k)
  have h3 := D.hm (min j k)
  have h4 := D.hm (max j k)
  have h5 := D.hG
  have := (laplace (s := 3/2) (by norm_num) 2 (ratio_mem ha h).1.le (ratio_mem ha h).2).2.2.1
  have h6 : (0:ℝ) ≤ laplace_def (3/2) 2 (a (min j k) / a (max j k)) := by simpa using this
  positivity

lemma qhat_hermitian (D : Data n) (a : Vec n) : (qhat D a).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [qhat, star_trivial]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), pairB_comm]

lemma qhat_off (D : Data n) (a : Vec n) {i j : Fin n} (h : i ≠ j) :
    qhat D a i j = pairB D a i j := by
  simp [qhat, h]

lemma dominance_qhat (D : Data n) (a : Vec n) (j : Fin n) :
    dominance (qhat D a) j = ∑ k ∈ Finset.univ.erase j, (pairA D a j k - pairB D a j k) := by
  unfold dominance
  have : ∑ k ∈ Finset.univ.erase j, qhat D a j k = ∑ k ∈ Finset.univ.erase j, pairB D a j k :=
    Finset.sum_congr rfl fun k hk => qhat_off D a (Finset.ne_of_mem_erase hk).symm
  rw [this, Finset.sum_sub_distrib]
  simp [qhat]

lemma gap_pos (D : Data n) (hn : 2 ≤ n) {a : Vec n} (ha : a ∈ axes n) (j : Fin n) :
    0 < ∑ k ∈ Finset.univ.erase j, (pairA D a j k - pairB D a j k) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  refine Finset.sum_pos (fun k hk => pairA_sub_pairB_pos D ha (Finset.ne_of_mem_erase hk).symm) ?_
  exact (Finset.erase_nonempty (Finset.mem_univ j)).2 Finset.univ_nontrivial

lemma action_pos (D : Data n) {a : Vec n} (ha : a ∈ axes n) (i : Fin n) : 0 < action D a i :=
  mul_pos (D.hm i) (Real.sqrt_pos.2 (mul_pos (mul_pos D.hG D.hm0) (ha.1 i)))

lemma quad_eigen_le {M : Mat n} (hM : M.IsHermitian) {c : ℝ}
    (hq : ∀ x, quad M x ≤ -c * length2 x ^ 2) (i : Fin n) : sorted M hM i ≤ -c := by
  set e : Fin (Fintype.card (Fin n)) ≃ Fin n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  have h0 : sorted M hM i = hM.eigenvalues (e (Fin.cast (Fintype.card_fin n).symm i.rev)) := by
    simp [sorted, Matrix.IsHermitian.eigenvalues, he]
  rw [h0]
  set j := e (Fin.cast (Fintype.card_fin n).symm i.rev)
  set v := hM.eigenvectorBasis j
  have hv := hM.mulVec_eigenvectorBasis j
  have hn1 : ∑ l, (v l) ^ 2 = 1 := by
    have h := (hM.eigenvectorBasis).norm_eq_one j
    rw [PiLp.norm_eq_of_L2, Real.sqrt_eq_one] at h
    simpa using h
  have hl : length2 (⇑v) = 1 := by rw [length2, hn1, Real.sqrt_one]
  have hquad : quad M ⇑v = hM.eigenvalues j := by
    have : ∀ l, ∑ m, v l * M l m * v m = v l * (hM.eigenvalues j * v l) := fun l => by
      have h2 := congrFun hv l
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    unfold quad
    rw [Finset.sum_congr rfl fun l _ => this l]
    have : ∀ l, v l * (hM.eigenvalues j * v l) = hM.eigenvalues j * v l ^ 2 := fun l => by ring
    rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.mul_sum, hn1, mul_one]
  have := hq ⇑v
  rw [hquad, hl] at this
  linarith

lemma continuousAt_pair {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i ≠ j) (k : ℕ)
    (D : Data n) :
    ContinuousAt (fun b : Vec n => D.G * D.m (min i j) * D.m (max i j) * b (min i j) /
      (4 * b (max i j)^2) * laplace_def (3/2) k (b (min i j) / b (max i j))) a := by
  have hq : 4 * a (max i j) ^ 2 ≠ 0 := by have := ha.1 (max i j); positivity
  have hev : ∀ p : Fin n, ContinuousAt (fun b : Vec n => b p) a := fun p =>
    (continuous_apply p).continuousAt
  have hr : ContinuousAt (fun b : Vec n => b (min i j) / b (max i j)) a :=
    (hev _).div (hev _) (ha.1 _).ne'
  have hl : ContinuousAt (laplace_def (3/2) k) (a (min i j) / a (max i j)) :=
    (analyticOnNhd_laplace_def (by norm_num : (0:ℝ) < 3/2) k _ (ratio_mem ha hij)).continuousAt
  exact (((continuousAt_const.mul (hev _)).div
    (continuousAt_const.mul ((hev _).pow 2)) hq)).mul
    (ContinuousAt.comp (g := laplace_def (3/2) k)
      (f := fun b : Vec n => b (min i j) / b (max i j)) (x := a) hl hr)

lemma continuousAt_gap (D : Data n) {a : Vec n} (ha : a ∈ axes n) (j : Fin n) :
    ContinuousAt
      (fun b : Vec n => ∑ k ∈ Finset.univ.erase j, (pairA D b j k - pairB D b j k)) a := by
  refine tendsto_finsetSum _ fun k hk => ?_
  have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
  exact (continuousAt_pair ha hjk 1 D).sub (continuousAt_pair ha hjk 2 D)

lemma continuousAt_coercivity (D : Data n) (hne : Nonempty (Fin n)) {a : Vec n}
    (ha : a ∈ axes n) : ContinuousAt (coercivity D) a := by
  have hnum : ContinuousAt (fun b : Vec n =>
      ⨅ j, ∑ k ∈ Finset.univ.erase j, (pairA D b j k - pairB D b j k)) a := by
    have := ContinuousAt.finset_inf'_apply (s := Finset.univ) (x := a) Finset.univ_nonempty
      (f := fun j (b : Vec n) => ∑ k ∈ Finset.univ.erase j, (pairA D b j k - pairB D b j k))
      (fun j _ => continuousAt_gap D ha j)
    convert this using 1
    funext b
    exact (Finset.inf'_univ_eq_ciInf _).symm
  have hden : ContinuousAt (fun b : Vec n => ⨆ i, action D b i) a := by
    have := ContinuousAt.finset_sup'_apply (s := Finset.univ) (x := a) Finset.univ_nonempty
      (f := fun i (b : Vec n) => action D b i)
      (fun i _ => by
        unfold action
        exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
          (continuousAt_const.mul (continuous_apply i).continuousAt)))
    convert this using 1
    funext b
    exact (Finset.sup'_univ_eq_ciSup _).symm
  obtain ⟨i0⟩ := hne
  have hpos : 0 < ⨆ i, action D a i :=
    lt_of_lt_of_le (action_pos D ha i0) (le_ciSup (Set.finite_range _).bddAbove i0)
  exact hnum.div hden hpos.ne'

theorem definite (D : Data n) (hn : 2 ≤ n)
    {a : Vec n} (ha : a ∈ axes n) :
    let cHat : ℝ := ⨅ j, ∑ k ∈ Finset.univ.erase j,
      (pairA D a j k - pairB D a j k)
    0 < cHat ∧
    (∀ x : Vec n,
      quad (qhat D a) x ≤
        -(∑ j, (∑ k ∈ Finset.univ.erase j,
          (pairA D a j k - pairB D a j k)) * x j^2) ∧
      -(∑ j, (∑ k ∈ Finset.univ.erase j,
          (pairA D a j k - pairB D a j k)) * x j^2) ≤
        -cHat * length2 x^2) ∧
    0 < coercivity D a ∧
    (∀ x, quad (coeffs D a) x ≤ -coercivity D a * length2 x^2) ∧
    (∀ j, sigma D a j ≤ -coercivity D a) ∧
    ContinuousOn (coercivity D) (axes n) := by
  intro cHat
  have hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hle : ∀ j, cHat ≤ ∑ k ∈ Finset.univ.erase j, (pairA D a j k - pairB D a j k) :=
    fun j => ciInf_le (Set.finite_range _).bddBelow j
  have hpos : 0 < cHat := by
    obtain ⟨j0, hj0⟩ := exists_eq_ciInf_of_finite
      (f := fun j => ∑ k ∈ Finset.univ.erase j, (pairA D a j k - pairB D a j k))
    have := gap_pos D hn ha j0
    rw [hj0] at this
    exact this
  have hlen2 : ∀ x : Vec n, length2 x ^ 2 = ∑ j, x j ^ 2 := fun x =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
  have hq : ∀ x : Vec n, quad (qhat D a) x ≤ -cHat * length2 x ^ 2 := fun x => by
    refine l75_bound (qhat D a) (qhat_hermitian D a)
      (fun i j h => by rw [qhat_off D a h]; exact pairB_nonneg D ha h) (c := cHat)
      (fun j => by rw [dominance_qhat]; exact hle j) x
  refine ⟨hpos, fun x => ⟨?_, ?_⟩, ?_⟩
  · rw [l75 _ (qhat_hermitian D a) x]
    have h2 : 0 ≤ ∑ j, ∑ k ∈ Finset.univ.filter (j < ·), qhat D a j k * (x j - x k) ^ 2 :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k hk =>
        mul_nonneg (by rw [qhat_off D a (Finset.mem_filter.1 hk).2.ne]
                       exact pairB_nonneg D ha (Finset.mem_filter.1 hk).2.ne)
          (sq_nonneg _)
    simp only [dominance_qhat]
    linarith
  · rw [hlen2, neg_mul, neg_le_neg_iff, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle j) (sq_nonneg _)
  · set L := ⨆ i, action D a i with hL
    obtain ⟨i0⟩ := hne
    have hLpos : 0 < L :=
      lt_of_lt_of_le (action_pos D ha i0) (le_ciSup (Set.finite_range _).bddAbove i0)
    have hcoer : 0 < coercivity D a := div_pos hpos hLpos
    have hcong : ∀ x : Vec n, quad (coeffs D a) x ≤ -coercivity D a * length2 x ^ 2 := fun x => by
      set y : Vec n := fun i => x i / √(action D a i) with hy
      have hsq : ∀ i, √(action D a i) ^ 2 = action D a i := fun i =>
        Real.sq_sqrt (action_pos D ha i).le
      have hsp : ∀ i, 0 < √(action D a i) := fun i => Real.sqrt_pos.2 (action_pos D ha i)
      have e1 : quad (coeffs D a) x = quad (qhat D a) y := by
        unfold quad coeffs
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have := (hsp i).ne'
        have := (hsp j).ne'
        simp only [hy]
        field_simp
      have e2 : length2 x ^ 2 / L ≤ length2 y ^ 2 := by
        rw [hlen2, hlen2, Finset.sum_div]
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [hy, div_pow, hsq]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (action_pos D ha i)
          (le_ciSup (Set.finite_range _).bddAbove i)
      have e3 := hq y
      rw [e1]
      have : -coercivity D a * length2 x ^ 2 = -(cHat * (length2 x ^ 2 / L)) := by
        unfold coercivity; rw [← hL]; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left e2 hpos.le]
    refine ⟨hcoer, hcong, fun j => quad_eigen_le (coeffs_hermitian D a) hcong j, ?_⟩
    intro b hb
    exact (continuousAt_coercivity D ⟨⟨0, by omega⟩⟩ hb).continuousWithinAt

end SecularSpectrum

end KAM.Planetary
