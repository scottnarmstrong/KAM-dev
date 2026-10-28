/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Basic
public import KAM.Planetary.SecularForm.Laplace
public import KAM.Planetary.SecularSpectrum.Norms

/-!
# Secular form: the matrix coefficients

Blueprint P, Part 8 (`bpP:p8:coeffs`): the pair coefficients `pairA`, `pairB`, the constant term,
the literal matrix `qhat`, the halved matrix `coeffs`, the quadratic form `quad`, together with
`coeffs_hermitian` and `coeffs_analytic`; and `SecularSpectrum.sigma`, the sorted spectrum of
`coeffs`, declared after `coeffs_hermitian`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

def pairA (D : Data n) (a : Vec n) (i j : Fin n) : ℝ :=
  D.G * D.m (min i j) * D.m (max i j) * a (min i j) / (4 * a (max i j)^2) *
    laplace_def (3/2) 1 (a (min i j) / a (max i j))
def pairB (D : Data n) (a : Vec n) (i j : Fin n) : ℝ :=
  D.G * D.m (min i j) * D.m (max i j) * a (min i j) / (4 * a (max i j)^2) *
    laplace_def (3/2) 2 (a (min i j) / a (max i j))
def constantTerm (D : Data n) (a : Vec n) : ℝ :=
  -∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    D.G * D.m i * D.m j / a j * laplace_def (1/2) 0 (a i / a j)
def qhat (D : Data n) (a : Vec n) : Mat n :=
  fun i j => if i = j then -∑ k ∈ Finset.univ.erase i, pairA D a i k else pairB D a i j
def coeffs (D : Data n) (a : Vec n) : Mat n :=
  fun i j => qhat D a i j / (√(action D a i) * √(action D a j))
def quad (M : Mat n) (x : Vec n) : ℝ := ∑ i, ∑ j, x i * M i j * x j

theorem pairB_comm (D : Data n) (a : Vec n) (i j : Fin n) : pairB D a i j = pairB D a j i := by
  simp only [pairB, min_comm i j, max_comm i j]

theorem coeffs_hermitian (D : Data n) (a : Vec n) : (coeffs D a).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [coeffs, qhat, star_trivial]
  by_cases h : i = j
  · subst h; rfl
  · rw [ite_cond_eq_false _ _ (eq_false h), ite_cond_eq_false _ _ (eq_false (Ne.symm h)),
      pairB_comm D a j i, mul_comm (√(action D a j))]

private theorem analyticAt_eval (i : Fin n) (a : Vec n) : AnalyticAt ℝ (fun b : Vec n => b i) a :=
  analyticAt_pi_iff.mp analyticAt_id i

private theorem analyticAt_ratio {a : Vec n} (ha : a ∈ axes n) {p q : Fin n} :
    AnalyticAt ℝ (fun b : Vec n => b p / b q) a := by
  have hq : a q ≠ 0 := (ha.1 q).ne'
  exact (analyticAt_eval p a).div (analyticAt_eval q a) hq

private theorem analyticAt_laplace_ratio {a : Vec n} (ha : a ∈ axes n) {p q : Fin n}
    (hpq : p < q) (k : ℕ) :
    AnalyticAt ℝ (fun b : Vec n => laplace_def (3/2) k (b p / b q)) a := by
  have hr0 : 0 < a p / a q := div_pos (ha.1 p) (ha.1 q)
  have hr1 : a p / a q < 1 := (div_lt_one (ha.1 q)).2 (ha.2 hpq)
  exact AnalyticAt.comp (g := laplace_def (3/2) k) (f := fun b : Vec n => b p / b q)
    (analyticOnNhd_laplace_def (by norm_num : (0:ℝ) < 3/2) k _ ⟨hr0, hr1⟩)
    (analyticAt_ratio ha)

private theorem analyticAt_pair {a : Vec n} (ha : a ∈ axes n) {i j : Fin n} (hij : i ≠ j)
    (k : ℕ) (D : Data n) :
    AnalyticAt ℝ (fun b : Vec n => D.G * D.m (min i j) * D.m (max i j) * b (min i j) /
      (4 * b (max i j)^2) * laplace_def (3/2) k (b (min i j) / b (max i j))) a := by
  have hpq : min i j < max i j := by
    rcases lt_or_gt_of_ne hij with h | h
    · simpa [min_eq_left h.le, max_eq_right h.le] using h
    · simpa [min_eq_right h.le, max_eq_left h.le] using h
  have hq : 4 * a (max i j) ^ 2 ≠ 0 := by have := ha.1 (max i j); positivity
  exact ((analyticAt_const.mul (analyticAt_eval _ a)).div
    (analyticAt_const.mul ((analyticAt_eval _ a).pow 2)) hq).mul
    (analyticAt_laplace_ratio ha hpq k)

theorem coeffs_analytic (D : Data n) : AnalyticOnNhd ℝ (coeffs D) (axes n) := by
  intro a ha
  refine analyticAt_pi_iff.2 fun i => analyticAt_pi_iff.2 fun j => ?_
  have hsq : ∀ l : Fin n, AnalyticAt ℝ (fun b : Vec n => √(action D b l)) a := fun l => by
    have h0 : 0 < D.G * D.m0 * a l := mul_pos (mul_pos D.hG D.hm0) (ha.1 l)
    have hin : AnalyticAt ℝ (fun b : Vec n => D.G * D.m0 * b l) a :=
      analyticAt_const.mul (analyticAt_eval l a)
    have h1 : AnalyticAt ℝ (fun b : Vec n => √(D.G * D.m0 * b l)) a :=
      (hin.contDiffAt.sqrt h0.ne').analyticAt
    have h2 : AnalyticAt ℝ (fun b : Vec n => action D b l) a :=
      analyticAt_const.mul h1
    exact (h2.contDiffAt.sqrt (mul_pos (D.hm l) (Real.sqrt_pos.2 h0)).ne').analyticAt
  have hden : √(action D a i) * √(action D a j) ≠ 0 := by
    have hpos : ∀ l, 0 < √(action D a l) := fun l =>
      Real.sqrt_pos.2 (mul_pos (D.hm l) (Real.sqrt_pos.2 (mul_pos (mul_pos D.hG D.hm0) (ha.1 l))))
    exact (mul_pos (hpos i) (hpos j)).ne'
  refine AnalyticAt.div ?_ ((hsq i).mul (hsq j)) hden
  by_cases h : i = j
  · subst h
    simp only [qhat, ite_true]
    have hs : AnalyticAt ℝ (fun b : Vec n => ∑ k ∈ Finset.univ.erase i, pairA D b i k) a :=
      Finset.analyticAt_fun_sum _ fun k hk =>
        analyticAt_pair ha (Finset.ne_of_mem_erase hk).symm 1 D
    exact (analyticAt_const (v := (0:ℝ))).sub hs |>.congr
      (Filter.Eventually.of_forall fun b => by simp)
  · simp only [qhat, ite_cond_eq_false _ _ (eq_false h)]
    exact analyticAt_pair ha h 2 D

end SecularForm

namespace SecularSpectrum
open SecularForm
variable {n : ℕ}

def sigma (D : Data n) (a : Vec n) : Vec n := sorted (coeffs D a) (coeffs_hermitian D a)

end SecularSpectrum

end KAM.Planetary
