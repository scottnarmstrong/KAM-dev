/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.RCLike.Basic

/-!
# Cartesian polynomials: formal partial derivatives (track B, B2-POLY)

`CartPoly.cartDq i`, `CartPoly.cartDp i` are the formal partial derivatives (computable). Over
`𝕜 ∈ {ℝ, ℂ}` (any `RCLike 𝕜`):

* `CartPoly.contDiff_eval`: `P.cartEval` is `C^k` for every `k` (including analytic order);
* `CartPoly.fderiv_eval_apply`: `fderiv 𝕜 cartEval P z v = ∑ i, (v.1 i * (P.cartDq i).cartEval z +
  v.2 i * (P.cartDp i).cartEval z)`;
* `CartPoly.fderiv_eval_q`, `CartPoly.fderiv_eval_p`: the coordinate directions.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

theorem getD_set_of_ne_zero (a : List ℕ) (i v k : ℕ) (h : a.getD i 0 ≠ 0) :
    (a.set i v).getD k 0 = if k = i then v else a.getD k 0 := by
  have hi : i < a.length := by
    by_contra hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
    exact h rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hk : k = i
  · subst hk; simp [hi]
  · simp [hk, Ne.symm hk, List.getD_eq_getElem?_getD]

namespace CartMonoK

variable {K : Type} [CertCoeff K]

/-- Formal derivative of a monomial in `q_i`. -/
def cartMonoDq (i : ℕ) (m : CartMonoK K) : List (CartMonoK K) :=
  if m.a.getD i 0 = 0 then [] else
    [⟨m.a.set i (m.a.getD i 0 - 1), m.b, m.c * (m.a.getD i 0 : K)⟩]

/-- Formal derivative of a monomial in `p_i`. -/
def cartMonoDp (i : ℕ) (m : CartMonoK K) : List (CartMonoK K) :=
  if m.b.getD i 0 = 0 then [] else
    [⟨m.a, m.b.set i (m.b.getD i 0 - 1), m.c * (m.b.getD i 0 : K)⟩]

end CartMonoK

namespace CartPoly

variable {K : Type} [CertCoeff K]

/-- Formal partial derivative in `q_i`. -/
def cartDq (i : ℕ) (P : CartPolyK K) : CartPolyK K := P.flatMap (CartMonoK.cartMonoDq i)

/-- Formal partial derivative in `p_i`. -/
def cartDp (i : ℕ) (P : CartPolyK K) : CartPolyK K := P.flatMap (CartMonoK.cartMonoDp i)

@[simp] theorem cartDq_nil (i : ℕ) : cartDq i ([] : CartPolyK K) = [] := rfl
@[simp] theorem cartDp_nil (i : ℕ) : cartDp i ([] : CartPolyK K) = [] := rfl
theorem cartDq_cons (i : ℕ) (m : CartMonoK K) (P : CartPolyK K) : cartDq i (m :: P) =
    CartMonoK.cartMonoDq
  i m ++ cartDq i P :=
  rfl
theorem cartDp_cons (i : ℕ) (m : CartMonoK K) (P : CartPolyK K) : cartDp i (m :: P) =
    CartMonoK.cartMonoDp
  i m ++ cartDp i P :=
  rfl

variable {R : Type*} [CommRing R] [Algebra K R] {n : ℕ}

/-- Evaluation of the formal `q`-derivative of a monomial. -/
theorem cartEval_dq_mono (i : Fin n) (m : CartMonoK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (CartMonoK.cartMonoDq i m) z = algebraMap K R m.c * (m.a.getD i 0 : R) *
      (z.1 i ^ (m.a.getD i 0 - 1) * z.2 i ^ m.b.getD i 0) *
      ∏ k ∈ Finset.univ.erase i, (z.1 k ^ m.a.getD k 0 * z.2 k ^ m.b.getD k 0) := by
  unfold CartMonoK.cartMonoDq
  by_cases h : m.a.getD i 0 = 0
  · simp only [h, ↓reduceIte, cartEval_nil]; simp
  · have hprod : ∏ k ∈ Finset.univ.erase i,
        (z.1 k ^ (m.a.set i (m.a.getD i 0 - 1)).getD k 0 * z.2 k ^ (m.b).getD k 0) =
        ∏ k ∈ Finset.univ.erase i, (z.1 k ^ m.a.getD k 0 * z.2 k ^ m.b.getD k 0) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      rw [getD_set_of_ne_zero _ _ _ _ h]
      simp only [hk', ite_false]
    simp only [h, ↓reduceIte]
    simp only [cartEval_cons, cartEval_nil, add_zero, CartMonoK.cartMonoEval, CartMonoK.powProd,
      map_mul,
      map_natCast]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hprod,
      getD_set_of_ne_zero _ _ _ _ h]
    simp only [ite_true]
    ring

/-- Evaluation of the formal `p`-derivative of a monomial. -/
theorem cartEval_dp_mono (i : Fin n) (m : CartMonoK K) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (CartMonoK.cartMonoDp i m) z = algebraMap K R m.c * (m.b.getD i 0 : R) *
      (z.1 i ^ m.a.getD i 0 * z.2 i ^ (m.b.getD i 0 - 1)) *
      ∏ k ∈ Finset.univ.erase i, (z.1 k ^ m.a.getD k 0 * z.2 k ^ m.b.getD k 0) := by
  unfold CartMonoK.cartMonoDp
  by_cases h : m.b.getD i 0 = 0
  · simp only [h, ↓reduceIte, cartEval_nil]; simp
  · have hprod : ∏ k ∈ Finset.univ.erase i,
        (z.1 k ^ (m.a).getD k 0 * z.2 k ^ (m.b.set i (m.b.getD i 0 - 1)).getD k 0) =
        ∏ k ∈ Finset.univ.erase i, (z.1 k ^ m.a.getD k 0 * z.2 k ^ m.b.getD k 0) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : (k : ℕ) ≠ i := fun e => (Finset.mem_erase.1 hk).1 (Fin.ext e)
      rw [getD_set_of_ne_zero _ _ _ _ h]
      simp only [hk', ite_false]
    simp only [h, ↓reduceIte]
    simp only [cartEval_cons, cartEval_nil, add_zero, CartMonoK.cartMonoEval, CartMonoK.powProd,
      map_mul,
      map_natCast]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hprod,
      getD_set_of_ne_zero _ _ _ _ h]
    simp only [ite_true]
    ring

end CartPoly

namespace CartPoly

variable {K : Type} [CertCoeff K] {𝕜 : Type*} [RCLike 𝕜] [Algebra K 𝕜] {n : ℕ}

theorem contDiff_eval_mono (m : CartMonoK K) (k : WithTop ℕ∞) :
    ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => m.cartMonoEval z) := by
  unfold CartMonoK.cartMonoEval CartMonoK.powProd
  refine contDiff_const.mul (contDiff_prod fun i _ => ?_)
  have h1 : ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => z.1 i) :=
    contDiff_pi.1 contDiff_fst i
  have h2 : ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => z.2 i) :=
    contDiff_pi.1 contDiff_snd i
  exact (h1.pow _).mul (h2.pow _)

/-- `P.cartEval` is smooth of every order. -/
theorem contDiff_eval (P : CartPolyK K) (k : WithTop ℕ∞) :
    ContDiff 𝕜 k (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z) := by
  induction P with
  | nil => simpa using contDiff_const
  | cons m P ih =>
    have : (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval (m :: P) z) =
        fun z => m.cartMonoEval z + cartEval P z := funext fun z => cartEval_cons m P z
    rw [this]
    exact (contDiff_eval_mono m k).add ih

/-- The directional derivative formula for one monomial, along a line. -/
theorem hasDerivAt_eval_mono (m : CartMonoK K) (z v : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    HasDerivAt (fun t : 𝕜 => m.cartMonoEval (z + t • v))
      (∑ i : Fin n, (v.1 i * cartEval (CartMonoK.cartMonoDq i m) z + v.2 i * cartEval
        (CartMonoK.cartMonoDp i m) z)) 0 := by
  have hg : ∀ i : Fin n, HasDerivAt
      (fun t : 𝕜 => (z.1 i + t * v.1 i) ^ m.a.getD i 0 * (z.2 i + t * v.2 i) ^ m.b.getD i 0)
      ((m.a.getD i 0 : 𝕜) * z.1 i ^ (m.a.getD i 0 - 1) * v.1 i * z.2 i ^ m.b.getD i 0 +
        z.1 i ^ m.a.getD i 0 * ((m.b.getD i 0 : 𝕜) * z.2 i ^ (m.b.getD i 0 - 1) * v.2 i)) 0 := by
    intro i
    have h1 : HasDerivAt (fun t : 𝕜 => z.1 i + t * v.1 i) (v.1 i) 0 := by
      exact HasDerivAt.congr_deriv (HasDerivAt.const_add (z.1 i)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : 𝕜)) (v.1 i))) (one_mul _)
    have h2 : HasDerivAt (fun t : 𝕜 => z.2 i + t * v.2 i) (v.2 i) 0 := by
      exact HasDerivAt.congr_deriv (HasDerivAt.const_add (z.2 i)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : 𝕜)) (v.2 i))) (one_mul _)
    exact HasDerivAt.congr_deriv (HasDerivAt.mul (HasDerivAt.pow h1 (m.a.getD i 0))
      (HasDerivAt.pow h2 (m.b.getD i 0))) (by simp)
  have hp := (HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : 𝕜))
    (fun i _ => hg i)).const_mul (algebraMap K 𝕜 m.c)
  have hfun : (fun t : 𝕜 => m.cartMonoEval (z + t • v)) = fun t : 𝕜 => algebraMap K 𝕜 m.c *
      ∏ i : Fin n, ((z.1 i + t * v.1 i) ^ m.a.getD i 0 * (z.2 i + t * v.2 i) ^ m.b.getD i 0) := by
    funext t
    simp [CartMonoK.cartMonoEval, CartMonoK.powProd]
  rw [hfun]
  convert hp using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cartEval_dq_mono, cartEval_dp_mono]
  simp only [smul_eq_mul, zero_mul, add_zero]
  ring

theorem hasDerivAt_eval (P : CartPolyK K) (z v : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    HasDerivAt (fun t : 𝕜 => cartEval P (z + t • v))
      (∑ i : Fin n, (v.1 i * cartEval (cartDq i P) z + v.2 i * cartEval (cartDp i P) z)) 0 := by
  induction P with
  | nil => simpa using hasDerivAt_const (0 : 𝕜) (0 : 𝕜)
  | cons m P ih =>
    have hfun : (fun t : 𝕜 => cartEval (m :: P) (z + t • v)) =
        fun t : 𝕜 => m.cartMonoEval (z + t • v) + cartEval P (z + t • v) := funext fun t =>
          cartEval_cons _ _ _
    rw [hfun]
    refine HasDerivAt.congr_deriv (HasDerivAt.add (hasDerivAt_eval_mono m z v) ih) ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cartDq_cons, cartDp_cons, show ∀ A B : CartPolyK K, cartEval (A ++ B) z = cartEval A z +
      cartEval B z from
      fun A B => cartEval_add A B z, show ∀ A B : CartPolyK K, cartEval (A ++ B) z = cartEval A z +
        cartEval B z from
      fun A B => cartEval_add A B z]
    ring

/-- The general derivative formula. -/
theorem fderiv_eval_apply (P : CartPolyK K) (z v : (Fin n → 𝕜) × (Fin n → 𝕜)) :
    fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z) z v =
      ∑ i : Fin n, (v.1 i * cartEval (cartDq i P) z + v.2 i * cartEval (cartDp i P) z) := by
  have hd : DifferentiableAt 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z) z :=
    ((contDiff_eval P 1).differentiable one_ne_zero).differentiableAt
  have hl : HasDerivAt (fun t : 𝕜 => z + t • v) v 0 := by
    exact HasDerivAt.congr_deriv (HasDerivAt.const_add z
      (HasDerivAt.smul_const (hasDerivAt_id (0 : 𝕜)) v)) (one_smul _ _)
  have hd' : HasFDerivAt (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z)
      (fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z) z) (z + (0 : 𝕜) • v) := by
    simpa using hd.hasFDerivAt
  have h2 := hd'.comp_hasDerivAt (0 : 𝕜) hl
  exact ((hasDerivAt_eval P z v).unique h2).symm

theorem fderiv_eval_q (P : CartPolyK K) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (i : Fin n) :
    fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z) z (Pi.single i 1, 0) =
      cartEval (cartDq i P) z := by
  rw [fderiv_eval_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

theorem fderiv_eval_p (P : CartPolyK K) (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (i : Fin n) :
    fderiv 𝕜 (fun z : (Fin n → 𝕜) × (Fin n → 𝕜) => cartEval P z) z (0, Pi.single i 1) =
      cartEval (cartDp i P) z := by
  rw [fderiv_eval_apply, Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

end CartPoly

end KAM.EffectiveStability
