/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Trig.Trunc

/-!
# Scaled trigonometric models (T2-CONF, N3)

`TP`: a trigonometric polynomial with integer mantissas `d` on the square layout of half-width `C`
(row stride `S`, shared by a computation), parity `par` and ONE binary scale `e`:
`TP.eval S x φ = 2^(-e) · evalK (Layout.key C S) par d φ`.

* `TP.ok S x`: zero padding, full length and the symmetry of its parity (decidable, linear);
* `TP.mul`, `TP.eval_mul`: the exact product (scales add, slot lists convolve), sign
  `psgn (p ∧ q)`; the second factor must satisfy `TP.ok`;
* `TP.abs_eval_le`, `TP.abs_pderiv_eval_le`, `TP.lowB_le_eval`: sup, derivative and positivity
  bounds from the mantissas;
* `TP.deriv`, `TP.pderiv_eval`: the partial derivative is again a `TP` (parity flip);
* `TP.trunc`, `TP.c1Close_trunc`: truncation to a smaller box with rounding by `s` bits (the scale
  becomes `e - s`), as a `C1Close` statement with the computed errors scaled by `2^(-e)`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open KAM.Certificate

/-- A scaled trigonometric polynomial: half-width `C`, parity, scale exponent `e`, mantissas. -/
structure TP where
  C : ℕ
  par : Bool
  e : ℤ
  d : List ℤ

namespace TP

/-- `2^(-e) Σ_i d_i trig_par (key i · φ)`. -/
noncomputable def eval (S : ℕ) (x : TP) (φ : Fin 2 → ℝ) : ℝ :=
  (2 : ℝ) ^ (-x.e) * evalK (Layout.key x.C S) x.par x.d φ

/-- Zero padding, full length and symmetry for the parity. -/
def ok (S : ℕ) (x : TP) : Bool :=
  colsOk x.C S x.d && x.d.length == Layout.len x.C S && symOk x.par x.d

theorem ok_spec {S : ℕ} {x : TP} (h : x.ok S = true) :
    colsOk x.C S x.d = true ∧ x.d.length = Layout.len x.C S ∧ symOk x.par x.d = true := by
  simp only [ok, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The exact product (without the sign `psgn (p ∧ q)`, see `eval_mul`). -/
def mul (x y : TP) : TP := ⟨x.C + y.C, xor x.par y.par, x.e + y.e, listConv x.d y.d⟩

theorem two_zpow_neg_add (a b : ℤ) : (2 : ℝ) ^ (-(a + b)) = (2 : ℝ) ^ (-a) * (2 : ℝ) ^ (-b) := by
  rw [neg_add, zpow_add₀ (by norm_num)]

/-- **The product of scaled models.** -/
theorem eval_mul {S : ℕ} {x y : TP} (hS : 2 * (x.C + y.C) < S) (hx : colsOk x.C S x.d = true)
    (hy : y.ok S = true) (φ : Fin 2 → ℝ) :
    x.eval S φ * y.eval S φ = (psgn (x.par && y.par) : ℝ) * (mul x y).eval S φ := by
  obtain ⟨hyc, hyl, hys⟩ := ok_spec hy
  have := evalK_mul (p := x.par) hS hx hyc hyl hys φ
  simp only [eval, mul, two_zpow_neg_add]
  rw [show (2 : ℝ) ^ (-x.e) * evalK (Layout.key x.C S) x.par x.d φ *
      ((2 : ℝ) ^ (-y.e) * evalK (Layout.key y.C S) y.par y.d φ) =
      (2 : ℝ) ^ (-x.e) * (2 : ℝ) ^ (-y.e) *
        (evalK (Layout.key x.C S) x.par x.d φ * evalK (Layout.key y.C S) y.par y.d φ) by ring,
    this]
  ring

theorem differentiable_eval (S : ℕ) (x : TP) : Differentiable ℝ (x.eval S) :=
  (differentiable_evalK _ _ _).const_mul _

theorem abs_eval_le (S : ℕ) (x : TP) (φ : Fin 2 → ℝ) :
    |x.eval S φ| ≤ (2 : ℝ) ^ (-x.e) * (l1 x.d : ℝ) := by
  rw [eval, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_evalK_le _ _ _ _) (by positivity)

/-- The partial derivative `∂_a` as a scaled model. -/
def deriv (S : ℕ) (a : Fin 2) (x : TP) : TP :=
  ⟨x.C, !x.par, x.e, dlist (Layout.key x.C S) a x.par x.d⟩

theorem pderiv_eval (S : ℕ) (x : TP) (φ : Fin 2 → ℝ) (a : Fin 2) :
    pderiv (x.eval S) φ a = (deriv S a x).eval S φ := by
  rw [show x.eval S = fun φ => (2 : ℝ) ^ (-x.e) * evalK (Layout.key x.C S) x.par x.d φ from rfl,
    C1Close.pderiv_const_mul (differentiable_evalK _ _ _), pderiv_evalK]
  rfl

theorem abs_pderiv_eval_le (S : ℕ) (x : TP) (φ : Fin 2 → ℝ) (a : Fin 2) :
    |pderiv (x.eval S) φ a| ≤ (2 : ℝ) ^ (-x.e) * (wl1 (Layout.key x.C S) a x.d : ℝ) := by
  rw [pderiv_eval]
  refine (abs_eval_le S _ φ).trans ?_
  simp only [deriv]
  rw [l1_dlist]

theorem lowB_le_eval (S : ℕ) (x : TP) (hp : x.par = false) (φ : Fin 2 → ℝ) :
    (2 : ℝ) ^ (-x.e) * (lowB (Layout.key x.C S) x.d : ℝ) ≤ x.eval S φ := by
  rw [eval, hp]
  exact mul_le_mul_of_nonneg_left (lowB_le_evalK _ _ _) (by positivity)

/-- Truncate to the box of half-width `C'` (mask `keep`) and round by `s` bits. -/
def trunc (S C' s : ℕ) (keep : ℤ × ℤ → Bool) (x : TP) : TP :=
  ⟨C', x.par, x.e - s, truncRound x.C C' S s keep x.d⟩

/-- The computed slotwise error of `trunc`, on the layout of `x`. -/
def truncErr (S C' s : ℕ) (keep : ℤ × ℤ → Bool) (x : TP) : List ℤ :=
  lsub x.d (embed x.C C' S ((truncRound x.C C' S s keep x.d).map ((2 ^ s : ℤ) * ·)))

/-- **Truncation and rounding of a scaled model**, as a `C1Close` statement: the errors are
`2^(-e)` times the computed `ℓ¹` and weighted norms of `truncErr`. -/
theorem c1Close_trunc {S C' s : ℕ} {keep : ℤ × ℤ → Bool} {x : TP} (hC : C' ≤ x.C)
    (hS : x.C + C' < S) {e₁ : ℝ}
    (h₁ : ∀ a, (wl1 (Layout.key x.C S) a (truncErr S C' s keep x) : ℝ) ≤ e₁) :
    C1Close (x.eval S) ((trunc S C' s keep x).eval S)
      ((2 : ℝ) ^ (-x.e) * (l1 (truncErr S C' s keep x) : ℝ)) ((2 : ℝ) ^ (-x.e) * e₁) := by
  have h := (c1Close_truncRound hC hS x.par s keep x.d h₁).const_mul ((2 : ℝ) ^ (-x.e))
  rw [abs_of_pos (by positivity)] at h
  have he : (fun φ => (2 : ℝ) ^ (-x.e) * (((2 ^ s : ℤ) : ℝ) *
      evalK (Layout.key C' S) x.par (truncRound x.C C' S s keep x.d) φ)) =
      (trunc S C' s keep x).eval S := by
    funext φ
    simp only [eval, trunc]
    rw [show -(x.e - (s : ℤ)) = -x.e + s by ring, zpow_add₀ (by norm_num), zpow_natCast]
    push_cast
    ring
  rw [he] at h
  exact h

end TP

end KAM.EffectiveStability.Tube

end
