/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Bound

/-!
# Cartesian polynomials: finite Lie sums and action substitution (track B, B2-STEP)

* `CartPoly.cartLieSum χ H L = ∑_{j < L} (1/j!) ad_χ^j H` as a `CartPoly`, with the evaluation
  lemmas `cartEval_lieSum` (any `ℚ`-algebra) and `cartEval_lieSum_complex` (the repo's
  `KAM.Canonical.adPow`);
* `CartPoly.cartActSubst Nact`: the substitution `q_i ↦ I_i = (q_i² + p_i²)/2` in a polynomial
  `Nact` that involves the `q`-variables only (`cartActOnly Nact = true`), with
  `cartEval_actSubst_real : (cartActSubst Nact).cartEval z = Nact.cartEval (oscAct z, 0)`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

namespace CartPoly

/-! ### Finite Lie sums -/

/-- The finite Lie sum `∑_{j < L} (1/j!) ad_χ^j H`. -/
def cartLieSum (χ H : CartPoly) (L : ℕ) : CartPoly :=
  (List.range L).flatMap fun j => cartSmul (1 / (j.factorial : ℚ)) (cartAdPow χ j H)

variable {R : Type*} [CommRing R] [Algebra ℚ R] {n : ℕ}

theorem cartLieSum_succ (χ H : CartPoly) (L : ℕ) :
    cartLieSum χ H (L + 1) =
      cartLieSum χ H L ++ cartSmul (1 / (L.factorial : ℚ)) (cartAdPow χ L H) := by
  simp [cartLieSum, List.range_succ]

theorem cartEval_lieSum (χ H : CartPoly) (L : ℕ) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartLieSum χ H L) z =
      ∑ j ∈ Finset.range L, algebraMap ℚ R (1 / (j.factorial : ℚ)) *
        cartEval (cartAdPow χ j H) z := by
  induction L with
  | zero => simp [cartLieSum]
  | succ L ih =>
    rw [cartLieSum_succ, ← cartAdd, cartEval_add, ih, cartEval_smul, Finset.sum_range_succ]

theorem cartFits_lieSum {χ H : CartPoly} (hχ : CartFits n χ) (hH : CartFits n H) (L : ℕ) :
    CartFits n (cartLieSum χ H L) :=
  cartFits_flatMap fun j _ => cartFits_smul _ (cartFits_adPow hχ hH j)

/-- The finite Lie sum evaluates, over `ℂ`, to `∑ (j!)⁻¹ ad_χ^j H`. -/
theorem cartEval_lieSum_complex (χ H : CartPoly) (hχ : CartFits n χ) (hH : CartFits n H)
    (L : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    cartEval (cartLieSum χ H L) z =
      ∑ j ∈ Finset.range L, ((j.factorial : ℂ)⁻¹) *
        KAM.Canonical.adPow (fun z => cartEval χ z) j (fun z => cartEval H z) z := by
  rw [cartEval_lieSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← congrFun (cartEval_adPow_complex χ H hχ hH j) z, eq_ratCast (algebraMap ℚ ℂ)]
  simp

/-! ### Action substitution -/

/-- Powers of a polynomial. -/
def cartPow (P : CartPoly) : ℕ → CartPoly
  | 0 => cartConst 1
  | k + 1 => cartMul P (cartPow P k)

theorem cartEval_pow (P : CartPoly) (k : ℕ) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartPow P k) z = cartEval P z ^ k := by
  induction k with
  | zero => simp [cartPow, cartEval_const]
  | succ k ih => rw [cartPow, cartEval_mul, ih, pow_succ']

/-- The product `∏_{k < L} (action k)^(a k)` as a polynomial. -/
def cartActProd (a : List ℕ) : ℕ → CartPoly
  | 0 => cartConst 1
  | L + 1 => cartMul (cartActProd a L) (cartPow (cartAction L) (a.getD L 0))

theorem cartEval_actProd (a : List ℕ) (L : ℕ) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartActProd a L) z =
      ∏ k ∈ Finset.range L, cartEval (cartAction k) z ^ a.getD k 0 := by
  induction L with
  | zero => simp [cartActProd, cartEval_const]
  | succ L ih => rw [cartActProd, cartEval_mul, ih, cartEval_pow, Finset.prod_range_succ]

/-- Substitution `q_i ↦ action i` in a polynomial (meaningful when it involves `q` only). -/
def cartActSubst (Nact : CartPoly) : CartPoly :=
  Nact.flatMap fun m => cartSmul m.c (cartActProd m.a m.a.length)

/-- Checkable: every monomial has all `p`-exponents zero. -/
def cartActOnly (Nact : CartPoly) : Bool := Nact.all fun m => m.b.all fun e => e == 0

theorem cartGetD_eq_zero_of_all {b : List ℕ} (h : b.all fun e => e == 0) (k : ℕ) :
    b.getD k 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : b[k]? with
  | none => rfl
  | some e =>
    have hmem : e ∈ b := List.mem_of_getElem? hk
    have := List.all_eq_true.1 h e hmem
    simpa using this

theorem getD_b_of_actOnly {Nact : CartPoly} (h : cartActOnly Nact = true) {m : CartMono}
    (hm : m ∈ Nact) (k : ℕ) : m.b.getD k 0 = 0 :=
  cartGetD_eq_zero_of_all (List.all_eq_true.1 h m hm) k

theorem prod_range_eq_fin {M : Type*} [CommMonoid M] (f : ℕ → M) (L n : ℕ)
    (h : ∀ k, n ≤ k ∨ L ≤ k → f k = 1) : ∏ k ∈ Finset.range L, f k = ∏ i : Fin n, f i := by
  rw [← Finset.prod_range f]
  have h1 : ∏ k ∈ Finset.range L, f k = ∏ k ∈ Finset.range (L + n), f k :=
    Finset.prod_subset (Finset.range_mono (Nat.le_add_right _ _)) fun i _ hni =>
      h i (Or.inr (by simpa using hni))
  have h2 : ∏ k ∈ Finset.range n, f k = ∏ k ∈ Finset.range (L + n), f k :=
    Finset.prod_subset (Finset.range_mono (Nat.le_add_left _ _)) fun i _ hni =>
      h i (Or.inl (by simpa using hni))
  rw [h1, h2]

theorem cartEval_actSubst_mono (m : CartMono) (hb : ∀ k, m.b.getD k 0 = 0)
    (ha : ∀ k, n ≤ k → m.a.getD k 0 = 0) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartSmul m.c (cartActProd m.a m.a.length)) z =
      m.cartMonoEval
        ((fun i => algebraMap ℚ R (1 / 2) * (z.1 i ^ 2 + z.2 i ^ 2), 0) :
          (Fin n → R) × (Fin n → R)) := by
  rw [cartEval_smul, cartEval_actProd]
  unfold CartMono.cartMonoEval CartMono.powProd
  congr 1
  rw [prod_range_eq_fin _ _ n (fun k hk => ?_)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [cartEval_action_eq, hb, pow_zero, mul_one]
  · have : m.a.getD k 0 = 0 := by
      rcases hk with hk | hk
      · exact ha k hk
      · exact getD_eq_zero_of_length_le _ _ hk
    rw [this, pow_zero]

/-- Evaluation of the action substitution, in any `ℚ`-algebra. -/
theorem cartEval_actSubst (Nact : CartPoly) (hN : CartFits n Nact)
    (hA : cartActOnly Nact = true) (z : (Fin n → R) × (Fin n → R)) :
    cartEval (cartActSubst Nact) z =
      cartEval Nact
        ((fun i => algebraMap ℚ R (1 / 2) * (z.1 i ^ 2 + z.2 i ^ 2), 0) :
          (Fin n → R) × (Fin n → R)) := by
  induction Nact with
  | nil => simp [cartActSubst]
  | cons m Nact ih =>
    have hN' : CartFits n Nact := fun m' hm' => hN m' (List.mem_cons_of_mem _ hm')
    have hA' : cartActOnly Nact = true := by
      simp only [cartActOnly, List.all_cons, Bool.and_eq_true] at hA ⊢
      exact hA.2
    have hs : cartActSubst (m :: Nact) =
        cartSmul m.c (cartActProd m.a m.a.length) ++ cartActSubst Nact := by
      simp [cartActSubst]
    rw [hs, ← cartAdd, cartEval_add, cartEval_cons, ih hN' hA',
      cartEval_actSubst_mono m (getD_b_of_actOnly hA (List.mem_cons_self ..))
        (fun k hk => (hN m (List.mem_cons_self ..) k hk).1) z]

/-- Real version: `cartActSubst Nact` evaluates to `Nact` at the oscillator actions. -/
theorem cartEval_actSubst_real (Nact : CartPoly) (hN : CartFits n Nact)
    (hA : cartActOnly Nact = true) (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    cartEval (cartActSubst Nact) z =
      cartEval Nact
        ((fun i => KAM.Planetary.oscillatorAction z.2 z.1 i, 0) :
          (Fin n → ℝ) × (Fin n → ℝ)) := by
  rw [cartEval_actSubst Nact hN hA]
  congr 2
  funext i
  simp only [KAM.Planetary.oscillatorAction, eq_ratCast (algebraMap ℚ ℝ)]
  push_cast
  ring

end CartPoly

/-! ### Smoke test -/

section Test

open CartPoly

example : cartActOnly (cartQVar 0) = true := by decide +kernel
example : cartEqCheck (cartActSubst (cartQVar 0)) (cartAction 0) = true := by decide +kernel
example : cartEqCheck (cartLieSum [] (cartAction 0) 1) (cartAction 0) = true := by decide +kernel

end Test

end KAM.EffectiveStability
