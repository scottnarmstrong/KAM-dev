/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Poly.Bracket

/-!
# Cartesian polynomials: computable sup bounds (track B, B2-POLY)

`CartPoly.cartSupBound P r s = ∑ |c| ∏ r_i^{a_i} s_i^{b_i}` (exact `ℚ`) majorizes `‖P.cartEval z‖`
  on
polydiscs `‖z.1 i‖ ≤ r_i`, `‖z.2 i‖ ≤ s_i` (for `P` fitting in `n` variables), over `ℝ` and `ℂ`;
the drift bound for a finite residual and the radius bridge for oscillator actions follow. The
file ends with kernel-evaluation smoke tests of `cartEqCheck`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

namespace CartPoly

/-- The majorant of a single monomial: `|c| ∏ r_k^{a_k} s_k^{b_k}`. -/
def cartMonoBound (m : CartMono) (r s : List ℚ) : ℚ :=
  |m.c| * ∏ k ∈ Finset.range (max m.a.length m.b.length),
    (r.getD k 0 ^ m.a.getD k 0 * s.getD k 0 ^ m.b.getD k 0)

/-- Computable majorant of `‖P.cartEval z‖` on the polydisc of radii `(r, s)`. -/
def cartSupBound (P : CartPoly) (r s : List ℚ) : ℚ := (P.map fun m => cartMonoBound m r s).sum

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem norm_algebraMap_rat (c : ℚ) : ‖algebraMap ℚ 𝕜 c‖ = |(c : ℝ)| := by
  rw [eq_ratCast (algebraMap ℚ 𝕜), ← RCLike.ofReal_ratCast, RCLike.norm_ofReal]

theorem prod_range_eq_univ (f : ℕ → ℝ) (L n : ℕ)
    (h : ∀ k, n ≤ k ∨ L ≤ k → f k = 1) :
    ∏ k ∈ Finset.range L, f k = ∏ i : Fin n, f i := by
  rw [← Finset.prod_range f]
  have h1 : ∏ k ∈ Finset.range L, f k = ∏ k ∈ Finset.range (L + n), f k :=
    Finset.prod_subset (Finset.range_mono (Nat.le_add_right _ _)) fun i hi hni =>
      h i (Or.inr (by simpa using hni))
  have h2 : ∏ k ∈ Finset.range n, f k = ∏ k ∈ Finset.range (L + n), f k :=
    Finset.prod_subset (Finset.range_mono (Nat.le_add_left _ _)) fun i hi hni =>
      h i (Or.inl (by simpa using hni))
  rw [h1, h2]

theorem norm_eval_mono_le (m : CartMono) (hm : ∀ k, n ≤ k → m.a.getD k 0 = 0 ∧ m.b.getD k 0 = 0)
    (r s : List ℚ) (z : (Fin n → 𝕜) × (Fin n → 𝕜))
    (hr : ∀ i : Fin n, ‖z.1 i‖ ≤ ((r.getD i 0 : ℚ) : ℝ))
    (hs : ∀ i : Fin n, ‖z.2 i‖ ≤ ((s.getD i 0 : ℚ) : ℝ)) :
    ‖m.cartMonoEval z‖ ≤ ((cartMonoBound m r s : ℚ) : ℝ) := by
  unfold CartMono.cartMonoEval CartMono.powProd cartMonoBound
  rw [norm_mul, norm_algebraMap_rat, Rat.cast_mul, Rat.cast_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [Rat.cast_prod]
  set f : ℕ → ℝ := fun k => (((r.getD k 0 ^ m.a.getD k 0 * s.getD k 0 ^ m.b.getD k 0 : ℚ)) : ℝ)
    with hf
  have hz : ∏ k ∈ Finset.range (max m.a.length m.b.length), f k = ∏ i : Fin n, f i := by
    refine prod_range_eq_univ f _ n fun k hk => ?_
    have h0 : m.a.getD k 0 = 0 ∧ m.b.getD k 0 = 0 := by
      rcases hk with hk | hk
      · exact hm k hk
      · exact ⟨getD_eq_zero_of_length_le _ _ (le_trans (le_max_left _ _) hk),
          getD_eq_zero_of_length_le _ _ (le_trans (le_max_right _ _) hk)⟩
    simp only [hf, h0.1, h0.2, pow_zero, mul_one, Rat.cast_one]
  rw [hz, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_mul, norm_pow, norm_pow]
  simp only [hf]
  push_cast
  have h1 := (norm_nonneg (z.1 i)).trans (hr i)
  have h2 := (norm_nonneg (z.2 i)).trans (hs i)
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hr i) _)
    (pow_le_pow_left₀ (norm_nonneg _) (hs i) _) (by positivity) (by positivity)

/-- `‖P.cartEval z‖ ≤ cartSupBound P r s` on the polydisc (`ℝ` and `ℂ`). -/
theorem norm_eval_le_supBound (P : CartPoly) (hP : CartFits n P) (r s : List ℚ)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜))
    (hr : ∀ i : Fin n, ‖z.1 i‖ ≤ ((r.getD i 0 : ℚ) : ℝ))
    (hs : ∀ i : Fin n, ‖z.2 i‖ ≤ ((s.getD i 0 : ℚ) : ℝ)) :
    ‖P.cartEval z‖ ≤ ((cartSupBound P r s : ℚ) : ℝ) := by
  induction P with
  | nil => simp [cartSupBound, cartEval]
  | cons m P ih =>
    have h1 := norm_eval_mono_le m (hP m (List.mem_cons_self ..)) r s z hr hs
    have h2 := ih fun m' hm' => hP m' (List.mem_cons_of_mem _ hm')
    have : cartSupBound (m :: P) r s = cartMonoBound m r s + cartSupBound P r s := by simp
      [cartSupBound]
    rw [this, Rat.cast_add, cartEval_cons]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- Real version of `norm_eval_le_supBound`. -/
theorem abs_eval_le_supBound (P : CartPoly) (hP : CartFits n P) (r s : List ℚ)
    (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hr : ∀ i : Fin n, |z.1 i| ≤ ((r.getD i 0 : ℚ) : ℝ))
    (hs : ∀ i : Fin n, |z.2 i| ≤ ((s.getD i 0 : ℚ) : ℝ)) :
    |P.cartEval z| ≤ ((cartSupBound P r s : ℚ) : ℝ) := by
  simpa using norm_eval_le_supBound (𝕜 := ℝ) P hP r s z (by simpa using hr) (by simpa using hs)

/-- The B1-E drift bound for a finite residual `P`:
`|q_j ∂_{p_j} P - p_j ∂_{q_j} P| ≤ cartSupBound (cartBracket (cartAction j) P) r r`. -/
theorem abs_actionBracket_le_supBound (P : CartPoly) (hP : CartFits n P) (j : Fin n) (r : List ℚ)
    (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hq : ∀ i : Fin n, |z.1 i| ≤ ((r.getD i 0 : ℚ) : ℝ))
    (hp : ∀ i : Fin n, |z.2 i| ≤ ((r.getD i 0 : ℚ) : ℝ)) :
    |z.1 j * cartEval (cartDp j P) z - z.2 j * cartEval (cartDq j P) z| ≤
      ((cartSupBound (cartBracket (cartAction j) P) r r : ℚ) : ℝ) := by
  rw [← cartEval_bracket_action]
  exact abs_eval_le_supBound _ (cartFits_bracket (cartFits_action j.2) hP) r r z hq hp

/-- Radius bridge: `I = (p² + q²)/2 ≤ b` and `2 b ≤ r²` give `|q| ≤ r` and `|p| ≤ r`. -/
theorem abs_le_of_action_le {q p b r : ℝ} (h : (p ^ 2 + q ^ 2) / 2 ≤ b) (hb : 2 * b ≤ r ^ 2)
    (hr : 0 ≤ r) : |q| ≤ r ∧ |p| ≤ r :=
  ⟨abs_le_of_sq_le_sq (by nlinarith [sq_nonneg p]) hr,
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg q]) hr⟩

/-- Vector form of the radius bridge for `KAM.Planetary.oscillatorAction`. -/
theorem abs_le_of_oscillatorAction_le (z : (Fin n → ℝ) × (Fin n → ℝ)) (b r : Fin n → ℝ)
    (i : Fin n) (h : KAM.Planetary.oscillatorAction z.2 z.1 i ≤ b i) (hb : 2 * b i ≤ r i ^ 2)
    (hr : 0 ≤ r i) : |z.1 i| ≤ r i ∧ |z.2 i| ≤ r i :=
  abs_le_of_action_le h hb hr

end CartPoly

/-! ### Smoke tests: kernel evaluation of the identity checker -/

section Test

open CartPoly

example : cartEqCheck (cartBracket (cartAction 0) (cartQVar 0)) (cartNeg (cartPVar 0)) = true := by
  decide +kernel
example : cartEqCheck (cartBracket (cartQVar 0) (cartPVar 0)) (cartConst 1) = true := by
  decide +kernel
example : cartEqCheck (cartBracket (cartAction 1) (cartPVar 1)) (cartQVar 1) = true := by
  decide +kernel
example : cartEqCheck
    (cartMul (cartAdd (cartQVar 0) (cartPVar 1)) (cartAdd (cartQVar 0) (cartPVar 1)))
    (cartAdd (cartAdd (cartMul (cartQVar 0) (cartQVar 0))
      (cartSmul 2 (cartMul (cartQVar 0) (cartPVar 1)))) (cartMul (cartPVar 1) (cartPVar 1)))
    = true := by decide +kernel
example : cartEqCheck (cartQVar 0) (cartPVar 0) = false := by decide +kernel

end Test

end KAM.EffectiveStability
