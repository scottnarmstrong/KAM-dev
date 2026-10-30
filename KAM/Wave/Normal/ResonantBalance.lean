/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Normal.ActionCoeff
public import KAM.Wave.Normal.Nonresonance

/-!
# Balanced sign patterns for the resonant quartic terms (blueprint `bpW:w0n:AB`, `resavg`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built.

A quartic term `g_{ijkl} ∏ (z_{i_s} or z̄_{i_s})` of the complex expansion of `G` is indexed by
`(i, j, k, l)` and a sign pattern `e ∈ Bool⁴` (`true ↦ z`, `false ↦ z̄`, signs `boolSign`).
`signBalanced e i j k l` says that the plus-indices and the minus-indices agree as multisets
(as count equations). We prove:
* `signBalanced_of_resonant`: if `g_{ijkl} ≠ 0` and the divisor `∑ ±λ` vanishes then
  `signBalanced` holds (consumes `quartic_nonresonance`);
* `signBalanced_sum_zero`: `signBalanced` forces `∑ ± f(i_s) = 0` for every `f` (so the divisor
  and the phases cancel);
* `signBalanced_count`: the number of balanced patterns is
  `4([i=j][k=l] + [i=k][j=l] + [i=l][j=k]) - 6[i=j=k=l]`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

def unitOfBool (b : Bool) : ℤˣ := if b then 1 else -1

theorem unitOfBool_val (b : Bool) : ((unitOfBool b : ℤˣ) : ℤ) = boolSign b := by
  cases b <;> simp [unitOfBool, boolSign]

theorem signSide_count {α : Type*} [DecidableEq α] (σ : Fin 4 → ℤˣ) (v : Fin 4 → α)
    (h : signSide σ v 1 = signSide σ v (-1)) (x : α) :
    ∑ t, (if v t = x then ((σ t : ℤˣ) : ℤ) else 0) = 0 := by
  have := congrArg (Multiset.count x) h
  simp only [signSide, Multiset.count_sum'] at this
  have key : ∀ t, (if v t = x then ((σ t : ℤˣ) : ℤ) else 0) =
      (Multiset.count x (if σ t = 1 then {v t} else 0) : ℤ)
        - (Multiset.count x (if σ t = -1 then {v t} else 0) : ℤ) := by
    intro t
    rcases Int.units_eq_one_or (σ t) with h1 | h1 <;> by_cases hv : v t = x
    · simp [h1, hv]
    · simp [h1, hv, Ne.symm hv]
    · simp [h1, hv]
    · simp [h1, hv, Ne.symm hv]
  simp only [key, Finset.sum_sub_distrib]
  rw [← Nat.cast_sum, ← Nat.cast_sum, this]; simp

def signBalanced {N : ℕ} (e : Bool × Bool × Bool × Bool) (i j k l : Fin N) : Prop :=
  ∀ x : Fin N, ((if i = x then boolSign e.1 else 0) + (if j = x then boolSign e.2.1 else 0)
    + (if k = x then boolSign e.2.2.1 else 0) + (if l = x then boolSign e.2.2.2 else 0)) = 0

theorem signBalanced_of_resonant {N : ℕ} (m : ℝ) (hm : 0 < m) (e : Bool × Bool × Bool × Bool)
    (i j k l : Fin N) (hg : gN i j k l ≠ 0)
    (hdiv : (boolSign e.1 : ℝ) * lamMode m hm i + (boolSign e.2.1 : ℝ) * lamMode m hm j
      + (boolSign e.2.2.1 : ℝ) * lamMode m hm k + (boolSign e.2.2.2 : ℝ) * lamMode m hm l = 0) :
    signBalanced e i j k l := by
  have hne := quartic_nonresonance m hm (fun t => modeIdx (![i, j, k, l] t))
    (by simpa [gN] using hg) ![unitOfBool e.1, unitOfBool e.2.1, unitOfBool e.2.2.1,
        unitOfBool e.2.2.2]
    (by
      simpa [Fin.sum_univ_four, unitOfBool_val, lamMode, Matrix.vecHead, Matrix.vecTail] using hdiv)
  intro x
  have := signSide_count _ _ hne (modeIdx x)
  simpa [Fin.sum_univ_four, unitOfBool_val, modeIdx_injective.eq_iff, Matrix.vecHead,
    Matrix.vecTail] using this


/-- The pairing condition equivalent to `signBalanced`. -/
def signBalancedCond {N : ℕ} (e : Bool × Bool × Bool × Bool) (i j k l : Fin N) : Prop :=
  match e with
  | (true, true, false, false) => (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  | (false, false, true, true) => (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  | (true, false, true, false) => (i = j ∧ k = l) ∨ (i = l ∧ k = j)
  | (false, true, false, true) => (i = j ∧ k = l) ∨ (i = l ∧ k = j)
  | (true, false, false, true) => (i = j ∧ l = k) ∨ (i = k ∧ l = j)
  | (false, true, true, false) => (i = j ∧ l = k) ∨ (i = k ∧ l = j)
  | _ => False

theorem signBalanced_iff {N : ℕ} (e : Bool × Bool × Bool × Bool) (i j k l : Fin N) :
    signBalanced e i j k l ↔ signBalancedCond e i j k l := by
  obtain ⟨e1, e2, e3, e4⟩ := e
  unfold signBalanced
  cases e1 <;> cases e2 <;> cases e3 <;> cases e4 <;> simp only [signBalancedCond,
      boolSign] <;> constructor <;>
    intro h <;> first
    | (exact fun x => by grind)
    | (have h1 := h i; have h2 := h j; have h3 := h k; have h4 := h l; grind)


open Classical in
theorem signBalanced_count {N : ℕ} (i j k l : Fin N) :
    ∑ e : Bool × Bool × Bool × Bool, (if signBalanced e i j k l then (1 : ℝ) else 0) =
      4 * ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0)
        + (if i = l ∧ j = k then 1 else 0)) - 6 * (if i = j ∧ j = k ∧ k = l then 1 else 0) := by
  simp only [signBalanced_iff, Fintype.sum_prod_type, Fintype.sum_bool, signBalancedCond]
  split_ifs <;> first | (exfalso; grind) | norm_num


theorem signBalanced_sum_zero {N : ℕ} (e : Bool × Bool × Bool × Bool) (i j k l : Fin N)
    (h : signBalanced e i j k l) (f : Fin N → ℝ) :
    (boolSign e.1 : ℝ) * f i + (boolSign e.2.1 : ℝ) * f j + (boolSign e.2.2.1 : ℝ) * f k
      + (boolSign e.2.2.2 : ℝ) * f l = 0 := by
  have h0 : ∑ x, f x * (((if i = x then boolSign e.1 else 0) + (if j = x then boolSign e.2.1 else 0)
      + (if k = x then boolSign e.2.2.1 else 0) + (if l =
          x then boolSign e.2.2.2 else 0) : ℤ) : ℝ) = 0 :=
    Finset.sum_eq_zero fun x _ => by rw [h x]; simp
  push_cast at h0
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at h0
  linarith



end KAM.Wave

end
