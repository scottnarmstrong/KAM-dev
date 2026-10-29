/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Interface
public import KAM.Strip.FourierSeries
public import KAM.Diophantine.SolverAlgebra

/-!
# Exact finite Fourier data

`CertPoly α` is a finite list of Fourier terms `(k, c)` with backend complex coefficients;
`CertRealPoly α` is real data on the half lattice. Their denotations `eval` are law-free; the
laws `[LawfulCertArith α]` enter only for `toPoly` (backend zero and conjugation).
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM CertArith

/-- A Fourier index, stored as a list of length `n` (kernel-friendly lexicographic order). -/
abbrev CertKey : Type := List ℤ

/-- The index `Fin n → ℤ` denoted by a key (missing entries are `0`). -/
def certKeyFun (n : ℕ) (k : CertKey) : Fin n → ℤ := fun i => k.getD i.val 0

/-- A finite complex Fourier polynomial (duplicates allowed; optimized algorithms validate and
canonicalize key lengths and order before relying on them). -/
structure CertPoly (α : Type) where
  terms : List (CertKey × CC α)

/-- The denoted trigonometric polynomial `Σ c_k e^{2πi k·θ}` (law-free). -/
def CertPoly.eval {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) : ℂ :=
  (P.terms.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum

/-- Its coefficient family (sum over repeated keys; zero off the support). -/
def CertPoly.coeff {α : Type} [CertArith α] (n : ℕ) (P : CertPoly α) (k : Fin n → ℤ) : ℂ :=
  ((P.terms.filter fun t => decide (certKeyFun n t.1 = k)).map fun t => t.2.toC).sum

section Helpers

variable {α : Type} [CertArith α]

/-- The coefficient as a sum of per-term contributions. -/
theorem CertPoly.coeff_eq_sum (n : ℕ) (P : CertPoly α) (k : Fin n → ℤ) :
    P.coeff n k =
      (P.terms.map fun t => if certKeyFun n t.1 = k then t.2.toC else 0).sum := by
  unfold CertPoly.coeff
  induction P.terms with
  | nil => simp
  | cons t L ih =>
    by_cases h : certKeyFun n t.1 = k <;> simp [List.filter_cons, h, ih]

/-- The Fourier series of a finite coefficient list is its finite sum. -/
theorem hasSum_list_coeff_mul_character (n : ℕ) (L : List (CertKey × CC α)) (θ : Fin n → ℂ) :
    HasSum (fun k : Fin n → ℤ =>
        (((L.filter fun t => decide (certKeyFun n t.1 = k)).map fun t => t.2.toC).sum) *
          character k θ)
      (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum := by
  induction L with
  | nil => simpa using hasSum_zero
  | cons t L ih =>
    have h1 := hasSum_ite_eq (certKeyFun n t.1) (t.2.toC * character (certKeyFun n t.1) θ)
    have h2 := h1.add ih
    rw [List.map_cons, List.sum_cons]
    convert h2 using 1
    funext k
    by_cases h : certKeyFun n t.1 = k
    · subst h; simp [List.filter_cons, add_mul]
    · have h' : k ≠ certKeyFun n t.1 := fun e => h e.symm
      simp [List.filter_cons, h, h']

/-- Bridge to the project's Fourier series (`KAM.fourierSum`). -/
theorem CertPoly.eval_eq_fourierSum (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) :
    P.eval n θ = fourierSum (P.coeff n) θ :=
  (hasSum_list_coeff_mul_character n P.terms θ).tsum_eq.symm

theorem character_add_int {n : ℕ} (k : Fin n → ℤ) (θ : Fin n → ℂ) (m : Fin n → ℤ) :
    character k (θ + fun i => (m i : ℂ)) = character k θ := by
  rw [character_add]
  have : character k (fun i => (m i : ℂ)) = 1 := by
    rw [character]
    have h : (2 * (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) * (m j : ℂ)) =
        ((∑ j, k j * m j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [h]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]

theorem differentiable_list_sum {n : ℕ} {ι : Type} (L : List ι) (f : ι → (Fin n → ℂ) → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) : Differentiable ℂ fun θ => (L.map fun i => f i θ).sum := by
  induction L with
  | nil => simpa using differentiable_const (0 : ℂ)
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf i).fun_add ih

theorem CertPoly.differentiable_eval (n : ℕ) (P : CertPoly α) : Differentiable ℂ (P.eval n) := by
  unfold CertPoly.eval
  exact differentiable_list_sum P.terms (fun t θ => t.2.toC * character (certKeyFun n t.1) θ)
    fun t => (differentiable_character _).const_mul _

theorem CertPoly.eval_add_int (n : ℕ) (P : CertPoly α) (θ : Fin n → ℂ) (k : Fin n → ℤ) :
    P.eval n (θ + fun i => (k i : ℂ)) = P.eval n θ := by
  simp only [CertPoly.eval, character_add_int]

end Helpers

/-- Real Fourier data on the half lattice: `a₀ + Σ_{(k, c) ∈ half} (c χ_k + c̄ χ_{-k})`. -/
structure CertRealPoly (α : Type) where
  zero : α
  half : List (CertKey × CC α)

/-- The denotation of real data, defined directly (law-free; no backend zero or conjugation). -/
def CertRealPoly.eval {α : Type} [CertArith α] (n : ℕ) (P : CertRealPoly α) (θ : Fin n → ℂ) :
    ℂ :=
  (val P.zero : ℂ) + (P.half.map fun t => t.2.toC * character (certKeyFun n t.1) θ +
    (starRingEnd ℂ) t.2.toC * character (-certKeyFun n t.1) θ).sum

section Real

variable {α : Type} [CertArith α]

theorem character_neg_ofReal {n : ℕ} (k : Fin n → ℤ) (x : Fin n → ℝ) :
    character (-k) (fun i => (x i : ℂ)) = (starRingEnd ℂ) (character k fun i => (x i : ℂ)) := by
  simp only [character]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_I, map_ofNat,
    map_intCast, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem im_list_sum_eq_zero {ι : Type} (L : List ι) (f : ι → ℂ) (h : ∀ i ∈ L, (f i).im = 0) :
    (L.map f).sum.im = 0 := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.sum_cons, Complex.add_im, h i (by simp),
      ih fun j hj => h j (by simp [hj]), add_zero]

/-- Reality is structural and law-free: each pair is `2 Re (c χ_k)` on reals. -/
theorem CertRealPoly.eval_real (n : ℕ) (P : CertRealPoly α) (x : Fin n → ℝ) :
    (P.eval n fun i => (x i : ℂ)).im = 0 := by
  unfold CertRealPoly.eval
  rw [Complex.add_im, Complex.ofReal_im, zero_add]
  refine im_list_sum_eq_zero _ _ fun t _ => ?_
  rw [character_neg_ofReal, ← map_mul, Complex.add_im]
  simp [Complex.conj_im]
  ring

theorem CertRealPoly.differentiable_eval (n : ℕ) (P : CertRealPoly α) :
    Differentiable ℂ (P.eval n) := by
  unfold CertRealPoly.eval
  refine (differentiable_const _).add ?_
  exact differentiable_list_sum P.half
    (fun t θ => t.2.toC * character (certKeyFun n t.1) θ +
      (starRingEnd ℂ) t.2.toC * character (-certKeyFun n t.1) θ)
    fun t => ((differentiable_character _).const_mul _).add
      ((differentiable_character _).const_mul _)

theorem CertRealPoly.eval_add_int (n : ℕ) (P : CertRealPoly α) (θ : Fin n → ℂ)
    (k : Fin n → ℤ) : P.eval n (θ + fun i => (k i : ℂ)) = P.eval n θ := by
  simp only [CertRealPoly.eval, character_add_int]

end Real

end KAM.Certificate
