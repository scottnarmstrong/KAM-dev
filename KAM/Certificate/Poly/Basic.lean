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
    by_cases h : certKeyFun n t.1 = k <;> simp [h, ih]

/-- The Fourier series of a finite coefficient list is its finite sum. -/
theorem hasSum_list_coeff_mul_character (n : ℕ) (L : List (CertKey × CC α)) (θ : Fin n → ℂ) :
    HasSum (fun k : Fin n → ℤ =>
        (((L.filter fun t => decide (certKeyFun n t.1 = k)).map fun t => t.2.toC).sum) *
          character k θ)
      (L.map fun t => t.2.toC * character (certKeyFun n t.1) θ).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
    have h1 := hasSum_ite_eq (certKeyFun n t.1) (t.2.toC * character (certKeyFun n t.1) θ)
    have h2 := h1.add ih
    rw [List.map_cons, List.sum_cons]
    convert h2 using 1
    funext k
    by_cases h : certKeyFun n t.1 = k
    · subst h; simp [add_mul]
    · have h' : k ≠ certKeyFun n t.1 := fun e => h e.symm
      simp [h, h']

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
  | nil => simp
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

section ToPoly

variable {α : Type} [CertArith α]

/-- The pair `(k, c)`, `(-k, c̄)` generated by a half-lattice term. -/
def certPair (t : CertKey × CC α) : List (CertKey × CC α) :=
  [t, (t.1.map Neg.neg, t.2.conj)]

/-- The full polynomial: the zero term (imaginary part `ofInt 0`), each half term and its
conjugate at `-k` (`CC.conj`, `List.map Neg.neg` on keys). -/
def CertRealPoly.toPoly (P : CertRealPoly α) : CertPoly α :=
  ⟨([], ⟨P.zero, ofInt 0⟩) :: P.half.flatMap certPair⟩

theorem certKeyFun_map_neg (n : ℕ) (k : CertKey) :
    certKeyFun n (k.map Neg.neg) = -certKeyFun n k := by
  funext i
  simp only [certKeyFun, List.getD_eq_getElem?_getD, List.getElem?_map, Pi.neg_apply]
  cases k[i.val]? <;> simp

theorem certKeyFun_nil (n : ℕ) : certKeyFun n [] = 0 := by
  funext i; simp [certKeyFun]

theorem list_sum_flatMap_pair {β ι : Type} (L : List β) (f : β → List ι) (g : ι → ℂ) :
    ((L.flatMap f).map g).sum = (L.map fun b => ((f b).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons b L ih => simp [List.flatMap_cons, ih]

/-- The explicit `toPoly` denotation (constant plus conjugate-pair sum); needs the laws. -/
theorem CertRealPoly.eval_toPoly [LawfulCertArith α] (n : ℕ) (P : CertRealPoly α)
    (θ : Fin n → ℂ) : P.toPoly.eval n θ = P.eval n θ := by
  unfold CertPoly.eval CertRealPoly.toPoly CertRealPoly.eval
  rw [List.map_cons, List.sum_cons, list_sum_flatMap_pair]
  have h0 : (⟨P.zero, ofInt 0⟩ : CC α).toC = (val P.zero : ℂ) := by
    simp [CC.toC, LawfulCertArith.val_ofInt, Complex.ext_iff]
  rw [h0, certKeyFun_nil]
  simp only [character, Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero,
    mul_zero, Complex.exp_zero, mul_one]
  refine congrArg (fun x : ℂ => (val P.zero : ℂ) + x) (congrArg List.sum
    (List.map_congr_left ?_))
  intro t _
  simp [certPair, CC.toC_conj, certKeyFun_map_neg]

theorem pair_coeff_symm {G : Type} [AddCommGroup G] [DecidableEq G] (a k : G) (c : ℂ) :
    ((if a = -k then c else 0) + if -a = -k then (starRingEnd ℂ) c else 0) =
      (starRingEnd ℂ) ((if a = k then c else 0) + if -a = k then (starRingEnd ℂ) c else 0) := by
  simp only [neg_eq_iff_eq_neg, neg_neg, map_add]
  split_ifs <;> simp [add_comm]

theorem CertRealPoly.conjugateSymmetric [LawfulCertArith α] (n : ℕ) (P : CertRealPoly α) :
    Fourier.ConjugateSymmetric (P.toPoly.coeff n) := by
  intro k
  unfold CertRealPoly.toPoly
  simp only [CertPoly.coeff_eq_sum]
  rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons,
    list_sum_flatMap_pair, list_sum_flatMap_pair, map_add, map_list_sum, List.map_map]
  have h0 : (⟨P.zero, ofInt 0⟩ : CC α).toC = (val P.zero : ℂ) := by
    simp [CC.toC, LawfulCertArith.val_ofInt, Complex.ext_iff]
  congr 1
  · simp only [certKeyFun_nil, h0]
    have e : (0 : Fin n → ℤ) = -k ↔ 0 = k := by rw [eq_comm, neg_eq_zero, eq_comm]
    by_cases hk : (0 : Fin n → ℤ) = k
    · subst hk
      simp [Complex.conj_ofReal]
    · simp [hk, mt e.mp hk]
  · refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    have e1 : (-certKeyFun n t.1 = -k) ↔ certKeyFun n t.1 = k := neg_inj
    have e2 : (-certKeyFun n t.1 = k) ↔ certKeyFun n t.1 = -k := neg_eq_iff_eq_neg
    simp only [certPair, certKeyFun_map_neg, CC.toC_conj, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
    exact pair_coeff_symm _ _ _

/-- Exact addition by list concatenation (no rounding, law-free). Coefficient merging with
rounding is a model operation (`CertModel.add`), whose error is paid in the strip-weighted
radius; a global bound for all complex `θ` would be false for nonzero modes (audit 2). -/
def CertPoly.add {α : Type} (P Q : CertPoly α) : CertPoly α := ⟨P.terms ++ Q.terms⟩

theorem CertPoly.eval_add (n : ℕ) (P Q : CertPoly α) (θ : Fin n → ℂ) :
    (P.add Q).eval n θ = P.eval n θ + Q.eval n θ := by
  simp [CertPoly.eval, CertPoly.add]

end ToPoly

end KAM.Certificate
