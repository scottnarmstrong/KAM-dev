/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Grouping a multi-index power series by degree

Blueprint-W `bpW:w1:holo-analytic-fd`, step `stepW:w1:hagroup` (package W1-ANALYTIC). This is
source-faithful infrastructure used by several nodes; the dependency graph is still being built.

For coefficients `c : (Fin n → ℕ) → F` we build the formal multilinear series
`KAM.Wave.degreeSeries c` on `Fin n → ℂ` with `p_m (h, …, h) = ∑_{|α| = m} h^α c_α`. The blueprint
uses a nondecreasing map `ι_α : Fin m → Fin n`; we use instead the sum over all words
`σ : Fin m → Fin n` weighted by the inverse of the number of words with the same multiplicity
vector `α`, which avoids the choice of `ι_α` (each `α` with `|α| = m` is realised by some word, so
the weights add up to `1`). The norm bound is
`‖p_m‖ ≤ #{α : |α| = m} · sup_{|α| = m} ‖c_α‖`, and
`#{α : |α| = m} = binom (m + n - 1, n - 1)` (stars and bars).
-/

@[expose] public noncomputable section

open Finset

namespace KAM.Wave

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The multiplicity vector of a word `σ : Fin m → Fin n`. -/
def wordCount {m : ℕ} (σ : Fin m → Fin n) : Fin n → ℕ :=
  fun i => (univ.filter fun l => σ l = i).card

/-- The number of words of length `m` with multiplicity vector `α`. -/
def wordFiberCard (m : ℕ) (α : Fin n → ℕ) : ℕ :=
  (univ.filter fun σ : Fin m → Fin n => wordCount σ = α).card

/-- The continuous `m`-linear map `(h₁, …, h_m) ↦ (∏ l, (h_l)_{σ l}) • e`. -/
def wordTerm {m : ℕ} (σ : Fin m → Fin n) (e : F) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) F :=
  ((ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).compContinuousLinearMap
    (fun l => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (σ l))).smulRight e

theorem wordTerm_apply {m : ℕ} (σ : Fin m → Fin n) (e : F) (h : Fin m → (Fin n → ℂ)) :
    wordTerm σ e h = (∏ l, h l (σ l)) • e := by
  simp [wordTerm, ContinuousMultilinearMap.smulRight_apply, List.prod_ofFn]

theorem norm_wordTerm_le {m : ℕ} (σ : Fin m → Fin n) (e : F) : ‖wordTerm σ e‖ ≤ ‖e‖ := by
  unfold wordTerm
  rw [ContinuousMultilinearMap.norm_smulRight]
  have h1 : ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ).compContinuousLinearMap
      (fun l => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (σ l))‖ ≤ 1 := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hp : ∀ l, ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (σ l)‖ ≤ 1 :=
      fun l => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
        simpa using norm_le_pi_norm x (σ l)
    have hn : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ m ℂ‖ ≤ 1 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · exact ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hm
    have hprod : ∏ l : Fin m, ‖ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ)
        (σ l)‖ ≤ 1 := Finset.prod_le_one₀ (fun l _ => norm_nonneg _) (fun l _ => hp l)
    exact (mul_le_mul hn hprod (Finset.prod_nonneg fun l _ => norm_nonneg _) zero_le_one).trans
      (by norm_num)
  calc _ ≤ 1 * ‖e‖ := by gcongr
    _ = ‖e‖ := one_mul _

/-- The degree-`m` part of the power series with coefficients `c`, as a formal multilinear
series. -/
def degreeSeries (c : (Fin n → ℕ) → F) : FormalMultilinearSeries ℂ (Fin n → ℂ) F :=
  fun m => ∑ σ : Fin m → Fin n,
    wordTerm σ (((wordFiberCard m (wordCount σ) : ℕ) : ℂ)⁻¹ • c (wordCount σ))


theorem sum_wordCount {m : ℕ} (σ : Fin m → Fin n) : ∑ i, wordCount σ i = m := by
  have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin m)))
    (t := (univ : Finset (Fin n)))
    (f := σ) (fun _ _ => mem_univ _)
  simpa [wordCount] using this.symm

/-- Every multiplicity vector `α` with `|α| = m` is the multiplicity vector of some word. -/
theorem exists_word_of_sum {m : ℕ} {α : Fin n → ℕ} (hα : ∑ i, α i = m) :
    ∃ σ : Fin m → Fin n, wordCount σ = α := by
  subst hα
  refine ⟨fun l => (finSigmaFinEquiv.symm l).1, ?_⟩
  funext i
  unfold wordCount
  have : (univ.filter fun l : Fin (∑ i, α i) => (finSigmaFinEquiv.symm l).1 = i).card =
      (univ.filter fun s : (j : Fin n) × Fin (α j) => s.1 = i).card := by
    refine Finset.card_bij (fun l _ => finSigmaFinEquiv.symm l) (fun l hl => by simpa using hl)
      (fun l _ l' _ h => finSigmaFinEquiv.symm.injective h) (fun s hs => ?_)
    exact ⟨finSigmaFinEquiv s, by simpa using hs, by simp⟩
  rw [this]
  have h2 : (univ.filter fun s : (j : Fin n) × Fin (α j) => s.1 = i) =
      univ.map ⟨fun k : Fin (α i) => (⟨i, k⟩ : (j : Fin n) × Fin (α j)), fun a b h => by
        simpa using h⟩ := by
    ext ⟨j, k⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro rfl; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩
      exact (Sigma.mk.inj_iff.mp hk').1.symm
  rw [h2]; simp

theorem prod_word {m : ℕ} (σ : Fin m → Fin n) (h : Fin n → ℂ) :
    ∏ l, h (σ l) = ∏ i, h i ^ wordCount σ i := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := (univ : Finset (Fin m)))
    (t := (univ : Finset (Fin n)))
    (g := σ) (fun _ _ => mem_univ _) (fun l => h (σ l))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => h i) (fun l hl => by rw [(Finset.mem_filter.mp hl).2])]
  simp [wordCount]


theorem wordFiberCard_pos {m : ℕ} {α : Fin n → ℕ} (hα : ∑ i, α i = m) : 0 < wordFiberCard m α := by
  obtain ⟨σ, hσ⟩ := exists_word_of_sum hα
  exact Finset.card_pos.mpr ⟨σ, by simpa using hσ⟩

/-- On the diagonal, the degree-`m` part is the sum of the monomials of degree `m`. -/
theorem degreeSeries_apply_diag (c : (Fin n → ℕ) → F) (m : ℕ) (h : Fin n → ℂ) :
    degreeSeries c m (fun _ => h) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple n m, (∏ i, h i ^ α i) • c α := by
  classical
  unfold degreeSeries
  rw [_root_.sum_apply]
  simp only [wordTerm_apply, prod_word]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset (Fin m → Fin n)))
    (t := Finset.Nat.antidiagonalTuple n m) (g := wordCount)
    (fun σ _ => Finset.Nat.mem_antidiagonalTuple.mpr (sum_wordCount σ))]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hpos := wordFiberCard_pos (Finset.Nat.mem_antidiagonalTuple.mp hα)
  rw [Finset.sum_congr rfl (g := fun _ => (∏ i, h i ^ α i) •
    (((wordFiberCard m α : ℕ) : ℂ)⁻¹ • c α)) (fun σ hσ => by
      rw [(Finset.mem_filter.mp hσ).2])]
  rw [Finset.sum_const, wordFiberCard, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [← wordFiberCard, smul_smul, mul_comm]
  have hne : ((wordFiberCard m α : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]


/-- Norm bound for the degree-`m` part: `‖p_m‖ ≤ #{α : |α| = m} · b` when `‖c_α‖ ≤ b` for
`|α| = m`. -/
theorem norm_degreeSeries_le (c : (Fin n → ℕ) → F) (m : ℕ) {b : ℝ}
    (hb : ∀ α : Fin n → ℕ, ∑ i, α i = m → ‖c α‖ ≤ b) :
    ‖degreeSeries c m‖ ≤ ((Finset.Nat.antidiagonalTuple n m).card : ℝ) * b := by
  classical
  have hmaps : ∀ σ ∈ (univ : Finset (Fin m → Fin n)),
      wordCount σ ∈ Finset.Nat.antidiagonalTuple n m := fun σ _ =>
    Finset.Nat.mem_antidiagonalTuple.mpr (sum_wordCount σ)
  have h1 : ‖degreeSeries c m‖ ≤
      ∑ σ : Fin m → Fin n, ((wordFiberCard m (wordCount σ) : ℝ))⁻¹ * b := by
    unfold degreeSeries
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    refine (norm_wordTerm_le _ _).trans ?_
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left
      (hb _ (Finset.Nat.mem_antidiagonalTuple.mp (hmaps σ (mem_univ σ))))
      (by positivity)
  refine h1.trans_eq ?_
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hpos := wordFiberCard_pos (Finset.Nat.mem_antidiagonalTuple.mp hα)
  rw [Finset.sum_congr rfl (g := fun _ => ((wordFiberCard m α : ℝ))⁻¹ * b) (fun σ hσ => by
    rw [(Finset.mem_filter.mp hσ).2])]
  rw [Finset.sum_const, wordFiberCard, nsmul_eq_mul, ← wordFiberCard, ← mul_assoc,
    mul_inv_cancel₀ (by exact_mod_cast hpos.ne')]
  simp

/-- Stars and bars: `#{α : Fin n → ℕ | |α| = m} = binom (n + m - 1, m)`. -/
theorem card_antidiagonalTuple (n m : ℕ) :
    (Finset.Nat.antidiagonalTuple n m).card = (n + m - 1).choose m := by
  classical
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (univ : Finset (Fin n))) m
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [← h]
  refine Finset.card_bij (fun α _ => Finsupp.equivFunOnFinite.symm α) (fun α hα => ?_)
    (fun α _ β _ h => Finsupp.equivFunOnFinite.symm.injective h) (fun f hf => ?_)
  · rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, fun i _ => mem_univ i⟩
    have := Finset.Nat.mem_antidiagonalTuple.mp hα
    simpa [Finsupp.sum_fintype] using this
  · refine ⟨Finsupp.equivFunOnFinite f, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    have := (Finset.mem_finsuppAntidiag.mp hf).1
    simpa [Finsupp.equivFunOnFinite_apply] using this

end KAM.Wave
