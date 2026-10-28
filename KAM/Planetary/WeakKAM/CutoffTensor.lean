/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.CutoffBump

/-! # P11B smooth cutoff: iterated coordinate derivatives of a tensor product

For `g w = ∏ j, f j (w j)` on `Fin n → ℝ`, the `k`-th derivative in the coordinate directions
`e_{i 1}, …, e_{i k}` is the product of the one-variable derivatives of order equal to the
multiplicity of each coordinate in `i`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

/-- Number of occurrences of the coordinate `j` in the index list `i`. -/
def selectionMult {k : ℕ} (i : Fin k → Fin n) (j : Fin n) : ℕ :=
  (Finset.univ.filter fun l => i l = j).card

theorem selectionMult_succ {k : ℕ} (i : Fin (k + 1) → Fin n) (j : Fin n) :
    selectionMult i j = selectionMult (Fin.tail i) j + if i 0 = j then 1 else 0 := by
  unfold selectionMult
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ, add_comm]
  rfl

theorem selectionTensor_fderiv_single {f : Fin n → ℝ → ℝ} (w : Fin n → ℝ) (a : Fin n)
    (hf : ∀ j, DifferentiableAt ℝ (f j) (w j)) :
    fderiv ℝ (fun y : Fin n → ℝ => ∏ j, f j (y j)) w (Pi.single a 1) =
      (∏ j ∈ Finset.univ.erase a, f j (w j)) * deriv (f a) (w a) := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin n)), HasFDerivAt (fun y : Fin n → ℝ => f j (y j))
      ((deriv (f j) (w j)) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) w := fun j _ =>
    ((hf j).hasDerivAt.comp_hasFDerivAt w (hasFDerivAt_apply j w))
  have := (HasFDerivAt.finsetProd h).fderiv
  rw [this]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · simp [mul_comm]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem selectionTensor_iteratedFDeriv (f : Fin n → ℝ → ℝ) :
    ∀ (k : ℕ), (∀ j, ContDiff ℝ k (f j)) → ∀ (i : Fin k → Fin n) (w : Fin n → ℝ),
      iteratedFDeriv ℝ k (fun y : Fin n → ℝ => ∏ j, f j (y j)) w
          (fun l => Pi.single (i l) 1) =
        ∏ j, iteratedDeriv (selectionMult i j) (f j) (w j) := by
  intro k
  induction k with
  | zero =>
    intro hf i w
    simp [selectionMult, iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro hf i w
    have hg : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun y : Fin n → ℝ => ∏ j, f j (y j)) :=
      contDiff_prod fun j _ => (hf j).comp (contDiff_pi.1 contDiff_id j)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k (fun y : Fin n → ℝ => ∏ j, f j (y j))) w :=
      (hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) w
    have hfk : ∀ j, ContDiff ℝ (k : ℕ) (f j) := fun j =>
      (hf j).of_le (by exact_mod_cast Nat.le_succ k)
    rw [hd.iteratedFDeriv_succ_apply_left']
    have hG : (fun y : Fin n → ℝ => iteratedFDeriv ℝ k (fun y : Fin n → ℝ => ∏ j, f j (y j)) y
        (Fin.tail fun l => (Pi.single (i l) 1 : Fin n → ℝ))) =
        fun y => ∏ j, iteratedDeriv (selectionMult (Fin.tail i) j) (f j) (y j) := by
      funext y
      exact ih hfk (Fin.tail i) y
    rw [hG]
    have hdiff : ∀ j, DifferentiableAt ℝ
        (iteratedDeriv (selectionMult (Fin.tail i) j) (f j)) (w j) := by
      intro j
      have hle : selectionMult (Fin.tail i) j ≤ k := by
        unfold selectionMult
        calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = k := by simp
      exact ((hf j).differentiable_iteratedDeriv _
        (by exact_mod_cast Nat.lt_succ_of_le hle)) _
    rw [selectionTensor_fderiv_single w (i 0) hdiff]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (i 0))]
    rw [← iteratedDeriv_succ]
    have hm : selectionMult i (i 0) = selectionMult (Fin.tail i) (i 0) + 1 := by
      rw [selectionMult_succ]; simp
    rw [hm, mul_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have : i 0 ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    rw [selectionMult_succ]; simp [this]

end KAM.Planetary
