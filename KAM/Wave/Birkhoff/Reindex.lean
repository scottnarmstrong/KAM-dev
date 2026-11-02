/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.Lambda

/-!
# Sums over `(ℤ ∖ {0})ⁿ` (blueprint-W `bpW:w3:quartic`, support)

Package W3-SETTING.

Reindexing of sums over `Fin n → BirkIdx` into a finite sum over sign patterns and a sum over
`Fin n → ℕ+` (`birk_tsum_pi`), the product of sign sums (`birk_sign_sum_prod`), and the
`ℕ+ × ℕ+ × ℕ+` form of `Fin 3 → ℕ+` (`birkTriEquiv`) used by the majorant of the cubic sums.
-/

@[expose] public noncomputable section

namespace KAM.Wave

/-- `(Fin n → Bool) × (Fin n → ℕ+) ≃ (Fin n → BirkIdx)`: signs and absolute values. -/
def birkPiEquiv (n : ℕ) : (Fin n → Bool) × (Fin n → ℕ+) ≃ (Fin n → BirkIdx) :=
  (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bool) (fun _ => ℕ+)).symm

@[simp] theorem birkPiEquiv_apply (n : ℕ) (z : (Fin n → Bool) × (Fin n → ℕ+)) (t : Fin n) :
    birkPiEquiv n z t = (z.1 t, z.2 t) := rfl

/-- The absolute values `|x_t|` of a point of `(ℤ ∖ {0})ⁿ`. -/
def birkAbs {n : ℕ} (x : Fin n → BirkIdx) : Fin n → ℕ+ := fun t => (x t).2

/-- The point `-x`. -/
def birkNegPi {n : ℕ} (x : Fin n → BirkIdx) : Fin n → BirkIdx := fun t => birkNeg (x t)

@[simp] theorem birkNegPi_apply {n : ℕ} (x : Fin n → BirkIdx) (t : Fin n) :
    birkNegPi x t = birkNeg (x t) := rfl

@[simp] theorem birkNegPi_birkNegPi {n : ℕ} (x : Fin n → BirkIdx) : birkNegPi (birkNegPi x) = x :=
    by
  ext t <;> simp [birkNegPi]

/-- `x ↦ -x` as an equivalence of `(ℤ ∖ {0})ⁿ`. -/
def birkNegPiEquiv (n : ℕ) : (Fin n → BirkIdx) ≃ (Fin n → BirkIdx) where
  toFun := birkNegPi
  invFun := birkNegPi
  left_inv := birkNegPi_birkNegPi
  right_inv := birkNegPi_birkNegPi

/-- Sum over `(ℤ ∖ {0})ⁿ` as a finite sum over sign patterns of sums over `(ℕ+)ⁿ`. -/
theorem birk_tsum_pi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {n : ℕ} {f : (Fin n → BirkIdx) → F} (hf : Summable f) :
    ∑' x, f x = ∑ s : Fin n → Bool, ∑' m : Fin n → ℕ+, f (fun t => (s t, m t)) := by
  have hs : Summable (f ∘ birkPiEquiv n) := (birkPiEquiv n).summable_iff.2 hf
  rw [← (birkPiEquiv n).tsum_eq]
  exact (Summable.tsum_prod hs).trans (by rw [tsum_fintype]; rfl)

/-- For a nonnegative `f`, summability of all the sign fibers gives summability. -/
theorem birk_summable_pi {n : ℕ} {f : (Fin n → BirkIdx) → ℝ} (hf : 0 ≤ f)
    (h : ∀ s : Fin n → Bool, Summable fun m : Fin n → ℕ+ => f (fun t => (s t, m t))) :
    Summable f := by
  have : Summable (f ∘ birkPiEquiv n) := by
    refine (summable_prod_of_nonneg (f := f ∘ birkPiEquiv n) (fun z => hf _)).2 ?_
    exact ⟨fun s => h s, Summable.of_finite⟩
  exact (birkPiEquiv n).summable_iff.1 this

/-- `Σ_{s ∈ {±}ⁿ} ∏_t h_t(s_t) = ∏_t (h_t(+) + h_t(-))`. -/
theorem birk_sign_sum_prod {R : Type*} [CommSemiring R] {n : ℕ} (h : Fin n → Bool → R) :
    ∑ s : Fin n → Bool, ∏ t, h t (s t) = ∏ t, (h t true + h t false) := by
  have := Finset.prod_univ_sum (fun t : Fin n => (Finset.univ : Finset Bool)) h
  rw [Fintype.piFinset_univ] at this
  simpa [Fintype.sum_bool] using this.symm

/-- Folding the signs: for a weight `G` depending only on `(|x_t|)_t`,
`Σ_{x ∈ (ℤ∖0)ⁿ} G(|x|) ∏_t W_t(x_t) = Σ_{m ∈ (ℕ+)ⁿ} G(m) ∏_t (W_t(+m_t) + W_t(-m_t))`. -/
theorem birk_pi_fold {n : ℕ} (G : (Fin n → ℕ+) → ℂ) (W : Fin n → BirkIdx → ℂ)
    (hsum : Summable fun x : Fin n → BirkIdx => G (birkAbs x) * ∏ t, W t (x t)) :
    ∑' x : Fin n → BirkIdx, G (birkAbs x) * ∏ t, W t (x t) =
      ∑' mm : Fin n → ℕ+, G mm * ∏ t, (W t (true, mm t) + W t (false, mm t)) := by
  rw [birk_tsum_pi hsum]
  have hs' := (birkPiEquiv n).summable_iff
    (f := fun x : Fin n → BirkIdx => G (birkAbs x) * ∏ t, W t (x t)) |>.2 hsum
  have hs : ∀ s ∈ (Finset.univ : Finset (Fin n → Bool)), Summable fun mm : Fin n → ℕ+ =>
      G mm * ∏ t, W t (s t, mm t) := fun s _ => (hs'.prod_factor s :)
  have e1 : ∑ s : Fin n → Bool, ∑' mm : Fin n → ℕ+, G mm * ∏ t, W t (s t, mm t) =
      ∑' mm : Fin n → ℕ+, ∑ s : Fin n → Bool, G mm * ∏ t, W t (s t, mm t) :=
    (Summable.tsum_finsetSum hs).symm
  have e0 : ∀ s : Fin n → Bool, ∀ mm : Fin n → ℕ+,
      G (birkAbs (fun t => (s t, mm t))) * ∏ t, W t ((fun t => (s t, mm t)) t) =
        G mm * ∏ t, W t (s t, mm t) := fun s mm => rfl
  simp only [e0]
  rw [e1]
  refine tsum_congr fun mm => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact birk_sign_sum_prod (fun t b => W t (b, mm t))

/-- `Fin 3 → ℕ+ ≃ ℕ+ × ℕ+ × ℕ+`. -/
def birkTriEquiv : (Fin 3 → ℕ+) ≃ ℕ+ × ℕ+ × ℕ+ where
  toFun m := (m 0, m 1, m 2)
  invFun t := ![t.1, t.2.1, t.2.2]
  left_inv m := by ext i; fin_cases i <;> rfl
  right_inv t := rfl

@[simp] theorem birkTriEquiv_apply (mm : Fin 3 → ℕ+) : birkTriEquiv mm = (mm 0, mm 1, mm 2) := rfl

end KAM.Wave

end
