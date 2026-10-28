/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.WeakKAM.ExtensionFrequency
public import KAM.Planetary.WeakKAM.Cutoff
public import KAM.Planetary.WeakKAM.Schedule

/-! # P11B finite extension (`finite-extension`)

For an arbitrary nested chain `K = K₀ ⊇ K₁ ⊇ … ⊇ K_ν` of nonempty compact sets carrying holomorphic,
real, bounded increments `Δω_j` on the collars `K_j + t_j`, the cutoff-weighted frequency
`ω + ∑_{j<ν} χ_j Δω_j` is `C^μ` on the real points of the action neighbourhood, agrees with
`Re ω_ν` on `K_ν`, and differs from `ω` by at most `c' ∑ ℓ_j t_j^{-μ}` in the Euclidean `C^k` seminorm
`selectionDGVector` (`k ≤ μ`). The Leibniz expansion and the Cauchy estimates are in
`ExtensionStage`; the Euclidean/max norm conversion is in `ExtensionNorm`.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n μ : ℕ} {t C₁ : ℝ}

theorem selectionCutoffC_nonneg (n μ k : ℕ) : 0 ≤ selectionCutoffC n μ k :=
  mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Real.sSup_nonneg (by
    rintro v ⟨a, -, rfl⟩
    exact Finset.prod_nonneg fun i _ => selectionBumpL1_nonneg _ _))

theorem selectionExtensionSet_bddAbove (n μ : ℕ) :
    BddAbove {v | ∃ k ≤ μ, v = (4 : ℝ) ^ k *
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)} := by
  refine Set.Finite.bddAbove (((Set.finite_Iic μ).image fun k => (4 : ℝ) ^ k *
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)).subset ?_)
  rintro v ⟨k, hk, rfl⟩
  exact ⟨k, hk, rfl⟩

theorem le_selectionExtensionC {k : ℕ} (hk : k ≤ μ) :
    Real.sqrt n * ((4 : ℝ) ^ k * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      selectionCutoffC n μ j * (k - j : ℕ) ^ (k - j)) ≤ selectionExtensionC n μ := by
  unfold selectionExtensionC
  exact mul_le_mul_of_nonneg_left (le_csSup (selectionExtensionSet_bddAbove n μ) ⟨k, hk, rfl⟩)
    (Real.sqrt_nonneg _)

/-- Euclidean-scaled Leibniz bound for one stage in terms of the extension constant. -/
theorem selectionStage_extension_bound {E : Set (SelectionR n)} (hE : IsCompact E)
    (hne : E.Nonempty) (ht : 0 < t) (ht1 : t ≤ 1) {Δ : SelectionC n → SelectionC n} {ℓ : ℝ}
    (hΔ : DifferentiableOn ℂ Δ (actionNbhd E t))
    (hreal : ∀ b : SelectionR n, selectionReal b ∈ actionNbhd E t →
      Δ (selectionReal b) = selectionReal (selectionRe (Δ (selectionReal b))))
    (hbd : ∀ b ∈ actionNbhd E t, ‖Δ b‖ ≤ ℓ) {χ : SelectionR n → ℝ}
    (hχ : ContDiff ℝ μ χ) (hsupp : tsupport χ ⊆ {y | Metric.infDist y E ≤ t / 2})
    (hχb : ∀ k ≤ μ, ∀ y, ∀ a : Fin k → SelectionR n, (∀ i, ‖a i‖ ≤ 1) →
      |iteratedFDeriv ℝ k χ y a| ≤ selectionCutoffC n μ k * (4 / t) ^ k)
    {k : ℕ} (hk : k ≤ μ) (y : SelectionR n) :
    Real.sqrt n * ‖iteratedFDeriv ℝ k (fun y => χ y • selectionIncrement Δ y) y‖ ≤
      ℓ / t ^ μ * selectionExtensionC n μ := by
  have hℓ : 0 ≤ ℓ := by
    obtain ⟨J, hJ⟩ := hne
    exact (norm_nonneg _).trans (hbd (selectionReal J) ⟨J, hJ, by
      rw [show selectionReal J - (fun i => (J i : ℂ)) = 0 from sub_self _, norm_zero]
      exact ht⟩)
  have h1 := selectionStage_norm_iteratedFDeriv_le hE hne ht hΔ hreal hbd
    (selectionCutoffC_nonneg n μ) hχ hsupp hχb hk y
  have hS := le_selectionExtensionC (n := n) hk
  have hpow : (4 / t) ^ k ≤ 4 ^ k / t ^ μ := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_of_le_one ht.le ht1 hk)
  set Sk := ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * selectionCutoffC n μ i * ((k - i : ℕ) : ℝ) ^ (k - i) with hSk
  have hSk0 : 0 ≤ Sk := Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (selectionCutoffC_nonneg _ _ _)) (pow_nonneg (Nat.cast_nonneg _) _)
  calc Real.sqrt n * ‖iteratedFDeriv ℝ k (fun y => χ y • selectionIncrement Δ y) y‖
      ≤ Real.sqrt n * (ℓ * (4 / t) ^ k * Sk) := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt n * (ℓ * (4 ^ k / t ^ μ) * Sk) := by gcongr
    _ = ℓ / t ^ μ * (Real.sqrt n * (4 ^ k * Sk)) := by ring
    _ ≤ ℓ / t ^ μ * selectionExtensionC n μ := by
        exact mul_le_mul_of_nonneg_left hS (div_nonneg hℓ (by positivity))

end KAM.Planetary
