/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

/-!
# Divisors after a KAM step (`bpW:w5:step` (iv), step `st-div`)

If `(ω, Ω)` satisfies the Melnikov conditions `(H_α)` and the corrections satisfy
`‖ω' - ω‖ ≤ 6πε`, `|Ω'_j - Ω_j| ≤ 3ε`, then for `|k|₁ ≤ K` and
`6π(1+K)(1+K^τ)ε ≤ α - α'` the new frequencies satisfy `(H_{α'})` on the pairs `(k,l) ∈ 𝒵` with
`|k|₁ ≤ K` (`stepDivisors`).
-/

@[expose] public section

namespace KAM.Wave

theorem homPairL_sub_le {l : ℕ+ →₀ ℤ} {Ω Ω' : ℕ+ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ j, |Ω' j - Ω j| ≤ δ) : |homPairL l Ω' - homPairL l Ω| ≤ homL1 l * δ := by
  unfold homPairL Finsupp.sum
  rw [← Finset.sum_sub_distrib, homL1_cast]
  unfold Finsupp.sum
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)

theorem waveA_le_of_modeSize_le {τ K : ℝ} (hτ : 0 ≤ τ) {k : Fin 2 → ℤ}
    (hk : Fourier.modeSize k ≤ K) : waveA τ k ≤ 1 + K ^ τ := by
  unfold waveA
  have h0 := Fourier.modeSize_nonneg k
  split_ifs
  · have : 0 ≤ K ^ τ := Real.rpow_nonneg (h0.trans hk) _
    linarith
  · have := Real.rpow_le_rpow h0 hk hτ
    linarith

/-- **Divisors after the step** (`bpW:w5:step` (iv)). -/
theorem stepDivisors {τ α α' ε K : ℝ} {Par : Set (Fin 2 → ℝ)} {ω ω' : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω Ω' : (Fin 2 → ℝ) → ℕ+ → ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hK : 1 ≤ K)
    (hH : HomMelnikov τ α Par ω Ω)
    (hω : ∀ ξ ∈ Par, ‖ω' ξ - ω ξ‖ ≤ 6 * Real.pi * ε)
    (hΩ : ∀ ξ ∈ Par, ∀ j, |Ω' ξ j - Ω ξ j| ≤ 3 * ε)
    (hα : 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α') {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ} (hkl : (k, l) ∈ homZ) (hkK : Fourier.modeSize k ≤ K) :
    α' * (homJap l : ℝ) / waveA τ k ≤ |homPairZ k (ω' ξ) + homPairL l (Ω' ξ)| := by
  have hold := hH ξ hξ (k, l) hkl
  have hA1 := waveA_ge_one (τ := τ) k
  have hAK := waveA_le_of_modeSize_le hτ hkK
  have hj : (1 : ℝ) ≤ homJap l := by exact_mod_cast le_max_left 1 _
  have hl2 : (homL1 l : ℝ) ≤ 2 := by exact_mod_cast hkl.2
  have hk0 := Fourier.modeSize_nonneg k
  have hKτ : 0 ≤ K ^ τ := Real.rpow_nonneg (by linarith) _
  have e1 : |homPairZ k (ω' ξ) - homPairZ k (ω ξ)| ≤ Fourier.modeSize k * (6 * Real.pi * ε) := by
    rw [homPairZ_sub]
    exact (abs_homPairZ_le k _).trans
      (mul_le_mul_of_nonneg_left (hω ξ hξ) hk0)
  have e2 := homPairL_sub_le (l := l) (by linarith) (hΩ ξ hξ)
  have hpi := Real.pi_pos
  have herr : |(homPairZ k (ω' ξ) + homPairL l (Ω' ξ)) - (homPairZ k (ω ξ) + homPairL l (Ω ξ))| ≤
      6 * Real.pi * (1 + K) * ε := by
    have : (homPairZ k (ω' ξ) + homPairL l (Ω' ξ)) - (homPairZ k (ω ξ) + homPairL l (Ω ξ)) =
        (homPairZ k (ω' ξ) - homPairZ k (ω ξ)) + (homPairL l (Ω' ξ) - homPairL l (Ω ξ)) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    have h3 : (homL1 l : ℝ) * (3 * ε) ≤ 2 * (3 * ε) :=
      mul_le_mul_of_nonneg_right hl2 (by linarith)
    have h4 : Fourier.modeSize k * (6 * Real.pi * ε) ≤ K * (6 * Real.pi * ε) :=
      mul_le_mul_of_nonneg_right hkK (by positivity)
    have h5 : 6 * ε ≤ 6 * Real.pi * ε := by
      have : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      nlinarith
    nlinarith
  have hpos : 0 < waveA τ k := by linarith
  have hpos2 : 0 < 1 + K ^ τ := by linarith
  -- the loss `(α - α') ⟨l⟩ / A_k ≥ (α - α')/(1 + K^τ) ≥ 6π(1+K)ε`
  have hloss : 6 * Real.pi * (1 + K) * ε ≤ (α - α') * (homJap l : ℝ) / waveA τ k := by
    have h1 : 6 * Real.pi * (1 + K) * ε ≤ (α - α') / (1 + K ^ τ) := by
      rw [le_div_iff₀ hpos2]; nlinarith
    have hnn : 0 ≤ α - α' := le_trans (by positivity) hα
    calc 6 * Real.pi * (1 + K) * ε ≤ (α - α') / (1 + K ^ τ) := h1
      _ ≤ (α - α') / waveA τ k := div_le_div_of_nonneg_left hnn hpos hAK
      _ ≤ (α - α') * (homJap l : ℝ) / waveA τ k := by
          rw [div_le_div_iff_of_pos_right hpos]
          nlinarith
  have hsub : α * (homJap l : ℝ) / waveA τ k - (α - α') * (homJap l : ℝ) / waveA τ k =
      α' * (homJap l : ℝ) / waveA τ k := by ring
  have hd := abs_sub_abs_le_abs_sub (homPairZ k (ω ξ) + homPairL l (Ω ξ))
    (homPairZ k (ω' ξ) + homPairL l (Ω' ξ))
  rw [abs_sub_comm] at hd
  linarith

theorem rpow_half_le_add_two_rpow {j : ℕ+} {c : ℝ} (hc : 1 / 2 ≤ c) :
    (j : ℝ) ^ (1 / 2 : ℝ) ≤ ((j : ℝ) + 2) ^ c := by
  have hj : (0 : ℝ) ≤ j := by positivity
  have hJ : (1 : ℝ) ≤ (j : ℝ) + 2 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    linarith
  calc (j : ℝ) ^ (1 / 2 : ℝ) ≤ ((j : ℝ) + 2) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hj (by linarith) (by norm_num)
    _ ≤ ((j : ℝ) + 2) ^ c := Real.rpow_le_rpow_of_exponent_le hJ hc

/-- **The frequency hypothesis is stable under the step** (`bpW:w5:step` (iii)): if the corrections
satisfy `(j+2)^{p_+-p}|Ω'_j - Ω_j| ≤ 3ε` (and the same for `ξ`-differences with `3ε/λ`), with
`p_+ - p ≥ 1/2`, then `(ω', Ω')` satisfies `bpW:w5:freq` with `M₀ + 3ε`, `M_ω + 6πε/λ`,
`M_Ω + 3ε/λ`. -/
theorem stepFreqHyp {Par : Set (Fin 2 → ℝ)} {ω ω' : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω Ω' : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ ε lam p pb : ℝ}
    (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hε : 0 ≤ ε) (hlam : 0 < lam) (hpp : 1 / 2 ≤ pb - p)
    (hωL : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ‖(ω' ξ - ω ξ) - (ω' ζ - ω ζ)‖ ≤ 6 * Real.pi * ε / lam * ‖ξ - ζ‖)
    (hΩ : ∀ ξ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) * |Ω' ξ j - Ω ξ j| ≤ 3 * ε)
    (hΩL : ∀ ξ ∈ Par, ∀ ζ ∈ Par, ∀ j : ℕ+, ((j : ℝ) + 2) ^ (pb - p) *
      |(Ω' ξ j - Ω ξ j) - (Ω' ζ j - Ω ζ j)| ≤ 3 * ε / lam * ‖ξ - ζ‖) :
    HomFreqHyp Par ω' Ω' (M0 + 3 * ε) (Mω + 6 * Real.pi * ε / lam) (MΩ + 3 * ε / lam) where
  consts_nonneg := by
    obtain ⟨n0, n1, n2⟩ := h.consts_nonneg
    have hpi := Real.pi_pos
    have a1 : 0 ≤ 6 * Real.pi * ε / lam := by positivity
    have a2 : 0 ≤ 3 * ε / lam := by positivity
    exact ⟨by linarith, by linarith, by linarith⟩
  tail ξ hξ j := by
    have h1 := h.tail ξ hξ j
    have hr := rpow_half_le_add_two_rpow (j := j) hpp
    have h2 : (j : ℝ) ^ (1 / 2 : ℝ) * |Ω' ξ j - Ω ξ j| ≤ 3 * ε :=
      (mul_le_mul_of_nonneg_right hr (abs_nonneg _)).trans (hΩ ξ hξ j)
    have e : Ω' ξ j - ((j : ℝ) + 2) = (Ω ξ j - ((j : ℝ) + 2)) + (Ω' ξ j - Ω ξ j) := by ring
    rw [e]
    calc (j : ℝ) ^ (1 / 2 : ℝ) * |(Ω ξ j - ((j : ℝ) + 2)) + (Ω' ξ j - Ω ξ j)| ≤
          (j : ℝ) ^ (1 / 2 : ℝ) * (|Ω ξ j - ((j : ℝ) + 2)| + |Ω' ξ j - Ω ξ j|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ M0 + 3 * ε := by rw [mul_add]; linarith
  lipOmega ξ hξ ζ hζ := by
    have h1 := h.lipOmega ξ hξ ζ hζ
    have h2 := hωL ξ hξ ζ hζ
    have e : ω' ξ - ω' ζ = (ω ξ - ω ζ) + ((ω' ξ - ω ξ) - (ω' ζ - ω ζ)) := by abel
    rw [e]
    calc _ ≤ ‖ω ξ - ω ζ‖ + ‖(ω' ξ - ω ξ) - (ω' ζ - ω ζ)‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith
  lipTail ξ hξ ζ hζ j := by
    have h1 := h.lipTail ξ hξ ζ hζ j
    have hr := rpow_half_le_add_two_rpow (j := j) hpp
    have h2 : (j : ℝ) ^ (1 / 2 : ℝ) * |(Ω' ξ j - Ω ξ j) - (Ω' ζ j - Ω ζ j)| ≤
        3 * ε / lam * ‖ξ - ζ‖ :=
      (mul_le_mul_of_nonneg_right hr (abs_nonneg _)).trans (hΩL ξ hξ ζ hζ j)
    have e : Ω' ξ j - Ω' ζ j = (Ω ξ j - Ω ζ j) + ((Ω' ξ j - Ω ξ j) - (Ω' ζ j - Ω ζ j)) := by ring
    rw [e]
    calc (j : ℝ) ^ (1 / 2 : ℝ) * |(Ω ξ j - Ω ζ j) + ((Ω' ξ j - Ω ξ j) - (Ω' ζ j - Ω ζ j))| ≤
          (j : ℝ) ^ (1 / 2 : ℝ) * (|Ω ξ j - Ω ζ j| +
            |(Ω' ξ j - Ω ξ j) - (Ω' ζ j - Ω ζ j)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ ≤ _ := by rw [mul_add]; nlinarith

end KAM.Wave
