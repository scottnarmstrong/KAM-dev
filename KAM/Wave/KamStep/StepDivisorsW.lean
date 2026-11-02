/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepClauses
public import KAM.Wave.Homological.WaveReindex
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

/-!
# Divisors after the step, Dirichlet-weight variant (blueprint-W `bpW:w5:step` (iv))

The blueprint's clause (iv) "holds for the Dirichlet weight `⟨l⟩^w` of `bpW:w4:wave` (ii) as well as
for `⟨l⟩`". `stepDivisorsW`: from the old wave-weight lower bound `α⟨l⟩^w/A_k` (`HomMelnikovW`) the
new one `α'⟨l⟩^w/A_k` follows by the same subtraction argument as `stepDivisors` (only `⟨l⟩^w ≥ 1`
is used; no comparison with `⟨l⟩` and no factor `3`). `StepCore.divisorsW` is the step instance.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem stepDivisorsW {τ α α' ε K : ℝ} {Par : Set (Fin 2 → ℝ)} {ω ω' : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω Ω' : (Fin 2 → ℝ) → ℕ+ → ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hK : 1 ≤ K)
    (hH : HomMelnikovW τ α Par ω Ω)
    (hω : ∀ ξ ∈ Par, ‖ω' ξ - ω ξ‖ ≤ 6 * Real.pi * ε)
    (hΩ : ∀ ξ ∈ Par, ∀ j, |Ω' ξ j - Ω ξ j| ≤ 3 * ε)
    (hα : 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α') {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ} (hkl : (k, l) ∈ homZ) (hkK : Fourier.modeSize k ≤ K) :
    α' * (homJapW l : ℝ) / waveA τ k ≤ |homPairZ k (ω' ξ) + homPairL l (Ω' ξ)| := by
  have hold := hH ξ hξ (k, l) hkl
  have hA1 := waveA_ge_one (τ := τ) k
  have hAK := waveA_le_of_modeSize_le hτ hkK
  have hj : (1 : ℝ) ≤ homJapW l := by exact_mod_cast le_max_left 1 _
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
  have hloss : 6 * Real.pi * (1 + K) * ε ≤ (α - α') * (homJapW l : ℝ) / waveA τ k := by
    have h1 : 6 * Real.pi * (1 + K) * ε ≤ (α - α') / (1 + K ^ τ) := by
      rw [le_div_iff₀ hpos2]; nlinarith
    have hnn : 0 ≤ α - α' := le_trans (by positivity) hα
    calc 6 * Real.pi * (1 + K) * ε ≤ (α - α') / (1 + K ^ τ) := h1
      _ ≤ (α - α') / waveA τ k := div_le_div_of_nonneg_left hnn hpos hAK
      _ ≤ (α - α') * (homJapW l : ℝ) / waveA τ k := by
          rw [div_le_div_iff_of_pos_right hpos]
          nlinarith
  have hsub : α * (homJapW l : ℝ) / waveA τ k - (α - α') * (homJapW l : ℝ) / waveA τ k =
      α' * (homJapW l : ℝ) / waveA τ k := by ring
  have hd := abs_sub_abs_le_abs_sub (homPairZ k (ω ξ) + homPairL l (Ω ξ))
    (homPairZ k (ω' ξ) + homPairL l (Ω' ξ))
  rw [abs_sub_comm] at hd
  linarith

variable {a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF : ℝ}
  {Par : Set (Fin 2 → ℝ)}
  {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
  {P : (Fin 2 → ℝ) → KamPhase → ℂ} {X : (Fin 2 → ℝ) → KamPhase → KamPhase}
  {FT : (Fin 2 → ℝ) → HomTaylor_gen a p pb (s - σ)}

namespace StepCore

variable (H : StepCore a p pb s r σ η τ α lam ε ε₀ ε₁ γ M0 Mω MΩ M₀ M₁ cF tF Par ω Ω P X FT) [Fact
  (0 < r)]

include H

/-- **The divisors after the step** (`bpW:w5:step` (iv)), Dirichlet-weight variant. -/
protected theorem divisorsW (hH : HomMelnikovW τ α Par ω Ω) {K α' : ℝ} (hK : 1 ≤ K)
    (hα' : 6 * Real.pi * (1 + K) * (1 + K ^ τ) * ε ≤ α - α') {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par)
    {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ} (hkl : (k, l) ∈ homZ) (hkK : Fourier.modeSize k ≤ K) :
    α' * (homJapW l : ℝ) / waveA τ k ≤
      |homPairZ k (H.omegaPlus ξ) + homPairL l (H.OmegaPlus ξ)| := by
  have hpi := Real.pi_pos
  refine stepDivisorsW (ω' := H.omegaPlus) (Ω' := H.OmegaPlus) H.hτ H.ε_pos.le hK hH
    (fun ξ hξ => (H.freq_sup hξ).trans (by nlinarith [H.ε₀_le])) (fun ξ hξ j => ?_) hα' hξ hkl hkK
  rw [H.OmegaPlus_sub]
  have h := stepOmegaTail_bound H.ha H.hp H.hpb H.hr H.hs (H.R ξ) (H.R_field ξ hξ) j
  have hj : (1 : ℝ) ≤ ((j : ℝ) + 2) ^ (pb - p) :=
    Real.one_le_rpow (by have : (0 : ℝ) ≤ j := by positivity
                         linarith) (by linarith [H.hpp])
  calc |stepOmegaTail (H.R ξ) j| ≤ ((j : ℝ) + 2) ^ (pb - p) * |stepOmegaTail (H.R ξ) j| :=
        le_mul_of_one_le_left (abs_nonneg _) hj
    _ ≤ 3 * ε₀ := h
    _ ≤ 3 * ε := by linarith [H.ε₀_le]

end StepCore

end KAM.Wave

end
