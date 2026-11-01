/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepPlusFam
public import KAM.Wave.KamStep.StepFreqBound
public import KAM.Wave.KamStep.StepSolve
public import KAM.Wave.KamStep.Data
public import KAM.Wave.KamStep.TaylorFieldBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The data of the KAM step: Taylor and solve families (blueprint-W `bpW:w5:step`, construction)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepFTfam`: the family `F_ξ = homSolveTaylor_gen … R_ξ` (zero off `Π`). `stepSetup_*`: the field
bounds of `R_ξ` (`3ε₀`, `3ε₁d`) and of `F_ξ` (`M₀`, `M₁ d`, with `M₀ + λ M₁ ≤ M_F`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem waveBW_pos {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 < σ) : 0 < waveBW τ σ := by
  have hs := waveBW_summable hτ hσ
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ (1 + Fourier.modeSize k) * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := fun k => by
    have := Fourier.modeSize_nonneg k
    have := waveA_ge_one (τ := τ) k
    positivity
  have h0 := hs.le_tsum 0 (fun k _ => hnn k)
  have h1 : (1 : ℝ) ≤ waveA τ 0 := waveA_ge_one 0
  have : 0 < (1 + Fourier.modeSize (0 : Fin 2 → ℤ)) * waveA τ 0 ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize (0 : Fin 2 → ℤ)) := by
    have := Fourier.modeSize_nonneg (0 : Fin 2 → ℤ)
    positivity
  exact lt_of_lt_of_le this h0

variable {a p pb s : ℝ}

open Classical in
/-- The family `F_ξ` of solutions of the homological equation (zero off `Π`). -/
def stepFTfam {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ} {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ}
    {M0 Mω MΩ τ α σ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ) (hH : HomMelnikov τ α Par ω Ω)
    (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (R : (Fin 2 → ℝ) → HomTaylor_gen a p pb s) (ξ : Fin 2 → ℝ) :
    HomTaylor_gen a p pb (s - σ) :=
  if hξ : ξ ∈ Par then homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) (R ξ)
  else zeroTaylor a p pb (s - σ)

theorem stepFTfam_of_mem {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ τ α σ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hH : HomMelnikov τ α Par ω Ω) (hτ : 0 ≤ τ) (hα : 0 < α) (hσ : 0 < σ) (hσs : σ < s)
    (R : (Fin 2 → ℝ) → HomTaylor_gen a p pb s) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ Par) :
    stepFTfam h hH hτ hα hσ hσs R ξ =
      homSolveTaylor_gen hτ hα hσ hσs (homMultBounds_of h hα hH hξ) (R ξ) := by
  classical
  simp [stepFTfam, hξ]

end KAM.Wave
