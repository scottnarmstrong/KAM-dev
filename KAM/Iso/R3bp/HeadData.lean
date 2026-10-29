/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Iso.PeriodOne
public import KAM.Iso.Confinement.Setting
public import KAM.Iso.R3bp.Safe

/-!
# The data of I-HEAD for the restricted three-body problem

Blueprint-I Part 8: `bpI:p8:head-data`.

* `r3bpH`, `r3bpS₀`, `r3bpR₀`: the Hamiltonian `h̃` and the radii `s₀ = δ₂/(2π)`, `r₀ = 2π δ₂`.
* `r3bp_headData`: all source premises of I-HEAD on `(B, s₀, r₀, h̃, B', η = 1)`.
* `r3bp_perturbData`: for `0 ≤ μ < μ₂`, `f̃_μ` with `ε = C_F μ` satisfies the premises on `f`.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.R3bp

open KAM KAM.Kepler KAM.Iso KAM.Iso.Confinement KAM.Planetary

section Data

variable {am ap em ep : ℝ}

/-- `h̃ = h_{(2π)², 1/(2π)}`. -/
def r3bpH : (Fin 2 → ℂ) → ℂ := keplerRotH ((2 * Real.pi) ^ 2) (1 / (2 * Real.pi))

/-- `s₀ = δ₂/(2π)`, `r₀ = 2π δ₂` with `δ₂ = exactDelta 𝒦`. -/
def r3bpS₀ (am ap em ep : ℝ) : ℝ := exactDelta (safeK am ap em ep) / (2 * Real.pi)
def r3bpR₀ (am ap em ep : ℝ) : ℝ := 2 * Real.pi * exactDelta (safeK am ap em ep)

/-- `bpI:p8:head-data` (a): all source premises of I-HEAD on `(B, s₀, r₀, h̃, B', η = 1)`. -/
theorem r3bp_headData (hp : R3bpParams am ap em ep) :
    HeadData (safeB am ap em ep) (r3bpS₀ am ap em ep) (r3bpR₀ am ap em ep) r3bpH
      (safeB' am ap em ep) 1 := by
  obtain ⟨hopen, hbdd, hne, hopen', hcpt, hin, hKB⟩ := safe_domain hp
  have hK := (safe_inclusions hp).2.2
  have hρ := (safe_radii hp).2.1
  obtain ⟨hs, hr, -, ⟨hholo, -⟩, -⟩ := period_one hK hρ hKB
  refine ⟨⟨hs, hr, hholo, ?_⟩, hopen, hbdd, hne, ?_, hopen', hcpt, hin, one_pos⟩
  · intro I _
    exact congrArg Complex.im (keplerRotH_real _ _ I) |>.trans (Complex.ofReal_im _)
  · intro I hI
    have h := (nondeg_exact hK hρ hKB I hI).2
    have h0 := (nondeg_exact hK hρ hKB I hI).1
    rw [r3bpH, h]
    exact div_ne_zero (by norm_num) (pow_ne_zero _ h0.ne')

/-- `bpI:p8:head-data` (b): for `0 ≤ μ < μ₂`, `f = f̃_μ` and `ε = C_F μ` satisfy the hypotheses of
I-HEAD except `ε < ε₀`. -/
theorem r3bp_perturbData (hp : R3bpParams am ap em ep) {μ : ℝ} (h0 : 0 ≤ μ)
    (hμ : μ < exactMu2 (safeK am ap em ep)) :
    PerturbData (safeB am ap em ep) (r3bpS₀ am ap em ep) (r3bpR₀ am ap em ep)
      (tildeF (safeK am ap em ep) μ) (μ * exactCF (safeK am ap em ep)) := by
  obtain ⟨-, -, hne, -, -, -, hKB⟩ := safe_domain hp
  have hK := (safe_inclusions hp).2.2
  have hρ := (safe_radii hp).2.1
  obtain ⟨hs0, hr0, -, -, hf, hreal⟩ := period_one hK hρ hKB
  have hs : 0 < r3bpS₀ am ap em ep := hs0
  have hr : 0 < r3bpR₀ am ap em ep := hr0
  have hμ' : |μ| < exactMu2 (safeK am ap em ep) := by rwa [abs_of_nonneg h0]
  obtain ⟨hholo, hbound, hper⟩ := hf μ hμ'
  rw [abs_of_nonneg h0] at hbound
  refine ⟨hholo, hper, ?_, ?_, hbound⟩
  · intro θ I hI
    have hθ : toC θ ∈ complexStrip 2 (r3bpS₀ am ap em ep) := by
      intro i
      simpa using hs
    exact (hreal μ hμ' (θ, I) ⟨hθ, hI⟩).1
  · obtain ⟨I, hI⟩ := hne
    have hIm : toC I ∈ actionNbhd (safeB am ap em ep) (r3bpR₀ am ap em ep) :=
      ⟨I, hI, by simpa [dist_eq_norm] using hr⟩
    have h0s : (0 : Fin 2 → ℂ) ∈ complexStrip 2 (r3bpS₀ am ap em ep) := by
      intro i
      simpa using hs
    exact (norm_nonneg _).trans (hbound (0, toC I) ⟨h0s, hIm⟩)

end Data

end KAM.Iso.R3bp

end
