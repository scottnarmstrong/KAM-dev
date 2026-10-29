/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowDivisor
public import KAM.Planetary.Preparation.SlowRates
public import KAM.Planetary.Preparation.RectangularAverage

/-!
# Slow averaging: application of the rectangular averaging lemma (P11A-P7c, `as-concl`)

`p11_slow_conclude` applies `aniso_avg` with `a = b = n`, center the secular center, `r₁ = s₂`,
`r₂ = π ε`, `T = K₂`, `α₁ = (γ/4) K₂^{-τ}`, `α₂ = ε α₁` and `E₀ = c₀ ε^{5/2} ℓ^{2τ+1}` (`ℓ = log (1/ε)`)
and repackages the conclusion into clauses 9-28 of `P11SlowSpecOf`, with the constants
`c ≥ c₀, …` of the spec as explicit lower bounds (so that the constants of `g₂` and of the
displacements do not depend on `c`). The inputs `h₀, f₂` are parametric in the P7b outputs.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology
namespace KAM.Planetary

section Conclude

variable {n : ℕ}

theorem p11Box_half_subset {a b : ℕ} (c : P11CVec (a+b)) {r1 r2 : ℝ} (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) :
    p11Box c (r1/2) (r2/2) ⊆ p11Box c r1 r2 :=
  fun _ hI => ⟨fun i => (hI.1 i).trans_le (by linarith), fun i => (hI.2 i).trans_le (by linarith)⟩

/-- A phase-independent function with finite weighted norm is bounded by it. -/
theorem p11_norm_le_of_wbound {m : ℕ} {V : Set (P11CVec m)} {s M : ℝ} {φ : P11CVec m → ℂ}
    (h : p11WBound (n := m) V s (fun z => φ z.2) M) {I : P11CVec m} (hI : I ∈ V) :
    ‖φ I‖ ≤ M := by
  obtain ⟨hsum, hle⟩ := h I hI
  have hc : KAM.Weighted.coeff (fun z : P11CVec m × P11CVec m => φ z.2) I 0 = φ I := by
    unfold KAM.Weighted.coeff KAM.torusCoeffW
    simp only [KAM.character_zero]
    simp only [neg_zero, KAM.character_zero, one_smul]
    exact p11_torusAverage_const _
  have h0 := hsum.le_tsum 0 (fun j _ => mul_nonneg (norm_nonneg _)
    (Real.exp_pos _).le)
  rw [hc] at h0
  have hw : KAM.Weighted.modeWeight s (0 : Fin m → ℤ) = 1 := by
    simp [KAM.Weighted.modeWeight, KAM.Fourier.modeSize]
  rw [hw, mul_one] at h0
  exact h0.trans hle

end Conclude

end KAM.Planetary

end
