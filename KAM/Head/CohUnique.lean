/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.Cohomological
public import KAM.Torus.Basic
public import KAM.Diophantine.Frozen

/-!
# Homogeneous uniqueness for the cohomological equation

The adapter `KAM.Head.coh_unique_zero` (used by `bp:p4:lagrangian`): a
holomorphic, `1`-periodic function `w` on `T_r` with zero average
and `∂_ω w = 0` on `T_r` is identically zero, for `ω` that is `(γ, τ)`-Diophantine with `γ > 0`.

The statement holds for every real `τ`, with no bound on `w` and no strip loss. The lemma
`KAM.eq_cohSolution` (`KAM/Strip/Cohomological.lean`) carries the premises `0 ≤ τ`, a bound on the
forcing and a strip loss of its section, so it is not applied. Instead the proof follows its
coefficient step: `ŵ_k` satisfies `2πi (k · ω) ŵ_k = 0` (`KAM.torusCoeff_fderiv`), the nonresonance
`k · ω ≠ 0` for `k ≠ 0` comes from `hω.condition.nonresonant hγ`, and `ŵ_0 = ⟨w⟩ = 0`; then
`KAM.eq_zero_of_torusCoeff_holomorphic` finishes.
-/

@[expose] public noncomputable section

open KAM.Torus

namespace KAM.Head

/-- Adapter for `bp:p1:cohomological` (homogeneous uniqueness): a holomorphic, periodic,
zero-average `w` with `∂_ω w = 0` on `T_r` vanishes, for `ω` Diophantine (`γ > 0`) and an arbitrary
exponent `τ`. The Fourier coefficients satisfy `2πi (k · ω) ŵ_k = 0`, and `k · ω ≠ 0` for `k ≠ 0`
(nonresonance, which needs no estimate and no boundedness of `w`); `ŵ_0 = ⟨w⟩ = 0`. -/
theorem coh_unique_zero {n : ℕ} {τ γ r : ℝ} (hr : 0 < r) (hγ : 0 < γ) {ω : Fin n → ℝ}
    (hω : IsDiophantine γ τ ω) {w : (Fin n → ℂ) → ℂ}
    (hw : DifferentiableOn ℂ w (complexStrip n r)) (hwp : IsPeriodicOn w r) (havg : avg w = 0)
    (hω0 : ∀ θ ∈ complexStrip n r, fderiv ℂ w θ (fun l => (ω l : ℂ)) = 0) :
    ∀ θ ∈ complexStrip n r, w θ = 0 := by
  refine eq_zero_of_torusCoeff_holomorphic hr hw hwp fun k => ?_
  by_cases hk : k = 0
  · rw [hk, torusCoeff_zero]
    exact havg
  · have hD := torusCoeff_fderiv hr hw hwp (fun j => (ω j : ℂ)) k
    beta_reduce at hD
    have hz : torusCoeff (fun x : Fin n → ℝ =>
        fderiv ℂ w (fun j => (x j : ℂ)) (fun j => (ω j : ℂ))) k = 0 := by
      have : (fun x : Fin n → ℝ => fderiv ℂ w (fun j => (x j : ℂ)) (fun j => (ω j : ℂ))) =
          fun _ => 0 := funext fun x => hω0 _ (ofReal_mem_complexStrip hr x)
      rw [this]
      simp [torusCoeff, torusAverage]
    rw [hz, sum_mul_eq_flowMultiplier] at hD
    exact (mul_eq_zero.mp hD.symm).resolve_left
      ((hω.condition.nonresonant hγ).flowMultiplier_ne_zero hk)

end KAM.Head

end
