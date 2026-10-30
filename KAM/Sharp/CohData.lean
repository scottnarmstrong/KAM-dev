/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Apost.Tools
public import KAM.Strip.CohomologicalRussmann
public import KAM.Strip.CohomologicalParseval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small-divisor data for the sharp a-posteriori theorems

`KAM.Sharp.CohData n τ κ cR` (blueprint `bp:p2s:cohdata`) packages the size clauses of the
cohomological estimate: for `0 < δ ≤ 1`, `‖𝓡 g‖ ≤ c_R γ⁻¹ δ^{-κ} H` on `T_{r-δ}` and the a-priori
bound `‖u‖ ≤ c_R γ⁻¹ δ^{-κ} H`. Instances:

* `cohData_russmann`: `κ = τ`, `c_R = cohConstR n τ` (headline);
* `cohData_parseval`: `κ = τ + n/2`, `c_R = cohConstP n τ`;
* `cohData_crude`: `κ = τ + n`, `c_R = cohConst n τ`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open KAM.Torus KAM.Apost

namespace KAM.Sharp

/-- Blueprint `bp:p2s:cohdata`: `(κ, c_R)` is small-divisor data for `(n, τ)`. The fields are the
size clauses of `KAM.cohomological` (vector solution) and `KAM.cohomological_operator` (a-priori
bound) with `Γ_δ = c_R γ⁻¹ δ^{-κ}`, for `0 < δ ≤ 1`; the qualitative clauses come from
`KAM.cohomological` itself (`0 ≤ τ`). Instances: `cohData_russmann`, `cohData_parseval`,
`cohData_crude`. -/
structure CohData (n : ℕ) (τ κ cR : ℝ) : Prop where
  tau_nonneg : 0 ≤ τ
  one_le_kappa : 1 ≤ κ
  cR_pos : 0 < cR
  sol : ∀ {γ : ℝ} {ω : Fin n → ℝ}, 0 < γ → IsDiophantine γ τ ω → ∀ {r δ : ℝ}, 0 < δ → δ ≤ 1 →
    δ < r → ∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (H : ℝ),
      DifferentiableOn ℂ g (complexStrip n r) → IsPeriodicOn g r →
      (∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) → avg g = 0 →
      ∀ θ ∈ complexStrip n (r - δ), ‖cohR ω g θ‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * H
  apriori : ∀ {γ : ℝ} {ω : Fin n → ℝ}, 0 < γ → IsDiophantine γ τ ω → ∀ {r δ : ℝ}, 0 < δ →
    δ ≤ 1 → δ < r → ∀ {p q : ℕ} (u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (H : ℝ),
      DifferentiableOn ℂ u (complexStrip n r) → IsPeriodicOn u r → avg u = 0 →
      (∀ θ ∈ complexStrip n r, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) →
      ∀ θ ∈ complexStrip n (r - δ), ‖u θ‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * H

/-- `c / (γ δ^κ) H = c γ⁻¹ δ^{-κ} H`. -/
private theorem div_eq_cR_form {c γ δ κ H : ℝ} (hδ : 0 < δ) :
    c / (γ * δ ^ κ) * H = c * γ⁻¹ * δ ^ (-κ) * H := by
  rw [Real.rpow_neg hδ.le, div_eq_mul_inv, mul_inv]
  ring

/-- `(a τ / (e π))^(b τ) > 0` for `τ ≥ 0` (the base vanishes only for `τ = 0`, where the power
is `1`). -/
private theorem rpow_tau_pos {a b τ : ℝ} (ha : 0 < a) (hτ : 0 ≤ τ) :
    0 < (a * τ / (Real.exp 1 * Real.pi)) ^ (b * τ) := by
  rcases hτ.eq_or_lt with h | h
  · subst h; simp
  · positivity

/-- Small-divisor data from the two bounds in the form `c / (γ δ^κ)`. -/
private theorem CohData.of_bounds {n : ℕ} {τ κ c : ℝ} (hτ : 0 ≤ τ) (hκ : 1 ≤ κ) (hc : 0 < c)
    (hsol : ∀ {γ : ℝ} {ω : Fin n → ℝ}, 0 < γ → IsDiophantine γ τ ω → ∀ {r δ : ℝ}, 0 < δ →
      δ < r → ∀ {p : ℕ} (g : (Fin n → ℂ) → Fin p → ℂ) (H : ℝ),
        DifferentiableOn ℂ g (complexStrip n r) → IsPeriodicOn g r →
        (∀ θ ∈ complexStrip n r, ‖g θ‖ ≤ H) → avg g = 0 →
        ∀ θ ∈ complexStrip n (r - δ), ‖cohR ω g θ‖ ≤ c / (γ * δ ^ κ) * H)
    (hap : ∀ {γ : ℝ} {ω : Fin n → ℝ}, 0 < γ → IsDiophantine γ τ ω → ∀ {r δ : ℝ}, 0 < δ →
      δ < r → ∀ {p q : ℕ} (u : (Fin n → ℂ) → Matrix (Fin p) (Fin q) ℂ) (H : ℝ),
        DifferentiableOn ℂ u (complexStrip n r) → IsPeriodicOn u r → avg u = 0 →
        (∀ θ ∈ complexStrip n r, ‖fderiv ℂ u θ (fun l => (ω l : ℂ))‖ ≤ H) →
        ∀ θ ∈ complexStrip n (r - δ), ‖u θ‖ ≤ c / (γ * δ ^ κ) * H) :
    CohData n τ κ c where
  tau_nonneg := hτ
  one_le_kappa := hκ
  cR_pos := hc
  sol := by
    intro γ ω hγ hω r δ hδ _ hδr p g H hg hp hH h0 θ hθ
    rw [← div_eq_cR_form hδ]
    exact hsol hγ hω hδ hδr g H hg hp hH h0 θ hθ
  apriori := by
    intro γ ω hγ hω r δ hδ _ hδr p q u H hu hp h0 hH θ hθ
    rw [← div_eq_cR_form hδ]
    exact hap hγ hω hδ hδr u H hu hp h0 hH θ hθ

/-- Blueprint `bp:p2s:cohdata-russmann` (from `KAM.cohomological_russmann`,
`KAM.cohomological_operator_russmann`). -/
theorem cohData_russmann {n : ℕ} {τ : ℝ} (hτ : 1 ≤ τ) : CohData n τ τ (cohConstR n τ) := by
  have hτ0 : 0 ≤ τ := by linarith
  refine CohData.of_bounds hτ0 hτ ?_ ?_ ?_
  · unfold cohConstR
    have := rpow_tau_pos (a := 2) (b := 2) (τ := τ) two_pos hτ0
    have : 0 < 6 * (1 + 2 ^ τ) * (2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) := by positivity
    positivity
  · intro γ ω hγ hω r δ hδ hδr p g H hg hp hH h0 θ hθ
    exact ((cohomological_russmann hω hγ hτ0 hδ hδr).2 g H hg hp hH h0).2.2.2.2.1 θ hθ
  · intro γ ω hγ hω r δ hδ hδr p q u H hu hp h0 hH θ hθ
    exact (cohomological_operator_russmann hω hγ hτ0 hδ hδr).2 u H hu hp h0 hH θ hθ

/-- Blueprint `bp:p2s:cohdata-parseval` (from `KAM.cohomological_parseval`,
`KAM.cohomological_operator_parseval`). -/
theorem cohData_parseval {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ) (hκ : 1 ≤ τ + (n : ℝ) / 2) :
    CohData n τ (τ + (n : ℝ) / 2) (cohConstP n τ) := by
  refine CohData.of_bounds hτ hκ ?_ ?_ ?_
  · unfold cohConstP
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have := rpow_tau_pos (a := 2) (b := 2) (τ := τ) two_pos hτ
    have : 0 < 2 ^ n * ((2 * τ / (Real.exp 1 * Real.pi)) ^ (2 * τ) *
        (8 * (n : ℝ) / Real.pi) ^ n) := by positivity
    positivity
  · intro γ ω hγ hω r δ hδ hδr p g H hg hp hH h0 θ hθ
    exact ((cohomological_parseval hω hγ hτ hδ hδr).2 g H hg hp hH h0).2.2.2.2.1 θ hθ
  · intro γ ω hγ hω r δ hδ hδr p q u H hu hp h0 hH θ hθ
    exact (cohomological_operator_parseval hω hγ hτ hδ hδr).2 u H hu hp h0 hH θ hθ

/-- Blueprint `bp:p2s:cohdata-crude` (from `KAM.cohomological`, `KAM.cohomological_operator`). -/
theorem cohData_crude {n : ℕ} (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 ≤ τ) :
    CohData n τ (τ + n) (cohConst n τ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine CohData.of_bounds hτ (by linarith) ?_ ?_ ?_
  · unfold cohConst
    have := rpow_tau_pos (a := 1) (b := 1) (τ := τ) one_pos hτ
    simp only [one_mul] at this
    positivity
  · intro γ ω hγ hω r δ hδ hδr p g H hg hp hH h0 θ hθ
    exact ((KAM.cohomological hω hγ hτ hδ hδr).2 g H hg hp hH h0).2.2.2.2.1 θ hθ
  · intro γ ω hγ hω r δ hδ hδr p q u H hu hp h0 hH θ hθ
    exact (KAM.cohomological_operator hω hγ hτ hδ hδr).2 u H hu hp h0 hH θ hθ

end KAM.Sharp

end
