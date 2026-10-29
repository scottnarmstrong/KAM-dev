/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Hamiltonian.Transport

/-!
# Period conversion bundle

`stepP:p1:pc-c`: one-line export of all claims of `bpP:p1:period-convert` (c), together with (d),
assembled from the landed conversion results of `KAM.Planetary.Hamiltonian.Transport` and
`KAM.Planetary.Hamiltonian.Chart`.
-/

public section

open Set Real Function

namespace KAM.Planetary

open KAM

/-- `stepP:p1:pc-c`: for `K(θ) = κ̃(2πθ)`, analyticity, the derivative, injectivity of the
derivative, the symplectic pullback (and its vanishing), the lattice clause for any family `T`,
injectivity modulo the lattice and the flow clause all transfer by composition with the bijection
`θ ↦ 2πθ`; and (d) the frozen fast shift is `S_{2π}` of the integer shift. -/
theorem period_convert_bundle {d a b : ℕ} (κ : (Fin d → ℝ) → Phase d) (omega : Fin d → ℝ)
    (T : (Fin d → ℤ) → Phase d) :
    (AnalyticOnNhd ℝ (periodOne κ) Set.univ ↔ AnalyticOnNhd ℝ κ Set.univ) ∧
    (∀ θ, fderiv ℝ (periodOne κ) θ = (2 * Real.pi) • fderiv ℝ κ ((2 * Real.pi) • θ)) ∧
    (∀ θ, Function.Injective (fderiv ℝ (periodOne κ) θ) ↔
      Function.Injective (fderiv ℝ κ ((2 * Real.pi) • θ))) ∧
    (∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v) =
      (2 * Real.pi) * (2 * Real.pi) *
        symplecticForm (fderiv ℝ κ ((2 * Real.pi) • θ) u)
          (fderiv ℝ κ ((2 * Real.pi) • θ) v)) ∧
    ((∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v) = 0) ↔
      ∀ ϑ u v, symplecticForm (fderiv ℝ κ ϑ u) (fderiv ℝ κ ϑ v) = 0) ∧
    ((∀ θ (k : Fin d → ℤ), periodOne κ (θ + fun i => (k i : ℝ)) = periodOne κ θ + T k) ↔
      ∀ ϑ (k : Fin d → ℤ), κ (ϑ + fun i => 2 * Real.pi * (k i : ℝ)) = κ ϑ + T k) ∧
    ((∀ θ θ', periodOne κ θ = periodOne κ θ' →
        ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ↔
      ∀ ϑ ϑ', κ ϑ = κ ϑ' → ∃ k : Fin d → ℤ, ϑ' = ϑ + fun i => 2 * Real.pi * (k i : ℝ)) ∧
    (∀ θ (v : Phase d) (t : ℝ),
      HasDerivAt (fun s : ℝ => periodOne κ (θ + s • (2 * Real.pi)⁻¹ • omega)) v t ↔
        HasDerivAt (fun s : ℝ => κ ((2 * Real.pi) • θ + s • omega)) v t) ∧
    (∀ k : Fin a → ℤ, fastShift (b := b) k =
      angleScale (2 * Real.pi) (Fin.append (fun i => (k i : ℝ)) (0 : Fin b → ℝ), 0)) := by
  have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hkey : ∀ θ, Function.Injective (fderiv ℝ (periodOne κ) θ) ↔
      Function.Injective (fderiv ℝ κ ((2 * Real.pi) • θ)) := by
    intro θ
    rw [fderiv_periodOne]
    constructor
    · intro h a b hab
      exact h (by simp [hab])
    · intro h a b hab
      apply h
      simpa [hπ] using hab
  have hsk : ∀ θ u v, symplecticForm (fderiv ℝ (periodOne κ) θ u) (fderiv ℝ (periodOne κ) θ v)
      = (2 * Real.pi) * (2 * Real.pi) * symplecticForm (fderiv ℝ κ ((2 * Real.pi) • θ) u)
        (fderiv ℝ κ ((2 * Real.pi) • θ) v) := by
    intro θ u v
    rw [fderiv_periodOne]
    simp only [symplecticForm, smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsc : ∀ ϑ : Fin d → ℝ, (2 * Real.pi) • (2 * Real.pi)⁻¹ • ϑ = ϑ := fun ϑ => by
    rw [smul_smul, mul_inv_cancel₀ hπ, one_smul]
  refine ⟨analyticOnNhd_periodOne_iff κ, fderiv_periodOne κ, hkey, hsk, ?_,
    periodOne_lattice_iff κ T, periodOne_injMod_iff κ,
    fun θ v t => periodOne_hasDerivAt_iff κ omega θ v t, fun k => fastShift_eq_angleScale k⟩
  constructor
  · intro h ϑ u v
    have := h ((2 * Real.pi)⁻¹ • ϑ) u v
    rw [hsk, hsc] at this
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hπ hπ)
  · intro h θ u v
    rw [hsk, h, mul_zero]

end KAM.Planetary
