/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Symplectic

/-!
# Cross jet: first orbit variation in `ξ`

Blueprint P, Part 8, `stepP:p8:qf-cross` (first orbit variations, `bpP:p7:regular-kepler` (a)):
along `ξ = s`, `η = 0` the Poincaré chart position of a planet with action `Λ` has, at `s = 0`,
the derivative `(a/√Λ)·(-1 - sin² λ, sin λ cos λ)` with `a = Λ²/(m²κ)`. In polar form this is
`r' = -a cos λ`, `θ' = 2 sin λ` (times `1/√Λ`). The proof differentiates the explicit chart formula
along the line, using `∂_v F = (sin F, -cos F)/J` from `fderiv_keplerLong_vec`.
-/

@[expose] public noncomputable section
open KAM KAM.Kepler
namespace KAM.Planetary
namespace SecularForm
/-- The prefactor `√((1 - Γ/(2Λ))/Λ)` of `poincareV` along the line `ξ = s`, `η = 0`. -/
noncomputable def lineC (Λ s : ℝ) : ℝ := √((1 - s ^ 2 / 2 / (2 * Λ)) / Λ)

/-- The chart position along the line `ξ = s`, `η = 0`, written out. -/
theorem poincare_line_fst (m κ Λ l s : ℝ) :
    (poincare m κ (![l, s], ![Λ, 0])).1 =
      ![Λ ^ 2 / (m ^ 2 * κ) * ((1 - s ^ 2 / 2 / Λ) * Real.cos (keplerLong l ![lineC Λ s * s, 0])
          - lineC Λ s * s + (lineC Λ s * s * Real.cos (keplerLong l ![lineC Λ s * s, 0]) /
            (1 + (1 - s ^ 2 / 2 / Λ))) * (lineC Λ s * s)),
        Λ ^ 2 / (m ^ 2 * κ) * ((1 - s ^ 2 / 2 / Λ) * Real.sin (keplerLong l ![lineC Λ s * s,
            0]))] := by
  ext c
  fin_cases c <;>
  simp [poincare, poincareK, poincareV, poincareGamma, poincareF, orbitalUnit, planeDot,
    Fin.sum_univ_two, lineC]

/-- The prefactor is stationary at `s = 0`. -/
theorem hasDerivAt_lineC {Λ : ℝ} (hΛ : 0 < Λ) :
    HasDerivAt (lineC Λ) 0 0 := by
  unfold lineC
  have hg : HasDerivAt (fun s : ℝ => (1 - s ^ 2 / 2 / (2 * Λ)) / Λ) 0 0 := by
    have := (((hasDerivAt_pow 2 (0:ℝ)).div_const 2).div_const (2 * Λ)).const_sub 1 |>.div_const Λ
    simpa using this
  have hpos : 0 < (1 - (0:ℝ) ^ 2 / 2 / (2 * Λ)) / Λ := by simp; positivity
  have := (hg.sqrt hpos.ne')
  simpa using this

/-- The prefactor at `s = 0`. -/
theorem lineC_zero {Λ : ℝ} : lineC Λ 0 = 1 / √Λ := by
  simp [lineC, Real.sqrt_inv]

/-- First variation of the eccentric longitude: `∂_s F = sin λ/√Λ` at `s = 0`. -/
theorem hasDerivAt_keplerLong_line {Λ : ℝ} (hΛ : 0 < Λ) (l : ℝ) :
    HasDerivAt (fun s => keplerLong l ![lineC Λ s * s, 0]) (Real.sin l / √Λ) 0 := by
  have hv0 : planeLength (![0, 0] : Fin 2 → ℝ) < 1 := by
    simp [planeLength, planeSq, Fin.sum_univ_two]
  have hv : planeLength (![lineC Λ 0 * 0, 0] : Fin 2 → ℝ) < 1 := by simpa using hv0
  have hA := (analyticOnNhd_keplerLong (l, (![lineC Λ 0 * 0, 0] : Fin 2 → ℝ)) hv).differentiableAt
  have hg : DifferentiableAt ℝ (fun u : Fin 2 → ℝ => keplerLong l u) ![lineC Λ 0 * 0, 0] :=
    hA.comp _ ((differentiableAt_const l).prodMk differentiableAt_id)
  have hcurve : HasDerivAt (fun s : ℝ => (![lineC Λ s * s, 0] : Fin 2 → ℝ))
      (![1 / √Λ, 0]) 0 := by
    rw [hasDerivAt_pi]
    intro c
    fin_cases c
    · have := (hasDerivAt_lineC hΛ).mul (hasDerivAt_id (0:ℝ))
      exact this.congr_deriv (by simp [lineC_zero])
    · simpa using hasDerivAt_const (0:ℝ) (0:ℝ)
  have hcomp := hg.hasFDerivAt.comp_hasDerivAt (0:ℝ) hcurve
  refine hcomp.congr_deriv ?_
  have hfd := (fderiv_keplerLong_vec (v := ![lineC Λ 0 * 0, 0]) hv l).1
  have hvec : (![1 / √Λ, 0] : Fin 2 → ℝ) = (1 / √Λ) • (Pi.single 0 1 : Fin 2 → ℝ) := by
    ext c; fin_cases c <;> simp
  rw [hvec, map_smul, hfd]
  have h0 : (![0, 0] : Fin 2 → ℝ) = 0 := by ext c; fin_cases c <;> rfl
  simp [h0, keplerLong_zero_vec, keplerJac, planeDot, div_eq_mul_inv, mul_comm]

/-- `stepP:p8:qf-cross`, first orbit variation: `∂_ξ q = (a/√Λ)(-1 - sin² λ, sin λ cos λ)`. -/
theorem hasDerivAt_poincare_fst_xi {m κ Λ : ℝ} (hΛ : 0 < Λ) (l : ℝ) :
    HasDerivAt (fun s => (poincare m κ (![l, s], ![Λ, 0])).1)
      ((Λ ^ 2 / (m ^ 2 * κ) / √Λ) • (![-1 - Real.sin l ^ 2, Real.sin l * Real.cos l] : Fin 2 →
          ℝ)) 0 := by
  simp_rw [poincare_line_fst]
  have hF := hasDerivAt_keplerLong_line hΛ l
  have hC := hasDerivAt_lineC hΛ
  have hK : HasDerivAt (fun s : ℝ => 1 - s ^ 2 / 2 / Λ) 0 0 := by
    have := ((((hasDerivAt_pow 2 (0:ℝ)).div_const 2).div_const Λ)).const_sub 1
    simpa using this
  have hcs : HasDerivAt (fun s : ℝ => lineC Λ s * s) (1 / √Λ) 0 := by
    have := hC.mul (hasDerivAt_id (0:ℝ))
    exact this.congr_deriv (by simp [lineC_zero])
  have hcos := hF.cos
  have hsin := hF.sin
  have hF0 : keplerLong l ![lineC Λ 0 * 0, 0] = l := by
    have h0 : (![lineC Λ 0 * 0, 0] : Fin 2 → ℝ) = 0 := by ext c; fin_cases c <;> simp
    rw [h0, keplerLong_zero_vec]
  have hden : HasDerivAt (fun s : ℝ => 1 + (1 - s ^ 2 / 2 / Λ)) 0 0 := hK.const_add 1
  have hq := (hcs.mul hcos).div hden (by simp)
  rw [hasDerivAt_pi]
  intro c
  fin_cases c
  · have h := ((((hK.mul hcos).sub hcs).add (hq.mul hcs))).const_mul (Λ ^ 2 / (m ^ 2 * κ))
    refine h.congr_deriv ?_
    simp only [hF0]
    simp [lineC_zero]
    ring
  · have h := (hK.mul hsin).const_mul (Λ ^ 2 / (m ^ 2 * κ))
    refine h.congr_deriv ?_
    simp only [hF0]
    simp
    ring

end SecularForm
end KAM.Planetary
