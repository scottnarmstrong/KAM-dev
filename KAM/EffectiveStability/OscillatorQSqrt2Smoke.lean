/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.OscillatorCheck
public import KAM.EffectiveStability.Poly.QSqrt2Smoke

/-!
# `ℚ(√2)` smoke test of the one-step checker (track B, B3-CHAINK)

`checkOscStep` over `QSqrt2` on tiny Hénon–Heiles-shaped data: `n = 2`,
`H = I₀ - (√2/2) I₁ + (1/1000)(q₀² q₁ - q₁³/3)`, `χ = 0`, `Nact = q₀ - (√2/2) q₁`, `P` the cubic
part, `L = 1`. The kernel check `hhStepCert_check` is by `decide +kernel`; the soundness theorem
`checkOscStep_sound` then applies over `ℚ(√2)` (the instances `Algebra QSqrt2 ℝ`, `Algebra QSqrt2 ℂ`
and `CertNormLe` of B3-COEF).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

open Set CartPoly

/-- The small cubic part `(1/1000)(q₀² q₁ - q₁³/3)` over `ℚ(√2)`. -/
def hhStepCubic : CartPolyK QSqrt2 := cartSmul (⟨1 / 1000, 0⟩ : QSqrt2) hhCubicSmoke

/-- The normal form `q₀ - (√2/2) q₁` (its action substitution is `I₀ - (√2/2) I₁`). -/
def hhStepNact : CartPolyK QSqrt2 :=
  cartAdd (cartQVar 0) (cartSmul (⟨0, -1 / 2⟩ : QSqrt2) (cartQVar 1))

/-- One-step certificate over `ℚ(√2)`: `χ = 0`, `H = Nact ∘ I + P`, `L = 1`. -/
def hhStepCert : OscStepCertK QSqrt2 2 where
  H := cartAdd hhQuadSmoke hhStepCubic
  χ := []
  Nact := hhStepNact
  P := hhStepCubic
  L := 1
  ρ := 5
  δ := 1
  δc := 1
  ε := 0
  εb := 1
  T := 1
  a := [0, 0]
  b := [1, 1]
  η := [1 / 2, 1 / 2]
  r := [2, 2]

/-- The `ℚ(√2)` one-step certificate is accepted by the kernel. -/
theorem hhStepCert_check : checkOscStep hhStepCert = true := by decide +kernel

/-- The accepted `ℚ(√2)` certificate yields the action-drift statement for the physical flow. -/
theorem hhStepCert_drift (w₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hw₀ : ∀ j, KAM.Planetary.oscillatorAction w₀.2 w₀.1 j ≤ 0) :
    ∃ z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ), ∀ t : ℝ, |t| ≤ 1 → ∀ j,
      |KAM.Planetary.oscillatorAction (stepChartInv ([] : CartPolyK QSqrt2) (5 : ℝ) (z t)).2
          (stepChartInv ([] : CartPolyK QSqrt2) (5 : ℝ) (z t)).1 j -
        KAM.Planetary.oscillatorAction w₀.2 w₀.1 j| ≤ 1 / 2 * |t| := by
  obtain ⟨T₁, -, z, -, -, -, hb⟩ := checkOscStep_sound hhStepCert hhStepCert_check w₀
    (fun j => by fin_cases j <;> simpa [hhStepCert] using hw₀ _)
  refine ⟨z, fun t ht j => ?_⟩
  have := ((hb t (by simpa [hhStepCert] using ht)).2 j).1
  fin_cases j <;> simpa [hhStepCert] using this

end KAM.EffectiveStability
