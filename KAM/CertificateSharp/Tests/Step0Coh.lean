/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Step0.Coh
public import KAM.CertificateSharp.Step0.GammaInf
public import KAM.CertificateSharp.Freq.QuadraticLunar
public import KAM.Certificate.Arith.Rat

/-!
# Kernel test of the certified cohomological solve (C5 core)

A toy model on `T²` (exact `ℚ` backend), solved at the rot-frame lunar frequency
`ω = (ν₋ − 1, 1)` (`(2461/100000, 1)`-Diophantine by package C2). The residual is non-trivial:
* seven modes, mostly at the edge `6 ≤ |k|₁ ≤ 8`, plus a tiny coefficient at the worst divisor
  `k = (1, 0)` (`|k·ω| = 0.0246`);
* a zero mode, which the solve drops;
* an ℓ¹ remainder `10⁻⁸` at width `ρ = 1/10`.

* **Frequency box.** `(−0.02462 ± 10⁻⁵, 1)`, proved to contain `ω` (`toyBox_encloses`).
* **`Γ_∞(ω, 1/20) ≤ 5`.** `SupData.check` with `N = 8` (144 box modes), together with
  `supBound_sound`; the true value is `4.72`.
* **The solve.** `toy_cohSolve`: for **every** `g` with `toyG.EnclosesL1 2 (1/10) g`, the solved
  model encloses `cohSolution ω g` at width `1/20`, in ℓ¹ and in sup. Its certified bound is at
  least 200 times below the a-priori `Γ · ‖g‖` (`toy_ratio`; the exact ratio is 209, from
  `scripts/apost_sharp/step0_coh_toy.py`).

Every check is `decide +kernel`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

/-- The frequency `ω = (ν₋ − 1, 1)`. -/
def toyω : Fin 2 → ℝ := ![lunarNuMinus - 1, 1]

/-- A low-precision box `(−0.02462 ± 10⁻⁵, 1 ± 0)`. -/
def toyBox : FreqBox := [(-2462 / 100000, 1 / 100000), (1, 0)]

/-- Input weight: width `1/10`, `w = 19/10 ≥ e^{2π/10}`. -/
def toyWin : CertWeight := ⟨1 / 10, 19 / 10⟩

/-- Output weight: width `1/20`, `w = 14/10 ≥ e^{2π/20}`. -/
def toyWout : CertWeight := ⟨1 / 20, 14 / 10⟩

/-- The `Γ_∞(ω, 1/20) ≤ 5` claim. -/
def toySup : SupData :=
  { box := toyBox, γ := 2461 / 100000, δ := 1 / 20, N := 8, J := 8, E1 := 731 / 1000,
    claim := 5 }

/-- The toy model of `g` (degree `0`, ℓ¹ radius `10⁻⁸`). -/
def toyG : CertModel ℚ :=
  ⟨0, ⟨[([0, 0], ⟨1 / 10 ^ 9, 0⟩), ([1, 0], ⟨1 / 10 ^ 6, 0⟩),
    ([6, 1], ⟨3 / 1000, 1 / 1000⟩), ([5, -2], ⟨-2 / 1000, 1 / 1000⟩),
    ([7, 0], ⟨1 / 1000, -2 / 1000⟩), ([3, 4], ⟨1 / 1000, 1 / 1000⟩),
    ([-4, 3], ⟨-1 / 1000, 2 / 1000⟩), ([8, -1], ⟨2 / 1000, 0⟩)]⟩, 1 / 10 ^ 8⟩

theorem toyWin_check : checkWeight toyWin 0 12 = true := by decide +kernel

theorem toyWout_check : checkWeight toyWout 0 12 = true := by decide +kernel

theorem toySup_check : toySup.check (n := 2) = true := by decide +kernel

theorem toyG_solveCheck : solveCheck 2 toyBox toyG.poly = true := by decide +kernel

/-- The certified bound of the solution is at least 200 times below the a-priori bound. -/
theorem toy_ratio :
    ((toyG.cohSolve 2 toyBox 5 toyWout).supBound toyWout) * 200 ≤ 5 * toyG.supBound toyWin := by
  decide +kernel

theorem toyBox_encloses : FreqEncloses 2 toyBox toyω := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h0 := Real.sqrt_nonneg 5
  unfold FreqEncloses
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · norm_num [toyω, toyBox, lunarNuMinus_eq]
    rw [abs_le]
    constructor <;> nlinarith
  · norm_num [toyω, toyBox]

theorem toyω_isDiophantine : IsDiophantine ((toySup.γ : ℚ) : ℝ) 1 toyω := by
  simpa [toySup, toyω] using lunarNuMinus_sub_one_isDiophantine_exact

theorem toy_gamma : smallDivisorSup toyω (((toyWin.rho : ℚ) : ℝ) - toyWout.rho) ≤ ((5 : ℚ) : ℝ) := by
  have e : ((toyWin.rho : ℚ) : ℝ) - toyWout.rho = (toySup.δ : ℝ) := by
    norm_num [toyWin, toyWout, toySup]
  rw [e]
  exact supBound_sound toySup toySup_check toyBox_encloses toyω_isDiophantine

/-- **The certified toy solve.** For every `g` enclosed by `toyG` with an ℓ¹ remainder of width
`1/10`, the solved model encloses `𝓡 g` at width `1/20` (ℓ¹ and sup), and its certified sup bound
bounds `𝓡 g` on `T_{1/20}`. -/
theorem toy_cohSolve (g : (Fin 2 → ℂ) → ℂ) (hg : toyG.EnclosesL1 2 (toyWin.rho : ℝ) g) :
    (toyG.cohSolve 2 toyBox 5 toyWout).EnclosesL1 2 toyWout.rho (cohSolution toyω g) ∧
      (toyG.cohSolve 2 toyBox 5 toyWout).Encloses 2 toyWout.rho (cohSolution toyω g) ∧
      ∀ θ ∈ complexStrip 2 toyWout.rho,
        ‖cohSolution toyω g θ‖ ≤ val ((toyG.cohSolve 2 toyBox 5 toyWout).supBound toyWout) := by
  have hρ : ((toyWout.rho : ℚ) : ℝ) < (toyWin.rho : ℝ) := by norm_num [toyWin, toyWout]
  have hγ : (0 : ℝ) < ((toySup.γ : ℚ) : ℝ) := by norm_num [toySup]
  have h1 := hg.cohSolve toyBox_encloses toyω_isDiophantine hγ zero_le_one toyWout_check hρ
    toy_gamma toyG_solveCheck
  have h2 := hg.cohSolve_encloses toyBox_encloses toyω_isDiophantine hγ zero_le_one toyWout_check
    hρ toy_gamma toyG_solveCheck
  exact ⟨h1, h2, fun θ hθ => CertModel.norm_le_supBound toyWout_check h2 hθ⟩

end KAM.CertificateSharp

end
