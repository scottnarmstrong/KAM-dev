/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.LatticeBW
public import KAM.Wave.KamSupport.FourierBanach
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Banach-valued Fourier-multiplier solve (blueprint-W `bpW:w4:solve`, (i) and (ii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

For complex Banach spaces `E, E'`, multipliers `T_k ∈ L(E, E')` and `u : T_s → E` holomorphic,
`1`-periodic and bounded, `homSolve T u = ∑_k T_k û_k e^{2πi⟨k,θ⟩}` (`û_k = homCoeff u k`).

* `homSolve_spec` (i): summability on `T_{s-σ}` with weight, the bound `κ B^W_σ m/α`, holomorphy,
  periodicity, coefficients `T_k û_k`;
* `homSolve_sub_le` (ii): the Lipschitz bound in the parameter `ξ`.

Linear images (iv) are in `KAM.Wave.Homological.SolveLinear`, derivatives (iii) in
`KAM.Wave.Homological.SolveDeriv`.
-/

@[expose] public section

namespace KAM.Wave

open KAM

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']

/-- The `k`-th Fourier coefficient of a function on the strip, a Bochner average over the real
torus (period one). -/
noncomputable def homCoeff (u : (Fin 2 → ℂ) → E) (k : Fin 2 → ℤ) : E :=
  torusCoeffW (fun x => u fun j => (x j : ℂ)) k

/-- **The multiplier solve** `∑_k T_k û_k e^{2πi⟨k,θ⟩}` (blueprint `bpW:w4:solve`). -/
noncomputable def homSolve (T : (Fin 2 → ℤ) → E →L[ℂ] E') (u : (Fin 2 → ℂ) → E) :
    (Fin 2 → ℂ) → E' :=
  fourierSumVec fun k => T k (homCoeff u k)

theorem norm_homCoeff_le {s m : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (k : Fin 2 → ℤ) :
    ‖homCoeff u k‖ ≤ m * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) :=
  kamFourierBanach_coeff_le hs hu hp hm k

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem homCoeff_nonneg_bound {s m : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → E}
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) : 0 ≤ m :=
  (norm_nonneg _).trans (hm 0 fun i => by simpa using hs)

omit [CompleteSpace E'] in
/-- The weighted coefficient bound `‖T_k û_k‖ e^{2π|k|₁(s-σ)} ≤ (κ m/α) A_k e^{-2π|k|₁σ}`. -/
theorem homSolve_term_le {s σ m κ α τ : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (T : E →L[ℂ] E') (k : Fin 2 → ℤ)
    (hT : ‖T‖ ≤ κ * waveA τ k / α) :
    ‖T (homCoeff u k)‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
      κ * m / α * (waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
  have hm0 := homCoeff_nonneg_bound hs hm
  have hc := norm_homCoeff_le hs hu hp hm k
  have hA := waveA_ge_one (τ := τ) k
  have hE : Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
      Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) =
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := by
    rw [← Real.exp_add]; congr 1; ring
  have hb : 0 ≤ κ * waveA τ k / α := (norm_nonneg T).trans hT
  have h1 : ‖T (homCoeff u k)‖ ≤
      κ * waveA τ k / α * (m * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) :=
    (T.le_opNorm _).trans (mul_le_mul hT hc (norm_nonneg _) hb)
  calc ‖T (homCoeff u k)‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)
      ≤ κ * waveA τ k / α * (m * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := by gcongr
    _ = κ * m / α * (waveA τ k * (Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k))) := by ring
    _ = _ := by rw [hE]

/-- **Multiplier solve, (i)** (blueprint `bpW:w4:solve` (i)): for `0 < σ < s` the series converges
absolutely and uniformly on `T_{s-σ}`, is holomorphic and `1`-periodic there, has coefficients
`T_k û_k`, and is bounded by `κ B^W_σ m / α`. -/
theorem homSolve_spec {s σ m κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ) (hσ : 0 < σ)
    (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E'} (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α)
    {u : (Fin 2 → ℂ) → E} (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) :
    Summable (fun k => ‖T k (homCoeff u k)‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)) ∧
      ∑' k, ‖T k (homCoeff u k)‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
        κ * waveBW τ σ * m / α ∧
      (∀ θ ∈ complexStrip 2 (s - σ), ‖homSolve T u θ‖ ≤ κ * waveBW τ σ * m / α) ∧
      DifferentiableOn ℂ (homSolve T u) (complexStrip 2 (s - σ)) ∧
      (∀ (i : Fin 2) z, z ∈ complexStrip 2 (s - σ) →
        homSolve T u (z + Pi.single i 1) = homSolve T u z) ∧
      ∀ k, homCoeff (homSolve T u) k = T k (homCoeff u k) := by
  have hs : 0 < s := hσ.trans hσs
  have hm0 := homCoeff_nonneg_bound hs hm
  have hc : 0 ≤ κ * m / α := by positivity
  obtain ⟨hAs, hAle⟩ := waveSum_A_le_waveBW (τ := τ) hτ hσ
  have hle : ∀ k, ‖T k (homCoeff u k)‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
      κ * m / α * (waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) :=
    fun k => homSolve_term_le hs hu hp hm (T k) k (hT k)
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ ‖T k (homCoeff u k)‖ *
      Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := fun k => by positivity
  have hsum := Summable.of_nonneg_of_le hnn hle (hAs.mul_left (κ * m / α))
  have hbd : ∑' k, ‖T k (homCoeff u k)‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤ κ * waveBW τ σ * m / α := by
    calc _ ≤ ∑' k : Fin 2 → ℤ, κ * m / α *
          (waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) :=
          Summable.tsum_le_tsum hle hsum (hAs.mul_left _)
      _ = κ * m / α * ∑' k : Fin 2 → ℤ, waveA τ k *
          Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := tsum_mul_left
      _ ≤ κ * m / α * waveBW τ σ := mul_le_mul_of_nonneg_left hAle hc
      _ = _ := by ring
  have hρ : 0 < s - σ := by linarith
  obtain ⟨_, _, hnorm, hdiff, hper, hcoef⟩ := kamFourierBanach_summation hρ hsum
  exact ⟨hsum, hbd, fun θ hθ => (hnorm θ hθ).trans hbd, hdiff, hper, hcoef⟩

/-- **Multiplier solve, (ii)** (blueprint `bpW:w4:solve` (ii)): the Lipschitz bound in the
parameter.
Here `d = |ξ - ζ|`, `(T₁, u₁)` and `(T₂, u₂)` are the data at `ξ` and `ζ`. -/
theorem homSolve_sub_le {s σ m mL κ α τ M d : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hσ : 0 < σ) (hσs : σ < s)
    {T₁ T₂ : (Fin 2 → ℤ) → E →L[ℂ] E'} (hT₁ : ∀ k, ‖T₁ k‖ ≤ κ * waveA τ k / α)
    (hT₂ : ∀ k, ‖T₂ k‖ ≤ κ * waveA τ k / α)
    (hTd : ∀ k, ‖T₁ k - T₂ k‖ ≤
      2 * κ * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d)
    {u₁ u₂ : (Fin 2 → ℂ) → E} (hu₁ : DifferentiableOn ℂ u₁ (complexStrip 2 s))
    (hu₂ : DifferentiableOn ℂ u₂ (complexStrip 2 s))
    (hp₁ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₁ (z + Pi.single i 1) = u₁ z)
    (hp₂ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₂ (z + Pi.single i 1) = u₂ z)
    (hm₁ : ∀ z ∈ complexStrip 2 s, ‖u₁ z‖ ≤ m) (hm₂ : ∀ z ∈ complexStrip 2 s, ‖u₂ z‖ ≤ m)
    (hmL : ∀ z ∈ complexStrip 2 s, ‖u₁ z - u₂ z‖ ≤ mL * d) (hmL0 : 0 ≤ mL) :
    ∀ θ ∈ complexStrip 2 (s - σ),
      ‖homSolve T₁ u₁ θ - homSolve T₂ u₂ θ‖ ≤ κ * waveBW τ σ / α * (mL + 2 * M * m / α) * d := by
  intro θ hθ
  have hs : 0 < s := hσ.trans hσs
  have hm0 := homCoeff_nonneg_bound hs hm₁
  have hρ : 0 < s - σ := by linarith
  obtain ⟨hsum₁, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT₁ hu₁ hp₁ hm₁
  obtain ⟨hsum₂, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT₂ hu₂ hp₂ hm₂
  set D : ℝ := d * (κ * mL / α + 2 * κ * M * m / α ^ 2) with hD
  have hD0 : 0 ≤ D := by positivity
  set a : (Fin 2 → ℤ) → E' := fun k => T₁ k (homCoeff u₁ k) - T₂ k (homCoeff u₂ k) with ha
  have hbound : ∀ k, ‖a k‖ ≤ D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2) *
      Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) := by
    intro k
    have hk0 := Fourier.modeSize_nonneg k
    have hA := waveA_ge_one (τ := τ) k
    have e := Real.exp_pos (-(2 * Real.pi * Fourier.modeSize k * s))
    have hc2 := norm_homCoeff_le hs hu₂ hp₂ hm₂ k
    have hc12 : ‖homCoeff u₁ k - homCoeff u₂ k‖ ≤
        mL * d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) :=
      kamFourierBanach_coeff_sub_le hs hu₁ hu₂ hp₁ hp₂ hmL k
    have hsplit : a k = T₁ k (homCoeff u₁ k - homCoeff u₂ k) +
        (T₁ k - T₂ k) (homCoeff u₂ k) := by
      simp only [ha, map_sub, sub_apply]; abel
    have hb1 : ‖T₁ k (homCoeff u₁ k - homCoeff u₂ k)‖ ≤
        κ * waveA τ k / α * (mL * d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) :=
      ((T₁ k).le_opNorm _).trans (mul_le_mul (hT₁ k) hc12 (norm_nonneg _)
        ((norm_nonneg _).trans (hT₁ k)))
    have hb2 : ‖(T₁ k - T₂ k) (homCoeff u₂ k)‖ ≤
        2 * κ * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d *
          (m * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) :=
      (((T₁ k - T₂ k).le_opNorm _).trans (mul_le_mul (hTd k) hc2 (norm_nonneg _)
        ((norm_nonneg _).trans (hTd k))))
    have hAle : waveA τ k ≤ (1 + Fourier.modeSize k) * waveA τ k ^ 2 := by nlinarith
    rw [hsplit]
    have hfin : κ * waveA τ k / α * (mL * d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) +
        2 * κ * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d *
          (m * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) ≤
        D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2) *
          Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) := by
      have h1 : κ * mL / α * waveA τ k ≤
          κ * mL / α * ((1 + Fourier.modeSize k) * waveA τ k ^ 2) :=
        mul_le_mul_of_nonneg_left hAle (by positivity)
      have h2 : 0 ≤ d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) := by positivity
      have h3 := mul_le_mul_of_nonneg_left h1 h2
      calc _ = d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
            (κ * mL / α * waveA τ k) + d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
            (2 * κ * M * m / α ^ 2 * ((1 + Fourier.modeSize k) * waveA τ k ^ 2)) := by ring
        _ ≤ d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
            (κ * mL / α * ((1 + Fourier.modeSize k) * waveA τ k ^ 2)) +
            d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
            (2 * κ * M * m / α ^ 2 * ((1 + Fourier.modeSize k) * waveA τ k ^ 2)) := by linarith
        _ = _ := by rw [hD]; ring
    exact ((norm_add_le _ _).trans (add_le_add hb1 hb2)).trans hfin
  have hg : HasSum (fun k : Fin 2 → ℤ => D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k))) (D * waveBW τ σ) :=
    ((waveBW_summable hτ hσ).hasSum).mul_left D
  have hdiff : homSolve T₁ u₁ θ - homSolve T₂ u₂ θ = ∑' k, character k θ • a k := by
    unfold homSolve fourierSumVec
    rw [← (summable_character_smul hsum₁ hθ).tsum_sub (summable_character_smul hsum₂ hθ)]
    refine tsum_congr fun k => ?_
    simp only [ha, smul_sub]
  rw [hdiff]
  have hterm : ∀ k, ‖character k θ • a k‖ ≤ D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2 *
      Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
    intro k
    refine (norm_character_smul_le a hθ k).trans ?_
    have hE : Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) =
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖a k‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)
        ≤ D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2) *
          Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := by
          gcongr; exact hbound k
      _ = _ := by rw [← hE]; ring
  refine (tsum_of_norm_bounded hg hterm).trans (le_of_eq ?_)
  rw [hD]; ring

end KAM.Wave
