/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.SolveDeriv
public import KAM.Wave.KamStep.LatticeBN
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Angle derivatives of a solve from its coefficients (`bpW:w5:w4-modified`, step `m-act`)

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

Step `m-act` bounds `∂_{θ_i} Q_F` by differentiating the solved series termwise instead of
solving for the derivative data (W4's bilinear route is not available for the modified divisors).
For multipliers `‖T_k‖ ≤ κA_k/α` and data `‖u‖ ≤ m` on `T_s`:

* `norm_homPartial_homSolve_le`: `‖∂_{θ_i} 𝒮u(θ)‖ ≤ 2πκ B^W_σ m/α` on `T_{s-σ}`
  (`|k_i|A_k ≤ (1+|k|₁)A_k²`);
* `norm_homPartial_homSolve_sub_le`: for two parameters, with
  `‖T₁-T₂‖ ≤ 2κ(1+|k|₁)A_k²Md/α²` and `‖u₁-u₂‖ ≤ m^L d`,
  `‖∂_{θ_i}(𝒮₁u₁ - 𝒮₂u₂)(θ)‖ ≤ 2πκ B^♮_σ (m^L + 2Mm/α) d/α`: the extra factor `|k|₁` of the
  differentiated series is why `B^♮_σ` replaces `B^W_σ`.
-/

@[expose] public section

namespace KAM.Wave

open KAM

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [CompleteSpace E']

theorem norm_two_pi_I_coord (k : Fin 2 → ℤ) (i : Fin 2) :
    ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ ≤ 2 * Real.pi * Fourier.modeSize k := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  have hπ : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2, hπ]
  have hk : ‖((k i : ℤ) : ℂ)‖ = |(k i : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  rw [hk]
  exact mul_le_mul_of_nonneg_left (Fourier.abs_coord_le_modeSize k i) (by positivity)

/-- `|k|₁ A_k ≤ (1+|k|₁)A_k²`. -/
theorem modeSize_mul_waveA_le (τ : ℝ) (k : Fin 2 → ℤ) :
    Fourier.modeSize k * waveA τ k ≤ (1 + Fourier.modeSize k) * waveA τ k ^ 2 := by
  have hA := waveA_ge_one (τ := τ) k
  have hk := Fourier.modeSize_nonneg k
  have h1 : waveA τ k ≤ waveA τ k ^ 2 := by nlinarith
  have h2 : Fourier.modeSize k * waveA τ k ≤ Fourier.modeSize k * waveA τ k ^ 2 :=
    mul_le_mul_of_nonneg_left h1 hk
  nlinarith [sq_nonneg (waveA τ k)]

/-- The termwise derivative of a Fourier series in the direction `e_i`, when both coefficient
families are weighted-summable at `ρ`. -/
theorem homPartial_fourierSumVec {ρ : ℝ} {a : (Fin 2 → ℤ) → E'} (i : Fin 2)
    (ha : Summable fun k => ‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k))
    (hb : Summable fun k => ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • a k‖ *
      Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 ρ) :
    homPartial i (fourierSumVec a) θ =
      fourierSumVec (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • a k) θ :=
  fderiv_fourierSumVec_single ha hb hθ

/-- **Step `m-act`, uniform part**: `‖∂_{θ_i} 𝒮u(θ)‖ ≤ 2πκ B^W_σ m/α` on `T_{s-σ}`. -/
theorem norm_homPartial_homSolve_le {s σ m κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) {T : (Fin 2 → ℤ) → E →L[ℂ] E'}
    (hT : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α) {u : (Fin 2 → ℂ) → E}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) (i : Fin 2) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 (s - σ)) :
    ‖homPartial i (homSolve T u) θ‖ ≤ 2 * Real.pi * κ * waveBW τ σ * m / α := by
  have hs : 0 < s := hσ.trans hσs
  have hm0 := homCoeff_nonneg_bound hs hm
  have hρ : 0 < s - σ := by linarith
  set a : (Fin 2 → ℤ) → E' := fun k => T k (homCoeff u k) with ha_def
  obtain ⟨hsum, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT hu hp hm
  have hC : 0 ≤ 2 * Real.pi * (κ * m / α) := by positivity
  have hle : ∀ k, ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • a k‖ *
      Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
      2 * Real.pi * (κ * m / α) * ((1 + Fourier.modeSize k) * waveA τ k ^ 2 *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
    intro k
    have h1 := homSolve_term_le (σ := σ) hs hu hp hm (T k) k (hT k)
    have h2 := norm_two_pi_I_coord k i
    have h3 := modeSize_mul_waveA_le τ k
    have he := Real.exp_pos (-(2 * Real.pi * σ) * Fourier.modeSize k)
    have hk0 := Fourier.modeSize_nonneg k
    rw [norm_smul, mul_assoc]
    calc ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ *
          (‖a k‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k))
        ≤ (2 * Real.pi * Fourier.modeSize k) *
          (κ * m / α * (waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k))) :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
      _ = 2 * Real.pi * (κ * m / α) * ((Fourier.modeSize k * waveA τ k) *
          Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact mul_le_mul_of_nonneg_right h3 he.le
  have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • a k‖ *
      Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := fun k => by positivity
  have hBs := (waveBW_summable hτ hσ).mul_left (2 * Real.pi * (κ * m / α))
  have hbsum := Summable.of_nonneg_of_le hnn hle hBs
  rw [show homSolve T u = fourierSumVec a from rfl, homPartial_fourierSumVec i hsum hbsum hθ]
  refine ((kamFourierBanach_summation hρ hbsum).2.2.1 θ hθ).trans ?_
  calc _ ≤ ∑' k : Fin 2 → ℤ, 2 * Real.pi * (κ * m / α) * ((1 + Fourier.modeSize k) *
        waveA τ k ^ 2 * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) :=
        Summable.tsum_le_tsum hle hbsum hBs
    _ = 2 * Real.pi * (κ * m / α) * waveBW τ σ := by rw [tsum_mul_left]; rfl
    _ = _ := by ring

/-- **Step `m-act`, Lipschitz part**: for the data `(T₁,u₁)`, `(T₂,u₂)` at two parameters,
`‖∂_{θ_i}(𝒮₁u₁ - 𝒮₂u₂)(θ)‖ ≤ 2πκ B^♮_σ (m^L + 2Mm/α) d/α` on `T_{s-σ}`. -/
theorem norm_homPartial_homSolve_sub_le {s σ m mL κ α τ M d : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α)
    (hκ : 1 ≤ κ) (hM : 0 ≤ M) (hd : 0 ≤ d) (hσ : 0 < σ) (hσs : σ < s)
    {T₁ T₂ : (Fin 2 → ℤ) → E →L[ℂ] E'} (hT₁ : ∀ k, ‖T₁ k‖ ≤ κ * waveA τ k / α)
    (hT₂ : ∀ k, ‖T₂ k‖ ≤ κ * waveA τ k / α)
    (hTd : ∀ k, ‖T₁ k - T₂ k‖ ≤
      2 * κ * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * M / α ^ 2 * d)
    {u₁ u₂ : (Fin 2 → ℂ) → E} (hu₁ : DifferentiableOn ℂ u₁ (complexStrip 2 s))
    (hu₂ : DifferentiableOn ℂ u₂ (complexStrip 2 s))
    (hp₁ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₁ (z + Pi.single i 1) = u₁ z)
    (hp₂ : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u₂ (z + Pi.single i 1) = u₂ z)
    (hm₁ : ∀ z ∈ complexStrip 2 s, ‖u₁ z‖ ≤ m) (hm₂ : ∀ z ∈ complexStrip 2 s, ‖u₂ z‖ ≤ m)
    (hmL : ∀ z ∈ complexStrip 2 s, ‖u₁ z - u₂ z‖ ≤ mL * d) (hmL0 : 0 ≤ mL) (i : Fin 2)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    ‖homPartial i (homSolve T₁ u₁) θ - homPartial i (homSolve T₂ u₂) θ‖ ≤
      2 * Real.pi * κ * waveBN τ σ / α * (mL + 2 * M * m / α) * d := by
  have hs : 0 < s := hσ.trans hσs
  have hm0 := homCoeff_nonneg_bound hs hm₁
  have hρ : 0 < s - σ := by linarith
  set a₁ : (Fin 2 → ℤ) → E' := fun k => T₁ k (homCoeff u₁ k) with ha₁
  set a₂ : (Fin 2 → ℤ) → E' := fun k => T₂ k (homCoeff u₂ k) with ha₂
  obtain ⟨hsum₁, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT₁ hu₁ hp₁ hm₁
  obtain ⟨hsum₂, -⟩ := homSolve_spec hτ hα hκ hσ hσs hT₂ hu₂ hp₂ hm₂
  -- the derivative series of each solve
  have hb : ∀ (T : (Fin 2 → ℤ) → E →L[ℂ] E') (u : (Fin 2 → ℂ) → E),
      (∀ k, ‖T k‖ ≤ κ * waveA τ k / α) → DifferentiableOn ℂ u (complexStrip 2 s) →
      (∀ (i : Fin 2) z, z ∈ complexStrip 2 s → u (z + Pi.single i 1) = u z) →
      (∀ z ∈ complexStrip 2 s, ‖u z‖ ≤ m) →
      Summable fun k => ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • T k (homCoeff u k)‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := by
    intro T u hT hu hp hm
    have hle : ∀ k, ‖(2 * Real.pi * Complex.I * (k i : ℂ)) • T k (homCoeff u k)‖ *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) ≤
        2 * Real.pi * (κ * m / α) * ((1 + Fourier.modeSize k) * waveA τ k ^ 2 *
          Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
      intro k
      have h1 := homSolve_term_le (σ := σ) hs hu hp hm (T k) k (hT k)
      have h2 := norm_two_pi_I_coord k i
      have h3 := modeSize_mul_waveA_le τ k
      have he := Real.exp_pos (-(2 * Real.pi * σ) * Fourier.modeSize k)
      have hk0 := Fourier.modeSize_nonneg k
      have hC : 0 ≤ 2 * Real.pi * (κ * m / α) := by positivity
      rw [norm_smul, mul_assoc]
      calc ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ *
            (‖T k (homCoeff u k)‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k))
          ≤ (2 * Real.pi * Fourier.modeSize k) *
            (κ * m / α * (waveA τ k * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k))) :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = 2 * Real.pi * (κ * m / α) * ((Fourier.modeSize k * waveA τ k) *
            Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            exact mul_le_mul_of_nonneg_right h3 he.le
    have hnn : ∀ k : Fin 2 → ℤ, 0 ≤ ‖(2 * Real.pi * Complex.I * (k i : ℂ)) •
        T k (homCoeff u k)‖ * Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) :=
      fun k => by positivity
    exact Summable.of_nonneg_of_le hnn hle ((waveBW_summable hτ hσ).mul_left _)
  have hb₁ := hb T₁ u₁ hT₁ hu₁ hp₁ hm₁
  have hb₂ := hb T₂ u₂ hT₂ hu₂ hp₂ hm₂
  rw [show homSolve T₁ u₁ = fourierSumVec a₁ from rfl, show homSolve T₂ u₂ = fourierSumVec a₂ from
    rfl, homPartial_fourierSumVec i hsum₁ hb₁ hθ, homPartial_fourierSumVec i hsum₂ hb₂ hθ]
  -- the coefficient differences
  set D : ℝ := d * (κ * mL / α + 2 * κ * M * m / α ^ 2) with hD
  have hD0 : 0 ≤ D := by positivity
  have hbound : ∀ k, ‖a₁ k - a₂ k‖ ≤ D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2) *
      Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) := by
    intro k
    have hk0 := Fourier.modeSize_nonneg k
    have hA := waveA_ge_one (τ := τ) k
    have e := Real.exp_pos (-(2 * Real.pi * Fourier.modeSize k * s))
    have hc2 := norm_homCoeff_le hs hu₂ hp₂ hm₂ k
    have hc12 : ‖homCoeff u₁ k - homCoeff u₂ k‖ ≤
        mL * d * Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) :=
      kamFourierBanach_coeff_sub_le hs hu₁ hu₂ hp₁ hp₂ hmL k
    have hsplit : a₁ k - a₂ k = T₁ k (homCoeff u₁ k - homCoeff u₂ k) +
        (T₁ k - T₂ k) (homCoeff u₂ k) := by
      simp only [ha₁, ha₂, map_sub, FunLike.coe_sub, Pi.sub_apply]; abel
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
  -- the difference of the two derivative series
  have hdiff : fourierSumVec (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • a₁ k) θ -
      fourierSumVec (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • a₂ k) θ =
      ∑' k, character k θ • ((2 * Real.pi * Complex.I * (k i : ℂ)) • (a₁ k - a₂ k)) := by
    unfold fourierSumVec
    rw [← (summable_character_smul hb₁ hθ).tsum_sub (summable_character_smul hb₂ hθ)]
    refine tsum_congr fun k => ?_
    simp only [ha₁, ha₂, smul_sub]
  rw [hdiff]
  have hg : HasSum (fun k : Fin 2 → ℤ => 2 * Real.pi * D * ((1 + Fourier.modeSize k) ^ 2 *
      waveA τ k ^ 2 * Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)))
      (2 * Real.pi * D * waveBN τ σ) :=
    ((waveBN_summable hτ hσ).hasSum).mul_left (2 * Real.pi * D)
  have hterm : ∀ k, ‖character k θ • ((2 * Real.pi * Complex.I * (k i : ℂ)) • (a₁ k - a₂ k))‖ ≤
      2 * Real.pi * D * ((1 + Fourier.modeSize k) ^ 2 * waveA τ k ^ 2 *
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by
    intro k
    refine (norm_character_smul_le
      (fun k => (2 * Real.pi * Complex.I * (k i : ℂ)) • (a₁ k - a₂ k)) hθ k).trans ?_
    have hk0 := Fourier.modeSize_nonneg k
    have hA := waveA_ge_one (τ := τ) k
    have h2 := norm_two_pi_I_coord k i
    have hE : Real.exp (-(2 * Real.pi * Fourier.modeSize k * s)) *
        Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) =
        Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k) := by
      rw [← Real.exp_add]; congr 1; ring
    have he := Real.exp_pos (-(2 * Real.pi * σ) * Fourier.modeSize k)
    have hkk : Fourier.modeSize k * (1 + Fourier.modeSize k) ≤ (1 + Fourier.modeSize k) ^ 2 := by
      nlinarith
    rw [norm_smul]
    calc ‖(2 * Real.pi * Complex.I * (k i : ℂ))‖ * ‖a₁ k - a₂ k‖ *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k)
        ≤ (2 * Real.pi * Fourier.modeSize k) * (D * ((1 + Fourier.modeSize k) * waveA τ k ^ 2) *
          Real.exp (-(2 * Real.pi * Fourier.modeSize k * s))) *
          Real.exp (2 * Real.pi * (s - σ) * Fourier.modeSize k) := by
          gcongr
          exact hbound k
      _ = 2 * Real.pi * D * ((Fourier.modeSize k * (1 + Fourier.modeSize k)) * waveA τ k ^ 2 *
          Real.exp (-(2 * Real.pi * σ) * Fourier.modeSize k)) := by rw [← hE]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_right ?_ he.le
          exact mul_le_mul_of_nonneg_right hkk (by positivity)
  refine (tsum_of_norm_bounded hg hterm).trans (le_of_eq ?_)
  rw [hD]; ring

end KAM.Wave
