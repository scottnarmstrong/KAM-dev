/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.SolveDeriv
public import KAM.Wave.Homological.Melnikov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The scalar cohomological equation (blueprint-W `bpW:w4:lemma1`, step *The equation*)

For a scalar `g` on `T_s` and multipliers `m_k` with `i(⟨k,ω⟩ - λ) m_k = 1` for `k ≠ 0`, the solve
`F = ∑ m_k ĝ_k e_k` satisfies, on `T_{s-σ}`,
`(1/2π)⟨ω, ∂_θ F⟩ - iλ F = g - e₀ ĝ₀`, with `e₀ = 1 + iλ m₀`
(`homCohEq_scalar`). The proof compares Fourier coefficients and uses the representation of a
holomorphic periodic bounded function by its Fourier series (`bpW:w4:F3`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

theorem homCoeff_continuous_of {s : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) :
    Continuous fun x : Fin 2 → ℝ => u fun j => (x j : ℂ) := homContinuous_restrict hs hu

theorem homCoeff_add {s : ℝ} (hs : 0 < s) {u v : (Fin 2 → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) (hv : DifferentiableOn ℂ v (complexStrip 2 s))
    (k : Fin 2 → ℤ) : homCoeff (fun z => u z + v z) k = homCoeff u k + homCoeff v k := by
  have hL : Continuous fun x : Fin 2 → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hchar : Continuous fun x : Fin 2 → ℝ => character (-k) (fun j => (x j : ℂ)) :=
    (differentiable_character (-k)).continuous.comp hL
  unfold homCoeff torusCoeffW torusAverage
  simp_rw [smul_add]
  exact MeasureTheory.integral_add
    (integrableOn_unitCube_of_continuous (hchar.smul (homContinuous_restrict hs hu)))
    (integrableOn_unitCube_of_continuous (hchar.smul (homContinuous_restrict hs hv)))

theorem homCoeff_sub {s : ℝ} (hs : 0 < s) {u v : (Fin 2 → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) (hv : DifferentiableOn ℂ v (complexStrip 2 s))
    (k : Fin 2 → ℤ) : homCoeff (fun z => u z - v z) k = homCoeff u k - homCoeff v k :=
  kamFourierBanach_coeff_sub (homContinuous_restrict hs hu) (homContinuous_restrict hs hv) k

theorem homCoeff_smul {s : ℝ} (hs : 0 < s) {u : (Fin 2 → ℂ) → ℂ}
    (hu : DifferentiableOn ℂ u (complexStrip 2 s)) (c : ℂ) (k : Fin 2 → ℤ) :
    homCoeff (fun z => c * u z) k = c * homCoeff u k := by
  have := homCoeff_clm hs hu (c • ContinuousLinearMap.id ℂ ℂ) k
  simpa using this

/-- **The scalar cohomological equation.** -/
theorem homCohEq_scalar {s σ m m' κ α τ : ℝ} (hτ : 0 ≤ τ) (hα : 0 < α) (hκ : 1 ≤ κ)
    (hσ : 0 < σ) (hσs : σ < s) (ω : Fin 2 → ℝ) (lam : ℝ) (mu : (Fin 2 → ℤ) → ℂ)
    (hmu : ∀ k, ‖mu k‖ ≤ κ * waveA τ k / α)
    (hres : ∀ k, k ≠ 0 → Complex.I * ((homPairZ k ω : ℂ) - lam) * mu k = 1)
    {g : (Fin 2 → ℂ) → ℂ} (hg : DifferentiableOn ℂ g (complexStrip 2 s))
    (hp : ∀ (i : Fin 2) z, z ∈ complexStrip 2 s → g (z + Pi.single i 1) = g z)
    (hm : ∀ z ∈ complexStrip 2 s, ‖g z‖ ≤ m)
    (hm' : ∀ i : Fin 2, ∀ z ∈ complexStrip 2 s, ‖homPartial i g z‖ ≤ m')
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 (s - σ)) :
    (2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) *
        homPartial i (homSolve (fun k => mu k • ContinuousLinearMap.id ℂ ℂ) g) θ)
      - Complex.I * lam * homSolve (fun k => mu k • ContinuousLinearMap.id ℂ ℂ) g θ =
      g θ - (1 + Complex.I * lam * mu 0) * homCoeff g 0 := by
  have hs : 0 < s := hσ.trans hσs
  have hρ : 0 < s - σ := by linarith
  set T : (Fin 2 → ℤ) → ℂ →L[ℂ] ℂ := fun k => mu k • ContinuousLinearMap.id ℂ ℂ with hT
  have hTn : ∀ k, ‖T k‖ ≤ κ * waveA τ k / α := fun k => by
    show ‖mu k • ContinuousLinearMap.id ℂ ℂ‖ ≤ _
    refine (norm_smul (mu k) (ContinuousLinearMap.id ℂ ℂ)).le.trans
      ((mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)).trans ?_)
    simpa using hmu k
  set F := homSolve T g with hF
  obtain ⟨-, -, -, hFd, hFp, hFc⟩ := homSolve_spec hτ hα hκ hσ hσs hTn hg hp hm
  have hsub : complexStrip 2 (s - σ) ⊆ complexStrip 2 s := fun z hz j => by
    have := hz j; linarith
  -- the derivatives of `F`
  have hDF : ∀ i : Fin 2, DifferentiableOn ℂ (homPartial i F) (complexStrip 2 (s - σ)) :=
    fun i => homPartial_differentiableOn i hFd
  have hDFp : ∀ i j : Fin 2, ∀ z ∈ complexStrip 2 (s - σ),
      homPartial i F (z + Pi.single j 1) = homPartial i F z :=
    fun i j z hz => homPartial_periodic hFp i j hz
  have hgd : ∀ i : Fin 2, DifferentiableOn ℂ (homPartial i g) (complexStrip 2 s) :=
    fun i => homPartial_differentiableOn i hg
  have hgdp : ∀ i j : Fin 2, ∀ z ∈ complexStrip 2 s,
      homPartial i g (z + Pi.single j 1) = homPartial i g z :=
    fun i j z hz => homPartial_periodic hp i j hz
  have hDFeq : ∀ i : Fin 2, ∀ z ∈ complexStrip 2 (s - σ),
      homPartial i F z = homSolve T (homPartial i g) z := fun i z hz =>
    homSolve_partial hτ hα hκ hσ hσs hTn hg hp hm i (hm' i) hz
  have hDFb : ∀ i : Fin 2, ∀ z ∈ complexStrip 2 (s - σ),
      ‖homPartial i F z‖ ≤ κ * waveBW τ σ * m' / α := fun i z hz => by
    rw [hDFeq i z hz]
    exact (homSolve_spec hτ hα hκ hσ hσs hTn (hgd i) (hgdp i) (hm' i)).2.2.1 z hz
  have hDFc : ∀ i : Fin 2, ∀ k, homCoeff (homPartial i F) k =
      (2 * Real.pi * Complex.I * (k i : ℂ)) * homCoeff F k := fun i k => by
    have := homCoeff_partial hρ hFd hFp i k
    simpa using this
  -- the function `Φ'`
  set Φ : (Fin 2 → ℂ) → ℂ := fun z =>
    (2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * homPartial i F z) - Complex.I * lam * F z - g z
    with hΦ
  have hS2 : (fun z => ∑ i : Fin 2, (ω i : ℂ) * homPartial i F z) =
      fun z => (ω 0 : ℂ) * homPartial 0 F z + (ω 1 : ℂ) * homPartial 1 F z := by
    funext z; simp [Fin.sum_univ_two]
  have hSd : DifferentiableOn ℂ (fun z => ∑ i : Fin 2, (ω i : ℂ) * homPartial i F z)
      (complexStrip 2 (s - σ)) := by
    rw [hS2]
    exact ((differentiableOn_const _).mul (hDF 0)).add ((differentiableOn_const _).mul (hDF 1))
  have hΦd : DifferentiableOn ℂ Φ (complexStrip 2 (s - σ)) := by
    have h1 := hSd
    exact ((differentiableOn_const _).mul h1 |>.sub ((differentiableOn_const _).mul hFd)).sub
      (hg.mono hsub)
  have hΦp : ∀ (j : Fin 2) z, z ∈ complexStrip 2 (s - σ) → Φ (z + Pi.single j 1) = Φ z := by
    intro j z hz
    have hz' := hsub hz
    have e : F (z + Pi.single j 1) = F z := hFp j z hz
    simp only [hΦ, hDFp _ j z hz, e, hp j z hz']
  obtain ⟨AF, hAF⟩ : ∃ A, ∀ z ∈ complexStrip 2 (s - σ), ‖Φ z‖ ≤ A := by
    refine ⟨(2 * Real.pi)⁻¹ * (∑ i, ‖(ω i : ℂ)‖ * (κ * waveBW τ σ * m' / α)) +
      ‖Complex.I * lam‖ * (κ * waveBW τ σ * m / α) + m, fun z hz => ?_⟩
    have hFb := (homSolve_spec hτ hα hκ hσ hσs hTn hg hp hm).2.2.1 z hz
    have e1 : ‖(2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * homPartial i F z)‖ ≤
        (2 * Real.pi)⁻¹ * (∑ i, ‖(ω i : ℂ)‖ * (κ * waveBW τ σ * m' / α)) := by
      rw [norm_mul, norm_inv]
      have : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
        simp [abs_of_pos Real.pi_pos]
      rw [this]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
        (by positivity)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hDFb i z hz) (norm_nonneg _)
    have e2 : ‖Complex.I * lam * F z‖ ≤ ‖Complex.I * lam‖ * (κ * waveBW τ σ * m / α) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hFb (norm_nonneg _)
    have e3 := hm z (hsub hz)
    calc ‖Φ z‖ ≤ ‖(2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * homPartial i F z) -
          Complex.I * lam * F z‖ + ‖g z‖ := norm_sub_le _ _
      _ ≤ (‖(2 * Real.pi : ℂ)⁻¹ * (∑ i, (ω i : ℂ) * homPartial i F z)‖ +
          ‖Complex.I * lam * F z‖) + ‖g z‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by gcongr
  -- the Fourier coefficients of `Φ`
  have hAd : DifferentiableOn ℂ (fun z => (2 * Real.pi : ℂ)⁻¹ *
      (∑ i : Fin 2, (ω i : ℂ) * homPartial i F z)) (complexStrip 2 (s - σ)) :=
    (differentiableOn_const _).mul hSd
  have hBd : DifferentiableOn ℂ (fun z => Complex.I * lam * F z) (complexStrip 2 (s - σ)) :=
    (differentiableOn_const _).mul hFd
  have hgd' : DifferentiableOn ℂ g (complexStrip 2 (s - σ)) := hg.mono hsub
  have hcoef : ∀ k, homCoeff Φ k =
      (2 * Real.pi : ℂ)⁻¹ * ((ω 0 : ℂ) * ((2 * Real.pi * Complex.I * (k 0 : ℂ)) * homCoeff F k)
        + (ω 1 : ℂ) * ((2 * Real.pi * Complex.I * (k 1 : ℂ)) * homCoeff F k))
      - Complex.I * lam * homCoeff F k - homCoeff g k := by
    intro k
    have e1 := homCoeff_sub hρ (u := fun z => (2 * Real.pi : ℂ)⁻¹ *
        (∑ i : Fin 2, (ω i : ℂ) * homPartial i F z) - Complex.I * lam * F z) (v := g)
      (hAd.sub hBd) hgd' k
    have e2 := homCoeff_sub hρ hAd hBd k
    have e3 := homCoeff_smul hρ hSd (2 * Real.pi : ℂ)⁻¹ k
    have e4 := homCoeff_add hρ (u := fun z => (ω 0 : ℂ) * homPartial 0 F z)
      (v := fun z => (ω 1 : ℂ) * homPartial 1 F z)
      ((differentiableOn_const _).mul (hDF 0)) ((differentiableOn_const _).mul (hDF 1)) k
    have e5 := homCoeff_smul hρ (hDF 0) (ω 0 : ℂ) k
    have e6 := homCoeff_smul hρ (hDF 1) (ω 1 : ℂ) k
    have e7 := homCoeff_smul hρ hFd (Complex.I * lam) k
    simp only [hΦ]
    rw [e1, e2, e3, e7]
    rw [hS2] at e3 ⊢
    rw [e4, e5, e6, hDFc 0 k, hDFc 1 k]
  have hcoefv : ∀ k, homCoeff Φ k =
      if k = 0 then -((1 + Complex.I * lam * mu 0) * homCoeff g 0) else 0 := by
    intro k
    rw [hcoef k, hFc k]
    simp only [hT, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    by_cases hk : k = 0
    · subst hk
      simp
      ring
    · simp only [hk, ite_false]
      have h1 := hres k hk
      have hz : (homPairZ k ω : ℂ) = (k 0 : ℂ) * (ω 0 : ℂ) + (k 1 : ℂ) * (ω 1 : ℂ) := by
        simp [homPairZ, Fin.sum_univ_two]
      rw [hz] at h1
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      field_simp
      linear_combination (homCoeff g k) * h1
  have hrep := eq_fourierSumVec_torusCoeffW hρ hΦd hΦp hAF hθ
  have hz : (torusCoeffW fun x : Fin 2 → ℝ => Φ fun j => (x j : ℂ)) =
      fun k => if k = 0 then -((1 + Complex.I * lam * mu 0) * homCoeff g 0) else 0 :=
    funext hcoefv
  rw [hz] at hrep
  have hval : fourierSumVec (fun k : Fin 2 → ℤ => if k = 0 then
      -((1 + Complex.I * lam * mu 0) * homCoeff g 0) else (0 : ℂ)) θ =
      -((1 + Complex.I * lam * mu 0) * homCoeff g 0) := by
    unfold fourierSumVec
    rw [tsum_eq_single 0]
    · simp [character_zero]
    · intro k hk; simp [hk]
  rw [hval] at hrep
  simp only [hΦ] at hrep
  linear_combination hrep

end KAM.Wave
