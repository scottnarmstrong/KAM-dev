/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Recon2.Orbit
public import KAM.Wave.Cubic.FrozenForm
public import KAM.Wave.Assembly.Ext
public import Mathlib.Analysis.ODE.Gronwall

/-!
# W8: uniqueness for the coefficient system (blueprint `bpW:w8:unique`)

Blueprint label `bpW:w8:unique` (milestone W8).

Two analytic coefficient solutions `Y, Y' : ℝ → WaveSpace` (Definition `bpW:w2:coeffsol`) with
`Y 0 = Y' 0` coincide (`KAM.Wave.isAnalyticCoeffSolution_unique`). The proof is the energy argument
of the blueprint: with `D_i = Y_i - Y'_i` and `f = ‖D₁‖² + ‖D₂‖²`, the linear terms cancel in
`f' = -2 ⟨D₂, g(Y₁) - g(Y₁')⟩`, where `g = S 𝒢^w` (`g(y)_j = ω_{1,1}(j) cubicGrad y j`), so
`|f'| ≤ L f` on every `[-T, T]`, and Gronwall's lemma gives `f = 0`.
-/

public section

open Set Filter

namespace KAM.Wave

/-- `g(y)_j = ω_{1,1}(j) · cubicGrad y j = j⁻¹ 𝒢^w(y)_j`, as the map `S 𝒢^w : ℓ²_ℝ → ℓ²_ℝ`
(blueprint `bpW:w8:unique`, Step `stepW:w8:u-raw`). -/
noncomputable def w8CubicG (m : ℝ) (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) :
    lp (fun _ : ℕ+ => ℝ) 2 :=
  waveShift (waveGw m hm y)

theorem w8CubicG_apply {m : ℝ} (hm : 0 < m) (y : lp (fun _ : ℕ+ => ℝ) 2) (j : ℕ+) :
    w8CubicG m hm y j = ellWeight 1 1 j * cubicGrad m hm y j := by
  rw [w8CubicG, waveShift_apply, waveGw_weighted_one_one]
  ring

/-- `‖g(y) - g(y')‖ ≤ 3 C_m ‖y - y'‖ max(‖y‖, ‖y'‖)²` (blueprint `bpW:w8:unique`, Step
`stepW:w8:u-raw`, from `bpW:w1:cubic-analytic` (iii), (iv)). -/
theorem w8CubicG_sub_le {m : ℝ} (hm : 0 < m) (y y' : lp (fun _ : ℕ+ => ℝ) 2) :
    ‖w8CubicG m hm y - w8CubicG m hm y'‖ ≤
      3 * waveCubicConst 1 * ‖y - y'‖ * (max ‖y‖ ‖y'‖) ^ 2 := by
  rw [w8CubicG, w8CubicG, ← map_sub]
  have hS : ‖waveShift‖ ≤ 1 := norm_diagCLM_le _ _
  calc ‖waveShift (waveGw m hm y - waveGw m hm y')‖
      ≤ ‖waveShift‖ * ‖waveGw m hm y - waveGw m hm y'‖ := waveShift.le_opNorm _
    _ ≤ 1 * ‖waveGw m hm y - waveGw m hm y'‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
    _ ≤ _ := by
        rw [one_mul]
        exact waveCubicNL_sub_le m hm zero_le_one _ y y'

section Curve

variable {m : ℝ} {hm : 0 < m} {Y : ℝ → WaveSpace}

/-- `(Y₁')_j = λ_j (Y₂)_j` (blueprint `bpW:w8:unique`, Step `stepW:w8:u-raw`). -/
theorem w8_deriv_fst_apply (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) (j : ℕ+) :
    deriv (fun s => (Y s).1) t j = lam m hm j * (Y t).2 j := by
  have h := coeff_deriv_coeffSol_fst hY t j
  unfold coeff at h
  have hw := (ellWeight_pos 1 1 j).ne'
  have e : deriv (fun s => (Y s).1) t j =
      deriv (fun s => (Y s).1) t j / ellWeight 1 1 j * ellWeight 1 1 j :=
    (div_mul_cancel₀ _ hw).symm
  rw [e, h]
  field_simp

/-- `(Y₂')_j = -λ_j (Y₁)_j - g(Y₁)_j` (blueprint `bpW:w8:unique`, Step `stepW:w8:u-raw`). -/
theorem w8_deriv_snd_apply (hY : IsAnalyticCoeffSolution m hm Y) (t : ℝ) (j : ℕ+) :
    deriv (fun s => (Y s).2) t j = -(lam m hm j * (Y t).1 j) - w8CubicG m hm (Y t).1 j := by
  have h := coeff_deriv_coeffSol_snd hY t j
  unfold coeff at h
  have hw := (ellWeight_pos 1 1 j).ne'
  have e : deriv (fun s => (Y s).2) t j =
      deriv (fun s => (Y s).2) t j / ellWeight 1 1 j * ellWeight 1 1 j :=
    (div_mul_cancel₀ _ hw).symm
  rw [e, h, w8CubicG_apply]
  field_simp

end Curve

/-- Gronwall in the form used by `bpW:w8:unique` (Step `stepW:w8:u-gron`): a nonnegative
differentiable `f` with `f 0 = 0` and `|f'| ≤ L_T f` on every `[-T, T]` vanishes. -/
theorem w8_eq_zero_of_abs_deriv_le {f f' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h0 : f 0 = 0) (hnn : ∀ t, 0 ≤ f t)
    (hbd : ∀ T : ℝ, ∃ L : ℝ, ∀ t ∈ Icc (-T) T, |f' t| ≤ L * f t) (t : ℝ) : f t = 0 := by
  obtain ⟨L, hL⟩ := hbd |t|
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun s => (hf s).continuousAt
  rcases le_or_gt 0 t with ht | ht
  · have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (E := ℝ) (K := L) (a := 0)
      (b := |t|) hcont.continuousOn (fun x _ => (hf x).hasDerivWithinAt) h0 (fun x hx => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn x)]
        exact hL x ⟨by linarith [abs_nonneg t, hx.1], hx.2.le⟩)
    exact this t ⟨ht, le_abs_self t⟩
  · have hg : ∀ s, HasDerivAt (fun s => f (-s)) (-(f' (-s))) s := fun s => by
      have := HasDerivAt.comp_const_sub (f := f) (0 : ℝ) s (by simpa using hf (-s))
      simpa using this
    have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (E := ℝ) (K := L) (a := 0)
      (b := |t|) (f := fun s => f (-s)) (hcont.comp continuous_neg).continuousOn
      (fun x _ => (hg x).hasDerivWithinAt) (by simpa using h0) (fun x hx => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg (hnn (-x))]
        exact hL (-x) ⟨by linarith [hx.2], by linarith [hx.1, abs_nonneg t]⟩)
    have h := this (-t) ⟨by linarith, by rw [abs_of_neg ht]⟩
    simpa using h

/-- **Uniqueness for the coefficient system** (blueprint `bpW:w8:unique`). Two analytic
coefficient solutions with the same value at `0` coincide. -/
theorem isAnalyticCoeffSolution_unique {m : ℝ} {hm : 0 < m} {Y Y' : ℝ → WaveSpace}
    (hY : IsAnalyticCoeffSolution m hm Y) (hY' : IsAnalyticCoeffSolution m hm Y')
    (h0 : Y 0 = Y' 0) : Y = Y' := by
  -- differences, derivatives and the energy
  set D₁ : ℝ → lp (fun _ : ℕ+ => ℝ) 2 := fun t => (Y t).1 - (Y' t).1 with hD₁def
  set D₂ : ℝ → lp (fun _ : ℕ+ => ℝ) 2 := fun t => (Y t).2 - (Y' t).2 with hD₂def
  set A : ℝ → lp (fun _ : ℕ+ => ℝ) 2 :=
    fun t => deriv (fun s => (Y s).1) t - deriv (fun s => (Y' s).1) t with hAdef
  set B : ℝ → lp (fun _ : ℕ+ => ℝ) 2 :=
    fun t => deriv (fun s => (Y s).2) t - deriv (fun s => (Y' s).2) t with hBdef
  set G : ℝ → lp (fun _ : ℕ+ => ℝ) 2 :=
    fun t => w8CubicG m hm (Y t).1 - w8CubicG m hm (Y' t).1 with hGdef
  have hD₁ : ∀ t, HasDerivAt D₁ (A t) t := fun t =>
    (hasDerivAt_coeffSol_fst hY t).sub (hasDerivAt_coeffSol_fst hY' t)
  have hD₂ : ∀ t, HasDerivAt D₂ (B t) t := fun t =>
    (hasDerivAt_coeffSol_snd hY t).sub (hasDerivAt_coeffSol_snd hY' t)
  have hA : ∀ t j, A t j = lam m hm j * D₂ t j := fun t j => by
    simp only [hAdef, hD₂def, lp.coeFn_sub, Pi.sub_apply, w8_deriv_fst_apply hY,
      w8_deriv_fst_apply hY']
    ring
  have hB : ∀ t j, B t j = -(lam m hm j * D₁ t j) - G t j := fun t j => by
    simp only [hBdef, hD₁def, hGdef, lp.coeFn_sub, Pi.sub_apply, w8_deriv_snd_apply hY,
      w8_deriv_snd_apply hY']
    ring
  -- Step `stepW:w8:u-energy`: `f' = -2 ⟨D₂, G⟩`
  have hcancel : ∀ t, inner ℝ (D₁ t) (A t) + inner ℝ (D₂ t) (B t) = -inner ℝ (D₂ t) (G t) := by
    intro t
    obtain ⟨s1, e1⟩ := w8ext_inner_eq_tsum (D₁ t) (A t)
    obtain ⟨s2, e2⟩ := w8ext_inner_eq_tsum (D₂ t) (B t)
    obtain ⟨s3, e3⟩ := w8ext_inner_eq_tsum (D₂ t) (G t)
    have hz : ∀ j, D₁ t j * A t j + D₂ t j * B t j + D₂ t j * G t j = 0 := fun j => by
      rw [hA, hB]; ring
    have : inner ℝ (D₁ t) (A t) + inner ℝ (D₂ t) (B t) + inner ℝ (D₂ t) (G t) = 0 := by
      rw [e1, e2, e3, ← s1.tsum_add s2, ← (s1.add s2).tsum_add s3]
      simp only [hz, tsum_zero]
    linarith
  set f : ℝ → ℝ := fun t => ‖D₁ t‖ ^ 2 + ‖D₂ t‖ ^ 2 with hfdef
  have hf : ∀ t, HasDerivAt f (-(2 * inner ℝ (D₂ t) (G t))) t := fun t => by
    have := ((hD₁ t).norm_sq).add ((hD₂ t).norm_sq)
    convert this using 1
    linarith [hcancel t]
  -- Step `stepW:w8:u-ineq`: `|f'| ≤ L f` on `[-T, T]`
  have hcY : Continuous Y := w8ext_continuous_of_analyticAt hY.1
  have hcY' : Continuous Y' := w8ext_continuous_of_analyticAt hY'.1
  have hbd : ∀ T : ℝ, ∃ L : ℝ, ∀ t ∈ Icc (-T) T,
      |-(2 * inner ℝ (D₂ t) (G t))| ≤ L * f t := by
    intro T
    obtain ⟨R₁, hR₁⟩ := w8ext_bounded_Icc (T := T) hcY.continuousOn
    obtain ⟨R₂, hR₂⟩ := w8ext_bounded_Icc (T := T) hcY'.continuousOn
    set R := max (max R₁ R₂) 0
    refine ⟨3 * waveCubicConst 1 * R ^ 2, fun t ht => ?_⟩
    have hC : 0 ≤ waveCubicConst 1 := waveCubicConst_nonneg 1
    have hmax : max ‖(Y t).1‖ ‖(Y' t).1‖ ≤ R :=
      max_le ((norm_fst_le _).trans ((hR₁ t ht).trans
          ((le_max_left _ _).trans (le_max_left _ _))))
        ((norm_fst_le _).trans ((hR₂ t ht).trans
          ((le_max_right _ _).trans (le_max_left _ _))))
    have hmax2 : (max ‖(Y t).1‖ ‖(Y' t).1‖) ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hmax 2
    have hG : ‖G t‖ ≤ 3 * waveCubicConst 1 * ‖D₁ t‖ * R ^ 2 :=
      (w8CubicG_sub_le hm _ _).trans (by gcongr)
    have hcs := w8ext_abs_inner_le (D₂ t) (G t)
    have h2 : 2 * ‖D₂ t‖ * ‖D₁ t‖ ≤ ‖D₁ t‖ ^ 2 + ‖D₂ t‖ ^ 2 := by
      nlinarith [sq_nonneg (‖D₁ t‖ - ‖D₂ t‖)]
    have hK : 0 ≤ 3 * waveCubicConst 1 * R ^ 2 := by positivity
    rw [abs_neg, abs_mul, abs_two]
    calc 2 * |inner ℝ (D₂ t) (G t)| ≤ 2 * (‖D₂ t‖ * (3 * waveCubicConst 1 * ‖D₁ t‖ * R ^ 2)) := by
          gcongr; exact hcs.trans (mul_le_mul_of_nonneg_left hG (norm_nonneg _))
      _ = (3 * waveCubicConst 1 * R ^ 2) * (2 * ‖D₂ t‖ * ‖D₁ t‖) := by ring
      _ ≤ (3 * waveCubicConst 1 * R ^ 2) * f t := mul_le_mul_of_nonneg_left h2 hK
  -- Step `stepW:w8:u-gron`
  have hf0 : f 0 = 0 := by simp [hfdef, hD₁def, hD₂def, h0]
  have hfz := w8_eq_zero_of_abs_deriv_le hf hf0 (fun t => by positivity) hbd
  funext t
  have h := hfz t
  have h1 : ‖D₁ t‖ = 0 := by nlinarith [sq_nonneg ‖D₁ t‖, sq_nonneg ‖D₂ t‖, norm_nonneg (D₁ t)]
  have h2 : ‖D₂ t‖ = 0 := by nlinarith [sq_nonneg ‖D₁ t‖, sq_nonneg ‖D₂ t‖, norm_nonneg (D₂ t)]
  rw [norm_eq_zero, hD₁def, sub_eq_zero] at h1
  rw [norm_eq_zero, hD₂def, sub_eq_zero] at h2
  exact Prod.ext h1 h2

/-- Step `stepW:w8:in-orbit` of `bpW:w8:injective` (W6-free part): two real-analytic maps
`K, K' : ℝ² → WaveSpace` satisfying the invariance `bpW:w2:inv` (frozen clause (4)) with
frequencies `ν, ν'` that meet, `K θ = K' θ'`, carry the same orbit:
`K (θ + t ν) = K' (θ' + t ν')` for all `t` (Lemma `bpW:w2:orbit` and `bpW:w8:unique`). -/
theorem w8_orbit_eq_of_meet {m : ℝ} (hm : 0 < m) {K K' : (Fin 2 → ℝ) → WaveSpace}
    {ν ν' : Fin 2 → ℝ} (hK : AnalyticOnNhd ℝ K Set.univ) (hK' : AnalyticOnNhd ℝ K' Set.univ)
    (hinv : ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).1 j) (lam m hm j * coeff (K θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K (θ + t • ν)).2 j)
        (-(lam m hm j * coeff (K θ).1 j) - cubicGrad m hm (K θ).1 j) 0)
    (hinv' : ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
      HasDerivAt (fun t : ℝ => coeff (K' (θ + t • ν')).1 j) (lam m hm j * coeff (K' θ).2 j) 0 ∧
      HasDerivAt (fun t : ℝ => coeff (K' (θ + t • ν')).2 j)
        (-(lam m hm j * coeff (K' θ).1 j) - cubicGrad m hm (K' θ).1 j) 0)
    {θ θ' : Fin 2 → ℝ} (hmeet : K θ = K' θ') (t : ℝ) :
    K (θ + t • ν) = K' (θ' + t • ν') := by
  have h := isAnalyticCoeffSolution_unique (isAnalyticCoeffSolution_orbit hm hK hinv θ)
    (isAnalyticCoeffSolution_orbit hm hK' hinv' θ') (by simpa using hmeet)
  exact congrFun h t

end KAM.Wave

end
