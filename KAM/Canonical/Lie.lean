/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Setting
public import KAM.Canonical.Flow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Derivatives along the flow and Taylor's formula

Blueprint-N Part 5, nodes `bpN:p5:lie-derivative` and `bpN:p5:taylor`.

* `KAM.Canonical.taylor_integral_aux`: the integral Taylor remainder for a family `G j` with
  `(G j)' = G (j+1)` on `[0, 1]` (Mathlib has only the mean-value forms of the remainder);
* `KAM.Canonical.lie_derivative`: `g(t) = u(X^t z)` is `C^∞` on `[-1, 1]` with
  `g⁽ʲ⁾(t) = (ad_φ^j u)(X^t z)`;
* `KAM.Canonical.taylor_lie`: Taylor's formula with integral remainder along the flow, and the
  remainder bound `B / N!`;
* `KAM.Canonical.taylor_poschel`: the displayed formula (`N = 2` for `h`, `N = 1` for `f₀`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace KAM.Canonical

/-! ### The integral Taylor remainder -/

/-- The antiderivative of the Taylor weight `(1 - t)^M / M!`. -/
theorem hasDerivAt_taylorWeight (M : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => -((1 - t) ^ (M + 1) / ((M + 1).factorial : ℝ)))
      ((1 - t) ^ M / (M.factorial : ℝ)) t := by
  have h := (((hasDerivAt_id t).const_sub 1).pow (M + 1)).div_const ((M + 1).factorial : ℝ) |>.neg
  refine HasDerivAt.congr_deriv h ?_
  have hf : ((M + 1).factorial : ℝ) = (M + 1) * (M.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf0 : (M.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
  simp only [id, Nat.add_sub_cancel, hf]
  push_cast
  field_simp

/-- Integral Taylor remainder: if `(G j)' = G (j+1)` on `[0, 1]` for all `j`, then
`G 0 1 = ∑_{j ≤ M} G j 0 / j! + ∫₀¹ (1-t)^M / M! · G (M+1) t dt`. -/
theorem taylor_integral_aux {G : ℕ → ℝ → ℂ}
    (hG : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (G j) (G (j + 1) t) t) (M : ℕ) :
    G 0 1 = ∑ j ∈ Finset.range (M + 1), ((j.factorial : ℂ)⁻¹) * G j 0 +
      ∫ t in (0 : ℝ)..1, ((((1 - t) ^ M / (M.factorial : ℝ) : ℝ) : ℂ)) * G (M + 1) t := by
  have hcont : ∀ j, ContinuousOn (G j) (Icc 0 1) := fun j t ht =>
    (hG j t ht).continuousAt.continuousWithinAt
  have hint : ∀ j, IntervalIntegrable (G j) MeasureTheory.volume 0 1 := fun j =>
    (hcont j).intervalIntegrable_of_Icc zero_le_one
  have hG' : ∀ j, ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (G j) (G (j + 1) t) t := fun j t ht =>
    hG j t (by rwa [uIcc_of_le zero_le_one] at ht)
  induction M with
  | zero =>
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (hG' 0) (hint 1)
    simp only [zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_mul, pow_zero, div_one, Complex.ofReal_one]
    rw [this]; ring
  | succ M ih =>
    rw [ih, Finset.sum_range_succ _ (M + 1)]
    set w : ℝ → ℂ := fun t => ((((1 - t) ^ M / (M.factorial : ℝ) : ℝ) : ℂ)) with hw
    set v : ℝ → ℂ := fun t =>
      ((-((1 - t) ^ (M + 1) / ((M + 1).factorial : ℝ)) : ℝ) : ℂ) with hv
    have hvd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt v (w t) t := fun t _ =>
      (hasDerivAt_taylorWeight M t).ofReal_comp
    have hwc : Continuous w := by
      rw [hw]; fun_prop
    have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (hG' (M + 1)) hvd
      (hint (M + 2)) (hwc.intervalIntegrable 0 1)
    have e1 : ∫ t in (0 : ℝ)..1, w t * G (M + 1) t = ∫ t in (0 : ℝ)..1, G (M + 1) t * w t := by
      simp_rw [mul_comm]
    have e2 : ∫ t in (0 : ℝ)..1,
        ((((1 - t) ^ (M + 1) / ((M + 1).factorial : ℝ) : ℝ) : ℂ)) * G (M + 1 + 1) t =
        -∫ t in (0 : ℝ)..1, G (M + 1 + 1) t * v t := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [hv, Complex.ofReal_neg]
      ring
    have hv1 : v 1 = 0 := by simp [hv]
    have hv0 : v 0 = -((((M + 1).factorial : ℝ)⁻¹ : ℝ) : ℂ) := by simp [hv]
    rw [e1, key, e2, hv1, hv0]
    push_cast
    ring

/-! ### Derivatives along the flow -/

section Lie

variable {n : ℕ}

/-- Along the flow, `d/dt v(X^t z) = {v, φ}(X^t z)` for `v` holomorphic where the trajectory is. -/
theorem hasDerivAt_comp_flow {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω Ω₁ : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε) (hΩ₁ : IsOpen Ω₁)
    (hv : DifferentiableOn ℂ v Ω₁) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ gaugeInterior W Ω (1 / 2)) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hmem : flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ Ω₁) :
    HasDerivAt (fun s => v (flow (KAM.hamiltonianVectorFieldℂ φ) Ω s z))
      (poissonBracket v φ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)) t := by
  obtain ⟨-, hsol, -, -⟩ := flow_a h hz
  have hγ := (hsol t ht).2
  have hd : DifferentiableAt ℂ v (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) :=
    hv.differentiableAt (hΩ₁.mem_nhds hmem)
  have := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hγ
  rw [poissonBracket_eq_fderiv_field]
  exact this

/-- The derivatives of the family `t ↦ (ad_φ^j u)(X^t z)` along the trajectory. -/
theorem hasDerivAt_adPow_flow {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω Ω₁ : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : Ω₁ ⊆ Ω) (hu : DifferentiableOn ℂ u Ω₁)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2))
    (htraj : ∀ t ∈ Icc (-1 : ℝ) 1, flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ Ω₁) (j : ℕ) :
    ∀ t ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun s => adPow φ j u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω s z))
        (adPow φ (j + 1) u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)) t := fun t ht =>
  hasDerivAt_comp_flow h hΩ₁ (differentiableOn_adPow hΩ₁ (hφ.mono hΩ₁Ω) hu j) hz ht (htraj t ht)

/-- `bpN:p5:lie-derivative`: `g(t) = u(X^t z)` is `C^∞` on `[-1, 1]`,
`g⁽ʲ⁾(t) = (ad_φ^j u)(X^t z)`. -/
theorem lie_derivative {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω Ω₁ : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : Ω₁ ⊆ Ω) (hu : DifferentiableOn ℂ u Ω₁)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2))
    (htraj : ∀ t ∈ Icc (-1 : ℝ) 1, flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ Ω₁) :
    (∀ j, DifferentiableOn ℂ (adPow φ j u) Ω₁) ∧
    ContDiffOn ℝ ∞ (fun t => u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)) (Icc (-1) 1) ∧
    ∀ j, ∀ t ∈ Icc (-1 : ℝ) 1,
      iteratedDerivWithin j (fun t => u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z))
        (Icc (-1) 1) t =
        adPow φ j u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) := by
  set G : ℕ → ℝ → ℂ := fun j s => adPow φ j u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω s z) with hG
  have hder : ∀ j, ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivAt (G j) (G (j + 1) t) t :=
    hasDerivAt_adPow_flow hφ h hΩ₁ hΩ₁Ω hu hz htraj
  have huniq : UniqueDiffOn ℝ (Icc (-1 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hdw : ∀ j, ∀ t ∈ Icc (-1 : ℝ) 1, derivWithin (G j) (Icc (-1) 1) t = G (j + 1) t :=
    fun j t ht => (hder j t ht).hasDerivWithinAt.derivWithin (huniq t ht)
  have hsm : ∀ k : ℕ, ∀ j, ContDiffOn ℝ k (G j) (Icc (-1) 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun t ht => (hder j t ht).continuousAt.continuousWithinAt
    | succ k ih =>
      intro j
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin huniq]
      refine ⟨fun t ht => (hder j t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro hk
        exact absurd hk (by simp)
      · exact (ih (j + 1)).congr fun t ht => hdw j t ht
  refine ⟨fun j => differentiableOn_adPow hΩ₁ (hφ.mono hΩ₁Ω) hu j,
    contDiffOn_infty.2 fun k => hsm k 0, ?_⟩
  intro j
  induction j with
  | zero => intro t ht; simp only [iteratedDerivWithin_zero]; rfl
  | succ j ih =>
    intro t ht
    rw [iteratedDerivWithin_succ]
    have e := derivWithin_congr (f₁ := iteratedDerivWithin j (G 0) (Icc (-1) 1)) (f := G j)
      (s := Icc (-1) 1) (x := t) (fun s hs => ih s hs) (ih t ht)
    exact e.trans (hdw j t ht)

/-- `bpN:p5:taylor`: Taylor with integral remainder along the flow, order `N ≥ 1`
(hypotheses of `lie_derivative`). -/
theorem taylor_lie {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω Ω₁ : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (h : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : Ω₁ ⊆ Ω) (hu : DifferentiableOn ℂ u Ω₁)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ gaugeInterior W Ω (1 / 2))
    (htraj : ∀ t ∈ Icc (-1 : ℝ) 1, flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ Ω₁)
    {N : ℕ} (hN : 1 ≤ N) :
    u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω 1 z) =
        ∑ j ∈ Finset.range N, ((j.factorial : ℂ)⁻¹) * adPow φ j u z +
          ∫ t in (0 : ℝ)..1, ((((1 - t) ^ (N - 1) / ((N - 1).factorial : ℝ) : ℝ) : ℂ)) *
            adPow φ N u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) ∧
    ∀ B : ℝ, (∀ t ∈ Icc (0 : ℝ) 1, ‖adPow φ N u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)‖ ≤ B) →
      ‖∫ t in (0 : ℝ)..1, ((((1 - t) ^ (N - 1) / ((N - 1).factorial : ℝ) : ℝ) : ℂ)) *
            adPow φ N u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)‖ ≤ B / (N.factorial : ℝ) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set G : ℕ → ℝ → ℂ := fun j s => adPow φ j u (flow (KAM.hamiltonianVectorFieldℂ φ) Ω s z) with hG
  have hder : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (G j) (G (j + 1) t) t := fun j t ht =>
    hasDerivAt_adPow_flow hφ h hΩ₁ hΩ₁Ω hu hz htraj j t ⟨by linarith [ht.1], ht.2⟩
  have h0 : flow (KAM.hamiltonianVectorFieldℂ φ) Ω 0 z = z := (flow_a h hz).1
  have hmain := taylor_integral_aux hder M
  have hsum : ∑ j ∈ Finset.range (M + 1), ((j.factorial : ℂ)⁻¹) * G j 0 =
      ∑ j ∈ Finset.range (M + 1), ((j.factorial : ℂ)⁻¹) * adPow φ j u z := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hG, h0]
  refine ⟨?_, fun B hB => ?_⟩
  · rw [← hsum]
    exact hmain
  · have hcont : Continuous fun t : ℝ => ((((1 - t) ^ M / (M.factorial : ℝ) : ℝ) : ℂ)) := by
      fun_prop
    have hwint : IntervalIntegrable (fun t : ℝ => (1 - t) ^ M / (M.factorial : ℝ))
        MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    have hI : ∫ t in (0 : ℝ)..1, (1 - t) ^ M / (M.factorial : ℝ) = 1 / ((M + 1).factorial : ℝ) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_taylorWeight M t)
        hwint]
      simp
    calc ‖∫ t in (0 : ℝ)..1, ((((1 - t) ^ M / (M.factorial : ℝ) : ℝ) : ℂ)) * G (M + 1) t‖
        ≤ ∫ t in (0 : ℝ)..1, (1 - t) ^ M / (M.factorial : ℝ) * B := by
          refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Filter.Eventually.of_forall fun t ht => ?_) (hwint.mul_const B)
          have hw : 0 ≤ (1 - t) ^ M / (M.factorial : ℝ) := by
            have : 0 ≤ 1 - t := by linarith [ht.2]
            positivity
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
          exact mul_le_mul_of_nonneg_left (hB t ⟨ht.1.le, ht.2⟩) hw
      _ = B / ((M + 1).factorial : ℝ) := by
          rw [intervalIntegral.integral_mul_const, hI]; ring

/-- Linearity of the bracket in the first slot, at a point of differentiability. -/
theorem poissonBracket_const_mul_add {a b φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {c : ℂ}
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (ha : DifferentiableAt ℂ a z) (hb : DifferentiableAt ℂ b z) :
    poissonBracket (fun w => c * a w + b w) φ z =
      c * poissonBracket a φ z + poissonBracket b φ z := by
  simp only [poissonBracket_eq_fderiv_field]
  rw [fderiv_fun_add (ha.const_mul c) hb, fderiv_const_mul ha]
  simp

/-- `bpN:p5:taylor`, displayed formula (`bpN:p5:eq:poschel`): `N = 2` for `h`, `N = 1` for `f₀`. -/
theorem taylor_poschel {W : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (Fin n → ℂ))}
    {Ω Ω₁ : Set ((Fin n → ℂ) × (Fin n → ℂ))} {φ h f₀ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ}
    (hφ : DifferentiableOn ℂ φ Ω) (hs : SmallField W Ω (KAM.hamiltonianVectorFieldℂ φ) ε)
    (hΩ₁ : IsOpen Ω₁) (hΩ₁Ω : Ω₁ ⊆ Ω) (hh : DifferentiableOn ℂ h Ω₁)
    (hf : DifferentiableOn ℂ f₀ Ω₁) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ gaugeInterior W Ω (1 / 2))
    (htraj : ∀ t ∈ Icc (-1 : ℝ) 1, flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z ∈ Ω₁) :
    h (flow (KAM.hamiltonianVectorFieldℂ φ) Ω 1 z) +
        f₀ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω 1 z) =
      h z + poissonBracket h φ z + f₀ z +
        ∫ t in (0 : ℝ)..1, poissonBracket
          (fun w => ((1 - t : ℝ) : ℂ) * poissonBracket h φ w + f₀ w) φ
          (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) := by
  have T1 := (taylor_lie hφ hs hΩ₁ hΩ₁Ω hh hz htraj (N := 2) (by norm_num)).1
  have T2 := (taylor_lie hφ hs hΩ₁ hΩ₁Ω hf hz htraj (N := 1) (by norm_num)).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, one_mul, adPow] at T1 T2
  have hcont : ∀ (v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ), DifferentiableOn ℂ v Ω₁ → ∀ j,
      ContinuousOn (fun t : ℝ => adPow φ j v (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z))
        (Icc 0 1) := fun v hv j t ht =>
    (hasDerivAt_adPow_flow hφ hs hΩ₁ hΩ₁Ω hv hz htraj j t
      ⟨by linarith [ht.1], ht.2⟩).continuousAt.continuousWithinAt
  simp only [show (2 : ℕ) - 1 = 1 from rfl, show (1 : ℕ) - 1 = 0 from rfl, Nat.factorial_one,
    Nat.factorial_zero, Nat.cast_one, pow_one, pow_zero, div_one, Complex.ofReal_one,
    one_mul] at T1 T2
  have hc2 := hcont h hh 2
  have hc1 := hcont f₀ hf 1
  have hcw : Continuous fun t : ℝ => ((1 - t : ℝ) : ℂ) := by fun_prop
  have hI1 : IntervalIntegrable (fun t : ℝ => ((1 - t : ℝ) : ℂ) *
      poissonBracket (poissonBracket h φ) φ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z))
      MeasureTheory.volume 0 1 :=
    (hcw.continuousOn.mul hc2).intervalIntegrable_of_Icc zero_le_one
  have hI2 : IntervalIntegrable (fun t : ℝ =>
      poissonBracket f₀ φ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z))
      MeasureTheory.volume 0 1 := hc1.intervalIntegrable_of_Icc zero_le_one
  have hdb : DifferentiableOn ℂ (poissonBracket h φ) Ω₁ :=
    differentiableOn_adPow hΩ₁ (hφ.mono hΩ₁Ω) hh 1
  have hsplit : ∫ t in (0 : ℝ)..1, poissonBracket
        (fun w => ((1 - t : ℝ) : ℂ) * poissonBracket h φ w + f₀ w) φ
        (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) =
      (∫ t in (0 : ℝ)..1, ((1 - t : ℝ) : ℂ) *
        poissonBracket (poissonBracket h φ) φ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z)) +
      ∫ t in (0 : ℝ)..1, poissonBracket f₀ φ (flow (KAM.hamiltonianVectorFieldℂ φ) Ω t z) := by
    rw [← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    have hm := htraj t ⟨by linarith [ht.1], ht.2⟩
    exact poissonBracket_const_mul_add (hdb.differentiableAt (hΩ₁.mem_nhds hm))
      (hf.differentiableAt (hΩ₁.mem_nhds hm))
  rw [hsplit, T1, T2]
  ring

end Lie

end KAM.Canonical

end
