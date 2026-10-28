/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
import KAM.Strip.Bridges
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Taylor formula along the extended flow (`bpN:p11:ext-taylor`, Part 11, package N11-E2)

Along a solution `γ` of `γ' = X^c_φ(γ)` in an open set `Ω` where `φ` and `u` are holomorphic,
`(u ∘ γ)^{(j)} = (ad^j_φ u) ∘ γ` (steps `et-one`, `et-ind`), and Taylor's formula with integral
remainder gives `ext_taylor` (step `et-taylor`), its sup bound `ext_taylor_bound` and the smoothness
statement `ext_taylor_regular`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators ContDiff

namespace KAM.Nekhoroshev

variable {n k : ℕ}

private theorem extAd_succ_left (c : ℝ) (φ : EC n k → ℂ) (j : ℕ) (u : EC n k → ℂ) :
    extAd c φ (j + 1) u = extAd c φ j (extBracket c u φ) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show extBracket c (extAd c φ (j + 1) u) φ = extBracket c (extAd c φ j (extBracket c u φ)) φ
    rw [ih]

private theorem differentiableOn_wfield {Ω : Set (EC n k)} (hΩ : IsOpen Ω) (c : ℝ)
    {φ : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) : DifferentiableOn ℂ (wfield c φ) Ω := by
  have hd : ∀ v : EC n k, DifferentiableOn ℂ (fun z => fderiv ℂ φ z v) Ω := fun v =>
    (KAM.holomorphic_regularity_of_finiteDimensional hΩ hφ).1.clm_apply (differentiableOn_const v)
  refine DifferentiableOn.prodMk (differentiableOn_pi.2 fun i => hd _)
    (differentiableOn_pi.2 fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]
    exact (hd _).neg
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_right, Fin.append_left]
      exact (differentiableOn_const _).mul (hd _)
    · simp only [Fin.append_right, neg_mul]
      exact ((differentiableOn_const _).mul (hd _)).neg

private theorem differentiableOn_extBracket {Ω : Set (EC n k)} (hΩ : IsOpen Ω) (c : ℝ)
    {φ v : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hv : DifferentiableOn ℂ v Ω) :
    DifferentiableOn ℂ (extBracket c v φ) Ω :=
  (KAM.holomorphic_regularity_of_finiteDimensional hΩ hv).1.clm_apply
    (differentiableOn_wfield hΩ c hφ)

private theorem differentiableOn_extAd {Ω : Set (EC n k)} (hΩ : IsOpen Ω) (c : ℝ)
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω) :
    ∀ j : ℕ, DifferentiableOn ℂ (extAd c φ j u) Ω
  | 0 => hu
  | j + 1 => differentiableOn_extBracket hΩ c hφ (differentiableOn_extAd hΩ c hφ hu j)

/-- Step `et-one`: one derivative of `v ∘ γ`. -/
private theorem hasDerivAt_comp {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ v : EC n k → ℂ} (hv : DifferentiableOn ℂ v Ω) {γ : ℝ → EC n k}
    (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t => v (γ t)) (extBracket c v φ (γ t)) t := by
  obtain ⟨hmem, hder⟩ := hγ t ht
  have hvd : DifferentiableAt ℂ v (γ t) := hv.differentiableAt (hΩ.mem_nhds hmem)
  exact (hvd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hder

private theorem contDiffOn_comp {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) {γ : ℝ → EC n k}
    (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ) (m : ℕ) :
    ∀ v : EC n k → ℂ, DifferentiableOn ℂ v Ω → ContDiffOn ℝ m (v ∘ γ) (Icc 0 1) := by
  induction m with
  | zero =>
    intro v hv
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht => (hasDerivAt_comp hΩ hv hγ ht).continuousAt.continuousWithinAt
  | succ m ih =>
    intro v hv
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc zero_lt_one)]
    refine ⟨fun t ht => (hasDerivAt_comp hΩ hv hγ ht).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    refine (ih _ (differentiableOn_extBracket hΩ c hφ hv)).congr fun t ht => ?_
    exact ((hasDerivAt_comp hΩ hv hγ ht).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ht))

private theorem iteratedDerivWithin_comp {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) {γ : ℝ → EC n k}
    (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ) (j : ℕ) :
    ∀ v : EC n k → ℂ, DifferentiableOn ℂ v Ω → ∀ t ∈ Icc (0 : ℝ) 1,
      iteratedDerivWithin j (v ∘ γ) (Icc 0 1) t = extAd c φ j v (γ t) := by
  induction j with
  | zero => intro v _ t _; simp [extAd]
  | succ j ih =>
    intro v hv t ht
    rw [iteratedDerivWithin_succ', extAd_succ_left]
    have hcongr : EqOn (derivWithin (v ∘ γ) (Icc 0 1)) (extBracket c v φ ∘ γ) (Icc 0 1) :=
      fun s hs => ((hasDerivAt_comp hΩ hv hγ hs).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Icc zero_lt_one s hs))
    rw [iteratedDerivWithin_congr hcongr ht]
    exact ih _ (differentiableOn_extBracket hΩ c hφ hv) t ht

/-- Smoothness and the full derivative sequence in the source Taylor statement. -/
theorem ext_taylor_regular {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ) :
    ContDiffOn ℝ ∞ (u ∘ γ) (Icc 0 1) ∧
    ∀ j : ℕ, ∀ t ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin j (u ∘ γ) (Icc 0 1) t = extAd c φ j u (γ t) :=
  ⟨contDiffOn_infty.2 fun m => contDiffOn_comp hΩ hφ hγ m u hu,
    fun j t ht => iteratedDerivWithin_comp hΩ hφ hγ j u hu t ht⟩

theorem ext_taylor {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ)
    (N : ℕ) (hN : 1 ≤ N) :
    u (γ 1) = (∑ j ∈ Finset.range N, ((j.factorial:ℂ)⁻¹)*extAd c φ j u (γ 0)) +
      ∫ t in (0:ℝ)..1, (((1-t)^(N-1)/(N-1).factorial:ℝ):ℂ)*extAd c φ N u (γ t) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hreg := ext_taylor_regular hΩ hφ hu hγ
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hcd : ContDiffOn ℝ (M + 1 : ℕ) (u ∘ γ) (uIcc 0 1) := by
    rw [hI]
    exact hreg.1.of_le (by exact_mod_cast le_top)
  have key := taylor_integral_remainder hcd
  rw [taylor_within_apply] at key
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, iteratedDerivWithin (M + 1) (u ∘ γ) (uIcc 0 1) t =
      extAd c φ (M + 1) u (γ t) := fun t ht => by
    rw [hI]
    exact hreg.2 _ t ht
  have hint0 : ∀ j, iteratedDerivWithin j (u ∘ γ) (uIcc 0 1) 0 = extAd c φ j u (γ 0) :=
    fun j => by
      rw [hI]
      exact hreg.2 _ 0 ⟨le_rfl, zero_le_one⟩
  simp only [hint0] at key
  have hsum : ∑ x ∈ Finset.range (M + 1), (((x.factorial : ℝ)⁻¹ * (1 - 0) ^ x) •
      extAd c φ x u (γ 0)) = ∑ j ∈ Finset.range (M + 1),
        ((j.factorial : ℂ)⁻¹) * extAd c φ j u (γ 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.real_smul]
    simp
  have hintegral : ∫ t in (0:ℝ)..1, (((1 - t) ^ M / M.factorial : ℝ) •
      iteratedDerivWithin (M + 1) (u ∘ γ) (uIcc 0 1) t) =
      ∫ t in (0:ℝ)..1, (((1-t)^(M+1-1)/(M+1-1).factorial:ℝ):ℂ) *
        extAd c φ (M + 1) u (γ t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [hI] at ht
    simp only [hint t ht, Complex.real_smul, Nat.add_sub_cancel]
  rw [hintegral, hsum] at key
  have e : (u ∘ γ) 1 = u (γ 1) := rfl
  linear_combination key - e

/-- Taylor remainder bound, without choosing a maximum on an empty set. -/
theorem ext_taylor_bound {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ)
    (N : ℕ) (hN : 1 ≤ N) (B : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖extAd c φ N u (γ t)‖ ≤ B) :
    ‖∫ t in (0:ℝ)..1, (((1-t)^(N-1)/(N-1).factorial:ℝ):ℂ)*extAd c φ N u (γ t)‖ ≤
      B/N.factorial := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hf : (M.factorial : ℝ) ≠ 0 := by positivity
  have hw : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (1 - t) ^ M / M.factorial := fun t ht =>
    div_nonneg (pow_nonneg (sub_nonneg.2 ht.2) _) (by positivity)
  have hint : ∫ t in (0:ℝ)..1, (1 - t) ^ M / M.factorial * B = B / (M + 1).factorial := by
    have h1 : ∫ t in (0:ℝ)..1, (1 - t) ^ M = 1 / (M + 1) := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ M) 1]
      simp
    have h2 : ∫ t in (0:ℝ)..1, (1 - t) ^ M / M.factorial * B =
        (∫ t in (0:ℝ)..1, (1 - t) ^ M) * (B / M.factorial) := by
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [h2, h1, Nat.factorial_succ]
    push_cast
    field_simp
  rw [← hint]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Filter.Eventually.of_forall fun t ht => ?_) ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Nat.add_sub_cancel,
      abs_of_nonneg (hw t ⟨ht.1.le, ht.2⟩)]
    exact mul_le_mul_of_nonneg_left (hb t ⟨ht.1.le, ht.2⟩) (hw t ⟨ht.1.le, ht.2⟩)
  · apply Continuous.intervalIntegrable
    fun_prop

end KAM.Nekhoroshev

end
