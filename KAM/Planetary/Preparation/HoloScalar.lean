/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Patch
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Strip.AnalyticTaylor
public import KAM.Nekhoroshev.Interfaces.Norms

/-!
# The Keplerian part of the holomorphic secular data (P11A-P2b, `stepP:p11:hc-rot`/`hc-F`)

The explicit holomorphic Keplerian energy `p11HoloH D J = -∑ᵢ (2π²cᵢ)/Jᵢ²`, `cᵢ = (G m₀)² mᵢ³`
(the value `-∑ᵢ cᵢ/(2 (Jᵢ/2π)²)` of the specification on real points) and its gradient
`p11HoloFreq D J`, the frequency `∂ᵢ h`, together with the jet bound by compactness
`p11_jet_bound_complex` giving the constant `L` of `P11SecularSpec`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace KAM.Planetary

section Scalar

variable {n : ℕ}

/-- The holomorphic Keplerian energy. -/
def p11HoloH (D : P11Physical n) (J : P11CVec n) : ℂ :=
  -∑ i, ((2 * Real.pi ^ 2 * ((D.G * D.m0) ^ 2 * D.m i ^ 3) : ℝ) : ℂ) / J i ^ 2

/-- The gradient of `p11HoloH` (the Keplerian frequency in the variable `J`). -/
def p11HoloFreq (D : P11Physical n) (J : P11CVec n) : P11CVec n := fun i =>
  ((4 * Real.pi ^ 2 * ((D.G * D.m0) ^ 2 * D.m i ^ 3) : ℝ) : ℂ) / J i ^ 3

/-- The set where no coordinate vanishes. -/
def p11NonVanishing (n : ℕ) : Set (P11CVec n) := {J | ∀ i, J i ≠ 0}

theorem isOpen_p11NonVanishing (n : ℕ) : IsOpen (p11NonVanishing n) := by
  have : p11NonVanishing n = ⋂ i, {J : P11CVec n | J i ≠ 0} := by ext; simp [p11NonVanishing]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const

/-- A ball around a real point with positive coordinates avoids the coordinate hyperplanes. -/
theorem exists_ball_nonvanishing {J0 : P11Vec n} (hJ0 : ∀ i, 0 < J0 i) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (KAM.realInclusion n J0) r ⊆ p11NonVanishing n := by
  set S : ℝ := ∑ i, (J0 i)⁻¹ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (inv_pos.2 (hJ0 i)).le
  refine ⟨(S + 1)⁻¹, by positivity, fun J hJ i => ?_⟩
  have h1 : ‖J i - (J0 i : ℂ)‖ < (S + 1)⁻¹ := by
    have := (norm_le_pi_norm (J - KAM.realInclusion n J0) i).trans_lt
      (mem_ball_iff_norm.1 hJ)
    simpa using this
  have h2 : (J0 i)⁻¹ ≤ S := Finset.single_le_sum (f := fun i => (J0 i)⁻¹)
    (fun i _ => (inv_pos.2 (hJ0 i)).le) (Finset.mem_univ i)
  have h3 : (S + 1)⁻¹ < J0 i := by
    rw [inv_lt_comm₀ (by positivity) (hJ0 i)]; linarith
  intro h0
  rw [h0, zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg (hJ0 i).le] at h1
  linarith

theorem differentiableOn_p11HoloH (D : P11Physical n) :
    DifferentiableOn ℂ (p11HoloH D) (p11NonVanishing n) := by
  intro J hJ
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold p11HoloH
  refine DifferentiableAt.neg (DifferentiableAt.fun_sum fun i _ => ?_)
  have := hJ i
  fun_prop (disch := exact pow_ne_zero 2 (hJ i))

theorem differentiableOn_p11HoloFreq (D : P11Physical n) :
    DifferentiableOn ℂ (p11HoloFreq D) (p11NonVanishing n) := by
  refine differentiableOn_pi.2 fun i => fun J hJ => ?_
  refine DifferentiableAt.differentiableWithinAt ?_
  show DifferentiableAt ℂ (fun J : P11CVec n =>
    ((4 * Real.pi ^ 2 * ((D.G * D.m0) ^ 2 * D.m i ^ 3) : ℝ) : ℂ) / J i ^ 3) J
  have := hJ i
  fun_prop (disch := exact pow_ne_zero 3 (hJ i))

/-- The frequency is the gradient of the energy. -/
theorem fderiv_p11HoloH (D : P11Physical n) {J : P11CVec n} (hJ : J ∈ p11NonVanishing n)
    (i : Fin n) : fderiv ℂ (p11HoloH D) J (Pi.single i 1) = p11HoloFreq D J i := by
  set c : Fin n → ℂ := fun k => ((2 * Real.pi ^ 2 * ((D.G * D.m0) ^ 2 * D.m k ^ 3) : ℝ) : ℂ)
    with hc
  have hk : ∀ k : Fin n, HasFDerivAt (fun J : P11CVec n => c k / J k ^ 2)
      ((c k * (-(((2 : ℕ) : ℂ) * J k ^ (2 - 1)) / (J k ^ 2) ^ 2)) •
        ContinuousLinearMap.proj (R := ℂ) k) J :=
    fun k => by
      have h1 := ((hasDerivAt_pow 2 (J k)).inv (pow_ne_zero 2 (hJ k))).const_mul (c k)
      have h2 := HasDerivAt.comp_hasFDerivAt (f := fun J : P11CVec n => J k) J h1
        (hasFDerivAt_apply (𝕜 := ℂ) k J)
      have : (fun J : P11CVec n => c k / J k ^ 2) = fun J => c k * (J k ^ 2)⁻¹ := by
        funext J; rw [div_eq_mul_inv]
      rw [this]
      exact h2
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => hk k).fun_neg
  have hH : p11HoloH D = fun J => -∑ k, c k / J k ^ 2 := rfl
  rw [hH, hs.fderiv]
  simp only [neg_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  have hJi := hJ i
  simp only [p11HoloFreq, hc]
  norm_num
  field_simp
  ring


theorem p11HoloH_re (D : P11Physical n) {J : P11Vec n} (hJ : ∀ i, J i ≠ 0) :
    (p11HoloH D (KAM.realInclusion n J)).re =
      -∑ i, (D.G * D.m0) ^ 2 * D.m i ^ 3 / (2 * (J i / (2 * Real.pi)) ^ 2) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have : p11HoloH D (KAM.realInclusion n J) =
      ((-∑ i, 2 * Real.pi ^ 2 * ((D.G * D.m0) ^ 2 * D.m i ^ 3) / J i ^ 2 : ℝ) : ℂ) := by
    simp [p11HoloH]
  rw [this, Complex.ofReal_re]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hJ i
  field_simp

theorem p11HoloFreq_re (D : P11Physical n) {J : P11Vec n} (hJ : ∀ i, J i ≠ 0) (i : Fin n) :
    (p11HoloFreq D (KAM.realInclusion n J) i).re =
      (D.G * D.m0) ^ 2 * D.m i ^ 3 / ((J i / (2 * Real.pi)) ^ 3 * (2 * Real.pi)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have : p11HoloFreq D (KAM.realInclusion n J) i =
      ((4 * Real.pi ^ 2 * ((D.G * D.m0) ^ 2 * D.m i ^ 3) / J i ^ 3 : ℝ) : ℂ) := by
    simp [p11HoloFreq]
  rw [this, Complex.ofReal_re]
  have := hJ i
  field_simp
  ring

/-- Jet bounds on a smaller ball by compactness (the constant `L` of `P11SecularSpec`), together
with the Euclidean bound. -/
theorem p11_jet_bound_complex {m : ℕ} {c : P11CVec n} {r0 ρ : ℝ} (hρ : ρ < r0)
    {W : P11CVec n → P11CVec m} (hW : DifferentiableOn ℂ W (Metric.ball c r0)) (k : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ J ∈ Metric.ball c ρ, (∀ j ≤ k, ‖iteratedFDeriv ℂ j W J‖ ≤ L) ∧
      KAM.Nekhoroshev.euclid (W J) ≤ L := by
  have hopen : IsOpen (Metric.ball c r0) := Metric.isOpen_ball
  have hcd : ContDiffOn ℂ k W (Metric.ball c r0) :=
    (KAM.analyticOnNhd_of_differentiableOn hopen hW).contDiffOn_of_completeSpace
  have hK : IsCompact (Metric.closedBall c ρ) := isCompact_closedBall _ _
  have hsub : Metric.closedBall c ρ ⊆ Metric.ball c r0 := Metric.closedBall_subset_ball hρ
  have hjet : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ (j ≤ k → ∀ J ∈ Metric.closedBall c ρ,
      ‖iteratedFDeriv ℂ j W J‖ ≤ B) := fun j => by
    by_cases hj : j ≤ k
    · have hc : ContinuousOn (iteratedFDeriv ℂ j W) (Metric.ball c r0) :=
        ContinuousOn.continuousOn_iteratedFDeriv hcd hopen (by exact_mod_cast hj)
      obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hsub).norm
      refine ⟨max B 0, le_max_right _ _, fun _ J hJ => ?_⟩
      have := hB J hJ
      rw [Real.norm_of_nonneg (norm_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose B hB0 hB using hjet
  have hcont : ContinuousOn W (Metric.ball c r0) := hW.continuousOn
  have heu : ContinuousOn (fun J => KAM.Nekhoroshev.euclid (W J)) (Metric.ball c r0) := by
    unfold KAM.Nekhoroshev.euclid
    refine (Real.continuous_sqrt.comp_continuousOn ?_)
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact (((continuous_apply i).comp_continuousOn hcont).norm).pow 2
  obtain ⟨E, hE⟩ := hK.exists_bound_of_continuousOn (heu.mono hsub)
  refine ⟨max 1 (∑ j ∈ Finset.range (k + 1), B j + max E 0),
    le_max_left _ _, fun J hJ => ⟨fun j hj => ?_, ?_⟩⟩
  · have hJ' := Metric.ball_subset_closedBall hJ
    refine (hB j hj J hJ').trans ((le_trans ?_ (le_add_of_nonneg_right (le_max_right _ _))).trans
      (le_max_right _ _))
    exact Finset.single_le_sum (f := B) (fun j _ => hB0 j)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · have hJ' := Metric.ball_subset_closedBall hJ
    have := hE J hJ'
    have h0 : 0 ≤ KAM.Nekhoroshev.euclid (W J) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg h0] at this
    refine this.trans ((le_max_left E 0).trans ?_)
    refine (le_add_of_nonneg_left (Finset.sum_nonneg (s := Finset.range (k + 1))
      fun j _ => hB0 j)).trans ?_
    exact le_max_right _ _

end Scalar

end KAM.Planetary

end
