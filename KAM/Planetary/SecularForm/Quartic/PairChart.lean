/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Conversion
public import KAM.Planetary.SecularForm.Quartic.Expansion
public import KAM.Planetary.SecularForm.Quartic.ChartAlgebra
public import KAM.Planetary.SecularForm.Quartic.Coefficients
public import KAM.Planetary.SecularForm.Quartic.PairScaling
public import KAM.Planetary.SecularForm.Quartic.PairAnalytic
public import KAM.Planetary.SecularForm.Quartic.Scaling
public import KAM.Planetary.SecularForm.Quartic.PairJet

/-!
# Secular form: the literal `Q₄^{(ij)}` conversion for the pair average

Blueprint P, Part 8, `stepP:p8:q4-a`: for the pair average `S_{ij} = -G mᵢ mⱼ aⱼ⁻¹ 𝒲(α; v₁, v₂)`
(`quartic_pair_scaling`, with `𝒲 = dimensionlessPair` analytic on the separated domain,
`quartic_scaling`) let `𝒲₂ = A |v₁|² + A' |v₂|² + B v₁·v₂` and
`𝒲₄ = ∑ c_m (quarticMonomials v₁ v₂) m` be the quadratic and quartic Taylor parts of `𝒲(α; ·)`
at `v = 0` (they exist, with `𝒲(0)` the
constant term, by `O(2)`-invariance, `taylor_parts_of_invariant`).  Then, with the exact chart
`v = (1 - |u|²/(4Λ))^{1/2} u/√Λ`, the quartic part `∑ quarticCoeff · quarticMonomials` of the pair
average in the canonical coordinates `u` equals
`-G mᵢ mⱼ aⱼ⁻¹ (𝒲₄(u/√Λ) - (A/4 |u₁|⁴/Λ₁² + A'/4 |u₂|⁴/Λ₂² +
B/8 (u₁·u₂/√(Λ₁Λ₂)) (|u₁|²/Λ₁ + |u₂|²/Λ₂)))`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm

variable {n : ℕ} (D : Data n) (i j : Fin n) {I0 J0 : ℝ}

/-- The normalized pair average as a function of the eccentricity vectors at a fixed ratio. -/
private def qpcW (α : ℝ) (v : PairW) : ℝ := dimensionlessPair (α, v.1, v.2)

private theorem qpc_alpha_facts (hI : 0 < I0) (hJ : 0 < J0)
    (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    0 < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) ∧
      0 < I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) ∧
      I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) < 1 := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have ha : 0 < I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) :=
    div_pos (pow_pos hI 2) (mul_pos (pow_pos (D.hm i) 2) hκ)
  have hb : 0 < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)) :=
    div_pos (pow_pos hJ 2) (mul_pos (pow_pos (D.hm j) 2) hκ)
  exact ⟨hb, div_pos ha hb, (div_lt_one hb).2 hab⟩

variable {D i j}

/-- Near `u = 0` the pair average is the prefactor times `𝒲` of the square-root chart. -/
private theorem qpc_pair_eq (hij : i < j) (hI : 0 < I0) (hJ : 0 < J0)
    (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    ∀ᶠ u in 𝓝 (0 : PairW), pairSlowSecular D i j I0 J0 u =
      -D.G * D.m i * D.m j / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) *
        qpcW (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))))
          (sqrtChart I0 u.1, sqrtChart J0 u.2) := by
  obtain ⟨hb, hα0, hα1⟩ := qpc_alpha_facts D i j hI hJ hab
  set α := I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) with hα
  have hc1 := continuous_planeSq_vec
  have hdom : ∀ {L : ℝ}, 0 < L → ∀ᶠ x in 𝓝 (0 : Fin 2 → ℝ),
      (![0, x 0], ![L, x 1]) ∈ poincareDom := fun {L} hL => by
    have hcont : Continuous fun x : Fin 2 → ℝ => planeSq x / 2 := hc1.div_const 2
    filter_upwards [(hcont.tendsto 0).eventually (gt_mem_nhds
      (show planeSq (0 : Fin 2 → ℝ) / 2 < L by simpa [planeSq] using hL))] with x hx
    refine ⟨by simpa using hL, ?_⟩
    simp only [poincareGamma, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : planeSq x = x 0 ^ 2 + x 1 ^ 2 := by simp [planeSq, Fin.sum_univ_two]
    simpa [this] using hx
  have h1 : ∀ᶠ u in 𝓝 (0 : PairW), (![0, u.1 0], ![I0, u.1 1]) ∈ poincareDom :=
    (continuous_fst.tendsto (0 : PairW)).eventually (hdom hI)
  have h2 : ∀ᶠ u in 𝓝 (0 : PairW), (![0, u.2 0], ![J0, u.2 1]) ∈ poincareDom :=
    (continuous_snd.tendsto (0 : PairW)).eventually (hdom hJ)
  have hch : Continuous fun u : PairW => (α, sqrtChart I0 u.1, sqrtChart J0 u.2) := by
    have := continuous_sqrtChart I0
    have := continuous_sqrtChart J0
    fun_prop
  have h3 : ∀ᶠ u in 𝓝 (0 : PairW), (α, sqrtChart I0 u.1, sqrtChart J0 u.2) ∈ separatedDomain :=
    (qsc_isOpen_separatedDomain.preimage hch).mem_nhds (by
      show (α, sqrtChart I0 (0 : PairW).1, sqrtChart J0 (0 : PairW).2) ∈ separatedDomain
      simp only [Prod.fst_zero, Prod.snd_zero, sqrtChart_zero]
      refine ⟨hα0, hα1, ?_, ?_, ?_⟩ <;> simp [planeLength, planeSq]; linarith)
  filter_upwards [h1, h2, h3] with u hu hv hs
  have e1 := poincareV_pair I0 hI (u.1)
  have e2 := poincareV_pair J0 hJ (u.2)
  have := quartic_pair_scaling D hij hI hJ u.1 u.2 hu hv (by
    rw [e1, e2]; exact hs)
  rw [e1, e2] at this
  simpa [qpcW] using this

private theorem qpc_W_invariant (hij : i < j) (hI : 0 < I0) (hJ : 0 < J0)
    (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))
    {R : Matrix (Fin 2) (Fin 2) ℝ} (hR : R.transpose * R = 1) :
    ∀ᶠ v in 𝓝 (0 : PairW),
      qpcW (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))))
        (matW R v) =
      qpcW (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0)))) v := by
  obtain ⟨hb, hα0, hα1⟩ := qpc_alpha_facts D i j hI hJ hab
  set α := I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) with hα
  set κ0 := -D.G * D.m i * D.m j / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) with hκ0
  have hκ : κ0 ≠ 0 := by
    have := D.hG; have := D.hm i; have := D.hm j
    rw [hκ0]; have : 0 < D.G * D.m i * D.m j / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) := by
      positivity
    intro h0
    rw [neg_mul, neg_mul, neg_div] at h0
    linarith [mul_assoc D.G (D.m i) (D.m j)]
  set Φ : PairW → PairW := fun v => (sqrtChartInv I0 v.1, sqrtChartInv J0 v.2) with hΦ
  have hΦc : Continuous Φ := by
    have := continuous_sqrtChartInv I0
    have := continuous_sqrtChartInv J0
    fun_prop
  have hΦ0 : Φ 0 = 0 := Prod.ext (sqrtChartInv_zero I0) (sqrtChartInv_zero J0)
  have hT : Tendsto Φ (𝓝 0) (𝓝 0) := by simpa [hΦ0] using hΦc.tendsto (0 : PairW)
  have hMc : Continuous (matW R) := (matW R).continuous
  have hM : Tendsto (matW R) (𝓝 0) (𝓝 0) := by simpa using hMc.tendsto (0 : PairW)
  have E1 := qpc_pair_eq hij hI hJ hab
  have E2 := pair_matW_invariant D i j hI hJ hab hR
  have hsq : ∀ᶠ v in 𝓝 (0 : PairW), planeSq v.1 < 1 ∧ planeSq v.2 < 1 := by
    have h1 : Continuous fun v : PairW => planeSq v.1 := continuous_planeSq_vec.comp continuous_fst
    have h2 : Continuous fun v : PairW => planeSq v.2 := continuous_planeSq_vec.comp continuous_snd
    exact ((h1.tendsto 0).eventually (gt_mem_nhds (by simp [planeSq]))).and
      ((h2.tendsto 0).eventually (gt_mem_nhds (by simp [planeSq])))
  filter_upwards [hT.eventually E1, (hT.comp hM).eventually E1, hT.eventually E2, hsq]
    with v ha hb' hc ⟨hd1, hd2⟩
  have hv1 : planeSq ((matW R v).1) < 1 := by
    rw [matW_apply]; exact (planeSq_mulVec hR v.1).symm ▸ hd1
  have hv2 : planeSq ((matW R v).2) < 1 := by
    rw [matW_apply]; exact (planeSq_mulVec hR v.2).symm ▸ hd2
  have e1 : (sqrtChart I0 (Φ v).1, sqrtChart J0 (Φ v).2) = v :=
    Prod.ext (sqrtChart_sqrtChartInv hI hd1) (sqrtChart_sqrtChartInv hJ hd2)
  have e2 : Φ (matW R v) = matW R (Φ v) := by
    rw [matW_apply]
    exact Prod.ext (sqrtChartInv_mulVec hR I0 _) (sqrtChartInv_mulVec hR J0 _)
  have e3 : (sqrtChart I0 (Φ (matW R v)).1, sqrtChart J0 (Φ (matW R v)).2) = matW R v :=
    Prod.ext (sqrtChart_sqrtChartInv hI hv1) (sqrtChart_sqrtChartInv hJ hv2)
  simp only [Function.comp_apply] at hb'
  rw [e1] at ha
  rw [e3] at hb'
  rw [e2] at hb'
  have : κ0 * qpcW α (matW R v) = κ0 * qpcW α v := by rw [← hb', hc, ha]
  exact mul_left_cancel₀ hκ this

/-- **The literal `Q₄^{(ij)}` conversion** (`stepP:p8:q4-a`). Let `W(v) = 𝒲(α; v₁, v₂)` be the
normalized pair average (`dimensionlessPair`) at the ratio `α = aᵢ/aⱼ`, which is analytic at
`v = 0`, and `(A, A', B, c)` its quadratic and quartic Taylor coefficients, i.e. the expansion
`W(v) - W(0) - (A |v₁|² + A' |v₂|² + B v₁·v₂) - ∑ c_m (quarticMonomials v₁ v₂) m = O(‖v‖⁵)`
holds.  Then the quartic part `∑ quarticCoeff · quarticMonomials` of the pair average in the
canonical coordinates equals `-G mᵢ mⱼ aⱼ⁻¹ · (W₄(u/√Λ) - (A/4 |u₁|⁴/Λ₁² + A'/4 |u₂|⁴/Λ₂² +
B/8 (u₁·u₂/√(Λ₁Λ₂)) (|u₁|²/Λ₁ + |u₂|²/Λ₂)))`. -/
theorem quartic_pair_chart_conversion (hij : i < j) (hI : 0 < I0) (hJ : 0 < J0)
    (hab : I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) < J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) :
    ∃ (A A' B : ℝ) (c : Fin 6 → ℝ),
      (fun v : PairW =>
        dimensionlessPair (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) /
          (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))), v.1, v.2) -
        dimensionlessPair (I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) /
          (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))), 0, 0) -
        (A * planeSq v.1 + A' * planeSq v.2 + B * planeDot v.1 v.2) -
        ∑ k, c k * quarticMonomials v.1 v.2 k) =O[𝓝 0] (fun v => ‖v‖ ^ 5) ∧
      ∀ w : PairW, ∑ k, quarticCoeff D i j (I0, J0) k * quarticMonomials w.1 w.2 k =
        -D.G * D.m i * D.m j / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) *
          (∑ k, c k * quarticMonomials ((√I0)⁻¹ • w.1) ((√J0)⁻¹ • w.2) k -
            (A / 4 * planeSq w.1 ^ 2 / I0 ^ 2 + A' / 4 * planeSq w.2 ^ 2 / J0 ^ 2 +
              B / 8 * (planeDot w.1 w.2 / (√I0 * √J0)) *
                (planeSq w.1 / I0 + planeSq w.2 / J0))) := by
  obtain ⟨hb, hα0, hα1⟩ := qpc_alpha_facts D i j hI hJ hab
  set α := I0 ^ 2 / (D.m i ^ 2 * (D.G * D.m0)) / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) with hα
  set κ0 := -D.G * D.m i * D.m j / (J0 ^ 2 / (D.m j ^ 2 * (D.G * D.m0))) with hκ0
  have hmem : (α, (0 : Fin 2 → ℝ), (0 : Fin 2 → ℝ)) ∈ separatedDomain := by
    refine ⟨hα0, hα1, ?_, ?_, ?_⟩ <;> simp [planeLength, planeSq] <;> linarith
  have hWan : AnalyticAt ℝ (qpcW α) 0 := by
    have h := quartic_scaling _ hmem
    have h2 : AnalyticAt ℝ (fun v : PairW => (α, v.1, v.2)) 0 :=
      analyticAt_const.prod (analyticAt_fst.prod analyticAt_snd)
    exact AnalyticAt.comp_of_eq h h2 rfl
  obtain ⟨A, A', B, c, -, -, hexp⟩ := taylor_parts_of_invariant (qpcW α) hWan
    (fun R hR => qpc_W_invariant hij hI hJ hab hR)
  refine ⟨A, A', B, c, hexp, fun w => ?_⟩
  have hconv := quartic_sqrt_chart_conversion_const hI hJ A A' B (qpcW α 0) κ0 c (qpcW α) hexp
  -- the pair average itself
  have hPan : AnalyticAt ℝ (fun w : PairW => pairSlowSecular D i j I0 J0 w) 0 := by
    have h1 := analyticAt_pairSlowSecular D i j hI hJ hab
    have h2 : AnalyticAt ℝ (fun w : PairW => (((I0, J0) : ℝ × ℝ), w)) 0 :=
      analyticAt_const.prod analyticAt_id
    exact AnalyticAt.comp_of_eq (f := fun w : PairW => (((I0, J0) : ℝ × ℝ), w))
      (g := fun p : (ℝ × ℝ) × PairW => pairSlowSecular D i j p.1.1 p.1.2 p.2) h1 h2 rfl
  obtain ⟨Au, Au', Bu, cu, -, h4, hexpP⟩ := taylor_parts_of_invariant _ hPan
    (fun R hR => pair_matW_invariant D i j hI hJ hab hR)
  have hq4 : ∀ u : PairW, ∑ k, cu k * quarticMonomials u.1 u.2 k =
      ∑ k, quarticCoeff D i j (I0, J0) k * quarticMonomials u.1 u.2 k := fun u => by
    rw [h4 u, ← pairQuartic_eq D i j hI hJ hab u]; rfl
  set Wq : PairW → ℝ := fun u => qpcW α 0 +
    (A * (planeSq u.1 / I0) + A' * (planeSq u.2 / J0) + B * (planeDot u.1 u.2 / (√I0 * √J0))) +
    (∑ k, c k * quarticMonomials ((√I0)⁻¹ • u.1) ((√J0)⁻¹ • u.2) k -
      (A / 4 * planeSq u.1 ^ 2 / I0 ^ 2 + A' / 4 * planeSq u.2 ^ 2 / J0 ^ 2 +
        B / 8 * (planeDot u.1 u.2 / (√I0 * √J0)) * (planeSq u.1 / I0 + planeSq u.2 / J0)))
    with hWq
  set Pq : PairW → ℝ := fun u => pairSlowSecular D i j I0 J0 0 +
    (Au * planeSq u.1 + Au' * planeSq u.2 + Bu * planeDot u.1 u.2) +
    ∑ k, quarticCoeff D i j (I0, J0) k * quarticMonomials u.1 u.2 k with hPq
  have hD : (fun u : PairW => Pq u - κ0 * Wq u) =O[𝓝 0] fun u => ‖u‖ ^ 5 := by
    refine (hconv.sub hexpP).congr' ?_ EventuallyEq.rfl
    filter_upwards [qpc_pair_eq hij hI hJ hab] with u hu
    simp only [hPq, hWq, hq4 u, hu]
    show _ = _
    simp only [qpcW, sqrtChart]
    ring
  have hT : Tendsto (fun s : ℝ => s • w) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun s : ℝ => s • w := by fun_prop
    simpa using hc.tendsto (0 : ℝ)
  have hnorm : (fun s : ℝ => ‖s • w‖ ^ 5) =O[𝓝 0] fun s : ℝ => ‖s‖ ^ 5 := by
    refine IsBigO.of_bound (‖w‖ ^ 5) (Eventually.of_forall fun s => ?_)
    simp only [norm_smul, mul_pow, norm_pow, norm_norm, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), abs_abs, mul_comm]
  have hray : (fun s : ℝ => Pq (s • w) - κ0 * Wq (s • w)) =O[𝓝 0] fun s : ℝ => ‖s‖ ^ 5 :=
    (hD.comp_tendsto hT).trans hnorm
  set S1 := ∑ k, quarticCoeff D i j (I0, J0) k * quarticMonomials w.1 w.2 k with hS1
  set S2 := ∑ k, c k * quarticMonomials ((√I0)⁻¹ • w.1) ((√J0)⁻¹ • w.2) k with hS2
  set Cr := A / 4 * planeSq w.1 ^ 2 / I0 ^ 2 + A' / 4 * planeSq w.2 ^ 2 / J0 ^ 2 +
    B / 8 * (planeDot w.1 w.2 / (√I0 * √J0)) * (planeSq w.1 / I0 + planeSq w.2 / J0) with hCr
  have hray2 : (fun s : ℝ => (pairSlowSecular D i j I0 J0 0 - κ0 * qpcW α 0) +
      ((Au * planeSq w.1 + Au' * planeSq w.2 + Bu * planeDot w.1 w.2) -
        κ0 * (A * (planeSq w.1 / I0) + A' * (planeSq w.2 / J0) +
          B * (planeDot w.1 w.2 / (√I0 * √J0)))) * s ^ 2 +
      (S1 - κ0 * (S2 - Cr)) * s ^ 4) =O[𝓝 0] fun s => ‖s‖ ^ 5 := by
    refine hray.congr_left (fun s => ?_)
    have e1 : ∑ k, quarticCoeff D i j (I0, J0) k * quarticMonomials (s • w.1) (s • w.2) k =
        s ^ 4 * S1 := by
      simp only [quarticMonomials_smul_vec, hS1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e2 : ∑ k, c k * quarticMonomials ((√I0)⁻¹ • s • w.1) ((√J0)⁻¹ • s • w.2) k =
        s ^ 4 * S2 := by
      simp only [smul_comm ((√I0)⁻¹) s w.1, smul_comm ((√J0)⁻¹) s w.2,
        quarticMonomials_smul_vec, hS2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [hPq, hWq, Prod.smul_fst, Prod.smul_snd, planeSq_smul_vec, planeDot_smul_vec]
    rw [e1, e2]
    ring
  have h0 := quartic_coeff_eq_zero_of_isBigO hray2
  linarith

end SecularForm
end KAM.Planetary
end
