/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Boundedness of `a(θ) = P(θ,0,0,0)` (blueprint-W `bpW:w5:taylor` (i), step `t-comp`)

`P(θ,0,0,0)` is `1`-periodic and its `θ`-gradient is `-2π X^y`, bounded by `2π r² ε`; hence it is
bounded on the strip by its sup over the unit cube plus `4π r² ε s`.
-/

@[expose] public noncomputable section

open Metric Set Filter Topology

namespace KAM.Wave

open KAM

variable {a p pb s r : ℝ} {P : KamPhase → ℂ} {X : KamPhase → KamPhase}

/-- The real points of the angle slice. -/
def taylorRealPt (x : Fin 2 → ℝ) : Fin 2 → ℂ := fun i => (x i : ℂ)

theorem realPt_mem_strip (hs : 0 < s) (x : Fin 2 → ℝ) : taylorRealPt x ∈ complexStrip 2 s :=
    fun i => by
  simpa [taylorRealPt] using hs

theorem tA0_real_bound (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) :
    ∃ M0 : ℝ, ∀ x : Fin 2 → ℝ, ‖tA0 P (taylorRealPt x)‖ ≤ M0 := by
  set Q : (Fin 2 → ℝ) → ℂ := fun x => tA0 P (taylorRealPt x) with hQ
  have hcont : Continuous Q := by
    have h1 : Continuous fun x : Fin 2 → ℝ => stepW0L (taylorRealPt x) := by
      unfold taylorRealPt; exact stepW0L.continuous.comp (by fun_prop)
    exact hP.holoP.continuousOn.comp_continuous h1 (fun x => stepW0L_mem hr (realPt_mem_strip hs x))
  have hper1 : ∀ i y, Q (y + Pi.single i 1) = Q y := fun i y => by
    have : taylorRealPt (y + Pi.single i 1) = taylorRealPt y + Pi.single i 1 := by
      funext j; by_cases h : j = i <;> simp [taylorRealPt, Pi.single_apply, h]
    simp only [hQ]
    rw [this]
    exact tA0_periodic ha hqq hr hP hper i (realPt_mem_strip hs y)
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (0 : Fin 2 → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M0, fun x => ?_⟩
  have hper_coord : ∀ i (y : Fin 2 → ℝ), Q y = Q (Function.update y i (Int.fract (y i))) := by
    intro i y
    have hp : Function.Periodic (fun t : ℝ => Q (Function.update y i t)) 1 := fun t => by
      have : Function.update y i (t + 1) = Function.update y i t + Pi.single i 1 := by
        funext j; by_cases h : j = i <;> simp [Function.update_apply, Pi.single_apply, h]
      simp only [this]; exact hper1 i _
    have h2 := hp.sub_int_mul_eq (x := y i) ⌊y i⌋
    simp only [mul_one] at h2
    have h3 : y i - (⌊y i⌋ : ℝ) = Int.fract (y i) := rfl
    rw [h3] at h2
    simpa using h2.symm
  have hx1 : Q x = Q (Function.update x 0 (Int.fract (x 0))) := hper_coord 0 x
  set x1 := Function.update x 0 (Int.fract (x 0))
  have hx2 : Q x1 = Q (Function.update x1 1 (Int.fract (x1 1))) := hper_coord 1 x1
  set x2 := Function.update x1 1 (Int.fract (x1 1))
  have hmem : x2 ∈ Icc (0 : Fin 2 → ℝ) 1 := by
    constructor <;> intro i <;> fin_cases i <;> simp [x2, x1, Int.fract_nonneg, (Int.fract_lt_one
        _).le]
  show ‖Q x‖ ≤ M0
  rw [hx1, hx2]
  exact hM0 x2 hmem

theorem taylorConvex_complexStrip (s : ℝ) : Convex ℝ (complexStrip 2 s) := by
  intro θ hθ θ' hθ' c d hc hd hcd i
  have h1 := hθ i
  have h2 := hθ' i
  have e : ((c • θ + d • θ') i).im = c * (θ i).im + d * (θ' i).im := by simp
  rw [e]
  calc |c * (θ i).im + d * (θ' i).im| ≤ |c * (θ i).im| + |d * (θ' i).im| := abs_add_le _ _
    _ = c * |(θ i).im| + d * |(θ' i).im| := by rw [abs_mul, abs_mul, abs_of_nonneg hc,
        abs_of_nonneg hd]
    _ < c * s + d * s := by
        rcases hc.eq_or_lt with h | h
        · subst h
          have : 0 < d := by linarith
          nlinarith
        · nlinarith
    _ = s := by rw [← add_mul, hcd, one_mul]

theorem norm_fderiv_tA0_le (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) :
    ‖fderiv ℂ (tA0 P) θ‖ ≤ 4 * Real.pi * r ^ 2 * ε := by
  have hε : 0 ≤ ε := (kamNorm_nonneg hr.le _).trans (hb _ (stepW0L_mem hr hθ))
  have hd : HasFDerivAt (tA0 P) ((fderiv ℂ P (stepW0L θ)).comp stepW0L) θ := by
    have h1 : DifferentiableAt ℂ P (stepW0L θ) :=
      hP.holoP.differentiableAt ((kamDomain_isOpen s r).mem_nhds (stepW0L_mem hr hθ))
    exact h1.hasFDerivAt.comp θ stepW0L.hasFDerivAt
  rw [hd.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have hz := stepW0L_mem hr hθ
  simp only [ContinuousLinearMap.comp_apply]
  rw [hP.deriv_eq _ hz]
  have hy : ‖(X (stepW0L θ)).2.1‖ ≤ r ^ 2 * ε := by
    have := hb _ hz
    unfold kamNorm at this
    have h1 : 0 ≤ ‖(X (stepW0L θ)).1‖ := norm_nonneg _
    have h2 : 0 ≤ ‖(X (stepW0L θ)).2.2.1‖ / r := by positivity
    have h3 : 0 ≤ ‖(X (stepW0L θ)).2.2.2‖ / r := by positivity
    have h4 : ‖(X (stepW0L θ)).2.1‖ / r ^ 2 ≤ ε := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm] at h4
  unfold stepSymp
  simp only [stepW0L_apply, Prod.snd_zero, Prod.fst_zero, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_sub, map_zero, sub_zero, ContinuousLinearMap.zero_apply]
  have hy' : ‖(X (θ, 0, 0, 0)).2.1‖ ≤ r ^ 2 * ε := hy
  have hS := norm_sum_two_le (X (θ, 0, 0, 0)).2.1 h
  rw [add_zero, norm_mul, norm_neg]
  have h2π : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul]; simp [abs_of_pos Real.pi_pos]
  have hS2 : ‖∑ i, (X (θ, 0, 0, 0)).2.1 i * h i‖ ≤ 2 * (r ^ 2 * ε * ‖h‖) :=
    hS.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy' (norm_nonneg _))
      (by norm_num))
  rw [h2π]
  nlinarith [Real.pi_pos]

theorem tA0_bounded (ha : 0 ≤ a) (hqq : 0 ≤ pb + p) (hs : 0 < s) (hr : 0 < r)
    (hP : IsSmoothing (p := p) ha hqq (kamDomain s r) P X)
    (hper : ∀ i, ∀ w ∈ kamDomain s r, P (w + stepTau i) = P w) {ε : ℝ}
    (hb : ∀ z ∈ kamDomain s r, kamNorm r (X z) ≤ ε) :
    ∃ C : ℝ, ∀ θ ∈ complexStrip 2 s, ‖tA0 P θ‖ ≤ C := by
  obtain ⟨M0, hM0⟩ := tA0_real_bound ha hqq hs hr hP hper
  have hε : 0 ≤ ε := (kamNorm_nonneg hr.le _).trans (hb _ (stepW0L_mem hr (realPt_mem_strip hs 0)))
  refine ⟨M0 + 4 * Real.pi * r ^ 2 * ε * s, fun θ hθ => ?_⟩
  set x : Fin 2 → ℝ := fun i => (θ i).re with hx
  have hdiff : ∀ θ' ∈ complexStrip 2 s, DifferentiableAt ℝ (tA0 P) θ' := fun θ' hθ' =>
    (((tA0_differentiableOn ha hqq hr hP).differentiableAt
      ((isOpen_complexStrip 2 s).mem_nhds hθ'))).restrictScalars ℝ
  have hbd : ∀ θ' ∈ complexStrip 2 s, ‖fderiv ℝ (tA0 P) θ'‖ ≤ 4 * Real.pi * r ^ 2 * ε := by
    intro θ' hθ'
    have hc := norm_fderiv_tA0_le ha hqq hr hP hb hθ'
    have hd' : DifferentiableAt ℂ (tA0 P) θ' :=
      (tA0_differentiableOn ha hqq hr hP).differentiableAt ((isOpen_complexStrip 2 s).mem_nhds hθ')
    rw [hd'.fderiv_restrictScalars ℝ]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    exact ((fderiv ℂ (tA0 P) θ').le_opNorm h).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hseg := (taylorConvex_complexStrip s).norm_image_sub_le_of_norm_fderiv_le hdiff hbd
    (realPt_mem_strip hs x) hθ
  have hdist : ‖θ - taylorRealPt x‖ ≤ s := by
    refine (pi_norm_le_iff_of_nonneg hs.le).2 fun i => ?_
    have : θ i - taylorRealPt x i = (θ i).im * Complex.I := by
      simp [taylorRealPt, hx]; apply Complex.ext <;> simp
    show ‖θ i - taylorRealPt x i‖ ≤ s
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact (hθ i).le
  have h1 := hM0 x
  calc ‖tA0 P θ‖ ≤ ‖tA0 P (taylorRealPt x)‖ + ‖tA0 P θ - tA0 P (taylorRealPt x)‖ :=
        norm_le_insert' _ _
    _ ≤ M0 + 4 * Real.pi * r ^ 2 * ε * ‖θ - taylorRealPt x‖ :=
        add_le_add h1 hseg
    _ ≤ M0 + 4 * Real.pi * r ^ 2 * ε * s := by
        have : 0 ≤ 4 * Real.pi * r ^ 2 * ε := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hdist this]

end KAM.Wave
