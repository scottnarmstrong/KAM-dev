/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet
public import KAM.Planetary.PlanarTorsion.Quartic.Compose
public import KAM.Planetary.PlanarTorsion.Quartic.Defs
public import KAM.Planetary.PlanarTorsion.Quartic.Jet

/-!
# Planar quartic torsion: the sixth-order remainder of the secular average (P11C, package T6)

Blueprint P, Part 11b (`stepP:p11b:qe-an`).  With `qeS p a u = pref · pairAverage α (qeV I u)` and
the polynomial `qePoly p a u` (constant, quadratic and the explicit quartic), the difference is
analytic at `0` and `O(‖u‖⁶)` (`qe_remainder`): the jet of `pairAverage` is `p11c_pairJet`
(`pair_jet`), and its composite with `qeV` is the exact algebra of `qe_alg`.
-/

@[expose] public noncomputable section
open Set Real Function Filter Asymptotics
open scoped Topology ContDiff
namespace KAM.Planetary

private theorem qeB_fst (i : Fin 2) (z : Phase 2) : AnalyticAt ℝ (fun z : Phase 2 => z.1 i) z :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt z

private theorem qeB_snd (i : Fin 2) (z : Phase 2) : AnalyticAt ℝ (fun z : Phase 2 => z.2 i) z :=
  ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt z

theorem qeScale_analyticAt {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) (i : Fin 2) :
    AnalyticAt ℝ (fun u : Phase 2 => qeScale I u i) 0 := by
  have hq : AnalyticAt ℝ (fun z : Phase 2 => (z.1 i ^ 2 + z.2 i ^ 2) / 2 / (2 * I i)) 0 :=
    ((((qeB_fst i 0).pow 2).add ((qeB_snd i 0).pow 2)).div_const).div_const
  have hr : AnalyticAt ℝ (fun z : Phase 2 =>
      (1 - (z.1 i ^ 2 + z.2 i ^ 2) / 2 / (2 * I i)) / I i) 0 :=
    (analyticAt_const.sub hq).div_const
  unfold qeScale
  refine ((hr.contDiffAt (n := ω)).sqrt ?_).analyticAt
  have := (hI i).ne'
  simp [this]

theorem qeV_analyticAt {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) : AnalyticAt ℝ (qeV I) 0 := by
  unfold qeV
  refine AnalyticAt.prod ?_ ?_
  · rw [analyticAt_pi_iff]
    exact fun i => (qeScale_analyticAt hI i).mul (qeB_fst i 0)
  · rw [analyticAt_pi_iff]
    exact fun i => (qeScale_analyticAt hI i).mul (qeB_snd i 0)

theorem qeV_zero (I : Fin 2 → ℝ) : qeV I 0 = 0 := by
  ext i <;> simp [qeV]

theorem qe_sq_le {u : Phase 2} (i : Fin 2) : u.1 i ^ 2 + u.2 i ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  have h1 : ‖u.1 i‖ ≤ ‖u‖ := (norm_le_pi_norm u.1 i).trans (le_max_left _ _)
  have h2 : ‖u.2 i‖ ≤ ‖u‖ := (norm_le_pi_norm u.2 i).trans (le_max_right _ _)
  have h1' : u.1 i ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← sq_abs, ← Real.norm_eq_abs]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' : u.2 i ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [← sq_abs, ← Real.norm_eq_abs]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

theorem qeA_le {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) {u : Phase 2} (i : Fin 2) :
    qeA I u i ≤ 2 * ‖u‖ ^ 2 / I i := by
  unfold qeA
  exact div_le_div_of_nonneg_right (qe_sq_le i) (hI i).le

theorem qeA_nonneg {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) (u : Phase 2) (i : Fin 2) :
    0 ≤ qeA I u i := by
  have := hI i
  unfold qeA; positivity

theorem qeV_norm_le {I : Fin 2 → ℝ} (hI : ∀ i, 0 < I i) {u : Phase 2}
    (h0 : qeA I u 0 ≤ 4) (h1 : qeA I u 1 ≤ 4) :
    ‖qeV I u‖ ≤ ((√(I 0))⁻¹ + (√(I 1))⁻¹) * ‖u‖ := by
  have hB : 0 ≤ ((√(I 0))⁻¹ + (√(I 1))⁻¹) * ‖u‖ := by positivity
  have hc : ∀ i, qeA I u i ≤ 4 → |qeScale I u i| ≤ (√(I i))⁻¹ := by
    intro i hi
    have hs := Real.sqrt_pos.2 (hI i)
    rw [qeScale_eq hI, abs_of_nonneg (by positivity), ← one_div]
    have hnn := qeA_nonneg hI u i
    exact div_le_div_of_nonneg_right (Real.sqrt_le_one.2 (by linarith)) hs.le
  have hcoord : ∀ i, ‖u.1 i‖ ≤ ‖u‖ ∧ ‖u.2 i‖ ≤ ‖u‖ := fun i =>
    ⟨(norm_le_pi_norm u.1 i).trans (le_max_left _ _),
     (norm_le_pi_norm u.2 i).trans (le_max_right _ _)⟩
  have hbd : ∀ i, qeA I u i ≤ 4 → (√(I i))⁻¹ ≤ (√(I 0))⁻¹ + (√(I 1))⁻¹ := by
    intro i _
    have h0' : 0 ≤ (√(I 0))⁻¹ := by positivity
    have h1' : 0 ≤ (√(I 1))⁻¹ := by positivity
    fin_cases i <;> simp
  have key : ∀ (x : Fin 2 → ℝ) (c : Fin 2 → ℝ) (y : Fin 2 → ℝ), (∀ i, qeA I u i ≤ 4 → True) →
      (∀ i, |c i| ≤ (√(I i))⁻¹ ∧ ‖y i‖ ≤ ‖u‖) → x = (fun i => c i * y i) →
      ‖x‖ ≤ ((√(I 0))⁻¹ + (√(I 1))⁻¹) * ‖u‖ := by
    intro x c y _ hcy hx
    rw [hx]
    refine (pi_norm_le_iff_of_nonneg hB).2 fun i => ?_
    rw [norm_mul, Real.norm_eq_abs]
    refine (mul_le_mul (hcy i).1 (hcy i).2 (norm_nonneg _) (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_right (hbd i (by fin_cases i <;> simp [h0, h1])) (norm_nonneg _)
  have hall : ∀ i, qeA I u i ≤ 4 := fun i => by fin_cases i <;> simp [h0, h1]
  refine max_le ?_ ?_
  · exact key _ (qeScale I u) u.1 (fun _ _ => trivial)
      (fun i => ⟨hc i (hall i), (hcoord i).1⟩) rfl
  · exact key _ (qeScale I u) u.2 (fun _ _ => trivial)
      (fun i => ⟨hc i (hall i), (hcoord i).2⟩) rfl

/-- The pair jet as a polynomial in the coordinates (the square root squares away). -/
theorem qe_pairJet_eq (α : ℝ) (z : Phase 2) :
    p11c_pairJet α z = p11c_laplace (1 / 2) 0 α +
      p11c_pairCoeffs α 0 * ((z.1 0 ^ 2 + z.2 0 ^ 2) + (z.1 1 ^ 2 + z.2 1 ^ 2)) +
      p11c_pairCoeffs α 1 * p11c_pairDot z +
      p11c_quartic (fun i => p11c_pairCoeffs α (i.castAdd 2 + 2)) z := by
  unfold p11c_pairJet
  rw [p11c_slowLength, Real.sq_sqrt (by positivity), Fin.sum_univ_two]

private theorem qeB_sumsq (i : Fin 2) (z : Phase 2) :
    AnalyticAt ℝ (fun z : Phase 2 => z.1 i ^ 2 + z.2 i ^ 2) z :=
  ((qeB_fst i z).pow 2).add ((qeB_snd i z).pow 2)

private theorem qeB_dot (z : Phase 2) : AnalyticAt ℝ p11c_pairDot z :=
  ((qeB_fst 0 z).mul (qeB_fst 1 z)).add ((qeB_snd 0 z).mul (qeB_snd 1 z))

theorem qe_quartic_analyticAt (c : Fin 6 → ℝ) (z : Phase 2) :
    AnalyticAt ℝ (p11c_quartic c) z := by
  have f0 := qeB_fst 0 z
  have f1 := qeB_fst 1 z
  have s0 := qeB_snd 0 z
  have s1 := qeB_snd 1 z
  unfold p11c_quartic p11c_pairDot
  simp only []
  fun_prop

theorem qe_pairJet_analyticAt (α : ℝ) (z : Phase 2) : AnalyticAt ℝ (p11c_pairJet α) z := by
  have h : p11c_pairJet α = fun z : Phase 2 => p11c_laplace (1 / 2) 0 α +
      p11c_pairCoeffs α 0 * ((z.1 0 ^ 2 + z.2 0 ^ 2) + (z.1 1 ^ 2 + z.2 1 ^ 2)) +
      p11c_pairCoeffs α 1 * p11c_pairDot z +
      p11c_quartic (fun i => p11c_pairCoeffs α (i.castAdd 2 + 2)) z :=
    funext (qe_pairJet_eq α)
  rw [h]
  have f0 := qeB_fst 0 z
  have f1 := qeB_fst 1 z
  have s0 := qeB_snd 0 z
  have s1 := qeB_snd 1 z
  have hq := qe_quartic_analyticAt (fun i => p11c_pairCoeffs α (i.castAdd 2 + 2)) z
  unfold p11c_pairDot
  fun_prop

/-- The sixth-order bound for the difference of the pair average and its jet. -/
theorem qe_gap_bound {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 (0 : Phase 2),
      |p11c_pairAverage α v - p11c_pairJet α v| ≤ C * ‖v‖ ^ 6 := by
  obtain ⟨han, hjet⟩ := pair_jet α hα
  have hg : AnalyticAt ℝ (fun v => p11c_pairAverage α v - p11c_pairJet α v) 0 :=
    han.sub (qe_pairJet_analyticAt α 0)
  refine qeJet_isBigO_of_jet_zero hg fun j hj z => ?_
  have h1 := iteratedFDeriv_sub_apply (i := j) han.contDiffAt
    (qe_pairJet_analyticAt α 0).contDiffAt
  have h2 := hjet j (by omega)
  change iteratedFDeriv ℝ j (p11c_pairAverage α - p11c_pairJet α) 0 (fun _ => z) = 0
  rw [h1]
  simp [h2]

end KAM.Planetary

end
