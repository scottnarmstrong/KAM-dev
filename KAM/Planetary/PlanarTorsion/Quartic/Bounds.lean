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

/-- The secular average at the eccentricity vector: `pref · pairAverage α (qeV I u)`. -/
def qeS (p : PlanarData) (a : Fin 2 → ℝ) (u : Phase 2) : ℝ :=
  -p.G * p.m 0 * p.m 1 / a 1 * p11c_pairAverage (a 0 / a 1) (qeV (p.actions a) u)

/-- Constant, quadratic and quartic part of `qeS`. -/
def qePoly (p : PlanarData) (a : Fin 2 → ℝ) (u : Phase 2) : ℝ :=
  -p.G * p.m 0 * p.m 1 / a 1 * (p11c_laplace (1 / 2) 0 (a 0 / a 1) +
    p11c_pairCoeffs (a 0 / a 1) 0 * (qeA (p.actions a) u 0 + qeA (p.actions a) u 1) +
    p11c_pairCoeffs (a 0 / a 1) 1 * qeD (p.actions a) u) + p11c_quartic (p11c_coeffs p a) u

theorem qe_alpha_mem {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) : a 0 / a 1 ∈ Ioo (0 : ℝ) 1 := by
  have h1 : 0 < a 1 := ha.1.trans ha.2
  exact ⟨div_pos ha.1 h1, (div_lt_one h1).2 ha.2⟩

theorem qeS_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    AnalyticAt ℝ (qeS p a) 0 := by
  have hI : ∀ i, 0 < p.actions a i := qe_actions_pos p hp ha
  have h := (pair_jet _ (qe_alpha_mem ha)).1.comp_of_eq (qeV_analyticAt hI) (qeV_zero _)
  exact analyticAt_const.mul h

theorem qePoly_analyticAt (p : PlanarData) (a : Fin 2 → ℝ) : AnalyticAt ℝ (qePoly p a) 0 := by
  have f0 := qeB_fst 0 (0 : Phase 2)
  have f1 := qeB_fst 1 (0 : Phase 2)
  have s0 := qeB_snd 0 (0 : Phase 2)
  have s1 := qeB_snd 1 (0 : Phase 2)
  have hA0 : AnalyticAt ℝ (fun u : Phase 2 => qeA (p.actions a) u 0) 0 :=
    (qeB_sumsq 0 0).div_const
  have hA1 : AnalyticAt ℝ (fun u : Phase 2 => qeA (p.actions a) u 1) 0 :=
    (qeB_sumsq 1 0).div_const
  have hD : AnalyticAt ℝ (fun u : Phase 2 => qeD (p.actions a) u) 0 := (qeB_dot 0).div_const
  have hq := qe_quartic_analyticAt (p11c_coeffs p a) 0
  unfold qePoly
  fun_prop

theorem qe_cauchy (I : Fin 2 → ℝ) (hI : ∀ i, 0 < I i) (u : Phase 2) :
    qeD I u ^ 2 ≤ qeA I u 0 * qeA I u 1 := by
  have h0 := hI 0
  have h1 := hI 1
  have e0 := Real.sqrt_pos.2 h0
  have e1 := Real.sqrt_pos.2 h1
  have hs : (√(I 0) * √(I 1)) ^ 2 = I 0 * I 1 := by
    rw [mul_pow, Real.sq_sqrt h0.le, Real.sq_sqrt h1.le]
  unfold qeD qeA p11c_pairDot
  rw [div_pow, hs, div_mul_div_comm, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [sq_nonneg (u.1 0 * u.2 1 - u.2 0 * u.1 1)]

theorem qe_sig_sq (I : Fin 2 → ℝ) {u : Phase 2} (h0 : qeA I u 0 ≤ 4) (h1 : qeA I u 1 ≤ 4) :
    qeSig I u ^ 2 = (1 - qeA I u 0 / 4) * (1 - qeA I u 1 / 4) := by
  unfold qeSig
  rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]

/-- The remainder of the secular average after the explicit quartic is `O(‖u‖⁶)`. -/
theorem qe_remainder_bound (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) :
    ∃ C : ℝ, ∀ᶠ u in 𝓝 (0 : Phase 2), |qeS p a u - qePoly p a u| ≤ C * ‖u‖ ^ 6 := by
  have hI : ∀ i, 0 < p.actions a i := qe_actions_pos p hp ha
  set I := p.actions a with hIdef
  set α := a 0 / a 1 with hαdef
  obtain ⟨C0, hC0⟩ := qe_gap_bound (qe_alpha_mem ha)
  set pref := -p.G * p.m 0 * p.m 1 / a 1 with hpref
  set co := p11c_pairCoeffs α with hco
  set K : ℝ := 2 / I 0 + 2 / I 1 with hK
  have hKpos : 0 < K := by have := hI 0; have := hI 1; positivity
  set B : ℝ := (√(I 0))⁻¹ + (√(I 1))⁻¹ with hB
  have hVt : Tendsto (qeV I) (𝓝 0) (𝓝 0) := by
    have := (qeV_analyticAt hI).continuousAt.tendsto
    rwa [qeV_zero] at this
  have hδ : (0 : ℝ) < min 1 (1 / K) := lt_min one_pos (by positivity)
  refine ⟨|pref| * ((∑ i, |co i|) * K ^ 3 + |C0| * B ^ 6), ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Phase 2) hδ, hVt.eventually hC0] with u hu hV
  have hun : ‖u‖ < min 1 (1 / K) := by simpa using hu
  have hu1 : ‖u‖ < 1 := hun.trans_le (min_le_left _ _)
  have hu2 : ‖u‖ < 1 / K := hun.trans_le (min_le_right _ _)
  have hn0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hm : qeA I u 0 + qeA I u 1 ≤ K * ‖u‖ ^ 2 := by
    have a0 := qeA_le hI (u := u) 0
    have a1 := qeA_le hI (u := u) 1
    have : 2 * ‖u‖ ^ 2 / I 0 + 2 * ‖u‖ ^ 2 / I 1 = K * ‖u‖ ^ 2 := by
      rw [hK]; ring
    linarith
  have hm1 : K * ‖u‖ ^ 2 ≤ 1 := by
    have h1 : ‖u‖ ^ 2 ≤ ‖u‖ := by nlinarith
    have h2 : K * ‖u‖ ≤ 1 := by
      have := (lt_div_iff₀ hKpos).1 hu2
      linarith
    nlinarith
  have hA0 := qeA_nonneg hI u 0
  have hA1 := qeA_nonneg hI u 1
  have hle0 : qeA I u 0 ≤ 4 := by linarith
  have hle1 : qeA I u 1 ≤ 4 := by linarith
  have hJ := qe_pairJet_qeV hI α hle0 hle1
  have hq : p11c_quartic (p11c_coeffs p a) u = pref * (qePolyExpr co (qeA I u 0) (qeA I u 1)
      (qeD I u) - co 0 * (qeA I u 0 + qeA I u 1) - co 1 * qeD I u) := by
    unfold p11c_coeffs
    exact qe_quartic_coeffs hI pref co u
  have hid : qeS p a u - qePoly p a u = pref * (qeJetExpr co (qeA I u 0) (qeA I u 1) (qeD I u)
      (qeSig I u) - qePolyExpr co (qeA I u 0) (qeA I u 1) (qeD I u)) +
      pref * (p11c_pairAverage α (qeV I u) - p11c_pairJet α (qeV I u)) := by
    unfold qeS qePoly
    rw [hq, hJ]
    ring
  have halg := qe_alg co (qeA I u 0) (qeA I u 1) (qeD I u) (qeSig I u) hA0 hA1 (by linarith)
    (qe_cauchy I hI u) (by unfold qeSig; positivity) (qe_sig_sq I hle0 hle1)
  have hm3 : (qeA I u 0 + qeA I u 1) ^ 3 ≤ K ^ 3 * ‖u‖ ^ 6 := by
    have := pow_le_pow_left₀ (by linarith) hm 3
    calc (qeA I u 0 + qeA I u 1) ^ 3 ≤ (K * ‖u‖ ^ 2) ^ 3 := this
      _ = K ^ 3 * ‖u‖ ^ 6 := by ring
  have hVn : ‖qeV I u‖ ≤ B * ‖u‖ := qeV_norm_le hI hle0 hle1
  have hV6 : ‖qeV I u‖ ^ 6 ≤ B ^ 6 * ‖u‖ ^ 6 := by
    calc ‖qeV I u‖ ^ 6 ≤ (B * ‖u‖) ^ 6 := pow_le_pow_left₀ (norm_nonneg _) hVn 6
      _ = B ^ 6 * ‖u‖ ^ 6 := by ring
  have hg : |p11c_pairAverage α (qeV I u) - p11c_pairJet α (qeV I u)| ≤
      |C0| * (B ^ 6 * ‖u‖ ^ 6) := by
    calc _ ≤ C0 * ‖qeV I u‖ ^ 6 := hV
      _ ≤ |C0| * ‖qeV I u‖ ^ 6 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C0| * (B ^ 6 * ‖u‖ ^ 6) := mul_le_mul_of_nonneg_left hV6 (abs_nonneg _)
  rw [hid]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 : |pref| * |qeJetExpr co (qeA I u 0) (qeA I u 1) (qeD I u) (qeSig I u) -
      qePolyExpr co (qeA I u 0) (qeA I u 1) (qeD I u)| ≤
      |pref| * ((∑ i, |co i|) * (K ^ 3 * ‖u‖ ^ 6)) :=
    mul_le_mul_of_nonneg_left (halg.trans (mul_le_mul_of_nonneg_left hm3
      (Finset.sum_nonneg fun i _ => abs_nonneg _))) (abs_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hg (abs_nonneg pref)
  calc _ ≤ |pref| * ((∑ i, |co i|) * (K ^ 3 * ‖u‖ ^ 6)) + |pref| * (|C0| * (B ^ 6 * ‖u‖ ^ 6)) :=
        add_le_add h1 h2
    _ = _ := by ring

end KAM.Planetary

end
