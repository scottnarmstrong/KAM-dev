/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGMeasure.OneScale
public import KAM.Planetary.PGAssembly.Remainder
public import KAM.Planetary.PGAssembly.FastComplex
public import KAM.Planetary.PGAssembly.FrequencyDefs
public import KAM.Planetary.PGAssembly.FrequencyJets
public import KAM.Planetary.PGAssembly.FrequencyLip
public import KAM.Planetary.PGAssembly.FrequencyBeta

/-!
# P Part 5: constants of the averaged frequency map (`bpP:p5:freq-data`)

`freq_data` produces the analytic constants `PGAnalytic` together with all clauses of
`PGAnalyticSpec` from the data `d : PGData a b` alone: the bi-Lipschitz constants of `bilip`, the
fifth-order remainder constants of `uniform_remainder`, the one-scale Diophantine constant of
`dio_one`, the radius-2 polynomial bounds and the Lipschitz constants (`FrequencyJets`,
`FrequencyLip`, a single data constant `lipConst d` serving as `AN` and `LN`), the complex torsion
inverse (`FrequencyBeta`), and finally a threshold `muStar` with `muStar ≤ min 1 mu0` and the three
smallness inequalities of the source. `pgAnalytic` selects the witness and `pgCU` is the explicit
constant `C_U` of `bpP:p5:freq-inj`. The definitions and the specification are in
`FrequencyDefs`. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FD.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- The polynomial clause of the specification on the radius-`ρ` tube, `ρ ≤ δ/16`. -/
theorem spec_poly_bounds (d : PGData a b) {rho : ℝ} (hρ : rho ≤ (pgExtension d).delta / 16) :
    ∀ mu ∈ Icc 0 d.mu0, ∀ J ∈ {J : Fin (a+b) → ℂ |
      blockFast J ∈ KAM.actionNbhd (closure d.V) rho ∧ ‖blockSlow J‖ < 2},
    ‖jetPolynomial d mu J‖ ≤ lipConst d ∧ ‖fderiv ℂ (jetPolynomial d mu) J‖ ≤ lipConst d ∧
      ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ ≤ lipConst d := by
  intro mu hmu J ⟨hJf, hJs⟩
  have h := jetPolynomial_derivs_bound d hmu (mem_actionNbhd_mono hρ hJf) hJs
  have hle : jpBound d ≤ lipConst d := by
    have h1 := lipRadius_pos d
    have : 0 ≤ 2 * (a : ℝ) * jpBound d / lipRadius d := by
      have := jpBound_ge_one d; positivity
    have : 0 ≤ 2 * (a : ℝ) * (jetK2 d + b * jetK4 d) / lipRadius d := by
      have := jetK2_nonneg d; have := jetK4_nonneg d; positivity
    unfold lipConst; linarith
  exact ⟨h.1.trans hle, h.2.1.trans hle, h.2.2.trans hle⟩

theorem jpBound_le_lipConst (d : PGData a b) : jpBound d ≤ lipConst d := by
  have h1 := lipRadius_pos d
  have : 0 ≤ 2 * (a : ℝ) * jpBound d / lipRadius d := by
    have := jpBound_ge_one d; positivity
  have : 0 ≤ 2 * (a : ℝ) * (jetK2 d + b * jetK4 d) / lipRadius d := by
    have := jetK2_nonneg d; have := jetK4_nonneg d; positivity
  unfold lipConst; linarith

/-- The Lipschitz clause in the fast action. -/
theorem spec_lip_fast (d : PGData a b) {rho : ℝ} (hρ : rho ≤ lipRadius d) :
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) rho,
    ∀ I' ∈ KAM.actionNbhd (closure d.V) rho, ∀ xi : Fin b → ℂ, ‖xi‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I' (Pi.single i 1))‖
          ≤ lipConst d * ‖I - I'‖ ∧
      ‖(jetOmega d mu I + (jetBeta d mu I).mulVec xi) -
        (jetOmega d mu I' + (jetBeta d mu I').mulVec xi)‖ ≤ lipConst d * ‖I - I'‖ := by
  intro mu hmu I hI I' hI' xi hxi
  have hI0 := mem_actionNbhd_mono hρ hI
  have hI0' := mem_actionNbhd_mono hρ hI'
  exact ⟨jpGrad_lip d hmu hxi hI0 hI0', jpTheta_lip d hmu hxi hI0 hI0'⟩

/-- The Lipschitz clause in the slow action. -/
theorem spec_lip_slow (d : PGData a b) {rho : ℝ} (hρ : rho ≤ (pgExtension d).delta / 16) :
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) rho,
    ∀ xi xi' : Fin b → ℂ, ‖xi‖ ≤ 1 → ‖xi'‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi')) I (Pi.single i 1))‖
          ≤ lipConst d * ‖xi - xi'‖ := by
  intro mu hmu I hI xi xi' hxi hxi'
  refine (jpGrad_lip_slow d hmu (mem_actionNbhd_mono hρ hI) hxi hxi').trans ?_
  exact mul_le_mul_of_nonneg_right (jpBound_le_lipConst d) (norm_nonneg _)

/-- The complex torsion inverse bound, from the compactness lower bound. -/
theorem spec_beta_inverse (d : PGData a b) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ mu ∈ Icc 0 d.mu0, ∀ x ∈ closure d.V, ∀ v : Fin b → ℂ,
      m * ‖v‖ ≤ ‖(jetBeta d mu (KAM.realInclusion a x)).mulVec v‖)
    {rho : ℝ} (hρ : rho ≤ betaRadius d m) :
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) rho, ∀ v : Fin b → ℂ,
      ‖v‖ ≤ max 1 (2 / m) * ‖(jetBeta d mu I).mulVec v‖ := by
  intro mu hmu I hI v
  have h := jetBeta_lower_nbhd d hm hlow mu hmu I (mem_actionNbhd_mono hρ hI) v
  have hnn : 0 ≤ ‖(jetBeta d mu I).mulVec v‖ := norm_nonneg _
  have h2 : ‖v‖ ≤ 2 / m * ‖(jetBeta d mu I).mulVec v‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    nlinarith
  exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hnn)

theorem freq_data (d : PGData a b) : ∃ p : PGAnalytic, PGAnalyticSpec d p := by
  have hδ := (pgExtension d).delta_pos
  obtain ⟨rhob, c0, M0, hrhob, hrhobδ, hc0, hM0, hlowb, hupb⟩ := bilip d
  obtain ⟨m, hm, hlowβ⟩ := jetBeta_lower d
  obtain ⟨r1, CQ, hr1, hr1le, hCQ, hrem⟩ := uniform_remainder d
  have htau : ((a + b : ℕ) : ℝ) < ((a + b : ℕ) : ℝ) + 1 := by linarith
  obtain ⟨hCd, hdio⟩ := dio_one d htau
  have hL := lipConst_ge_one d
  have hβr := betaRadius_pos d hm
  have hβle : betaRadius d m ≤ lipRadius d := min_le_left _ _
  have hlr : lipRadius d ≤ (pgExtension d).delta / 16 := by unfold lipRadius; linarith
  set rho : ℝ := min rhob (betaRadius d m) with hrho
  have hrho0 : 0 < rho := lt_min hrhob hβr
  have hrhob' : rho ≤ rhob := min_le_left _ _
  have hrhoβ : rho ≤ betaRadius d m := min_le_right _ _
  have hrholip : rho ≤ lipRadius d := hrhoβ.trans hβle
  set LB : ℝ := max 1 (2 / m) with hLB
  have hLB1 : 1 ≤ LB := le_max_left _ _
  have hLB0 : 0 < LB := by linarith
  set Lam : ℝ := lipConst d with hLam
  set mu : ℝ := min (min 1 d.mu0) (min (c0 / (2 * Lam)) (c0 / (4 * Lam ^ 2 * LB))) with hmu
  have hLam0 : 0 < Lam := by linarith
  have hmu0 : 0 < mu := lt_min (lt_min one_pos d.hmu0)
    (lt_min (by positivity) (by positivity))
  have hmu1 : mu ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hmu2 : mu ≤ d.mu0 := (min_le_left _ _).trans (min_le_right _ _)
  have hmu3 : mu ≤ c0 / (2 * Lam) := (min_le_right _ _).trans (min_le_left _ _)
  have hmu4 : mu ≤ c0 / (4 * Lam ^ 2 * LB) := (min_le_right _ _).trans (min_le_right _ _)
  have e3 : mu * Lam ≤ c0 / 2 := by
    have := mul_le_mul_of_nonneg_right hmu3 hLam0.le
    calc _ ≤ c0 / (2 * Lam) * Lam := this
      _ = c0 / 2 := by field_simp
  have e4 : 4 * mu * Lam ^ 2 * LB ≤ c0 := by
    have := mul_le_mul_of_nonneg_right hmu4 (by positivity : 0 ≤ 4 * Lam ^ 2 * LB)
    calc 4 * mu * Lam ^ 2 * LB = mu * (4 * Lam ^ 2 * LB) := by ring
      _ ≤ c0 / (4 * Lam ^ 2 * LB) * (4 * Lam ^ 2 * LB) := this
      _ = c0 := by field_simp
  have e5 : 2 * mu * Lam ^ 2 * LB < c0 := by nlinarith [mul_pos hLam0 hLam0, mul_pos hLB0 hc0]
  refine ⟨⟨rho, c0, M0, Lam, Lam, LB, mu, max 1 ((pgExtension d).MP *
    KAM.Weighted.coth ((pgExtension d).delta / 4) ^ a), CQ, r1, dioConstant d (((a + b : ℕ) : ℝ) + 1)⟩,
    ?_⟩
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hrho0, hrhob'.trans_lt hrhobδ, hc0, hM0, hL, hL, hLB1, hmu0, hmu1, hmu2,
    le_max_left _ _, le_max_right _ _, hCQ, hr1, hr1le, hCd, e3, e4, e5, le_rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact fun γ hγ => by simpa using hdio γ hγ
  · exact fun z hz z' hz' => hlowb z (mem_actionNbhd_mono hrhob' hz) z'
      (mem_actionNbhd_mono hrhob' hz')
  · exact fun z hz => hupb z (mem_actionNbhd_mono (by linarith) hz)
  · exact spec_lip_fast d hrholip
  · exact spec_lip_slow d (hrholip.trans hlr)
  · exact spec_poly_bounds d (hrholip.trans hlr)
  · exact spec_beta_inverse d hm hlowβ hrhoβ
  · exact fun mu hmu I hI x hx => hrem mu hmu I hI x hx

/-- The chosen analytic constants. -/
def pgAnalytic (d : PGData a b) : PGAnalytic := (freq_data d).choose

/-- The constant `C_U` of `bpP:p5:freq-inj`. -/
def pgCU (p : PGAnalytic) : ℝ :=
  max (p.M0+p.AN+1) (max (4*(p.AN+1)^2*p.LB/p.c0+4) (8*p.LB+4))

theorem pgAnalytic_spec (d : PGData a b) : PGAnalyticSpec d (pgAnalytic d) :=
  (freq_data d).choose_spec

end KAM.Planetary

end
