/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Family

/-!
# P Part 5: real forms of the analytic frequency bounds (`stepP:p5:bu-dio`, inputs)

The S4 premises `N1`, `N2`, `N3` of the P4 measure data are real statements about the frozen
frequency map `freq` on `V`. They are read off the complex specification `PGAnalyticSpec` through
the real slice: gradient and slow frequency of `jetPolynomial` agree with the real formulas
(`jpGrad_realSlice`, `jetOmega_real`, `jetBeta_real`) and the inclusion `ℝⁿ → ℂⁿ` is isometric.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-BU.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Planetary

variable {a b : ℕ}

theorem jetBeta_mulVec_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℝ}
    (hI : I ∈ d.V) (v : Fin b → ℝ) :
    (jetBeta d mu (KAM.realInclusion a I)).mulVec (KAM.realInclusion b v) =
      KAM.realInclusion b ((d.beta mu I).mulVec v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, jetBeta_real d hmu hI, KAM.realInclusion_apply]
  push_cast
  rfl

theorem jpTheta_realSlice (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℝ}
    (hI : I ∈ d.V) (ξ : Fin b → ℝ) :
    jpTheta d mu (KAM.realInclusion b ξ) (KAM.realInclusion a I) =
      KAM.realInclusion b (slowFrequency d.Omega d.beta mu I ξ) := by
  funext j
  have := congrFun (jetBeta_mulVec_real d hmu hI ξ) j
  simp only [jpTheta, slowFrequency, Pi.add_apply, jetOmega_real d hmu hI, this,
    KAM.realInclusion_apply]
  push_cast
  rfl

/-- The fast part of the frozen frequency map on a real point of `V`. -/
theorem blockFast_freq_append (d : PGData a b) (mu : ℝ) (I : Fin a → ℝ) (ξ : Fin b → ℝ) :
    (blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append I ξ)) : Fin a → ℝ) =
      fastFrequency d.H0 I + mu • fun i => fderiv ℝ
        (fun I' => secularPolynomial d.P0 d.Omega d.beta mu I' ξ) I (Pi.single i 1) := by
  have hf : (blockFast (Fin.append I ξ : Fin (a+b) → ℝ) : Fin a → ℝ) = I := by
    funext i; simp [blockFast, Fin.append_left]
  have hs : (blockSlow (Fin.append I ξ : Fin (a+b) → ℝ) : Fin b → ℝ) = ξ := by
    funext i; simp [blockSlow, Fin.append_right]
  funext i
  simp [blockFast, freq, Fin.append_left, hf, hs]

theorem jpGrad_real_eq (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℝ}
    (hI : I ∈ d.V) (ξ : Fin b → ℝ) :
    KAM.realInclusion a (fun i => fderiv ℝ
        (fun I' => secularPolynomial d.P0 d.Omega d.beta mu I' ξ) I (Pi.single i 1)) =
      jpGrad d mu (KAM.realInclusion b ξ) (KAM.realInclusion a I) :=
  (jpGrad_realSlice d hmu hI ξ).symm

theorem real_N1 (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I I' : Fin a → ℝ}
    (hI : I ∈ d.V) (hI' : I' ∈ d.V) {ξ : Fin b → ℝ} (hξ : ‖ξ‖ ≤ 1) :
    ‖(blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append I ξ)) : Fin a → ℝ) -
        fastFrequency d.H0 I -
      ((blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append I' ξ)) : Fin a → ℝ) -
        fastFrequency d.H0 I')‖ ≤ mu*(pgAnalytic d).LN*‖I-I'‖ ∧
    ‖slowFrequency d.Omega d.beta mu I ξ - slowFrequency d.Omega d.beta mu I' ξ‖ ≤
      (pgAnalytic d).LN*‖I-I'‖ := by
  obtain ⟨hρ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN1, -⟩ :=
    pgAnalytic_spec d
  have hδ := hρ
  have hI1 := realInclusion_mem_actionNbhd hδ (subset_closure hI)
  have hI1' := realInclusion_mem_actionNbhd hδ (subset_closure hI')
  have hξ' : ‖KAM.realInclusion b ξ‖ ≤ 1 := by rwa [KAM.norm_realInclusion]
  obtain ⟨h1, h2⟩ := hN1 mu hmu _ hI1 _ hI1' _ hξ'
  change ‖jpGrad d mu (KAM.realInclusion b ξ) (KAM.realInclusion a I) -
    jpGrad d mu (KAM.realInclusion b ξ) (KAM.realInclusion a I')‖ ≤ _ at h1
  have e : ‖KAM.realInclusion a I - KAM.realInclusion a I'‖ = ‖I-I'‖ := by
    rw [← map_sub, KAM.norm_realInclusion]
  constructor
  · rw [blockFast_freq_append, blockFast_freq_append]
    have : fastFrequency d.H0 I + mu • (fun i => fderiv ℝ
        (fun I'' => secularPolynomial d.P0 d.Omega d.beta mu I'' ξ) I (Pi.single i 1)) -
        fastFrequency d.H0 I - (fastFrequency d.H0 I' + mu • (fun i => fderiv ℝ
        (fun I'' => secularPolynomial d.P0 d.Omega d.beta mu I'' ξ) I' (Pi.single i 1)) -
        fastFrequency d.H0 I') = mu • ((fun i => fderiv ℝ
        (fun I'' => secularPolynomial d.P0 d.Omega d.beta mu I'' ξ) I (Pi.single i 1)) -
        (fun i => fderiv ℝ
        (fun I'' => secularPolynomial d.P0 d.Omega d.beta mu I'' ξ) I' (Pi.single i 1))) := by
      simp only [add_sub_cancel_left, smul_sub]
    rw [this, norm_smul, Real.norm_of_nonneg hmu.1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hmu.1
    rw [← KAM.norm_realInclusion, map_sub, jpGrad_real_eq d hmu hI, jpGrad_real_eq d hmu hI']
    exact h1.trans (by rw [e])
  · rw [← KAM.norm_realInclusion, map_sub, ← jpTheta_realSlice d hmu hI,
      ← jpTheta_realSlice d hmu hI']
    exact h2.trans (by rw [e])

theorem real_N2 (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℝ}
    (hI : I ∈ d.V) {ξ ξ' : Fin b → ℝ} (hξ : ‖ξ‖ ≤ 1) (hξ' : ‖ξ'‖ ≤ 1) :
    ‖(blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append I ξ)) : Fin a → ℝ) -
      blockFast (freq d.H0 d.P0 d.Omega d.beta mu (Fin.append I ξ'))‖ ≤
        mu*(pgAnalytic d).LN*‖ξ-ξ'‖ := by
  obtain ⟨hρ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hN2, -⟩ :=
    pgAnalytic_spec d
  have hI1 := realInclusion_mem_actionNbhd hρ (subset_closure hI)
  have h1 := hN2 mu hmu _ hI1 (KAM.realInclusion b ξ) (KAM.realInclusion b ξ')
    (by rwa [KAM.norm_realInclusion]) (by rwa [KAM.norm_realInclusion])
  change ‖jpGrad d mu (KAM.realInclusion b ξ) (KAM.realInclusion a I) -
    jpGrad d mu (KAM.realInclusion b ξ') (KAM.realInclusion a I)‖ ≤ _ at h1
  rw [blockFast_freq_append, blockFast_freq_append, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, Real.norm_of_nonneg hmu.1, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hmu.1
  rw [← KAM.norm_realInclusion, map_sub, jpGrad_real_eq d hmu hI, jpGrad_real_eq d hmu hI]
  exact h1.trans (by rw [← map_sub, KAM.norm_realInclusion])

theorem real_N3 (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℝ}
    (hI : I ∈ d.V) (v : Fin b → ℝ) :
    ‖v‖ ≤ (pgAnalytic d).LB*‖(d.beta mu I).transpose.mulVec v‖ := by
  obtain ⟨hρ, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hLB, -⟩ :=
    pgAnalytic_spec d
  have hI1 := realInclusion_mem_actionNbhd hρ (subset_closure hI)
  have h := hLB mu hmu _ hI1 (KAM.realInclusion b v)
  rw [jetBeta_mulVec_real d hmu hI, KAM.norm_realInclusion, KAM.norm_realInclusion] at h
  rwa [(d.hsymm mu hmu I hI).eq]

end KAM.Planetary

end
