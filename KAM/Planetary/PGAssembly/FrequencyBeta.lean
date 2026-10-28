/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyLip

/-!
# P Part 5: the complex torsion lower bound (`stepP:p5:fd-beta`)

On the real points of `closure V` the complex matrix `jetBeta d mu x` has determinant of modulus at
least `B > 0` (`jetBeta_det_closure`). By compactness of `[0, mu0] × closure V × S¹` the lower
bound `‖jetBeta d mu x v‖ ≥ m ‖v‖` holds uniformly (`jetBeta_lower`); the neighbourhood version
`jetBeta_lower_nbhd` perturbs it with the Lipschitz bound of `Θ`. (The adjugate/Cramer bound of the
source gives an explicit constant; compactness gives the same conclusion with a data-only
constant, which is all that `PGAnalyticSpec` records.)
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FD.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

theorem jetBeta_lower (d : PGData a b) : ∃ m : ℝ, 0 < m ∧
    ∀ mu ∈ Icc 0 d.mu0, ∀ x ∈ closure d.V, ∀ v : Fin b → ℂ,
      m * ‖v‖ ≤ ‖(jetBeta d mu (KAM.realInclusion a x)).mulVec v‖ := by
  set K : Set (ℝ × (Fin a → ℝ) × (Fin b → ℂ)) :=
    Icc 0 d.mu0 ×ˢ (closure d.V ×ˢ sphere (0 : Fin b → ℂ) 1) with hK
  have hKc : IsCompact K :=
    isCompact_Icc.prod (d.hVb.isCompact_closure.prod (isCompact_sphere 0 1))
  set F : ℝ × (Fin a → ℝ) × (Fin b → ℂ) → ℝ := fun z =>
    ‖(jetBeta d z.1 (KAM.realInclusion a z.2.1)).mulVec z.2.2‖ with hF
  have hentry : ∀ i j, ContinuousOn
      (fun z : ℝ × (Fin a → ℝ) × (Fin b → ℂ) => jetBeta d z.1 (KAM.realInclusion a z.2.1) i j) K := by
    intro i j
    have hc := (jet_continuousOn d).2.2 i j
    have hg : ContinuousOn (fun z : ℝ × (Fin a → ℝ) × (Fin b → ℂ) =>
        ((z.1, KAM.realInclusion a z.2.1) : ℝ × (Fin a → ℂ))) K :=
      (continuous_fst.prodMk ((KAM.realInclusion a).continuous.comp
        (continuous_fst.comp continuous_snd))).continuousOn
    exact hc.comp hg fun z hz => ⟨hz.1, realInclusion_mem_tube d hz.2.1⟩
  have hFc : ContinuousOn F K := by
    refine ContinuousOn.norm (continuousOn_pi.2 fun i => ?_)
    simp only [Matrix.mulVec, dotProduct]
    refine continuousOn_finset_sum _ fun j _ => (hentry i j).mul ?_
    exact (continuous_apply j |>.comp (continuous_snd.comp continuous_snd)).continuousOn
  have hpos : ∀ z ∈ K, 0 < F z := by
    intro z hz
    obtain ⟨hmu, hx, hv⟩ := hz
    have hdet : (jetBeta d z.1 (KAM.realInclusion a z.2.1)).det ≠ 0 := by
      intro h
      have := jetBeta_det_closure d hmu hx
      rw [h] at this
      simp at this
      linarith [d.hB]
    have hv0 : z.2.2 ≠ 0 := by
      intro h; rw [h] at hv; simp at hv
    refine norm_pos_iff.2 fun h => hv0 ?_
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h
  obtain ⟨m, hm, hlow⟩ := hKc.exists_forall_le' hFc hpos
  refine ⟨m, hm, fun mu hmu x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : Fin b → ℂ := ((‖v‖ : ℂ))⁻¹ • v with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hvpos.ne']
  have h1 := hlow (mu, x, w) ⟨hmu, hx, by simpa using hwn⟩
  have hvw : v = (‖v‖ : ℂ) • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hvpos.ne'), one_smul]
  have h2 : (jetBeta d mu (KAM.realInclusion a x)).mulVec v =
      (‖v‖ : ℂ) • (jetBeta d mu (KAM.realInclusion a x)).mulVec w := by
    conv_lhs => rw [hvw]
    exact Matrix.mulVec_smul _ _ _
  rw [h2, norm_smul, Complex.norm_real, norm_norm]
  calc m * ‖v‖ = ‖v‖ * m := mul_comm _ _
    _ ≤ ‖v‖ * ‖(jetBeta d mu (KAM.realInclusion a x)).mulVec w‖ := by gcongr; exact h1

/-- Homogeneous form of the Lipschitz bound of `Θ`: the matrix `jetBeta` is Lipschitz in `I`. -/
theorem jetBeta_lip_mulVec (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {I I' : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) (lipRadius d))
    (hI' : I' ∈ KAM.actionNbhd (closure d.V) (lipRadius d)) (v : Fin b → ℂ) :
    ‖(jetBeta d mu I).mulVec v - (jetBeta d mu I').mulVec v‖ ≤
      2 * lipConst d * ‖I - I'‖ * ‖v‖ := by
  have hL := lipConst_ge_one d
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : Fin b → ℂ := ((‖v‖ : ℂ))⁻¹ • v with hw
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hvpos.ne']
  have hvw : v = (‖v‖ : ℂ) • w := by
    rw [hw, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hvpos.ne'), one_smul]
  have e1 := jpTheta_lip d hmu hwn.le hI hI'
  have e0 := jpTheta_lip d hmu (ξ := 0) (by simp) hI hI'
  have hdiff : (jetBeta d mu I).mulVec w - (jetBeta d mu I').mulVec w =
      (jpTheta d mu w I - jpTheta d mu w I') - (jpTheta d mu 0 I - jpTheta d mu 0 I') := by
    unfold jpTheta
    simp only [Matrix.mulVec_zero, add_zero]
    abel
  have hw2 : ‖(jetBeta d mu I).mulVec w - (jetBeta d mu I').mulVec w‖ ≤
      2 * lipConst d * ‖I - I'‖ := by
    rw [hdiff]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have h3 : (jetBeta d mu I).mulVec v - (jetBeta d mu I').mulVec v =
      (‖v‖ : ℂ) • ((jetBeta d mu I).mulVec w - (jetBeta d mu I').mulVec w) := by
    rw [smul_sub, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hvw]
  rw [h3, norm_smul, Complex.norm_real, norm_norm]
  calc ‖v‖ * ‖(jetBeta d mu I).mulVec w - (jetBeta d mu I').mulVec w‖
      ≤ ‖v‖ * (2 * lipConst d * ‖I - I'‖) := by gcongr
    _ = 2 * lipConst d * ‖I - I'‖ * ‖v‖ := mul_comm _ _

/-- The data-only radius of the torsion inverse. -/
def betaRadius (d : PGData a b) (m : ℝ) : ℝ :=
  min (lipRadius d) (m / (4 * lipConst d))

theorem betaRadius_pos (d : PGData a b) {m : ℝ} (hm : 0 < m) : 0 < betaRadius d m := by
  have := lipConst_ge_one d
  have := lipRadius_pos d
  unfold betaRadius; positivity

/-- The inverse bound for `jetBeta` on the `betaRadius`-neighbourhood of `closure V`. -/
theorem jetBeta_lower_nbhd (d : PGData a b) {m : ℝ} (hm : 0 < m)
    (hlow : ∀ mu ∈ Icc 0 d.mu0, ∀ x ∈ closure d.V, ∀ v : Fin b → ℂ,
      m * ‖v‖ ≤ ‖(jetBeta d mu (KAM.realInclusion a x)).mulVec v‖) :
    ∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) (betaRadius d m), ∀ v : Fin b → ℂ,
      m / 2 * ‖v‖ ≤ ‖(jetBeta d mu I).mulVec v‖ := by
  intro mu hmu I hI v
  have hL := lipConst_ge_one d
  obtain ⟨x, hx, hxI⟩ := hI
  have hρ : betaRadius d m ≤ lipRadius d := min_le_left _ _
  have hρ2 : betaRadius d m ≤ m / (4 * lipConst d) := min_le_right _ _
  have hI0 : I ∈ KAM.actionNbhd (closure d.V) (lipRadius d) := ⟨x, hx, hxI.trans_le hρ⟩
  have hx0 : KAM.realInclusion a x ∈ KAM.actionNbhd (closure d.V) (lipRadius d) :=
    ⟨x, hx, by simpa using lipRadius_pos d⟩
  have h1 := jetBeta_lip_mulVec d hmu hI0 hx0 v
  have h2 := hlow mu hmu x hx v
  have hd : ‖I - KAM.realInclusion a x‖ ≤ m / (4 * lipConst d) := by
    have : ‖I - KAM.realInclusion a x‖ < betaRadius d m := by
      simpa [KAM.realInclusion] using hxI
    exact (this.le).trans hρ2
  have h3 : 2 * lipConst d * ‖I - KAM.realInclusion a x‖ ≤ m / 2 := by
    calc _ ≤ 2 * lipConst d * (m / (4 * lipConst d)) := by gcongr
      _ = m / 2 := by field_simp; ring
  have h4 : ‖(jetBeta d mu (KAM.realInclusion a x)).mulVec v‖ ≤
      ‖(jetBeta d mu I).mulVec v‖ + ‖(jetBeta d mu I).mulVec v -
        (jetBeta d mu (KAM.realInclusion a x)).mulVec v‖ := by
    calc _ = ‖(jetBeta d mu I).mulVec v -
          ((jetBeta d mu I).mulVec v - (jetBeta d mu (KAM.realInclusion a x)).mulVec v)‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h5 : ‖(jetBeta d mu I).mulVec v - (jetBeta d mu (KAM.realInclusion a x)).mulVec v‖ ≤
      m / 2 * ‖v‖ := h1.trans (by gcongr)
  linarith

end KAM.Planetary

end
