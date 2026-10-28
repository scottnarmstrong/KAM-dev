/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FrequencyJets

/-!
# P Part 5: Lipschitz bounds for the averaged frequency map (`stepP:p5:fd-lip`)

For the fast gradient `G(I, ξ) = ∂_I (jetPolynomial (I, ξ))` and the slow frequency
`Θ(I, ξ) = jetOmega I + jetBeta I ξ` (`‖ξ‖ ≤ 1`): Lipschitz bounds in `I` (from `lip_complex` on the
radius `2 ρ₀`, `ρ₀ = δ/32`, using the radius-2 bounds) and, for `G`, in `ξ` (mean value inequality
with the second derivative bound). The constant `lipConst d` is explicit and depends on the data
only. Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FD.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped BigOperators

namespace KAM.Planetary

variable {a b : ℕ}

/-- The embedding `I ↦ (I, 0)` of the fast actions. -/
def embFast (a b : ℕ) : (Fin a → ℂ) →L[ℂ] (Fin (a + b) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun I => Fin.append I (0 : Fin b → ℂ)
      map_add' := fun I I' => by
        funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
      map_smul' := fun c I => by
        funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp }

/-- The embedding `ξ ↦ (0, ξ)` of the slow actions. -/
def embSlow (a b : ℕ) : (Fin b → ℂ) →L[ℂ] (Fin (a + b) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => Fin.append (0 : Fin a → ℂ) ξ
      map_add' := fun ξ ξ' => by
        funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
      map_smul' := fun c ξ => by
        funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp }

theorem embFast_apply (I : Fin a → ℂ) : embFast a b I = Fin.append I (0 : Fin b → ℂ) := rfl

theorem embSlow_apply (ξ : Fin b → ℂ) : embSlow a b ξ = Fin.append (0 : Fin a → ℂ) ξ := rfl

theorem append_eq_add (I : Fin a → ℂ) (ξ : Fin b → ℂ) :
    Fin.append I ξ = embFast a b I + embSlow a b ξ := by
  funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
    simp [embFast_apply, embSlow_apply]

theorem norm_embFast_le (I : Fin a → ℂ) : ‖embFast a b I‖ ≤ ‖I‖ := by
  rw [embFast_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simpa using norm_le_pi_norm I i
  · simp

theorem norm_embSlow_le (ξ : Fin b → ℂ) : ‖embSlow a b ξ‖ ≤ ‖ξ‖ := by
  rw [embSlow_apply]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp
  · simpa using norm_le_pi_norm ξ j

theorem blockFast_append (I : Fin a → ℂ) (ξ : Fin b → ℂ) :
    blockFast (Fin.append I ξ : Fin (a + b) → ℂ) = I :=
  funext fun i => Fin.append_left _ _ i

theorem blockSlow_append (I : Fin a → ℂ) (ξ : Fin b → ℂ) :
    blockSlow (Fin.append I ξ : Fin (a + b) → ℂ) = ξ :=
  funext fun i => Fin.append_right _ _ i

theorem norm_single_le_one_fin {n : ℕ} (j : Fin n) : ‖(Pi.single j (1 : ℂ) : Fin n → ℂ)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem norm_embFast_single_le (i : Fin a) : ‖embFast a b (Pi.single i 1)‖ ≤ 1 :=
  (norm_embFast_le _).trans (norm_single_le_one_fin i)

/-- The fast gradient `G(I, ξ)` of the jet polynomial at frozen slow action `ξ`. -/
def jpGrad (d : PGData a b) (mu : ℝ) (ξ : Fin b → ℂ) (I : Fin a → ℂ) : Fin a → ℂ :=
  fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I ξ)) I (Pi.single i 1)

/-- The slow frequency `Θ(I, ξ) = Ω(I) + β(I) ξ`. -/
def jpTheta (d : PGData a b) (mu : ℝ) (ξ : Fin b → ℂ) (I : Fin a → ℂ) : Fin b → ℂ :=
  jetOmega d mu I + (jetBeta d mu I).mulVec ξ

theorem differentiableOn_fderiv_jp (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) :
    DifferentiableOn ℂ (fderiv ℂ (jetPolynomial d mu)) (jpDom d) := by
  have h : AnalyticOnNhd ℂ (jetPolynomial d mu) (jpDom d) :=
    KAM.analyticOnNhd_of_differentiableOn (isOpen_jpDom d) (jetPolynomial_differentiableOn d hmu)
  have h' : AnalyticOnNhd ℂ (fderiv ℂ (jetPolynomial d mu)) (jpDom d) := h.fderiv
  exact h'.differentiableOn

theorem append_mem_jpDom (d : PGData a b) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (ξ : Fin b → ℂ) :
    (Fin.append I ξ : Fin (a + b) → ℂ) ∈ jpDom d := by
  show blockFast (Fin.append I ξ : Fin (a + b) → ℂ) ∈
    KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)
  rw [blockFast_append]; exact hI

theorem hasFDerivAt_append (ξ : Fin b → ℂ) (I : Fin a → ℂ) :
    HasFDerivAt (fun I : Fin a → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) (embFast a b) I := by
  have : (fun I : Fin a → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) =
      fun I => embFast a b I + embSlow a b ξ := funext fun I => append_eq_add I ξ
  rw [this]
  exact (embFast a b).hasFDerivAt.add_const _

theorem jpGrad_eq (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (ξ : Fin b → ℂ)
    {I : Fin a → ℂ} (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2))
    (i : Fin a) :
    jpGrad d mu ξ I i =
      fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ) (embFast a b (Pi.single i 1)) := by
  have hJ := append_mem_jpDom d hI ξ
  have hd : DifferentiableAt ℂ (jetPolynomial d mu) (Fin.append I ξ) :=
    (jetPolynomial_differentiableOn d hmu).differentiableAt ((isOpen_jpDom d).mem_nhds hJ)
  have h := hd.hasFDerivAt.comp I (hasFDerivAt_append ξ I)
  unfold jpGrad
  rw [show (fun I => jetPolynomial d mu (Fin.append I ξ)) =
    jetPolynomial d mu ∘ (fun I : Fin a → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) from rfl,
    h.fderiv]
  rfl

theorem norm_jpGrad_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {ξ : Fin b → ℂ}
    (hξ : ‖ξ‖ ≤ 1) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16)) :
    ‖jpGrad d mu ξ I‖ ≤ jpBound d := by
  have hI2 := mem_actionNbhd_mono (by linarith [(pgExtension d).delta_pos] :
    (pgExtension d).delta / 16 ≤ (pgExtension d).delta / 2) hI
  have hJf : blockFast (Fin.append I ξ : Fin (a + b) → ℂ) ∈
      KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16) := by
    rw [blockFast_append]; exact hI
  have hJs : ‖blockSlow (Fin.append I ξ : Fin (a + b) → ℂ)‖ < 2 := by
    rw [blockSlow_append]; linarith
  have h := (jetPolynomial_derivs_bound d hmu hJf hJs).2.1
  have hB := jpBound_ge_one d
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
  rw [jpGrad_eq d hmu ξ hI2 i]
  calc _ ≤ ‖fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ)‖ * ‖embFast a b (Pi.single i 1)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ jpBound d * 1 := by
        gcongr
        exact norm_embFast_single_le i
    _ = jpBound d := mul_one _

theorem differentiableOn_jpGrad (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    (ξ : Fin b → ℂ) :
    DifferentiableOn ℂ (jpGrad d mu ξ)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := by
  have hmaps : MapsTo (fun I : Fin a → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ))
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) (jpDom d) :=
    fun _ hI => append_mem_jpDom d hI ξ
  have haff : Differentiable ℂ (fun I : Fin a → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) :=
    fun I => (hasFDerivAt_append ξ I).differentiableAt
  refine differentiableOn_pi.2 fun i => ?_
  have hi := ((differentiableOn_fderiv_jp d hmu).comp haff.differentiableOn hmaps).clm_apply
    (differentiableOn_const (embFast a b (Pi.single i 1)))
  refine hi.congr fun I hI => ?_
  exact jpGrad_eq d hmu ξ hI i

theorem differentiableOn_jpTheta (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    (ξ : Fin b → ℂ) :
    DifferentiableOn ℂ (jpTheta d mu ξ)
      (KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) := by
  refine differentiableOn_pi.2 fun j => ?_
  unfold jpTheta
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  refine (jetOmega_differentiableOn d hmu j).add (DifferentiableOn.fun_sum fun k _ => ?_)
  exact (jetBeta_differentiableOn d hmu j k).mul (differentiableOn_const _)

theorem norm_jpTheta_le (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {ξ : Fin b → ℂ}
    (hξ : ‖ξ‖ ≤ 1) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2)) :
    ‖jpTheta d mu ξ I‖ ≤ jetK2 d + b * jetK4 d := by
  have h2 := jetK2_nonneg d
  have h4 := jetK4_nonneg d
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  unfold jpTheta
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  refine (norm_add_le _ _).trans (add_le_add (jetOmega_norm_le d hmu hI j) ?_)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖jetBeta d mu I j k * ξ k‖ ≤ ∑ _k : Fin b, jetK4 d := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) ((norm_le_pi_norm ξ k).trans hξ)).trans
          (jetBeta_norm_le d hmu hI j k)
    _ = b * jetK4 d := by simp

/-- Radius of the Lipschitz estimates. -/
def lipRadius (d : PGData a b) : ℝ := (pgExtension d).delta / 32

theorem lipRadius_pos (d : PGData a b) : 0 < lipRadius d := by
  have := (pgExtension d).delta_pos
  unfold lipRadius; positivity

/-- Lipschitz constant: it depends on the data only. -/
def lipConst (d : PGData a b) : ℝ :=
  jpBound d + 2 * a * jpBound d / lipRadius d + 2 * a * (jetK2 d + b * jetK4 d) / lipRadius d

theorem lipConst_ge_one (d : PGData a b) : 1 ≤ lipConst d := by
  have h1 := jpBound_ge_one d
  have h2 := lipRadius_pos d
  have h3 := jetK2_nonneg d
  have h4 := jetK4_nonneg d
  unfold lipConst
  have : 0 ≤ 2 * (a : ℝ) * jpBound d / lipRadius d := by positivity
  have : 0 ≤ 2 * (a : ℝ) * (jetK2 d + b * jetK4 d) / lipRadius d := by positivity
  linarith

theorem actionNbhd_two_lipRadius (d : PGData a b) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) (2 * lipRadius d)) :
    I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16) :=
  mem_actionNbhd_mono (by unfold lipRadius; linarith) hI

/-- Lipschitz estimate of `G` in the fast action. -/
theorem jpGrad_lip (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {ξ : Fin b → ℂ}
    (hξ : ‖ξ‖ ≤ 1) {I I' : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) (lipRadius d))
    (hI' : I' ∈ KAM.actionNbhd (closure d.V) (lipRadius d)) :
    ‖jpGrad d mu ξ I - jpGrad d mu ξ I'‖ ≤ lipConst d * ‖I - I'‖ := by
  have hρ := lipRadius_pos d
  have key := lip_complex d.ha hρ (A := jpBound d) (f := jpGrad d mu ξ)
    ((differentiableOn_jpGrad d hmu ξ).mono (fun I hI => mem_actionNbhd_mono
      (by unfold lipRadius; linarith [(pgExtension d).delta_pos]) hI))
    (fun I hI => norm_jpGrad_le d hmu hξ (actionNbhd_two_lipRadius d hI)) I hI I' hI'
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have h1 := jpBound_ge_one d
  have : 0 ≤ 2 * (a : ℝ) * (jetK2 d + b * jetK4 d) / lipRadius d := by
    have := jetK2_nonneg d; have := jetK4_nonneg d; positivity
  unfold lipConst
  linarith

/-- Lipschitz estimate of `Θ` in the fast action. -/
theorem jpTheta_lip (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {ξ : Fin b → ℂ}
    (hξ : ‖ξ‖ ≤ 1) {I I' : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) (lipRadius d))
    (hI' : I' ∈ KAM.actionNbhd (closure d.V) (lipRadius d)) :
    ‖jpTheta d mu ξ I - jpTheta d mu ξ I'‖ ≤ lipConst d * ‖I - I'‖ := by
  have hρ := lipRadius_pos d
  have hδ := (pgExtension d).delta_pos
  have hsub : ∀ {I : Fin a → ℂ}, I ∈ KAM.actionNbhd (closure d.V) (2 * lipRadius d) →
      I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 2) := fun hI =>
    mem_actionNbhd_mono (by unfold lipRadius; linarith) hI
  have key := lip_complex d.ha hρ (A := jetK2 d + b * jetK4 d) (f := jpTheta d mu ξ)
    ((differentiableOn_jpTheta d hmu ξ).mono fun I hI => hsub hI)
    (fun I hI => norm_jpTheta_le d hmu hξ (hsub hI)) I hI I' hI'
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have h1 := jpBound_ge_one d
  have : 0 ≤ 2 * (a : ℝ) * jpBound d / lipRadius d := by positivity
  unfold lipConst
  linarith

/-- Lipschitz estimate of `G` in the slow action (mean value inequality on `‖ξ‖ ≤ 1`). -/
theorem jpGrad_lip_slow (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) {I : Fin a → ℂ}
    (hI : I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16)) {ξ ξ' : Fin b → ℂ}
    (hξ : ‖ξ‖ ≤ 1) (hξ' : ‖ξ'‖ ≤ 1) :
    ‖jpGrad d mu ξ I - jpGrad d mu ξ' I‖ ≤ jpBound d * ‖ξ - ξ'‖ := by
  have hB := jpBound_ge_one d
  have hI2 := mem_actionNbhd_mono (by linarith [(pgExtension d).delta_pos] :
    (pgExtension d).delta / 16 ≤ (pgExtension d).delta / 2) hI
  have hjd : ∀ ξ : Fin b → ℂ, (Fin.append I ξ : Fin (a + b) → ℂ) ∈ jpDom d :=
    fun ξ => append_mem_jpDom d hI2 ξ
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hf : ∀ ξ : Fin b → ℂ, HasFDerivAt
      (fun ξ : Fin b → ℂ => fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ)
        (embFast a b (Pi.single i 1)))
      ((ContinuousLinearMap.apply ℂ ℂ (embFast a b (Pi.single i 1))).comp
        ((fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ)).comp (embSlow a b))) ξ := by
    intro ξ
    have hD : DifferentiableAt ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ) :=
      (differentiableOn_fderiv_jp d hmu).differentiableAt ((isOpen_jpDom d).mem_nhds (hjd ξ))
    have haff : HasFDerivAt (fun ξ : Fin b → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ))
        (embSlow a b) ξ := by
      have : (fun ξ : Fin b → ℂ => (Fin.append I ξ : Fin (a + b) → ℂ)) =
          fun ξ => embSlow a b ξ + embFast a b I := by
        funext ξ; exact (append_eq_add I ξ).trans (add_comm _ _)
      rw [this]; exact (embSlow a b).hasFDerivAt.add_const _
    have h1 := hD.hasFDerivAt.comp ξ haff
    exact (ContinuousLinearMap.apply ℂ ℂ (embFast a b (Pi.single i 1))).hasFDerivAt.comp ξ h1
  have hbd : ∀ ξ : Fin b → ℂ, ‖ξ‖ ≤ 1 → ‖(ContinuousLinearMap.apply ℂ ℂ
      (embFast a b (Pi.single i 1))).comp
        ((fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ)).comp (embSlow a b))‖ ≤
        jpBound d := by
    intro ξ hξ1
    have hJf : blockFast (Fin.append I ξ : Fin (a + b) → ℂ) ∈
        KAM.actionNbhd (closure d.V) ((pgExtension d).delta / 16) := by
      rw [blockFast_append]; exact hI
    have hJs : ‖blockSlow (Fin.append I ξ : Fin (a + b) → ℂ)‖ < 2 := by
      rw [blockSlow_append]; linarith
    have h2 := (jetPolynomial_derivs_bound d hmu hJf hJs).2.2
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) fun w => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    calc ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ) (embSlow a b w)
          (embFast a b (Pi.single i 1))‖
        ≤ ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ) (embSlow a b w)‖ *
          ‖embFast a b (Pi.single i 1)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ)‖ * ‖embSlow a b w‖) * 1 := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ _
          · exact norm_embFast_single_le i
      _ ≤ (jpBound d * ‖w‖) * 1 := by gcongr; exact (norm_embSlow_le w)
      _ = jpBound d * ‖w‖ := mul_one _
  have key := (convex_closedBall (0 : Fin b → ℂ) 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun ξ : Fin b → ℂ => fderiv ℂ (jetPolynomial d mu) (Fin.append I ξ)
        (embFast a b (Pi.single i 1)))
    (f' := fun ξ => (ContinuousLinearMap.apply ℂ ℂ (embFast a b (Pi.single i 1))).comp
        ((fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) (Fin.append I ξ)).comp (embSlow a b)))
    (fun ξ _ => (hf ξ).hasFDerivWithinAt)
    (fun ξ hξ1 => hbd ξ (by simpa using hξ1)) (x := ξ') (y := ξ)
    (by simpa using hξ') (by simpa using hξ)
  rw [Pi.sub_apply, jpGrad_eq d hmu ξ hI2 i, jpGrad_eq d hmu ξ' hI2 i]
  exact key

end KAM.Planetary

end
