/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Static
public import KAM.Matrix.Norms
public import KAM.Strip.FourierSeries

/-!
# Soundness of the embedding sub-check

`checkEmbedding_sound`: on `T_ρ`, `ball (K θ) μ ⊆ D` and `‖DK‖ ≤ σK - μ`.

* Angles: `|Im U_i(θ)| ≤ ρ_H - ρ - μ` either from `sup |U_i|` (`angleModel`,
  `realCompModel_encloses`, `CertModel.norm_le_supBound`) or by the mean value inequality from the
  real point `Re θ`, where `Im U_i = 0` (`realComp_real`), with `‖DU_i‖ ≤ Σ_j sup |∂_j U_i|`
  (`compDerivModel_encloses`, `norm_clm_le_sum_single`).
* Actions: `|A_i(θ) - c_i| ≤ r_i - μ` from `actionShiftModel` (`Encloses.addMixed`,
  `constModel_encloses`).
* `‖DK‖ = ‖tangentMat‖` (`norm_colMat`) is the maximal row sum (`KAM.norm_le_iff_forall_rowSum`),
  each row bounded by `dkRowUp` (`dkModels_encloses`, `sumUp_ge`).
-/

public section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α]

theorem sum_finRange_map_eq {β : Type*} [AddCommMonoid β] (f : Fin n → β) :
    ((List.finRange n).map f).sum = ∑ j, f j := by
  rw [Fin.sum_univ_def]

variable [LawfulCertArith α]

/-- `|Im U_i(θ)| ≤ room` on `T_ρ` from `angleImOk`. -/
theorem angleImOk_sound {K : CertEmbedding α} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true)
    {room : ℚ} {i : ℕ} (h : angleImOk n K W pe W.rho room i = true) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n W.rho) : |(K.angleAt n i θ).im| ≤ room := by
  have hρ := CertWeight.rho_pos hW
  have hroom := LawfulCertArith.ofRatDown_le (α := α) room
  unfold angleImOk at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · have h1 := LawfulCertArith.ble_sound _ _ h
    have h2 := CertModel.norm_le_supBound hW (realCompModel_encloses (α := α) n W.rho
      (K.angleDeg.getD i 0) K.angle[i]?) hθ
    exact (Complex.abs_im_le_norm _).trans (h2.trans (h1.trans hroom))
  · have h1 := LawfulCertArith.ble_sound _ _ h
    set S := sumUp (fun j : Fin n =>
      (compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j.val).supBound W)
      (List.finRange n)
    have hj (j : Fin n) {y : Fin n → ℂ} (hy : y ∈ complexStrip n W.rho) :
        ‖fderiv ℂ (K.angleAt n i) y (Pi.single j 1)‖ ≤
          val ((compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j.val).supBound W) :=
      CertModel.norm_le_supBound hW (compDerivModel_encloses hW hpe _ _ j) hy
    have hS : ∑ j : Fin n,
        val ((compDerivModel n W pe (K.angleDeg.getD i 0) K.angle[i]? j.val).supBound W) ≤
          val S := by
      rw [← sum_finRange_map_eq]; exact sumUp_ge _ _
    have hS0 : 0 ≤ val S := le_trans (Finset.sum_nonneg fun j _ =>
      (norm_nonneg _).trans (hj j (y := 0) fun k => by simpa using hρ)) hS
    have hbd : ∀ y ∈ complexStrip n W.rho, ‖fderiv ℂ (K.angleAt n i) y‖ ≤ val S := fun y hy =>
      (norm_clm_le_sum_single _).trans ((Finset.sum_le_sum fun j _ => hj j hy).trans hS)
    set x : Fin n → ℂ := fun k => ((θ k).re : ℂ)
    have hx : x ∈ complexStrip n W.rho := fun k => by simpa [x] using hρ
    have hmv := (convex_complexStrip n W.rho).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (differentiable_angleAt n K i).differentiableAt) hbd hx hθ
    have hxθ : ‖θ - x‖ ≤ W.rho := by
      refine (pi_norm_le_iff_of_nonneg hρ.le).2 fun k => ?_
      have : θ k - x k = ((θ k).im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [x]
      rw [Pi.sub_apply, this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      exact (hθ k).le
    have hre : (K.angleAt n i x).im = 0 := realComp_real n _ _ fun k => (θ k).re
    have hup := LawfulCertArith.upMul_ge (ofRatUp W.rho : α) S
      (hρ.le.trans (LawfulCertArith.ofRatUp_ge _)) hS0
    have hρup := LawfulCertArith.ofRatUp_ge (α := α) W.rho
    calc |(K.angleAt n i θ).im| = |(K.angleAt n i θ - K.angleAt n i x).im| := by
          rw [Complex.sub_im, hre, sub_zero]
      _ ≤ ‖K.angleAt n i θ - K.angleAt n i x‖ := Complex.abs_im_le_norm _
      _ ≤ val S * ‖θ - x‖ := hmv
      _ ≤ val S * W.rho := mul_le_mul_of_nonneg_left hxθ hS0
      _ ≤ val (ofRatUp W.rho : α) * val S := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_right hρup hS0
      _ ≤ room := hup.trans (h1.trans hroom)

theorem checkEmbedding_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkEmbedding c = true) :
    (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ := by
  have hS := checkStatic_sound hs
  have hW := hS.hW
  have hpe := hS.hpe
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ; rw [hS.hrho]; exact hθ
  unfold checkEmbedding at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hang, hact⟩, hdk⟩ := h
  rw [← hS.hrho] at hang
  have hr : (c.weight.rho : ℝ) = c.params.rho := by rw [hS.hrho]
  refine ⟨fun θ hθ w hw => ?_, fun θ hθ => ?_⟩
  · have hθ' := hstrip θ hθ
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw1 : ‖w.1 - (c.K θ).1‖ < c.params.μ := (norm_fst_le _).trans_lt hw
    have hw2 : ‖w.2 - (c.K θ).2‖ < c.params.μ := (norm_snd_le _).trans_lt hw
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hU := angleImOk_sound hW hpe (hang i i.isLt) hθ'
      have hd : |(w.1 i - (c.K θ).1 i).im| < c.params.μ :=
        (Complex.abs_im_le_norm _).trans_lt ((norm_le_pi_norm _ i).trans_lt hw1)
      have he : w.1 i = θ i + c.emb.angleAt n i.val θ + (w.1 i - (c.K θ).1 i) := by
        rw [TorusCertificate.K, CertEmbedding.eval_fst]; ring
      rw [he, Complex.add_im, Complex.add_im]
      have := hθ i
      push_cast at hU
      calc |(θ i).im + (c.emb.angleAt n i.val θ).im + (w.1 i - (c.K θ).1 i).im|
          ≤ |(θ i).im| + |(c.emb.angleAt n i.val θ).im| + |(w.1 i - (c.K θ).1 i).im| :=
            abs_add_three _ _ _
        _ < c.weightH.rho := by linarith
    · have hA := CertModel.norm_le_supBound hW
        ((realCompModel_encloses (α := α) n c.weight.rho (c.emb.actionDeg.getD i 0)
          c.emb.action[i.val]?).addMixed hW hpe (constModel_encloses n c.weight.rho
            (-(c.centre.getD i 0)) 0 0)) hθ'
      have h1 := LawfulCertArith.ble_sound _ _ (hact i i.isLt)
      have h2 := LawfulCertArith.ofRatDown_le (α := α) (c.radius.getD i 0 - c.params.μ)
      have hA' : ‖c.emb.actionAt n i.val θ - ((c.centre.getD i 0 : ℚ) : ℂ)‖ ≤
          ((c.radius.getD i 0 - c.params.μ : ℚ) : ℝ) := by
        refine le_trans (le_of_eq ?_) (hA.trans (h1.trans h2))
        simp [slpConstVal, CertEmbedding.actionAt, sub_eq_add_neg]
      have hd : ‖w.2 i - (c.K θ).2 i‖ < c.params.μ := (norm_le_pi_norm _ i).trans_lt hw2
      have he : w.2 i - ((c.centre.getD i 0 : ℚ) : ℂ) = (w.2 i - (c.K θ).2 i) +
          (c.emb.actionAt n i.val θ - ((c.centre.getD i 0 : ℚ) : ℂ)) := by
        rw [TorusCertificate.K, CertEmbedding.eval_snd]; ring
      rw [he]
      push_cast at hA'
      exact (norm_add_le _ _).trans_lt (by linarith)
  · have hθ' := hstrip θ hθ
    have henc := dkModels_encloses (n := n) hW hpe c.emb
    have hrow (r : Fin n ⊕ Fin n) : ∑ j, ‖tangentMat c.K θ r j‖ ≤
        (c.params.σK : ℝ) - c.params.μ := by
      have hsum : ∑ j : Fin n, ‖tangentMat c.K θ r j‖ ≤
          val (dkRowUp n c.emb c.weight c.piEnc (phaseNat r)) := by
        refine le_trans (Finset.sum_le_sum fun j _ =>
          CertModel.norm_le_supBound hW (henc r j) hθ') ?_
        rw [dkRowUp, ← sum_finRange_map_eq]; exact sumUp_ge _ _
      have h1 := LawfulCertArith.ble_sound _ _ (hdk _ (phaseNat_lt_add r))
      have h2 := LawfulCertArith.ofRatDown_le (α := α) (c.params.σK - c.params.μ)
      push_cast at h2
      exact hsum.trans (h1.trans h2)
    have hB : (0 : ℝ) ≤ (c.params.σK : ℝ) - c.params.μ :=
      (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hrow (.inl ⟨0, by
        have := hS.hn; omega⟩))
    rw [← norm_colMat]
    exact (KAM.norm_le_iff_forall_rowSum hB).2 hrow

end KAM.Certificate
