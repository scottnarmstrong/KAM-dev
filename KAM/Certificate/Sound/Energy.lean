/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Ham
public import KAM.Certificate.Sound.Embedding

/-!
# Soundness of the energy sub-check

`checkEnergy_sound_of`: the singleton composition encloses `H ∘ K` (`Slp.compose_sound`,
`HamExpr.jet_v0`); shifted by `-E₀` at degree `0`, its zero mode ball plus radius bounds the real
torus average (`CertModel.Encloses.average`, continuity of `H ∘ K` on the strip from the
nonvanishing denominators and the `μ`-ball of the embedding). Its two extra hypotheses are
verbatim the conclusions of `checkHamBounds_sound` and `checkEmbedding_sound`.
-/

public section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- `checkEnergy_sound` with the conclusions of the Hamiltonian-bounds and embedding contracts as
hypotheses. -/
theorem checkEnergy_sound_of {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    (h : checkEnergy c = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hρ : (0 : ℝ) < c.weight.rho := by
    rw [S.hrho]; exact S.hρinf.trans S.hρinfρ
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.K θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  -- continuity of `H ∘ K` on the strip
  have hHd : DifferentiableOn ℂ c.H c.D :=
    (c.ham.contDiffOn_eval (isOpen_certDomain _ _ _ _) hH.1).differentiableOn (by simp)
  have hHK : ContinuousOn (fun θ => c.H (c.K θ)) (complexStrip n c.weight.rho) :=
    hHd.continuousOn.comp (c.emb.differentiable_eval n).continuous.continuousOn hKD
  unfold checkEnergy at h
  split at h
  · rename_i m hc
    obtain ⟨-, hm⟩ := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgFull S.hpe _ hc
    have hm0 : m.Encloses n c.weight.rho (fun θ => c.H (c.K θ)) :=
      (hm 0 (by simp)).of_eq_fun fun θ => by
        simp only [List.getD_cons_zero]
        exact c.ham.jet_v0 _
    set d := CertModel.addMixed c.weight c.piEnc (CertModel.toDeg c.weight c.piEnc 0 m)
      (constModel n (-c.params.E0) 0 0) with hd
    have hdE : d.Encloses n c.weight.rho
        (fun θ => c.H (c.K θ) + slpConstVal (-c.params.E0) 0 0) :=
      (hm0.toDeg S.hW S.hpe 0).addMixed S.hW S.hpe (constModel_encloses n _ _ _ _)
    simp only [energyOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hdeg, hb⟩ := h
    rw [← hd] at hdeg hb
    have hb' := (LawfulCertArith.ble_sound _ _ hb).trans (LawfulCertArith.ofRatDown_le _)
    have hu1 := LawfulCertArith.upAdd_ge (upAdd (zeroModeBall n d).c.normUp (zeroModeBall n d).r)
      d.rad
    have hu2 := LawfulCertArith.upAdd_ge (zeroModeBall n d).c.normUp (zeroModeBall n d).r
    have hnu := CC.norm_le_normUp (zeroModeBall n d).c
    have havg := hdE.average hρ (hHK.add continuousOn_const)
    rw [hdeg, zpow_zero, zpow_zero, one_mul, one_mul] at havg
    have hz := CertPoly.mem_coeffSumBall n
      (⟨d.poly.terms.filter fun t => isZeroKeyN n t.1⟩ : CertPoly α)
    rw [← CertPoly.coeff_zero_eq] at hz
    unfold CertBall.Mem at hz
    -- the average of `H ∘ K - E₀`
    have hcK : Continuous fun x : Fin n → ℝ => c.H (c.K fun i => (x i : ℂ)) :=
      hHK.comp_continuous (continuous_pi fun i => Complex.continuous_ofReal.comp
        (continuous_apply i)) fun x => ofReal_mem_complexStrip hρ x
    have hA : torusAverage (fun x : Fin n → ℝ =>
        c.H (c.K fun i => (x i : ℂ)) + slpConstVal (-c.params.E0) 0 0) =
        KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ) := by
      rw [torusAverage, MeasureTheory.integral_add (integrableOn_unitCube_of_continuous hcK)
        (integrableOn_unitCube_of_continuous continuous_const), MeasureTheory.integral_const]
      rw [MeasureTheory.measureReal_restrict_apply_univ, MeasureTheory.measureReal_def,
        volume_unitCube, ENNReal.toReal_one, one_smul]
      simp only [slpConstVal, zpow_zero, mul_one]
      push_cast
      simp [KAM.Iso.energyAverage, sub_eq_add_neg]
    rw [hA] at havg
    have hzc : ‖d.poly.coeff n 0‖ ≤ val (zeroModeBall n d).c.normUp + val (zeroModeBall n d).r := by
      have := norm_le_norm_add_norm_sub' (d.poly.coeff n 0) (zeroModeBall n d).c.toC
      unfold zeroModeBall at hnu this ⊢
      linarith
    calc _ ≤ ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ) - d.poly.coeff n 0‖ +
          ‖d.poly.coeff n 0‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by linarith
  · exact absurd h (by simp)

theorem checkEnergy_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (h : checkEnergy c = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err :=
  checkEnergy_sound_of hs (checkHamBounds_sound hs hh) (checkEmbedding_sound hs he) h

end KAM.Certificate
