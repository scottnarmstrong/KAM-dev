/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Omega
public import KAM.Certificate.Sound.Energy

/-!
# The linearised energy error of the step (package C8c, isoenergetic)

`ε̃ = ⟨H∘K⟩ - E₀ + ⟨DH(K) ΔK⟩` (`KAM.Sharp2.Hybrid.linNewEnergy`). One merged model of
`H∘K - E₀ + DH(K) ΔK` is formed (the energy composition, the constant `-E₀`, and the first-derivative
composition times the exact models of `ΔK`); its zero mode plus its radius bounds `|ε̃|`, exactly as
the landed `energyOk` bounds `|⟨H∘K⟩ - E₀|`.

* `d1slot_encloses`: the composed first derivatives `∂_a H ∘ K`;
* `enModel`, `energyLinOk`, `linNewEnergy_le`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith Matrix

variable {n : ℕ} {α : Type} [CertArith α]

/-- The model of `H∘K - E₀ + DH(K) ΔK`: `mv` is the energy composition (slot `v₀`), `ms` the
first-derivative composition. -/
def enModel (c : TorusCertificate n α) (dK : CertEmbedding α) (mv : CertModel α)
    (ms : List (CertModel α)) : CertModel α :=
  CertModel.addMixed c.weight c.piEnc
    (CertModel.addMixed c.weight c.piEnc (CertModel.toDeg c.weight c.piEnc 0 mv)
      (constModel n (-c.params.E0) 0 0))
    (CertModel.toDeg c.weight c.piEnc 0
      (dotModel c.weight c.cfgFull c.piEnc (n + n) (fun a => ms.getD a zeroModel)
        (fun a => stepModel n dK a)))

/-- `|ε̃| ≤ ℓ_H` (zero mode and radius of `enModel`). -/
def energyLinOk (c : TorusCertificate n α) (dK : CertEmbedding α) (mv : CertModel α)
    (ms : List (CertModel α)) (lH : ℚ) : Bool :=
  let d := enModel c dK mv ms
  d.deg == 0 &&
    ble (upAdd (upAdd (zeroModeBall n d).c.normUp (zeroModeBall n d).r) d.rad) (ofRatDown lH)

variable [LawfulCertArith α]

/-- The composed first derivatives of `H` along `K`. -/
theorem d1slot_encloses {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hnv : c.ham.NonvanishingOn c.D)
    (hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D) {ms : List (CertModel α)}
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms) (y : Fin n ⊕ Fin n) :
    (ms.getD (phaseNat y) zeroModel).Encloses n c.weight.rho
      (fun θ => fderiv ℂ c.H (c.K θ) (phaseBasis y)) := by
  have S := checkStatic_sound hs
  have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
  obtain ⟨hlen, hm⟩ := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgFull S.hpe _ hc
  have hy := phaseNat_lt_add y
  have hq : phaseNat y < ms.length := by rw [hlen]; simpa [d1Slots] using hy
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
  refine (hm _ hq).of_eqOn fun θ hθ => ?_
  have : (d1Slots n c.ham.jet).getD (phaseNat y) 0 = c.ham.jet.d1.getD (phaseNat y) 0 := by
    simp [d1Slots, List.getD_eq_getElem?_getD, hy]
  rw [this, c.ham.jet_d1 hD hnv (hKD θ hθ) y]
  rfl

omit [CertArith α] [LawfulCertArith α] in
/-- `DH(z) v = ∑_a v_a ∂_a H(z)`. -/
theorem fderiv_eq_sum_phase (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (z v : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ H z v = ∑ a : Fin n ⊕ Fin n, sumVec n v a * fderiv ℂ H z (phaseBasis a) := by
  conv_lhs => rw [← sum_sumVec_smul_phaseBasis v]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- **`|ε̃| ≤ ℓ_H`.** -/
theorem linNewEnergy_le {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hnv : c.ham.NonvanishingOn c.D)
    (hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D) {mv : CertModel α}
    {ms : List (CertModel α)}
    (hv : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      [c.ham.jet.v0] = some [mv])
    (hc : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (d1Slots n c.ham.jet) = some ms) {dK : CertEmbedding α} {lH : ℚ}
    (h : energyLinOk c dK mv ms lH = true) :
    ‖KAM.Sharp2.Hybrid.linNewEnergy c.H c.K (stepFun n dK) c.params.E0‖ ≤ lH := by
  have S := checkStatic_sound hs
  have hρ : (0 : ℝ) < c.weight.rho := by
    rw [S.hrho]; exact S.hρinf.trans S.hρinfρ
  have hDo := isOpen_certDomain n c.weightH.rho c.centre c.radius
  have hHc := c.ham.contDiffOn_eval hDo hnv
  have hHd : DifferentiableOn ℂ c.H c.D := hHc.differentiableOn (by simp)
  have hKc : Continuous c.K := (c.emb.differentiable_eval n).continuous
  have hHK : ContinuousOn (fun θ => c.H (c.K θ)) (complexStrip n c.weight.rho) :=
    hHd.continuousOn.comp hKc.continuousOn hKD
  have hDH : ContinuousOn (fderiv ℂ c.H) c.D := hHc.continuousOn_fderiv_of_isOpen hDo (by simp)
  have hDHK : ContinuousOn (fun θ => fderiv ℂ c.H (c.K θ) (stepFun n dK θ))
      (complexStrip n c.weight.rho) :=
    (hDH.comp hKc.continuousOn hKD).clm_apply
      (differentiable_stepFun dK).continuous.continuousOn
  -- the models
  obtain ⟨-, hm⟩ := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgFull S.hpe _ hv
  have hm0 : mv.Encloses n c.weight.rho (fun θ => c.H (c.K θ)) :=
    (hm 0 (by simp)).of_eq_fun fun θ => by
      simp only [List.getD_cons_zero]
      exact c.ham.jet_v0 _
  have hP := dotModel_encloses S.hW c.cfgFull S.hpe (n + n)
    (a := fun a => ms.getD a zeroModel) (b := fun a => stepModel n dK a)
    (fa := fun a θ => fderiv ℂ c.H (c.K θ) (phaseBasis (finSumFinEquiv.symm a)))
    (fb := fun a θ => sumVec n (stepFun n dK θ) (finSumFinEquiv.symm a))
    (fun a => by
      have := d1slot_encloses hs hnv hKD hc (finSumFinEquiv.symm a)
      rwa [phaseNat_finSumFinEquiv_symm] at this)
    (fun a => by
      have := stepModel_encloses dK c.weight.rho (finSumFinEquiv.symm a)
      rwa [phaseNat_finSumFinEquiv_symm] at this)
  have hP' : (dotModel c.weight c.cfgFull c.piEnc (n + n) (fun a => ms.getD a zeroModel)
      (fun a => stepModel n dK a)).Encloses n c.weight.rho
      (fun θ => fderiv ℂ c.H (c.K θ) (stepFun n dK θ)) := hP.of_eq_fun fun θ => by
    rw [fderiv_eq_sum_phase, ← Equiv.sum_comp finSumFinEquiv.symm]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  set d := enModel c dK mv ms with hd
  have hdE : d.Encloses n c.weight.rho
      (fun θ => c.H (c.K θ) + slpConstVal (-c.params.E0) 0 0 +
        fderiv ℂ c.H (c.K θ) (stepFun n dK θ)) :=
    ((hm0.toDeg S.hW S.hpe 0).addMixed S.hW S.hpe
      (constModel_encloses n _ _ _ _)).addMixed S.hW S.hpe (hP'.toDeg S.hW S.hpe 0)
  simp only [energyLinOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hdeg, hb⟩ := h
  rw [← hd] at hdeg hb
  have hb' := (LawfulCertArith.ble_sound _ _ hb).trans (LawfulCertArith.ofRatDown_le _)
  have hu1 := LawfulCertArith.upAdd_ge (upAdd (zeroModeBall n d).c.normUp (zeroModeBall n d).r)
    d.rad
  have hu2 := LawfulCertArith.upAdd_ge (zeroModeBall n d).c.normUp (zeroModeBall n d).r
  have hnu := CC.norm_le_normUp (zeroModeBall n d).c
  have havg := hdE.average hρ ((hHK.add continuousOn_const).add hDHK)
  rw [hdeg, zpow_zero, zpow_zero, one_mul, one_mul] at havg
  have hemb : Continuous fun x : Fin n → ℝ => fun i => (x i : ℂ) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have hcK : Continuous fun x : Fin n → ℝ => c.H (c.K fun i => (x i : ℂ)) :=
    hHK.comp_continuous hemb fun x => ofReal_mem_complexStrip hρ x
  have hcD : Continuous fun x : Fin n → ℝ =>
      fderiv ℂ c.H (c.K fun i => (x i : ℂ)) (stepFun n dK fun i => (x i : ℂ)) :=
    hDHK.comp_continuous hemb fun x => ofReal_mem_complexStrip hρ x
  have hA : torusAverage (fun x : Fin n → ℝ =>
      c.H (c.K fun i => (x i : ℂ)) + slpConstVal (-c.params.E0) 0 0 +
        fderiv ℂ c.H (c.K fun i => (x i : ℂ)) (stepFun n dK fun i => (x i : ℂ))) =
      KAM.Sharp2.Hybrid.linNewEnergy c.H c.K (stepFun n dK) c.params.E0 := by
    have i1 : MeasureTheory.IntegrableOn (fun x : Fin n → ℝ =>
        c.H (c.K fun i => (x i : ℂ)) + slpConstVal (-c.params.E0) 0 0)
        (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
      integrableOn_unitCube_of_continuous (hcK.add continuous_const)
    have i2 : MeasureTheory.IntegrableOn (fun x : Fin n → ℝ =>
        fderiv ℂ c.H (c.K fun i => (x i : ℂ)) (stepFun n dK fun i => (x i : ℂ)))
        (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) :=
      integrableOn_unitCube_of_continuous hcD
    rw [torusAverage, MeasureTheory.integral_add i1 i2,
      MeasureTheory.integral_add (integrableOn_unitCube_of_continuous hcK)
        (integrableOn_unitCube_of_continuous continuous_const), MeasureTheory.integral_const]
    rw [MeasureTheory.measureReal_restrict_apply_univ, MeasureTheory.measureReal_def,
      volume_unitCube, ENNReal.toReal_one, one_smul]
    simp only [slpConstVal, zpow_zero, mul_one]
    push_cast
    simp [KAM.Sharp2.Hybrid.linNewEnergy, KAM.Iso.energyAverage, sub_eq_add_neg]
  rw [hA] at havg
  have hz := CertPoly.mem_coeffSumBall n
    (⟨d.poly.terms.filter fun t => isZeroKeyN n t.1⟩ : CertPoly α)
  rw [← CertPoly.coeff_zero_eq] at hz
  unfold CertBall.Mem at hz
  have hzc : ‖d.poly.coeff n 0‖ ≤ val (zeroModeBall n d).c.normUp + val (zeroModeBall n d).r := by
    have := norm_le_norm_add_norm_sub' (d.poly.coeff n 0) (zeroModeBall n d).c.toC
    unfold zeroModeBall at hnu this ⊢
    linarith
  calc _ ≤ ‖KAM.Sharp2.Hybrid.linNewEnergy c.H c.K (stepFun n dK) c.params.E0 -
        d.poly.coeff n 0‖ + ‖d.poly.coeff n 0‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith

end KAM.CertificateSharp.Hybrid

end
