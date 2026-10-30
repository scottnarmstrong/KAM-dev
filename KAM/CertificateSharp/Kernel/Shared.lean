/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Engine
public import KAM.CertificateSharp.Kernel.Prune

/-!
# Invariance and energy from one pruned composition

`checkInvariance` and `checkEnergy` each run `Slp.compose` over the whole jet program, with
different wanted slots, and `checkGram` and `checkTorsion` each run `gramCheck`. This file replaces
those four sub-checks by two:

* `checkInvEnShared`: one `Slp.composePruned` with wanted slots `v0 :: d1Slots`, then the
  invariance sup bounds and `energyOk` on the shared models. Composition runs only the operations
  `v0` and the `∂_a H` depend on, once.
* `checkTorsion` alone: it begins with the same `gramCheck`, so a passing `checkTorsion` contains
  the Gram check (`checkGram_of_checkTorsion`).

`checkInvEnShared_sound` proves the contents of `checkInvariance_sound` and `checkEnergy_sound`
(the two `G1Hyps` fields `hE` and `hEn`) with the same hypotheses; `checkTorusCertificateShared`
slots into the engine interface and `checkTorusCertificateShared_sound` has the conclusion of
`checkTorusCertificateWith_sound`.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Torus KAM.Certificate CertArith

/-- The slots composed for invariance and energy: `H`, then the `2n` first derivatives. -/
def wantedInvEn (n : ℕ) (J : HamJet) : List ℕ := J.v0 :: d1Slots n J

/-- The invariance bound on the models `ms` (`d1Slots` order), as in `checkInvariance`. -/
def invarianceOk {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (ms : List (CertModel α)) : Bool :=
  (List.range (n + n)).all fun a =>
    ble ((invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms a).supBound
      c.weight) (ofRatDown c.params.err)

/-- Invariance and energy from one pruned composition. -/
def checkInvEnShared {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  match Slp.composePruned n c.ham.jet.prog c.emb c.wit c.weight c.cfgFull c.piEnc
      (wantedInvEn n c.ham.jet) with
  | some (m :: ms) => energyOk n c.weight c.piEnc m c.params.E0 c.params.err && invarianceOk c ms
  | _ => false

/-- The shared sub-checks in place of `checkInvariance`, `checkEnergy` and `checkGram`. -/
def checkTorusCertificateShared (E : AposterioriEngine) {n : ℕ} {α : Type} [CertArith α]
    (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbedding c && checkInvEnShared c && checkTorsion c &&
    E.test c

theorem checkGram_of_checkTorsion {n : ℕ} {α : Type} [CertArith α] {c : TorusCertificate n α}
    (h : checkTorsion c = true) : checkGram c = true := by
  unfold checkTorsion at h
  unfold checkGram
  split at h
  · rename_i δβ hG
    rw [hG]; rfl
  · exact absurd h (by simp)

section Sound

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- The invariance field from the composed derivative models (the proof of
`checkInvariance_sound_of`, with the composition as hypothesis). -/
theorem invarianceOk_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {ms : List (CertModel α)} (hlen : ms.length = (d1Slots n c.ham.jet).length)
    (hm : ∀ idx (hidx : idx < ms.length), ms[idx].Encloses n c.weight.rho
      (fun θ => c.ham.jet.prog.val n (c.emb.eval n θ) ((d1Slots n c.ham.jet).getD idx 0)))
    (h : invarianceOk c ms = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
  have hslot : ∀ y : Fin n ⊕ Fin n, (ms.getD (phaseNat y) zeroModel).Encloses n c.weight.rho
      (fun θ => fderiv ℂ c.H (c.K θ) (phaseBasis y)) := by
    intro y
    have hy := phaseNat_lt_add y
    have hq : phaseNat y < ms.length := by rw [hlen]; simpa [d1Slots] using hy
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    refine (hm _ hq).of_eqOn fun θ hθ => ?_
    have : (d1Slots n c.ham.jet).getD (phaseNat y) 0 = c.ham.jet.d1.getD (phaseNat y) 0 := by
      simp [d1Slots, List.getD_eq_getElem?_getD, hy]
    rw [this, c.ham.jet_d1 hD hH.1 (hKD θ hθ) y]
    rfl
  have hcoord : ∀ x : Fin n ⊕ Fin n,
      (invarianceModel n c.emb c.freqBox c.params.s c.weight c.cfgFull c.piEnc ms
        (phaseNat x)).Encloses n c.weight.rho
        (fun θ => sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x) := by
    intro x
    have hdk := (dkFreqModel_encloses S.hW c.cfgFull S.hpe c.emb hω c.params.s x).negM
    have hfun : ∀ θ, sumVec n (invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ) x =
        hamSign x * fderiv ℂ c.H (c.K θ) (phaseBasis x.swap) +
          -∑ l, ((((c.params.s : ℝ) • ωstar) l : ℝ) : ℂ) * tangentMat (c.emb.eval n) θ x l := by
      intro θ
      rw [invarianceError, map_sub, Pi.sub_apply, sumVec_hamiltonianVectorFieldℂ,
        sumVec_fderiv_apply, sub_eq_add_neg]
      rfl
    have hsw : swapNat n (phaseNat x) = phaseNat x.swap := swapNat_phaseNat x
    unfold invarianceModel
    rcases x with i | i
    · have hlt : phaseNat (Sum.inl i : Fin n ⊕ Fin n) < n := i.isLt
      simp only [hlt, ↓reduceIte, hsw]
      exact ((hslot _).addMixed S.hW S.hpe hdk).of_eq_fun fun θ => by
        rw [hfun]; simp [hamSign]
    · have hlt : ¬(phaseNat (Sum.inr i : Fin n ⊕ Fin n) < n) := by simp [phaseNat]
      simp only [hlt, ↓reduceIte, hsw]
      exact ((hslot _).negM.addMixed S.hW S.hpe hdk).of_eq_fun fun θ => by
        rw [hfun]; simp [hamSign]
  intro θ hθ
  rw [← S.hrho] at hθ
  rw [← norm_sumVec, pi_norm_le_iff_of_nonneg S.he0]
  intro x
  unfold invarianceOk at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hb := (LawfulCertArith.ble_sound _ _ (h _ (phaseNat_lt_add x))).trans
    (LawfulCertArith.ofRatDown_le _)
  exact (CertModel.norm_le_supBound S.hW (hcoord x) hθ).trans hb

/-- The energy field from the composed `H ∘ K` model (the proof of `checkEnergy_sound_of`, with
the composition as hypothesis). -/
theorem energyOk_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D))
    (hHd : DifferentiableOn ℂ c.H c.D) {m : CertModel α}
    (hm0 : m.Encloses n c.weight.rho (fun θ => c.H (c.K θ)))
    (h : energyOk n c.weight c.piEnc m c.params.E0 c.params.err = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hρ : (0 : ℝ) < c.weight.rho := by
    rw [S.hrho]; exact S.hρinf.trans S.hρinfρ
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.K θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE θ hθ (Metric.mem_ball_self S.hμ)
  have hHK : ContinuousOn (fun θ => c.H (c.K θ)) (complexStrip n c.weight.rho) :=
    hHd.continuousOn.comp (c.emb.differentiable_eval n).continuous.continuousOn hKD
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

/-- **Soundness of the shared check**: the invariance field and the energy field, with the
hypotheses of `checkInvariance_sound_of` and `checkEnergy_sound_of`. -/
theorem checkInvEnShared_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    (h : checkInvEnShared c = true) :
    (∀ {ωstar : Fin n → ℝ}, FreqEncloses n c.freqBox ωstar →
      ∀ θ ∈ complexStrip n c.params.rho,
        ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err) ∧
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  unfold checkInvEnShared at h
  split at h
  · rename_i ms0 m ms hc
    obtain ⟨hlen, hm⟩ :=
      Slp.composePruned_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgFull S.hpe _ hc
    simp only [Bool.and_eq_true] at h
    obtain ⟨hen, hinv⟩ := h
    have hD := isOpen_certDomain n c.weightH.rho c.centre c.radius
    have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
      intro θ hθ
      rw [S.hrho] at hθ
      exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
    refine ⟨fun hω => invarianceOk_sound hs hH hE (ms := ms) ?_ ?_ hinv hω, ?_⟩
    · simpa [wantedInvEn] using hlen
    · intro idx hidx
      have := hm (idx + 1) (by simp; omega)
      simp only [wantedInvEn, List.getD_cons_succ] at this
      exact this
    · have hHd : DifferentiableOn ℂ c.H c.D :=
        (c.ham.contDiffOn_eval hD hH.1).differentiableOn (by simp)
      refine energyOk_sound hs hE.1 hHd ?_ hen
      have := hm 0 (by simp)
      simp only [wantedInvEn, List.getD_cons_zero] at this
      exact CertModel.Encloses.of_eq_fun this fun θ => c.ham.jet_v0 _
  · exact absurd h (by simp)

/-- **Soundness of the shared certifier.** -/
theorem checkTorusCertificateShared_sound (E : AposterioriEngine) {c : TorusCertificate n α}
    (h : checkTorusCertificateShared E c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar := by
  simp only [checkTorusCertificateShared, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hie⟩, ht⟩, hsm⟩ := h
  have S := checkStatic_sound hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq hs hω
  have hH := checkHamBounds_sound hs hh
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  have hEm := checkEmbedding_sound hs he
  obtain ⟨hball, hDK⟩ := hEm
  have hg := checkGram_of_checkTorsion ht
  obtain ⟨hTu, hTb⟩ := checkTorsion_sound hs hh he hg ht hω
  obtain ⟨hinv, hen⟩ := checkInvEnShared_sound hs hH ⟨hball, hDK⟩ hie
  obtain ⟨C₁, C₂, C₃, hC1, hdisp, hbody⟩ := E.sound c hs hsm
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hbody ωstar hω0 c.D c.H c.K
    c.params.s c.params.γ c.params.err c.params.E0 hopen htransl hholo hper hreal hH.2 hK hKp hKr
    hball hDK (checkGram_sound hs hg) hTu hTb S.hs1 S.hsσ hν1 hν2 S.hγ S.hγγbar hdio S.he0
    (hinv hω) hen hC1
  have hd : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ)) := by
    have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
    have := Real.rpow_pos_of_pos hρ0 (2 * (c.params.tau : ℝ))
    have := S.hγ
    positivity
  have hmono : ∀ C : ℝ, C ≤ max C₂ C₃ → C * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp :=
    fun C hC => (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC S.he0) hd.le).trans
      hdisp
  exact ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans (hmono _ (le_max_left _ _)),
    h11.trans (hmono _ (le_max_right _ _))⟩

end Sound

end KAM.CertificateSharp
