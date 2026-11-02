/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetLift
public import KAM.CertificateSharp.Packed.JetBase

/-!
# The packed jet route with lifted constant slots

The consumers of the packed jet (`checkTorsionJ`, `checkFrameMajorantsRJ`, `checkInvarianceJ`,
`checkEnergyJ`), the base checker `jetBase` and the engine `routeARefinedPackedJ`, with the jet's
wanted slots read through `jetSlotsL` and checked by `jetCheckL` (`JetLift.lean`): a constant slot
(a Hamiltonian linear in an action) is lifted to the box. Every definition is its landed
counterpart with `jetLowOk`, `jetFullOk`, `jetSlots` replaced by `jetLowOkL`, `jetFullOkL`,
`jetSlotsL`; every soundness proof is the landed one with `jetLowOk_sound`, `jetFullOk_sound`
replaced by `jetLowOkL_sound`, `jetFullOkL_sound` (the inner checks `torsRCoreJ`, `trTChainOkJ`,
`ivRowOk`, `enOk` take any slots). The end to end `checkV2With_jetBaseLPackedJL_sound` concludes the
landed `CertifiedTorus`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith KAM.CertificateSharp
  KAM.CertificateSharp.V2

open scoped Matrix Matrix.Norms.Operator

section Checks

variable {n : ℕ} {α : Type} [CertArith α]

/-- **The jet chain at `cfgLow`** with lifted constants, on the torsion's box and scale. -/
def jetLowOkL (rb : PRBook) (jd : JetData) (c : TorusCertificate n α) : Bool :=
  layoutEq jd.jb.Lb rb.Lb && jd.jb.P == rb.P &&
    jetCheckL n c.weight c.piEnc c.cfgLow c.emb c.ham.jet.prog jd rb.bA (torsionSlots n c.ham.jet)

/-- The rounded packed torsion check on the jet's boundary, with lifted constants. -/
def checkTorsionJL (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jd : JetData) (c : TorusCertificate n α) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && jetLowOkL rb jd c && ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm &&
        torsRCoreJ n c.gramInv c.weight c.cfgLow c.freqBox c.params.s c.ham.jet (jetSlotsL n jd) rb
          mm tm rm eps c.torsInv (c.params.σT - c.params.μ)
    | none => false
  | none => false

/-- Packed `sup |T| ≤ bT` on the jet's torsion, with lifted constants. -/
def checkFrameTRJL (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jd : JetData) (c : TorusCertificate n α) (bT : ℚ) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && jetLowOkL rb jd c && ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm &&
        trTChainOkJ n c.gramInv c.weight c.cfgLow c.freqBox c.params.s c.ham.jet (jetSlotsL n jd) rb
          mm tm rm eps &&
        trFrameTOk (α := α) n c.weight rb rm bT
    | none => false
  | none => false

/-- The packed frame majorants on the jet's torsion, with lifted constants. -/
def checkFrameMajorantsRJL (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) (c : TorusCertificate n α) (b : FrameBounds) : Bool :=
  checkFrameLR bk mm rb tm c b.bL && checkFrameNR bk mm rb tm rm c b.bN b.bNt &&
    checkFrameTRJL bk mm rb tm rm jd c b.bT && checkFrameOmega c b.bOm

/-- **The jet chain at `cfgFull`** with lifted constants, for `v0` and the `d1` slots. -/
def jetFullOkL (ib : PIBook) (jd : JetData) (c : TorusCertificate n α) : Bool :=
  layoutEq jd.jb.Lb ib.Lb && jd.jb.P == ib.P &&
    jetCheckL n c.weight c.piEnc c.cfgFull c.emb c.ham.jet.prog jd ib.bJ
      (c.ham.jet.v0 :: d1Slots n c.ham.jet)

/-- The packed invariance check on the jet's boundary, with lifted constants. -/
def checkInvarianceJL (bk : PGramBook) (mm : PGramMemo) (ib : PIBook) (jd : JetData)
    (c : TorusCertificate n α) : Bool :=
  (gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ)).isSome &&
    ib.P == bk.P && jetFullOkL ib jd c && ivGuard n c.weight c.freqBox c.params.s ib mm &&
    (List.range (n + n)).all fun a =>
      ivRowOk n c.weight c.freqBox c.params.s c.ham.jet (jetSlotsL (α := α) n jd) ib mm
        c.params.err a

/-- The packed energy check on the jet's boundary, with lifted constants. -/
def checkEnergyJL (ib : PIBook) (jd : JetData) (c : TorusCertificate n α) : Bool :=
  jetFullOkL ib jd c && enGuard n ib &&
    enOk n c.ham.jet (jetSlotsL (α := α) n jd) ib c.params.E0 c.params.err

end Checks

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- The jet chain at `cfgLow` gives packed models of the (lifted) torsion slots on the torsion's
box. -/
theorem jetLowOkL_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {rb : PRBook}
    {jd : JetData} (h : jetLowOkL rb jd c = true) :
    JSlotsEnc rb.Lb rb.bA rb.P (jetSlotsL (α := α) n jd) n c.weight.rho c.ham.jet.prog c.emb
      (torsionSlots n c.ham.jet) := by
  have S := checkStatic_sound hs
  simp only [jetLowOkL, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hL, hP⟩, hj⟩ := h
  have hJ := jetPackedL_sound S.hW S.hpe hj
  rw [layoutEq_eq hL, hP] at hJ
  exact hJ

/-- The jet chain at `cfgFull` gives packed models of `v0` and the (lifted) `d1` slots. -/
theorem jetFullOkL_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {ib : PIBook}
    {jd : JetData} (h : jetFullOkL ib jd c = true) :
    JSlotsEnc ib.Lb ib.bJ ib.P (jetSlotsL (α := α) n jd) n c.weight.rho c.ham.jet.prog c.emb
      (c.ham.jet.v0 :: d1Slots n c.ham.jet) := by
  have S := checkStatic_sound hs
  simp only [jetFullOkL, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hL, hP⟩, hj⟩ := h
  have hJ := jetPackedL_sound S.hW S.hpe hj
  rw [layoutEq_eq hL, hP] at hJ
  exact hJ

/-- **Soundness of the rounded packed torsion sub-check with lifted constants.** -/
theorem checkTorsionJL_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} (h : checkTorsionJL bk mm rb tm rm jd c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
        (c.params.σT : ℝ) - c.params.μ := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  unfold checkTorsionJL at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hP, hjet⟩, hD2⟩, hcore⟩ := h
      have := torsRJ_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD c.gramInv c.cfgLow
        S.hpe hG heps (jetLowOkL_sound hs hjet) hP hD2 c.freqBox c.params.s c.torsInv _ hcore hω
      push_cast at this
      exact this
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The packed `sup |T|` bound on the jet's torsion, with lifted constants. -/
theorem checkFrameTRJL_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D)
    (hE : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} {bT : ℚ} (h : checkFrameTRJL bk mm rb tm rm jd c bT = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.weight.rho, ∀ i : Fin n, ∑ j : Fin n,
      ‖KAM.Iso.extendedTorsion c.H c.K ((c.params.s : ℝ) • ωstar) θ (Sum.inl i) (Sum.inl j)‖ ≤
        bT := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE θ hθ (Metric.mem_ball_self S.hμ)
  unfold checkFrameTRJL at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hP, hjet⟩, hD2⟩, hch⟩, hTok⟩ := h
      have hT := trT_chainJ (isOpen_certDomain _ _ _ _) hH S.hW hKD c.gramInv c.cfgLow S.hpe hn
        hG heps (jetLowOkL_sound hs hjet) hP hD2 hω hch
      have nrm := trNormOk_spec (by simp only [trTChainOkJ, Bool.and_eq_true] at hch; tauto)
      simp only [trFrameTOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at hTok
      obtain ⟨haT, hrow⟩ := hTok
      exact frameT_bound S.hW (hT.mono (le_trans haT (Nat.le_add_right _ _))) nrm.nW hrow
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Soundness of the packed frame majorants on the jet's torsion, with lifted constants.** -/
theorem checkFrameMajorantsRJL_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} {b : FrameBounds} (h : checkFrameMajorantsRJL bk mm rb tm rm jd c b = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) : FrameMajorants c b ωstar := by
  have S := checkStatic_sound hs
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ
    rwa [S.hrho]
  simp only [checkFrameMajorantsRJL, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hNc⟩, hTc⟩, hOm⟩ := h
  obtain ⟨hNr, hNt⟩ := checkFrameNR_sound hs hNc
  refine ⟨fun θ hθ j => checkFrameLR_sound hs hL θ (hstrip θ hθ) j,
    fun θ hθ r => hNr θ (hstrip θ hθ) r, fun θ hθ j => hNt θ (hstrip θ hθ) j,
    fun θ hθ i => checkFrameTRJL_sound hs hH.1 hE.1 hTc hω θ (hstrip θ hθ) i, ?_⟩
  unfold checkFrameOmega at hOm
  simp only [decide_eq_true_eq] at hOm
  exact (norm_le_freqNormUp hω).trans (by exact_mod_cast hOm)

/-- **Soundness of the packed invariance sub-check, with lifted constants.** -/
theorem checkInvarianceJL_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {ib : PIBook} {jd : JetData}
    (h : checkInvarianceJL bk mm ib jd c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  simp only [checkInvarianceJL, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hGs, hP⟩, hjet⟩, hg⟩, hrow⟩ := h
  obtain ⟨δβ, hG⟩ := Option.isSome_iff_exists.mp hGs
  have g := ivGuard_spec hg
  have hJ := jetFullOkL_sound hs hjet
  have hK := ptK_encloses (tb := ib.toT) S.hW S.hpe c.emb (pgEntries_of_check hG) hP g.wb g.pK
    g.nK
  have hF := fun l : Fin n => ptF_encloses (α := α) (tb := ib.toT) g.w0 g.s0 (s := c.params.s) hω
    l (g.fF l.val l.isLt) c.weight.rho
  have hx := fun x => ivX_encloses (isOpen_certDomain n c.weightH.rho c.centre c.radius) hH.1
    S.hW hKD g hK hF (fun y => hJ _ (d1Slot_mem_full c.ham.jet y)) x
  intro θ hθ
  rw [← S.hrho] at hθ
  rw [← norm_sumVec, pi_norm_le_iff_of_nonneg S.he0]
  intro x
  have hb := (LawfulCertArith.ble_sound _ _ (hrow _ (phaseNat_lt_add x))).trans
    (LawfulCertArith.ofRatDown_le _)
  exact (PEnc.norm_le_bound (hx x) hθ).trans hb

/-- **Soundness of the packed energy sub-check, with lifted constants.** -/
theorem checkEnergyJL_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {ib : PIBook} {jd : JetData} (h : checkEnergyJL ib jd c = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hρ : (0 : ℝ) < c.weight.rho := by
    rw [S.hrho]; exact S.hρinf.trans S.hρinfρ
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.K θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  have hHd : DifferentiableOn ℂ c.H c.D :=
    (c.ham.contDiffOn_eval (isOpen_certDomain _ _ _ _) hH.1).differentiableOn (by simp)
  have hHK : ContinuousOn (fun θ => c.H (c.K θ)) (complexStrip n c.weight.rho) :=
    hHd.continuousOn.comp (c.emb.differentiable_eval n).continuous.continuousOn hKD
  simp only [checkEnergyJL, enGuard, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hjet, ⟨⟨hw, hdim⟩, hz⟩, hA⟩, hok⟩ := h
  have hv := (jetFullOkL_sound hs hjet _ List.mem_cons_self).congr
    (g := fun θ => c.H (c.K θ)) fun θ _ => c.ham.jet_v0 _
  have havg := PEnc.average hw hdim (slot_zslot hz) hA hρ hHK hv
  set z := ptDigit n ib.Lb ib.P ((jetSlotsL (α := α) n jd).x c.ham.jet.v0)
  have hdig : qC z = ((slotAt ib.Lb.width (zslot n ib.Lb)
      ((jetSlotsL (α := α) n jd).x c.ham.jet.v0).re : ℂ) + Complex.I * (slotAt ib.Lb.width
      (zslot n ib.Lb) ((jetSlotsL (α := α) n jd).x c.ham.jet.v0).im : ℂ)) / 2 ^ ib.P := by
    simp only [z]
    unfold qC ptDigit
    push_cast
    ring
  have hEa : torusAverage (fun v : Fin n → ℝ => c.H (c.K fun j => (v j : ℂ))) =
      KAM.Iso.energyAverage c.H c.K := rfl
  rw [hEa, ← hdig] at havg
  have hb := (LawfulCertArith.ble_sound _ _ hok).trans (LawfulCertArith.ofRatDown_le _)
  have hu := LawfulCertArith.upAdd_ge (ofRatUp (|z.1 - c.params.E0| + |z.2|) : α)
    ((jetSlotsL (α := α) n jd).r c.ham.jet.v0)
  have hq := LawfulCertArith.ofRatUp_ge (α := α) (|z.1 - c.params.E0| + |z.2|)
  have hz' := norm_qC_sub_le z c.params.E0
  have hcast : ((|z.1 - c.params.E0| + |z.2| : ℚ) : ℝ) = |(z.1 : ℝ) - c.params.E0| + |(z.2 : ℝ)| :=
    by push_cast; rfl
  rw [hcast] at hq
  calc ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖
      ≤ ‖KAM.Iso.energyAverage c.H c.K - qC z‖ + ‖qC z - ((c.params.E0 : ℝ) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ val ((jetSlotsL (α := α) n jd).r c.ham.jet.v0) +
          (|(z.1 : ℝ) - c.params.E0| + |(z.2 : ℝ)|) :=
        add_le_add havg hz'
    _ ≤ c.params.err := by linarith

end Sound

/-! ### The base checker and the engine -/

/-- **The packed base checker on the packed jet, with lifted constants.** -/
def jetBaseL (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jl : JetData) (ib : PIBook) (jf : JetData) : BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbedding c &&
    checkGramPacked bk mm c && checkTorsionJL bk mm rb tm rm jl c &&
    checkInvarianceJL bk mm ib jf c && checkEnergyJL ib jf c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hg⟩, ht⟩, hi⟩, hen⟩ := h
    have hH := checkHamBounds_sound hs hh
    have hE := checkEmbedding_sound hs he
    obtain ⟨hTu, hTb⟩ := checkTorsionJL_sound hs hH hE ht hω
    exact ⟨hs, hH, hE, checkGramPacked_sound hs hg, hTu, hTb,
      checkInvarianceJL_sound hs hH hE hi hω, checkEnergyJL_sound hs hH hE hen⟩

/-- The test of route A refined with the packed frames on the jet's torsion, with lifted
constants. -/
def refinedTestPackedJL (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (w : RefinedWit) : Bool :=
  checkHamClaim c w.R && checkFrameMajorantsRJL bk mm rb tm rm jd c (w.R.frame c.freqBox) &&
    refinedCore n c.params c.freqBox w

/-- **Route A refined with the packed frames on the jet's torsion, with lifted constants.** -/
def routeARefinedPackedJL (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) : EngineV2 where
  Wit := RefinedWit
  test := fun c w => refinedTestPackedJL bk mm rb tm rm jd c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestPackedJL, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    obtain ⟨h1, h2, h3, h4, -⟩ := checkFrameMajorantsRJL_sound B.hs B.hH B.hEm hF hω
    exact refinedCore_sound c w hω hdio B (checkHamClaim_sound B.hs hH) ⟨h1, h2, h3, h4⟩ hc

/-- **End to end, the packed route with lifted constants**: a certificate passing the v2 certifier
with `jetBaseL` and `routeARefinedPackedJL` is a landed `CertifiedTorus`. -/
theorem checkV2With_jetBaseLPackedJL_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jl : JetData) (ib : PIBook) (jf : JetData) {c : TorusCertificate n α} {w : RefinedWit}
    (h : checkV2With (jetBaseL bk mm rb tm rm jl ib jf) (routeARefinedPackedJL bk mm rb tm rm jl)
      c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound _ _ h hω hdio

/-! ### Assembly from parts -/

section Of

variable {α : Type} [CertArith α] {n : ℕ}

/-- The torsion check with lifted constants from its parts. -/
theorem checkTorsionJL_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jd : JetData} {δβ : α × α} {eps : α}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hP : rb.P = bk.P) (hjet : jetLowOkL rb jd c = true)
    (hD2 : ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm = true)
    (hcore : torsRCoreJ n c.gramInv c.weight c.cfgLow c.freqBox c.params.s c.ham.jet
      (jetSlotsL n jd) rb mm tm rm eps c.torsInv (c.params.σT - c.params.μ) = true) :
    checkTorsionJL bk mm rb tm rm jd c = true := by
  unfold checkTorsionJL
  rw [hG]
  dsimp only
  rw [heps]
  dsimp only
  rw [hP, hjet, hD2, hcore]
  simp

/-- The frame majorants with lifted constants from their parts. -/
theorem checkFrameMajorantsRJL_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jd : JetData} {δβ : α × α} {eps : α}
    {b : FrameBounds}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hP : rb.P = bk.P) (hjet : jetLowOkL rb jd c = true)
    (hD2 : ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm = true)
    (hlay : trLayOk n rb = true) (hnrm : trNormOk n c.weight c.freqBox c.params.s rb = true)
    (hpk : ptPackOk n c.gramInv c.cfgLow rb.toT mm tm = true)
    (hN : trStN n c.gramInv c.weight c.cfgLow rb mm rm eps = true)
    (hDL : trStDL (α := α) n c.weight c.freqBox c.params.s rb tm rm = true)
    (hDG : trStDG (α := α) n c.weight rb mm rm = true)
    (hC : trStC n c.gramInv c.weight c.cfgLow rb rm eps = true)
    (hDGi : trStDGi n c.gramInv c.weight c.cfgLow rb rm eps = true)
    (hDN : trStDN n c.gramInv c.weight c.cfgLow rb mm rm eps = true)
    (hXN : trStXNJ n c.ham.jet (jetSlotsL (α := α) n jd) c.weight rb rm = true)
    (hL : trFrameLOk (α := α) n c.weight rb mm b.bL = true)
    (hNok : trFrameNOk (α := α) n rb rm b.bN b.bNt = true)
    (hT : trFrameTOk (α := α) n c.weight rb rm b.bT = true) (hOm : checkFrameOmega c b.bOm = true) :
    checkFrameMajorantsRJL bk mm rb tm rm jd c b = true := by
  unfold checkFrameMajorantsRJL checkFrameLR checkFrameNR checkFrameTRJL trTChainOkJ
  rw [hG]
  dsimp only
  rw [heps]
  dsimp only
  rw [hP, hjet, hD2, hlay, hnrm, hpk, hN, hDL, hDG, hC, hDGi, hDN, hXN, hL, hNok, hT, hOm]
  simp

/-- The invariance check with lifted constants from its parts. -/
theorem checkInvarianceJL_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {ib : PIBook} {jd : JetData} {δβ : α × α}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (hP : ib.P = bk.P) (hjet : jetFullOkL ib jd c = true)
    (hg : ivGuard n c.weight c.freqBox c.params.s ib mm = true)
    (hrow : ∀ a < n + n, ivRowOk n c.weight c.freqBox c.params.s c.ham.jet
      (jetSlotsL (α := α) n jd) ib mm c.params.err a = true) :
    checkInvarianceJL bk mm ib jd c = true := by
  simp only [checkInvarianceJL, hG, Option.isSome_some, hP, beq_self_eq_true, hjet, hg,
    Bool.and_self, Bool.true_and, List.all_eq_true, List.mem_range]
  exact hrow

/-- The energy check with lifted constants from its parts. -/
theorem checkEnergyJL_of {c : TorusCertificate n α} {ib : PIBook} {jd : JetData}
    (hjet : jetFullOkL ib jd c = true) (hg : enGuard n ib = true)
    (hok : enOk n c.ham.jet (jetSlotsL (α := α) n jd) ib c.params.E0 c.params.err = true) :
    checkEnergyJL ib jd c = true := by
  simp only [checkEnergyJL, hjet, hg, hok, Bool.and_self]

/-- `jetBaseL` from its parts. -/
theorem jetBaseL_check_of {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jl : JetData} {ib : PIBook} {jf : JetData}
    {c : TorusCertificate n α} {δβ : α × α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true)
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ)
    (ht : checkTorsionJL bk mm rb tm rm jl c = true) (hi : checkInvarianceJL bk mm ib jf c = true)
    (hen : checkEnergyJL ib jf c = true) :
    (jetBaseL bk mm rb tm rm jl ib jf).check c = true := by
  have hg : checkGramPacked bk mm c = true := by
    simp only [checkGramPacked, hG, Option.isSome_some]
  simp only [jetBaseL, hs, hh, he, hg, ht, hi, hen, Bool.and_self]

end Of

end KAM.CertificateSharp.Packed
