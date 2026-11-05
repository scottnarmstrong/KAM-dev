/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.TorsRChain

/-!
# The rounded packed torsion stage: soundness

* `torsR_sound`: a passing core (with passing boundary entries) gives the conclusion of the landed
  `torsionAvgCheck_sound` for the frozen `extendedTorsionAverage`: the averages of `T` and `Y` are
  within the table radii of the table centres (`PEnc.average` and the table checks), the frequency
  column and the corner are exact, and `tabFinal_sound` closes;
* `checkTorsionR_sound`: **the conclusion of the landed `checkTorsion_sound_of`**, under its
  hypotheses; `checkTorsionR_of`: the check from its parts.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **The averaged torsion bound from a passing rounded core.** -/
theorem torsR_sound (hn : 1 ≤ n) {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hG : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {ms : List (CertModel α)}
    (hms : SlotsEnclose n e K W.rho ms) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    (hP : rb.P = bk.P) (hent : ptEntries n K W cfg pe rb.toT tm ms = true) (box : FreqBox)
    (s : ℚ) (S : List (List (CC α))) (σTμ : ℚ)
    (hcore : torsRCore n Binv W cfg box s rb mm tm rm eps S σTμ = true) {ω : Fin n → ℝ}
    (hω : FreqEncloses n box ω) :
    IsUnit (KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω))⁻¹ i j‖ ≤
        σTμ := by
  -- the Gram facts
  obtain ⟨-, hGs⟩ := gramPackedCheck_sound hn K Binv hW cfg hpe bk mm σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  have hρ : (0 : ℝ) < W.rho := CertWeight.rho_pos hW
  -- the guards and the boundary
  simp only [torsRCore, Bool.and_eq_true] at hcore
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlay, hnrm⟩, hpk⟩, hN⟩, hDL⟩, hDG⟩, hC⟩, hDGi⟩, hDN⟩, hXN⟩, hTc⟩, hYc⟩,
    hfin⟩ := hcore
  have lay := trLayOk_spec hlay
  have nrm := trNormOk_spec hnrm
  have pk := ptPackOk_spec hpk
  obtain ⟨eD2, eA, eD1⟩ := ptEntries_spec hent
  -- the boundary models
  have hK := ptK_encloses (tb := rb.toT) hW hpe K (pgEntries_of_check hG) hP lay.wb pk.pK nrm.nK
  have hB := ptB_encloses (tb := rb.toT) (eps := eps) hW lay.wb pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2 := ptD2_encloses (tb := rb.toT) hW hpe K lay.wb eD2 pk.pD nrm.nD
  have hF := fun l : Fin n => ptF_encloses (α := α) (tb := rb.toT) lay.w0 lay.s0 (s := s) hω l
    (nrm.fF l.val l.isLt) W.rho
  have hA := ptA_encloses (tb := rb.toT) hW hpe hD hnv hKD hms lay.wb eA pk.pA nrm.nA
  have hD1 := ptD1_encloses (tb := rb.toT) hW hpe hD hnv hKD hms lay.wb eD1 pk.pD1 nrm.nA
  -- the chain
  have hDL0 := trDL0_encloses K lay hD2 hF
  have hNm := trNm_encloses hW lay nrm hK hB hN
  have hNN := hNm.omega
  have hDLm := trDLm_encloses hW lay nrm hDL0 hDL
  have hDGm := trDGm_encloses hW lay nrm hK hDLm hDG
  have hCm := trCm_encloses hW lay nrm hB hDGm hC
  have hDGim := trDGi_encloses hW lay nrm hCm hB hDGi
  have hDNm := trDN_encloses hW lay nrm hK hB hDLm hDGim hDN
  have hXNm := trXNm_encloses hW lay nrm hA hNN hDNm hXN
  have hT := trT_encloses lay hNN hXNm
  have hY := trY_encloses lay hD1 hNN
  -- the entries of the average
  set A := KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω)
  have hH : DifferentiableOn ℂ e.eval D := (e.contDiffOn_eval hD hnv).differentiableOn (by simp)
  have hcont := fun a b => continuousOn_extendedTorsion (ω := (s : ℝ) • ω) hD hH
    (K.differentiable_eval n) hKD hGu a b
  have hdig : ∀ (L : PackLayout) (e' : ℕ) (x : PC),
      qC (ptDigit n L e' x) = ((slotAt L.width (zslot n L) x.re : ℂ) +
        Complex.I * (slotAt L.width (zslot n L) x.im : ℂ)) / 2 ^ e' := by
    intro L e' x
    unfold qC ptDigit
    push_cast
    ring
  simp only [trTCheck, trYCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at hTc hYc
  refine tabFinal_sound (A := A) (fun x y => ?_) hfin
  have hA' : A x y = torusAverage (fun v : Fin n → ℝ =>
      KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) (fun i => (v i : ℂ)) x y) := rfl
  rw [hA']
  rcases x with i | _ <;> rcases y with j | _
  · -- the torsion block
    have hTij := (hT i j).congr (g := fun θ =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j))
      fun θ hθ => by
        show _ = torsion e.eval (K.eval n) ((s : ℝ) • ω) θ i j
        rw [torsion_eq_models (K.differentiable_eval n) hGu _ hθ]
    have h1 := PEnc.average lay.wW lay.dimsW lay.sw nrm.fT hρ (hcont _ _) hTij
    obtain ⟨hc, hr⟩ := hTc i.val i.isLt j.val j.isLt
    have hr' := (LawfulCertArith.ble_sound _ _ hr).trans (LawfulCertArith.ofRatDown_le _)
    simp only [torsionIdx, Sum.elim_inl, trCentre, trRad, i.isLt, j.isLt, ↓reduceIte]
    rw [← hc, hdig]
    exact h1.trans hr'
  · -- the frequency column
    simp only [torsionIdx, Sum.elim_inl, Sum.elim_inr, trCentre, trRad, i.isLt, lt_irrefl,
      ↓reduceIte]
    show ‖torusAverage (fun _ : Fin n → ℝ => ((((s : ℝ) • ω) i : ℝ) : ℂ)) - _‖ ≤ _
    rw [torusAverage_const_c]
    have hb : |ω i - ((box.getD i.val (0, 0)).1 : ℝ)| ≤ ((box.getD i.val (0, 0)).2 : ℝ) := hω i
    unfold qC
    have e1 : ((((s : ℝ) • ω) i : ℝ) : ℂ) - (((s * (box.getD i.val (0, 0)).1 : ℚ) : ℂ) +
        Complex.I * ((0 : ℚ) : ℂ)) =
        (((s : ℝ) * (ω i - ((box.getD i.val (0, 0)).1 : ℝ)) : ℝ) : ℂ) := by
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    push_cast
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  · -- the last row
    have hYj := (hY () j).congr (g := fun θ =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inr ()) (Sum.inl j))
      fun θ _ => by
        show _ = fderiv ℂ e.eval (K.eval n θ) (normalFrame (K.eval n) θ j)
        rw [fderiv_apply_normalFrame]
        beta_reduce
        rw [Matrix.mul_apply]
        simp only [normalMat, Matrix.mul_assoc, Matrix.of_apply]
    have h1 := PEnc.average lay.wW lay.dimsW lay.sw nrm.fY hρ (hcont _ _) hYj
    obtain ⟨hc, hr⟩ := hYc j.val j.isLt
    have hr' := (LawfulCertArith.ble_sound _ _ hr).trans (LawfulCertArith.ofRatDown_le _)
    simp only [torsionIdx, Sum.elim_inl, Sum.elim_inr, trCentre, trRad, j.isLt, lt_irrefl,
      ↓reduceIte]
    rw [← hc, hdig]
    exact h1.trans hr'
  · -- the corner
    simp only [torsionIdx, Sum.elim_inr, trCentre, trRad, lt_irrefl, ↓reduceIte]
    show ‖torusAverage (fun _ : Fin n → ℝ => (0 : ℂ)) - _‖ ≤ _
    rw [torusAverage_const_c]
    simp [qC]

/-- **Soundness of the rounded packed torsion sub-check**: the conclusion of the landed
`checkTorsion_sound_of`, under its hypotheses. -/
theorem checkTorsionR_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    (h : checkTorsionR bk mm rb tm rm c = true) {ωstar : Fin n → ℝ}
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
  unfold checkTorsionR at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps ms heps hcomp
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hP, hent⟩, hcore⟩ := h
      have hms : SlotsEnclose n c.ham c.emb c.weight.rho ms := by
        have := Slp.compose_sound c.ham.jet.prog c.emb c.wit S.hW c.cfgLow S.hpe _ hcomp
        exact ⟨this.1, this.2⟩
      have := torsR_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD c.gramInv c.cfgLow
        S.hpe hG heps hms hP hent c.freqBox c.params.s c.torsInv _ hcore hω
      push_cast at this
      exact this
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [LawfulCertArith α] in
/-- The rounded packed torsion check from its parts (for proofs split across declarations). -/
theorem checkTorsionR_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {δβ : α × α} {eps : α} {ms : List (CertModel α)}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hcomp : Slp.compose n c.ham.jet.prog c.emb c.wit c.weight c.cfgLow c.piEnc
      (torsionSlots n c.ham.jet) = some ms) (hP : rb.P = bk.P)
    (hent : ptEntries n c.emb c.weight c.cfgLow c.piEnc rb.toT tm ms = true)
    (hcore : torsRCore n c.gramInv c.weight c.cfgLow c.freqBox c.params.s rb mm tm rm eps
      c.torsInv (c.params.σT - c.params.μ) = true) :
    checkTorsionR bk mm rb tm rm c = true := by
  unfold checkTorsionR
  rw [hG]
  dsimp only
  rw [heps, hcomp]
  dsimp only
  rw [hP, hent, hcore]
  simp

end Sound

end KAM.CertificateSharp.Packed
