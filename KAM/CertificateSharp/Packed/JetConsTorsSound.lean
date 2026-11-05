/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsTors
public import KAM.CertificateSharp.Packed.JetCheck

/-!
# The rounded packed torsion on the jet's boundary: soundness and the check

* `torsRJ_sound`: a passing `torsRCoreJ`, with packed models of the torsion slots
  (`JSlotsEnc`, the conclusion of `jetPacked_sound`) and the `D²K` boundary, gives the conclusion of
  the landed `torsionAvgCheck_sound` for the frozen `extendedTorsionAverage` (the chain of B3b's
  `torsR_sound`, with `trAJ_encloses` and `trD1J_encloses` in place of the landed composition);
* `jetSlots`, `jetLowOk`, `jetLowOk_sound`: the keyed jet chain at `cfgLow` (`jetCheck`), on the
  torsion's box and scale, for the torsion slots; its soundness is `jetPacked_sound`;
* `checkTorsionJ`: the packed Gram check (for `δβ`), the jet chain, the `D²K` boundary and the
  core; **`checkTorsionJ_sound`: the conclusion of the landed `checkTorsion_sound_of`**, under its
  hypotheses, with no landed `Slp.compose`;
* `checkTorsionJ_of`, `torsRCoreJ_of`: the check from its parts (each established once, in
  separate declarations).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **The averaged torsion bound from a passing rounded core on the jet's boundary.** -/
theorem torsRJ_sound (hn : 1 ≤ n) {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hG : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {js : JSlots α} (hJ : JSlotsEnc rb.Lb rb.bA rb.P js n W.rho e.jet.prog K (torsionSlots n e.jet))
    (hP : rb.P = bk.P) (hD2 : ptD2All n K W cfg pe rb.toT tm = true) (box : FreqBox)
    (s : ℚ) (S : List (List (CC α))) (σTμ : ℚ)
    (hcore : torsRCoreJ n Binv W cfg box s e.jet js rb mm tm rm eps S σTμ = true)
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) :
    IsUnit (KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω))⁻¹ i j‖ ≤
        σTμ := by
  -- the Gram facts
  obtain ⟨-, hGs⟩ := gramPackedCheck_sound hn K Binv hW cfg hpe bk mm σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  have hρ : (0 : ℝ) < W.rho := CertWeight.rho_pos hW
  -- the guards and the boundary
  simp only [torsRCoreJ, Bool.and_eq_true] at hcore
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlay, hnrm⟩, hpk⟩, hN⟩, hDL⟩, hDG⟩, hC⟩, hDGi⟩, hDN⟩, hXN⟩, hTc⟩, hYc⟩,
    hfin⟩ := hcore
  have lay := trLayOk_spec hlay
  have nrm := trNormOk_spec hnrm
  have pk := ptPackOk_spec hpk
  have eD2 : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2Ok n K W cfg pe rb.toT tm r j l = true := by
    simpa only [ptD2All, List.all_eq_true, List.mem_range] using hD2
  -- the boundary models
  have hK := ptK_encloses (tb := rb.toT) hW hpe K (pgEntries_of_check hG) hP lay.wb pk.pK nrm.nK
  have hB := ptB_encloses (tb := rb.toT) (eps := eps) hW lay.wb pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2m := ptD2_encloses (tb := rb.toT) hW hpe K lay.wb eD2 pk.pD nrm.nD
  have hF := fun l : Fin n => ptF_encloses (α := α) (tb := rb.toT) lay.w0 lay.s0 (s := s) hω l
    (nrm.fF l.val l.isLt) W.rho
  have hA := trAJ_encloses hD hnv hKD hJ
  have hD1 := trD1J_encloses hD hnv hKD hJ
  -- the chain
  have hDL0 := trDL0_encloses K lay hD2m hF
  have hNm := trNm_encloses hW lay nrm hK hB hN
  have hNN := hNm.omega
  have hDLm := trDLm_encloses hW lay nrm hDL0 hDL
  have hDGm := trDGm_encloses hW lay nrm hK hDLm hDG
  have hCm := trCm_encloses hW lay nrm hB hDGm hC
  have hDGim := trDGi_encloses hW lay nrm hCm hB hDGi
  have hDNm := trDN_encloses hW lay nrm hK hB hDLm hDGim hDN
  have hXNm := trXNmJ_encloses hW lay nrm hA hNN hDNm hXN
  have hT := trT_encloses lay hNN hXNm
  have hY := trYJ_encloses lay hD1 hNN
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
  simp only [trTCheck, trYCheckJ, List.all_eq_true, List.mem_range, Bool.and_eq_true,
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

end Sound

/-! ### The jet chain at `cfgLow` and the check -/

/-- The packed models of a keyed jet chain's slots (`jetNode`, `jetRad`, `jetNb`). -/
def jetSlots {α : Type} [CertArith α] (jd : JetData) : JSlots α :=
  ⟨jetNode jd, jetRad jd, jetNb jd⟩

/-- **The jet chain at `cfgLow`** for the torsion slots, on the torsion's box and scale, with
load at most `rb.bA` (`jetCheck`; the box agreement is checked). -/
def jetLowOk {n : ℕ} {α : Type} [CertArith α] (rb : PRBook) (jd : JetData)
    (c : TorusCertificate n α) : Bool :=
  layoutEq jd.jb.Lb rb.Lb && jd.jb.P == rb.P &&
    jetCheck n c.weight c.piEnc c.cfgLow c.emb c.ham.jet.prog jd rb.bA (torsionSlots n c.ham.jet)

/-- **The rounded packed torsion check on the jet's boundary** at the certificate's data: the
packed Gram check (for `δβ`), the jet chain at `cfgLow`, the `D²K` boundary, then the core. No
landed `Slp.compose`. -/
def checkTorsionJ {n : ℕ} {α : Type} [CertArith α] (bk : PGramBook) (mm : PGramMemo)
    (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo) (jd : JetData) (c : TorusCertificate n α) :
    Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && jetLowOk rb jd c && ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm &&
        torsRCoreJ n c.gramInv c.weight c.cfgLow c.freqBox c.params.s c.ham.jet (jetSlots jd) rb mm
          tm rm eps c.torsInv (c.params.σT - c.params.μ)
    | none => false
  | none => false

section Check

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- The jet chain at `cfgLow` gives packed models of the torsion slots on the torsion's box. -/
theorem jetLowOk_sound {c : TorusCertificate n α} (hs : checkStatic c = true) {rb : PRBook}
    {jd : JetData} (h : jetLowOk rb jd c = true) :
    JSlotsEnc rb.Lb rb.bA rb.P (jetSlots (α := α) jd) n c.weight.rho c.ham.jet.prog c.emb
      (torsionSlots n c.ham.jet) := by
  have S := checkStatic_sound hs
  simp only [jetLowOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hL, hP⟩, hj⟩ := h
  have hJ := jetPacked_sound S.hW S.hpe hj
  rw [layoutEq_eq hL, hP] at hJ
  exact hJ

/-- **Soundness of the rounded packed torsion sub-check on the jet's boundary**: the conclusion
of the landed `checkTorsion_sound_of`, under its hypotheses. -/
theorem checkTorsionJ_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} (h : checkTorsionJ bk mm rb tm rm jd c = true) {ωstar : Fin n → ℝ}
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
  unfold checkTorsionJ at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hP, hjet⟩, hD2⟩, hcore⟩ := h
      have := torsRJ_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD c.gramInv c.cfgLow
        S.hpe hG heps (jetLowOk_sound hs hjet) hP hD2 c.freqBox c.params.s c.torsInv _ hcore hω
      push_cast at this
      exact this
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [LawfulCertArith α] in
/-- The rounded packed torsion check on the jet's boundary from its parts (for proofs split
across declarations; each part is a shared conjunct). -/
theorem checkTorsionJ_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jd : JetData} {δβ : α × α} {eps : α}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hP : rb.P = bk.P) (hjet : jetLowOk rb jd c = true)
    (hD2 : ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm = true)
    (hcore : torsRCoreJ n c.gramInv c.weight c.cfgLow c.freqBox c.params.s c.ham.jet
      (jetSlots jd) rb mm tm rm eps c.torsInv (c.params.σT - c.params.μ) = true) :
    checkTorsionJ bk mm rb tm rm jd c = true := by
  unfold checkTorsionJ
  rw [hG]
  dsimp only
  rw [heps]
  dsimp only
  rw [hP, hjet, hD2, hcore]
  simp

omit [LawfulCertArith α] in
/-- The core from its conjuncts (each node, the averages and the final test in its own
declaration). -/
theorem torsRCoreJ_of {Binv : List (List (CertPoly α))} {W : CertWeight} {cfg : ModelConfig α}
    {box : FreqBox} {s : ℚ} {J : HamJet} {js : JSlots α} {rb : PRBook} {mm : PGramMemo}
    {tm : PTorsMemo} {rm : PRMemo} {eps : α} {S : List (List (CC α))} {σTμ : ℚ}
    (hlay : trLayOk n rb = true) (hnrm : trNormOk n W box s rb = true)
    (hpk : ptPackOk n Binv cfg rb.toT mm tm = true)
    (hN : trStN n Binv W cfg rb mm rm eps = true)
    (hDL : trStDL (α := α) n W box s rb tm rm = true)
    (hDG : trStDG (α := α) n W rb mm rm = true) (hC : trStC n Binv W cfg rb rm eps = true)
    (hDGi : trStDGi n Binv W cfg rb rm eps = true)
    (hDN : trStDN n Binv W cfg rb mm rm eps = true) (hXN : trStXNJ n J js W rb rm = true)
    (hTc : trTCheck (α := α) n rb rm = true) (hYc : trYCheckJ n J js rb rm = true)
    (hfin : tabFinal n cfg rb.P (trCentre n box s rm) (trRad n box s rm) S σTμ = true) :
    torsRCoreJ n Binv W cfg box s J js rb mm tm rm eps S σTμ = true := by
  simp only [torsRCoreJ, hlay, hnrm, hpk, hN, hDL, hDG, hC, hDGi, hDN, hXN, hTc, hYc, hfin,
    Bool.and_self]

end Check

end KAM.CertificateSharp.Packed
