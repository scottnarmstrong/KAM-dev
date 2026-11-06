/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Trunc.Gram
public import KAM.CertificateSharp.Packed.JetConsFrames

/-!
# The rounded packed torsion on truncated boundary memos

The rounded torsion (`TorsR.lean`, on the jet's boundary `JetConsTors.lean`) packs its boundary, the
`DK` memo of the Gram check and the `D²K` memo, on its box `Lb`; the landed checks `pgEntryOk` and
`ptD2Ok` require these memos to be exact, so `Lb` must hold the embedding's whole support. Here both
memos are checked against the landed models truncated to the box (`jBoxTrunc`, the dropped terms in
the radius):

* `ptD2OkT`, `ptD2AllT`: the truncated `D²K` boundary (on the box of the torsion book's `L1`);
* `ptK_enclosesT`, `ptD2_enclosesT`: the packed models of `DK` and `D²K` from the truncated memos
  (the landed `ptK_encloses`, `ptD2_encloses` with `jBoxTrunc_encloses`);
* `torsRJT_sound`, `trT_chainJT`: the landed `torsRJ_sound` and `trT_chainJ` with the truncated
  Gram check (`gramPackedCheckT`) and boundary; the same conclusions. The stage checks, the
  averages and the final test are the landed ones.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith
open scoped Matrix Matrix.Norms.Operator

section Defs

variable {α : Type} [CertArith α]

/-- One `D²K` entry against the memo, the landed model truncated to the box of `tb.L1`. -/
def ptD2OkT (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (cfg : ModelConfig α)
    (pe : PiEnclosure α) (tb : PTorsBook) (tm : PTorsMemo) (r j l : ℕ) : Bool :=
  memoOk cfg.toMant tb.P (jBoxTrunc W tb.L1 (d2kModel n K W pe r j l))
    (tm.d2.getD (d2Idx n r j l) ([], [], 0))

/-- The truncated `D²K` boundary entries. -/
def ptD2AllT (n : ℕ) (K : CertEmbedding α) (W : CertWeight) (cfg : ModelConfig α)
    (pe : PiEnclosure α) (tb : PTorsBook) (tm : PTorsMemo) : Bool :=
  (List.range (n + n)).all fun r => (List.range n).all fun j => (List.range n).all fun l =>
    ptD2OkT n K W cfg pe tb tm r j l

theorem ptD2AllT_of {n : ℕ} {K : CertEmbedding α} {W : CertWeight} {cfg : ModelConfig α}
    {pe : PiEnclosure α} {tb : PTorsBook} {tm : PTorsMemo}
    (h : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2OkT n K W cfg pe tb tm r j l = true) :
    ptD2AllT n K W cfg pe tb tm = true := by
  simp only [ptD2AllT, List.all_eq_true, List.mem_range]
  exact h

end Defs

section Base

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} {W : CertWeight} {sw Nw : ℕ}
  {cfg : ModelConfig α} {pe : PiEnclosure α} {tb : PTorsBook} {mm : PGramMemo} {tm : PTorsMemo}

/-- `L = DK` from the truncated Gram memo (`ptK_encloses` with the truncated models). -/
theorem ptK_enclosesT (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) {bk : PGramBook} (he : pgEntriesT n K W cfg pe bk mm = true)
    (hP : tb.P = bk.P) (hw : layoutWf tb.L1 = true)
    (hpk : ∀ r < n + n, ∀ a < n, packRepOk tb.L1 (mm.reAt r a) tb.bK = true ∧
      packRepOk tb.L1 (mm.imAt r a) tb.bK = true)
    (hok : normOk W tb.q tb.lK tb.bK tb.L1 = true) :
    PMat.Encloses tb.L1 tb.bK tb.P n W.rho phaseNat Fin.val (ptK (α := α) W tb mm)
      (tangentMat (K.eval n)) := by
  intro x a
  have hr : phaseNat x < 2 * n := by have := phaseNat_lt_add x; omega
  obtain ⟨hd, hmt, hrad⟩ := pgEntriesT_spec he hr a.isLt
  have hm := dkModels_encloses hW hpe K x a
  rw [dkModels, buildMat_entry _ (phaseNat_lt_add _) a.isLt] at hm
  have hm' : (dkModel n K W pe (phaseNat x) a.val).Encloses n W.rho
      (fun θ => tangentMat (K.eval n) θ x a) := hm
  have hmT : (dkModelT n K W pe bk.L1 (phaseNat x) a.val).Encloses n W.rho
      (fun θ => tangentMat (K.eval n) θ x a) := jBoxTrunc_encloses hW bk.L1 hm'
  rw [← hP] at hmt
  obtain ⟨hre, him⟩ := hpk _ (phaseNat_lt_add x) _ a.isLt
  exact PEnc.ofPCRep hW hok (PCRep.ofMants hmt hw hre him) fun θ hθ =>
    (encloses_deg0 hmT hd hθ).trans (LawfulCertArith.ble_sound _ _ hrad)

/-- `∂_l L` from the truncated torsion memo. -/
theorem ptD2_enclosesT (hW : checkWeight W sw Nw = true) (hpe : checkPiEnclosure pe = true)
    (K : CertEmbedding α) (hw : layoutWf tb.L1 = true)
    (hent : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2OkT n K W cfg pe tb tm r j l = true)
    (hpk : ∀ r < n + n, ∀ j < n, ∀ l < n,
      memoPackOk tb.L1 tb.bD (tm.d2.getD (d2Idx n r j l) ([], [], 0)) = true)
    (hok : normOk W tb.q tb.lD tb.bD tb.L1 = true) (l : Fin n) :
    PMat.Encloses tb.L1 tb.bD tb.P n W.rho phaseNat Fin.val (ptD2 (α := α) n W tb tm l.val)
      (fun θ => Matrix.of fun x j =>
        fderiv ℂ (fun y => tangentMat (K.eval n) y x j) θ (Pi.single l 1)) := by
  intro x j
  exact (PEnc.ofMemo hW hok hw (jBoxTrunc_encloses hW tb.L1 (d2kModel_encloses hW hpe K x j l))
    (hent _ (phaseNat_lt_add x) _ j.isLt _ l.isLt)
    (hpk _ (phaseNat_lt_add x) _ j.isLt _ l.isLt)).congr fun θ _ => by simp

end Base

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **The averaged torsion bound** from a passing rounded core on the jet's boundary, on the
truncated memos (`torsRJ_sound` with `ptK_enclosesT`, `ptD2_enclosesT`). -/
theorem torsRJT_sound (hn : 1 ≤ n) {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hD : IsOpen D) (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hG : gramPackedCheckT n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {js : JSlots α} (hJ : JSlotsEnc rb.Lb rb.bA rb.P js n W.rho e.jet.prog K (torsionSlots n e.jet))
    (hP : rb.P = bk.P) (hD2 : ptD2AllT n K W cfg pe rb.toT tm = true) (box : FreqBox)
    (s : ℚ) (S : List (List (CC α))) (σTμ : ℚ)
    (hcore : torsRCoreJ n Binv W cfg box s e.jet js rb mm tm rm eps S σTμ = true)
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) :
    IsUnit (KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage e.eval (K.eval n) ((s : ℝ) • ω))⁻¹ i j‖ ≤
        σTμ := by
  -- the Gram facts
  obtain ⟨-, hGs⟩ := gramPackedCheckT_sound hn K Binv hW cfg hpe bk mm σBμ hG
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
  have eD2 : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2OkT n K W cfg pe rb.toT tm r j l = true := by
    simpa only [ptD2AllT, List.all_eq_true, List.mem_range] using hD2
  -- the boundary models
  have hK := ptK_enclosesT (tb := rb.toT) hW hpe K (pgEntriesT_of_check hG) hP lay.wb pk.pK nrm.nK
  have hB := ptB_encloses (tb := rb.toT) (eps := eps) hW lay.wb pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2m := ptD2_enclosesT (tb := rb.toT) hW hpe K lay.wb eD2 pk.pD nrm.nD
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

/-- **The packed torsion block on the jet's boundary** from the stage checks, on the truncated
memos (`trT_chainJ` with `ptK_enclosesT`, `ptD2_enclosesT`). -/
theorem trT_chainJT {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hn : 1 ≤ n) (hG : gramPackedCheckT n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {js : JSlots α} (hJ : JSlotsEnc rb.Lb rb.bA rb.P js n W.rho e.jet.prog K (torsionSlots n e.jet))
    (hP : rb.P = bk.P) (hD2 : ptD2AllT n K W cfg pe rb.toT tm = true) {box : FreqBox} {s : ℚ}
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω)
    (hch : trTChainOkJ n Binv W cfg box s e.jet js rb mm tm rm eps = true) :
    PMat.Encloses rb.Lw (rb.aT n) (2 * rb.P) n W.rho Fin.val Fin.val (trT (α := α) n rb rm)
      (fun θ => Matrix.of fun i j =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j)) := by
  obtain ⟨-, hGs⟩ := gramPackedCheckT_sound hn K Binv hW cfg hpe bk mm σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  simp only [trTChainOkJ, Bool.and_eq_true] at hch
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlay, hnrm⟩, hpk⟩, hN⟩, hDL⟩, hDG⟩, hC⟩, hDGi⟩, hDN⟩, hXN⟩ := hch
  have lay := trLayOk_spec hlay
  have nrm := trNormOk_spec hnrm
  have pk := ptPackOk_spec hpk
  have eD2 : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2OkT n K W cfg pe rb.toT tm r j l = true := by
    simpa only [ptD2AllT, List.all_eq_true, List.mem_range] using hD2
  have hK := ptK_enclosesT (tb := rb.toT) hW hpe K (pgEntriesT_of_check hG) hP lay.wb pk.pK nrm.nK
  have hB := ptB_encloses (tb := rb.toT) (eps := eps) hW lay.wb pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2m := ptD2_enclosesT (tb := rb.toT) hW hpe K lay.wb eD2 pk.pD nrm.nD
  have hF := fun l : Fin n => ptF_encloses (α := α) (tb := rb.toT) lay.w0 lay.s0 (s := s) hω l
    (nrm.fF l.val l.isLt) W.rho
  have hA := trAJ_encloses hD hnv hKD hJ
  have hNN := (trNm_encloses hW lay nrm hK hB hN).omega
  have hDLm := trDLm_encloses hW lay nrm (trDL0_encloses K lay hD2m hF) hDL
  have hDGm := trDGm_encloses hW lay nrm hK hDLm hDG
  have hCm := trCm_encloses hW lay nrm hB hDGm hC
  have hDGim := trDGi_encloses hW lay nrm hCm hB hDGi
  have hDNm := trDN_encloses hW lay nrm hK hB hDLm hDGim hDN
  have hXNm := trXNmJ_encloses hW lay nrm hA hNN hDNm hXN
  intro i j
  refine (trT_encloses lay hNN hXNm i j).congr fun θ hθ => ?_
  show _ = torsion e.eval (K.eval n) ((s : ℝ) • ω) θ i j
  rw [torsion_eq_models (K.differentiable_eval n) hGu _ hθ]

end Sound

end KAM.CertificateSharp.Packed
