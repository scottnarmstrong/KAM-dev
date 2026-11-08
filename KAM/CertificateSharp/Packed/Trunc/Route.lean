/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Trunc.Tors
public import KAM.CertificateSharp.Packed.JetConsLift

/-!
# The packed jet route on truncated boundary memos

The route of `JetConsLift.lean` (the packed jet with lifted constant slots) with the Gram, torsion
and frame stages on a **small box**:

* the `DK` memo `mm` and the `D²K` memo of the torsion are checked against the landed models
  truncated to the box (`gramPackedCheckT`, `ptD2AllT`; `Trunc/Gram.lean`, `Trunc/Tors.lean`);
* the inverse witness is the certificate's `gramInv` truncated to the box of the Gram book's `LB`
  (`gramInvTrunc`): any witness is sound, since the Gram check certifies its own defect;
* the invariance keeps the data box and an **exact** `DK` memo `mf` (the landed `pgEntries`, without
  the Gram products), since its tolerance is far below any truncation;
* the energy check is `checkEnergyJL`, unchanged.

Every definition is its counterpart in `JetConsLift.lean` (or `Frames.lean` for `|Lᵀ|`, `|N|`) with
these replacements, and every soundness proof is the landed one with `gramPackedCheckT_sound`,
`ptK_enclosesT`, `torsRJT_sound`, `trT_chainJT`. The end to end
`checkV2With_jetBaseLTPackedJLT_sound` concludes the landed `CertifiedTorus`.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith KAM.CertificateSharp
  KAM.CertificateSharp.V2

open scoped Matrix Matrix.Norms.Operator

section Checks

variable {n : ℕ} {α : Type} [CertArith α]

/-- The inverse witness truncated to the box of `L` (the terms with a slot on `L`). -/
def gramInvTrunc (L : PackLayout) (B : List (List (CertPoly α))) : List (List (CertPoly α)) :=
  B.map fun row => row.map fun p => ⟨p.terms.filter fun t => (L.slot t.1).isSome⟩

/-- The truncated inverse witness of a certificate on the Gram book's box. -/
def bwT (bk : PGramBook) (c : TorusCertificate n α) : List (List (CertPoly α)) :=
  gramInvTrunc bk.LB c.gramInv

/-- The rounded packed torsion check on the jet's boundary, with lifted constants, on truncated
memos. -/
def checkTorsionJLT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) (c : TorusCertificate n α) : Bool :=
  match gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && jetLowOkL rb jd c &&
        ptD2AllT n c.emb c.weight c.cfgLow c.piEnc rb.toT tm &&
        torsRCoreJ n (bwT bk c) c.weight c.cfgLow c.freqBox c.params.s c.ham.jet (jetSlotsL n jd)
          rb mm tm rm eps c.torsInv (c.params.σT - c.params.μ)
    | none => false
  | none => false

/-- Packed `|Lᵀ| ≤ b` on truncated memos. -/
def checkFrameLRT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (c : TorusCertificate n α) (b : ℚ) : Bool :=
  (gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ)).isSome &&
    rb.P == bk.P && trLayOk n rb && trNormOk n c.weight c.freqBox c.params.s rb &&
    ptPackOk n (bwT bk c) c.cfgLow rb.toT mm tm && trFrameLOk (α := α) n c.weight rb mm b

/-- Packed `|N| ≤ bN`, `|Nᵀ| ≤ bNt` on truncated memos. -/
def checkFrameNRT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (c : TorusCertificate n α) (bN bNt : ℚ) : Bool :=
  match gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && trLayOk n rb && trNormOk n c.weight c.freqBox c.params.s rb &&
        ptPackOk n (bwT bk c) c.cfgLow rb.toT mm tm &&
        trStN n (bwT bk c) c.weight c.cfgLow rb mm rm eps && trFrameNOk (α := α) n rb rm bN bNt
    | none => false
  | none => false

/-- Packed `sup |T| ≤ bT` on the jet's torsion, with lifted constants, on truncated memos. -/
def checkFrameTRJLT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) (c : TorusCertificate n α) (bT : ℚ) : Bool :=
  match gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && jetLowOkL rb jd c &&
        ptD2AllT n c.emb c.weight c.cfgLow c.piEnc rb.toT tm &&
        trTChainOkJ n (bwT bk c) c.weight c.cfgLow c.freqBox c.params.s c.ham.jet
          (jetSlotsL n jd) rb mm tm rm eps &&
        trFrameTOk (α := α) n c.weight rb rm bT
    | none => false
  | none => false

/-- The packed frame majorants on the jet's torsion, with lifted constants, on truncated memos. -/
def checkFrameMajorantsRJLT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) (c : TorusCertificate n α) (b : FrameBounds) : Bool :=
  checkFrameLRT bk mm rb tm c b.bL && checkFrameNRT bk mm rb tm rm c b.bN b.bNt &&
    checkFrameTRJLT bk mm rb tm rm jd c b.bT && checkFrameOmega c b.bOm

/-- The packed invariance check on the jet's boundary, with lifted constants: the exact `DK` memo
`mf` (the landed `pgEntries`; no Gram products), on the invariance book's box. -/
def checkInvarianceJLT (bk : PGramBook) (mf : PGramMemo) (ib : PIBook) (jd : JetData)
    (c : TorusCertificate n α) : Bool :=
  pgEntries n c.emb c.weight c.cfgLow c.piEnc bk mf &&
    ib.P == bk.P && jetFullOkL ib jd c && ivGuard n c.weight c.freqBox c.params.s ib mf &&
    (List.range (n + n)).all fun a =>
      ivRowOk n c.weight c.freqBox c.params.s c.ham.jet (jetSlotsL (α := α) n jd) ib mf
        c.params.err a

end Checks

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **Soundness of the rounded packed torsion sub-check on truncated memos.** -/
theorem checkTorsionJLT_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} (h : checkTorsionJLT bk mm rb tm rm jd c = true) {ωstar : Fin n → ℝ}
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
  unfold checkTorsionJLT at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hP, hjet⟩, hD2⟩, hcore⟩ := h
      have := torsRJT_sound hn (isOpen_certDomain _ _ _ _) hH.1 S.hW hKD (bwT bk c) c.cfgLow
        S.hpe hG heps (jetLowOkL_sound hs hjet) hP hD2 c.freqBox c.params.s c.torsInv _ hcore hω
      push_cast at this
      exact this
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The packed `|Lᵀ|` bound on truncated memos. -/
theorem checkFrameLRT_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {b : ℚ}
    (h : checkFrameLRT bk mm rb tm c b = true) :
    ∀ θ ∈ complexStrip n c.weight.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤ b := by
  have S := checkStatic_sound hs
  simp only [checkFrameLRT, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hGs, hP⟩, hlay⟩, hnrm⟩, hpk⟩, hLok⟩ := h
  obtain ⟨δβ, hG⟩ := Option.isSome_iff_exists.mp hGs
  have hK := ptK_enclosesT (tb := rb.toT) S.hW S.hpe c.emb (pgEntriesT_of_check hG) hP
    (trLayOk_spec hlay).wb (ptPackOk_spec hpk).pK (trNormOk_spec hnrm).nK
  simp only [trFrameLOk, List.all_eq_true, List.mem_range] at hLok
  intro θ hθ j
  calc ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤
        ∑ r : Fin n ⊕ Fin n, val (pmBound (ptK (α := α) c.weight rb.toT mm) (phaseNat r) j.val) :=
        Finset.sum_le_sum fun r _ => PEnc.norm_le_bound (hK r j) hθ
    _ = ∑ k ∈ Finset.range (n + n), val (pmBound (ptK (α := α) c.weight rb.toT mm) k j.val) :=
        sum_phaseNat_eq (fun k => val (pmBound (ptK (α := α) c.weight rb.toT mm) k j.val))
    _ ≤ b := sum_le_sumUp_bound (fun k _ => le_rfl) (hLok j.val j.isLt)

/-- The packed `|N|`, `|Nᵀ|` bounds on truncated memos. -/
theorem checkFrameNRT_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {bN bNt : ℚ}
    (h : checkFrameNRT bk mm rb tm rm c bN bNt = true) :
    (∀ θ ∈ complexStrip n c.weight.rho, ∀ r : Fin n ⊕ Fin n,
      ∑ j : Fin n, ‖normalMat c.K θ r j‖ ≤ bN) ∧
    ∀ θ ∈ complexStrip n c.weight.rho, ∀ j : Fin n,
      ∑ r : Fin n ⊕ Fin n, ‖normalMat c.K θ r j‖ ≤ bNt := by
  have S := checkStatic_sound hs
  have hn : 1 ≤ n := le_trans (by norm_num) S.hn
  unfold checkFrameNRT at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨⟨hP, hlay⟩, hnrm⟩, hpk⟩, hN⟩, hNok⟩ := h
      obtain ⟨-, hGs⟩ := gramPackedCheckT_sound hn c.emb (bwT bk c) S.hW c.cfgLow S.hpe bk mm _
        hG
      have lay := trLayOk_spec hlay
      have nrm := trNormOk_spec hnrm
      have pk := ptPackOk_spec hpk
      have hK := ptK_enclosesT (tb := rb.toT) S.hW S.hpe c.emb (pgEntriesT_of_check hG) hP lay.wb
        pk.pK nrm.nK
      have hB := ptB_encloses (tb := rb.toT) (eps := eps) S.hW lay.wb pk.pB nrm.nB fun θ hθ =>
        ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
      have hNN := (trNm_encloses S.hW lay nrm hK hB hN).omega
      have hnm : ∀ θ, normalMat c.K θ =
          omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ * (gramMatrix (c.emb.eval n) θ)⁻¹) :=
        fun θ => by unfold normalMat; rw [Matrix.mul_assoc]; rfl
      simp only [trFrameNOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hNok
      obtain ⟨hrow, hcol⟩ := hNok
      refine ⟨fun θ hθ r => ?_, fun θ hθ j => ?_⟩
      · rw [hnm θ]
        calc ∑ j : Fin n, ‖(omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
              (gramMatrix (c.emb.eval n) θ)⁻¹)) r j‖ ≤
              ∑ j : Fin n, val (pmBound (trN (α := α) n rb rm) (phaseNat r) j.val) :=
              Finset.sum_le_sum fun j _ => PEnc.norm_le_bound (hNN r j) hθ
          _ = ∑ k ∈ Finset.range n, val (pmBound (trN (α := α) n rb rm) (phaseNat r) k) :=
              Fin.sum_univ_eq_sum_range
                (fun k => val (pmBound (trN (α := α) n rb rm) (phaseNat r) k)) n
          _ ≤ bN := sum_le_sumUp_bound (fun k _ => le_rfl) (hrow _ (phaseNat_lt_add r))
      · rw [hnm θ]
        calc ∑ r : Fin n ⊕ Fin n, ‖(omegaZeroMatrix n * (tangentMat (c.emb.eval n) θ *
              (gramMatrix (c.emb.eval n) θ)⁻¹)) r j‖ ≤
              ∑ r : Fin n ⊕ Fin n, val (pmBound (trN (α := α) n rb rm) (phaseNat r) j.val) :=
              Finset.sum_le_sum fun r _ => PEnc.norm_le_bound (hNN r j) hθ
          _ = ∑ k ∈ Finset.range (n + n), val (pmBound (trN (α := α) n rb rm) k j.val) :=
              sum_phaseNat_eq (fun k => val (pmBound (trN (α := α) n rb rm) k j.val))
          _ ≤ bNt := sum_le_sumUp_bound (fun k _ => le_rfl) (hcol j.val j.isLt)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The packed `sup |T|` bound on the jet's torsion, with lifted constants, on truncated memos. -/
theorem checkFrameTRJLT_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D)
    (hE : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} {bT : ℚ} (h : checkFrameTRJLT bk mm rb tm rm jd c bT = true)
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
  unfold checkFrameTRJLT at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hP, hjet⟩, hD2⟩, hch⟩, hTok⟩ := h
      have hT := trT_chainJT (isOpen_certDomain _ _ _ _) hH S.hW hKD (bwT bk c) c.cfgLow S.hpe hn
        hG heps (jetLowOkL_sound hs hjet) hP hD2 hω hch
      have nrm := trNormOk_spec (by simp only [trTChainOkJ, Bool.and_eq_true] at hch; tauto)
      simp only [trFrameTOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at hTok
      obtain ⟨haT, hrow⟩ := hTok
      exact frameT_bound S.hW (hT.mono (le_trans haT (Nat.le_add_right _ _))) nrm.nW hrow
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Soundness of the packed frame majorants on truncated memos.** -/
theorem checkFrameMajorantsRJLT_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} {b : FrameBounds} (h : checkFrameMajorantsRJLT bk mm rb tm rm jd c b = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) : FrameMajorants c b ωstar := by
  have S := checkStatic_sound hs
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ
    rwa [S.hrho]
  simp only [checkFrameMajorantsRJLT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hNc⟩, hTc⟩, hOm⟩ := h
  obtain ⟨hNr, hNt⟩ := checkFrameNRT_sound hs hNc
  refine ⟨fun θ hθ j => checkFrameLRT_sound hs hL θ (hstrip θ hθ) j,
    fun θ hθ r => hNr θ (hstrip θ hθ) r, fun θ hθ j => hNt θ (hstrip θ hθ) j,
    fun θ hθ i => checkFrameTRJLT_sound hs hH.1 hE.1 hTc hω θ (hstrip θ hθ) i, ?_⟩
  unfold checkFrameOmega at hOm
  simp only [decide_eq_true_eq] at hOm
  exact (norm_le_freqNormUp hω).trans (by exact_mod_cast hOm)

/-- **Soundness of the packed invariance sub-check on the exact memo.** -/
theorem checkInvarianceJLT_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mf : PGramMemo} {ib : PIBook} {jd : JetData}
    (h : checkInvarianceJLT bk mf ib jd c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := by
  have S := checkStatic_sound hs
  have hKD : ∀ θ ∈ complexStrip n c.weight.rho, c.emb.eval n θ ∈ c.D := by
    intro θ hθ
    rw [S.hrho] at hθ
    exact hE.1 θ hθ (Metric.mem_ball_self S.hμ)
  simp only [checkInvarianceJLT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hent, hP⟩, hjet⟩, hg⟩, hrow⟩ := h
  have g := ivGuard_spec hg
  have hJ := jetFullOkL_sound hs hjet
  have hK := ptK_encloses (tb := ib.toT) S.hW S.hpe c.emb hent hP g.wb g.pK g.nK
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

end Sound

/-! ### The base checker and the engine -/

/-- **The packed base checker on the packed jet, with lifted constants, on truncated memos**: the
Gram, torsion and frame memo `mm` on the small box, the exact invariance memo `mf`. -/
def jetBaseLT (bk : PGramBook) (mm mf : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jl : JetData) (ib : PIBook) (jf : JetData) : BaseChecker where
  check := fun c => checkStatic c && checkHamBounds c && checkEmbedding c &&
    checkGramPackedT (bwT bk c) bk mm c && checkTorsionJLT bk mm rb tm rm jl c &&
    checkInvarianceJLT bk mf ib jf c && checkEnergyJL ib jf c
  sound := by
    intro n α _ _ c h ωstar hω
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hs, hh⟩, he⟩, hg⟩, ht⟩, hi⟩, hen⟩ := h
    have hH := checkHamBounds_sound hs hh
    have hE := checkEmbedding_sound hs he
    obtain ⟨hTu, hTb⟩ := checkTorsionJLT_sound hs hH hE ht hω
    exact ⟨hs, hH, hE, checkGramPackedT_sound hs hg, hTu, hTb,
      checkInvarianceJLT_sound hs hH hE hi hω, checkEnergyJL_sound hs hH hE hen⟩

/-- The test of route A refined with the packed frames on the jet's torsion, with lifted
constants, on truncated memos. -/
def refinedTestPackedJLT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (w : RefinedWit) : Bool :=
  checkHamClaim c w.R && checkFrameMajorantsRJLT bk mm rb tm rm jd c (w.R.frame c.freqBox) &&
    refinedCore n c.params c.freqBox w

/-- **Route A refined with the packed frames on the jet's torsion, on truncated memos.** -/
def routeARefinedPackedJLT (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) : EngineV2 where
  Wit := RefinedWit
  test := fun c w => refinedTestPackedJLT bk mm rb tm rm jd c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestPackedJLT, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    obtain ⟨h1, h2, h3, h4, -⟩ := checkFrameMajorantsRJLT_sound B.hs B.hH B.hEm hF hω
    exact refinedCore_sound c w hω hdio B (checkHamClaim_sound B.hs hH) ⟨h1, h2, h3, h4⟩ hc

/-- **End to end, the packed route on truncated memos**: a certificate passing the v2 certifier
with `jetBaseLT` and `routeARefinedPackedJLT` is a landed `CertifiedTorus`. -/
theorem checkV2With_jetBaseLTPackedJLT_sound {n : ℕ} {α : Type} [CertArith α]
    [LawfulCertArith α] (bk : PGramBook) (mm mf : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jl : JetData) (ib : PIBook) (jf : JetData) {c : TorusCertificate n α}
    {w : RefinedWit}
    (h : checkV2With (jetBaseLT bk mm mf rb tm rm jl ib jf)
      (routeARefinedPackedJLT bk mm rb tm rm jl) c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound _ _ h hω hdio

/-! ### Assembly from parts -/

section Of

variable {α : Type} [CertArith α] {n : ℕ}

/-- The torsion check on truncated memos from its parts. -/
theorem checkTorsionJLT_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jd : JetData} {δβ : α × α} {eps : α}
    (hG : gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hP : rb.P = bk.P) (hjet : jetLowOkL rb jd c = true)
    (hD2 : ptD2AllT n c.emb c.weight c.cfgLow c.piEnc rb.toT tm = true)
    (hcore : torsRCoreJ n (bwT bk c) c.weight c.cfgLow c.freqBox c.params.s c.ham.jet
      (jetSlotsL n jd) rb mm tm rm eps c.torsInv (c.params.σT - c.params.μ) = true) :
    checkTorsionJLT bk mm rb tm rm jd c = true := by
  unfold checkTorsionJLT
  rw [hG]
  dsimp only
  rw [heps]
  dsimp only
  rw [hP, hjet, hD2, hcore]
  simp

/-- The frame majorants on truncated memos from their parts. -/
theorem checkFrameMajorantsRJLT_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jd : JetData} {δβ : α × α} {eps : α}
    {b : FrameBounds}
    (hG : gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hP : rb.P = bk.P) (hjet : jetLowOkL rb jd c = true)
    (hD2 : ptD2AllT n c.emb c.weight c.cfgLow c.piEnc rb.toT tm = true)
    (hlay : trLayOk n rb = true) (hnrm : trNormOk n c.weight c.freqBox c.params.s rb = true)
    (hpk : ptPackOk n (bwT bk c) c.cfgLow rb.toT mm tm = true)
    (hN : trStN n (bwT bk c) c.weight c.cfgLow rb mm rm eps = true)
    (hDL : trStDL (α := α) n c.weight c.freqBox c.params.s rb tm rm = true)
    (hDG : trStDG (α := α) n c.weight rb mm rm = true)
    (hC : trStC n (bwT bk c) c.weight c.cfgLow rb rm eps = true)
    (hDGi : trStDGi n (bwT bk c) c.weight c.cfgLow rb rm eps = true)
    (hDN : trStDN n (bwT bk c) c.weight c.cfgLow rb mm rm eps = true)
    (hXN : trStXNJ n c.ham.jet (jetSlotsL (α := α) n jd) c.weight rb rm = true)
    (hL : trFrameLOk (α := α) n c.weight rb mm b.bL = true)
    (hNok : trFrameNOk (α := α) n rb rm b.bN b.bNt = true)
    (hT : trFrameTOk (α := α) n c.weight rb rm b.bT = true) (hOm : checkFrameOmega c b.bOm = true) :
    checkFrameMajorantsRJLT bk mm rb tm rm jd c b = true := by
  unfold checkFrameMajorantsRJLT checkFrameLRT checkFrameNRT checkFrameTRJLT trTChainOkJ
  rw [hG]
  dsimp only
  rw [heps]
  dsimp only
  rw [hP, hjet, hD2, hlay, hnrm, hpk, hN, hDL, hDG, hC, hDGi, hDN, hXN, hL, hNok, hT, hOm]
  simp

/-- The invariance check on the exact memo from its parts. -/
theorem checkInvarianceJLT_of {c : TorusCertificate n α} {bk : PGramBook} {mf : PGramMemo}
    {ib : PIBook} {jd : JetData}
    (hent : pgEntries n c.emb c.weight c.cfgLow c.piEnc bk mf = true) (hP : ib.P = bk.P)
    (hjet : jetFullOkL ib jd c = true) (hg : ivGuard n c.weight c.freqBox c.params.s ib mf = true)
    (hrow : ∀ a < n + n, ivRowOk n c.weight c.freqBox c.params.s c.ham.jet
      (jetSlotsL (α := α) n jd) ib mf c.params.err a = true) :
    checkInvarianceJLT bk mf ib jd c = true := by
  simp only [checkInvarianceJLT, hent, hP, beq_self_eq_true, hjet, hg, Bool.and_self,
    Bool.true_and, List.all_eq_true, List.mem_range]
  exact hrow

/-- `jetBaseLT` from its parts. -/
theorem jetBaseLT_check_of {bk : PGramBook} {mm mf : PGramMemo} {rb : PRBook} {tm : PTorsMemo}
    {rm : PRMemo} {jl : JetData} {ib : PIBook} {jf : JetData} {c : TorusCertificate n α}
    {δβ : α × α} (hs : checkStatic c = true) (hh : checkHamBounds c = true)
    (he : checkEmbedding c = true)
    (hG : gramPackedCheckT n c.emb (bwT bk c) c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ)
    (ht : checkTorsionJLT bk mm rb tm rm jl c = true)
    (hi : checkInvarianceJLT bk mf ib jf c = true) (hen : checkEnergyJL ib jf c = true) :
    (jetBaseLT bk mm mf rb tm rm jl ib jf).check c = true := by
  have hg : checkGramPackedT (bwT bk c) bk mm c = true := by
    simp only [checkGramPackedT, hG, Option.isSome_some]
  simp only [jetBaseLT, hs, hh, he, hg, ht, hi, hen, Bool.and_self]

/-- The v2 certifier on truncated memos from its two parts. -/
theorem checkV2With_jetBaseLTPackedJLT_of {bk : PGramBook} {mm mf : PGramMemo} {rb : PRBook}
    {tm : PTorsMemo} {rm : PRMemo} {jl : JetData} {ib : PIBook} {jf : JetData}
    {c : TorusCertificate n α} {w : RefinedWit}
    (hb : (jetBaseLT bk mm mf rb tm rm jl ib jf).check c = true)
    (he : refinedTestPackedJLT bk mm rb tm rm jl c w = true) :
    checkV2With (jetBaseLT bk mm mf rb tm rm jl ib jf) (routeARefinedPackedJLT bk mm rb tm rm jl)
      c w = true := by
  simp only [checkV2With, hb, Bool.true_and]
  exact he

end Of

end KAM.CertificateSharp.Packed
