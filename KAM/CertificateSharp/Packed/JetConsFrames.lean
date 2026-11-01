/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetConsTorsSound
public import KAM.CertificateSharp.Packed.Frames

/-!
# Packed frame majorants on the jet's torsion, and the packed route-A-refined engine on it

`checkFrameMajorantsR` (`Frames.lean`) reads B3b's torsion objects; its `sup |T|` test
(`checkFrameTR`) re-runs the landed `cfgLow` composition for `DX_H ∘ K`. Here:

* `|Lᵀ|`, `|N|`, `|Nᵀ|` and `|ω*|` are the landed packed tests **verbatim** (`checkFrameLR`,
  `checkFrameNR`, `checkFrameOmega`): they read only the Gram memo, the guards, the packing and the
  node `N`, which are conjuncts of `checkTorsionJ` too;
* `sup |T|` (`checkFrameTRJ`) reads the packed `T` whose `X_N` stage takes `DX_H ∘ K` from the jet
  (`trTChainOkJ`); its conjuncts are those of `checkTorsionJ` (the packed Gram check, `jetLowOk`,
  `ptD2All`, the guards and stages of `torsRCoreJ`) plus the frame test `trFrameTOk`;
* `checkFrameMajorantsRJ_sound`: the conclusion of the landed `checkFrameMajorants_sound`
  (`FrameMajorants`); `checkFrameMajorantsRJ_of` assembles the check from the shared parts (each
  established once, for the torsion and the frames);
* `routeARefinedPackedJ`: route A refined with these frames; `checkV2With_packedJ_sound` gives the
  landed `CertifiedTorus` for any base checker (`jetBase`, `JetBase.lean`).
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Torus KAM.Certificate KAM.Certificate.CertArith KAM.CertificateSharp
  KAM.CertificateSharp.V2
open scoped Matrix Matrix.Norms.Operator

section Checks

variable {n : ℕ} {α : Type} [CertArith α]

/-- **Packed `sup |T| ≤ bT` on the jet's torsion.** -/
def checkFrameTRJ (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo) (rm : PRMemo)
    (jd : JetData) (c : TorusCertificate n α) (bT : ℚ) : Bool :=
  match gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) with
  | some δβ =>
    match gramInvRadius δβ with
    | some eps =>
      rb.P == bk.P && jetLowOk rb jd c && ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm &&
        trTChainOkJ n c.gramInv c.weight c.cfgLow c.freqBox c.params.s c.ham.jet (jetSlots jd) rb
          mm tm rm eps &&
        trFrameTOk (α := α) n c.weight rb rm bT
    | none => false
  | none => false

/-- **The packed frame majorants on the jet's torsion.** -/
def checkFrameMajorantsRJ (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) (c : TorusCertificate n α) (b : FrameBounds) : Bool :=
  checkFrameLR bk mm rb tm c b.bL && checkFrameNR bk mm rb tm rm c b.bN b.bNt &&
    checkFrameTRJ bk mm rb tm rm jd c b.bT && checkFrameOmega c b.bOm

end Checks

section Sound

variable {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}

/-- **The packed torsion block on the jet's boundary** from the stage checks. -/
theorem trT_chainJ {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (Binv : List (List (CertPoly α))) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) {bk : PGramBook} {mm : PGramMemo} {σBμ : ℚ} {δβ : α × α}
    (hn : 1 ≤ n) (hG : gramPackedCheck n K Binv W cfg pe bk mm σBμ = some δβ) {eps : α}
    (heps : gramInvRadius δβ = some eps) {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {js : JSlots α} (hJ : JSlotsEnc rb.Lb rb.bA rb.P js n W.rho e.jet.prog K (torsionSlots n e.jet))
    (hP : rb.P = bk.P) (hD2 : ptD2All n K W cfg pe rb.toT tm = true) {box : FreqBox} {s : ℚ}
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω)
    (hch : trTChainOkJ n Binv W cfg box s e.jet js rb mm tm rm eps = true) :
    PMat.Encloses rb.Lw (rb.aT n) (2 * rb.P) n W.rho Fin.val Fin.val (trT (α := α) n rb rm)
      (fun θ => Matrix.of fun i j =>
        KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ (Sum.inl i) (Sum.inl j)) := by
  obtain ⟨-, hGs⟩ := gramPackedCheck_sound hn K Binv hW cfg hpe bk mm σBμ hG
  have hGu : ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det :=
    fun θ hθ => (hGs θ hθ).1
  simp only [trTChainOkJ, Bool.and_eq_true] at hch
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hlay, hnrm⟩, hpk⟩, hN⟩, hDL⟩, hDG⟩, hC⟩, hDGi⟩, hDN⟩, hXN⟩ := hch
  have lay := trLayOk_spec hlay
  have nrm := trNormOk_spec hnrm
  have pk := ptPackOk_spec hpk
  have eD2 : ∀ r < n + n, ∀ j < n, ∀ l < n, ptD2Ok n K W cfg pe rb.toT tm r j l = true := by
    simpa only [ptD2All, List.all_eq_true, List.mem_range] using hD2
  have hK := ptK_encloses (tb := rb.toT) hW hpe K (pgEntries_of_check hG) hP lay.wb pk.pK nrm.nK
  have hB := ptB_encloses (tb := rb.toT) (eps := eps) hW lay.wb pk.pB nrm.nB fun θ hθ =>
    ((hGs θ hθ).2.2).trans (gramInvRadius_spec heps)
  have hD2m := ptD2_encloses (tb := rb.toT) hW hpe K lay.wb eD2 pk.pD nrm.nD
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

/-- The packed `sup |T|` bound on the jet's torsion. -/
theorem checkFrameTRJ_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D)
    (hE : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} {bT : ℚ} (h : checkFrameTRJ bk mm rb tm rm jd c bT = true)
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
  unfold checkFrameTRJ at h
  split at h
  · rename_i δβ hG
    split at h
    · rename_i eps heps
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hP, hjet⟩, hD2⟩, hch⟩, hTok⟩ := h
      have hT := trT_chainJ (isOpen_certDomain _ _ _ _) hH S.hW hKD c.gramInv c.cfgLow S.hpe hn
        hG heps (jetLowOk_sound hs hjet) hP hD2 hω hch
      have nrm := trNormOk_spec (by simp only [trTChainOkJ, Bool.and_eq_true] at hch; tauto)
      simp only [trFrameTOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at hTok
      obtain ⟨haT, hrow⟩ := hTok
      exact frameT_bound S.hW (hT.mono (le_trans haT (Nat.le_add_right _ _))) nrm.nW hrow
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Soundness of the packed frame majorants on the jet's torsion**: the conclusion of the landed
`checkFrameMajorants_sound`, under its hypotheses. -/
theorem checkFrameMajorantsRJ_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hH : c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M)
    (hE : (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ)
    {bk : PGramBook} {mm : PGramMemo} {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo}
    {jd : JetData} {b : FrameBounds} (h : checkFrameMajorantsRJ bk mm rb tm rm jd c b = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) : FrameMajorants c b ωstar := by
  have S := checkStatic_sound hs
  have hstrip : ∀ θ ∈ complexStrip n c.params.rho, θ ∈ complexStrip n c.weight.rho := by
    intro θ hθ
    rwa [S.hrho]
  simp only [checkFrameMajorantsRJ, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hL, hNc⟩, hTc⟩, hOm⟩ := h
  obtain ⟨hNr, hNt⟩ := checkFrameNR_sound hs hNc
  refine ⟨fun θ hθ j => checkFrameLR_sound hs hL θ (hstrip θ hθ) j,
    fun θ hθ r => hNr θ (hstrip θ hθ) r, fun θ hθ j => hNt θ (hstrip θ hθ) j,
    fun θ hθ i => checkFrameTRJ_sound hs hH.1 hE.1 hTc hω θ (hstrip θ hθ) i, ?_⟩
  unfold checkFrameOmega at hOm
  simp only [decide_eq_true_eq] at hOm
  exact (norm_le_freqNormUp hω).trans (by exact_mod_cast hOm)

omit [LawfulCertArith α] in
/-- The packed frame majorants on the jet's torsion from their parts: the facts shared with
`checkTorsionJ` (the Gram check, the jet chain, the `D²K` boundary, the guards, the stages) and the
four frame tests (each shared fact established once). -/
theorem checkFrameMajorantsRJ_of {c : TorusCertificate n α} {bk : PGramBook} {mm : PGramMemo}
    {rb : PRBook} {tm : PTorsMemo} {rm : PRMemo} {jd : JetData} {δβ : α × α} {eps : α}
    {b : FrameBounds}
    (hG : gramPackedCheck n c.emb c.gramInv c.weight c.cfgLow c.piEnc bk mm
      (c.params.σB - c.params.μ) = some δβ) (heps : gramInvRadius δβ = some eps)
    (hP : rb.P = bk.P) (hjet : jetLowOk rb jd c = true)
    (hD2 : ptD2All n c.emb c.weight c.cfgLow c.piEnc rb.toT tm = true)
    (hlay : trLayOk n rb = true) (hnrm : trNormOk n c.weight c.freqBox c.params.s rb = true)
    (hpk : ptPackOk n c.gramInv c.cfgLow rb.toT mm tm = true)
    (hN : trStN n c.gramInv c.weight c.cfgLow rb mm rm eps = true)
    (hDL : trStDL (α := α) n c.weight c.freqBox c.params.s rb tm rm = true)
    (hDG : trStDG (α := α) n c.weight rb mm rm = true)
    (hC : trStC n c.gramInv c.weight c.cfgLow rb rm eps = true)
    (hDGi : trStDGi n c.gramInv c.weight c.cfgLow rb rm eps = true)
    (hDN : trStDN n c.gramInv c.weight c.cfgLow rb mm rm eps = true)
    (hXN : trStXNJ n c.ham.jet (jetSlots (α := α) jd) c.weight rb rm = true)
    (hL : trFrameLOk (α := α) n c.weight rb mm b.bL = true)
    (hNok : trFrameNOk (α := α) n rb rm b.bN b.bNt = true)
    (hT : trFrameTOk (α := α) n c.weight rb rm b.bT = true) (hOm : checkFrameOmega c b.bOm = true) :
    checkFrameMajorantsRJ bk mm rb tm rm jd c b = true := by
  unfold checkFrameMajorantsRJ checkFrameLR checkFrameNR checkFrameTRJ trTChainOkJ
  rw [hG]
  dsimp only
  rw [heps]
  dsimp only
  rw [hP, hjet, hD2, hlay, hnrm, hpk, hN, hDL, hDG, hC, hDGi, hDN, hXN, hL, hNok, hT, hOm]
  simp

end Sound

/-! ### The engine -/

/-- The test of route A refined with the packed frames on the jet's torsion. -/
def refinedTestPackedJ (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α)
    (w : RefinedWit) : Bool :=
  checkHamClaim c w.R && checkFrameMajorantsRJ bk mm rb tm rm jd c (w.R.frame c.freqBox) &&
    refinedCore n c.params c.freqBox w

/-- **Route A refined with the packed frames on the jet's torsion** (the landed disc pass and
refined core). -/
def routeARefinedPackedJ (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) : EngineV2 where
  Wit := RefinedWit
  test := fun c w => refinedTestPackedJ bk mm rb tm rm jd c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestPackedJ, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    obtain ⟨h1, h2, h3, h4, -⟩ := checkFrameMajorantsRJ_sound B.hs B.hH B.hEm hF hω
    exact refinedCore_sound c w hω hdio B (checkHamClaim_sound B.hs hH) ⟨h1, h2, h3, h4⟩ hc

/-- **End to end** for any base checker: a certificate passing the v2 certifier with route A
refined on the packed frames of the jet's torsion is a landed `CertifiedTorus`. -/
theorem checkV2With_packedJ_sound {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (B : BaseChecker) (bk : PGramBook) (mm : PGramMemo) (rb : PRBook) (tm : PTorsMemo)
    (rm : PRMemo) (jd : JetData) {c : TorusCertificate n α} {w : RefinedWit}
    (h : checkV2With B (routeARefinedPackedJ bk mm rb tm rm jd) c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkV2With_sound B (routeARefinedPackedJ bk mm rb tm rm jd) h hω hdio

end KAM.CertificateSharp.Packed
