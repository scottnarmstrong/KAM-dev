/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteH
public import KAM.CertificateSharp.V2.Fiber.Bulk2Site

/-!
# Route B at the refined data, with extended bulk sites

`routeBRefinedK` is `routeBRefinedG` (`V2/Fiber/RouteBG.lean`) with the three sites of each prefix
stage tested by `siteOkK` (`V2/Fiber/Bulk2Site.lean`): every test of `siteOkH` (landed sites and
bulk sites, `.h`) or the extended bulk test (`.bulk2`). The definitions and the soundness proof
are those of the `G` engine with `sdConst_of_siteOkK` at the sites (copied by script, nothing
else changes).

`RefinedBWitK.ofH` sends a witness of `routeBRefinedH` to one of `routeBRefinedK` with the same
verdict (`refinedBCoreK_ofH`), so the engine is never worse than `routeBRefinedH`. Route A is not
copied: the combined engine of applications is V2-CONSOL's.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteB KAM.Iso.Apost

/-- The tests of the three sites of each prefix stage. -/
abbrev BSitesK := List (SiteWitK × SiteWitK × SiteWitK)

namespace NumBQ

variable (Q : NumBQ) (n : ℕ)

/-- The prefix sites, with general tests. -/
def sitesOkK (J : ℕ) (box : FreqBox) (κ γ : ℚ) (sites : BSitesK) : Bool :=
  (List.range Q.kp).all fun s =>
    siteOkK n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail)
        (sites.getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical))).1 &&
      siteOkK n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
        (sites.getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical))).2.1 &&
      siteOkK n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail)
        (sites.getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical))).2.2

variable {Q n}

/-- Sharding: `sitesOkK` from its stages, each site a kernel computation of its own. -/
theorem sitesOkK_of {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSitesK}
    (h : ∀ s < Q.kp,
      siteOkK n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail)
          (sites.getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical))).1 = true ∧
        siteOkK n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
          (sites.getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical))).2.1 = true ∧
        siteOkK n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail)
          (sites.getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical))).2.2 = true) :
    Q.sitesOkK n J box κ γ sites = true := by
  simp only [sitesOkK, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  exact ⟨⟨h1, h2⟩, h3⟩

/-- **The certificates on the ray**, from the extended prefix sites and the classical tail. -/
theorem cert_rayK (hN : (Q.toNum n).Wf) {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSitesK}
    (hs : Q.sitesOkK n J box κ γ sites = true) (ht : Q.tailOk n J = true) (hγ : 0 < γ)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) (Q.τ : ℝ) ωstar) : (Q.toNum n).Cert γ (ray ωstar) := by
  simp only [sitesOkK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  have hn := one_le_n hN
  have hτ := one_le_τ hN
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hsub : ray ωstar ⊆ {ω | IsDiophantine (γ : ℝ) (Q.τ : ℝ) ω} := by
    rintro ω ⟨t, ht, rfl⟩
    exact isDiophantine_ray hdio ht
  obtain ⟨htail, htbar⟩ := cert_tail hN ht hγ' hsub
  refine ⟨fun s hsk => ?_, fun s hsk => ?_, fun s hsk => ?_, htail, htbar⟩
  · have hf := sched_facts hN s
    rw [cast_δ]
    exact sdConst_of_siteOkK hn hτ hγ hf.1 hf.2.1 (hs s hsk).1.1 hω hdio
  · have hf := sched_facts hN s
    rw [cast_split, cast_δ, ← Rat.cast_mul]
    exact sdConst_of_siteOkK hn hτ hγ hf.2.2.1 hf.2.2.2.1 (hs s hsk).1.2 hω hdio
  · have hf := sched_facts hN s
    rw [cast_bfull]
    exact sdConst_of_siteOkK hn hτ hγ hf.2.2.2.2.1 hf.2.2.2.2.2 (hs s hsk).2 hω hdio

end NumBQ

/-- The witness of route B at the refined data, with extended bulk sites. -/
structure RefinedBWitK where
  /-- The numbers of the run. -/
  core : RunBWit
  /-- The claimed bounds on `H` and the frame. -/
  R : RefClaim
  /-- The last coordinate of the frequency (lunar bites only). -/
  κ : ℚ
  /-- The tests at `δ_s`, at the split bite and at `min r_s 1`, `s < kp`. -/
  sites : BSitesK

/-- The rational numbers of the refined run. -/
def RefinedBWitK.num (w : RefinedBWitK) (p : CertParams) (box : FreqBox) : NumBQ :=
  w.core.num p box w.R.dx w.R.d2x w.R.d2h

/-- The numerical test of route B with extended bulk sites. -/
def refinedBCoreK (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWitK) : Bool :=
  let Q := w.num p box
  decide (0 < w.core.Xs) && Q.wfOk n && Q.fitsOk w.R.bL w.R.bNt &&
    Q.initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ)
      (p.μ / 2) w.core.Xs &&
    Q.sitesOkK n w.core.J box w.κ p.γ w.sites && Q.tailOk n w.core.J &&
    finalB Q n p box w.R.bL w.R.bNt w.core.Xs

/-- Sharding: `refinedBCoreK` from its parts, each a kernel computation of its own. -/
theorem refinedBCoreK_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedBWitK}
    (h0 : 0 < w.core.Xs) (h1 : (w.num p box).wfOk n = true)
    (h2 : (w.num p box).fitsOk w.R.bL w.R.bNt = true)
    (h3 : (w.num p box).initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ = true)
    (h4 : (w.num p box).okB n ((w.num p box).capBQ p.σT p.μ p.nuRay)
      (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ) (p.μ / 2) w.core.Xs = true)
    (h5 : (w.num p box).sitesOkK n w.core.J box w.κ p.γ w.sites = true)
    (h6 : (w.num p box).tailOk n w.core.J = true)
    (h7 : finalB (w.num p box) n p box w.R.bL w.R.bNt w.core.Xs = true) :
    refinedBCoreK n p box w = true := by
  simp only [refinedBCoreK, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- A witness of `routeBRefinedH` as a witness of `routeBRefinedK`. -/
def RefinedBWitK.ofH (w : RefinedBWitH) : RefinedBWitK where
  core := w.core
  R := w.R
  κ := w.κ
  sites := w.sites.map fun o => (SiteWitK.h o.1, SiteWitK.h o.2.1, SiteWitK.h o.2.2)

/-- **The engine is never worse than `routeBRefinedH`**: the image of its witness has the same
verdict. -/
theorem refinedBCoreK_ofH (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWitH) :
    refinedBCoreK n p box (RefinedBWitK.ofH w) = refinedBCoreH n p box w := by
  have hs : ∀ (Q : NumBQ) (J : ℕ) (κ γ : ℚ),
      Q.sitesOkK n J box κ γ (RefinedBWitK.ofH w).sites = Q.sitesOkH n J box κ γ w.sites := by
    intro Q J κ γ
    simp only [NumBQ.sitesOkK, NumBQ.sitesOkH, RefinedBWitK.ofH]
    congr 1
    funext s
    have hg : (w.sites.map fun o => (SiteWitK.h o.1, SiteWitK.h o.2.1,
        SiteWitK.h o.2.2)).getD s (.h (.g .classical), .h (.g .classical), .h (.g .classical)) =
        (SiteWitK.h (w.sites.getD s (.g .classical, .g .classical, .g .classical)).1,
          SiteWitK.h (w.sites.getD s (.g .classical, .g .classical, .g .classical)).2.1,
          SiteWitK.h (w.sites.getD s (.g .classical, .g .classical, .g .classical)).2.2) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
      cases w.sites[s]? <;> rfl
    rw [hg, siteOkK_h, siteOkK_h, siteOkK_h]
  simp only [refinedBCoreK, refinedBCoreH, RefinedBWitK.num, RefinedBWitH.num, hs]
  rfl

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness**, through `iso_g1_branch_B` (the proof of `refinedBCore_sound`, with
`NumBQ.cert_rayK` at the sites). -/
theorem refinedBCoreK_sound (c : TorusCertificate n α) (w : RefinedBWitK) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
    (h : refinedBCoreK n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedBCoreK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hX, hwf⟩, hfit⟩, hini⟩, hok⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := w.num c.params c.freqBox with hQ
  have hN : (Q.toNum n).Wf := NumBQ.wfOk_sound hwf
  have hX' : (0 : ℝ) < w.core.Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hγq : 0 < c.params.γ := by exact_mod_cast S.hγ
  obtain ⟨hsm, hd2, hd3, hroom⟩ := finalB_sound (Q := Q) (iN := w.R.bN) B.hs rfl rfl hX hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hOk := NumBQ.okB_sound hN hok
  rw [← NumBQ.cast_capB, ← NumBQ.cast_initB] at hOk
  have hμ2 : (((c.params.μ / 2 : ℚ)) : ℝ) = (c.params.μ : ℝ) / 2 := by push_cast; ring
  rw [hμ2] at hOk
  have hIS : IsoStanding n (c.params.tau : ℝ) c.params.M c.params.σK c.params.σB c.params.σT
      c.params.σω c.params.nuRay ωstar c.D c.H c.params.γ :=
    { toParams := ⟨S.hn, S.hτ, S.hM, S.hσK, S.hσB, S.hσT⟩
      σω_gt := S.hσω
      ν_pos := S.hν
      ωstar_ne := hω0
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := B.hH.2
      gamma_pos := S.hγ
      dio := hdio }
  have hSv := (hIS.setting S.hs1.le).toStanding
  have hRef : RefHypB (Q.toNum n) ⟨w.R.bL, w.R.bN, w.R.bNt⟩ c.D c.H c.K (Q.toNum n).ρ :=
    refHypB_of (NumBQ.one_le_n hN) rfl hρ0 rfl rfl
      (by show ((2 * w.R.dx : ℚ) : ℝ) = _; push_cast; ring)
      (by show ((2 * w.R.d2x : ℚ) : ℝ) = _; push_cast; ring) hopen
      (differentiableOn_fderiv_ham hSv) hH hF
  have hCt := NumBQ.cert_rayK hN hsites htail hγq hω hdio
  have hν2' : (c.params.nuRay : ℝ) ≤
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖ - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_B
    (N := Q.toNum n) (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB)
    (σT := c.params.σT) (μ := c.params.μ) (γbar := c.params.γbar)
    (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖) (ν := c.params.nuRay)
    (Xs := w.core.Xs) (I := ⟨w.R.bL, w.R.bN, w.R.bNt⟩) (Ω := ray ωstar)
    hN rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by show ((c.params.σK - c.params.μ / 2 : ℚ) : ℝ) = _; push_cast; ring) hΘ
    (by show ((c.params.M * w.core.sN : ℚ) : ℝ) = _; push_cast; rfl)
    (NumBQ.initOk_sound hini) (NumBQ.fitsOk_sound hfit) hOk hX' hopen htransl hholo hper hreal
    B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hRef hH.d2h
    (fun t ht => ⟨t, ht, rfl⟩) hCt S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

/-- The test of the engine. -/
def refinedBTestK (c : TorusCertificate n α) (w : RefinedBWitK) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedBCoreK n c.params c.freqBox w

omit [LawfulCertArith α] in
theorem refinedBTestK_ofH (c : TorusCertificate n α) (w : RefinedBWitH) :
    refinedBTestK c (RefinedBWitK.ofH w) = refinedBTestH c w := by
  simp only [refinedBTestK, refinedBTestH, refinedBCoreK_ofH]
  rfl

/-- **The engine of route B at the refined data, with extended bulk sites.** -/
def routeBRefinedK : EngineV2 where
  Wit := RefinedBWitK
  test := fun c w => refinedBTestK c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBTestK, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCoreK_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω)
      hc

omit [LawfulCertArith α] in
/-- Sharding: the whole certifier at `routeBRefinedK` from the landed sub-checks, the disc pass, the
frame majorants and the numerical core, each a kernel computation of its own. -/
theorem checkTorusCertificateV2_routeBRefinedK_of {c : TorusCertificate n α} {w : RefinedBWitK}
    (hb : landedBase.check c = true) (hH : checkHamClaim c w.R = true)
    (hF : checkFrameMajorants c (w.R.frame c.freqBox) = true)
    (hc : refinedBCoreK n c.params c.freqBox w = true) :
    checkTorusCertificateV2 routeBRefinedK c w = true := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedK, refinedBTestK, Bool.and_eq_true]
  exact ⟨hb, ⟨hH, hF⟩, hc⟩

omit [LawfulCertArith α] in
/-- A witness of `routeBRefinedH` passes the new engine exactly when it passes `routeBRefinedH`. -/
theorem checkTorusCertificateV2_routeBRefinedK_ofH (c : TorusCertificate n α) (w : RefinedBWitH) :
    checkTorusCertificateV2 routeBRefinedK c (RefinedBWitK.ofH w) =
      checkTorusCertificateV2 routeBRefinedH c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedK, routeBRefinedH,
    refinedBTestK_ofH]

end KAM.CertificateSharp.V2

end
