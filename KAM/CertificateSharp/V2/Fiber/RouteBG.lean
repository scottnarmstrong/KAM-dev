/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBEngine
public import KAM.CertificateSharp.V2.Fiber.RouteAG

/-!
# Route B at the refined data, with three-frequency sites

`routeBRefinedG` is `routeBRefined` (`V2/RouteBEngine.lean`) with the three sites of each prefix
stage (`δ_s`, the split bite, `min r_s 1`) tested by `siteOkG` instead of `siteOk`. Route B
consumes the sites only through `NumBQ.cert_ray`; `NumBQ.cert_rayG` is that theorem with
`sdConst_of_siteOkG`, and `refinedBCoreG_sound` is `refinedBCore_sound` with `cert_rayG`.

`RefinedBWitG.ofRefined` sends a witness of `routeBRefined` to one of `routeBRefinedG` with the same
verdict (`refinedBCoreG_ofRefined`). `routeV2G` chains route A (`routeAV2G`) and both forms of
route B with general sites.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteB KAM.Iso.Apost

/-- The tests of the three sites of each prefix stage. -/
abbrev BSitesG := List (SiteWitG × SiteWitG × SiteWitG)

namespace NumBQ

variable (Q : NumBQ) (n : ℕ)

/-- The prefix sites, with general tests. -/
def sitesOkG (J : ℕ) (box : FreqBox) (κ γ : ℚ) (sites : BSitesG) : Bool :=
  (List.range Q.kp).all fun s =>
    siteOkG n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail)
        (sites.getD s (.classical, .classical, .classical)).1 &&
      siteOkG n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
        (sites.getD s (.classical, .classical, .classical)).2.1 &&
      siteOkG n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail)
        (sites.getD s (.classical, .classical, .classical)).2.2

variable {Q n}

/-- **The certificates on the ray**, from the general prefix sites and the classical tail. -/
theorem cert_rayG (hN : (Q.toNum n).Wf) {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSitesG}
    (hs : Q.sitesOkG n J box κ γ sites = true) (ht : Q.tailOk n J = true) (hγ : 0 < γ)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) (Q.τ : ℝ) ωstar) : (Q.toNum n).Cert γ (ray ωstar) := by
  simp only [sitesOkG, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
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
    exact sdConst_of_siteOkG hn hτ hγ hf.1 hf.2.1 (hs s hsk).1.1 hω hdio
  · have hf := sched_facts hN s
    rw [cast_split, cast_δ, ← Rat.cast_mul]
    exact sdConst_of_siteOkG hn hτ hγ hf.2.2.1 hf.2.2.2.1 (hs s hsk).1.2 hω hdio
  · have hf := sched_facts hN s
    rw [cast_bfull]
    exact sdConst_of_siteOkG hn hτ hγ hf.2.2.2.2.1 hf.2.2.2.2.2 (hs s hsk).2 hω hdio

end NumBQ

/-- The witness of route B at the refined data, with general sites. -/
structure RefinedBWitG where
  /-- The numbers of the run. -/
  core : RunBWit
  /-- The claimed bounds on `H` and the frame. -/
  R : RefClaim
  /-- The last coordinate of the frequency (lunar bites only). -/
  κ : ℚ
  /-- The tests at `δ_s`, at the split bite and at `min r_s 1`, `s < kp`. -/
  sites : BSitesG

/-- The rational numbers of the refined run. -/
def RefinedBWitG.num (w : RefinedBWitG) (p : CertParams) (box : FreqBox) : NumBQ :=
  w.core.num p box w.R.dx w.R.d2x w.R.d2h

/-- The numerical test of route B with general sites. -/
def refinedBCoreG (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWitG) : Bool :=
  let Q := w.num p box
  decide (0 < w.core.Xs) && Q.wfOk n && Q.fitsOk w.R.bL w.R.bNt &&
    Q.initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ)
      (p.μ / 2) w.core.Xs &&
    Q.sitesOkG n w.core.J box w.κ p.γ w.sites && Q.tailOk n w.core.J &&
    finalB Q n p box w.R.bL w.R.bNt w.core.Xs

/-- A witness of `routeBRefined` as a witness of `routeBRefinedG`. -/
def RefinedBWitG.ofRefined (w : RefinedBWit) : RefinedBWitG where
  core := w.core
  R := w.R
  κ := w.κ
  sites := w.sites.map fun o =>
    (SiteWitG.ofOption o.1, SiteWitG.ofOption o.2.1, SiteWitG.ofOption o.2.2)

/-- **The new engine is never worse**: the image of a witness of `routeBRefined` has the same
verdict. -/
theorem refinedBCoreG_ofRefined (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWit) :
    refinedBCoreG n p box (RefinedBWitG.ofRefined w) = refinedBCore n p box w := by
  have hs : ∀ (Q : NumBQ) (J : ℕ) (κ γ : ℚ),
      Q.sitesOkG n J box κ γ (RefinedBWitG.ofRefined w).sites = Q.sitesOk n J box κ γ w.sites := by
    intro Q J κ γ
    simp only [NumBQ.sitesOkG, NumBQ.sitesOk, RefinedBWitG.ofRefined]
    congr 1
    funext s
    have hg : (w.sites.map fun o => (SiteWitG.ofOption o.1, SiteWitG.ofOption o.2.1,
        SiteWitG.ofOption o.2.2)).getD s (.classical, .classical, .classical) =
        (SiteWitG.ofOption (w.sites.getD s (none, none, none)).1,
          SiteWitG.ofOption (w.sites.getD s (none, none, none)).2.1,
          SiteWitG.ofOption (w.sites.getD s (none, none, none)).2.2) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
      cases w.sites[s]? <;> rfl
    rw [hg, siteOkG_ofOption, siteOkG_ofOption, siteOkG_ofOption]
  simp only [refinedBCoreG, refinedBCore, RefinedBWitG.num, RefinedBWit.num, hs]
  rfl

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness**, through `iso_g1_branch_B` (the proof of `refinedBCore_sound`, with
`NumBQ.cert_rayG` at the sites). -/
theorem refinedBCoreG_sound (c : TorusCertificate n α) (w : RefinedBWitG) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
    (h : refinedBCoreG n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedBCoreG, Bool.and_eq_true, decide_eq_true_eq] at h
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
  have hCt := NumBQ.cert_rayG hN hsites htail hγq hω hdio
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
def refinedBTestG (c : TorusCertificate n α) (w : RefinedBWitG) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedBCoreG n c.params c.freqBox w

omit [LawfulCertArith α] in
theorem refinedBTestG_ofRefined (c : TorusCertificate n α) (w : RefinedBWit) :
    refinedBTestG c (RefinedBWitG.ofRefined w) = refinedBTest c w := by
  simp only [refinedBTestG, refinedBTest, refinedBCoreG_ofRefined]
  rfl

/-- **The engine of route B at the refined data, with three-frequency sites.** -/
def routeBRefinedG : EngineV2 where
  Wit := RefinedBWitG
  test := fun c w => refinedBTestG c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBTestG, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCoreG_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω)
      hc

/-- The minimum over route A (`routeAV2G`) and route B (frozen, refined with general sites). -/
def routeV2G : EngineV2 := routeAV2G.orElse (routeBFrozen.orElse routeBRefinedG)

omit [LawfulCertArith α] in
/-- **v2 is never worse than the landed certifier**, at the combined engine. -/
theorem checkTorusCertificateV2_routeV2G_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeV2G c (Sum.inl (Sum.inl (Sum.inl ()))) =
      checkTorusCertificateSharp c :=
  rfl

omit [LawfulCertArith α] in
/-- A refined route-B witness passes the new engine exactly when it passes `routeBRefined`. -/
theorem checkTorusCertificateV2_routeBRefinedG_ofRefined (c : TorusCertificate n α)
    (w : RefinedBWit) :
    checkTorusCertificateV2 routeBRefinedG c (RefinedBWitG.ofRefined w) =
      checkTorusCertificateV2 routeBRefined c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedG, routeBRefined,
    refinedBTestG_ofRefined]

end KAM.CertificateSharp.V2

end
