/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.RouteBG
public import KAM.CertificateSharp.V2.Fiber.BulkSite

/-!
# Routes A and B at the refined data, with bulk sites

`routeARefinedH` and `routeBRefinedH` are `routeARefinedG` and `routeBRefinedG`
(`V2/Fiber/RouteAG.lean`, `V2/Fiber/RouteBG.lean`) with the sites tested by `siteOkH`
(`V2/Fiber/BulkSite.lean`): every landed site test (`.g`), or the bulk test (`.bulk`, `n = 3`,
`Fiber/Bulk.lean`). The definitions and the soundness proofs are those of the `G` engines with
`sdConst_of_siteOkH` at the sites; nothing else changes.

`RefinedWitH.ofG` and `RefinedBWitH.ofG` send a witness of the `G` engine to one of the `H` engine
with the same verdict (`refinedCoreH_ofG`, `refinedBCoreH_ofG`), so the new engines are never
worse. `routeV2H` adds both to `routeV2G`; at the witness of the landed sharp engine it is the
landed certifier (`checkTorusCertificateV2_routeV2H_sharp`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2

/-! ### Route A -/

section RouteA

open KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp

/-- The witness of route A at the refined data, with bulk sites. -/
structure RefinedWitH where
  /-- `X⋆`, the schedule, the constants and the caps. -/
  core : FrozenWit
  /-- The claimed bounds on `H` and the frame. -/
  R : RefClaim
  /-- The last coordinate of the frequency (lunar bites only). -/
  κ : ℚ
  /-- The tests at `δ_s` and at `b_s`, `s < kp`. -/
  sites : List (SiteWitH × SiteWitH)

/-- The rational numbers of the refined run. -/
def RefinedWitH.num (w : RefinedWitH) (n : ℕ) (p : CertParams) (box : FreqBox) : NumQ :=
  { w.core.num n p box with
    M1 := w.R.dx, M2 := w.R.d2x, HY := w.R.dh * w.core.sN, Mh2 := w.R.d2h }

/-- The sites of the prefix. -/
def sitesOkH (Q : NumQ) (J : ℕ) (box : FreqBox) (κ γ : ℚ) (sites : List (SiteWitH × SiteWitH)) :
    Bool :=
  (List.range Q.kp).all fun s =>
    siteOkH Q.n Q.τ J box κ γ (Q.δ s) (Q.c.getD s 0)
        (sites.getD s (.g .classical, .g .classical)).1 &&
      siteOkH Q.n Q.τ J box κ γ (Q.b s) (Q.cbar.getD s 0)
        (sites.getD s (.g .classical, .g .classical)).2

/-- The numerical test. -/
def refinedCoreH (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedWitH) : Bool :=
  let Q := w.num n p box
  decide (0 < w.core.Xs) && Q.wfOk &&
    Q.okB (capQ Q p.μ p.nuRay) (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs &&
    sitesOkH Q w.core.J box w.κ p.γ w.sites &&
    classicalOk n p.tau w.core.J (Q.δ w.core.kp) Q.ctail && finalOkA Q p box w.core.Xs

/-- Sharding: `sitesOkH` from its sites, each a kernel computation of its own. -/
theorem sitesOkH_of {Q : NumQ} {J : ℕ} {box : FreqBox} {κ γ : ℚ}
    {sites : List (SiteWitH × SiteWitH)}
    (h : ∀ s < Q.kp, siteOkH Q.n Q.τ J box κ γ (Q.δ s) (Q.c.getD s 0)
        (sites.getD s (.g .classical, .g .classical)).1 = true ∧
      siteOkH Q.n Q.τ J box κ γ (Q.b s) (Q.cbar.getD s 0)
        (sites.getD s (.g .classical, .g .classical)).2 = true) :
    sitesOkH Q J box κ γ sites = true := by
  simp only [sitesOkH, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact h

/-- Sharding: `refinedCoreH` from its parts. -/
theorem refinedCoreH_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedWitH}
    (h0 : 0 < w.core.Xs) (h1 : (w.num n p box).wfOk = true)
    (h2 : (w.num n p box).okB (capQ (w.num n p box) p.μ p.nuRay)
      (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs = true)
    (h3 : sitesOkH (w.num n p box) w.core.J box w.κ p.γ w.sites = true)
    (h4 : classicalOk n p.tau w.core.J ((w.num n p box).δ w.core.kp) (w.num n p box).ctail = true)
    (h5 : finalOkA (w.num n p box) p box w.core.Xs = true) :
    refinedCoreH n p box w = true := by
  simp only [refinedCoreH, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

/-- A witness of `routeARefinedG` as a witness of `routeARefinedH`. -/
def RefinedWitH.ofG (w : RefinedWitG) : RefinedWitH where
  core := w.core
  R := w.R
  κ := w.κ
  sites := w.sites.map fun o => (SiteWitH.g o.1, SiteWitH.g o.2)

/-- **The new engine is never worse**: the image of a witness of `routeARefinedG` has the same
verdict. -/
theorem refinedCoreH_ofG (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedWitG) :
    refinedCoreH n p box (RefinedWitH.ofG w) = refinedCoreG n p box w := by
  have hs : ∀ (Q : NumQ) (J : ℕ) (κ γ : ℚ),
      sitesOkH Q J box κ γ ((RefinedWitH.ofG w).sites) = sitesOkG Q J box κ γ w.sites := by
    intro Q J κ γ
    simp only [sitesOkH, sitesOkG, RefinedWitH.ofG]
    congr 1
    funext s
    have hg : (w.sites.map fun o => (SiteWitH.g o.1, SiteWitH.g o.2)).getD s
        (.g .classical, .g .classical) =
        (SiteWitH.g (w.sites.getD s (.classical, .classical)).1,
          SiteWitH.g (w.sites.getD s (.classical, .classical)).2) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
      cases w.sites[s]? <;> rfl
    rw [hg, siteOkH_g, siteOkH_g]
  simp only [refinedCoreH, refinedCoreG, RefinedWitH.num, RefinedWitG.num, hs]
  rfl

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness**, through `iso_g1_branch_A` (the proof of `refinedCore_sound`, with
`sdConst_of_siteOkH` at the sites). -/
theorem refinedCoreH_sound (c : TorusCertificate n α) (w : RefinedWitH) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
    (h : refinedCoreH n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedCoreH, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hX, hwf⟩, hok⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := w.num n c.params c.freqBox with hQ
  have hN : Q.toNum.Wf := NumQ.wfOk_sound hwf
  have hτ1 : 1 ≤ Q.τ := by
    have h : (1 : ℝ) ≤ (Q.τ : ℝ) := hN.τ_ge
    exact_mod_cast h
  have hX' : (0 : ℝ) < w.core.Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hγq : 0 < c.params.γ := by exact_mod_cast S.hγ
  obtain ⟨hsm, hd2, hd3, hroom⟩ := finalOkA_sound (Q := Q) B.hs rfl rfl rfl hτ1 hX hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hOk := NumQ.okB_sound hτ1 hok
  rw [← cast_capQ, ← cast_initQ] at hOk
  have hRef : RefHypIA Q.toNum w.R.init w.R.dh c.D c.H c.K ((c.params.s : ℝ) • ωstar) :=
    refHyp_of (N := Q.toNum) (by have := hN.two_le; omega) rfl (hN.δ_pos 0).le hρ0 rfl rfl rfl hH hF
  have hn1 : 1 ≤ n := by have := S.hn; omega
  have hδq : ∀ s, 0 < Q.δ s := fun s => by
    have := hN.δ_pos s
    rw [NumQ.cast_δ] at this
    exact_mod_cast this
  have hδ1 : ∀ s, Q.δ s ≤ 1 := fun s => by
    have := hN.δ_le s
    rw [NumQ.cast_δ] at this
    exact_mod_cast this
  simp only [sitesOkH, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsites
  have hCert : Q.toNum.Cert (c.params.γ : ℝ) (ray ωstar) := by
    refine NumQ.cert_ray hN S.hγ hdio (fun s hs => ?_) (fun s hs => ?_)
      (cohConstC_le_of_ok (hδq _).le htail)
    · exact sdConst_of_siteOkH hn1 hτ1 hγq (hδq s) (hδ1 s) (hsites s hs).1 hω hdio
    · have hb := (hN.bbar s hs).1
      rw [NumQ.cast_b] at hb
      exact sdConst_of_siteOkH hn1 hτ1 hγq (by exact_mod_cast hb) (min_le_right _ _)
        (hsites s hs).2 hω hdio
  have hν2' : (c.params.nuRay : ℝ) ≤
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖ - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_A
    (N := Q.toNum) (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT)
    (μ := c.params.μ)
    (γbar := c.params.γbar) (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖)
    (ν := c.params.nuRay) (Xs := w.core.Xs) (Mh1 := w.R.dh) (I := w.R.init) (Ω := ray ωstar)
    hN rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by simp [NumQ.toNum, Q, RefinedWitH.num, FrozenWit.num]) hΘ
    (by simp [NumQ.toNum, Q, RefinedWitH.num, FrozenWit.num]) hOk hX' hopen htransl hholo hper
    hreal B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hRef
    (fun t ht => ⟨t, ht, rfl⟩) hCert S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

/-- The test of the engine. -/
def refinedTestH (c : TorusCertificate n α) (w : RefinedWitH) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedCoreH n c.params c.freqBox w

omit [LawfulCertArith α] in
theorem refinedTestH_ofG (c : TorusCertificate n α) (w : RefinedWitG) :
    refinedTestH c (RefinedWitH.ofG w) = refinedTestG c w := by
  simp only [refinedTestH, refinedTestG, refinedCoreH_ofG]
  rfl

/-- **The engine of route A at the refined data, with bulk sites.** -/
def routeARefinedH : EngineV2 where
  Wit := RefinedWitH
  test := fun c w => refinedTestH c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestH, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedCoreH_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω) hc

omit [LawfulCertArith α] in
/-- Sharding: the whole certifier at `routeARefinedH` from the landed sub-checks, the disc pass, the
frame majorants and the numerical core, each a kernel computation of its own. -/
theorem checkTorusCertificateV2_routeARefinedH_of {c : TorusCertificate n α} {w : RefinedWitH}
    (hb : landedBase.check c = true) (hH : checkHamClaim c w.R = true)
    (hF : checkFrameMajorants c (w.R.frame c.freqBox) = true)
    (hc : refinedCoreH n c.params c.freqBox w = true) :
    checkTorusCertificateV2 routeARefinedH c w = true := by
  simp only [checkTorusCertificateV2, checkV2With, routeARefinedH, refinedTestH, Bool.and_eq_true]
  exact ⟨hb, ⟨hH, hF⟩, hc⟩

omit [LawfulCertArith α] in
/-- A witness of `routeARefinedG` passes the new engine exactly when it passes `routeARefinedG`. -/
theorem checkTorusCertificateV2_routeARefinedH_ofG (c : TorusCertificate n α) (w : RefinedWitG) :
    checkTorusCertificateV2 routeARefinedH c (RefinedWitH.ofG w) =
      checkTorusCertificateV2 routeARefinedG c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeARefinedH, routeARefinedG,
    refinedTestH_ofG]

end RouteA

/-! ### Route B -/

section RouteB

open KAM.Apost KAM.Sharp2.RouteB KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteB KAM.Iso.Apost

/-- The tests of the three sites of each prefix stage. -/
abbrev BSitesH := List (SiteWitH × SiteWitH × SiteWitH)

namespace NumBQ

variable (Q : NumBQ) (n : ℕ)

/-- The prefix sites, with general tests. -/
def sitesOkH (J : ℕ) (box : FreqBox) (κ γ : ℚ) (sites : BSitesH) : Bool :=
  (List.range Q.kp).all fun s =>
    siteOkH n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail)
        (sites.getD s (.g .classical, .g .classical, .g .classical)).1 &&
      siteOkH n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
        (sites.getD s (.g .classical, .g .classical, .g .classical)).2.1 &&
      siteOkH n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail)
        (sites.getD s (.g .classical, .g .classical, .g .classical)).2.2

variable {Q n}

/-- Sharding: `sitesOkH` from its stages, each site a kernel computation of its own. -/
theorem sitesOkH_of {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSitesH}
    (h : ∀ s < Q.kp,
      siteOkH n Q.τ J box κ γ (Q.δ s) (Q.c.getD s Q.ctail)
          (sites.getD s (.g .classical, .g .classical, .g .classical)).1 = true ∧
        siteOkH n Q.τ J box κ γ (Q.split * Q.δ s) (Q.c'.getD s Q.ctail)
          (sites.getD s (.g .classical, .g .classical, .g .classical)).2.1 = true ∧
        siteOkH n Q.τ J box κ γ (Q.bfull s) (Q.cbar.getD s Q.cbtail)
          (sites.getD s (.g .classical, .g .classical, .g .classical)).2.2 = true) :
    Q.sitesOkH n J box κ γ sites = true := by
  simp only [sitesOkH, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  exact ⟨⟨h1, h2⟩, h3⟩

/-- **The certificates on the ray**, from the general prefix sites and the classical tail. -/
theorem cert_rayH (hN : (Q.toNum n).Wf) {J : ℕ} {box : FreqBox} {κ γ : ℚ} {sites : BSitesH}
    (hs : Q.sitesOkH n J box κ γ sites = true) (ht : Q.tailOk n J = true) (hγ : 0 < γ)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) (Q.τ : ℝ) ωstar) : (Q.toNum n).Cert γ (ray ωstar) := by
  simp only [sitesOkH, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
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
    exact sdConst_of_siteOkH hn hτ hγ hf.1 hf.2.1 (hs s hsk).1.1 hω hdio
  · have hf := sched_facts hN s
    rw [cast_split, cast_δ, ← Rat.cast_mul]
    exact sdConst_of_siteOkH hn hτ hγ hf.2.2.1 hf.2.2.2.1 (hs s hsk).1.2 hω hdio
  · have hf := sched_facts hN s
    rw [cast_bfull]
    exact sdConst_of_siteOkH hn hτ hγ hf.2.2.2.2.1 hf.2.2.2.2.2 (hs s hsk).2 hω hdio

end NumBQ

/-- The witness of route B at the refined data, with bulk sites. -/
structure RefinedBWitH where
  /-- The numbers of the run. -/
  core : RunBWit
  /-- The claimed bounds on `H` and the frame. -/
  R : RefClaim
  /-- The last coordinate of the frequency (lunar bites only). -/
  κ : ℚ
  /-- The tests at `δ_s`, at the split bite and at `min r_s 1`, `s < kp`. -/
  sites : BSitesH

/-- The rational numbers of the refined run. -/
def RefinedBWitH.num (w : RefinedBWitH) (p : CertParams) (box : FreqBox) : NumBQ :=
  w.core.num p box w.R.dx w.R.d2x w.R.d2h

/-- The numerical test of route B with bulk sites. -/
def refinedBCoreH (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWitH) : Bool :=
  let Q := w.num p box
  decide (0 < w.core.Xs) && Q.wfOk n && Q.fitsOk w.R.bL w.R.bNt &&
    Q.initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ)
      (p.μ / 2) w.core.Xs &&
    Q.sitesOkH n w.core.J box w.κ p.γ w.sites && Q.tailOk n w.core.J &&
    finalB Q n p box w.R.bL w.R.bNt w.core.Xs

/-- Sharding: `refinedBCoreH` from its parts, each a kernel computation of its own. -/
theorem refinedBCoreH_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedBWitH}
    (h0 : 0 < w.core.Xs) (h1 : (w.num p box).wfOk n = true)
    (h2 : (w.num p box).fitsOk w.R.bL w.R.bNt = true)
    (h3 : (w.num p box).initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ = true)
    (h4 : (w.num p box).okB n ((w.num p box).capBQ p.σT p.μ p.nuRay)
      (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ) (p.μ / 2) w.core.Xs = true)
    (h5 : (w.num p box).sitesOkH n w.core.J box w.κ p.γ w.sites = true)
    (h6 : (w.num p box).tailOk n w.core.J = true)
    (h7 : finalB (w.num p box) n p box w.R.bL w.R.bNt w.core.Xs = true) :
    refinedBCoreH n p box w = true := by
  simp only [refinedBCoreH, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- A witness of `routeBRefinedG` as a witness of `routeBRefinedH`. -/
def RefinedBWitH.ofG (w : RefinedBWitG) : RefinedBWitH where
  core := w.core
  R := w.R
  κ := w.κ
  sites := w.sites.map fun o => (SiteWitH.g o.1, SiteWitH.g o.2.1, SiteWitH.g o.2.2)

/-- **The new engine is never worse**: the image of a witness of `routeBRefinedG` has the same
verdict. -/
theorem refinedBCoreH_ofG (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWitG) :
    refinedBCoreH n p box (RefinedBWitH.ofG w) = refinedBCoreG n p box w := by
  have hs : ∀ (Q : NumBQ) (J : ℕ) (κ γ : ℚ),
      Q.sitesOkH n J box κ γ (RefinedBWitH.ofG w).sites = Q.sitesOkG n J box κ γ w.sites := by
    intro Q J κ γ
    simp only [NumBQ.sitesOkH, NumBQ.sitesOkG, RefinedBWitH.ofG]
    congr 1
    funext s
    have hg : (w.sites.map fun o => (SiteWitH.g o.1, SiteWitH.g o.2.1,
        SiteWitH.g o.2.2)).getD s (.g .classical, .g .classical, .g .classical) =
        (SiteWitH.g (w.sites.getD s (.classical, .classical, .classical)).1,
          SiteWitH.g (w.sites.getD s (.classical, .classical, .classical)).2.1,
          SiteWitH.g (w.sites.getD s (.classical, .classical, .classical)).2.2) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
      cases w.sites[s]? <;> rfl
    rw [hg, siteOkH_g, siteOkH_g, siteOkH_g]
  simp only [refinedBCoreH, refinedBCoreG, RefinedBWitH.num, RefinedBWitG.num, hs]
  rfl

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness**, through `iso_g1_branch_B` (the proof of `refinedBCore_sound`, with
`NumBQ.cert_rayH` at the sites). -/
theorem refinedBCoreH_sound (c : TorusCertificate n α) (w : RefinedBWitH) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
    (h : refinedBCoreH n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedBCoreH, Bool.and_eq_true, decide_eq_true_eq] at h
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
  have hCt := NumBQ.cert_rayH hN hsites htail hγq hω hdio
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
def refinedBTestH (c : TorusCertificate n α) (w : RefinedBWitH) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedBCoreH n c.params c.freqBox w

omit [LawfulCertArith α] in
theorem refinedBTestH_ofG (c : TorusCertificate n α) (w : RefinedBWitG) :
    refinedBTestH c (RefinedBWitH.ofG w) = refinedBTestG c w := by
  simp only [refinedBTestH, refinedBTestG, refinedBCoreH_ofG]
  rfl

/-- **The engine of route B at the refined data, with bulk sites.** -/
def routeBRefinedH : EngineV2 where
  Wit := RefinedBWitH
  test := fun c w => refinedBTestH c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBTestH, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCoreH_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω)
      hc

omit [LawfulCertArith α] in
/-- Sharding: the whole certifier at `routeBRefinedH` from the landed sub-checks, the disc pass, the
frame majorants and the numerical core, each a kernel computation of its own. -/
theorem checkTorusCertificateV2_routeBRefinedH_of {c : TorusCertificate n α} {w : RefinedBWitH}
    (hb : landedBase.check c = true) (hH : checkHamClaim c w.R = true)
    (hF : checkFrameMajorants c (w.R.frame c.freqBox) = true)
    (hc : refinedBCoreH n c.params c.freqBox w = true) :
    checkTorusCertificateV2 routeBRefinedH c w = true := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedH, refinedBTestH, Bool.and_eq_true]
  exact ⟨hb, ⟨hH, hF⟩, hc⟩

omit [LawfulCertArith α] in
/-- A witness of `routeBRefinedG` passes the new engine exactly when it passes `routeBRefinedG`. -/
theorem checkTorusCertificateV2_routeBRefinedH_ofG (c : TorusCertificate n α) (w : RefinedBWitG) :
    checkTorusCertificateV2 routeBRefinedH c (RefinedBWitH.ofG w) =
      checkTorusCertificateV2 routeBRefinedG c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedH, routeBRefinedG,
    refinedBTestH_ofG]

end RouteB

/-! ### The combined engine -/

/-- `routeV2G` and both refined routes with bulk sites. -/
def routeV2H : EngineV2 := routeV2G.orElse (routeARefinedH.orElse routeBRefinedH)

section Combined

variable {n : ℕ} {α : Type} [CertArith α]

/-- **v2 is never worse than the landed certifier**, at the combined engine. -/
theorem checkTorusCertificateV2_routeV2H_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeV2H c (Sum.inl (Sum.inl (Sum.inl (Sum.inl ())))) =
      checkTorusCertificateSharp c :=
  rfl

/-- Every witness of `routeV2G` is a witness of `routeV2H`, with the same verdict. -/
theorem checkTorusCertificateV2_routeV2H_ofG (c : TorusCertificate n α) (w : routeV2G.Wit) :
    checkTorusCertificateV2 routeV2H c (Sum.inl w) = checkTorusCertificateV2 routeV2G c w :=
  rfl

/-- A witness of `routeARefinedH` at the combined engine. -/
theorem checkTorusCertificateV2_routeV2H_A (c : TorusCertificate n α) (w : RefinedWitH) :
    checkTorusCertificateV2 routeV2H c (Sum.inr (Sum.inl w)) =
      checkTorusCertificateV2 routeARefinedH c w :=
  rfl

/-- A witness of `routeBRefinedH` at the combined engine. -/
theorem checkTorusCertificateV2_routeV2H_B (c : TorusCertificate n α) (w : RefinedBWitH) :
    checkTorusCertificateV2 routeV2H c (Sum.inr (Sum.inr w)) =
      checkTorusCertificateV2 routeBRefinedH c w :=
  rfl

end Combined

end KAM.CertificateSharp.V2

end
