/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefinedEngine
public import KAM.CertificateSharp.V2.Fiber.Site3

/-!
# Route A at the refined data, with three-frequency sites

`routeARefinedG` is `routeARefined` (`V2/RouteARefinedEngine.lean`) with the sites of the schedule
tested by `siteOkG` (`V2/Fiber/Site3.lean`) instead of `siteOk`: classical, the lunar bite
(`n = 2`, `τ = 1`), or the fibered test (`n = 3`, any `τ`). The rest of the test (`NumQ.Wf`,
`okB`, the classical tail, `finalOkA`, the disc pass and the frame majorants) is unchanged, and so
is the soundness argument (`iso_g1_branch_A`): the sites enter only through
`NumQ.cert_ray`, whose hypotheses are the `SDConst … (ray ω*)` that `sdConst_of_siteOkG` gives.

`RefinedWitG.ofRefined` sends a witness of `routeARefined` to one of `routeARefinedG` with the same
verdict (`refinedCoreG_ofRefined`), so the new engine is never worse.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp

/-- The witness of route A at the refined data, with general sites. -/
structure RefinedWitG where
  /-- `X⋆`, the schedule, the constants and the caps. -/
  core : FrozenWit
  /-- The claimed bounds on `H` and the frame. -/
  R : RefClaim
  /-- The last coordinate of the frequency (lunar bites only). -/
  κ : ℚ
  /-- The tests at `δ_s` and at `b_s`, `s < kp`. -/
  sites : List (SiteWitG × SiteWitG)

/-- The rational numbers of the refined run. -/
def RefinedWitG.num (w : RefinedWitG) (n : ℕ) (p : CertParams) (box : FreqBox) : NumQ :=
  { w.core.num n p box with
    M1 := w.R.dx, M2 := w.R.d2x, HY := w.R.dh * w.core.sN, Mh2 := w.R.d2h }

/-- The sites of the prefix. -/
def sitesOkG (Q : NumQ) (J : ℕ) (box : FreqBox) (κ γ : ℚ) (sites : List (SiteWitG × SiteWitG)) :
    Bool :=
  (List.range Q.kp).all fun s =>
    siteOkG Q.n Q.τ J box κ γ (Q.δ s) (Q.c.getD s 0)
        (sites.getD s (.classical, .classical)).1 &&
      siteOkG Q.n Q.τ J box κ γ (Q.b s) (Q.cbar.getD s 0)
        (sites.getD s (.classical, .classical)).2

/-- The numerical test. -/
def refinedCoreG (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedWitG) : Bool :=
  let Q := w.num n p box
  decide (0 < w.core.Xs) && Q.wfOk &&
    Q.okB (capQ Q p.μ p.nuRay) (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs &&
    sitesOkG Q w.core.J box w.κ p.γ w.sites &&
    classicalOk n p.tau w.core.J (Q.δ w.core.kp) Q.ctail && finalOkA Q p box w.core.Xs

/-- Sharding: `sitesOkG` from its sites, each a kernel computation of its own. -/
theorem sitesOkG_of {Q : NumQ} {J : ℕ} {box : FreqBox} {κ γ : ℚ}
    {sites : List (SiteWitG × SiteWitG)}
    (h : ∀ s < Q.kp, siteOkG Q.n Q.τ J box κ γ (Q.δ s) (Q.c.getD s 0)
        (sites.getD s (.classical, .classical)).1 = true ∧
      siteOkG Q.n Q.τ J box κ γ (Q.b s) (Q.cbar.getD s 0)
        (sites.getD s (.classical, .classical)).2 = true) :
    sitesOkG Q J box κ γ sites = true := by
  simp only [sitesOkG, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact h

/-- Sharding: `refinedCoreG` from its parts. -/
theorem refinedCoreG_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedWitG}
    (h0 : 0 < w.core.Xs) (h1 : (w.num n p box).wfOk = true)
    (h2 : (w.num n p box).okB (capQ (w.num n p box) p.μ p.nuRay)
      (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs = true)
    (h3 : sitesOkG (w.num n p box) w.core.J box w.κ p.γ w.sites = true)
    (h4 : classicalOk n p.tau w.core.J ((w.num n p box).δ w.core.kp) (w.num n p box).ctail = true)
    (h5 : finalOkA (w.num n p box) p box w.core.Xs = true) :
    refinedCoreG n p box w = true := by
  simp only [refinedCoreG, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

/-- A witness of `routeARefined` as a witness of `routeARefinedG`. -/
def SiteWitG.ofOption : Option BiteWit → SiteWitG
  | none => .classical
  | some w => .bite w

/-- A witness of `routeARefined` as a witness of `routeARefinedG`. -/
def RefinedWitG.ofRefined (w : RefinedWit) : RefinedWitG where
  core := w.core
  R := w.R
  κ := w.κ
  sites := w.sites.map fun o => (SiteWitG.ofOption o.1, SiteWitG.ofOption o.2)

theorem siteOkG_ofOption (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) (o : Option BiteWit) :
    siteOkG n τ J box κ γ b c (SiteWitG.ofOption o) = siteOk n τ J box κ γ b c o := by
  cases o <;> rfl

/-- **The new engine is never worse**: the image of a witness of `routeARefined` has the same
verdict. -/
theorem refinedCoreG_ofRefined (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedWit) :
    refinedCoreG n p box (RefinedWitG.ofRefined w) = refinedCore n p box w := by
  have hs : ∀ (Q : NumQ) (J : ℕ) (κ γ : ℚ),
      sitesOkG Q J box κ γ ((RefinedWitG.ofRefined w).sites) = sitesOk Q J box κ γ w.sites := by
    intro Q J κ γ
    simp only [sitesOkG, sitesOk, RefinedWitG.ofRefined]
    congr 1
    funext s
    have e : ∀ o : Option BiteWit × Option BiteWit,
        ((fun o : Option BiteWit × Option BiteWit =>
          (SiteWitG.ofOption o.1, SiteWitG.ofOption o.2)) o) =
          (SiteWitG.ofOption o.1, SiteWitG.ofOption o.2) := fun _ => rfl
    have hg : (w.sites.map fun o => (SiteWitG.ofOption o.1, SiteWitG.ofOption o.2)).getD s
        (.classical, .classical) =
        (SiteWitG.ofOption (w.sites.getD s (none, none)).1,
          SiteWitG.ofOption (w.sites.getD s (none, none)).2) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
      cases w.sites[s]? <;> rfl
    rw [hg, siteOkG_ofOption, siteOkG_ofOption]
  simp only [refinedCoreG, refinedCore, RefinedWitG.num, RefinedWit.num, hs]
  rfl

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness**, through `iso_g1_branch_A` (the proof of `refinedCore_sound`, with
`sdConst_of_siteOkG` at the sites). -/
theorem refinedCoreG_sound (c : TorusCertificate n α) (w : RefinedWitG) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
    (h : refinedCoreG n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedCoreG, Bool.and_eq_true, decide_eq_true_eq] at h
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
  simp only [sitesOkG, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsites
  have hCert : Q.toNum.Cert (c.params.γ : ℝ) (ray ωstar) := by
    refine NumQ.cert_ray hN S.hγ hdio (fun s hs => ?_) (fun s hs => ?_)
      (cohConstC_le_of_ok (hδq _).le htail)
    · exact sdConst_of_siteOkG hn1 hτ1 hγq (hδq s) (hδ1 s) (hsites s hs).1 hω hdio
    · have hb := (hN.bbar s hs).1
      rw [NumQ.cast_b] at hb
      exact sdConst_of_siteOkG hn1 hτ1 hγq (by exact_mod_cast hb) (min_le_right _ _)
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
    (by simp [NumQ.toNum, Q, RefinedWitG.num, FrozenWit.num]) hΘ
    (by simp [NumQ.toNum, Q, RefinedWitG.num, FrozenWit.num]) hOk hX' hopen htransl hholo hper
    hreal B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hRef
    (fun t ht => ⟨t, ht, rfl⟩) hCert S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

/-- The test of the engine. -/
def refinedTestG (c : TorusCertificate n α) (w : RefinedWitG) : Bool :=
  checkHamClaim c w.R && checkFrameMajorants c (w.R.frame c.freqBox) &&
    refinedCoreG n c.params c.freqBox w

omit [LawfulCertArith α] in
theorem refinedTestG_ofRefined (c : TorusCertificate n α) (w : RefinedWit) :
    refinedTestG c (RefinedWitG.ofRefined w) = refinedTest c w := by
  simp only [refinedTestG, refinedTest, refinedCoreG_ofRefined]
  rfl

/-- **The engine of route A at the refined data, with three-frequency sites.** -/
def routeARefinedG : EngineV2 where
  Wit := RefinedWitG
  test := fun c w => refinedTestG c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestG, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedCoreG_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω) hc

/-- The minimum over the landed sharp engine, route A (frozen, refined) and route A with
three-frequency sites. -/
def routeAV2G : EngineV2 := routeAV2.orElse routeARefinedG

omit [LawfulCertArith α] in
/-- **v2 is never worse than the landed certifier**, at the combined engine. -/
theorem checkTorusCertificateV2_routeAV2G_sharp (c : TorusCertificate n α) :
    checkTorusCertificateV2 routeAV2G c (Sum.inl (Sum.inl ())) = checkTorusCertificateSharp c :=
  rfl

omit [LawfulCertArith α] in
/-- A refined witness passes the new engine exactly when it passes `routeARefined`. -/
theorem checkTorusCertificateV2_routeARefinedG_ofRefined (c : TorusCertificate n α)
    (w : RefinedWit) :
    checkTorusCertificateV2 routeARefinedG c (RefinedWitG.ofRefined w) =
      checkTorusCertificateV2 routeARefined c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeARefinedG, routeARefined,
    refinedTestG_ofRefined]

end KAM.CertificateSharp.V2

end
