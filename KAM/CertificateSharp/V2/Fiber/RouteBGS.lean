/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBE
public import KAM.CertificateSharp.V2.Fiber.RouteBG
public import KAM.CertificateSharp.V2.SiteSign
import Mathlib.Tactic.Linarith

/-!
# Route B with general sites on a box of the witness, without the torsion majorant

`routeBRefinedLN` and `routeBRefinedE` run the lunar sites of `siteOk` on the certificate's box, so
`clockOk` asks a positive last coordinate and the sites are two-frequency. `routeBRefinedG` runs the
general sites `siteOkG` (three-frequency fibres) but reads the torsion majorant and `y₀ = M s_N`.
This module combines the three, next to the unchanged engines:

* the sites are `siteOkG` (classical, lunar bite or three-frequency fibres), run on a box `bw` of
  the witness that contains the box of `±ω*` (`V2/SiteSign.lean`), reflected if the witness says so;
* the frame check is `checkFrameLN` (no torsion majorant, as `routeBRefinedLN`);
* the energy row reads `y₀ = Mh1 s_N`; `routeBRefinedGSLN` takes `Mh1 = M` (the run of
  `routeBRefinedLN`), `routeBRefinedGSE` the certified `Mh1 = dh` (the run of `routeBRefinedE`).

Both engines go through `iso_g1_branch_E`, whose premise `‖DH‖ ≤ Mh1` on `D` is `BaseFacts` at
`Mh1 = M` and `HamFacts.dh` at `Mh1 = dh`.

* `cert_of_signVec`, `NumBQ.cert_rayGS`: the Fourier certificates on the ray of `ω*` from general
  sites on `bw`;
* `RefinedBWitGS`, `RefinedBWitGS.num`, `refinedBCoreGS`, `refinedBCoreGS_of`,
  `refinedBCoreGS_sound`;
* `refinedBTestGSLN`, `routeBRefinedGSLN`, `refinedBTestGSE`, `routeBRefinedGSE`;
* **never worse**: the image of a witness of `routeBRefinedLN`, `routeBRefinedE` or
  `routeBRefinedG` (with the sign `false` and the certificate's box) has the verdict of that
  engine's core (`refinedBCoreGS_ofLN`, `refinedBCoreGS_ofE`, `refinedBCoreGS_ofG`) and test
  (`refinedBTestGSLN_ofLN`, `refinedBTestGSE_ofE`).
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Iso.Sharp2.RouteB KAM.Iso.Sharp2.RouteBE KAM.Iso.Apost

variable {n : ℕ}

/-! ### The certificates on the ray from sites on a box of the witness -/

/-- **The reflection of the Fourier certificates**: certificates on the ray of `signVec neg ω`
are certificates on the ray of `ω`. -/
theorem cert_of_signVec {N : NumB n} {γ : ℝ} (neg : Bool) {ω : Fin n → ℝ}
    (h : N.Cert γ (ray (signVec neg ω))) : N.Cert γ (ray ω) :=
  ⟨fun s hs => sdConst_ray_of_signVec neg (h.stage s hs),
    fun s hs => sdConst_ray_of_signVec neg (h.split s hs),
    fun s hs => sdConst_ray_of_signVec neg (h.bar s hs),
    fun b hb hle => sdConst_ray_of_signVec neg (h.tail b hb hle),
    fun j hj => sdConst_ray_of_signVec neg (h.tailbar j hj)⟩

namespace NumBQ

variable {Q : NumBQ}

/-- **The certificates on the ray**, from general prefix sites on a box `bw` of the witness that
contains the box of `signVec neg ω*`, and the classical tail. -/
theorem cert_rayGS (hN : (Q.toNum n).Wf) {J : ℕ} {box bw : FreqBox} {κ γ : ℚ} {sites : BSitesG}
    (neg : Bool) (hc : coverOk n (signBox neg box) bw = true)
    (hs : Q.sitesOkG n J bw κ γ sites = true) (ht : Q.tailOk n J = true) (hγ : 0 < γ)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n box ωstar)
    (hdio : IsDiophantine (γ : ℝ) (Q.τ : ℝ) ωstar) : (Q.toNum n).Cert γ (ray ωstar) :=
  cert_of_signVec neg (cert_rayG hN hs ht hγ
    (freqEncloses_of_coverOk hc (freqEncloses_signBox neg hω)) (isDiophantine_signVec neg hdio))

/-- The general sites of the image of lunar sites are the lunar sites. -/
theorem sitesOkG_ofRefined (Q : NumBQ) (J : ℕ) (box : FreqBox) (κ γ : ℚ) (w : RefinedBWit) :
    Q.sitesOkG n J box κ γ (RefinedBWitG.ofRefined w).sites = Q.sitesOk n J box κ γ w.sites := by
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

end NumBQ

/-! ### The witness and the numerical test -/

/-- The witness of route B with general sites on a box of the witness. -/
structure RefinedBWitGS where
  /-- The witness of `routeBRefinedG`; its `κ` is the last coordinate of `bw`. -/
  base : RefinedBWitG
  /-- Whether the sites read `-ω*`. -/
  neg : Bool
  /-- The box of the sites. -/
  bw : FreqBox

/-- The rational numbers of the run with `y₀ = Mh1 s_N`. -/
def RefinedBWitGS.num (ws : RefinedBWitGS) (p : CertParams) (box : FreqBox) (Mh1 : ℚ) : NumBQ :=
  { ws.base.num p box with y0 := Mh1 * ws.base.core.sN }

/-- The numerical test of route B with general sites on `bw`, at `y₀ = Mh1 s_N`. -/
def refinedBCoreGS (n : ℕ) (p : CertParams) (box : FreqBox) (Mh1 : ℚ) (ws : RefinedBWitGS) :
    Bool :=
  let w := ws.base
  let Q := ws.num p box Mh1
  decide (0 < w.core.Xs) && Q.wfOk n && Q.fitsOk w.R.bL w.R.bNt &&
    Q.initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ)
      (p.μ / 2) w.core.Xs &&
    coverOk n (signBox ws.neg box) ws.bw && Q.sitesOkG n w.core.J ws.bw w.κ p.γ w.sites &&
    Q.tailOk n w.core.J && finalB Q n p box w.R.bL w.R.bNt w.core.Xs

/-- Sharding: `refinedBCoreGS` from its parts, each a kernel computation of its own. -/
theorem refinedBCoreGS_of {p : CertParams} {box : FreqBox} {Mh1 : ℚ} {ws : RefinedBWitGS}
    (h0 : 0 < ws.base.core.Xs) (h1 : (ws.num p box Mh1).wfOk n = true)
    (h2 : (ws.num p box Mh1).fitsOk ws.base.R.bL ws.base.R.bNt = true)
    (h3 : (ws.num p box Mh1).initOk ws.base.R.bL ws.base.R.bN ws.base.R.bNt p.σT p.μ = true)
    (h4 : (ws.num p box Mh1).okB n ((ws.num p box Mh1).capBQ p.σT p.μ p.nuRay)
      (NumBQ.initBQ ws.base.R.bL ws.base.R.bN ws.base.R.bNt p.σK p.σB p.μ) (p.μ / 2)
      ws.base.core.Xs = true)
    (hc : coverOk n (signBox ws.neg box) ws.bw = true)
    (h5 : (ws.num p box Mh1).sitesOkG n ws.base.core.J ws.bw ws.base.κ p.γ ws.base.sites = true)
    (h6 : (ws.num p box Mh1).tailOk n ws.base.core.J = true)
    (h7 : finalB (ws.num p box Mh1) n p box ws.base.R.bL ws.base.R.bNt ws.base.core.Xs = true) :
    refinedBCoreGS n p box Mh1 ws = true := by
  simp only [refinedBCoreGS, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, hc⟩, h5⟩, h6⟩, h7⟩

/-- At `Mh1 = M` the numbers are those of `routeBRefinedG`. -/
theorem RefinedBWitGS.num_M (w : RefinedBWitG) (neg : Bool) (bw : FreqBox) (p : CertParams)
    (box : FreqBox) : (⟨w, neg, bw⟩ : RefinedBWitGS).num p box p.M = w.num p box := rfl

/-- At the image of a witness of `routeBRefinedE`, the numbers are those of `routeBRefinedE`. -/
theorem RefinedBWitGS.num_dh (w : RefinedBWit) (neg : Bool) (bw : FreqBox) (p : CertParams)
    (box : FreqBox) :
    (⟨RefinedBWitG.ofRefined w, neg, bw⟩ : RefinedBWitGS).num p box w.R.dh = w.numE p box := rfl

/-- **Never worse than `routeBRefinedG`'s core**, at `Mh1 = M`, the sign `false` and the
certificate's box. -/
theorem refinedBCoreGS_ofG (p : CertParams) (box : FreqBox) (w : RefinedBWitG) :
    refinedBCoreGS n p box p.M ⟨w, false, box⟩ = refinedBCoreG n p box w := by
  simp only [refinedBCoreGS, refinedBCoreG, RefinedBWitGS.num_M, signBox, coverOk_self,
    Bool.and_true, Bool.false_eq_true, ite_false]

/-- **Never worse than `routeBRefinedLN`'s core** (`refinedBCore`). -/
theorem refinedBCoreGS_ofLN (p : CertParams) (box : FreqBox) (w : RefinedBWit) :
    refinedBCoreGS n p box p.M ⟨RefinedBWitG.ofRefined w, false, box⟩ = refinedBCore n p box w :=
  (refinedBCoreGS_ofG p box _).trans (refinedBCoreG_ofRefined n p box w)

/-- **Never worse than `routeBRefinedE`'s core** (`refinedBCoreE`), at `Mh1 = dh`. -/
theorem refinedBCoreGS_ofE (p : CertParams) (box : FreqBox) (w : RefinedBWit) :
    refinedBCoreGS n p box w.R.dh ⟨RefinedBWitG.ofRefined w, false, box⟩ =
      refinedBCoreE n p box w := by
  simp only [refinedBCoreGS, refinedBCoreE, RefinedBWitGS.num_dh, signBox, coverOk_self,
    Bool.and_true, Bool.false_eq_true, ite_false, NumBQ.sitesOkG_ofRefined]
  rfl

/-! ### Soundness -/

variable {α : Type} [CertArith α]

section Sound

variable [LawfulCertArith α]

/-- **Soundness of route B with general sites on a box of the witness**, through
`iso_g1_branch_E` at `Mh1`: the proof of `refinedBCoreE_sound`, with `NumBQ.cert_rayGS` at the
sites. -/
theorem refinedBCoreGS_sound (c : TorusCertificate n α) (ws : RefinedBWitGS) {Mh1 : ℚ}
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c ws.base.R) (hF : FrameFactsLN c ws.base.R)
    (hdH : ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ (Mh1 : ℝ))
    (h : refinedBCoreGS n c.params c.freqBox Mh1 ws = true) : CertifiedTorus c ωstar := by
  obtain ⟨w, neg, bw⟩ := ws
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedBCoreGS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hX, hwf⟩, hfit⟩, hini⟩, hok⟩, hcov⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := (⟨w, neg, bw⟩ : RefinedBWitGS).num c.params c.freqBox Mh1 with hQ
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
    refHypB_ofLN (NumBQ.one_le_n hN) rfl hρ0 rfl rfl
      (by show ((2 * w.R.dx : ℚ) : ℝ) = _; push_cast; ring)
      (by show ((2 * w.R.d2x : ℚ) : ℝ) = _; push_cast; ring) hopen
      (differentiableOn_fderiv_ham hSv) hH hF
  have hCt := NumBQ.cert_rayGS hN neg hcov hsites htail hγq hω hdio
  have hν2' : (c.params.nuRay : ℝ) ≤
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖ - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_E
    (N := Q.toNum n) (M := c.params.M) (Mh1 := Mh1) (σK := c.params.σK) (σB := c.params.σB)
    (σT := c.params.σT) (μ := c.params.μ) (γbar := c.params.γbar)
    (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖) (ν := c.params.nuRay)
    (Xs := w.core.Xs) (I := ⟨w.R.bL, w.R.bN, w.R.bNt⟩) (Ω := ray ωstar)
    hN rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by show ((c.params.σK - c.params.μ / 2 : ℚ) : ℝ) = _; push_cast; ring) hΘ
    (by show ((Mh1 * w.core.sN : ℚ) : ℝ) = _; push_cast; rfl)
    (NumBQ.initOk_sound hini) (NumBQ.fitsOk_sound hfit) hOk hX' hopen htransl hholo hper hreal
    B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hdH hRef hH.d2h
    (fun t ht => ⟨t, ht, rfl⟩) hCt S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

end Sound

/-! ### The engines -/

/-- The test of route B with general sites, at `y₀ = M s_N`, without the torsion majorant. -/
def refinedBTestGSLN (c : TorusCertificate n α) (ws : RefinedBWitGS) : Bool :=
  checkHamClaim c ws.base.R && checkFrameLN c ws.base.R.bL ws.base.R.bN ws.base.R.bNt &&
    refinedBCoreGS n c.params c.freqBox c.params.M ws

/-- **Route B with general sites on a box of the witness, without the torsion majorant.** -/
def routeBRefinedGSLN : EngineV2 where
  Wit := RefinedBWitGS
  test := fun c w => refinedBTestGSLN c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBTestGSLN, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCoreGS_sound c w hω hdio B (checkHamClaim_sound B.hs hH)
      (frameFactsLN_of B.hs hF) (fun z hz => (B.hH.2 z hz).1) hc

/-- The test of route B with general sites, at `y₀ = dh s_N`, without the torsion majorant. -/
def refinedBTestGSE (c : TorusCertificate n α) (ws : RefinedBWitGS) : Bool :=
  checkHamClaim c ws.base.R && checkFrameLN c ws.base.R.bL ws.base.R.bN ws.base.R.bNt &&
    refinedBCoreGS n c.params c.freqBox ws.base.R.dh ws

/-- **Route B with general sites on a box of the witness and the gradient bound in the energy
row.** -/
def routeBRefinedGSE : EngineV2 where
  Wit := RefinedBWitGS
  test := fun c w => refinedBTestGSE c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBTestGSE, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCoreGS_sound c w hω hdio B (checkHamClaim_sound B.hs hH)
      (frameFactsLN_of B.hs hF) (checkHamClaim_sound B.hs hH).dh hc

/-- The unused `bT` does not affect the tests. -/
theorem refinedBTestGSLN_bT (c : TorusCertificate n α) (ws : RefinedBWitGS) (t : ℚ) :
    refinedBTestGSLN c { ws with base := { ws.base with R := { ws.base.R with bT := t } } } =
      refinedBTestGSLN c ws := rfl

theorem refinedBTestGSE_bT (c : TorusCertificate n α) (ws : RefinedBWitGS) (t : ℚ) :
    refinedBTestGSE c { ws with base := { ws.base with R := { ws.base.R with bT := t } } } =
      refinedBTestGSE c ws := rfl

/-- **Never worse than `routeBRefinedLN`**: the image of its witness has the same verdict. -/
theorem refinedBTestGSLN_ofLN (c : TorusCertificate n α) (w : RefinedBWit) :
    refinedBTestGSLN c ⟨RefinedBWitG.ofRefined w, false, c.freqBox⟩ = refinedBLNTest c w := by
  simp only [refinedBTestGSLN, refinedBLNTest, refinedBCoreGS_ofLN]
  rfl

/-- **Never worse than `routeBRefinedE`**: the image of its witness has the same verdict. -/
theorem refinedBTestGSE_ofE (c : TorusCertificate n α) (w : RefinedBWit) :
    refinedBTestGSE c ⟨RefinedBWitG.ofRefined w, false, c.freqBox⟩ = refinedBETest c w := by
  simp only [refinedBTestGSE, refinedBETest]
  rw [show (⟨RefinedBWitG.ofRefined w, false, c.freqBox⟩ : RefinedBWitGS).base.R.dh = w.R.dh
    from rfl, refinedBCoreGS_ofE]
  rfl

/-- The certifier at the image of a witness of `routeBRefinedLN` is the certifier of that engine. -/
theorem checkTorusCertificateV2_routeBRefinedGSLN_ofLN (c : TorusCertificate n α)
    (w : RefinedBWit) :
    checkTorusCertificateV2 routeBRefinedGSLN c ⟨RefinedBWitG.ofRefined w, false, c.freqBox⟩ =
      checkTorusCertificateV2 routeBRefinedLN c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedGSLN, routeBRefinedLN,
    refinedBTestGSLN_ofLN]

/-- The certifier at the image of a witness of `routeBRefinedE` is the certifier of that engine. -/
theorem checkTorusCertificateV2_routeBRefinedGSE_ofE (c : TorusCertificate n α)
    (w : RefinedBWit) :
    checkTorusCertificateV2 routeBRefinedGSE c ⟨RefinedBWitG.ofRefined w, false, c.freqBox⟩ =
      checkTorusCertificateV2 routeBRefinedE c w := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedGSE, routeBRefinedE,
    refinedBTestGSE_ofE]

/-- **Every witness `routeBRefinedG` accepts, `routeBRefinedGSLN` accepts**, at the sign `false`
and the certificate's box. -/
theorem refinedBTestGSLN_of_refinedBTestG (c : TorusCertificate n α) (w : RefinedBWitG)
    (h : refinedBTestG c w = true) : refinedBTestGSLN c ⟨w, false, c.freqBox⟩ = true := by
  simp only [refinedBTestG, refinedBTestGSLN, checkFrameMajorants, checkFrameLN, RefClaim.frame,
    Bool.and_eq_true] at h ⊢
  obtain ⟨⟨hH, ⟨⟨⟨hL, hN⟩, -⟩, -⟩⟩, hc⟩ := h
  exact ⟨⟨hH, hL, hN⟩, (refinedBCoreGS_ofG c.params c.freqBox w).trans hc⟩

/-- Sharding: the whole certifier at `routeBRefinedGSLN` from its parts. -/
theorem checkTorusCertificateV2_routeBRefinedGSLN_of {c : TorusCertificate n α}
    {ws : RefinedBWitGS} (hb : landedBase.check c = true) (hH : checkHamClaim c ws.base.R = true)
    (hF : checkFrameLN c ws.base.R.bL ws.base.R.bN ws.base.R.bNt = true)
    (hc : refinedBCoreGS n c.params c.freqBox c.params.M ws = true) :
    checkTorusCertificateV2 routeBRefinedGSLN c ws = true := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedGSLN, refinedBTestGSLN,
    Bool.and_eq_true]
  exact ⟨hb, ⟨hH, hF⟩, hc⟩

/-- Sharding: the whole certifier at `routeBRefinedGSE` from its parts. -/
theorem checkTorusCertificateV2_routeBRefinedGSE_of {c : TorusCertificate n α}
    {ws : RefinedBWitGS} (hb : landedBase.check c = true) (hH : checkHamClaim c ws.base.R = true)
    (hF : checkFrameLN c ws.base.R.bL ws.base.R.bN ws.base.R.bNt = true)
    (hc : refinedBCoreGS n c.params c.freqBox ws.base.R.dh ws = true) :
    checkTorusCertificateV2 routeBRefinedGSE c ws = true := by
  simp only [checkTorusCertificateV2, checkV2With, routeBRefinedGSE, refinedBTestGSE,
    Bool.and_eq_true]
  exact ⟨hb, ⟨hH, hF⟩, hc⟩

section Sound

variable [LawfulCertArith α]

/-- **Soundness of the certifier at `routeBRefinedGSLN`.** -/
theorem checkTorusCertificateV2_routeBRefinedGSLN_sound {c : TorusCertificate n α}
    {w : RefinedBWitGS} (h : checkTorusCertificateV2 routeBRefinedGSLN c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateV2_sound routeBRefinedGSLN h hω hdio

/-- **Soundness of the certifier at `routeBRefinedGSE`.** -/
theorem checkTorusCertificateV2_routeBRefinedGSE_sound {c : TorusCertificate n α}
    {w : RefinedBWitGS} (h : checkTorusCertificateV2 routeBRefinedGSE c w = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateV2_sound routeBRefinedGSE h hω hdio

end Sound

end KAM.CertificateSharp.V2

end
