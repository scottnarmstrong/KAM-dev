/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBLN
public import KAM.Iso.Sharp2.RouteBE
import Mathlib.Tactic.Linarith

/-!
# Route B at the refined data, with the certified gradient bound in the energy row

`RunBWit.num` sets `y₀ = M s_N`, with the one-size `M` of the certificate, and `refinedBCore` reads
those numbers. Route A's refined run uses the certified `dh` here (`HY = dh s_N`). This module gives
route B the same, next to the unchanged `routeBRefined` and `routeBRefinedLN`:

* `RunBWit.numE`, `RefinedBWit.numE`: the numbers of the run with `y₀ = Mh1 s_N`;
* `refinedBCoreE`, `refinedBCoreE_of`: the numerical test at those numbers, and its sharding;
* `refinedBCoreE_sound`: through `iso_g1_branch_E`, with `Mh1 = R.dh`;
* `refinedBETest`, `routeBRefinedE`: the test and the engine, at the same witness `RefinedBWit`.

**The claim `Mh1`** is the field `dh` of the witness's `RefClaim`. `checkHamClaim` checks it against
the disc pass (`HamFacts.dh`), so an understated claim is rejected by the check that already runs,
and no new pass is needed. As in `routeBRefinedLN`, the unused `bT` is not read.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteB
  KAM.Iso.Sharp2.RouteB KAM.Iso.Sharp2.RouteBE KAM.Iso.Apost

variable {n : ℕ} {α : Type} [CertArith α]

/-- The rational numbers of the run with `y₀ = Mh1 s_N`. -/
def RunBWit.numE (w : RunBWit) (p : CertParams) (box : FreqBox) (M1 M2 Mh2 Mh1 : ℚ) : NumBQ :=
  { w.num p box M1 M2 Mh2 with y0 := Mh1 * w.sN }

/-- The rational numbers of the refined run, with `Mh1 = dh`. -/
def RefinedBWit.numE (w : RefinedBWit) (p : CertParams) (box : FreqBox) : NumBQ :=
  w.core.numE p box w.R.dx w.R.d2x w.R.d2h w.R.dh

/-- The numerical test of route B at the refined data, with `y₀ = dh s_N`. -/
def refinedBCoreE (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWit) : Bool :=
  let Q := w.numE p box
  decide (0 < w.core.Xs) && Q.wfOk n && Q.fitsOk w.R.bL w.R.bNt &&
    Q.initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ)
      (p.μ / 2) w.core.Xs &&
    Q.sitesOk n w.core.J box w.κ p.γ w.sites && Q.tailOk n w.core.J &&
    finalB Q n p box w.R.bL w.R.bNt w.core.Xs

/-- Sharding: `refinedBCoreE` from its parts, each a kernel computation of its own. -/
theorem refinedBCoreE_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedBWit}
    (h0 : 0 < w.core.Xs) (h1 : (w.numE p box).wfOk n = true)
    (h2 : (w.numE p box).fitsOk w.R.bL w.R.bNt = true)
    (h3 : (w.numE p box).initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ = true)
    (h4 : (w.numE p box).okB n ((w.numE p box).capBQ p.σT p.μ p.nuRay)
      (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ) (p.μ / 2) w.core.Xs = true)
    (h5 : (w.numE p box).sitesOk n w.core.J box w.κ p.γ w.sites = true)
    (h6 : (w.numE p box).tailOk n w.core.J = true)
    (h7 : finalB (w.numE p box) n p box w.R.bL w.R.bNt w.core.Xs = true) :
    refinedBCoreE n p box w = true := by
  simp only [refinedBCoreE, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

/-- **Soundness of route B at the refined data, with `y₀ = dh s_N`**, through `iso_g1_branch_E`. -/
theorem refinedBCoreE_sound [LawfulCertArith α] (c : TorusCertificate n α) (w : RefinedBWit)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFactsLN c w.R)
    (h : refinedBCoreE n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedBCoreE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hX, hwf⟩, hfit⟩, hini⟩, hok⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := w.numE c.params c.freqBox with hQ
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
  have hCt := NumBQ.cert_ray hN hsites htail hγq hω hdio
  have hν2' : (c.params.nuRay : ℝ) ≤
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖ - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := iso_g1_branch_E
    (N := Q.toNum n) (M := c.params.M) (Mh1 := w.R.dh) (σK := c.params.σK) (σB := c.params.σB)
    (σT := c.params.σT) (μ := c.params.μ) (γbar := c.params.γbar)
    (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖) (ν := c.params.nuRay)
    (Xs := w.core.Xs) (I := ⟨w.R.bL, w.R.bN, w.R.bNt⟩) (Ω := ray ωstar)
    hN rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by show ((c.params.σK - c.params.μ / 2 : ℚ) : ℝ) = _; push_cast; ring) hΘ
    (by show ((w.R.dh * w.core.sN : ℚ) : ℝ) = _; push_cast; rfl)
    (NumBQ.initOk_sound hini) (NumBQ.fitsOk_sound hfit) hOk hX' hopen htransl hholo hper hreal
    B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hH.dh hRef hH.d2h
    (fun t ht => ⟨t, ht, rfl⟩) hCt S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

/-- The test of route B at the refined data, with `y₀ = dh s_N`, without the torsion majorant. -/
def refinedBETest (c : TorusCertificate n α) (w : RefinedBWit) : Bool :=
  checkHamClaim c w.R && checkFrameLN c w.R.bL w.R.bN w.R.bNt &&
    refinedBCoreE n c.params c.freqBox w

/-- The unused `bT` does not affect the test. -/
theorem refinedBETest_bT (c : TorusCertificate n α) (w : RefinedBWit) (t : ℚ) :
    refinedBETest c { w with R := { w.R with bT := t } } = refinedBETest c w := rfl

/-- **The engine of route B at the refined data, with the gradient bound in the energy row.** -/
def routeBRefinedE : EngineV2 where
  Wit := RefinedBWit
  test := fun c w => refinedBETest c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedBETest, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedBCoreE_sound c w hω hdio B (checkHamClaim_sound B.hs hH)
      (frameFactsLN_of B.hs hF) hc

/-- **Soundness of the certifier at `routeBRefinedE`.** -/
theorem checkTorusCertificateV2_routeBRefinedE_sound [LawfulCertArith α]
    {c : TorusCertificate n α} {w : RefinedBWit}
    (h : checkTorusCertificateV2 routeBRefinedE c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateV2_sound routeBRefinedE h hω hdio

end KAM.CertificateSharp.V2

end
