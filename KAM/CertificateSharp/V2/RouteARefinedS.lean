/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAll
public import KAM.CertificateSharp.V2.SiteSign

/-!
# Route A at the refined data, with the sites on the witness's box

`refinedCore` runs `sitesOk` on the certificate's box, so `clockOk` asks a positive last coordinate
and `balBound` carries the digits of that box. `routeARefinedS` is `routeARefined` with the sites on
a box of the witness, which contains the certificate's box, reflected if the witness says so
(`V2/SiteSign.lean`). Everything else is the landed test, on the certificate's box: `sitesOk` is
called unchanged.

* `RefinedWitS`, `refinedCoreS`, `refinedCoreS_of`, `refinedCoreS_sound`;
* `refinedCoreS_ofRefined`: a witness of `routeARefined` has an image here with the same verdict;
* `refinedTestS`, `routeARefinedS`, `routeV2AllS`, with `routeV2All` and its witnesses unchanged.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp

/-- The witness of route A with the sites on a box of the witness. -/
structure RefinedWitS where
  /-- The landed witness; its `κ` is the last coordinate of `bw`. -/
  base : RefinedWit
  /-- Whether the sites read `-ω*`. -/
  neg : Bool
  /-- The box of the sites. -/
  bw : FreqBox

/-- The numerical test: `refinedCore`, with the sites on `bw`. -/
def refinedCoreS (n : ℕ) (p : CertParams) (box : FreqBox) (ws : RefinedWitS) : Bool :=
  let w := ws.base
  let Q := w.num n p box
  decide (0 < w.core.Xs) && Q.wfOk &&
    Q.okB (capQ Q p.μ p.nuRay) (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs &&
    coverOk n (signBox ws.neg box) ws.bw && sitesOk Q w.core.J ws.bw w.κ p.γ w.sites &&
    classicalOk n p.tau w.core.J (Q.δ w.core.kp) Q.ctail && finalOkA Q p box w.core.Xs

/-- Sharding: `refinedCoreS` from its parts. -/
theorem refinedCoreS_of {n : ℕ} {p : CertParams} {box : FreqBox} {ws : RefinedWitS}
    (h0 : 0 < ws.base.core.Xs) (h1 : (ws.base.num n p box).wfOk = true)
    (h2 : (ws.base.num n p box).okB (capQ (ws.base.num n p box) p.μ p.nuRay)
      (initQ ws.base.R.bL ws.base.R.bN ws.base.R.bNt ws.base.R.bT p.σK p.σB p.σT p.μ)
      ws.base.core.Xs = true)
    (hc : coverOk n (signBox ws.neg box) ws.bw = true)
    (h3 : sitesOk (ws.base.num n p box) ws.base.core.J ws.bw ws.base.κ p.γ ws.base.sites = true)
    (h4 : classicalOk n p.tau ws.base.core.J ((ws.base.num n p box).δ ws.base.core.kp)
      (ws.base.num n p box).ctail = true)
    (h5 : finalOkA (ws.base.num n p box) p box ws.base.core.Xs = true) :
    refinedCoreS n p box ws = true := by
  simp only [refinedCoreS, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, hc⟩, h3⟩, h4⟩, h5⟩

/-- **Never worse:** a landed witness passes here at its own box. -/
theorem refinedCoreS_ofRefined {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedWit}
    (h : refinedCore n p box w = true) : refinedCoreS n p box ⟨w, false, box⟩ = true := by
  simp only [refinedCore, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact refinedCoreS_of h0 h1 h2 (coverOk_self n box) h3 h4 h5

variable {n : ℕ} {α : Type} [CertArith α]

section Sound

variable [LawfulCertArith α]

/-- **Soundness of stage 2 with the sites on the witness's box**, through `iso_g1_branch_A`:
`refinedCore_sound`, whose only change is the site step. -/
theorem refinedCoreS_sound (c : TorusCertificate n α) (ws : RefinedWitS) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c ws.base.R) (hF : FrameFacts c ws.base.R ωstar)
    (h : refinedCoreS n c.params c.freqBox ws = true) : CertifiedTorus c ωstar := by
  obtain ⟨w, neg, bw⟩ := ws
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedCoreS, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hX, hwf⟩, hok⟩, hcov⟩, hsites⟩, htail⟩, hfin⟩ := h
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
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsites
  have hCert : Q.toNum.Cert (c.params.γ : ℝ) (ray ωstar) := by
    refine NumQ.cert_ray hN S.hγ hdio (fun s hs => ?_) (fun s hs => ?_)
      (cohConstC_le_of_ok (hδq _).le htail)
    · exact sdConst_of_siteOk_sign neg hn1 hτ1 hγq (hδq s) (hδ1 s) hcov (hsites s hs).1 hω hdio
    · have hb := (hN.bbar s hs).1
      rw [NumQ.cast_b] at hb
      exact sdConst_of_siteOk_sign neg hn1 hτ1 hγq (by exact_mod_cast hb) (min_le_right _ _) hcov
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
    (by simp [NumQ.toNum, Q, RefinedWit.num, FrozenWit.num]) hΘ
    (by simp [NumQ.toNum, Q, RefinedWit.num, FrozenWit.num]) hOk hX' hopen htransl hholo hper hreal
    B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hRef
    (fun t ht => ⟨t, ht, rfl⟩) hCert S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

end Sound

/-- The test of route A with the sites on the witness's box. -/
def refinedTestS (c : TorusCertificate n α) (ws : RefinedWitS) : Bool :=
  checkHamClaim c ws.base.R && checkFrameMajorants c (ws.base.R.frame c.freqBox) &&
    refinedCoreS n c.params c.freqBox ws

/-- **The engine of route A with the sites on the witness's box.** -/
def routeARefinedS : EngineV2 where
  Wit := RefinedWitS
  test := fun c w => refinedTestS c w
  sound := by
    intro n α _ _ c w ωstar hω hdio B h
    simp only [refinedTestS, Bool.and_eq_true] at h
    obtain ⟨⟨hH, hF⟩, hc⟩ := h
    exact refinedCoreS_sound c w hω hdio B (checkHamClaim_sound B.hs hH) (frameFacts_of B hF hω) hc

/-- **Soundness of the certifier at `routeARefinedS`.** -/
theorem checkTorusCertificateV2_routeARefinedS_sound [LawfulCertArith α]
    {c : TorusCertificate n α} {w : RefinedWitS}
    (h : checkTorusCertificateV2 routeARefinedS c w = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  checkTorusCertificateV2_sound routeARefinedS h hω hdio

/-- `routeV2All` and route A with the sites on the witness's box. -/
def routeV2AllS : EngineV2 := routeV2All.orElse routeARefinedS

/-- The witnesses of `routeV2All` run unchanged. -/
theorem checkTorusCertificateV2_routeV2AllS_all (c : TorusCertificate n α) (w : routeV2All.Wit) :
    checkTorusCertificateV2 routeV2AllS c (Sum.inl w) = checkTorusCertificateV2 routeV2All c w :=
  rfl

/-- The witness of route A with the sites on the witness's box. -/
theorem checkTorusCertificateV2_routeV2AllS_aS (c : TorusCertificate n α) (w : RefinedWitS) :
    checkTorusCertificateV2 routeV2AllS c (Sum.inr w) =
      checkTorusCertificateV2 routeARefinedS c w := rfl

end KAM.CertificateSharp.V2

end
