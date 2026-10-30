/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAFrozen
public import KAM.CertificateSharp.V2.RefinedFacts
public import KAM.CertificateSharp.V2.SmallDivQ

/-!
# Stage 2: route A at the refined data

`refinedCore` is the numerical part of the test of the route-A branch
`KAM.Iso.Sharp2.RouteA.iso_g1_branch_A`: `NumA.Wf`, `routeAOkI` with `M₁, M₂, HY, Mh2` and the
initial values of the claim `RefClaim`, the small-divisor constants of the schedule (`sitesOk`,
certified or classical per site), and `finalOkA`.

The test takes the branch and not the wrapper `iso_g1_v2A`, whose displacement constants are
`max {C₂♯, c2I}`, `max {C₃♯, c3I}`. `C₂♯` is v1's constant at the frozen data: near a refined
threshold it dominates `c2I` and leaves a useless displacement. On the design package R1 at
`e = 4.7·10⁻¹²`, `C₂♯ e/(γ²ρ²) ≈ 7`, above the room `(σω - s)|ω*| ≈ 1.75` of the ray.

`refinedCore_sound` concludes `CertifiedTorus` from `BaseFacts`, `HamFacts`, `FrameFacts` and the
test. `HamFacts`, `FrameFacts` are statements on the objects of the certificate, with no smallness:
`V2/RouteARefinedEngine.lean` proves them by checks, and this split also lets a certificate prove
them in modules of their own (the cosh pass of `V2/HamTrig.lean` cannot share a module with the
frame majorants).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp

/-- The witness of stage 2. -/
structure RefinedWit where
  /-- `X⋆`, the schedule, the constants and the caps. -/
  core : FrozenWit
  /-- The claimed bounds on `H` and the frame. -/
  R : RefClaim
  /-- The last coordinate of the frequency. -/
  κ : ℚ
  /-- The witnesses at `δ_s` and at `b_s`, `s < kp`: certified, or classical if `none`. -/
  sites : List (Option BiteWit × Option BiteWit)

/-- The rational numbers of the refined run. -/
def RefinedWit.num (w : RefinedWit) (n : ℕ) (p : CertParams) (box : FreqBox) : NumQ :=
  { w.core.num n p box with
    M1 := w.R.dx, M2 := w.R.d2x, HY := w.R.dh * w.core.sN, Mh2 := w.R.d2h }

/-- The sites of the prefix. -/
def sitesOk (Q : NumQ) (J : ℕ) (box : FreqBox) (κ γ : ℚ)
    (sites : List (Option BiteWit × Option BiteWit)) : Bool :=
  (List.range Q.kp).all fun s =>
    siteOk Q.n Q.τ J box κ γ (Q.δ s) (Q.c.getD s 0) (sites.getD s (none, none)).1 &&
      siteOk Q.n Q.τ J box κ γ (Q.b s) (Q.cbar.getD s 0) (sites.getD s (none, none)).2

/-- The numerical test of stage 2. -/
def refinedCore (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedWit) : Bool :=
  let Q := w.num n p box
  decide (0 < w.core.Xs) && Q.wfOk &&
    Q.okB (capQ Q p.μ p.nuRay) (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs &&
    sitesOk Q w.core.J box w.κ p.γ w.sites &&
    classicalOk n p.tau w.core.J (Q.δ w.core.kp) Q.ctail && finalOkA Q p box w.core.Xs

/-- Sharding: `sitesOk` from its sites, each a kernel computation of its own. -/
theorem sitesOk_of {Q : NumQ} {J : ℕ} {box : FreqBox} {κ γ : ℚ}
    {sites : List (Option BiteWit × Option BiteWit)}
    (h : ∀ s < Q.kp, siteOk Q.n Q.τ J box κ γ (Q.δ s) (Q.c.getD s 0)
        (sites.getD s (none, none)).1 = true ∧
      siteOk Q.n Q.τ J box κ γ (Q.b s) (Q.cbar.getD s 0) (sites.getD s (none, none)).2 = true) :
    sitesOk Q J box κ γ sites = true := by
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact h

/-- Sharding: `refinedCore` from its parts. -/
theorem refinedCore_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedWit}
    (h0 : 0 < w.core.Xs) (h1 : (w.num n p box).wfOk = true)
    (h2 : (w.num n p box).okB (capQ (w.num n p box) p.μ p.nuRay)
      (initQ w.R.bL w.R.bN w.R.bNt w.R.bT p.σK p.σB p.σT p.μ) w.core.Xs = true)
    (h3 : sitesOk (w.num n p box) w.core.J box w.κ p.γ w.sites = true)
    (h4 : classicalOk n p.tau w.core.J ((w.num n p box).δ w.core.kp) (w.num n p box).ctail = true)
    (h5 : finalOkA (w.num n p box) p box w.core.Xs = true) :
    refinedCore n p box w = true := by
  simp only [refinedCore, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness of stage 2**, through `iso_g1_branch_A`. The refined facts are statements on the
objects of `c`, proved by checks; see the module docstring. -/
theorem refinedCore_sound (c : TorusCertificate n α) (w : RefinedWit) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R) (hF : FrameFacts c w.R ωstar)
    (h : refinedCore n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedCore, Bool.and_eq_true, decide_eq_true_eq] at h
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
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsites
  have hCert : Q.toNum.Cert (c.params.γ : ℝ) (ray ωstar) := by
    refine NumQ.cert_ray hN S.hγ hdio (fun s hs => ?_) (fun s hs => ?_)
      (cohConstC_le_of_ok (hδq _).le htail)
    · exact sdConst_of_siteOk hn1 hτ1 hγq (hδq s) (hδ1 s) (hsites s hs).1 hω hdio
    · have hb := (hN.bbar s hs).1
      rw [NumQ.cast_b] at hb
      exact sdConst_of_siteOk hn1 hτ1 hγq (by exact_mod_cast hb) (min_le_right _ _)
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

end KAM.CertificateSharp.V2

end
