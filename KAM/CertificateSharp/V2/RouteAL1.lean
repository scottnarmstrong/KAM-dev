/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAL1Core

/-!
# Route A with the ℓ¹ entry: the numerical test and its soundness (package C6L1)

`l1Core` is the numerical part of the test of the branch `KAM.Iso.Sharp2.L1.iso_g1_branch_AL1`
(package B10C): `NumA.Wf`; the exact rational mirror `okL1` of `routeAOkIL1` with C6's caps and the
claimed initial values; C6's certified small-divisor sites; the classical tail; the entry record
against the ℓ¹ claim and the box (`entryOk`); and the final comparisons (`finalL1`).

`l1Core_sound` concludes the landed `CertifiedTorus c ω*` from `BaseFacts`, `HamFacts`,
`FrameFacts`, `L1Facts` (statements on the objects of `c`, proved by checks in
`V2/RouteAL1Engine.lean`) and the test, for every Diophantine `ω*` of the box.

As in C6 the test takes the branch and not the wrapper `iso_g1_v2A_l1`, whose displacement
constants are the maxima with v1's `C₂♯`, `C₃♯`: near a refined threshold `C₂♯` dominates and leaves
no room on the ray.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.V2.L1

open KAM KAM.Torus KAM.Certificate KAM.CertificateSharp CertArith KAM.Sharp2.L1
  KAM.CertificateSharp.V2 KAM.Sharp KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA KAM.Sharp.Engine
  KAM.Iso.Sharp KAM.Sharp2
open KAM.Sharp2.Examples (EntryQ)

/-- The numerical test of route A with the ℓ¹ entry. -/
def l1Core (n : ℕ) (p : CertParams) (box : FreqBox) (w : L1Wit) : Bool :=
  let Q := w.num n p box
  decide (0 < w.base.core.Xs) && Q.wfOk &&
    okL1 Q w.E (capQ Q p.μ p.nuRay)
      (initQ w.base.R.bL w.base.R.bN w.base.R.bNt w.base.R.bT p.σK p.σB p.σT p.μ)
      w.base.core.Xs &&
    sitesOk Q w.base.core.J box w.base.κ p.γ w.base.sites &&
    classicalOk n p.tau w.base.core.J (Q.δ w.base.core.kp) Q.ctail &&
    entryOk n Q p box w && finalL1 Q w.E p box w.base.core.Xs

/-- Sharding: `l1Core` from its parts. -/
theorem l1Core_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : L1Wit}
    (h0 : 0 < w.base.core.Xs) (h1 : (w.num n p box).wfOk = true)
    (h2 : okL1 (w.num n p box) w.E (capQ (w.num n p box) p.μ p.nuRay)
      (initQ w.base.R.bL w.base.R.bN w.base.R.bNt w.base.R.bT p.σK p.σB p.σT p.μ)
      w.base.core.Xs = true)
    (h3 : sitesOk (w.num n p box) w.base.core.J box w.base.κ p.γ w.base.sites = true)
    (h4 : classicalOk n p.tau w.base.core.J ((w.num n p box).δ w.base.core.kp)
      (w.num n p box).ctail = true)
    (h5 : entryOk n (w.num n p box) p box w = true)
    (h6 : finalL1 (w.num n p box) w.E p box w.base.core.Xs = true) :
    l1Core n p box w = true := by
  simp only [l1Core, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness of route A with the ℓ¹ entry**, through `iso_g1_branch_AL1`. -/
theorem l1Core_sound (c : TorusCertificate n α) (w : L1Wit) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.base.R) (hF : FrameFacts c w.base.R ωstar) (hL : L1Facts c w.L ωstar)
    (h : l1Core n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, -, hKr⟩ := c.emb_structural
  simp only [l1Core, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hX, hwf⟩, hok⟩, hsites⟩, htail⟩, hent⟩, hfin⟩ := h
  set Q := w.num n c.params c.freqBox with hQ
  have hN : Q.toNum.Wf := NumQ.wfOk_sound hwf
  have hτ1 : 1 ≤ Q.τ := by
    have h : (1 : ℝ) ≤ (Q.τ : ℝ) := hN.τ_ge
    exact_mod_cast h
  have hX' : (0 : ℝ) < w.base.core.Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hγq : 0 < c.params.γ := by exact_mod_cast S.hγ
  obtain ⟨hEw, hei, hOk⟩ := okL1_sound hN hτ1 hok
  rw [← cast_capQ, ← cast_initQ] at hOk
  obtain ⟨hsm, hd2, hd3, hroom⟩ := finalL1_sound B.hs hN rfl hτ1 hEw hei hX hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hle : Q.toNum.ρ ≤ c.params.rho := hL.rho1.2.le
  have hsub : ∀ θ ∈ complexStrip n Q.toNum.ρ, θ ∈ complexStrip n c.params.rho :=
    fun θ hθ i => (hθ i).trans_le hle
  have hRef : RefHypIA Q.toNum w.base.R.init w.base.R.dh c.D c.H c.K
      ((c.params.s : ℝ) • ωstar) :=
    refHyp_of_le (N := Q.toNum) (by have := hN.two_le; omega) hle (hN.δ_pos 0).le hρ0 rfl rfl
      rfl hH hF
  have hEH := entryHyp_of B hω hdio hF hL hent
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
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    KAM.Iso.Sharp2.L1.iso_g1_branch_AL1
    (N := Q.toNum) (E := w.E.toA) (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB)
    (σT := c.params.σT) (μ := c.params.μ) (γbar := c.params.γbar)
    (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖)
    (ν := c.params.nuRay) (Xs := w.base.core.Xs) (Mh1 := w.base.R.dh) (I := w.base.R.init)
    (Ω := ray ωstar)
    hN hEw rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by simp [NumQ.toNum, Q, L1Wit.num, RefinedWit.num, FrozenWit.num]) hΘ
    (by simp [NumQ.toNum, Q, L1Wit.num, RefinedWit.num, FrozenWit.num]) hOk hX' hopen htransl
    hholo hper hreal B.hH.2 (hK.mono hsub) (CertEmbedding.isPrimaryOnStrip n c.emb _) hKr
    (fun θ hθ => B.hEm.1 θ (hsub θ hθ)) (fun θ hθ => B.hEm.2 θ (hsub θ hθ))
    (fun θ hθ => B.hG θ (hsub θ hθ)) B.hTu B.hTb S.hs1 hν1 hν2' hRef
    (fun t ht => ⟨t, ht, rfl⟩) hCert hEH S.hγ S.hγγbar hdio S.he0
    (fun θ hθ => B.hE θ (hsub θ hθ)) B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

end KAM.CertificateSharp.V2.L1

end
