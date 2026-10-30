/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteARefined
public import KAM.CertificateSharp.V2.RouteAQRef

/-!
# Stage 2 with lever L8′

`refinedCoreR` is the numerical part of the test of the branch
`KAM.Iso.Sharp2.RouteA.Ref.iso_g1_branch_R`: the same test as `refinedCore`, with `routeAOkRI` in
place of `routeAOkI` and the budgets of the torsion (`NumQ.budgetOk`). The witness adds the two
numbers of the lever: the local bound `b_F` and the budget `b_T` of `𝒯_ab`.

The test takes the branch and not the wrapper `iso_g1_v2A'`, for the reason of
`V2/RouteARefined.lean`: `C₂♯` at the frozen data leaves a useless displacement.

The certified constants are not computed twice: `ch = c_{s+1}` at the bite `δ_s/2` is a constant of
the schedule, and `sitesOk`, `classicalOk` are the tests of `refinedCore`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp2.RouteA.Ref KAM.Iso.Sharp

/-- The witness of stage 2 with lever L8′. -/
structure RefinedWitR where
  /-- The witness of stage 2; its cap `t` bounds the torsion, its cap `sT` the bordered average. -/
  base : RefinedWit
  /-- The bound of the local part of the torsion. -/
  bF : ℚ
  /-- The budget of `𝒯_ab`. -/
  bT : ℚ

/-- The caps of `capRI`, for the budgets `μ/2`, `ν/2`. -/
def capRQ (Q : NumQ) (μ ν bT : ℚ) : Fin 8 → ℚ :=
  ![μ / 2, Q.sK, Q.sB, bT, Q.sLt, Q.sN, Q.sNt, ν / 2]

/-- The initial values of `initRI`. -/
def initRQ (iLt iN iNt σK σB μ : ℚ) : Fin 8 → ℚ :=
  ![0, σK - μ, σB - μ, 0, iLt, iN, iNt, 0]

theorem cast_capRQ (Q : NumQ) (μ ν bT : ℚ) :
    capRI Q.toNum ((μ : ℝ) / 2) (bT : ℝ) ((ν : ℝ) / 2) = fun i => (capRQ Q μ ν bT i : ℝ) := by
  funext i
  fin_cases i <;> simp [capRI, capRQ, NumQ.toNum]

theorem cast_initRQ (iLt iN iNt iH σK σB μ : ℚ) :
    initRI ⟨iLt, iN, iNt, iH⟩ σK σB μ = fun i => (initRQ iLt iN iNt σK σB μ i : ℝ) := by
  funext i
  fin_cases i <;> simp [initRI, initRQ]

/-- The numerical test of stage 2 with lever L8′. -/
def refinedCoreR (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedWitR) : Bool :=
  let Q := w.base.num n p box
  decide (0 < w.base.core.Xs) && Q.wfOk &&
    Q.okR w.bF (capRQ Q p.μ p.nuRay w.bT) (initRQ w.base.R.bL w.base.R.bN w.base.R.bNt p.σK p.σB p.μ)
      w.base.core.Xs &&
    Q.budgetOk (p.σT - p.μ) w.base.R.bT w.bF w.bT &&
    sitesOk Q w.base.core.J box w.base.κ p.γ w.base.sites &&
    classicalOk n p.tau w.base.core.J (Q.δ w.base.core.kp) Q.ctail &&
    finalOkA Q p box w.base.core.Xs

/-- Sharding: `refinedCoreR` from its parts. -/
theorem refinedCoreR_of {n : ℕ} {p : CertParams} {box : FreqBox} {w : RefinedWitR}
    (h0 : 0 < w.base.core.Xs) (h1 : (w.base.num n p box).wfOk = true)
    (h2 : (w.base.num n p box).okR w.bF (capRQ (w.base.num n p box) p.μ p.nuRay w.bT)
      (initRQ w.base.R.bL w.base.R.bN w.base.R.bNt p.σK p.σB p.μ) w.base.core.Xs = true)
    (h3 : (w.base.num n p box).budgetOk (p.σT - p.μ) w.base.R.bT w.bF w.bT = true)
    (h4 : sitesOk (w.base.num n p box) w.base.core.J box w.base.κ p.γ w.base.sites = true)
    (h5 : classicalOk n p.tau w.base.core.J ((w.base.num n p box).δ w.base.core.kp)
      (w.base.num n p box).ctail = true)
    (h6 : finalOkA (w.base.num n p box) p box w.base.core.Xs = true) :
    refinedCoreR n p box w = true := by
  simp only [refinedCoreR, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

variable {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]

/-- **Soundness of stage 2 with lever L8′**, through `Ref.iso_g1_branch_R`. -/
theorem refinedCoreR_sound (c : TorusCertificate n α) (w : RefinedWitR) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.base.R) (hF : FrameFacts c w.base.R ωstar)
    (h : refinedCoreR n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [refinedCoreR, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hX, hwf⟩, hok⟩, hbud⟩, hsites⟩, htail⟩, hfin⟩ := h
  set Q := w.base.num n c.params c.freqBox with hQ
  have hN : Q.toNum.Wf := NumQ.wfOk_sound hwf
  have hτ1 : 1 ≤ Q.τ := by
    have h : (1 : ℝ) ≤ (Q.τ : ℝ) := hN.τ_ge
    exact_mod_cast h
  have hX' : (0 : ℝ) < w.base.core.Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hγq : 0 < c.params.γ := by exact_mod_cast S.hγ
  obtain ⟨hsm, hd2, hd3, hroom⟩ := finalOkA_sound (Q := Q) B.hs rfl rfl rfl hτ1 hX hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hOk := NumQ.okR_sound hτ1 hok
  rw [← cast_capRQ, ← cast_initRQ _ _ _ w.base.R.bT] at hOk
  have hB := NumQ.budgetOk_sound hbud
  rw [show ((c.params.σT - c.params.μ : ℚ) : ℝ) = (c.params.σT : ℝ) - c.params.μ by
    push_cast; rfl] at hB
  have hRef : RefHypIA Q.toNum w.base.R.init w.base.R.dh c.D c.H c.K
      ((c.params.s : ℝ) • ωstar) :=
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
  obtain ⟨Kinf, sinf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := Ref.iso_g1_branch_R
    (N := Q.toNum) (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT)
    (μ := c.params.μ)
    (γbar := c.params.γbar) (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖)
    (ν := c.params.nuRay) (Xs := w.base.core.Xs) (Mh1 := w.base.R.dh) (I := w.base.R.init)
    (Ω := ray ωstar)
    hN rfl S.hτ S.hM S.hμ (S.hσω.trans_le hσ) S.hν hω0 rfl
    (by simp [NumQ.toNum, Q, RefinedWit.num, FrozenWit.num]) hΘ
    (by simp [NumQ.toNum, Q, RefinedWit.num, FrozenWit.num]) hOk hB hX' hopen htransl hholo hper
    hreal B.hH.2 hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb S.hs1 hν1 hν2' hRef
    (fun t ht => ⟨t, ht, rfl⟩) hCert S.hγ S.hγγbar hdio S.he0 B.hE B.hEn hsm
  exact ⟨Kinf, sinf, h1, ray_lt_of_disp hroom (h11.trans hd3), h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans hd2, h11.trans hd3⟩

end KAM.CertificateSharp.V2

end
