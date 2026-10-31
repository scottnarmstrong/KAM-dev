/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.RestartQ
public import KAM.CertificateSharp.V2.RouteAL1Core
public import KAM.Sharp2.RouteB.Frozen

/-!
# The hybrid checker (package C8c)

`checkHybrid c w`: the transfer checks H0–H4 (`transferOk`), the step claims (`hybStepOk`, at the
strips of the restarted run) and the route-A′ core at the restart numbers
(`refinedCoreR n params1 box witness1`, format v1 H5).

`checkHybrid_sound`: with the base facts of `c` (the landed checks other than the threshold test)
and the base claim (`HamFacts`, `FrameFacts` of `w.R0`), a passing check gives the conclusion of
C8b's `iso_g1_hybrid_R` for the base embedding `K̂`: an invariant torus within `dinf + disp₁` of
`K̂` on `T_{ρ∞}`, at a frequency within `d_ω + disp₁` of `s ω*`. The ray bound of the route-A
wrappers stands for `σω` (`rayBound`); `Iso.lean` turns the conclusion into `CertifiedTorus`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp2.RouteA.Ref KAM.Iso.Sharp KAM.CertificateSharp.V2 Matrix
open KAM.Sharp2.Hybrid (IG1Concl)
open KAM.Iso.Sharp2.Hybrid (iso_g1_hybrid_R IG1Concl.mono)

variable {n : ℕ} {α : Type} [CertArith α]

/-- **The hybrid checker.** -/
def checkHybrid (c : TorusCertificate n α) (w : HybWit) : Bool :=
  transferOk n c.params c.freqBox w &&
    hybStepOk c w.step w.p1.rho w.p1.rhoInf (w.ρT n c.freqBox) &&
    refinedCoreR n w.p1 c.freqBox w.w1

/-- The norms of the frame of `K` on `T_ρ` from the frame facts. -/
theorem frame_norms {c : TorusCertificate n α} {R : RefClaim} {ωstar : Fin n → ℝ} (hn : 1 ≤ n)
    (hρ0 : (0 : ℝ) < c.params.rho) (hF : FrameFacts c R ωstar) :
    (∀ θ ∈ complexStrip n c.params.rho, ‖(tangentMat c.K θ)ᵀ‖ ≤ R.bL) ∧
      (∀ θ ∈ complexStrip n c.params.rho, ‖normalMat c.K θ‖ ≤ R.bN) ∧
      (∀ θ ∈ complexStrip n c.params.rho, ‖(normalMat c.K θ)ᵀ‖ ≤ R.bNt) := by
  have h00 : (0 : Fin n → ℂ) ∈ complexStrip n c.params.rho := fun i => by simpa using hρ0
  have j0 : Fin n := ⟨0, hn⟩
  have hbL : (0 : ℝ) ≤ R.bL :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bL 0 h00 j0)
  have hbN : (0 : ℝ) ≤ R.bN :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bN 0 h00 (Sum.inl j0))
  have hbNt : (0 : ℝ) ≤ R.bNt :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bNt 0 h00 j0)
  exact ⟨fun θ hθ => (norm_le_iff_forall_rowSum hbL).2 fun j => hF.bL θ hθ j,
    fun θ hθ => (norm_le_iff_forall_rowSum hbN).2 fun r => hF.bN θ hθ r,
    fun θ hθ => (norm_le_iff_forall_rowSum hbNt).2 fun j => hF.bNt θ hθ j⟩

variable [LawfulCertArith α]

/-- **Soundness of the hybrid checker**: the conclusion of `iso_g1_hybrid_R` for `K̂`. -/
theorem checkHybrid_sound (c : TorusCertificate n α) (w : HybWit) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (hH : HamFacts c w.R0) (hF : FrameFacts c w.R0 ωstar) (h : checkHybrid c w = true) :
    IG1Concl c.D c.H c.K ωstar c.params.s c.params.E0 c.params.rhoInf c.params.μ c.params.σK
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖)
      (w.step.cl.dinf + w.p1.disp) (w.step.dw + w.p1.disp) := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, hν1, hν2⟩ := checkStatic_freq B.hs hω
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural B.hH.1
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  simp only [checkHybrid, Bool.and_eq_true] at h
  obtain ⟨⟨hTr, hSt⟩, hR⟩ := h
  have T := transferOk_sound hTr
  obtain ⟨hb, hlin, hdω⟩ := hybStepBounds hω hdio B hSt
  simp only [refinedCoreR, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨⟨⟨⟨⟨⟨hX, hwf⟩, hok⟩, hbud⟩, hsites⟩, htail⟩, hfin⟩ := hR
  set Q := w.w1.base.num n w.p1 c.freqBox with hQ
  have hN : Q.toNum.Wf := NumQ.wfOk_sound hwf
  have hτ1 : 1 ≤ Q.τ := by
    have h : (1 : ℝ) ≤ (Q.τ : ℝ) := hN.τ_ge
    exact_mod_cast h
  have hX' : (0 : ℝ) < w.w1.base.core.Xs := by exact_mod_cast hX
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hγq : 0 < c.params.γ := by exact_mod_cast S.hγ
  have hn1 : 1 ≤ n := by have := S.hn; omega
  -- the numbers of the restarted run against the base and the transfer
  have hτeq : Q.toNum.τ = (c.params.tau : ℝ) := by
    show ((w.p1.tau : ℕ) : ℝ) = _
    rw [T.tau]
  have hnn : (Q.toNum.n : ℝ) = ((n : ℚ) : ℝ) := by push_cast; rfl
  have hM1 : Q.toNum.M1 = ((w.R0.dx : ℚ) : ℝ) := by
    show ((w.w1.base.R.dx : ℚ) : ℝ) = _
    rw [T.dx]
  have hM2 : Q.toNum.M2 = ((w.R0.d2x : ℚ) : ℝ) := by
    show ((w.w1.base.R.d2x : ℚ) : ℝ) = _
    rw [T.d2x]
  have hMh2 : Q.toNum.Mh2 = ((w.R0.d2h : ℚ) : ℝ) := by
    show ((w.w1.base.R.d2h : ℚ) : ℝ) = _
    rw [T.d2h]
  have hδ0 : Q.toNum.δ 0 = ((w.δ1 n c.freqBox : ℚ) : ℝ) := NumQ.cast_δ 0
  have hρi : Q.toNum.ρinf = (c.params.rhoInf : ℝ) := by
    show ((w.p1.rhoInf : ℚ) : ℝ) = _
    rw [T.rhoInf]
  have hγ1 : (w.p1.γ : ℝ) = c.params.γ := by rw [T.gamma]
  have hdio1 : IsDiophantine (c.params.γ : ℝ) Q.toNum.τ ωstar := by rw [hτeq]; exact hdio
  -- the ray bound `σh = Θ/‖ω*‖`
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hν2' : (c.params.nuRay : ℝ) ≤
      (((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖ - c.params.s) * ‖ωstar‖ :=
    hν2.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  -- `e₁` of the theorem is `err₁`
  have he1 : w.qq.toNum.e1 w.step.cl.toNum Q.toNum.M2 = (w.p1.err : ℝ) := by
    rw [hM2, IsoNumQ.cast_e1]
    have e : w.qq.e1 w.step.cl w.R0.d2x = w.p1.err := by
      simp only [IsoNumQ.e1, HybWit.qq, sub_add_cancel]
      exact max_eq_right T.e1
    rw [e]
  -- the final comparisons at the restart parameters
  have hρi1 : (w.p1.rhoInf : ℝ) = c.params.rhoInf := by rw [T.rhoInf]
  obtain ⟨hsm, hc2, hc3⟩ := finalOkA_at (Q := Q) (p := w.p1) rfl rfl rfl hτ1
    (by rw [hγ1]; exact S.hγ) hN.ρinf_lt (by rw [hρi1]; exact S.hρinf)
    (by exact_mod_cast T.err0) hfin
  rw [hγ1] at hsm hc2 hc3
  -- (J1)–(J3) at the exact transferred numbers
  have hok' := NumQ.okR_sound hτ1 hok
  rw [← cast_capRQ, ← cast_initRQ _ _ _ w.w1.base.R.bT] at hok'
  have hnu : (w.p1.nuRay : ℝ) ≤ (c.params.nuRay : ℝ) - w.step.dw := by exact_mod_cast T.nu
  have hsK1 : ((w.step.cl.sK1 (w.kq c.params) w.p1.μ : ℚ) : ℝ) ≤ w.p1.σK := by rw [T.sK]
  have hsB1 : ((w.step.cl.sB1 (w.kq c.params) w.p1.μ : ℚ) : ℝ) ≤ w.p1.σB := by
    exact_mod_cast T.sB
  have hbL : (((w.kq c.params).ℓt + w.step.cl.d1t : ℚ) : ℝ) ≤ w.w1.base.R.bL := by
    exact_mod_cast T.bL
  have hbN : (((w.kq c.params).ν + (w.step.cl.frS (w.kq c.params)).nΔ : ℚ) : ℝ) ≤
      w.w1.base.R.bN := by exact_mod_cast T.bN
  have hbNt : (((w.kq c.params).νt + (w.step.cl.frS (w.kq c.params)).nΔt : ℚ) : ℝ) ≤
      w.w1.base.R.bNt := by exact_mod_cast T.bNt
  have hOk : routeAOkRI Q.toNum w.w1.bF
      (capRI Q.toNum ((w.p1.μ : ℝ) / 2) w.w1.bT (((c.params.nuRay : ℝ) - w.qq.toNum.dω) / 2))
      (initRI (w.step.cl.toNum.init1 (w.kq c.params).toK Q.toNum.n Q.toNum.M1 Q.toNum.M2
        (Q.toNum.δ 0) ((2 * w.R0.dx : ℚ) : ℝ)) (w.step.cl.toNum.sK1 (w.kq c.params).toK w.p1.μ)
        (w.step.cl.toNum.sB1 (w.kq c.params).toK w.p1.μ) w.p1.μ) w.w1.base.core.Xs := by
    rw [hnn, hM1, hM2, hδ0, StepNumQ.cast_init1, StepNumQ.cast_sK1, StepNumQ.cast_sB1]
    refine okRI_mono hok' (fun i => ?_) (fun i => ?_)
    · have hq : w.qq.toNum.dω = (w.step.dw : ℝ) := rfl
      have q0 := T.nu
      rw [hq]
      fin_cases i <;> simp [capRI]
      linarith
    · push_cast at hbL hbN hbNt
      have q1 := T.sB
      have q2 := T.bL
      have q3 := T.bN
      have q4 := T.bNt
      have q5 := T.sK
      fin_cases i <;> simp [initRI] <;> linarith
  -- the budgets of the torsion at the exact transferred numbers
  have hbud' := NumQ.budgetOk_sound hbud
  have hm0 : (0 : ℚ) < 1 - (w.kq c.params).m * w.tAx n c.params c.freqBox := by
    linarith [T.tA]
  have hB : KAM.Sharp2.RouteA.Ref.Budget Q.toNum
      ((w.kq c.params).toK.m / (1 - (w.kq c.params).toK.m * w.qq.toNum.tAext w.step.cl.toNum
        (w.kq c.params).toK Q.toNum.n Q.toNum.M1 Q.toNum.M2 (Q.toNum.δ 0)
        ((2 * w.R0.dx : ℚ) : ℝ)))
      (w.step.cl.toNum.init1 (w.kq c.params).toK Q.toNum.n Q.toNum.M1 Q.toNum.M2 (Q.toNum.δ 0)
        ((2 * w.R0.dx : ℚ) : ℝ)).iH w.w1.bF w.w1.bT := by
    rw [hnn, hM1, hM2, hδ0, StepNumQ.cast_init1, IsoNumQ.cast_tAext]
    have em : (w.kq c.params).toK.m = (((w.kq c.params).m : ℚ) : ℝ) := rfl
    rw [em]
    refine budget_mono hbud' ?_ ?_ ?_
    · have : (0 : ℚ) < (w.kq c.params).m / (1 - (w.kq c.params).m *
          w.tAx n c.params c.freqBox) := div_pos T.m0 hm0
      exact_mod_cast this
    · have : (w.kq c.params).m / (1 - (w.kq c.params).m * w.tAx n c.params c.freqBox) ≤
          w.p1.σT - w.p1.μ := by
        have := T.sT
        simp only [HybWit.mT] at this
        linarith
      exact_mod_cast this
    · have := T.bT
      simp only [HybWit.t1] at this
      show ((w.step.cl.t1 (w.kq c.params) (n : ℚ) w.R0.dx w.R0.d2x (w.δ1 n c.freqBox)
        (2 * w.R0.dx) : ℚ) : ℝ) ≤ _
      exact_mod_cast this
  -- the step bounds at the strips of the restarted run
  have eT : Q.toNum.ρ - Q.toNum.δ 0 = ((w.ρT n c.freqBox : ℚ) : ℝ) := by
    rw [hδ0]
    show ((w.p1.rho : ℚ) : ℝ) - _ = ((w.p1.rho - w.δ1 n c.freqBox : ℚ) : ℝ)
    push_cast
    rfl
  rw [← eT] at hb
  -- the numbers of the theorem
  have hlH : (w.step.lH : ℝ) ≤ w.qq.toNum.lH := by
    have : w.step.lH ≤ w.p1.err - w.R0.d2h / 2 * w.step.cl.d0R ^ 2 := by linarith [T.eH]
    show (w.step.lH : ℝ) ≤ ((w.p1.err - w.R0.d2h / 2 * w.step.cl.d0R ^ 2 : ℚ) : ℝ)
    exact_mod_cast this
  have hcTh : ∀ z ∈ c.D, ‖KAM.Sharp2.hamComm c.H z‖ ≤ ((2 * w.R0.dx : ℚ) : ℝ) :=
    fun z hz => by
      push_cast
      exact KAM.Sharp2.RouteB.norm_hamComm_le (hH.dx z hz)
  have hRef : ∀ z ∈ c.D, ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ Q.toNum.M1 ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ Q.toNum.M2 ∧
      ‖fderiv ℂ c.H z‖ ≤ w.qq.toNum.Mh1 ∧ ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ w.qq.toNum.Mh2 ∧
      w.qq.toNum.Mh2 ≤ Q.toNum.Mh2 := fun z hz => by
    rw [hM1, hM2, hMh2]
    exact ⟨hH.dx z hz, hH.d2x z hz, hH.dh z hz, hH.d2h z hz, le_rfl⟩
  obtain ⟨hLt, hNm, hNt⟩ := frame_norms hn1 hρ0 hF
  have hRI := V2.L1.refHyp_of_le (N := Q.toNum) (c := c) (R := w.R0) (ωstar := ωstar) hn1
    (by show ((w.p1.rho : ℚ) : ℝ) ≤ c.params.rho; exact_mod_cast T.rho) (hN.δ_pos 0).le hρ0
    hM1 hM2 hMh2 hH hF
  rw [T.gamma] at hsites
  simp only [sitesOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hsites
  have hδq : ∀ s, 0 < Q.δ s := fun s => by
    have := hN.δ_pos s
    rw [NumQ.cast_δ] at this
    exact_mod_cast this
  have hδ1 : ∀ s, Q.δ s ≤ 1 := fun s => by
    have := hN.δ_le s
    rw [NumQ.cast_δ] at this
    exact_mod_cast this
  have hdioQ : IsDiophantine (c.params.γ : ℝ) (Q.τ : ℝ) ωstar := hdio1
  have hCert : Q.toNum.Cert (c.params.γ : ℝ) (ray ωstar) := by
    refine NumQ.cert_ray hN S.hγ hdioQ (fun s hs => ?_) (fun s hs => ?_)
      (cohConstC_le_of_ok (hδq _).le htail)
    · exact sdConst_of_siteOk hn1 hτ1 hγq (hδq s) (hδ1 s) (hsites s hs).1 hω hdioQ
    · have hbb := (hN.bbar s hs).1
      rw [NumQ.cast_b] at hbb
      exact sdConst_of_siteOk hn1 hτ1 hγq (by exact_mod_cast hbb) (min_le_right _ _)
        (hsites s hs).2 hω hdioQ
  have eg : (c.params.γ : ℝ) ^ 2 * Q.toNum.ρ ^ (2 * Q.toNum.τ) =
      (c.params.γ : ℝ) ^ 2 * (w.p1.rho : ℝ) ^ (2 * (w.p1.tau : ℝ)) := rfl
  have hmain := iso_g1_hybrid_R (N₁ := Q.toNum) hN rfl (by rw [hτeq]; exact S.hτ)
    (Ω := ray ωstar)
    (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT)
    (μ := c.params.μ) (μ₁ := w.p1.μ) (γbar := Q.toNum.γb)
    (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖) (ν := c.params.nuRay)
    (ρ₀ := c.params.rho) (Xs := w.w1.base.core.Xs) (bF := w.w1.bF) (bT := w.w1.bT)
    (cTh := ((2 * w.R0.dx : ℚ) : ℝ)) (w.kq c.params).toK w.step.cl.toNum w.qq.toNum S.hM
    (by exact_mod_cast T.mu1) (S.hσω.trans_le hσ) hω0 rfl
    (by show ((w.p1.rho : ℚ) : ℝ) ≤ c.params.rho; exact_mod_cast T.rho)
    (by simp only [HybWit.kq, KDataQ.toK]; push_cast; ring)
    (by simp only [HybWit.kq, KDataQ.toK]; push_cast; ring)
    (by simp only [HybWit.kq, KDataQ.toK]; push_cast; ring)
    (by
      show ((w.p1.σK - w.p1.μ / 2 : ℚ) : ℝ) = _
      rw [StepNumQ.cast_sK1, ← T.sK]
      push_cast
      ring)
    (by
      show (((w.p1.σω * boxNormUp c.freqBox : ℚ) : ℝ)) = _
      rw [T.sigma]
      exact hΘ)
    (by
      show ((w.w1.base.R.dh * w.w1.base.core.sN : ℚ) : ℝ) = _
      rw [T.dh]
      push_cast
      rfl)
    (by
      have := T.nu0
      show (0 : ℝ) < c.params.nuRay - w.step.dw
      have h' : (0 : ℝ) < ((c.params.nuRay - w.step.dw : ℚ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      exact h')
    hOk hB hX'
    (by show ((w.step.cl.d0 : ℚ) : ℝ) + w.p1.μ ≤ c.params.μ; exact_mod_cast T.m1)
    (by show ((w.step.cl.d1 : ℚ) : ℝ) + (w.p1.μ : ℝ) / 2 ≤ (c.params.μ : ℝ) / 2
        exact_mod_cast T.m2)
    (by
      rw [StepNumQ.frS_toNum, FrameQ.cast_g]
      show (((w.kq c.params).β : ℚ) : ℝ) * _ < 1
      exact_mod_cast T.gS)
    (by
      rw [StepNumQ.frR_toNum, FrameQ.cast_g]
      show (((w.kq c.params).β : ℚ) : ℝ) * _ < 1
      exact_mod_cast T.gR)
    (by
      rw [hnn, hM1, hM2, hδ0, IsoNumQ.cast_tAext]
      show (((w.kq c.params).m : ℚ) : ℝ) * _ < 1
      exact_mod_cast T.tA)
    hopen htransl hholo hper hreal B.hH.2 hcTh hK hKp hKr B.hEm.1 B.hEm.2 B.hG B.hTu B.hTb
    S.hs1 hν1 hν2' hRef hLt hNm hNt hRI.tors (isStep_stepFun _ _) hb (hlin.trans hlH) hdω
    (fun t ht => ⟨t, ht, rfl⟩) hCert S.hγ
    (by
      show (c.params.γ : ℝ) ≤ (w.p1.γbar : ℝ)
      rw [T.gbar]
      exact S.hγγbar) hdio1
    (by rw [he1]; exact hsm)
    (by
      rw [he1]
      have hd : ((w.step.cl.dinf : ℚ) : ℝ) + w.p1.disp ≤ (c.params.μ : ℝ) / 2 := by
        exact_mod_cast T.bud
      rw [eg]
      show ((w.step.cl.dinf : ℚ) : ℝ) + _ ≤ _
      linarith [hc2])
  rw [he1, hρi, eg] at hmain
  refine IG1Concl.mono ?_ ?_ hmain
  · show ((w.step.cl.dinf : ℚ) : ℝ) + _ ≤ _
    linarith [hc2]
  · show ((w.step.dw : ℚ) : ℝ) + _ ≤ _
    linarith [hc3]

end KAM.CertificateSharp.Hybrid

end
