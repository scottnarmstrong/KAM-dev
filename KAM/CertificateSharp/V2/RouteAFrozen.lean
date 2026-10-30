/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteACore

/-!
# Stage 1: route A at the frozen data

`routeAFrozen` is the engine of `KAM.Iso.Sharp2.RouteA.iso_g1_v2A_default`: no refined hypothesis,
`M₁ = M₂ = M`, the default initial values of `defaultInit`, the classical small-divisor constants.
The test evaluates, in exact rational arithmetic, `NumA.Wf` (`wfOk`), `routeAOkI` (`okB`), the
classical constants (`classicalListOk`), and the comparisons `finalOk`, from the certificate's
parameters, its frequency box and a witness `FrozenWit`.

That theorem works at the threshold `torsionXs N M σK σB X⋆ = min X⋆ (1 + torsionCoef)⁻¹`, a real
number through `cohConstR`. `torsionCapOk` checks `X⋆ ≤ (1 + A)⁻¹` for a rational `A ≥ torsionCoef`,
and then `torsionXs = X⋆` (`torsionXs_eq`): the constants stay rational.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp

/-- The witness of stage 1. -/
structure FrozenWit where
  /-- The majorant `X⋆` of the initial normalised error. -/
  Xs : ℚ
  /-- The number of prefix stages. -/
  kp : ℕ
  /-- The Neumann ratio `ϑ`. -/
  th : ℚ
  /-- The classical constants at `δ_s`, `s < kp`. -/
  c : List ℚ
  /-- The classical constants at `b_s = min r_s 1`, `s < kp`. -/
  cbar : List ℚ
  /-- The classical constant at `δ_kp`. -/
  ctail : ℚ
  /-- The caps of `|B|`, `|⟨T⟩⁻¹|`, `|Lᵀ|`, `|N|`, `|Nᵀ|`, `|T|`. -/
  sB : ℚ
  sT : ℚ
  sLt : ℚ
  sN : ℚ
  sNt : ℚ
  t : ℚ
  /-- The number of explicit terms of `ζ(2, 2^τ)`. -/
  J : ℕ

/-- The rational numbers of the run at the parameters `p`, in dimension `n`. -/
def FrozenWit.num (w : FrozenWit) (n : ℕ) (p : CertParams) (box : FreqBox) : NumQ :=
  { n := n, τ := p.tau, ρ := p.rho, ρinf := p.rhoInf, M1 := p.M, M2 := p.M, sK := p.σK - p.μ / 2,
    sB := w.sB, sT := w.sT, sLt := w.sLt, sN := w.sN, sNt := w.sNt, t := w.t, th := w.th,
    γb := p.γbar, c := w.c, cbar := w.cbar, ctail := w.ctail, kp := w.kp,
    Θ := p.σω * boxNormUp box, HY := p.M * w.sN, Mh2 := p.M }

/-- The classical constants at the schedule. -/
def classicalListOk (Q : NumQ) (J : ℕ) : Bool :=
  (List.range Q.kp).all (fun s => classicalOk Q.n Q.τ J (Q.δ s) (Q.c.getD s 0) &&
    classicalOk Q.n Q.τ J (Q.b s) (Q.cbar.getD s 0)) && classicalOk Q.n Q.τ J (Q.δ Q.kp) Q.ctail

/-- The rational majorant of `torsionCoef`, with `c_R := cRRQ`. -/
def torsionCoefQ (Q : NumQ) (M σK σB : ℚ) : ℚ :=
  cT1Q Q.n σK σB * (Q.γb ^ 4 * Q.δ 0 ^ (2 * (2 * Q.τ) - 1)) +
    cT2Q Q.n Q.τ (cRRQ Q.n Q.τ) M σK σB * (Q.γb ^ 3 * Q.δ 0 ^ (3 * Q.τ - 1))

/-- `X⋆` is below the torsion cap of `torsionXs`. -/
def torsionCapOk (Q : NumQ) (M σK σB Xs : ℚ) : Bool :=
  decide ((1 + torsionCoefQ Q M σK σB) * Xs ≤ 1)

/-- The default initial values of `defaultInit`, for the parameters `p`. -/
def defaultInitQ (n : ℕ) (p : CertParams) : Fin 9 → ℚ :=
  initQ (2 * n * (p.σK - p.μ)) ((p.σK - p.μ) * (p.σB - p.μ)) (2 * n * (p.σK - p.μ) * (p.σB - p.μ))
    (hTQ n p.M p.σK p.σB) p.σK p.σB p.σT p.μ

/-- The test of stage 1 on the parameters and the box. -/
def frozenCore (n : ℕ) (p : CertParams) (box : FreqBox) (w : FrozenWit) : Bool :=
  let Q := w.num n p box
  decide (0 < w.Xs) && Q.wfOk && Q.okB (capQ Q p.μ p.nuRay) (defaultInitQ n p) w.Xs &&
    torsionCapOk Q p.M p.σK p.σB w.Xs && classicalListOk Q w.J && finalOk Q n p box w.Xs

variable {n : ℕ} {α : Type} [CertArith α]

/-- `hT` at rational data. -/
theorem cast_hT (n : ℕ) (M σK σB : ℚ) : hT n M σK σB = (hTQ n M σK σB : ℝ) := by
  simp only [hT, cT0, hTQ, cT0Q]; push_cast; rfl

/-- The default initial values at rational data. -/
theorem cast_defaultInit (n : ℕ) (p : CertParams) :
    initI (defaultInit n p.M p.σK p.σB p.μ) p.σK p.σB p.σT p.μ =
      fun i => (defaultInitQ n p i : ℝ) := by
  rw [defaultInitQ, ← cast_initQ]
  simp only [defaultInit, cast_hT]
  push_cast
  rfl

/-- `cT2` at `c_R = cohConstR` is below its mirror at `cRRQ`. -/
theorem cT2_le (n τ : ℕ) {M σK σB : ℚ} (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) :
    cT2 n (τ : ℝ) (cohConstR n (τ : ℝ)) M σK σB ≤ (cT2Q n τ (cRRQ n τ) M σK σB : ℝ) := by
  have hc := cohConstR_le_cRRQ n τ
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hK' : (0 : ℝ) < σK := by exact_mod_cast hσK
  have hB' : (0 : ℝ) < σB := by exact_mod_cast hσB
  have e : (2 : ℝ) ^ ((τ : ℝ) + 1) = (2 : ℝ) ^ (τ + 1) := by
    rw [← Nat.cast_succ, Real.rpow_natCast]
  simp only [cT2, cT2Q, wT, wTQ, cOm, cOmQ, e]
  push_cast
  gcongr

/-- `torsionCoef` is below its rational majorant. -/
theorem torsionCoef_le {Q : NumQ} {M σK σB : ℚ} (hτ : 1 ≤ Q.τ) (hγ : 0 < Q.γb) (hδ : 0 ≤ Q.δ 0)
    (hσK : 0 < σK) (hσB : 0 < σB) (hM : 0 < M) :
    torsionCoef Q.toNum M σK σB ≤ (torsionCoefQ Q M σK σB : ℝ) := by
  have e4 : (2 * (2 * (Q.τ : ℝ)) - 1 : ℝ) = ((2 * (2 * Q.τ) - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e3 : (3 * (Q.τ : ℝ) - 1 : ℝ) = ((3 * Q.τ - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have ec1 : cT1 Q.n (σK : ℝ) σB = (cT1Q Q.n σK σB : ℝ) := by
    simp only [cT1, cT1Q]; push_cast; rfl
  have hc2 := cT2_le Q.n Q.τ hM hσK hσB
  have hγ' : (0 : ℝ) ≤ Q.γb := by exact_mod_cast hγ.le
  have hδ' : (0 : ℝ) ≤ Q.δ 0 := by exact_mod_cast hδ
  unfold torsionCoef
  show cT1 Q.n (σK : ℝ) σB * ((Q.γb : ℝ) ^ 4 * Q.toNum.δ 0 ^ (2 * (2 * (Q.τ : ℝ)) - 1)) +
    cT2 Q.n (Q.τ : ℝ) (cohConstR Q.n (Q.τ : ℝ)) M σK σB *
      ((Q.γb : ℝ) ^ 3 * Q.toNum.δ 0 ^ (3 * (Q.τ : ℝ) - 1)) ≤ _
  rw [NumQ.cast_δ, e4, e3, Real.rpow_natCast, Real.rpow_natCast, ec1]
  simp only [torsionCoefQ]
  push_cast
  gcongr

/-- Below the rational cap, `torsionXs` is `X⋆`. -/
theorem torsionXs_eq {Q : NumQ} {M σK σB Xs : ℚ} (hτ : 1 ≤ Q.τ) (hγ : 0 < Q.γb) (hδ : 0 ≤ Q.δ 0)
    (hσK : 0 < σK) (hσB : 0 < σB) (hM : 0 < M) (hX : 0 ≤ Xs) (hN : Q.toNum.Wf)
    (h : torsionCapOk Q M σK σB Xs = true) : torsionXs Q.toNum M σK σB Xs = Xs := by
  simp only [torsionCapOk, decide_eq_true_eq] at h
  have hc := torsionCoef_le hτ hγ hδ hσK hσB hM
  have hc0 : 0 ≤ torsionCoef Q.toNum M σK σB := by
    have hT1 : 0 ≤ cT1 Q.toNum.n (σK : ℝ) σB := by
      have : (0 : ℝ) < σK := by exact_mod_cast hσK
      have : (0 : ℝ) < σB := by exact_mod_cast hσB
      unfold cT1; positivity
    have hT2 : 0 ≤ cT2 Q.toNum.n Q.toNum.τ (cohConstR Q.toNum.n Q.toNum.τ) M σK σB := by
      have hcR := (cohData_russmann (n := Q.toNum.n) hN.τ_ge).cR_pos
      have : (0 : ℝ) < σK := by exact_mod_cast hσK
      have : (0 : ℝ) < σB := by exact_mod_cast hσB
      have : (0 : ℝ) < M := by exact_mod_cast hM
      unfold cT2 wT cOm
      positivity
    have h1 := Real.rpow_nonneg (hN.δ_pos 0).le (2 * (2 * Q.toNum.τ) - 1)
    have h2 := Real.rpow_nonneg (hN.δ_pos 0).le (3 * Q.toNum.τ - 1)
    have h3 := hN.γb
    unfold torsionCoef
    positivity
  have hX' : (0 : ℝ) ≤ Xs := by exact_mod_cast hX
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  have hpos : 0 < 1 + torsionCoef Q.toNum M σK σB := by linarith
  unfold torsionXs
  refine min_eq_left ?_
  rw [← one_div, le_div_iff₀ hpos]
  have : (Xs : ℝ) * (1 + torsionCoef Q.toNum M σK σB) ≤
      (1 + (torsionCoefQ Q M σK σB : ℝ)) * Xs := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) hX'
  exact this.trans h'

/-- The classical certificates from `classicalListOk`. -/
theorem cert_of_classicalListOk {Q : NumQ} {J : ℕ} (hN : Q.toNum.Wf)
    (h : classicalListOk Q J = true) {γ : ℝ} (hγ : 0 < γ) :
    Q.toNum.Cert γ {ω | IsDiophantine γ Q.toNum.τ ω} := by
  simp only [classicalListOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  have hδ : ∀ s, 0 ≤ Q.δ s := fun s => by
    have := hN.δ_pos s
    rw [NumQ.cast_δ] at this
    exact_mod_cast this.le
  have hb : ∀ s < Q.kp, 0 ≤ Q.b s := fun s hs => by
    have := (hN.bbar s hs).1
    rw [NumQ.cast_b] at this
    exact_mod_cast this.le
  have hb1 : ∀ s < Q.toNum.kp, Q.toNum.bbar s ≤ 1 := fun s _ => by
    rw [NumQ.cast_b]
    have : Q.b s ≤ 1 := min_le_right _ _
    exact_mod_cast this
  refine NumA.cert_of_le hN hb1 hγ (fun s hs => ?_) (fun s hs => ?_) ?_
  · rw [NumQ.cast_δ]
    exact cohConstC_le_of_ok (hδ s) (h1 s hs).1
  · rw [NumQ.cast_b]
    exact cohConstC_le_of_ok (hb s hs) (h1 s hs).2
  · rw [NumQ.cast_δ]
    exact cohConstC_le_of_ok (hδ _) h2

/-- **Soundness of stage 1**, through `iso_g1_v2A_default`. -/
theorem frozenCore_sound [LawfulCertArith α] (c : TorusCertificate n α) (w : FrozenWit)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) (B : BaseFacts c ωstar)
    (h : frozenCore n c.params c.freqBox w = true) : CertifiedTorus c ωstar := by
  have S := checkStatic_sound B.hs
  obtain ⟨hω0, -, -⟩ := checkStatic_freq B.hs hω
  simp only [frozenCore, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hX, hwf⟩, hok⟩, htor⟩, hcl⟩, hfin⟩ := h
  set Q := w.num n c.params c.freqBox with hQ
  have hN : Q.toNum.Wf := NumQ.wfOk_sound hwf
  have hτ1 : 1 ≤ Q.τ := by
    have h : (1 : ℝ) ≤ (Q.τ : ℝ) := hN.τ_ge
    exact_mod_cast h
  have hγb : 0 < Q.γb := by
    have h : (0 : ℝ) < (Q.γb : ℝ) := hN.γb
    exact_mod_cast h
  have hX' : (0 : ℝ) < w.Xs := by exact_mod_cast hX
  have hδ0 : 0 ≤ Q.δ 0 := by
    have := hN.δ_pos 0
    rw [NumQ.cast_δ] at this
    exact_mod_cast this.le
  obtain ⟨hA, hroom⟩ := finalOk_sound (Q := Q) B.hs rfl rfl rfl hτ1 hX hfin hω
  have hσ0 : (0 : ℝ) ≤ c.params.σω := by linarith [S.hσω]
  obtain ⟨hσ, hΘ⟩ := rayBound (σ := c.params.σω) (Θ := c.params.σω * boxNormUp c.freqBox)
    hσ0 (by push_cast; exact le_rfl) hω hω0
  have hOk := NumQ.okB_sound hτ1 hok
  rw [← cast_capQ, ← cast_defaultInit] at hOk
  obtain ⟨-, -, -, hbody⟩ := iso_g1_v2A_default (N := Q.toNum) (M := c.params.M)
    (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT) (μ := c.params.μ)
    (γbar := c.params.γbar) (σω := ((c.params.σω * boxNormUp c.freqBox : ℚ) : ℝ) / ‖ωstar‖)
    (ν := c.params.nuRay) (Xs := w.Xs) hN rfl S.hτ S.hM S.hσK S.hσB S.hσT S.hμ
    (S.hσω.trans_le hσ) S.hν ωstar hω0 rfl (by simp [NumQ.toNum, Q, FrozenWit.num]) hΘ
    (by simp [NumQ.toNum, Q, FrozenWit.num]) rfl rfl rfl hOk hX'
    (fun _ hγ _ => cert_of_classicalListOk hN hcl hγ)
  rw [torsionXs_eq hτ1 hγb hδ0 (by exact_mod_cast S.hσK) (by exact_mod_cast S.hσB)
    (by exact_mod_cast S.hM) hX.le hN htor] at hbody
  exact certifiedTorus_of_ray hω hdio B hσ hA (fun _ _ ht => ray_lt_of_disp hroom ht) hbody

/-- **The engine of route A at the frozen data.** -/
def routeAFrozen : EngineV2 where
  Wit := FrozenWit
  test := fun {n} _ _ c w => frozenCore n c.params c.freqBox w
  sound := fun c w _ hω hdio B h => frozenCore_sound c w hω hdio B h

end KAM.CertificateSharp.V2

end
