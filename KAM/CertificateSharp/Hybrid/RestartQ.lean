/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Hybrid.Claims
public import KAM.CertificateSharp.V2.RouteARefinedRef

/-!
# The restarted run of the hybrid witness (package C8c)

The witness rounds the restart data upward (format v1 §5 H4: `sB ≥ σ_{B,1} + μ₁`, `bL ≥ ℓᵗ + d₁ᵗ`,
…), and the route-A′ core runs at those rounded numbers. C8b's `iso_g1_hybrid_R` asks for the run at
the exact transferred numbers; the two tests below are monotone in the data the rounding moves:

* `okRI_mono`: `routeAOkRI` is monotone in the caps `σ` and antitone in the initial values `m₀`
  (both enter only (J3));
* `budget_mono`: `Budget` is antitone in the cap `m_T` of `|⟨T⟩⁻¹|` and the initial torsion `i_H`;
* `finalOkA_at`: `finalOkA` at any parameters (the restart's), without a certificate.

* `HybWit`: the hybrid witness (format v1): the base claim `R0`, the step, `params1`, `witness1`;
* `transferOk`, `TransferFacts`, `transferOk_sound`: the checks H0–H4 of format §5 in exact
  rationals, through the mirrors of `TransferQ` (`KDataQ`, `StepNumQ`, `IsoNumQ`).

The iso number `ℓ_H` of the theorem is `err₁ - (M_{h2}/2)(d₀ᴿ)²` (`HybWit.qq`), at least the claimed
`ℓ_H` by H2: then `e₁` of the theorem is `params1.err` exactly (H2: `e₁ ≤ err₁`), and no
monotonicity of the closeness constants in `e₁` is needed.
-/

@[expose] public section

namespace KAM.CertificateSharp.Hybrid

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp2.RouteA.Ref KAM.Iso.Sharp KAM.Sharp.Engine
  KAM.CertificateSharp.V2

/-! ### Monotonicity of the restarted run -/

theorem okRI_mono {N : NumA} {bF Xs : ℝ} {σ σ' m₀ m₀' : Fin 8 → ℝ}
    (h : routeAOkRI N bF σ m₀ Xs) (hσ : ∀ i, σ i ≤ σ' i) (hm : ∀ i, m₀' i ≤ m₀ i) :
    routeAOkRI N bF σ' m₀' Xs :=
  ⟨h.Xs_nonneg, h.J1, h.J1t, h.J2, fun i => by linarith [h.J3 i, hσ i, hm i]⟩

theorem budget_mono {N : NumA} {mT mT' iH iH' bF bT : ℝ}
    (h : KAM.Sharp2.RouteA.Ref.Budget N mT iH bF bT) (hpos : 0 < mT') (hmT : mT' ≤ mT)
    (hiH : iH' ≤ iH) : KAM.Sharp2.RouteA.Ref.Budget N mT' iH' bF bT := by
  have hs : 0 < N.sT := h.mT_pos.trans h.mT_lt
  refine ⟨hpos, hmT.trans_lt h.mT_lt, h.beta.trans ?_, by linarith [h.sup]⟩
  rw [div_le_div_iff₀ (mul_pos hs h.mT_pos) (mul_pos hs hpos)]
  have : 0 ≤ N.sT ^ 2 * (mT - mT') := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith [this]

/-- **`finalOkA` at the parameters `p`** (the restart's), from rational facts on `p`. -/
theorem finalOkA_at {Q : NumQ} {p : CertParams} {box : FreqBox} {Xs : ℚ} (hτ : Q.τ = p.tau)
    (hρ : Q.ρ = p.rho) (hρi : Q.ρinf = p.rhoInf) (hτ1 : 1 ≤ Q.τ) (hγ : (0 : ℝ) < p.γ)
    (hρρ : (p.rhoInf : ℝ) < p.rho) (hρi0 : (0 : ℝ) < p.rhoInf) (he0 : (0 : ℝ) ≤ p.err)
    (h : finalOkA Q p box Xs = true) :
    (p.err : ℝ) / ((p.γ : ℝ) ^ 4 *
        delta0 3 Q.toNum.ρ Q.toNum.ρinf ^ (2 * (2 * Q.toNum.τ))) < Xs ∧
      c2I Q.toNum Xs * p.err / ((p.γ : ℝ) ^ 2 * (p.rho : ℝ) ^ (2 * (p.tau : ℝ))) ≤ p.disp ∧
      c3I Q.toNum Xs * p.err / ((p.γ : ℝ) ^ 2 * (p.rho : ℝ) ^ (2 * (p.tau : ℝ))) ≤ p.disp := by
  simp only [finalOkA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  have hρ0 : (0 : ℝ) < p.rho := hρi0.trans hρρ
  have hd0 : 0 < (Q.δ0 : ℝ) := by
    rw [← NumQ.cast_δ0, hρ, hρi]
    exact delta0_pos (by norm_num) hρρ
  have e2 : (2 * (p.tau : ℝ)) = ((2 * p.tau : ℕ) : ℝ) := by push_cast; ring
  have hτQ : ((Q.τ : ℕ) : ℝ) = (p.tau : ℝ) := by rw [hτ]
  have hb := (Rat.cast_le (K := ℝ)).mpr h2
  push_cast at hb
  have hg : (0 : ℝ) < (p.γ : ℝ) ^ 2 * (p.rho : ℝ) ^ (2 * p.tau) :=
    mul_pos (pow_pos hγ 2) (pow_pos hρ0 _)
  have hclose : ∀ {C B : ℝ}, C ≤ B →
      B * p.err ≤ p.disp * ((p.γ : ℝ) ^ 2 * (p.rho : ℝ) ^ (2 * p.tau)) →
      C * p.err / ((p.γ : ℝ) ^ 2 * (p.rho : ℝ) ^ (2 * p.tau)) ≤ p.disp := fun {C B} hC hB => by
    rw [div_le_iff₀ hg]
    exact (mul_le_mul_of_nonneg_right hC he0).trans hB
  refine ⟨?_, ?_, ?_⟩
  · have hτ' : Q.toNum.τ = (p.tau : ℝ) := hτQ
    have e4 : 2 * (2 * (p.tau : ℝ)) = ((4 * p.tau : ℕ) : ℝ) := by push_cast; ring
    have hX4 : (0 : ℝ) < (p.γ : ℝ) ^ 4 * (Q.δ0 : ℝ) ^ (4 * p.tau) :=
      mul_pos (pow_pos hγ 4) (pow_pos hd0 _)
    have hh := (Rat.cast_lt (K := ℝ)).mpr h1
    push_cast at hh
    show (p.err : ℝ) / ((p.γ : ℝ) ^ 4 *
      delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (2 * (2 * Q.toNum.τ))) < Xs
    rw [NumQ.cast_δ0, hτ', e4, Real.rpow_natCast, div_lt_iff₀ hX4]
    calc (p.err : ℝ) < Xs * (p.γ : ℝ) ^ 4 * (Q.δ0 : ℝ) ^ (4 * p.tau) := hh
      _ = _ := by ring
  · rw [e2, Real.rpow_natCast, NumQ.cast_c2 hτ1]
    exact hclose (le_max_left _ _) hb
  · rw [e2, Real.rpow_natCast, NumQ.cast_c3 hτ1]
    exact hclose (le_max_right _ _) hb

/-! ### The witness and the transfer checks -/

/-- **The hybrid witness** (format v1): the base claim, the step, the restart. -/
structure HybWit where
  /-- `base.claim`: the refined claims of `K̂` (checked by the Hamiltonian pass and the frame
  majorants). -/
  R0 : RefClaim
  /-- `step`. -/
  step : HybStep
  /-- `restart.params1`. -/
  p1 : CertParams
  /-- `restart.witness1` (its sites: `"reuse-base"` is the base run's list). -/
  w1 : RefinedWitR

namespace HybWit

variable (w : HybWit) (n : ℕ) (p : CertParams) (box : FreqBox)

/-- The rational numbers of the restarted run. -/
def Q1 : NumQ := w.w1.base.num n w.p1 box
/-- `K`'s certified data: `ℓ = σK − μ`, `β = σB − μ`, `m = σT − μ` and the base claim. -/
def kq : KDataQ := ⟨p.σK - p.μ, w.R0.bL, p.σB - p.μ, w.R0.bN, w.R0.bNt, w.R0.bT, p.σT - p.μ⟩
/-- The iso numbers of the theorem: `ℓ_H := err₁ − (M_{h2}/2)(d₀ᴿ)²`, `d_ω`, `M_{h1}`, `M_{h2}`. -/
def qq : IsoNumQ := ⟨w.p1.err - w.R0.d2h / 2 * w.step.cl.d0R ^ 2, w.step.dw, w.R0.dh, w.R0.d2h⟩
/-- `δ₀′` of the restarted run. -/
def δ1 : ℚ := (w.Q1 n box).δ 0
/-- The torsion strip `ρ₁ − δ₀′`. -/
def ρT : ℚ := w.p1.rho - w.δ1 n box
/-- `t_A^ext`, with `c_Th = 2M₁`. -/
def tAx : ℚ := (w.qq).tAext w.step.cl (w.kq p) n w.R0.dx w.R0.d2x (w.δ1 n box) (2 * w.R0.dx)
/-- `t₁`. -/
def t1 : ℚ := w.step.cl.t1 (w.kq p) n w.R0.dx w.R0.d2x (w.δ1 n box) (2 * w.R0.dx)
/-- The exact cap `m/(1 − m t_A^ext)` of `|⟨T₁⟩⁻¹|`. -/
def mT : ℚ := (w.kq p).m / (1 - (w.kq p).m * w.tAx n p box)

end HybWit

/-- **The checks H0–H4 of format v1 §5**, exact rationals; `p` are the base parameters. -/
structure TransferFacts (n : ℕ) (p : CertParams) (box : FreqBox) (w : HybWit) : Prop where
  mu1 : 0 < w.p1.μ
  m1 : w.step.cl.d0 + w.p1.μ ≤ p.μ
  m2 : w.step.cl.d1 + w.p1.μ / 2 ≤ p.μ / 2
  rho : w.p1.rho ≤ p.rho
  gS : (w.kq p).β * (w.step.cl.frS (w.kq p)).g < 1
  gR : (w.kq p).β * (w.step.cl.frR (w.kq p)).g < 1
  e1 : w.step.cl.e1 w.R0.d2x ≤ w.p1.err
  eH : w.step.lH + w.R0.d2h / 2 * w.step.cl.d0R ^ 2 ≤ w.p1.err
  err0 : 0 ≤ w.p1.err
  m0 : 0 < (w.kq p).m
  tA : (w.kq p).m * w.tAx n p box < 1
  tau : w.p1.tau = p.tau
  rhoInf : w.p1.rhoInf = p.rhoInf
  M : w.p1.M = p.M
  gamma : w.p1.γ = p.γ
  gbar : w.p1.γbar = p.γbar
  sigma : w.p1.σω = p.σω
  E0 : w.p1.E0 = p.E0
  s1 : w.p1.s = w.step.s1
  sK : w.p1.σK = w.step.cl.sK1 (w.kq p) w.p1.μ
  sB : w.step.cl.sB1 (w.kq p) w.p1.μ ≤ w.p1.σB
  sT : w.mT n p box + w.p1.μ ≤ w.p1.σT
  nu : w.p1.nuRay ≤ p.nuRay - w.step.dw
  nu0 : 0 < p.nuRay - w.step.dw
  dh : w.w1.base.R.dh = w.R0.dh
  dx : w.w1.base.R.dx = w.R0.dx
  d2x : w.w1.base.R.d2x = w.R0.d2x
  d2h : w.w1.base.R.d2h = w.R0.d2h
  bL : (w.kq p).ℓt + w.step.cl.d1t ≤ w.w1.base.R.bL
  bN : (w.kq p).ν + (w.step.cl.frS (w.kq p)).nΔ ≤ w.w1.base.R.bN
  bNt : (w.kq p).νt + (w.step.cl.frS (w.kq p)).nΔt ≤ w.w1.base.R.bNt
  bT : w.t1 n p box ≤ w.w1.base.R.bT
  disp : max w.step.cl.dinf w.step.dw + w.p1.disp ≤ p.disp
  bud : w.step.cl.dinf + w.p1.disp ≤ p.μ / 2
  room : p.disp < (p.σω - p.s) * freqNormLo box

/-- The test of `TransferFacts`. -/
def transferOk (n : ℕ) (p : CertParams) (box : FreqBox) (w : HybWit) : Bool :=
  decide (0 < w.p1.μ) && decide (w.step.cl.d0 + w.p1.μ ≤ p.μ) &&
    decide (w.step.cl.d1 + w.p1.μ / 2 ≤ p.μ / 2) && decide (w.p1.rho ≤ p.rho) &&
    decide ((w.kq p).β * (w.step.cl.frS (w.kq p)).g < 1) &&
    decide ((w.kq p).β * (w.step.cl.frR (w.kq p)).g < 1) &&
    decide (w.step.cl.e1 w.R0.d2x ≤ w.p1.err) &&
    decide (w.step.lH + w.R0.d2h / 2 * w.step.cl.d0R ^ 2 ≤ w.p1.err) &&
    decide (0 ≤ w.p1.err) && decide (0 < (w.kq p).m) &&
    decide ((w.kq p).m * w.tAx n p box < 1) &&
    decide (w.p1.tau = p.tau) && decide (w.p1.rhoInf = p.rhoInf) && decide (w.p1.M = p.M) &&
    decide (w.p1.γ = p.γ) && decide (w.p1.γbar = p.γbar) && decide (w.p1.σω = p.σω) &&
    decide (w.p1.E0 = p.E0) && decide (w.p1.s = w.step.s1) &&
    decide (w.p1.σK = w.step.cl.sK1 (w.kq p) w.p1.μ) &&
    decide (w.step.cl.sB1 (w.kq p) w.p1.μ ≤ w.p1.σB) &&
    decide (w.mT n p box + w.p1.μ ≤ w.p1.σT) &&
    decide (w.p1.nuRay ≤ p.nuRay - w.step.dw) && decide (0 < p.nuRay - w.step.dw) &&
    decide (w.w1.base.R.dh = w.R0.dh) && decide (w.w1.base.R.dx = w.R0.dx) &&
    decide (w.w1.base.R.d2x = w.R0.d2x) && decide (w.w1.base.R.d2h = w.R0.d2h) &&
    decide ((w.kq p).ℓt + w.step.cl.d1t ≤ w.w1.base.R.bL) &&
    decide ((w.kq p).ν + (w.step.cl.frS (w.kq p)).nΔ ≤ w.w1.base.R.bN) &&
    decide ((w.kq p).νt + (w.step.cl.frS (w.kq p)).nΔt ≤ w.w1.base.R.bNt) &&
    decide (w.t1 n p box ≤ w.w1.base.R.bT) &&
    decide (max w.step.cl.dinf w.step.dw + w.p1.disp ≤ p.disp) &&
    decide (w.step.cl.dinf + w.p1.disp ≤ p.μ / 2) &&
    decide (p.disp < (p.σω - p.s) * freqNormLo box)

theorem transferOk_sound {n : ℕ} {p : CertParams} {box : FreqBox} {w : HybWit}
    (h : transferOk n p box w = true) : TransferFacts n p box w := by
  simp only [transferOk, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩

end KAM.CertificateSharp.Hybrid

end
