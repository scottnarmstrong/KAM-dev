/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowMean
public import KAM.Planetary.Preparation.SlowCauchy

/-!
# Slow averaging: the polar averages of `R₄` and `ḡ` (P11A-P7b, graph step `as-osc`)

`p11_slow_polar` applies `polar_avg` to the quartic remainder `p11R4` (`S = M_F/16`, jets from
`p11R4_jets`) and to the fast-averaging remainder `p11Gbar` (`S = η₁`) on
`D(J₀, s₁/2) × B(0, r_z/2)`.  `p11_partial_rho_jet` is the `ρ`-derivative / `J`-jet Cauchy
estimate (`p11PartialVec_norm_le`) used for the `Z` jet clause.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Polar

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}


theorem p11eta1_pos (hC : P11SecularSpec D C) {eps : ℝ} (heps : 0 < eps)
    (hεM : eps * C.MF ≤ Real.exp (-1)) : 0 < p11eta1 C eps := by
  obtain ⟨hα, -⟩ := p11_alpha_le hC heps hεM
  obtain ⟨hd, -⟩ := p11d1_le hC heps hεM
  obtain ⟨-, -, -, -, -, -, -, -, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  unfold p11eta1
  have : (0 : ℝ) < (1 + n) := by positivity
  positivity

/-- Holomorphy and the `η₁` bound of `ḡ = G - FastMean` on `D(J₀, s₁/2) × B(0, r_z/2)`. -/
theorem p11_gbar_data (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1)) :
    DifferentiableOn ℂ (p11Gbar C Fast) (ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
      ball (0 : P11Phase n) (C.rz / 2)) ∧
    p11Bound (ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
      ball (0 : P11Phase n) (C.rz / 2)) (p11Gbar C Fast) (p11eta1 C eps) := by
  obtain ⟨-, -, -, hrC0, -, -, -, hrz0, -⟩ := fast_consts hC
  have hrC : p11s1 C eps ≤ C.rC := p11s1_le C eps
  have hsub : ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ⊆
      ball (KAM.realInclusion n C.J0) (2 * C.rC) := ball_subset_ball (by
    have := p11s1_pos hC heps hεM
    linarith)
  have hsubz : ball (0 : P11Phase n) (C.rz / 2) ⊆ ball (0 : P11Phase n) C.rz :=
    ball_subset_ball (by linarith)
  obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGb, -⟩ := hF
  refine ⟨hGd.sub ((p11FastMean_differentiableOn hC).mono (prod_mono hsub hsubz)), ?_⟩
  rintro ⟨J, z⟩ ⟨hJ, hz⟩
  exact hGb J (mem_ball_iff_norm.1 hJ) z (mem_ball_zero_iff.1 hz)

/-- The two polar averages of graph step `as-osc`: `AR = 𝒜 R₄`, `AB = 𝒜 ḡ` with their bounds. -/
theorem p11_slow_polar (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (hF : P11FastSpec C eps Fast) (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1)) :
    ∃ AR AB : P11CVec n × P11CVec n → ℂ,
      DifferentiableOn ℂ AR (ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4)) ∧
      DifferentiableOn ℂ AB (ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
        ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4)) ∧
      (∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
          ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4),
        ‖AR z‖ ≤ 2 ^ (2 * n) * (C.MF / 16) *
          (4 * ‖z.2‖ / (Real.pi * (C.rz / 2) ^ 2)) ^ 2) ∧
      (∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
          ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4),
        ‖AB z‖ ≤ 2 ^ (2 * n) * p11eta1 C eps) ∧
      (∀ z ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) ×ˢ
          ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4), (∀ i, 0 < (z.2 i).re) →
        AR z = p11PolarAverage (p11R4 C) z ∧ AB z = p11PolarAverage (p11Gbar C Fast) z) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hs0 := p11s1_pos hC heps hεM
  have hrC : p11s1 C eps ≤ C.rC := p11s1_le C eps
  have hr : 0 < C.rz / 2 := by positivity
  have hr1 : C.rz / 2 ≤ 1 := by linarith
  set Dm : Set (P11CVec n) := ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) with hDm
  have hsub : Dm ⊆ ball (KAM.realInclusion n C.J0) (2 * C.rC) :=
    ball_subset_ball (by linarith)
  have hsubz : ball (0 : P11Phase n) (C.rz / 2) ⊆ ball (0 : P11Phase n) C.rz :=
    ball_subset_ball (by linarith)
  -- `R₄`
  have hR4d : DifferentiableOn ℂ (p11R4 C) (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) :=
    (p11R4_differentiableOn hC).mono (prod_mono hsub hsubz)
  have hR4b : p11Bound (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) (p11R4 C) (C.MF / 16) := by
    rintro ⟨J, z⟩ ⟨hJ, hz⟩
    have hzr : ‖z‖ < C.rz / 2 := mem_ball_zero_iff.1 hz
    refine (p11R4_bound hC (hsub hJ) (hzr.trans (by linarith))).trans ?_
    have h4 : ‖z‖ ^ 4 ≤ (C.rz / 2) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hzr.le 4
    calc C.MF / C.rz ^ 4 * ‖z‖ ^ 4 ≤ C.MF / C.rz ^ 4 * (C.rz / 2) ^ 4 := by gcongr
      _ = C.MF / 16 := by field_simp; norm_num
  obtain ⟨AR, hARd, hARb, hARe, hARc⟩ := polar_avg (D := Dm) isOpen_ball hr hr1
    (by linarith : 0 < C.MF / 16) hR4d hR4b
  -- `ḡ`
  have hη0 := p11eta1_pos hC heps hεM
  obtain ⟨hGbd, hGbb⟩ := p11_gbar_data hC Fast hF heps hεM
  obtain ⟨AB, hABd, hABb, hABe, hABc⟩ := polar_avg (D := Dm) isOpen_ball hr hr1 hη0 hGbd hGbb
  refine ⟨AR, AB, hARd, hABd, ?_, ?_, ?_⟩
  · intro z hz
    have := hARc 4 (fun J hJ j hj => p11R4_jets hC (hsub hJ) j hj) z hz
    simpa using this
  · intro z hz
    exact hABb z hz |>.trans (le_of_eq rfl)
  · intro z hz hre
    exact ⟨hARe z hz hre, hABe z hz hre⟩

end Polar

section Jet

variable {n : ℕ}

/-- The `ρ`-derivative of a jointly holomorphic `Zq` at the fixed `ρ₀` is holomorphic in `J`. -/
theorem p11_rhoDeriv_differentiableOn {U : Set (P11CVec n)} (hU : IsOpen U) {R0 : ℝ}
    {Zq : P11CVec n × P11CVec n → ℂ} (hZ : DifferentiableOn ℂ Zq (U ×ˢ ball 0 R0))
    {ρ0 : P11CVec n} (hρ0 : ρ0 ∈ ball (0 : P11CVec n) R0) :
    DifferentiableOn ℂ (fun J' : P11CVec n => fun i : Fin n =>
      fderiv ℂ (fun ρ => Zq (J', ρ)) ρ0 (Pi.single i 1)) U := by
  have hUb : IsOpen (U ×ˢ ball (0 : P11CVec n) R0) := hU.prod isOpen_ball
  have hfd : DifferentiableOn ℂ (fderiv ℂ Zq) (U ×ˢ ball (0 : P11CVec n) R0) :=
    (KAM.analyticOnNhd_of_differentiableOn hUb hZ).fderiv.differentiableOn
  refine differentiableOn_pi.2 fun i => ?_
  have h1 : DifferentiableOn ℂ (fun J' : P11CVec n => fderiv ℂ Zq (J', ρ0)) U :=
    hfd.comp (by fun_prop : DifferentiableOn ℂ (fun J' : P11CVec n => (J', ρ0)) U)
      (fun J' hJ' => ⟨hJ', hρ0⟩)
  have h2 := h1.clm_apply (differentiableOn_const ((0 : P11CVec n), (Pi.single i 1 : P11CVec n)))
  refine h2.congr fun J' hJ' => ?_
  have hZd : DifferentiableAt ℂ Zq (J', ρ0) := hZ.differentiableAt (hUb.mem_nhds ⟨hJ', hρ0⟩)
  have := fderiv_comp ρ0 hZd (by fun_prop : DifferentiableAt ℂ (fun ρ : P11CVec n => (J', ρ)) ρ0)
  simp only [Function.comp_def] at this ⊢
  rw [this, (hasFDerivAt_prodMk_right J' ρ0).fderiv]
  simp

/-- Cauchy estimate in `ρ`: if `Zq` is holomorphic and bounded by `K` on `U × B(ρ₀, δ')`, then
`‖∂_{ρ_i} Zq (w, ρ₀)‖ ≤ K/δ` for `δ < δ'`. -/
theorem p11_rho_cauchy {U : Set (P11CVec n)} {R0 : ℝ} {Zq : P11CVec n × P11CVec n → ℂ}
    (hZ : DifferentiableOn ℂ Zq (U ×ˢ ball 0 R0)) {ρ0 : P11CVec n} {δ δ' K : ℝ} (hδ : 0 < δ)
    (hδδ : δ < δ') (hball : ball ρ0 δ' ⊆ ball (0 : P11CVec n) R0)
    (hK : ∀ J ∈ U, ∀ ρ ∈ ball ρ0 δ', ‖Zq (J, ρ)‖ ≤ K) {w : P11CVec n} (hw : w ∈ U) (i : Fin n) :
    ‖fderiv ℂ (fun ρ => Zq (w, ρ)) ρ0 (Pi.single i 1)‖ ≤ K / δ := by
  have hfd : DifferentiableOn ℂ (fun ρ => Zq (w, ρ)) (ball ρ0 δ') :=
    hZ.comp (by fun_prop : DifferentiableOn ℂ (fun ρ : P11CVec n => (w, ρ)) _)
      (fun ρ hρ => ⟨hw, hball hρ⟩)
  exact (cauchy_open isOpen_ball hfd hδ (z := ρ0)
    (closedBall_subset_ball hδδ) (fun ρ hρ => hK w hw ρ hρ)).1 i

/-- Sharp `J`-jet estimate for the `ρ`-derivative: a uniform bound `M` on `∂ρ Zq (·, ρ₀)` over `U`
gives `‖∂_J^α ∂ρ Zq (J, ρ₀)‖ ≤ α! M R^{-|α|}`. -/
theorem p11_partial_rho_jet {U : Set (P11CVec n)} (hU : IsOpen U) {R0 : ℝ}
    {Zq : P11CVec n × P11CVec n → ℂ} (hZ : DifferentiableOn ℂ Zq (U ×ˢ ball 0 R0))
    {ρ0 : P11CVec n} (hρ0 : ρ0 ∈ ball (0 : P11CVec n) R0) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ U, ∀ i : Fin n, ‖fderiv ℂ (fun ρ => Zq (w, ρ)) ρ0 (Pi.single i 1)‖ ≤ M)
    {J : P11CVec n} {R : ℝ} (hR : 0 < R) (hJ : closedBall J R ⊆ U) (α : Fin n → ℕ) :
    ‖p11PartialVec α (fun J' : P11CVec n => fun i : Fin n =>
        fderiv ℂ (fun ρ => Zq (J', ρ)) ρ0 (Pi.single i 1)) J‖ ≤
      (∏ i, ((α i).factorial : ℝ)) * M / R ^ (∑ i, α i) :=
  p11PartialVec_norm_le hU (p11_rhoDeriv_differentiableOn hU hZ hρ0) hR hJ
    (fun w hw => (pi_norm_le_iff_of_nonneg hM0).2 (hM w hw)) α

end Jet

end KAM.Planetary

end
