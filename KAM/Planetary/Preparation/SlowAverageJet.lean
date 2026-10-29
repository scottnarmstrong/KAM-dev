/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowAverageW

/-!
# Slow averaging: the derivative bounds of `Ẑ` (P11A-P7b, graph step `as-osc`)

`p11_slow_rho_bound`: `‖∂_ρ̃ (𝒜R₄ + 𝒜ḡ)‖ ≤ c (ε + η₁)` on `D(J₀, s₁/2) × D(2πε, πε)` by
`cauchy_open` (radius `πε/4` for `𝒜R₄` with `‖𝒜R₄‖ ≲ ε²`; radius `π r_z²/64` for `𝒜ḡ`).
`p11_slow_Z_jets` is the `J`-jet clause of `P11SlowSpec` through `p11PartialVec_norm_le`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators
namespace KAM.Planetary

section Jet

variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}

/-- The constant of the `ρ̃`-derivative bound. -/
def p11SlowCZ (C : P11SecularData n) : ℝ :=
  2 ^ (2 * n) * (C.MF / 16) * (784 / (Real.pi * (C.rz / 2) ^ 4)) +
    2 ^ (2 * n) * (16 / (Real.pi * (C.rz / 2) ^ 2))

theorem p11SlowZ_append (AR AB : P11CVec n × P11CVec n → ℂ) (J ρ : P11CVec n) :
    p11SlowZ AR AB (Fin.append J ρ) = AR (J, ρ) + AB (J, ρ) := by
  have h1 : p11SlowJ (Fin.append J ρ) = J := by funext i; simp [p11SlowJ]
  have h2 : p11SlowR (Fin.append J ρ) = ρ := by funext i; simp [p11SlowR]
  simp [p11SlowZ, h1, h2]

theorem p11_diffAt_rho {U : Set (P11CVec n)} (hU : IsOpen U) {R0 : ℝ}
    {F : P11CVec n × P11CVec n → ℂ} (hF : DifferentiableOn ℂ F (U ×ˢ ball 0 R0)) {w ρ0 : P11CVec n}
    (hw : w ∈ U) (hρ0 : ρ0 ∈ ball (0 : P11CVec n) R0) :
    DifferentiableAt ℂ (fun ρ => F (w, ρ)) ρ0 := by
  have hZd : DifferentiableAt ℂ F (w, ρ0) :=
    hF.differentiableAt ((hU.prod isOpen_ball).mem_nhds ⟨hw, hρ0⟩)
  exact hZd.comp ρ0 (by fun_prop : DifferentiableAt ℂ (fun ρ : P11CVec n => (w, ρ)) ρ0)

/-- Cauchy bound for `∂ρ̃ (𝒜R₄ + 𝒜ḡ)` at a point of `D(2πε, πε)` (graph step `as-osc`). -/
theorem p11_slow_rho_bound (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 128 * eps < C.rz ^ 2)
    {AR AB : P11CVec n × P11CVec n → ℂ} (hP : P11SlowPolarOut C Fast eps AR AB)
    {ρ0 : P11CVec n} (hρ0 : ‖ρ0 - (fun _ => (2 * Real.pi * eps : ℂ))‖ < Real.pi * eps)
    {w : P11CVec n} (hw : w ∈ ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2)) (i : Fin n) :
    ‖fderiv ℂ (fun ρ => AR (w, ρ) + AB (w, ρ)) ρ0 (Pi.single i 1)‖ ≤
      p11SlowCZ C * (eps + p11eta1 C eps) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -, hMF⟩ := fast_consts hC
  have hM0 : 0 < C.MF := by linarith
  obtain ⟨hARd, hABd, hARb, hABb, -⟩ := hP
  have hpi := Real.pi_pos
  have hη0 := p11eta1_pos hC heps hεM
  have hr : 0 < C.rz / 2 := by positivity
  set r := C.rz / 2 with hrdef
  have hr2 : 128 * eps < 4 * r ^ 2 := by rw [hrdef]; nlinarith
  have hc : ‖(fun _ => (2 * Real.pi * eps : ℂ) : P11CVec n)‖ ≤ 2 * Real.pi * eps := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hρ03 : ‖ρ0‖ < 3 * Real.pi * eps := by
    have := norm_le_norm_sub_add ρ0 (fun _ => (2 * Real.pi * eps : ℂ) : P11CVec n)
    linarith
  set U := ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) with hU
  have hU' : IsOpen U := isOpen_ball
  -- radii
  have hA : ‖fderiv ℂ (fun ρ => AR (w, ρ)) ρ0 (Pi.single i 1)‖ ≤
      2 ^ (2 * n) * (C.MF / 16) * (784 / (Real.pi * r ^ 4)) * eps := by
    have hball : ball ρ0 (Real.pi * eps / 2) ⊆ ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4) := by
      intro ρ hρ
      rw [mem_ball_iff_norm] at hρ
      rw [mem_ball_zero_iff]
      have := norm_le_norm_sub_add ρ ρ0
      nlinarith [mul_pos hpi hr]
    have hK : ∀ J ∈ U, ∀ ρ ∈ ball ρ0 (Real.pi * eps / 2),
        ‖AR (J, ρ)‖ ≤ 2 ^ (2 * n) * (C.MF / 16) * (196 * eps ^ 2 / r ^ 4) := by
      intro J hJ ρ hρ
      have hρ' := mem_ball_iff_norm.1 hρ
      have hn := norm_le_norm_sub_add ρ ρ0
      refine (hARb (J, ρ) ⟨hJ, hball hρ⟩).trans ?_
      simp only
      have h1 : 4 * ‖ρ‖ / (Real.pi * r ^ 2) ≤ 14 * eps / r ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hr 2]
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      calc 2 ^ (2 * n) * (C.MF / 16) * (4 * ‖ρ‖ / (Real.pi * r ^ 2)) ^ 2
          ≤ 2 ^ (2 * n) * (C.MF / 16) * (14 * eps / r ^ 2) ^ 2 := by gcongr
        _ = _ := by field_simp; ring
    have := p11_rho_cauchy hARd (δ := Real.pi * eps / 4) (δ' := Real.pi * eps / 2)
      (by positivity) (by nlinarith [mul_pos hpi heps]) (hball) hK hw i
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hB : ‖fderiv ℂ (fun ρ => AB (w, ρ)) ρ0 (Pi.single i 1)‖ ≤
      2 ^ (2 * n) * (16 / (Real.pi * r ^ 2)) * p11eta1 C eps := by
    have hball : ball ρ0 (Real.pi * r ^ 2 / 8) ⊆ ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4) := by
      intro ρ hρ
      rw [mem_ball_iff_norm] at hρ
      rw [mem_ball_zero_iff]
      have := norm_le_norm_sub_add ρ ρ0
      nlinarith [mul_pos hpi hr, mul_pos hpi heps]
    have hK : ∀ J ∈ U, ∀ ρ ∈ ball ρ0 (Real.pi * r ^ 2 / 8),
        ‖AB (J, ρ)‖ ≤ 2 ^ (2 * n) * p11eta1 C eps := fun J hJ ρ hρ =>
      hABb (J, ρ) ⟨hJ, hball hρ⟩
    have := p11_rho_cauchy hABd (δ := Real.pi * r ^ 2 / 16) (δ' := Real.pi * r ^ 2 / 8)
      (by positivity) (by nlinarith [mul_pos hpi (pow_pos hr 2)]) hball hK hw i
    refine this.trans (le_of_eq ?_)
    field_simp
  have hρm : ρ0 ∈ ball (0 : P11CVec n) (Real.pi * r ^ 2 / 4) := by
    rw [mem_ball_zero_iff]; nlinarith [mul_pos hpi hr, mul_pos hpi heps]
  have hsum : fderiv ℂ (fun ρ => AR (w, ρ) + AB (w, ρ)) ρ0 (Pi.single i 1) =
      fderiv ℂ (fun ρ => AR (w, ρ)) ρ0 (Pi.single i 1) +
        fderiv ℂ (fun ρ => AB (w, ρ)) ρ0 (Pi.single i 1) := by
    have hfun : (fun ρ => AR (w, ρ) + AB (w, ρ)) =
        (fun ρ => AR (w, ρ)) + (fun ρ => AB (w, ρ)) := rfl
    rw [hfun, fderiv_add (p11_diffAt_rho hU' hARd hw hρm) (p11_diffAt_rho hU' hABd hw hρm)]
    rfl
  rw [hsum]
  refine (norm_add_le _ _).trans ?_
  have hc1 : 2 ^ (2 * n) * (C.MF / 16) * (784 / (Real.pi * r ^ 4)) ≤ p11SlowCZ C := by
    unfold p11SlowCZ
    have : 0 ≤ 2 ^ (2 * n) * (16 / (Real.pi * (C.rz / 2) ^ 2)) := by positivity
    linarith
  have hc2 : 2 ^ (2 * n) * (16 / (Real.pi * r ^ 2)) ≤ p11SlowCZ C := by
    unfold p11SlowCZ
    have : 0 ≤ 2 ^ (2 * n) * (C.MF / 16) * (784 / (Real.pi * (C.rz / 2) ^ 4)) := by
      positivity
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hc1 heps.le, mul_le_mul_of_nonneg_right hc2 hη0.le]

/-- The `J`-jet clause for `∂ρ̃ Ẑ` of `P11SlowSpec` (graph step `as-osc`; Cauchy radius `s₁/4`). -/
theorem p11_slow_Z_jets (hC : P11SecularSpec D C) {eps : ℝ} (Fast : P11FastData n)
    (heps : 0 < eps) (hεM : eps * C.MF ≤ Real.exp (-1)) (hsm : 128 * eps < C.rz ^ 2)
    {AR AB : P11CVec n × P11CVec n → ℂ} (hP : P11SlowPolarOut C Fast eps AR AB) {c : ℝ}
    (hc : p11SlowCZ C ≤ c) :
    ∀ alpha : Fin n → ℕ, ∀ J : P11CVec n, ‖J - KAM.realInclusion n C.J0‖ < p11s1 C eps / 4 →
      ∀ rho : P11CVec n, ‖rho - (fun _ => (2 * Real.pi * eps : ℂ))‖ < Real.pi * eps →
        ‖p11PartialVec alpha (fun J : P11CVec n => fun i : Fin n =>
            fderiv ℂ (fun rho : P11CVec n => p11SlowZ AR AB (Fin.append J rho)) rho
              (Pi.single i 1)) J‖ ≤
          c * (eps + p11eta1 C eps) * (∏ i, ((alpha i).factorial : ℝ)) *
            (4 / p11s1 C eps) ^ (∑ i, alpha i) := by
  obtain ⟨-, -, -, -, -, -, -, hrz0, -, hMF⟩ := fast_consts hC
  have hs0 := p11s1_pos hC heps hεM
  have hpi := Real.pi_pos
  have hη0 := p11eta1_pos hC heps hεM
  intro alpha J hJ rho hrho
  simp only [p11SlowZ_append]
  obtain ⟨hARd, hABd, -⟩ := id hP
  have hr : 0 < C.rz / 2 := by positivity
  have hcn : ‖(fun _ => (2 * Real.pi * eps : ℂ) : P11CVec n)‖ ≤ 2 * Real.pi * eps := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [show (2 * Real.pi * eps : ℂ) = ((2 * Real.pi * eps : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hρ3 : ‖rho‖ < 3 * Real.pi * eps := by
    have := norm_le_norm_sub_add rho (fun _ => (2 * Real.pi * eps : ℂ) : P11CVec n)
    linarith [hcn]
  have hρm : rho ∈ ball (0 : P11CVec n) (Real.pi * (C.rz / 2) ^ 2 / 4) := by
    rw [mem_ball_zero_iff]; nlinarith [mul_pos hpi hr, mul_pos hpi heps]
  have hJs : closedBall J (p11s1 C eps / 4) ⊆
      ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2) := by
    intro w hw
    rw [mem_closedBall_iff_norm] at hw
    rw [mem_ball_iff_norm]
    have := norm_le_norm_sub_add (w - KAM.realInclusion n C.J0) (J - KAM.realInclusion n C.J0)
    have h3 : w - KAM.realInclusion n C.J0 = (w - J) + (J - KAM.realInclusion n C.J0) := by abel
    rw [h3]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    linarith
  have hM0 : 0 ≤ p11SlowCZ C * (eps + p11eta1 C eps) := by
    have hM : 0 < C.MF := by linarith
    have : 0 ≤ p11SlowCZ C := by unfold p11SlowCZ; positivity
    positivity
  have hmain := p11_partial_rho_jet (U := ball (KAM.realInclusion n C.J0) (p11s1 C eps / 2))
    isOpen_ball (Zq := fun p => AR p + AB p) (hARd.add hABd) hρm hM0
    (fun w hw i => p11_slow_rho_bound hC Fast heps hεM hsm hP hrho hw i)
    (by linarith : 0 < p11s1 C eps / 4) hJs alpha
  refine hmain.trans ?_
  have e : (4 / p11s1 C eps) ^ (∑ i, alpha i) = 1 / (p11s1 C eps / 4) ^ (∑ i, alpha i) := by
    rw [← inv_div, inv_pow, one_div]
  rw [e]
  have hfac : 0 ≤ ∏ i, ((alpha i).factorial : ℝ) := by positivity
  have hpow : 0 < (p11s1 C eps / 4) ^ (∑ i, alpha i) := by positivity
  have hle : p11SlowCZ C * (eps + p11eta1 C eps) ≤ c * (eps + p11eta1 C eps) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  calc (∏ i, ((alpha i).factorial : ℝ)) * (p11SlowCZ C * (eps + p11eta1 C eps)) /
        (p11s1 C eps / 4) ^ (∑ i, alpha i)
      = (p11SlowCZ C * (eps + p11eta1 C eps)) * (∏ i, ((alpha i).factorial : ℝ)) *
        (1 / (p11s1 C eps / 4) ^ (∑ i, alpha i)) := by ring
    _ ≤ (c * (eps + p11eta1 C eps)) * (∏ i, ((alpha i).factorial : ℝ)) *
        (1 / (p11s1 C eps / 4) ^ (∑ i, alpha i)) := by gcongr

end Jet

end KAM.Planetary

end
