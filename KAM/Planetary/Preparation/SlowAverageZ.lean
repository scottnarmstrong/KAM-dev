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
  obtain ⟨-, -, -, -, hGd, -, -, -, -, -, -, -, -, hGb, -⟩ := hF
  have hGbd : DifferentiableOn ℂ (p11Gbar C Fast) (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) := by
    have h1 : DifferentiableOn ℂ Fast.G (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) := hGd
    have h2 := (p11FastMean_differentiableOn hC).mono
      (show Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2) ⊆
        ball (KAM.realInclusion n C.J0) (2 * C.rC) ×ˢ ball (0 : P11Phase n) C.rz from
        prod_mono hsub hsubz)
    exact h1.sub h2
  have hη0 : 0 < p11eta1 C eps := by
    obtain ⟨hα, -⟩ := p11_alpha_le hC heps hεM
    obtain ⟨hd, -⟩ := p11d1_le hC heps hεM
    unfold p11eta1
    have : (0 : ℝ) < (1 + n) := by positivity
    positivity
  have hGbb : p11Bound (Dm ×ˢ ball (0 : P11Phase n) (C.rz / 2)) (p11Gbar C Fast)
      (p11eta1 C eps) := by
    rintro ⟨J, z⟩ ⟨hJ, hz⟩
    exact hGb J (mem_ball_iff_norm.1 hJ) z (mem_ball_zero_iff.1 hz)
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

end KAM.Planetary

end
