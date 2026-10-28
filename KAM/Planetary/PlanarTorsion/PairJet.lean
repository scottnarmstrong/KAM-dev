/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Defs
public import KAM.Planetary.PlanarTorsion.PairJet.Bridge
public import KAM.Planetary.PlanarTorsion.PairJet.Diag
public import KAM.Planetary.PlanarTorsion.PairJet.Diff
public import KAM.Planetary.PlanarTorsion.PairJet.PolyJet
public import KAM.Planetary.PlanarTorsion.PairJet.Ray
public import KAM.Planetary.PlanarTorsion.PairJet.Combine2
public import KAM.Planetary.PlanarTorsion.PairJet.Combine4

/-!
# Planar quartic torsion: the actual averaged interaction `pair_jet` (P11C, package T5)

Blueprint P, Part 11b (`bpP:p11b:pair-jet`; steps `pj-formal`, `pj-bin`, `pj-avg`, `pj-red`).  The pair
average `p11c_pairAverage a` is real analytic at `0` and its jet of order five is `p11c_pairJet a`.

*Proof.*  Analyticity and evenness come from the Part-8 secular average (`PairJet/Bridge`).  For the jet
we compare diagonal derivatives (`PairJet/Diag`): those of the average are the averages of those of the
integrand (`PairJet/Diff`), those of the integrand along a line are the coefficients of the binomial
expansion of `N^{-1/2}` for the jet `N` of `|α z₁ - z₂|²` (`PairJet/Ray`), averaged over the torus by
Fourier selection (`PairJet/Average`, `PairJet/Terms`, `PairJet/Piece*`) and reduced to
`b_{1/2}^{(0)}, b_{1/2}^{(1)}` (`PairJet/Reduction`, `PairJet/Combine*`); odd orders vanish by evenness.
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Filter Topology
open scoped ContDiff
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

private theorem pjF_zeta_prod (x y : ℝ) :
    ((x : ℂ) + Complex.I * (y : ℂ)) * ((x : ℂ) - Complex.I * (y : ℂ)) =
      ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(y : ℂ) ^ 2) * Complex.I_sq

private theorem pjF_zeta_dot (x0 y0 x1 y1 : ℝ) :
    (((x0 : ℂ) - Complex.I * (y0 : ℂ)) * ((x1 : ℂ) + Complex.I * (y1 : ℂ)) +
      ((x0 : ℂ) + Complex.I * (y0 : ℂ)) * ((x1 : ℂ) - Complex.I * (y1 : ℂ))) / 2 =
      ((x0 * x1 + y0 * y1 : ℝ) : ℂ) := by
  push_cast
  linear_combination (-(y0 : ℂ) * (y1 : ℂ)) * Complex.I_sq

/-- The mean of the leading term of the jet. -/
theorem p11cPJ_avg0 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (ζ1 ζb1 ζ2 ζb2 : ℂ) :
    ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
        (p11cPJcJet (p11cPJrotN a ζ1 ζb1 ζ2 ζb2 l) ((p11cPJS a (l 0 - l 1) : ℝ) : ℂ)).a0 =
      ((2 * π : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ) * ((p11c_laplace (1 / 2) 0 a : ℝ) : ℂ) := by
  have hgc : Continuous fun θ : ℝ => (((p11cPJS a θ) ^ 1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((p11cPJS_continuous ha).pow _)
  have hgp : Function.Periodic (fun θ : ℝ => (((p11cPJS a θ) ^ 1 : ℝ) : ℂ)) (2 * π) := by
    intro θ; simp only [p11cPJS_periodic a θ]
  have h := p11cPJ_cell_neutral hgc hgp 0
  have h2 := p11cPJ_laplace ha 1 0
  simp only [p11cPJE_zero, neg_zero, one_mul, pow_one] at h h2
  simp only [p11cPJcJet, p11cPJrotN]
  rw [h, h2]
  norm_num
  ring

/-- The diagonal derivative of the pair average, as an average of jet coefficients. -/
theorem p11cPJ_diag_avg {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {j : ℕ} (hj : j ≤ 4) (w : Phase 2) :
    ((iteratedFDeriv ℝ j (p11c_pairAverage a) 0 (fun _ => w) : ℝ) : ℂ) =
      (((2 * π) ^ (-2 : ℤ) : ℝ) : ℂ) * (j.factorial : ℂ) *
        ∫ l in Set.pi univ (fun _ : Fin 2 => Icc (0 : ℝ) (2 * π)),
          p11cPJcoeff (p11cPJrot a ((w.1 0 : ℂ) + Complex.I * (w.2 0 : ℂ))
            ((w.1 0 : ℂ) - Complex.I * (w.2 0 : ℂ)) ((w.1 1 : ℂ) + Complex.I * (w.2 1 : ℂ))
            ((w.1 1 : ℂ) - Complex.I * (w.2 1 : ℂ)) l) j := by
  rw [p11cPJ_diag_integral ha hj w]
  push_cast
  rw [← integral_ofReal, mul_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  exact p11cPJ_diag_coeff (p11cPJF_analyticAt ha l) w (p11cPJ_ray ha l w) j hj

/-- The diagonal derivatives of the pair jet. -/
theorem p11cPJ_diag_jet (a : ℝ) {j : ℕ} (hj : j ≤ 4) (w : Phase 2) :
    ((iteratedFDeriv ℝ j (p11c_pairJet a) 0 (fun _ => w) : ℝ) : ℂ) =
      (j.factorial : ℂ) * p11cPJcoeff ⟨((p11c_laplace (1 / 2) 0 a : ℝ) : ℂ), 0,
        ((p11cPJP2 a w : ℝ) : ℂ), 0, ((p11cPJP4 a w : ℝ) : ℂ)⟩ j :=
  p11cPJ_diag_coeff (p11c_pairJet_analyticAt a) w (p11c_pairJet_isJet a w) j hj

/-- `bpP:p11b:pair-jet`: the pair average is real analytic at `0` and its fifth-order jet is the
displayed quartic polynomial. -/
theorem pair_jet (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    AnalyticAt ℝ (p11c_pairAverage a) 0 ∧ p11c_JetEq 5 (p11c_pairAverage a) (p11c_pairJet a) := by
  have hW := p11cPJ_pairAverage_analyticAt ha
  have hP := p11c_pairJet_analyticAt a
  refine ⟨hW, p11cPJ_jetEq_of_diag hW hP 5 fun j hj w => ?_⟩
  rcases Nat.even_or_odd j with hje | hjo
  · -- even orders: the Fourier computation
    have hj4 : j ≤ 4 := by
      rcases hje with ⟨k, hk⟩; omega
    apply Complex.ofReal_injective
    rw [p11cPJ_diag_avg ha hj4 w, p11cPJ_diag_jet a hj4 w]
    have hc : (((2 * π) ^ (-2 : ℤ) : ℝ) : ℂ) * (((2 * π : ℝ) : ℂ) * ((2 * π : ℝ) : ℂ)) = 1 := by
      have h : ((2 * π) ^ (-2 : ℤ) : ℝ) * ((2 * π) * (2 * π)) = 1 := by
        rw [zpow_neg, zpow_two]
        field_simp
      exact_mod_cast h
    set ζ1 : ℂ := (w.1 0 : ℂ) + Complex.I * (w.2 0 : ℂ) with hζ1
    set ζb1 : ℂ := (w.1 0 : ℂ) - Complex.I * (w.2 0 : ℂ) with hζb1
    set ζ2 : ℂ := (w.1 1 : ℂ) + Complex.I * (w.2 1 : ℂ) with hζ2
    set ζb2 : ℂ := (w.1 1 : ℂ) - Complex.I * (w.2 1 : ℂ) with hζb2
    have hA : ζ1 * ζb1 = ((w.1 0 ^ 2 + w.2 0 ^ 2 : ℝ) : ℂ) := pjF_zeta_prod _ _
    have hB : ζ2 * ζb2 = ((w.1 1 ^ 2 + w.2 1 ^ 2 : ℝ) : ℂ) := pjF_zeta_prod _ _
    have hD : (ζb1 * ζ2 + ζ1 * ζb2) / 2 = ((p11c_pairDot w : ℝ) : ℂ) := by
      have := pjF_zeta_dot (w.1 0) (w.2 0) (w.1 1) (w.2 1)
      simpa [p11c_pairDot] using this
    have hsl : ((p11c_slowLength w ^ 2 : ℝ) : ℂ) = ζ1 * ζb1 + ζ2 * ζb2 := by
      rw [hA, hB, p11c_slowLength_sq]; push_cast; ring
    interval_cases j
    · simp only [p11cPJcoeff, p11cPJrot, Nat.factorial_zero, Nat.cast_one, one_mul]
      rw [p11cPJ_avg0 ha ζ1 ζb1 ζ2 ζb2]
      rw [mul_assoc, hc]
      simp
    · exact absurd hje (by decide)
    · simp only [p11cPJcoeff, p11cPJrot]
      have h2 := p11cPJ_avg2 ha ζ1 ζb1 ζ2 ζb2
      simp only [p11cPJrotN]
      rw [h2]
      have hP2 : ((p11cPJP2 a w : ℝ) : ℂ) =
          ((p11c_pairCoeffs a 0 : ℝ) : ℂ) * (ζ1 * ζb1 + ζ2 * ζb2) +
            ((p11c_pairCoeffs a 1 : ℝ) : ℂ) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) := by
        unfold p11cPJP2
        push_cast
        rw [hD, hsl.symm]
        push_cast
        ring
      rw [hP2]
      linear_combination (((p11c_pairCoeffs a 0 : ℝ) : ℂ) * (ζ1 * ζb1 + ζ2 * ζb2) +
        ((p11c_pairCoeffs a 1 : ℝ) : ℂ) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2)) * (Nat.factorial 2 : ℂ) * hc
    · exact absurd hje (by decide)
    · simp only [p11cPJcoeff, p11cPJrot]
      have h4 := p11cPJ_avg4 ha ζ1 ζb1 ζ2 ζb2
      simp only [p11cPJrotN]
      rw [h4]
      have hc0 : ((0 : Fin 6).castAdd 2 + 2 : Fin 8) = 2 := by decide
      have hc1 : ((1 : Fin 6).castAdd 2 + 2 : Fin 8) = 3 := by decide
      have hc2 : ((2 : Fin 6).castAdd 2 + 2 : Fin 8) = 4 := by decide
      have hc3 : ((3 : Fin 6).castAdd 2 + 2 : Fin 8) = 5 := by decide
      have hc4 : ((4 : Fin 6).castAdd 2 + 2 : Fin 8) = 6 := by decide
      have hc5 : ((5 : Fin 6).castAdd 2 + 2 : Fin 8) = 7 := by decide
      have hP4 : ((p11cPJP4 a w : ℝ) : ℂ) =
          ((p11c_pairCoeffs a 2 : ℝ) : ℂ) * (ζ1 * ζb1) ^ 2 +
          ((p11c_pairCoeffs a 3 : ℝ) : ℂ) * (ζ2 * ζb2) ^ 2 +
          ((p11c_pairCoeffs a 4 : ℝ) : ℂ) * (ζ1 * ζb1) * (ζ2 * ζb2) +
          ((p11c_pairCoeffs a 5 : ℝ) : ℂ) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) ^ 2 +
          ((p11c_pairCoeffs a 6 : ℝ) : ℂ) * (ζ1 * ζb1) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) +
          ((p11c_pairCoeffs a 7 : ℝ) : ℂ) * (ζ2 * ζb2) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) := by
        unfold p11cPJP4 p11c_quartic
        simp only [hc0, hc1, hc2, hc3, hc4, hc5]
        rw [hD, hA, hB]
        push_cast
        ring
      rw [hP4]
      linear_combination (((p11c_pairCoeffs a 2 : ℝ) : ℂ) * (ζ1 * ζb1) ^ 2 +
          ((p11c_pairCoeffs a 3 : ℝ) : ℂ) * (ζ2 * ζb2) ^ 2 +
          ((p11c_pairCoeffs a 4 : ℝ) : ℂ) * (ζ1 * ζb1) * (ζ2 * ζb2) +
          ((p11c_pairCoeffs a 5 : ℝ) : ℂ) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) ^ 2 +
          ((p11c_pairCoeffs a 6 : ℝ) : ℂ) * (ζ1 * ζb1) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2) +
          ((p11c_pairCoeffs a 7 : ℝ) : ℂ) * (ζ2 * ζb2) * ((ζb1 * ζ2 + ζ1 * ζb2) / 2)) *
        (Nat.factorial 4 : ℂ) * hc
  · have h1 : iteratedFDeriv ℝ j (p11c_pairAverage a) 0 = 0 :=
      iteratedFDeriv_odd_eq_zero (p11cPJ_pairAverage_even ha) hjo
    have h2 : iteratedFDeriv ℝ j (p11c_pairJet a) 0 = 0 :=
      iteratedFDeriv_odd_eq_zero (Filter.Eventually.of_forall fun u =>
        (p11c_pairJet_neg a u).symm) hjo
    simp [h1, h2]

end KAM.Planetary

end
