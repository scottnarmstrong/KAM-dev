/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.PairJet.Defs
public import KAM.Planetary.PlanarTorsion.PairJet.Diag

/-!
# Planar quartic torsion: the polynomial `p11c_pairJet` along lines

Blueprint P, Part 11b (`stepP:p11b:pj-formal`): `p11c_pairJet a` is an even polynomial of degree
    four
in the coordinates of `z`, analytic everywhere, with `p11c_pairJet a (t • w) = β₀ + t² P₂(w) + t⁴
    P₄(w)`.
Its diagonal derivatives at `0` are therefore `j! [t^j]`.  The coordinates `ζ₁ = z.1 0 + i z.2 0`,
`ζ₂ = z.1 1 + i z.2 1` express `P₂, P₄` through `|ζ_k|²` and `Re(ζ̄₁ ζ₂)`.
-/

@[expose] public noncomputable section
open Set Real Filter Topology
namespace KAM.Planetary
open KAM.Planetary.OrbitJet

theorem p11c_slowLength_sq (z : Phase 2) :
    p11c_slowLength z ^ 2 = z.1 0 ^ 2 + z.2 0 ^ 2 + z.1 1 ^ 2 + z.2 1 ^ 2 := by
  unfold p11c_slowLength
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  simp [Fin.sum_univ_two]
  ring

/-- The quadratic part of the pair jet. -/
def p11cPJP2 (a : ℝ) (w : Phase 2) : ℝ :=
  p11c_pairCoeffs a 0 * p11c_slowLength w ^ 2 + p11c_pairCoeffs a 1 * p11c_pairDot w

/-- The quartic part of the pair jet. -/
def p11cPJP4 (a : ℝ) (w : Phase 2) : ℝ :=
  p11c_quartic (fun i => p11c_pairCoeffs a (i.castAdd 2 + 2)) w

theorem p11c_pairJet_smul (a t : ℝ) (w : Phase 2) :
    p11c_pairJet a (t • w) = p11c_laplace (1 / 2) 0 a + t ^ 2 * p11cPJP2 a w + t ^ 4 * p11cPJP4 a w
        := by
  have h1 : p11c_slowLength (t • w) ^ 2 = t ^ 2 * p11c_slowLength w ^ 2 := by
    rw [p11c_slowLength_sq, p11c_slowLength_sq]
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    ring
  unfold p11c_pairJet p11cPJP2 p11cPJP4 p11c_quartic p11c_pairDot
  rw [h1]
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring

theorem p11c_pairJet_neg (a : ℝ) (z : Phase 2) : p11c_pairJet a (-z) = p11c_pairJet a z := by
  have := p11c_pairJet_smul a (-1) z
  rw [show (-z) = (-1 : ℝ) • z by simp, this]
  have h2 := p11c_pairJet_smul a 1 z
  simp only [one_smul] at h2
  rw [h2]; ring

theorem p11c_pairJet_analyticAt (a : ℝ) : AnalyticAt ℝ (p11c_pairJet a) 0 := by
  have hx : ∀ i, AnalyticAt ℝ (fun z : Phase 2 => z.1 i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt 0
  have hy : ∀ i, AnalyticAt ℝ (fun z : Phase 2 => z.2 i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))).analyticAt 0
  have hsl : AnalyticAt ℝ (fun z : Phase 2 => p11c_slowLength z ^ 2) 0 := by
    simp only [p11c_slowLength_sq]
    exact ((((hx 0).pow 2).add ((hy 0).pow 2)).add ((hx 1).pow 2)).add ((hy 1).pow 2)
  have hd : AnalyticAt ℝ (fun z : Phase 2 => p11c_pairDot z) 0 := by
    simp only [p11c_pairDot]
    exact ((hx 0).mul (hx 1)).add ((hy 0).mul (hy 1))
  have hA : AnalyticAt ℝ (fun z : Phase 2 => z.1 0 ^ 2 + z.2 0 ^ 2) 0 :=
    ((hx 0).pow 2).add ((hy 0).pow 2)
  have hB : AnalyticAt ℝ (fun z : Phase 2 => z.1 1 ^ 2 + z.2 1 ^ 2) 0 :=
    ((hx 1).pow 2).add ((hy 1).pow 2)
  have hq : AnalyticAt ℝ (fun z : Phase 2 =>
      p11c_quartic (fun i => p11c_pairCoeffs a (i.castAdd 2 + 2)) z) 0 := by
    unfold p11c_quartic
    simp only
    fun_prop
  unfold p11c_pairJet
  fun_prop

/-- The jet of the pair jet along a line is exact. -/
theorem p11c_pairJet_isJet (a : ℝ) (w : Phase 2) :
    IsJet (fun t : ℝ => ((p11c_pairJet a (t • w) : ℝ) : ℂ))
      ⟨((p11c_laplace (1 / 2) 0 a : ℝ) : ℂ), 0, ((p11cPJP2 a w : ℝ) : ℂ), 0,
        ((p11cPJP4 a w : ℝ) : ℂ)⟩ := by
  have : ∀ t : ℝ, ((p11c_pairJet a (t • w) : ℝ) : ℂ) = Jet5.ev
      ⟨((p11c_laplace (1 / 2) 0 a : ℝ) : ℂ), 0, ((p11cPJP2 a w : ℝ) : ℂ), 0,
        ((p11cPJP4 a w : ℝ) : ℂ)⟩ t := by
    intro t
    rw [p11c_pairJet_smul]
    simp only [Jet5.ev]
    push_cast
    ring
  exact (isJet_ev _).congr fun t => (this t).symm

end KAM.Planetary

end
