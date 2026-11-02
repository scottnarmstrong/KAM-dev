/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.NoCrossing
public import KAM.Application.LambdaDrift.ObservableBridge

/-!
# No orbit crossing from a certified Λ-drift, the first exit driven by an observable

Scoping note `docs/tracks/LP/REDUCED-MASS-SCOPE.md` §4, for any planar system of `n ≥ 2` planets.
The observable counterpart of `noCrossing_of_approxIntegrals` (`NoCrossing.lean`).

* `ObsDriftData`, `ObsDriftData.ok`: the rational drift data `(η, lo, hi, loG, hiG, ε, T, d, r)` of
  an approximate-integral certificate for an observable `G` and its decided arithmetic.
* `noCrossing_of_approxIntegrals_obs`: `noCrossing_of_stoppedDrift` with `hstop` discharged by the
  observable bridge (`stoppedDrift_of_approxIntegrals_obs`): from `LiftData`, decided drift data,
  the range of `G - Λ` on the chart tube and an approximate-integral certificate for `G` (the
  per-region bounds `hη`, `hFG`) to "no orbit crossing for `|t| ≤ T`".

The separation constants `dStar`, `dPair` are those of LP0 for `(ν, U, δ / 2)`: they are chosen
before the initial state, the mass parameter `μ`, the observable, the certificate and the horizon.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-- Rational drift data of an approximate-integral certificate for an observable `G`: the bounds
`η_i` on `|{F_i, H}|`, the range `[lo_i, hi_i]` of `F_i - G_i` over the region, the range
`[loG_i, hiG_i]` of `G_i - Λ_i` over the chart tube and its bound `ε`, the horizon `T`, the
certified `G`-drift `d` and the tube radius `r` of `LiftData`. -/
structure ObsDriftData (n : ℕ) where
  /-- Bound on the bracket `|dF_i (X_H)|` over the region. -/
  eta : Fin n → ℚ
  /-- Lower end of the range of `F_i - G_i` over the region. -/
  lo : Fin n → ℚ
  /-- Upper end of the range of `F_i - G_i` over the region. -/
  hi : Fin n → ℚ
  /-- Lower end of the range of `G_i - Λ_i` over the chart tube. -/
  loG : Fin n → ℚ
  /-- Upper end of the range of `G_i - Λ_i` over the chart tube. -/
  hiG : Fin n → ℚ
  /-- A bound on the widths `hiG_i - loG_i`. -/
  eps : ℚ
  /-- The horizon, in model time units. -/
  T : ℚ
  /-- The certified drift of the observable. -/
  d : ℚ
  /-- The tube radius of `LiftData`. -/
  r : ℚ

/-- The decided arithmetic of the observable drift data: `0 < T`, `0 < d`, `2 (d + ε) ≤ r`,
`η_i T + (hi_i - lo_i) < d` and `hiG_i - loG_i ≤ ε` for every `i`. -/
def ObsDriftData.ok (D : ObsDriftData n) : Bool :=
  decide (0 < D.T) && decide (0 < D.d) && decide (2 * (D.d + D.eps) ≤ D.r) &&
    decide (∀ i, D.eta i * D.T + (D.hi i - D.lo i) < D.d) &&
    decide (∀ i, D.hiG i - D.loG i ≤ D.eps)

/-- What `ObsDriftData.ok` decides, over `ℝ`. -/
theorem ObsDriftData.ok_spec {D : ObsDriftData n} (h : D.ok = true) :
    (0 : ℝ) < D.T ∧ (0 : ℝ) < D.d ∧ (D.d : ℝ) + D.eps ≤ D.r / 2 ∧
      (∀ i, (D.eta i : ℝ) * D.T + (D.hi i - D.lo i) < D.d) ∧
      ∀ i, (D.hiG i : ℝ) - D.loG i ≤ D.eps := by
  simp only [ObsDriftData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hT, hd⟩, hdr⟩, hη⟩, hε⟩ := h
  refine ⟨by exact_mod_cast hT, by exact_mod_cast hd, ?_, fun i => by exact_mod_cast hη i,
    fun i => by exact_mod_cast hε i⟩
  have : ((2 * (D.d + D.eps) : ℚ) : ℝ) ≤ D.r := by exact_mod_cast hdr
  push_cast at this
  linarith

/-- **No orbit crossing from a certified Λ-drift, driven by an observable** (scoping note §4), for
any planar system.

Fix the masses `ν`, a compact action set `U` in the chamber and a margin `δ > 0`; LP0 gives the
separation constants `dStar`, `dPair`. Then for every decided drift data `D`, every `μ`, every
initial state `z₀` with LP-LIFT's `LiftData ν U z₀ δ D.r`, every observable `G` continuous on the
chart tube with `loG_i ≤ G_i - Λ_i ≤ hiG_i` there, and every approximate-integral certificate for
`G` (`F` differentiable on the open `O ⊇ R`, `R` containing the chart states reachable with
`G`-drift `≤ d`, action drift `≤ d + ε` and chart AMD `≤ C(z₀) + n (d + ε)`, `|dF_i (X_H)| ≤ η_i`
and `lo_i ≤ F_i - G_i ≤ hi_i` on `R`), the moving solution from `z₀` exists and is unique on
`[-T, T]`, and along it the orbits keep LP0's separations: they never cross. -/
theorem noCrossing_of_approxIntegrals_obs (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hUc : IsCompact U) (hUch : U ⊆ chamber ν) (δ : ℝ) (hδ : 0 < δ) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : ObsDriftData n), D.ok = true → ∀ (μ : ℝ) (z₀ : Phase (n * 2)),
        LiftData ν U z₀ δ D.r →
        ∀ (G F : Fin n → Phase (n + n) → ℝ) (R O : Set (Phase (n + n))),
          (∀ i, ContinuousOn (G i) (chartTube ν z₀ D.r)) →
          (∀ i, ∀ w ∈ chartTube ν z₀ D.r,
            (D.loG i : ℝ) ≤ G i w - fast w.2 i ∧ G i w - fast w.2 i ≤ D.hiG i) →
          IsOpen O → R ⊆ O → (∀ i, DifferentiableOn ℝ (F i) O) →
          (∀ w₀ ∈ chartSafe ν, poincareProd ν 1 w₀ = z₀ → ∀ w ∈ chartSafe ν,
            (∀ i, |G i w - G i w₀| ≤ D.d) →
            (∀ i, |fast w.2 i - actionVector ν z₀ i| ≤ (D.d : ℝ) + D.eps) →
            chartAMD w ≤ strongAMD ν z₀ + n * ((D.d : ℝ) + D.eps) → w ∈ R) →
          (∀ i, ∀ w ∈ R,
            |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ D.eta i) →
          (∀ i, ∀ w ∈ R, (D.lo i : ℝ) ≤ F i w - G i w ∧ F i w - G i w ≤ D.hi i) →
          ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧
            IsMovingSolutionOn ν μ (Icc (-(D.T : ℝ)) D.T) z ∧
            MovingUniqueOn ν μ (Icc (-(D.T : ℝ)) D.T) z ∧
            ∀ t ∈ Icc (-(D.T : ℝ)) D.T,
              (∀ i, dStar ≤
                keplerAxis ν (z t) i * (1 - planeLength (keplerEccVector ν (z t) i))) ∧
              (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                  (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
                keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
              (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
              (∀ i j, i ≠ j →
                dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) := by
  obtain ⟨dStar, dPair, hdS, hdP, hmain⟩ := noCrossing_of_stoppedDrift hn ν hν U hUc hUch δ hδ
  refine ⟨dStar, dPair, hdS, hdP,
    fun D hD μ z₀ hd G F R O hGc hGΛ hO hRO hF hR hη hFG => ?_⟩
  obtain ⟨hT0, hd0, hdr, hTd, hε⟩ := D.ok_spec hD
  exact hmain z₀ D.r μ D.T hd hT0
    (stoppedDrift_of_approxIntegrals_obs hd G F R O (fun i => (D.eta i : ℝ))
      (fun i => (D.lo i : ℝ)) (fun i => (D.hi i : ℝ)) (fun i => (D.loG i : ℝ))
      (fun i => (D.hiG i : ℝ)) hO hRO hF hGc hGΛ hR hη hFG hd0 hTd hε hdr)

end KAM.Application.LambdaDrift

end
