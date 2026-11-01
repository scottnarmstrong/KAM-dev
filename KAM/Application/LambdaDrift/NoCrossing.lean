/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.Bridge
public import KAM.Frozen.Planetary.StrongAMD.Theorems.PlanarStrongAMDBarrier
public import KAM.Planetary.StrongAMD.Confinement
public import KAM.Planetary.StrongAMD.SourceCarrier

/-!
# No orbit crossing from a certified Λ-drift

Design `docs/campaign/design/HD11964-PILOT.md` §2–§3, for any planar system of `n ≥ 2` planets.

* `DriftData`, `DriftData.ok`: the rational drift data `(η, lo, hi, T, d, r)` of an
  approximate-integral certificate and its decided arithmetic (`driftOk` of design §6.3).
* `noCrossing_of_stoppedDrift`: **conditional helper** — LP-CONF's
  `strongFirstExit_of_stopped_drift` composed with LP0 (`planar_strongAMD_barrier`): from LP-LIFT's
  `LiftData` and LP-CONF's own `hstop` hypothesis, existence, uniqueness and LP0's separations on
  `[-T, T]`.
* `noCrossing_of_approxIntegrals`: the same with `hstop` discharged by the Λ-drift bridge
  (`stoppedDrift_of_approxIntegrals`): from `LiftData`, decided drift data and an
  approximate-integral certificate (the per-region bounds `hη`, `hG`) to "no orbit crossing for
  `|t| ≤ T`".

The separation constants `dStar`, `dPair` are those of LP0 for `(ν, U, δ / 2)`: they are chosen
before the initial state, the mass parameter `μ`, the certificate and the horizon.
-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Planetary.StrongAMD

namespace KAM.Application.LambdaDrift

variable {n : ℕ}

/-- Rational drift data of an approximate-integral certificate (design §6.3): the bounds `η_i` on
`|{F_i, H}|`, the range `[lo_i, hi_i]` of `F_i - Λ_i`, the horizon `T`, the certified drift `d` and
the tube radius `r` of `LiftData`. -/
structure DriftData (n : ℕ) where
  /-- Bound on the bracket `|dF_i (X_H)|` over the region. -/
  eta : Fin n → ℚ
  /-- Lower end of the range of `F_i - Λ_i` over the region. -/
  lo : Fin n → ℚ
  /-- Upper end of the range of `F_i - Λ_i` over the region. -/
  hi : Fin n → ℚ
  /-- The horizon, in model time units. -/
  T : ℚ
  /-- The certified action drift. -/
  d : ℚ
  /-- The tube radius of `LiftData`. -/
  r : ℚ

/-- The decided arithmetic of the drift data: `0 < T`, `0 < d`, `2 d ≤ r` and
`η_i T + (hi_i - lo_i) < d` for every `i` (`driftOk`, design §6.3). -/
def DriftData.ok (D : DriftData n) : Bool :=
  decide (0 < D.T) && decide (0 < D.d) && decide (2 * D.d ≤ D.r) &&
    decide (∀ i, D.eta i * D.T + (D.hi i - D.lo i) < D.d)

/-- What `DriftData.ok` decides, over `ℝ`. -/
theorem DriftData.ok_spec {D : DriftData n} (h : D.ok = true) :
    (0 : ℝ) < D.T ∧ (0 : ℝ) < D.d ∧ (D.d : ℝ) ≤ D.r / 2 ∧
      ∀ i, (D.eta i : ℝ) * D.T + (D.hi i - D.lo i) < D.d := by
  simp only [DriftData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hT, hd⟩, hdr⟩, hη⟩ := h
  refine ⟨by exact_mod_cast hT, by exact_mod_cast hd, ?_, fun i => by exact_mod_cast hη i⟩
  have : ((2 * D.d : ℚ) : ℝ) ≤ D.r := by exact_mod_cast hdr
  push_cast at this
  linarith

/-- **Conditional helper (LP-CONF's `hstop` as a hypothesis; not a source result).**
`strongFirstExit_of_stopped_drift` composed with LP0: for the data `LiftData ν U z₀ δ r` and the
stopped drift `hstop` up to `T`, there is a unique moving solution on `[-T, T]` from `z₀`, and along
it the osculating perihelia, the adjacent annulus gaps, the star distances and the pair distances
stay above LP0's constants `dStar`, `dPair` for `(ν, U, δ / 2)`. -/
theorem noCrossing_of_stoppedDrift (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hUc : IsCompact U) (hUch : U ⊆ chamber ν) (δ : ℝ) (hδ : 0 < δ) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (z₀ : Phase (n * 2)) (r μ T : ℝ), LiftData ν U z₀ δ r → 0 < T →
        (∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z : ℝ → Phase (n * 2),
          IsMovingSolutionOn ν μ J z → z 0 = z₀ → ∀ t ∈ J, |t| ≤ T →
            StoppedOn ν z₀ δ r z t →
            ‖actionVector ν (z t) - actionVector ν z₀‖ ≤ r / 2) →
        ∃ z : ℝ → Phase (n * 2), z 0 = z₀ ∧ IsMovingSolutionOn ν μ (Icc (-T) T) z ∧
          MovingUniqueOn ν μ (Icc (-T) T) z ∧
          ∀ t ∈ Icc (-T) T,
            (∀ i, dStar ≤ keplerAxis ν (z t) i * (1 - planeLength (keplerEccVector ν (z t) i))) ∧
            (∀ a : AdjIdx n, dPair ≤ keplerAxis ν (z t) a.upperIdx *
                (1 - planeLength (keplerEccVector ν (z t) a.upperIdx)) -
              keplerAxis ν (z t) a.1 * (1 + planeLength (keplerEccVector ν (z t) a.1))) ∧
            (∀ i, dStar ≤ planeLength (bodyVector (z t).1 i)) ∧
            (∀ i j, i ≠ j → dPair ≤ planeLength (bodyVector (z t).1 i - bodyVector (z t).1 j)) := by
  obtain ⟨dStar, dPair, hdS, hdP, -, _K, -, -, hsep⟩ :=
    planar_strongAMD_barrier hn ν hν U hUc hUch (δ / 2) (half_pos hδ)
  refine ⟨dStar, dPair, hdS, hdP, fun z₀ r μ T hd hT hstop => ?_⟩
  obtain ⟨z, hz0, hsol, huniq, hall⟩ := strongFirstExit_of_stopped_drift hν hn hUc hUch
    hd.delta_pos hd.r_pos hT hd.budget hd.physical hd.ball hd.amd hstop
  refine ⟨z, hz0, hsol, huniq, fun t ht => ?_⟩
  obtain ⟨hphys, hΛ, hC⟩ := (hall t ht).2.2.2
  have hsrc : sourceStrongAMD (⟨z t, ⟨hν, hphys⟩⟩ : SourceCanonicalPhase n ν) ≤
      orderedStrongThreshold hn ⟨_, hUch hΛ⟩ - δ / 2 := by
    rw [sourceStrongAMD_eq, orderedStrongThreshold_eq]
    exact hC
  obtain ⟨h1, h2, h3, h4, -⟩ := hsep (z t) hphys hΛ ⟨hν, hphys⟩ hsrc
  exact ⟨h1, h2, h3, h4⟩

/-- **No orbit crossing from a certified Λ-drift** (design §2–§4), for any planar system.

Fix the masses `ν`, a compact action set `U` in the chamber and a margin `δ > 0`; LP0 gives the
separation constants `dStar`, `dPair`. Then for every decided drift data `D`, every `μ`, every
initial state `z₀` with LP-LIFT's `LiftData ν U z₀ δ D.r`, and every approximate-integral
certificate (`F` differentiable on the open `O ⊇ R`, `R` containing the chart states reachable with
drift `≤ d`, `|dF_i (X_H)| ≤ η_i` and `lo_i ≤ F_i - Λ_i ≤ hi_i` on `R`), the moving solution from
`z₀` exists and is unique on `[-T, T]`, and along it the orbits keep LP0's separations: they never
cross. -/
theorem noCrossing_of_approxIntegrals (hn : 2 ≤ n) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (U : Set (Fin n → ℝ)) (hUc : IsCompact U) (hUch : U ⊆ chamber ν) (δ : ℝ) (hδ : 0 < δ) :
    ∃ dStar dPair : ℝ, 0 < dStar ∧ 0 < dPair ∧
      ∀ (D : DriftData n), D.ok = true → ∀ (μ : ℝ) (z₀ : Phase (n * 2)),
        LiftData ν U z₀ δ D.r →
        ∀ (F : Fin n → Phase (n + n) → ℝ) (R O : Set (Phase (n + n))),
          IsOpen O → R ⊆ O → (∀ i, DifferentiableOn ℝ (F i) O) →
          (∀ w ∈ chartSafe ν, (∀ i, |fast w.2 i - actionVector ν z₀ i| ≤ D.d) →
            chartAMD w ≤ strongAMD ν z₀ + n * D.d → w ∈ R) →
          (∀ i, ∀ w ∈ R,
            |fderiv ℝ (F i) w (hamiltonianVectorField (liftChartHam ν μ) w)| ≤ D.eta i) →
          (∀ i, ∀ w ∈ R, (D.lo i : ℝ) ≤ F i w - fast w.2 i ∧ F i w - fast w.2 i ≤ D.hi i) →
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
  refine ⟨dStar, dPair, hdS, hdP, fun D hD μ z₀ hd F R O hO hRO hF hR hη hG => ?_⟩
  obtain ⟨hT0, hd0, hdr, hTd⟩ := D.ok_spec hD
  exact hmain z₀ D.r μ D.T hd hT0
    (stoppedDrift_of_approxIntegrals hd F R O (fun i => (D.eta i : ℝ)) (fun i => (D.lo i : ℝ))
      (fun i => (D.hi i : ℝ)) hO hRO hF hR hη hG hd0 hTd hdr)

end KAM.Application.LambdaDrift

end
