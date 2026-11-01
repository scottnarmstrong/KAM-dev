/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.ChartLift.Lift
public import KAM.Planetary.Spatial.NonresonantAdapter

/-!
# The spatial premises of the Lemma 13 adapter on the stopped interval

Package LP-SP-LIFT, MAIN Lemma 14 (`LP:MAIN L14 (477–483)`) for `d = 3` with Lemma 18
(`LP:MAIN L18 (47)`, `(595–597)`) feeding MAIN Lemma 13 (`LP:MAIN L13 (429–464)`, N6); track LP,
non-frozen.  The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.

For the block `b = spatialStoppedBlock ν δ I⁰ r wₛ = ⟨I⁰, spLiftSecularBall ν δ I⁰, r, wₛ⟩ :
PartialBlock n (n + n)` and the chart lift `w` of the stopped orbit
(`spatialChartLift_of_stopped`), `spatialChartLift_premises` derives, in exactly the shape
`nonresonant_drift_of_chartDataNM` consumes (with `J := uIcc 0 t`):

* (i) the lift `w` (in `spLiftChartSafe`, projecting to `z`, solving the chart ODE of
  `spLiftChartHam ν μ`) on `uIcc 0 t`;
* (ii) `lpRescaleNM b.lam (w u) ∈ b.realDom b.rB` (outer localization);
* (iii) the stopped slow membership `(slow (w u).1, slow (w u).2) ∈ b.S` (the ball (47));
* the initial fast action `fastAction (lpRescaleNM b.lam (w 0)) = b.Ic`.

None is assumed.  `spatialStopped_drift_of_chartData` composes them with the (conditional)
adapter, to check that the shapes match; it does not discharge `hstop`.
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM KAM.Planetary KAM.Planetary.StrongAMD KAM.Nekhoroshev KAM.Weighted KAM.NormalForm Set

variable {n : ℕ}

/-- The block of MAIN Lemma 13 at the centre `I⁰` for the spatial chart: slow base
`spLiftSecularBall ν δ I⁰` (the ball (47)), action radius `r`, physical slow width `wₛ`
(`LP:MAIN L13 (429–441)`, N6). -/
def spatialStoppedBlock (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) (r wS : ℝ) :
    PartialBlock n (n + n) :=
  ⟨I0, spLiftSecularBall ν δ I0, r, wS⟩

/-- (ii) Outer localization: a chart point with real angles, action within `b.rB` of the block
centre and slow pair in the block's base rescales into the open real domain (any `n m`). -/
theorem lpRescaleNM_mem_realDom {m : ℕ} (b : PartialBlock n m) (hrB : 0 < b.rB)
    {w : Phase (n + m)} (hact : ‖fast w.2 - b.Ic‖ < b.rB) (hS : (slow w.1, slow w.2) ∈ b.S) :
    lpRescaleNM b.lam w ∈ b.realDom b.rB := by
  set I' : Fin (n + (m + m)) → ℂ := Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((slow w.1 i / b.lam : ℝ) : ℂ))
      (fun i => ((slow w.2 i / b.lam : ℝ) : ℂ))) with hI'
  refine ⟨KAM.ofReal_mem_complexStrip one_pos _, I', ⟨_, hS, rfl⟩, ?_⟩
  refine (pi_norm_lt_iff hrB).2 fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · have h1 := norm_le_pi_norm (fast w.2 - b.Ic) i
    have : ‖(extCx (lpRescaleNM b.lam w)).2 (Fin.castAdd (m + m) i) - I' (Fin.castAdd (m + m) i)‖ =
        ‖(fast w.2 - b.Ic) i‖ := by
      simp [hI', extCx, lpRescaleNM_apply, lpRescaleNMFun, fast, ← Complex.ofReal_sub,
        Complex.norm_real]
    simpa only [Pi.sub_apply, this] using lt_of_le_of_lt h1 hact
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simpa [hI', extCx, lpRescaleNM_apply, lpRescaleNMFun, slow] using hrB

namespace SpatialLiftData

variable {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 3)} {δ r : ℝ}

/-- **Items 3–4 (`LP:MAIN L14 (477–483)`, `LP:MAIN L18 (47)`, N2, N6): the D1 premises.**  Under
the data of Lemma 14 for `d = 3` (aligned `z₀`), a spatial moving solution `z` on `J ∋ 0` with
`z 0 = z₀`, `t ∈ J`, and the strict stopped conditions on `uIcc 0 t`, there is a chart curve `w`
such that, for the block `spatialStoppedBlock ν δ (Λ z₀) r wₛ` (any `wₛ`), on `uIcc 0 t`:
(i) `w` is a chart lift (in `spLiftChartSafe`, projecting to `z`, solving the chart ODE of
`spLiftChartHam ν μ` two-sidedly); (ii) its rescaling lies in `b.realDom b.rB`; (iii) its slow
pair lies in `b.S`; and `fastAction (lpRescaleNM b.lam (w 0))` is the block centre. -/
theorem spatialChartLift_premises (hd : SpatialLiftData ν U z₀ δ r) {wS : ℝ} {μ : ℝ} {J : Set ℝ}
    (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 3)}
    (hz : IsSpatialMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (hs : SpatialStoppedOn ν z₀ δ r z t) :
    ∃ w : ℝ → Phase (n + (n + n)),
      (∀ u ∈ uIcc 0 t, w u ∈ spLiftChartSafe ν ∧ spatialPoincareProd ν (w u) = z u ∧
        HasDerivAt w (hamiltonianVectorField (spLiftChartHam ν μ) (w u)) u) ∧
      (∀ u ∈ uIcc 0 t,
        lpRescaleNM (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).lam (w u) ∈
          (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).realDom
            (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).rB) ∧
      fastAction (lpRescaleNM (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).lam
        (w 0)) = (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).Ic ∧
      (∀ u ∈ uIcc 0 t, (slow (w u).1, slow (w u).2) ∈
        (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).S) := by
  obtain ⟨w, I, -, -, hsub, hI, hproj, hinit⟩ :=
    hd.spatialChartLift_of_stopped hJ h0 hz hz0 ht hs
  have hν := hd.pos_mass
  have hpro := hd.spLift_prograde_of_stopped hJ h0 hz hz0 ht hs
  have hS : ∀ u ∈ uIcc (0 : ℝ) t, (slow (w u).1, slow (w u).2) ∈
      (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).S := by
    intro u hu
    have hdom := spLiftChartSafe_subset_dom ν (hI u (hsub hu)).1
    have hal := (hpro u hu).2.1
    rw [← hproj u hu] at hal
    have hC : spatialChartAMD (w u) ≤ strongThreshold ν (spatialActionVector ν z₀) - δ / 4 := by
      rw [spatialChartAMD_eq_of_aligned hν hdom hal, hproj u hu]
      exact hd.spLift_strongAMD_le_of_stopped hs hu
    exact hC
  refine ⟨w, fun u hu => ⟨(hI u (hsub hu)).1, hproj u hu, (hI u (hsub hu)).2⟩, fun u hu => ?_,
    ?_, hS⟩
  · have hdom := spLiftChartSafe_subset_dom ν (hI u (hsub hu)).1
    refine lpRescaleNM_mem_realDom _ hd.r_pos ?_ (hS u hu)
    have : fast (w u).2 = spatialActionVector ν (z u) := by
      rw [← hproj u hu]; exact (spLiftActionVector_spatialPoincareProd hν hdom).symm
    show ‖fast (w u).2 - spatialActionVector ν z₀‖ < r
    rw [this]
    exact (hs u hu).2.1
  · show fastAction (lpRescaleNM _ (w 0)) = spatialActionVector ν z₀
    rw [fastAction_lpRescaleNM, hinit]

/-- **Conditional on the analytic data of MAIN L8; not a source result and not `hstop`.**  The
composition of `spatialChartLift_premises` with `nonresonant_drift_of_chartDataNM` on
`J' := uIcc 0 t`, for `t` within the engine time: the Kepler actions drift by at most `r/2` along
the stopped interval.  The stopped conditions are premises here, not derived. -/
theorem spatialStopped_drift_of_chartData (hd : SpatialLiftData ν U z₀ δ r) {wS : ℝ}
    {s K α L p ε : ℝ} {h : (Fin n → ℂ) → ℂ} {f : EC n (n + n) → ℂ}
    (hh : ExtNFHyp (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS) s K α L p ε {0} h f)
    (hsmall : ε ≤ α * r / (2 ^ 7 * conjExp p * K)) {μ : ℝ}
    (htr : ∀ y ∈ (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).realDom r,
      ((liftFast h + f : EC n (n + n) → ℂ) (extCx y)).re =
        lpRescaleHamNM (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS).lam
          (spLiftChartHam ν μ) y)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 3)}
    (hz : IsSpatialMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (htime : |t| ≤ s * r / (5 * ε) * Real.exp ((2 * Real.pi * K * s) / 6))
    (hs : SpatialStoppedOn ν z₀ δ r z t) :
    ∀ u ∈ uIcc 0 t,
      ‖spatialActionVector ν (z u) - spatialActionVector ν z₀‖ ≤ r / 2 := by
  obtain ⟨w, hlift, hmem, hinit, hS⟩ := spatialChartLift_premises (wS := wS) hd hJ h0 hz hz0 ht hs
  have key := nonresonant_drift_of_chartDataNM
    (spatialStoppedBlock ν δ (spatialActionVector ν z₀) r wS) hh hsmall htr
    (J := uIcc 0 t) ordConnected_uIcc left_mem_uIcc
    (fun u hu => differentiableAt_spatialChartHam hd.pos_mass μ (hlift u hu).1)
    (fun u hu => (hlift u hu).2.2) hmem
    (by simpa [fastAction_lpRescaleNM] using hinit) (t1 := t) right_mem_uIcc htime hS
  intro u hu
  have hdom := spLiftChartSafe_subset_dom ν (hlift u hu).1
  have : fast (w u).2 = spatialActionVector ν (z u) := by
    rw [← (hlift u hu).2.1]; exact (spLiftActionVector_spatialPoincareProd hd.pos_mass hdom).symm
  have h2 := key u hu
  rw [this] at h2
  exact h2

end SpatialLiftData

end KAM.Planetary.Spatial

end
