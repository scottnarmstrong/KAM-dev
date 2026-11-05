/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Containment
public import KAM.Planetary.StrongAMD.ChartLift.Lift
public import KAM.Planetary.StrongAMD.NonresonantAdapter

/-!
# The premises of the Lemma 13 adapter on the stopped interval

Source: MAIN Lemma 14 (`LP:MAIN L14 (477–483)`) feeding MAIN Lemma 13
(`LP:MAIN L13 (429–464)`, N6), track LP, non-frozen.

For the block `b = lpStoppedBlock ν δ I⁰ r wₛ = ⟨I⁰, secularBall ν δ I⁰, r, wₛ⟩` and the chart lift
`w` of the stopped orbit (`lpChartLift_of_stopped`), `lpChartLift_premises` derives, in exactly the
shape `nonresonant_drift_of_chartData` consumes (with `J := uIcc 0 t`):

* (i) the lift `w` (in `chartSafe`, projecting to `z`, solving the chart ODE) on `uIcc 0 t`;
* (ii) `lpRescale b.lam (w u) ∈ b.realDom b.rB` (outer localization);
* (iii) the stopped slow membership `(slow (w u).1, slow (w u).2) ∈ b.S`;
* the initial fast action `fastAction (lpRescale b.lam (w 0)) = b.Ic`.

None is assumed.  `lpStopped_drift_of_chartData` composes them with the (conditional) adapter, to
check that the shapes match; it does not discharge `hstop`.

-/

@[expose] public noncomputable section

open Set KAM KAM.Planetary KAM.Nekhoroshev KAM.Weighted KAM.NormalForm

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-- The block of MAIN Lemma 13 at the centre `I⁰`: slow base `secularBall ν δ I⁰`, action radius
`r`, physical slow width `wₛ` (`LP:MAIN L13 (429–441)`, N6). -/
def lpStoppedBlock (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) (r wS : ℝ) : PartialBlock n n :=
  ⟨I0, secularBall ν δ I0, r, wS⟩

/-- (ii) Outer localization: a chart point with real angles, action within `b.rB` of the block
centre and slow pair in the block's base rescales into the open real domain. -/
theorem lpRescale_mem_realDom (b : PartialBlock n n) (hrB : 0 < b.rB) {w : Phase (n + n)}
    (hact : ‖fast w.2 - b.Ic‖ < b.rB) (hS : (slow w.1, slow w.2) ∈ b.S) :
    lpRescale b.lam w ∈ b.realDom b.rB := by
  set I' : Fin (n + (n + n)) → ℂ := Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((slow w.1 i / b.lam : ℝ) : ℂ))
      (fun i => ((slow w.2 i / b.lam : ℝ) : ℂ))) with hI'
  refine ⟨KAM.ofReal_mem_complexStrip one_pos _, I', ⟨_, hS, rfl⟩, ?_⟩
  refine (pi_norm_lt_iff hrB).2 fun j => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · have h1 := norm_le_pi_norm (fast w.2 - b.Ic) i
    have : ‖(extCx (lpRescale b.lam w)).2 (Fin.castAdd (n + n) i) - I' (Fin.castAdd (n + n) i)‖ =
        ‖(fast w.2 - b.Ic) i‖ := by
      simp [hI', extCx, lpRescale_apply, lpRescaleFun, fast, ← Complex.ofReal_sub,
        Complex.norm_real]
    simpa only [Pi.sub_apply, this] using lt_of_le_of_lt h1 hact
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simpa [hI', extCx, lpRescale_apply, lpRescaleFun, slow] using hrB

/-- **Items 3–4 (`LP:MAIN L14 (477–483)`, N2, N6): the D1 premises.**  Under the data of Lemma 14,
a moving solution `z` on `J ∋ 0` with `z 0 = z₀`, `t ∈ J`, and the strict stopped conditions on
`uIcc 0 t`, there is a chart curve `w` such that, for the block
`lpStoppedBlock ν δ (Λ z₀) r wₛ` (any `0 < wₛ`), on `uIcc 0 t`: (i) `w` is a chart lift (in
`chartSafe`, projecting to `z`, solving the chart ODE two-sidedly); (ii) its rescaling lies in
`b.realDom b.rB`; (iii) its slow pair lies in `b.S`; and `fastAction (lpRescale b.lam (w 0))` is the
block centre. -/
theorem lpChartLift_premises {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 2)}
    {δ r : ℝ} (hd : LiftData ν U z₀ δ r) {wS : ℝ} {μ : ℝ} {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn ν μ J z)
    (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J) (hs : StoppedOn ν z₀ δ r z t) :
    ∃ w : ℝ → Phase (n + n),
      (∀ u ∈ uIcc 0 t, w u ∈ chartSafe ν ∧ poincareProd ν 1 (w u) = z u ∧
        HasDerivAt w (hamiltonianVectorField (liftChartHam ν μ) (w u)) u) ∧
      (∀ u ∈ uIcc 0 t, lpRescale (lpStoppedBlock ν δ (actionVector ν z₀) r wS).lam (w u) ∈
        (lpStoppedBlock ν δ (actionVector ν z₀) r wS).realDom
          (lpStoppedBlock ν δ (actionVector ν z₀) r wS).rB) ∧
      fastAction (lpRescale (lpStoppedBlock ν δ (actionVector ν z₀) r wS).lam (w 0)) =
        (lpStoppedBlock ν δ (actionVector ν z₀) r wS).Ic ∧
      (∀ u ∈ uIcc 0 t, (slow (w u).1, slow (w u).2) ∈
        (lpStoppedBlock ν δ (actionVector ν z₀) r wS).S) := by
  obtain ⟨w, I, -, -, hsub, hI, hproj, hinit⟩ := hd.lpChartLift_of_stopped hJ h0 hz hz0 ht hs
  have hν := hd.pos_mass
  have hS : ∀ u ∈ uIcc (0 : ℝ) t, (slow (w u).1, slow (w u).2) ∈
      (lpStoppedBlock ν δ (actionVector ν z₀) r wS).S := by
    intro u hu
    have hdom := chartSafe_subset_dom ν (hI u (hsub hu)).1
    have hC : chartAMD (w u) ≤ strongThreshold ν (actionVector ν z₀) - δ / 4 := by
      rw [← lpChart_strongAMD hν hdom, hproj u hu]
      exact hd.strongAMD_le_of_stopped hs hu
    exact hC
  refine ⟨w, fun u hu => ⟨(hI u (hsub hu)).1, hproj u hu, (hI u (hsub hu)).2⟩, fun u hu => ?_,
    ?_, hS⟩
  · have hdom := chartSafe_subset_dom ν (hI u (hsub hu)).1
    refine lpRescale_mem_realDom _ hd.r_pos ?_ (hS u hu)
    have : fast (w u).2 = actionVector ν (z u) := by
      funext i
      rw [← lpChart_action hν hdom i, hproj u hu]
      rfl
    show ‖fast (w u).2 - actionVector ν z₀‖ < r
    rw [this]
    exact (hs u hu).2.1
  · show fastAction (lpRescale _ (w 0)) = actionVector ν z₀
    rw [fastAction_lpRescale, hinit]

/-- **Conditional on the analytic data of MAIN L8; not a source result and not `hstop`.**  The
composition of `lpChartLift_premises` with `nonresonant_drift_of_chartData` on `J' := uIcc 0 t`,
for `t` within the engine time: the Kepler actions drift by at most `r/2` along the stopped
interval.  The stopped conditions are premises here, not derived. -/
theorem lpStopped_drift_of_chartData {ν : Fin n → ℝ} {U : Set (Fin n → ℝ)} {z₀ : Phase (n * 2)}
    {δ r wS : ℝ} (hd : LiftData ν U z₀ δ r) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n n → ℂ}
    (hh : ExtNFHyp (lpStoppedBlock ν δ (actionVector ν z₀) r wS) s K α L p ε {0} h f)
    (hsmall : ε ≤ α * r / (2 ^ 7 * conjExp p * K)) {μ : ℝ}
    (htr : ∀ y ∈ (lpStoppedBlock ν δ (actionVector ν z₀) r wS).realDom r,
      ((liftFast h + f : EC n n → ℂ) (extCx y)).re =
        lpRescaleHam (lpStoppedBlock ν δ (actionVector ν z₀) r wS).lam (liftChartHam ν μ) y)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → Phase (n * 2)}
    (hz : IsMovingSolutionOn ν μ J z) (hz0 : z 0 = z₀) {t : ℝ} (ht : t ∈ J)
    (htime : |t| ≤ s * r / (5 * ε) * Real.exp ((2 * Real.pi * K * s) / 6))
    (hs : StoppedOn ν z₀ δ r z t) :
    ∀ u ∈ uIcc 0 t, ‖(fun i => keplerAction ν (z u) i) - actionVector ν z₀‖ ≤ r / 2 := by
  obtain ⟨w, hlift, hmem, hinit, hS⟩ := lpChartLift_premises (wS := wS) hd hJ h0 hz hz0 ht hs
  exact nonresonant_drift_of_chartData (lpStoppedBlock ν δ (actionVector ν z₀) r wS) hh hsmall
    hd.pos_mass htr (J := uIcc 0 t) ordConnected_uIcc left_mem_uIcc hlift hmem hinit
    (t1 := t) right_mem_uIcc htime hS

end KAM.Planetary.StrongAMD

end
