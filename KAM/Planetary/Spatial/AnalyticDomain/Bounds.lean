/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.AnalyticDomain.Extension
public import KAM.Planetary.Spatial.AnalyticDomain.Containment
public import KAM.Planetary.Spatial.AnalyticDomain.Bounds.Tube
public import KAM.Planetary.Spatial.AnalyticDomain.Bounds.Algebra
public import KAM.Planetary.Spatial.AnalyticDomain.Bounds.Chart
public import KAM.Planetary.Spatial.AnalyticDomain.Bounds.Denominator

/-!
# MAIN Lemma 18, complete: spatial chart, momenta, first derivatives and denominators

Source: `LP:MAIN L18 (580–597)` with `LP:MAIN L8 (244–271)`, track LP, non-frozen.

the spatial analytic domain proved the holomorphic extension `fc` of the perturbation, its sup bound, its real trace
and the (22) containment over the spatial core (47).  This package adds the two sentences of MAIN
L8 (line 253), carried over to the spatial setting by L18 (line 595): "on a slightly smaller
version of this domain the chart, momenta, `f`, and all their first derivatives have bound `M`",
and "every Newtonian denominator there has a single holomorphic branch, and its modulus is
bounded away from zero" (`(q_i − q_j)·(q_i − q_j)` keeps positive real part on the complex tube).

* `exists_spatialChart` (in `Bounds.Chart`): item 1, the holomorphic chart and momenta `Ψc`.
* `Bounds.Tube`: item 2, Cauchy estimates on `complexTubeNM`.
* `exists_spatialDenominatorTube` (in `Bounds.Denominator`): item 3.
* `SpatialTubeData`: the collected analytic data on `complexTubeNM (spatialStrongCore ν L δ r)`.
* `exists_spatialTubeData`: items 1–3 together with SP-DOM's `exists_spatialStrongTube`.
* `lemma18_complete`: item 4, quantified as MAIN L18, with the containment of (22) with (47).

-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary KAM.Planetary.StrongAMD Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- The collected analytic data of MAIN L18 on the thin complex tube around the spatial sharp
core (`LP:MAIN L18 (595)`, `LP:MAIN L8 (253, 259–271)`):

* `fc`, `Ψc`: the holomorphic shift-periodic extensions of the perturbation `f = fSpatial ∘ Ψ` and
  of the product chart (positions and momenta, `6n` real coordinates) to `complexTubeNM core R`,
  with real traces;
* sup bounds `M`, `M'` on the half tube `R/2`;
* first-derivative (Cauchy) bounds `M/(R/4)`, `M'/(R/4)` on the quarter tube `R/4`;
* on `complexTubeNM core ρ` (`ρ ≤ R/4`): for every star `q_i` and pair `q_i - q_j` of complexified
  3-vector positions, `Re (w · w) ≥ dS²/2` (resp. `dP²/2`), the principal branch `(w · w)^(1/2)`
  has a holomorphic reciprocal of norm `≤ √2/dS` (resp. `√2/dP`), and on real points the branch
  is the Euclidean length. -/
structure SpatialTubeData (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ r R ρ M M' dS dP : ℝ)
    (fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ)
    (Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
      (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ)) : Prop where
  R_pos : 0 < R
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ R / 4
  fc_holo : DifferentiableOn ℂ fc (complexTubeNM (spatialStrongCore ν L δ r) R)
  fc_real : ∀ w : Phase (n + (n + n)),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTubeNM (spatialStrongCore ν L δ r) R →
      w ∈ spatialChartSafe ν ∧
        fc (KAM.Nekhoroshev.complexifyPhase w) = (fSpatial ν (spatialPoincareProd ν w) : ℂ)
  fc_periodic : ∀ (k : Fin n → ℤ) (z : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)),
    z ∈ complexTubeNM (spatialStrongCore ν L δ r) R →
      z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + (n + n))) ∈
          complexTubeNM (spatialStrongCore ν L δ r) R ∧
        fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + (n + n)))) = fc z
  chart : IsSpatialChartExtension ν (spatialStrongCore ν L δ r) R Ψc
  fc_bound : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R / 2), ‖fc z‖ ≤ M
  chart_bound : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R / 2), ‖Ψc z‖ ≤ M'
  fc_deriv : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R / 4),
    ‖fderiv ℂ fc z‖ ≤ M / (R / 4)
  chart_deriv : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R / 4),
    ‖fderiv ℂ Ψc z‖ ≤ M' / (R / 4)
  dS_pos : 0 < dS
  dP_pos : 0 < dP
  star_re : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ, ∀ i,
    dS ^ 2 / 2 ≤ (cDot3 (cBody3 (Ψc z).1 i)).re
  pair_re : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ, ∀ i j, i ≠ j →
    dP ^ 2 / 2 ≤ (cDot3 (cBody3 (Ψc z).1 i - cBody3 (Ψc z).1 j)).re
  star_holo : ∀ i, DifferentiableOn ℂ
    (fun z => ((cDot3 (cBody3 (Ψc z).1 i)) ^ (1 / 2 : ℂ))⁻¹)
    (complexTubeNM (spatialStrongCore ν L δ r) ρ)
  pair_holo : ∀ i j, i ≠ j → DifferentiableOn ℂ
    (fun z => ((cDot3 (cBody3 (Ψc z).1 i - cBody3 (Ψc z).1 j)) ^ (1 / 2 : ℂ))⁻¹)
    (complexTubeNM (spatialStrongCore ν L δ r) ρ)
  star_norm : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ, ∀ i,
    ‖((cDot3 (cBody3 (Ψc z).1 i)) ^ (1 / 2 : ℂ))⁻¹‖ ≤ Real.sqrt 2 / dS
  pair_norm : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ, ∀ i j, i ≠ j →
    ‖((cDot3 (cBody3 (Ψc z).1 i - cBody3 (Ψc z).1 j)) ^ (1 / 2 : ℂ))⁻¹‖ ≤ Real.sqrt 2 / dP
  star_real : ∀ w : Phase (n + (n + n)),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ → ∀ i,
      (cDot3 (cBody3 (Ψc (KAM.Nekhoroshev.complexifyPhase w)).1 i)) ^ (1 / 2 : ℂ) =
        (spaceLength (bodyVector3 (spatialPoincareProd ν w).1 i) : ℂ)
  pair_real : ∀ w : Phase (n + (n + n)),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ →
      ∀ i j, i ≠ j →
      (cDot3 (cBody3 (Ψc (KAM.Nekhoroshev.complexifyPhase w)).1 i -
          cBody3 (Ψc (KAM.Nekhoroshev.complexifyPhase w)).1 j)) ^ (1 / 2 : ℂ) =
        (spaceLength (bodyVector3 (spatialPoincareProd ν w).1 i -
          bodyVector3 (spatialPoincareProd ν w).1 j) : ℂ)

/-- Items 1–3 with SP-DOM's D4 (`LP:MAIN L18 (595)`, `LP:MAIN L8 (253, 259–271)`): all constants
and functions are chosen before any `I⁰` or `μ`; they depend only on `(ν, L, δ, r_g)`. -/
theorem exists_spatialTubeData (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R ρ M M' dS dP : ℝ,
      ∃ fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ,
      ∃ Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
        (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ),
      SpatialTubeData ν L δ r R ρ M M' dS dP fc Ψc := by
  obtain ⟨R, hR, M, fc, hfc, hreal, hper, hM⟩ := exists_spatialStrongTube hν hn hL hLch hg hδ
  obtain ⟨R', hR', Ψc, hΨ, M', hM'⟩ := exists_spatialChart hν hn hL hLch hg hδ
  set R'' : ℝ := min R R' with hR''def
  have hR'' : 0 < R'' := lt_min hR hR'
  have hle1 : R'' ≤ R := min_le_left _ _
  have hle2 : R'' ≤ R' := min_le_right _ _
  have hfc'' : DifferentiableOn ℂ fc (complexTubeNM (spatialStrongCore ν L δ r) R'') :=
    hfc.mono (complexTubeNM_mono _ hle1)
  have hΨ'' : IsSpatialChartExtension ν (spatialStrongCore ν L δ r) R'' Ψc :=
    hΨ.toSmallerSpatialTube hle2
  have hMfc : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R'' / 2), ‖fc z‖ ≤ M :=
    fun z hz => hM z (complexTubeNM_mono _ (by linarith) hz)
  have hMΨ : ∀ z ∈ complexTubeNM (spatialStrongCore ν L δ r) (R'' / 2), ‖Ψc z‖ ≤ M' :=
    fun z hz => hM' z (complexTubeNM_mono _ (by linarith) hz)
  have hdf := norm_fderiv_le_quarterTubeNM hR'' hfc'' hMfc
  have hdΨ := norm_fderiv_le_quarterTubeNM hR'' hΨ''.holo hMΨ
  obtain ⟨dS, dP, ρ, hdS, hdP, hρ, hρR, hden⟩ :=
    exists_spatialDenominatorTube hν hn hg hδ hR'' hΨ'' hdΨ
  have hcoord : ∀ j, DifferentiableOn ℂ (fun z => (Ψc z).1 j)
      (complexTubeNM (spatialStrongCore ν L δ r) ρ) := fun j =>
    (differentiableOn_pi.1 (differentiable_fst.comp_differentiableOn hΨ''.holo) j).mono
      (complexTubeNM_mono _ (by linarith))
  refine ⟨R'', ρ, M, M', dS, dP, fc, Ψc, ?_⟩
  exact
    { R_pos := hR''
      ρ_pos := hρ
      ρ_le := hρR
      fc_holo := hfc''
      fc_real := fun w hw => hreal w (complexTubeNM_mono _ hle1 hw)
      fc_periodic := fun k z hz =>
        ⟨(complexTubeNM_add_fastShift _ R'' k z).2 hz,
          (hper k z (complexTubeNM_mono _ hle1 hz)).2⟩
      chart := hΨ''
      fc_bound := hMfc
      chart_bound := hMΨ
      fc_deriv := hdf
      chart_deriv := hdΨ
      dS_pos := hdS
      dP_pos := hdP
      star_re := fun z hz i => (hden z hz).1 i
      pair_re := fun z hz i j hij => (hden z hz).2 i j hij
      star_holo := fun i => differentiableOn_inv_sqrt_cDot3
        (fun k => hcoord _) (fun z hz => lt_of_lt_of_le (by positivity) ((hden z hz).1 i))
      pair_holo := fun i j hij => differentiableOn_inv_sqrt_cDot3
        (fun k => (hcoord _).sub (hcoord _))
        (fun z hz => lt_of_lt_of_le (by positivity) ((hden z hz).2 i j hij))
      star_norm := fun z hz i => norm_inv_sqrt_le hdS ((hden z hz).1 i)
      pair_norm := fun z hz i j hij => norm_inv_sqrt_le hdP ((hden z hz).2 i j hij)
      star_real := fun w hw i => by
        have h := (hΨ''.real w (complexTubeNM_mono _ (hρR.trans (by linarith)) hw)).2
        rw [h]
        exact cDot3_cpow_ofReal (bodyVector3 (spatialPoincareProd ν w).1 i)
      pair_real := fun w hw i j hij => by
        have h := (hΨ''.real w (complexTubeNM_mono _ (hρR.trans (by linarith)) hw)).2
        rw [h]
        have e : cBody3 (KAM.Nekhoroshev.complexifyPhase (spatialPoincareProd ν w)).1 i -
            cBody3 (KAM.Nekhoroshev.complexifyPhase (spatialPoincareProd ν w)).1 j =
            fun k => ((((bodyVector3 (spatialPoincareProd ν w).1 i -
              bodyVector3 (spatialPoincareProd ν w).1 j) k : ℝ)) : ℂ) := by
          funext k
          simp [cBody3, bodyVector3, KAM.Nekhoroshev.complexifyPhase]
        rw [e]
        exact cDot3_cpow_ofReal _ }

/-- Item 4 (`LP:MAIN L18 (580–597)`), quantified as MAIN L18 (Lemma 8 with `m = 2n`, the product
chart of Lemma 17 and the ball (47)): the constants `R, ρ, M, M', dS, dP`, the functions
`fc, Ψc` and the widths `r_*, s, b` (with `r_* ≤ 4 r_g`, amendment N3) are fixed before any
`I⁰`; for every `I⁰ ∈ 𝓛_δ`, every point of the domain (22) with all `2n` slow pairs in the
`4b`-neighbourhood of the ball (47) lies in the thin tube `complexTubeNM core ρ` on which all the
data of `SpatialTubeData` hold (holomorphy, real traces, bounds, first-derivative bounds,
holomorphic denominators bounded away from zero). The exact split `H = h + μ f` is SP-DOM's
`spatialHamiltonian_split_chartSafe`. -/
theorem lemma18_complete (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R ρ M M' dS dP : ℝ,
      ∃ fc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) → ℂ,
      ∃ Ψc : ((Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ)) →
        (Fin (n * 3) → ℂ) × (Fin (n * 3) → ℂ),
      SpatialTubeData ν L δ r R ρ M M' dS dP fc Ψc ∧
      ∃ rStar s b : ℝ, 0 < rStar ∧ rStar ≤ 4 * r ∧ 0 < s ∧ 0 < b ∧
        ∀ I0 ∈ strongLevelSet ν L δ,
          ∀ z : (Fin (n + (n + n)) → ℂ) × (Fin (n + (n + n)) → ℂ),
          ‖(fun i => z.2 (Fin.castAdd (n + n) i)) - fun i => ((I0 i : ℝ) : ℂ)‖ < rStar →
          ‖fun i => (z.1 (Fin.castAdd (n + n) i)).im‖ < 4 * s →
          (∃ y ∈ spatialSecularBall ν δ I0,
            ‖(fun i : Fin (n + n) => z.1 (Fin.natAdd n i)) - fun i => ((y.1 i : ℝ) : ℂ)‖ <
              4 * b ∧
            ‖(fun i : Fin (n + n) => z.2 (Fin.natAdd n i)) - fun i => ((y.2 i : ℝ) : ℂ)‖ <
              4 * b) →
          z ∈ complexTubeNM (spatialStrongCore ν L δ r) ρ := by
  obtain ⟨R, ρ, M, M', dS, dP, fc, Ψc, hd⟩ := exists_spatialTubeData hν hn hL hLch hg hδ
  have hρ := hd.ρ_pos
  refine ⟨R, ρ, M, M', dS, dP, fc, Ψc, hd, min (4 * r) (ρ / 2), ρ / 8, ρ / 8,
    lt_min (by linarith [hg.pos]) (by positivity), min_le_left _ _, by positivity, by positivity,
    fun I0 hI0 z hact hang hslow => ?_⟩
  have hmax : max (min (4 * r) (ρ / 2)) (max (4 * (ρ / 8)) (4 * (ρ / 8))) < 2 * ρ / 2 := by
    refine max_lt ?_ (max_lt ?_ ?_) <;> linarith [min_le_right (4 * r) (ρ / 2)]
  have := spatialStrongCore_containment (r := r) (R := 2 * ρ) (lt_min (by linarith [hg.pos])
    (by positivity)) (min_le_left _ _) hmax hI0 hact hang hslow
  have e : 2 * ρ / 2 = ρ := by ring
  rwa [e] at this

end KAM.Planetary.Spatial

end
