/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.StrongAMD.AnalyticDomain.Extension
public import KAM.Planetary.StrongAMD.AnalyticDomain.Containment
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Cauchy
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.TubeBound
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Algebra
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Chart
public import KAM.Planetary.StrongAMD.AnalyticDomain.Bounds.Denominator

/-!
# MAIN Lemma 8, complete: chart, momenta, first derivatives and Newtonian denominators

Package LP-DOMX, `LP:MAIN L8 (244–271)`, track LP, non-frozen.

LP-DOM proved the holomorphic extension `fc` of the perturbation, its sup bound, its real trace and
the (22) containment.  This package adds the two sentences of MAIN L8 (line 253) that were omitted:
"on a slightly smaller version of this domain the chart, momenta, `f`, and all their first
derivatives have bound `M`", and "every Newtonian denominator there has a single holomorphic
branch, and its modulus is bounded away from zero".

* `exists_strongChart` (in `Bounds.Chart`): item 1, the holomorphic chart and momenta `Ψc`.
* `StrongTubeData`: the collected analytic data on `complexTube (strongCore ν L δ r)`.
* `exists_strongTubeData`: items 1–3 together with LP-DOM's `exists_strongTube` (D4).
* `lemma8_complete`: item 4, quantified as MAIN L8, with the containment of (22) (D5).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.StrongAMD

open KAM.Planetary Set Metric

variable {n : ℕ} {ν : Fin n → ℝ} {L : Set (Fin n → ℝ)} {δ r : ℝ}

/-- The complex coordinate `j` of the first (position) component of a holomorphic chart is holomorphic. -/
theorem differentiableOn_chart_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : Set E} {Ψc : E → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ)}
    (h : DifferentiableOn ℂ Ψc T) (j : Fin (n * 2)) :
    DifferentiableOn ℂ (fun z => (Ψc z).1 j) T :=
  differentiableOn_pi.1 (differentiable_fst.comp_differentiableOn h) j

/-- The collected analytic data of MAIN L8 on the thin complex tube around the sharp core
(`LP:MAIN L8 (253, 259–271)`):

* `fc`, `Ψc`: the holomorphic shift-periodic extensions of the perturbation `f = fMov ∘ Ψ` and of
  the chart (positions and momenta) to `complexTube core R`, with real traces;
* sup bounds `M`, `M'` on the half tube `R/2`;
* first-derivative (Cauchy) bounds `M/(R/4)`, `M'/(R/4)` on the quarter tube `R/4`;
* on `complexTube core ρ` (`ρ ≤ R/4`): for every star `q_i` and pair `q_i - q_j` of complexified
  positions, `Re (w · w) ≥ dS²/2` (resp. `dP²/2`), the principal branch `(w · w)^(1/2)` has a
  holomorphic reciprocal of norm `≤ √2/dS` (resp. `√2/dP`), and on real points the branch is the
  Euclidean length. -/
structure StrongTubeData (ν : Fin n → ℝ) (L : Set (Fin n → ℝ)) (δ r R ρ M M' dS dP : ℝ)
    (fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ)
    (Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ)) :
    Prop where
  R_pos : 0 < R
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ R / 4
  fc_holo : DifferentiableOn ℂ fc (complexTube (strongCore ν L δ r) R)
  fc_real : ∀ w : Phase (n + n),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTube (strongCore ν L δ r) R →
      w ∈ chartSafe ν ∧
        fc (KAM.Nekhoroshev.complexifyPhase w) = (fMov 1 1 ν (poincareProd ν 1 w) : ℂ)
  fc_periodic : ∀ (k : Fin n → ℤ) (z : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)),
    z ∈ complexTube (strongCore ν L δ r) R →
      z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n)) ∈
          complexTube (strongCore ν L δ r) R ∧
        fc (z + KAM.Nekhoroshev.complexifyPhase (fastShift k : Phase (n + n))) = fc z
  chart : IsChartExtension ν (strongCore ν L δ r) R Ψc
  fc_bound : ∀ z ∈ complexTube (strongCore ν L δ r) (R / 2), ‖fc z‖ ≤ M
  chart_bound : ∀ z ∈ complexTube (strongCore ν L δ r) (R / 2), ‖Ψc z‖ ≤ M'
  fc_deriv : ∀ z ∈ complexTube (strongCore ν L δ r) (R / 4), ‖fderiv ℂ fc z‖ ≤ M / (R / 4)
  chart_deriv : ∀ z ∈ complexTube (strongCore ν L δ r) (R / 4), ‖fderiv ℂ Ψc z‖ ≤ M' / (R / 4)
  dS_pos : 0 < dS
  dP_pos : 0 < dP
  star_re : ∀ z ∈ complexTube (strongCore ν L δ r) ρ, ∀ i,
    dS ^ 2 / 2 ≤ (cDot (cBody (Ψc z).1 i)).re
  pair_re : ∀ z ∈ complexTube (strongCore ν L δ r) ρ, ∀ i j, i ≠ j →
    dP ^ 2 / 2 ≤ (cDot (cBody (Ψc z).1 i - cBody (Ψc z).1 j)).re
  star_holo : ∀ i, DifferentiableOn ℂ (fun z => ((cDot (cBody (Ψc z).1 i)) ^ (1 / 2 : ℂ))⁻¹)
    (complexTube (strongCore ν L δ r) ρ)
  pair_holo : ∀ i j, i ≠ j → DifferentiableOn ℂ
    (fun z => ((cDot (cBody (Ψc z).1 i - cBody (Ψc z).1 j)) ^ (1 / 2 : ℂ))⁻¹)
    (complexTube (strongCore ν L δ r) ρ)
  star_norm : ∀ z ∈ complexTube (strongCore ν L δ r) ρ, ∀ i,
    ‖((cDot (cBody (Ψc z).1 i)) ^ (1 / 2 : ℂ))⁻¹‖ ≤ Real.sqrt 2 / dS
  pair_norm : ∀ z ∈ complexTube (strongCore ν L δ r) ρ, ∀ i j, i ≠ j →
    ‖((cDot (cBody (Ψc z).1 i - cBody (Ψc z).1 j)) ^ (1 / 2 : ℂ))⁻¹‖ ≤ Real.sqrt 2 / dP
  star_real : ∀ w : Phase (n + n),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTube (strongCore ν L δ r) ρ → ∀ i,
      (cDot (cBody (Ψc (KAM.Nekhoroshev.complexifyPhase w)).1 i)) ^ (1 / 2 : ℂ) =
        (planeLength (bodyVector (poincareProd ν 1 w).1 i) : ℂ)
  pair_real : ∀ w : Phase (n + n),
    KAM.Nekhoroshev.complexifyPhase w ∈ complexTube (strongCore ν L δ r) ρ → ∀ i j, i ≠ j →
      (cDot (cBody (Ψc (KAM.Nekhoroshev.complexifyPhase w)).1 i -
          cBody (Ψc (KAM.Nekhoroshev.complexifyPhase w)).1 j)) ^ (1 / 2 : ℂ) =
        (planeLength (bodyVector (poincareProd ν 1 w).1 i -
          bodyVector (poincareProd ν 1 w).1 j) : ℂ)

/-- Items 1–3 with D4 (`LP:MAIN L8 (253, 259–271)`): all constants and functions are chosen before any
`I⁰` or `μ`; they depend only on `(ν, L, δ, r_g)`. -/
theorem exists_strongTubeData (hν : ∀ i, 0 < ν i) (hn : 2 ≤ n) (hL : IsCompact L)
    (hLch : L ⊆ chamber ν) (hg : IsSharedTube ν L δ r) (hδ : 0 < δ) :
    ∃ R ρ M M' dS dP : ℝ, ∃ fc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → ℂ,
      ∃ Ψc : ((Fin (n + n) → ℂ) × (Fin (n + n) → ℂ)) → (Fin (n * 2) → ℂ) × (Fin (n * 2) → ℂ),
      StrongTubeData ν L δ r R ρ M M' dS dP fc Ψc := by
  obtain ⟨R, hR, M, fc, hfc, hreal, hper, hM⟩ := exists_strongTube hν hn hL hLch hg hδ
  obtain ⟨R', hR', Ψc, hΨ, M', hM'⟩ := exists_strongChart hν hn hL hLch hg hδ
  set R'' : ℝ := min R R' with hR''def
  have hR'' : 0 < R'' := lt_min hR hR'
  have hle1 : R'' ≤ R := min_le_left _ _
  have hle2 : R'' ≤ R' := min_le_right _ _
  have hfc'' : DifferentiableOn ℂ fc (complexTube (strongCore ν L δ r) R'') :=
    hfc.mono (complexTube_mono hle1)
  have hΨ'' : IsChartExtension ν (strongCore ν L δ r) R'' Ψc := hΨ.mono hle2
  have hMfc : ∀ z ∈ complexTube (strongCore ν L δ r) (R'' / 2), ‖fc z‖ ≤ M := fun z hz =>
    hM z (complexTube_mono (by linarith) hz)
  have hMΨ : ∀ z ∈ complexTube (strongCore ν L δ r) (R'' / 2), ‖Ψc z‖ ≤ M' := fun z hz =>
    hM' z (complexTube_mono (by linarith) hz)
  have hdf := norm_fderiv_le_quarterTube hR'' hfc'' hMfc
  have hdΨ := norm_fderiv_le_quarterTube hR'' hΨ''.holo hMΨ
  obtain ⟨dS, dP, ρ, hdS, hdP, hρ, hρR, hden⟩ :=
    exists_strongDenominatorTube hν hn hg hδ hR'' hΨ'' hdΨ
  have hcoord : ∀ j, DifferentiableOn ℂ (fun z => (Ψc z).1 j)
      (complexTube (strongCore ν L δ r) ρ) := fun j =>
    (differentiableOn_chart_coord hΨ''.holo j).mono (complexTube_mono (by linarith))
  refine ⟨R'', ρ, M, M', dS, dP, fc, Ψc, ?_⟩
  exact
    { R_pos := hR''
      ρ_pos := hρ
      ρ_le := hρR
      fc_holo := hfc''
      fc_real := fun w hw => hreal w (complexTube_mono hle1 hw)
      fc_periodic := fun k z hz =>
        ⟨complexTube_add_shift k hz, (hper k z (complexTube_mono hle1 hz)).2⟩
      chart := hΨ''
      fc_bound := hMfc
      chart_bound := hMΨ
      fc_deriv := hdf
      chart_deriv := hdΨ
      dS_pos := hdS
      dP_pos := hdP
      star_re := fun z hz i => (hden z hz).1 i
      pair_re := fun z hz i j hij => (hden z hz).2 i j hij
      star_holo := fun i => differentiableOn_inv_sqrt_cDot
        (fun k => hcoord _) (fun z hz => lt_of_lt_of_le (by positivity) ((hden z hz).1 i))
      pair_holo := fun i j hij => differentiableOn_inv_sqrt_cDot
        (fun k => (hcoord _).sub (hcoord _))
        (fun z hz => lt_of_lt_of_le (by positivity) ((hden z hz).2 i j hij))
      star_norm := fun z hz i => norm_inv_sqrt_le hdS ((hden z hz).1 i)
      pair_norm := fun z hz i j hij => norm_inv_sqrt_le hdP ((hden z hz).2 i j hij)
      star_real := fun w hw i => by
        have h := (hΨ''.real w (complexTube_mono (hρR.trans (by linarith)) hw)).2
        rw [h]
        exact cDot_cpow_ofReal (bodyVector (poincareProd ν 1 w).1 i)
      pair_real := fun w hw i j hij => by
        have h := (hΨ''.real w (complexTube_mono (hρR.trans (by linarith)) hw)).2
        rw [h]
        have e : cBody (KAM.Nekhoroshev.complexifyPhase (poincareProd ν 1 w)).1 i -
            cBody (KAM.Nekhoroshev.complexifyPhase (poincareProd ν 1 w)).1 j =
            fun k => ((((bodyVector (poincareProd ν 1 w).1 i -
              bodyVector (poincareProd ν 1 w).1 j) k : ℝ)) : ℂ) := by
          funext k
          simp [cBody, bodyVector, KAM.Nekhoroshev.complexifyPhase]
        rw [e]
        exact cDot_cpow_ofReal _ }

end KAM.Planetary.StrongAMD

end
