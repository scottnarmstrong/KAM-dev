/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Nekhoroshev.Partial.Nonresonant
public import KAM.Planetary.Exponential.Lift
public import KAM.Planetary.StrongAMD.NonresonantAdapterRescale
public import KAM.Planetary.StrongAMD.PlanarDictionary

/-!
# The Lemma 13 adapter, one centre

Source: MAIN Lemma 13 (`LP:MAIN L13 (429–464)`, with amendment N6), track LP,
non-frozen.

An early test of the riskiest interface of the campaign: physical orbit → rescaled chart →
`KAM.Nekhoroshev.nonresonant`.

* `lpRealDom_isOpen`, `lpIndicator_field`: the indicator Hamiltonian `realHamiltonianExt b R H` has
  the same weighted field as `Ĝ` on the (open) real domain once the trace identity
  `(H (extCx y)).re = Ĝ y` holds there (item 7);
* `lpOrbit_hasDerivAt`: the rescaled chart lift of a moving solution is an orbit of
  `F = realWfield b.c (realHamiltonianExt b b.rB H)` (item 8, the `hy` premise of `nonresonant`);
* `nonresonant_drift_of_chartData`: conditional on the analytic data of MAIN L8 (the `ExtNFHyp`
  bundle and the trace identity); not a source result (item 9).  Premises: the engine's inputs plus
  the chart lift of the physical solution, in the output shape of `KAM.Planetary.lift`.  No drift,
  confinement or AMD bound is assumed.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev KAM.Weighted KAM.NormalForm Set

namespace KAM.Planetary.StrongAMD

variable {n : ℕ}

/-! ### Item 7: the indicator Hamiltonian -/

theorem lpContinuous_extCx : Continuous (extCx : ER n n → EC n n) := by
  unfold extCx
  fun_prop

/-- The real domain `b.realDom R` is open. -/
theorem lpRealDom_isOpen (b : PartialBlock n n) (R : ℝ) : IsOpen (b.realDom R) :=
  (isOpen_Dom (n := n) b.base R 1).preimage lpContinuous_extCx

/-- `realWfield` depends on the Hamiltonian only through its germ at the point. -/
theorem lpRealWfield_congr_eventuallyEq {c : ℝ} {H₁ H₂ : ER n n → ℝ} {z : ER n n}
    (h : H₁ =ᶠ[nhds z] H₂) : realWfield c H₁ z = realWfield c H₂ z := by
  simp only [realWfield, h.fderiv_eq]

/-- (`LP:MAIN L13 (441)`, N6) On the open real domain, the indicator Hamiltonian
`realHamiltonianExt`
has the weighted field of `Ĝ` as soon as the trace identity `(H (extCx y)).re = Ĝ y` holds there. -/
theorem lpIndicator_field (b : PartialBlock n n) (R c : ℝ) (H : EC n n → ℂ)
    (Ĝ : ER n n → ℝ) (htr : ∀ y ∈ b.realDom R, (H (extCx y)).re = Ĝ y) :
    ∀ y ∈ b.realDom R,
      realWfield c (realHamiltonianExt b R H) y = realWfield c Ĝ y := by
  intro y hy
  refine lpRealWfield_congr_eventuallyEq (Filter.eventuallyEq_of_mem
    ((lpRealDom_isOpen b R).mem_nhds hy) fun y' hy' => ?_)
  simp only [realHamiltonianExt, indicator_of_mem hy', htr y' hy']

/-- With `b.lam = ℓ` the block's bracket coefficient is `2π/ℓ²`. -/
theorem lpBlock_c_eq (b : PartialBlock n n) {ℓ : ℝ} (hl : b.lam = ℓ) :
    b.c = 2 * Real.pi / ℓ ^ 2 := by
  simp [PartialBlock.c, hl]

/-- For a block with positive width and radius, `lam = w/rB` is positive. -/
theorem lpBlock_lam_pos {b : PartialBlock n n} (hrB : 0 < b.rB) (hw : 0 < b.w) : 0 < b.lam :=
  div_pos hw hrB

/-! ### Item 8: the rescaled chart lift is an engine orbit -/

/-- (`LP:MAIN L13 (437–441)`, N6) Let `y = lpRescale ℓ ∘ w` with `ℓ = b.lam`.  If the chart curve
`w`
solves the Hamiltonian field of `G` (differentiable along it) on `J`, stays so that its rescaling is
in the open real domain `b.realDom b.rB`, and the trace identity `(H (extCx y)).re = Ĝ y` holds
there
(`Ĝ = lpRescaleHam ℓ G`), then `y` satisfies the `hy` premise of `nonresonant`, with
`F = realWfield b.c (realHamiltonianExt b b.rB H)`. -/
theorem lpOrbit_hasDerivAt (b : PartialBlock n n) {G : Phase (n + n) → ℝ} {H : EC n n → ℂ}
    (hℓ : b.lam ≠ 0)
    (htr : ∀ y ∈ b.realDom b.rB, (H (extCx y)).re = lpRescaleHam b.lam G y)
    {J : Set ℝ} {w : ℝ → Phase (n + n)}
    (hd : ∀ u ∈ J, DifferentiableAt ℝ G (w u))
    (hw : ∀ u ∈ J, HasDerivAt w (hamiltonianVectorField G (w u)) u)
    (hmem : ∀ u ∈ J, lpRescale b.lam (w u) ∈ b.realDom b.rB) :
    ∀ u ∈ J, HasDerivAt (lpRescale b.lam ∘ w)
      (realWfield b.c (realHamiltonianExt b b.rB H) ((lpRescale b.lam ∘ w) u)) u := by
  intro u hu
  have h1 := lpRescale_hasDerivAt hℓ (hd u hu) (hw u hu)
  rw [← lpBlock_c_eq b rfl] at h1
  have h2 := lpIndicator_field b b.rB b.c H _ htr _ (hmem u hu)
  simp only [Function.comp_apply]
  rw [h2]
  exact h1

/-! ### Item 9: the conditional one-centre composition -/

/-- Reading the engine coordinates of the rescaled chart lift: the fast action of `y u` is the
Kepler action of the physical point `z u = Ψ (w u)`. -/
theorem lpFastAction_rescale_eq_keplerAction {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {ℓ : ℝ}
    {w : Phase (n + n)} {z : Phase (n * 2)} (hw : w ∈ poincareProdDom n)
    (hz : poincareProd ν 1 w = z) :
    fastAction (lpRescale ℓ w) = fun i => keplerAction ν z i := by
  rw [fastAction_lpRescale]
  funext i
  rw [← hz, lpChart_action hν hw i]

/-- **Conditional on the analytic data of MAIN L8; not a source result.**  (`LP:MAIN L13 (429–464)`,
N6, one centre.)  Let `h`, `f` satisfy the engine's bundle `ExtNFHyp b s K α L p ε {0} h f` and the
smallness premise.  Let `z` be a physical solution on the `OrdConnected` interval `J ∋ 0` with chart
lift `w` (the output shape of `KAM.Planetary.lift`: `w u ∈ chartSafe ν`, `Ψ (w u) = z u`, and `w`
solves the chart Hamiltonian field of `liftChartHam ν μ`), whose rescaling stays in the real domain
where the trace identity `((liftFast h + f) (extCx y)).re = Ĝ y`
(`Ĝ = lpRescaleHam b.lam (liftChartHam ν μ)`) holds.  If the initial Kepler action is the block
centre
and the chart slow pair is in `b.S` up to the queried time `t1`, then the Kepler actions drift by at
most `rB/2` up to the engine time `s * rB / (5 ε) * exp (2π K s / 6)`.  Nothing about drift,
confinement or AMD is assumed. -/
theorem nonresonant_drift_of_chartData (b : PartialBlock n n) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n n → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α * b.rB / (2 ^ 7 * conjExp p * K))
    {ν : Fin n → ℝ} (hν : ∀ i, 0 < ν i) {μ : ℝ}
    (htr : ∀ y ∈ b.realDom b.rB,
      ((liftFast h + f : EC n n → ℂ) (extCx y)).re = lpRescaleHam b.lam (liftChartHam ν μ) y)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {z : ℝ → Phase (n * 2)} {w : ℝ → Phase (n + n)}
    (hlift : ∀ u ∈ J, w u ∈ chartSafe ν ∧ poincareProd ν 1 (w u) = z u ∧
      HasDerivAt w (hamiltonianVectorField (liftChartHam ν μ) (w u)) u)
    (hmem : ∀ u ∈ J, lpRescale b.lam (w u) ∈ b.realDom b.rB)
    (hinit : fastAction (lpRescale b.lam (w 0)) = b.Ic)
    {t1 : ℝ} (ht1 : t1 ∈ J)
    (ht : |t1| ≤ s * b.rB / (5 * ε) * Real.exp ((2 * Real.pi * K * s) / 6))
    (hstop : ∀ u ∈ uIcc 0 t1, (slow (w u).1, slow (w u).2) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖(fun i => keplerAction ν (z u) i) - b.Ic‖ ≤ b.rB / 2 := by
  have hℓ : b.lam ≠ 0 := (lpBlock_lam_pos hh.radius_pos hh.slow_width_pos).ne'
  have hsub : uIcc (0 : ℝ) t1 ⊆ J := hJ.uIcc_subset h0 ht1
  have hdiff : ∀ u ∈ J, DifferentiableAt ℝ (liftChartHam ν μ) (w u) := fun u hu =>
    ((analyticOnNhd_liftChartHam hν μ) _ (hlift u hu).1).differentiableAt
  have hy := lpOrbit_hasDerivAt b hℓ htr hdiff (fun u hu => (hlift u hu).2.2) hmem
  have hS : ∀ u ∈ uIcc (0 : ℝ) t1, b.lam • slowPair ((lpRescale b.lam ∘ w) u) ∈ b.S := by
    intro u hu
    simpa only [Function.comp_apply, smul_slowPair_lpRescale hℓ] using hstop u hu
  have key := nonresonant b hh hsmall _ (fun _ _ => rfl) hJ h0 hy hinit
    (hS 0 left_mem_uIcc) ht1 ht hS
  intro u hu
  have hu' : u ∈ J := hsub hu
  obtain ⟨hws, hzu, -⟩ := hlift u hu'
  have := key u hu
  rwa [Function.comp_apply, lpFastAction_rescale_eq_keplerAction hν
    (chartSafe_subset_dom ν hws) hzu] at this

end KAM.Planetary.StrongAMD

end
