/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Nekhoroshev.Partial.Nonresonant
public import KAM.Planetary.Spatial.NonresonantAdapterRescale
public import KAM.Planetary.StrongAMD.NonresonantAdapter

/-!
# The Lemma 13 adapter for unequal fast and slow blocks

Source: re-typing of the planar chart-dictionary Part B items 7–9
(`LP:MAIN L13 (429–464)`, with amendment N6), track LP, non-frozen.

For a `PartialBlock n m`: `lpRealDomNM_isOpen`, `lpIndicatorNM_field` (the indicator Hamiltonian
`realHamiltonianExt b R H` has the weighted field of `Ĝ` on the open real domain once the trace
identity `(H (extCx y)).re = Ĝ y` holds there), `lpOrbitNM_hasDerivAt` (the rescaled chart lift of a
solution of the chart Hamiltonian field of an abstract `G` is an orbit of
`F = realWfield b.c (realHamiltonianExt b b.rB H)`), and `lpRescaleNM_eq_lpRescale`, the agreement
with the planar chart dictionary's planar `lpRescale` at `m = n`.

`nonresonant_drift_of_chartDataNM` is **conditional** (not a source result): it assumes the
engine's inputs, the trace identity, real-domain membership along the interval and the stopped
slow membership, with an abstract chart Hamiltonian `G` and lift `w`.  Nothing about drift,
confinement or AMD is assumed.
-/

@[expose] public noncomputable section

open KAM KAM.Planetary KAM.Nekhoroshev KAM.Weighted KAM.NormalForm Set

namespace KAM.Planetary.Spatial

variable {n m : ℕ}

/-! ### Agreement with the planar adapter at `m = n` -/

/-- At `m = n` the generic rescaling is the planar chart dictionary's planar `lpRescale`. -/
theorem lpRescaleNM_eq_lpRescale (ℓ : ℝ) :
    (lpRescaleNM ℓ : Phase (n + n) →L[ℝ] ER n n) = KAM.Planetary.StrongAMD.lpRescale ℓ := rfl

/-! ### The indicator Hamiltonian -/

theorem lpContinuousNM_extCx : Continuous (extCx : ER n m → EC n m) := by
  unfold extCx
  fun_prop

/-- The real domain `b.realDom R` is open. -/
theorem lpRealDomNM_isOpen (b : PartialBlock n m) (R : ℝ) : IsOpen (b.realDom R) :=
  (isOpen_Dom (n := n) b.base R 1).preimage lpContinuousNM_extCx

/-- `realWfield` depends on the Hamiltonian only through its germ at the point. -/
theorem lpRealWfieldNM_congr_eventuallyEq {c : ℝ} {H₁ H₂ : ER n m → ℝ} {z : ER n m}
    (h : H₁ =ᶠ[nhds z] H₂) : realWfield c H₁ z = realWfield c H₂ z := by
  simp only [realWfield, h.fderiv_eq]

/-- (`LP:MAIN L13 (441)`, N6) On the open real domain, the indicator Hamiltonian
`realHamiltonianExt` has the weighted field of `Ĝ` as soon as the trace identity
`(H (extCx y)).re = Ĝ y` holds there. -/
theorem lpIndicatorNM_field (b : PartialBlock n m) (R c : ℝ) (H : EC n m → ℂ)
    (Ĝ : ER n m → ℝ) (htr : ∀ y ∈ b.realDom R, (H (extCx y)).re = Ĝ y) :
    ∀ y ∈ b.realDom R,
      realWfield c (realHamiltonianExt b R H) y = realWfield c Ĝ y := by
  intro y hy
  refine lpRealWfieldNM_congr_eventuallyEq (Filter.eventuallyEq_of_mem
    ((lpRealDomNM_isOpen b R).mem_nhds hy) fun y' hy' => ?_)
  simp only [realHamiltonianExt, indicator_of_mem hy', htr y' hy']

/-- With `b.lam = ℓ` the block's bracket coefficient is `2π/ℓ²`. -/
theorem lpBlockNM_c_eq (b : PartialBlock n m) {ℓ : ℝ} (hl : b.lam = ℓ) :
    b.c = 2 * Real.pi / ℓ ^ 2 := by
  simp [PartialBlock.c, hl]

/-- For a block with positive width and radius, `lam = w/rB` is positive. -/
theorem lpBlockNM_lam_pos {b : PartialBlock n m} (hrB : 0 < b.rB) (hw : 0 < b.w) : 0 < b.lam :=
  div_pos hw hrB

/-! ### The rescaled chart lift is an engine orbit -/

/-- (`LP:MAIN L13 (437–441)`, N6) Let `y = lpRescaleNM ℓ ∘ w` with `ℓ = b.lam`.  If the chart curve
`w` solves the Hamiltonian field of `G` (differentiable along it) on `J`, stays so that its
rescaling is in the open real domain `b.realDom b.rB`, and the trace identity
`(H (extCx y)).re = Ĝ y` holds there (`Ĝ = lpRescaleHamNM ℓ G`), then `y` satisfies the `hy`
premise of `nonresonant`, with `F = realWfield b.c (realHamiltonianExt b b.rB H)`. -/
theorem lpOrbitNM_hasDerivAt (b : PartialBlock n m) {G : Phase (n + m) → ℝ} {H : EC n m → ℂ}
    (hℓ : b.lam ≠ 0)
    (htr : ∀ y ∈ b.realDom b.rB, (H (extCx y)).re = lpRescaleHamNM b.lam G y)
    {J : Set ℝ} {w : ℝ → Phase (n + m)}
    (hd : ∀ u ∈ J, DifferentiableAt ℝ G (w u))
    (hw : ∀ u ∈ J, HasDerivAt w (hamiltonianVectorField G (w u)) u)
    (hmem : ∀ u ∈ J, lpRescaleNM b.lam (w u) ∈ b.realDom b.rB) :
    ∀ u ∈ J, HasDerivAt (lpRescaleNM b.lam ∘ w)
      (realWfield b.c (realHamiltonianExt b b.rB H) ((lpRescaleNM b.lam ∘ w) u)) u := by
  intro u hu
  have h1 := lpRescaleNM_hasDerivAt hℓ (hd u hu) (hw u hu)
  rw [← lpBlockNM_c_eq b rfl] at h1
  have h2 := lpIndicatorNM_field b b.rB b.c H _ htr _ (hmem u hu)
  simp only [Function.comp_apply]
  rw [h2]
  exact h1

/-! ### The conditional composition -/

/-- **Conditional; not a source result.**  (`LP:MAIN L13 (429–464)`, N6, one centre, generic
`n m`.)  Let `h`, `f` satisfy the engine's bundle `ExtNFHyp b s K α L p ε {0} h f` and the
smallness premise.  Let `w` be a chart curve on the `OrdConnected` interval `J ∋ 0` solving the
Hamiltonian field of an abstract chart Hamiltonian `G` (differentiable along it), whose rescaling
stays in the real domain where the trace identity
`((liftFast h + f) (extCx y)).re = Ĝ y` (`Ĝ = lpRescaleHamNM b.lam G`) holds.  If the initial fast
action is the block centre and the chart slow pair is in `b.S` up to the queried time `t1`, then
the fast actions drift by at most `rB/2` up to the engine time
`s * rB / (5 ε) * exp (2π K s / 6)`.  Nothing about drift, confinement or AMD is assumed. -/
theorem nonresonant_drift_of_chartDataNM (b : PartialBlock n m) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n m → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α * b.rB / (2 ^ 7 * conjExp p * K))
    {G : Phase (n + m) → ℝ}
    (htr : ∀ y ∈ b.realDom b.rB,
      ((liftFast h + f : EC n m → ℂ) (extCx y)).re = lpRescaleHamNM b.lam G y)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {w : ℝ → Phase (n + m)}
    (hd : ∀ u ∈ J, DifferentiableAt ℝ G (w u))
    (hw : ∀ u ∈ J, HasDerivAt w (hamiltonianVectorField G (w u)) u)
    (hmem : ∀ u ∈ J, lpRescaleNM b.lam (w u) ∈ b.realDom b.rB)
    (hinit : fast (w 0).2 = b.Ic)
    {t1 : ℝ} (ht1 : t1 ∈ J)
    (ht : |t1| ≤ s * b.rB / (5 * ε) * Real.exp ((2 * Real.pi * K * s) / 6))
    (hstop : ∀ u ∈ uIcc 0 t1, (slow (w u).1, slow (w u).2) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖fast (w u).2 - b.Ic‖ ≤ b.rB / 2 := by
  have hℓ : b.lam ≠ 0 := (lpBlockNM_lam_pos hh.radius_pos hh.slow_width_pos).ne'
  have hy := lpOrbitNM_hasDerivAt b hℓ htr hd hw hmem
  have hS : ∀ u ∈ uIcc (0 : ℝ) t1, b.lam • slowPair ((lpRescaleNM b.lam ∘ w) u) ∈ b.S := by
    intro u hu
    simpa only [Function.comp_apply, smul_slowPair_lpRescaleNM hℓ] using hstop u hu
  have key := nonresonant b hh hsmall _ (fun _ _ => rfl) hJ h0 hy
    (by simpa only [Function.comp_apply, fastAction_lpRescaleNM] using hinit)
    (hS 0 left_mem_uIcc) ht1 ht hS
  intro u hu
  simpa only [Function.comp_apply, fastAction_lpRescaleNM] using key u hu

end KAM.Planetary.Spatial

end
