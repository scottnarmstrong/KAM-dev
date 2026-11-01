/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.FlowSmoothDeriv
public import KAM.Wave.KamStep.FlowSymplectic
public import KAM.Wave.KamStep.FlowTransport
public import KAM.Wave.KamStep.HoloFderiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Transport of smoothing Hamiltonians by the flow (blueprint-W `bpW:w5:flow-calc` (iii), (iv))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`transNop`: `N_t(w) = DΨ^t(w) ∘ ι : G →L G`, so that `Dφ^t(w) ∘ ι = ι ∘ (1 + N_t(w))`.
`hasFDerivAt_comp_flow_smooth`: if `DGf(φ^t w) = B(ι Z_g(φ^t w), ·)` and `y` solves
`(1 + N_t(w)) y = Z_g(φ^t w)` then `Gf ∘ φ^t` has derivative `B(ι y, ·)` at `w`: the field of the
transported Hamiltonian lies in the `p_+` target `G`.
-/

@[expose] public section

open Set Metric Filter Topology

namespace KAM.Wave

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {ι : G →L[ℂ] F} {Z : F → G} {V U : Set F} {M δ : ℝ}

/-- `N_t(w) = DΨ^t(w) ∘ ι`. -/
noncomputable def transNop (ι : G →L[ℂ] F) (Z : F → G) (t : ℝ) (w : F) : G →L[ℂ] G :=
  (fderiv ℂ (smoothDisp ι Z t) w).comp ι

theorem fderiv_flow_comp_iota (h : FlowHyp (smoothField ι Z) V U M δ) (hZ : DifferentiableOn ℂ Z V)
    (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (y : G) :
    fderiv ℂ (holoFlow (smoothField ι Z) t) w (ι y) = ι (y + transNop ι Z t w y) := by
  rw [fderiv_holoFlow_smooth h hZ hb hw ht]
  simp [transNop]

/-- **Field of a transported Hamiltonian** (`bpW:w5:flow-calc` (iv), with the `p_+` target). -/
theorem hasFDerivAt_comp_flow_smooth (h : FlowHyp (smoothField ι Z) V U M δ)
    (hZ : DifferentiableOn ℂ Z V) (hb : ∀ z ∈ V, ‖Z z‖ ≤ M) (B : F →L[ℂ] F →L[ℂ] ℂ)
    (hskew : ∀ z ∈ V, ∀ x y, B (fderiv ℂ (smoothField ι Z) z x) y +
      B x (fderiv ℂ (smoothField ι Z) z y) = 0)
    {Gf : F → ℂ} {Zg : F → G} {w : F} (hw : w ∈ U) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (hG : HasFDerivAt Gf (B (ι (Zg (holoFlow (smoothField ι Z) t w)))) (holoFlow (smoothField ι Z)
        t w))
    {y : G} (hy : y + transNop ι Z t w y = Zg (holoFlow (smoothField ι Z) t w)) :
    HasFDerivAt (fun z => Gf (holoFlow (smoothField ι Z) t z)) (B (ι y)) w := by
  have hφ : HasFDerivAt (holoFlow (smoothField ι Z) t)
      (fderiv ℂ (holoFlow (smoothField ι Z) t) w) w :=
    ((holomorphicOn_holoFlow h ht).differentiableAt (h.isOpen_U.mem_nhds hw)).hasFDerivAt
  refine hasFDerivAt_comp_hamiltonian B (XG := fun z => ι (Zg z)) hG hφ
    (fun a b => holoFlow_preserves_form h B hskew hw ht a b) ?_
  rw [fderiv_flow_comp_iota h hZ hb hw ht, hy]

section solve

variable {N : G →L[ℂ] G}

theorem isUnit_one_add (hN : ‖N‖ < 1) : IsUnit ((1 : G →L[ℂ] G) + N) := by
  have hlt : ‖-N‖ < 1 := by rwa [norm_neg]
  have := (Units.oneSub (-N) hlt).isUnit
  rwa [Units.val_oneSub, sub_neg_eq_add] at this

/-- The solution operator `u ↦ (1 + N)⁻¹ u`. -/
noncomputable def transSolve (N : G →L[ℂ] G) : G →L[ℂ] G := Ring.inverse ((1 : G →L[ℂ] G) + N)

theorem transSolve_spec (hN : ‖N‖ < 1) (u : G) : transSolve N u + N (transSolve N u) = u := by
  have h := Ring.mul_inverse_cancel _ (isUnit_one_add hN)
  have := congrArg (fun L : G →L[ℂ] G => L u) h
  simpa [transSolve] using this

theorem transSolve_unique (hN : ‖N‖ < 1) {u y y' : G} (hy : y + N y = u) (hy' : y' + N y' = u) :
    y = y' := by
  have h : y + N y = y' + N y' := hy.trans hy'.symm
  have h0 : (y - y') + (N y - N y') = 0 := by
    have := sub_eq_zero.mpr h
    rw [← this]; abel
  have e : y - y' = -(N (y - y')) := by
    rw [map_sub]; exact eq_neg_of_add_eq_zero_left h0
  have h1 : ‖y - y'‖ ≤ ‖N‖ * ‖y - y'‖ := by
    have : ‖y - y'‖ = ‖N (y - y')‖ := by
      conv_lhs => rw [e]
      rw [norm_neg]
    exact this.trans_le (N.le_opNorm _)
  have h2 : (1 - ‖N‖) * ‖y - y'‖ ≤ 0 := by nlinarith
  have h3 : ‖y - y'‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)

theorem differentiableAt_transSolve_apply {N : F → (G →L[ℂ] G)} {u : F → G} {w : F}
    (hN : DifferentiableAt ℂ N w) (hu : DifferentiableAt ℂ u w) (hlt : ‖N w‖ < 1) :
    DifferentiableAt ℂ (fun z => transSolve (N z) (u z)) w := by
  have h1 : DifferentiableAt ℂ (fun z => (1 : G →L[ℂ] G) + N z) w := hN.const_add _
  have h2 : DifferentiableAt ℂ (Ring.inverse : (G →L[ℂ] G) → (G →L[ℂ] G))
      ((1 : G →L[ℂ] G) + N w) := differentiableAt_inverse (isUnit_one_add hlt)
  exact (h2.comp w h1).clm_apply hu

end solve

end KAM.Wave
