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
    (hG : HasFDerivAt Gf (B (ι (Zg (holoFlow (smoothField ι Z) t w)))) (holoFlow (smoothField ι Z) t w))
    {y : G} (hy : y + transNop ι Z t w y = Zg (holoFlow (smoothField ι Z) t w)) :
    HasFDerivAt (fun z => Gf (holoFlow (smoothField ι Z) t z)) (B (ι y)) w := by
  have hφ : HasFDerivAt (holoFlow (smoothField ι Z) t)
      (fderiv ℂ (holoFlow (smoothField ι Z) t) w) w :=
    ((holomorphicOn_holoFlow h ht).differentiableAt (h.isOpen_U.mem_nhds hw)).hasFDerivAt
  refine hasFDerivAt_comp_hamiltonian B (XG := fun z => ι (Zg z)) hG hφ
    (fun a b => holoFlow_preserves_form h B hskew hw ht a b) ?_
  rw [fderiv_flow_comp_iota h hZ hb hw ht, hy]

end KAM.Wave
