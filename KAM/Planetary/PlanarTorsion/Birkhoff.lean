/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Defs
public import KAM.Planetary.PlanarTorsion.Birkhoff.Constants

/-!
# Planar quartic torsion: the secular Birkhoff form (package T16)

Blueprint P, Part 11b (`bpP:p11b:birkhoff-form`, with `stepP:p11b:bt-rot`, `stepP:p11b:bt-rot#lift`,
`stepP:p11b:bt-K`, `stepP:p11b:bt-nf`, `stepP:p11b:bt-avg`, `stepP:p11b:bt-frozen`).

* `p11c_phi4` and `PlanarBirkhoffResult` (module `Birkhoff/Defs`) are the signed definitions.
* `birkhoff_form` produces the slow radius `r` and the remainder constant `C` before the good axis
  neighbourhood `Oa`, then, for every open good `Oa ⊇ closedBall a0 rho`, an action neighbourhood
  `O'` with compact closure inside `p.actions '' Oa`, the quartic family `F`, its homological
  solution `chi`, and the **same** map `T = p11c_rotationLift p ∘ p11c_liftFlow chi.eval` for both
  physical perturbations, with its chart, injectivity, action preservation, angle-translation
  covariance, image in the analytic physical domain, the sixth-order expansion of the torus average
  of the actual pullback `f̂ ∘ T`, and the frozen predicate `HasSecularBirkhoffForm`.
* The proof is split over `Birkhoff/Domain` (physical domain, uniform radius), `Birkhoff/Family`
  and `Birkhoff/Chi` (quartic family), `Birkhoff/Diag` and `Birkhoff/Jets` (remainder jets),
  `Birkhoff/Choice` (action neighbourhoods, nonresonance), `Birkhoff/Map`, `Birkhoff/Compose`
  (the map `T`), `Birkhoff/Average` and `Birkhoff/BetaAvg` (torus averages),
  `Birkhoff/Estimate`, `Birkhoff/FhatClause`, `Birkhoff/Result` and `Birkhoff/Constants`.
-/

@[expose] public section

open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

theorem birkhoff_form (p : PlanarData) (hp : p.Valid)
    (a0 : Fin 2 → ℝ) (rho : ℝ)
    (hgoodK : closedBall a0 rho ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0}) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ Oa : Set (Fin 2 → ℝ),
      IsOpen Oa → closedBall a0 rho ⊆ Oa →
      Oa ⊆ {a ∈ p11c_axes | p11c_phi4 p a ≠ 0} →
      PlanarBirkhoffResult p a0 rho Oa r C := by
  obtain ⟨r, C, hr, hC, h⟩ := p11cB_main p hp a0 rho hgoodK
  exact ⟨r, C, hr, hC, fun Oa hOa hKOa _ => h Oa hOa hKOa⟩

end KAM.Planetary

end
