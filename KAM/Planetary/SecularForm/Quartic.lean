/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quartic.Defs
public import KAM.Planetary.SecularForm.Quartic.PairScaling
public import KAM.Planetary.SecularForm.Quartic.Jet
public import KAM.Planetary.SecularForm.Quartic.Diagonal

/-!
# Secular form: the quartic jet

Blueprint P, Part 8, `bpP:p8:quartic` (Proposition, quartic jet): the six invariant coefficients of
the degree-four part of the secular function, their analyticity in the two actions, and the exact
diagonal values.

* `quartic` (`stepP:p8:q4-str`, `stepP:p8:q4-b`, `stepP:p8:q4-c`): the six coefficients are the
  explicit analytic functions `quarticCoeff` (`Quartic.Coefficients`), assembled from the pair
  decomposition (`Quartic.PairDecomp`), the joint analyticity of the pair average
  (`Quartic.PairAnalytic`), the `O(2)`-invariance of its fourth derivative (`Quartic.PairSymmetry`,
  `Quartic.PairJet`) and `Quartic.Jet`; the diagonal values come from `pairSlowSecular_diag_jet`
  and the exchange of the two planets (`Quartic.Swap`, `Quartic.Diagonal`).
* `quartic_pair_scaling` (`stepP:p8:q4-a`): `Quartic.PairScaling`.
* `quartic_scaling` (`stepP:p8:q4-a`): `Quartic.Scaling`.

The mixed coefficients `c₃, …, c₆` are not computed here (forward obligation of Part 11b).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

/-- Joint six-coefficient existence, analyticity and exact diagonal values. -/
theorem quartic (D : Data n) (hn : 2 ≤ n) :
    ∃ c : Fin n → Fin n → (ℝ × ℝ) → Fin 6 → ℝ,
    (∀ i j, i < j → AnalyticOnNhd ℝ (c i j)
      {IJ | 0 < IJ.1 ∧ 0 < IJ.2 ∧ IJ.1^2/(D.m i^2*(D.G*D.m0)) <
        IJ.2^2/(D.m j^2*(D.G*D.m0))}) ∧
    (∀ I ∈ actionDomain D, ∀ u : Vec n × Vec n,
      iteratedFDeriv ℝ 4 (slowSecular D false I) 0 (fun _ => u) / 24 =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        ∑ k, c i j (I i,I j) k * quarticMonomials ![u.1 i,u.2 i] ![u.1 j,u.2 j] k) ∧
    (∀ I ∈ actionDomain D, ∀ i j, i < j →
      c i j (I i,I j) 0 = -D.G*D.m i*D.m j *
        (iteratedDeriv 4 (radialH (axis D I i) (axis D I j)) 0 / 64 -
         iteratedDeriv 2 (radialH (axis D I i) (axis D I j)) 0 / 16) / I i^2 ∧
      c i j (I i,I j) 1 = -D.G*D.m i*D.m j *
        (iteratedDeriv 4 (radialH (axis D I j) (axis D I i)) 0 / 64 -
         iteratedDeriv 2 (radialH (axis D I j) (axis D I i)) 0 / 16) / I j^2) := by
  refine ⟨fun i j IJ => quarticCoeff D i j IJ, fun i j _ IJ hIJ => ?_,
    fun I hI u => quartic_jet D hI u, fun I hI i j hij => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hIJ
    exact analyticAt_quarticCoeff D i j h1 h2 h3
  · obtain ⟨a, ha, rfl⟩ := hI
    exact ⟨quarticCoeff_zero D i j (action_pos D ha i) (action_pos D ha j)
      (action_axes_lt D ha hij),
      quarticCoeff_one D i j (action_pos D ha i) (action_pos D ha j) (action_axes_lt D ha hij)⟩

end SecularForm
end KAM.Planetary
end
