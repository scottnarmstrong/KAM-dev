/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.NewHamIntegral
public import KAM.Wave.KamStep.FlowSkew
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bracket Hamiltonian and its field (blueprint-W `bpW:w5:new-ham` step `n-br`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`hasFDerivAt_bracket_smooth`: for smoothing fields `Z_a, Z_b : F → G` (with `ι`-embedded `B`-skew
derivatives) the function `z ↦ B(ιZ_a, ιZ_b)` has derivative `B(ι[Z_a,Z_b], ·)` with the bracket
`[Z_a, Z_b] = DZ_a(ιZ_b) - DZ_b(ιZ_a)` taking values in `G`.
-/

@[expose] public section

namespace KAM.Wave

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] {ι : G →L[ℂ] F}

theorem fderiv_smoothField {Z : F → G} {z : F} (hZ : DifferentiableAt ℂ Z z) :
    fderiv ℂ (smoothField ι Z) z = ι.comp (fderiv ℂ Z z) :=
  (ι.hasFDerivAt.comp z hZ.hasFDerivAt).fderiv

/-- The bracket Hamiltonian `B(ιZ_a, ιZ_b)` and its `G`-valued field. -/
theorem hasFDerivAt_bracket_smooth (B : F →L[ℂ] F →L[ℂ] ℂ) (hB : ∀ a c, B a c = -B c a)
    {Za Zb : F → G} {z : F} (hZa : DifferentiableAt ℂ Za z) (hZb : DifferentiableAt ℂ Zb z)
    (sa : ∀ a c, B (ι (fderiv ℂ Za z a)) c + B a (ι (fderiv ℂ Za z c)) = 0)
    (sb : ∀ a c, B (ι (fderiv ℂ Zb z a)) c + B a (ι (fderiv ℂ Zb z c)) = 0) :
    HasFDerivAt (fun y => B (ι (Za y)) (ι (Zb y)))
      (B (ι (fderiv ℂ Za z (ι (Zb z)) - fderiv ℂ Zb z (ι (Za z))))) z := by
  have h1 : HasFDerivAt (fun y => ι (Za y)) (ι.comp (fderiv ℂ Za z)) z :=
    ι.hasFDerivAt.comp z hZa.hasFDerivAt
  have h2 : HasFDerivAt (fun y => ι (Zb y)) (ι.comp (fderiv ℂ Zb z)) z :=
    ι.hasFDerivAt.comp z hZb.hasFDerivAt
  have := hasFDerivAt_bracket B hB h1 h2 (fun a c => sa a c) (fun a c => sb a c)
  simpa [map_sub] using this

end KAM.Wave
