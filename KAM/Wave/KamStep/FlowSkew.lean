/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Complex.Basic

/-!
# Skewness of the derivative of a Hamiltonian field (`bpW:w5:flow-calc`, step `c-skew`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

If `G` has derivative `B(X_G(z), ·)` at every `z` near `x`, with `B` antisymmetric, and `X_G` has
derivative `DX` at `x`, then `B(DX·a, c) + B(a, DX·c) = 0`: the second derivative of `G` is
symmetric (external fact `W5-E3`, `second_derivative_symmetric_of_eventually`) while `B` is
antisymmetric.
-/

@[expose] public section

open Filter Topology

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem skew_of_hamiltonian (B : F →L[ℂ] F →L[ℂ] ℂ) (hB : ∀ a c, B a c = -B c a) {G : F → ℂ}
    {XG : F → F} {DX : F →L[ℂ] F} {x : F}
    (hG : ∀ᶠ y in 𝓝 x, HasFDerivAt G (B (XG y)) y) (hX : HasFDerivAt XG DX x) (a c : F) :
    B (DX a) c + B a (DX c) = 0 := by
  have hf' : HasFDerivAt (fun y => B (XG y)) (B.comp DX) x := B.hasFDerivAt.comp x hX
  have := second_derivative_symmetric_of_eventually (𝕜 := ℂ) hG hf' a c
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [this, hB a (DX c)]
  ring

end KAM.Wave
