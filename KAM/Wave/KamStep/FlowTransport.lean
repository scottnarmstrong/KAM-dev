/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Complex.Basic

/-!
# Transport of Hamiltonian fields (`bpW:w5:flow-calc` (iv), step `c-trans`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

If `DG(z) = B(X_G(z), ·)`, the map `φ` has derivative `A` at `w` with `B(Aa, Ab) = B(a, b)` and
`A Y = X_G(φ w)`, then `D(G ∘ φ)(w) = B(Y, ·)`: `Y = A⁻¹ X_G(φ w)` is the field of `G ∘ φ`.
-/

@[expose] public section

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem hasFDerivAt_comp_hamiltonian (B : F →L[ℂ] F →L[ℂ] ℂ) {G : F → ℂ} {XG : F → F}
    {φ : F → F} {A : F →L[ℂ] F} {w Y : F} (hG : HasFDerivAt G (B (XG (φ w))) (φ w))
    (hφ : HasFDerivAt φ A w) (hsymp : ∀ a b, B (A a) (A b) = B a b) (hY : A Y = XG (φ w)) :
    HasFDerivAt (fun z => G (φ z)) (B Y) w := by
  have := hG.comp w hφ
  have e : (B (XG (φ w))).comp A = B Y := by
    refine ContinuousLinearMap.ext fun W => ?_
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hY, hsymp]
  rwa [e] at this

end KAM.Wave
