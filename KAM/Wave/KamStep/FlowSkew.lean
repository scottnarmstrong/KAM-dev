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

/-- **Bracket field** (`bpW:w5:new-ham`, step `n-br`): `D{G,F}(z) = B([X_G, X_F], ·)` with
`{G,F}(y) = B(X_G(y), X_F(y))`
and `[X_G,X_F] = DX_G X_F - DX_F X_G`, when `DX_G`, `DX_F` are `B`-skew. -/
theorem hasFDerivAt_bracket (B : F →L[ℂ] F →L[ℂ] ℂ) (hB : ∀ a c, B a c = -B c a)
    {XG XF : F → F} {DG DF : F →L[ℂ] F} {z : F} (hG : HasFDerivAt XG DG z)
    (hF : HasFDerivAt XF DF z) (sG : ∀ a c, B (DG a) c + B a (DG c) = 0)
    (sF : ∀ a c, B (DF a) c + B a (DF c) = 0) :
    HasFDerivAt (fun y => B (XG y) (XF y)) (B (DG (XF z) - DF (XG z))) z := by
  have hc : HasFDerivAt (fun y => B (XG y)) (B.comp DG) z := B.hasFDerivAt.comp z hG
  have := hc.clm_apply hF
  convert this using 1
  refine ContinuousLinearMap.ext fun W => ?_
  simp only [add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, map_sub]
  have e1 : B (DG W) (XF z) = B (DG (XF z)) W := by
    have h := hB W (DG (XF z))
    linear_combination sG W (XF z) - h
  have e2 : B (XG z) (DF W) = -B (DF (XG z)) W := by
    have h1 := hB (XG z) (DF W)
    have h2 := hB W (DF (XG z))
    linear_combination h1 + h2 - sF W (XG z)
  rw [e1, e2, sub_apply]
  ring

end KAM.Wave
