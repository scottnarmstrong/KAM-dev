/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Symplecticity of the flow: abstract core (`bpW:w5:flow-calc` (ii), step `c-symp`)

If `a, a' : ℝ → E` solve the variational equation `a' = K(t) a` (derivative within `[-1,1]`) and the
bilinear form `B` is skewed by every `K(t)`, i.e. `B(Kx, y) + B(x, Ky) = 0` (step `c-skew`), then
`t ↦ B(a(t), a'(t))` is constant (`stepSymp_const`). With `a(t) = Dφ^t(w) W`, `K(t) = DX_F(φ^t w)`
and `B = ϖ` this is `ϖ(Dφ^t W, Dφ^t W') = ϖ(W, W')`.
-/

@[expose] public section

namespace KAM.Wave

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative of `t ↦ B (a t) (b t)`. -/
theorem stepSymp_hasDerivWithinAt (B : E →L[ℂ] E →L[ℂ] ℂ) {a b : ℝ → E} {a' b' : E} {s : Set ℝ}
    {t : ℝ} (ha : HasDerivWithinAt a a' s t) (hb : HasDerivWithinAt b b' s t) :
    HasDerivWithinAt (fun u => B (a u) (b u)) (B a' (b t) + B (a t) b') s t := by
  letI : NormedSpace ℝ E := NormedSpace.complexToReal
  set L : E →L[ℝ] (E →L[ℝ] ℂ) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E ℂ ℝ ℝ).comp (B.restrictScalars ℝ) with hL
  have hc : HasDerivWithinAt (fun u => L (a u)) (L a') s t := HasFDerivAt.comp_hasDerivWithinAt t
      (L.hasFDerivAt (x := a t)) ha
  have hb' : HasDerivWithinAt b b' s t := hb
  have := hc.clm_apply hb'
  simpa [hL] using this

/-- **Constancy** of `B(a(t), a'(t))` along the variational equation. -/
theorem stepSymp_const (B : E →L[ℂ] E →L[ℂ] ℂ) {a b : ℝ → E} {K : ℝ → E →L[ℂ] E}
    (hskew : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x y, B (K t x) y + B x (K t y) = 0)
    (ha : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt a (K t (a t)) (Icc (-1) 1) t)
    (hb : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt b (K t (b t)) (Icc (-1) 1) t)
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    B (a t) (b t) = B (a 0) (b 0) := by
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hd : ∀ u ∈ Icc (-1 : ℝ) 1,
      HasDerivWithinAt (fun v => B (a v) (b v)) 0 (Icc (-1) 1) u := by
    intro u hu
    have := stepSymp_hasDerivWithinAt B (ha u hu) (hb u hu)
    rwa [hskew u hu] at this
  have hcont : ContinuousOn (fun v => B (a v) (b v)) (Icc (-1 : ℝ) 1) :=
    fun u hu => (hd u hu).continuousWithinAt
  have hr : ∀ x ∈ Ico (-1 : ℝ) 1, HasDerivWithinAt (fun v => B (a v) (b v)) 0 (Ici x) x := by
    intro x hx
    exact (hd x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hx.1, hx.2⟩)
  have h1 := constant_of_has_deriv_right_zero hcont hr t ht
  have h2 := constant_of_has_deriv_right_zero hcont hr 0 h0
  rw [h1, h2]

end KAM.Wave
