/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.ParameterIntegral
public import KAM.Planetary.SecularForm.ProductInterface
public import KAM.Planetary.Poincare.Symplectic
public import KAM.Planetary.Poincare.D25

/-!
# Secular form: exact orthogonality of the momenta (Lemma 64) and the identification

Blueprint P, Part 8 (`bpP:p8:lemma64`, `stepP:p8:l64-a` .. `l64-e`, `bpP:p8:identification`,
`stepP:p8:id-diff`, `id-avg`, `id-int`).  The momentum `p^{(i)}` of body `i` and its position
`q^{(i)}` depend on the angles only through `λ_i`; `m_i ν_i ∂_{λ_i} q^{(i)} = p^{(i)}` is the
decoupled Kepler field transported by the product chart (`pc_dec`, `product_chart`), the period
mean of `p^{(i)}` vanishes by periodicity of `q^{(i)}`, the cross means vanish by Fubini, and the
virial value comes from the single-planet means.  The moving and fixed perturbations differ by
`|Σ p^{(i)}|²/(2 m₀)`, whose average is `modelDelta`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

def momentum (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) : Fin 2 → ℝ :=
  bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).2 i
def position (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) : Fin 2 → ℝ :=
  bodyVector (poincareProd D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1)).1 i

/-! ### Block calculus -/

/-- The slow data of planet `i` with its angle replaced by `s`. -/
def blk (x : Slow n) (i : Fin n) (s : ℝ) : Phase 2 := (![s, x.1 i], ![x.2.1 i, x.2.2 i])

theorem blk_mem {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) (s : ℝ) :
    blk x i s ∈ poincareDom := by
  have := hx i
  rw [planetBlock_assemble] at this
  simpa [poincareDom, poincareGamma, blk] using this

theorem assemble_mem {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (t : Vec n) :
    (assemble x.2.1 t x.2.2 x.1 : Phase (n + n)) ∈ poincareProdDom n := by
  intro i
  rw [planetBlock_assemble]
  exact blk_mem hx i (t i)

theorem position_eq_block (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) :
    position D x t i = (poincare (D.m i) (D.G*D.m0) (blk x i (t i))).1 := by
  have := poincareProd_block D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1) i
  rw [planetBlock_assemble] at this
  exact congrArg Prod.fst this

theorem momentum_eq_block (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) :
    momentum D x t i = (poincare (D.m i) (D.G*D.m0) (blk x i (t i))).2 := by
  have := poincareProd_block D.m (D.G*D.m0) (assemble x.2.1 t x.2.2 x.1) i
  rw [planetBlock_assemble] at this
  exact congrArg Prod.snd this

theorem position_update_ne (D : Data n) (x : Slow n) (t : Vec n) {i j : Fin n} (hij : i ≠ j)
    (s : ℝ) : position D x (Function.update t j s) i = position D x t i := by
  rw [position_eq_block, position_eq_block, Function.update_of_ne hij]

theorem position_update_self (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) (s : ℝ) :
    position D x (Function.update t i s) i = (poincare (D.m i) (D.G*D.m0) (blk x i s)).1 := by
  rw [position_eq_block, Function.update_self]

theorem momentum_update_self (D : Data n) (x : Slow n) (t : Vec n) (i : Fin n) (s : ℝ) :
    momentum D x (Function.update t i s) i = (poincare (D.m i) (D.G*D.m0) (blk x i s)).2 := by
  rw [momentum_eq_block, Function.update_self]

theorem continuous_momentum {D : Data n} {x : Slow n} (hx : x ∈ slowDom D) (i : Fin n) :
    Continuous (fun t => momentum D x t i) := by
  have hκ : 0 < D.G * D.m0 := mul_pos D.hG D.hm0
  have h : Continuous fun s : ℝ => (poincare (D.m i) (D.G*D.m0) (blk x i s)).2 := by
    have hc : ContinuousOn (poincare (D.m i) (D.G*D.m0)) poincareDom :=
      (analyticOnNhd_poincare (D.hm i) hκ).continuousOn
    have hb : Continuous (blk x i) := by
      unfold blk
      refine Continuous.prodMk (continuous_pi fun k => ?_) continuous_const
      fin_cases k
      · exact continuous_id
      · exact continuous_const
    exact continuous_snd.comp (hc.comp_continuous hb (blk_mem hx i))
  have : (fun t : Vec n => momentum D x t i) =
      fun t => (poincare (D.m i) (D.G*D.m0) (blk x i (t i))).2 :=
    funext fun t => momentum_eq_block D x t i
  rw [this]
  exact h.comp (continuous_apply i)

end SecularForm
end KAM.Planetary

end
