/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorFunDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Hamiltonian field of a Taylor polynomial (blueprint-W `bpW:w5:solve`, step `s-class`)

`stepField T w = (b/2π, -(1/2π)F_θ, F_v, -F_u)` is the field of `waveStepFun T` in the weighted
representatives of `ℓ^N_{a,p_+}`; `stepFun_field` shows
`D(waveStepFun T)(w) W = ϖ(stepField T w, W)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- **The field `X_F` of a Taylor polynomial** in the weighted representatives
(`p_+`-weight on the normal components): `(b/2π, -(1/2π)F_θ, F_v, -F_u)`. -/
def stepField (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (w : KamPhase) : KamPhase :=
  (fun i => (2 * Real.pi : ℂ)⁻¹ * T.b w.1 i,
    fun i => -(2 * Real.pi : ℂ)⁻¹ * homRtheta_gen ha hp hpb T i w.1 w.2.1 (stepZ w) (stepZb w),
    homRv_gen T w.1 (stepZ w) (stepZb w),
    -homRu_gen T w.1 (stepZ w) (stepZb w))

/-- The normal-component bookkeeping: `⟨R_z,Z'⟩ + ⟨R_{z̄},Z̄'⟩ = ⟨R_u,U'⟩ + ⟨R_v,V'⟩`. -/
theorem stepPr_uv (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (T : HomTaylor_gen a p pb s) (θ : Fin 2 → ℂ)
    (z zb U' V' : HomL2) :
    stepPr ha hpp (homRz_gen T θ z zb) (homSqrt2⁻¹ • (U' + Complex.I • V'))
      + stepPr ha hpp (homRzb_gen T θ z zb) (homSqrt2⁻¹ • (U' - Complex.I • V')) =
    stepPr ha hpp (homRu_gen T θ z zb) U' + stepPr ha hpp (homRv_gen T θ z zb) V' := by
  unfold homRu_gen homRv_gen
  simp only [map_smul, map_add, map_sub, smul_apply, smul_eq_mul, add_apply, sub_apply]
  ring

/-- **`DF = ϖ(X_F, ·)`** for the polynomial of a Taylor polynomial (`bpW:w5:solve` step `s-class`):
`waveStepFun T` is Fréchet differentiable at every point with `θ ∈ T_s`, and its derivative is the
symplectic pairing with `stepField T`. -/
theorem stepFun_field (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    {w : KamPhase} (hw : w.1 ∈ KAM.complexStrip 2 s) :
    ∃ D : KamPhase →L[ℂ] ℂ, HasFDerivAt (waveStepFun ha (homPP hp hpb) T) D w ∧ ∀ W : KamPhase,
      D W = stepSymp (q := p) (q' := pb) ha (homPP hp hpb) (stepField ha hp hpb T w) W := by
  obtain ⟨D, hD, hDW⟩ := stepFun_hasFDerivAt ha (homPP hp hpb) T hw
  refine ⟨D, hD, fun W => ?_⟩
  rw [hDW]
  have hP : ∀ x y, stepPr ha (homPP hp hpb) (T.P w.1 x) y = stepPr ha (homPP hp hpb) (T.P w.1 y) x
      :=
    fun x y => stepPr_swap ha hp hpb (fun i j => T.symP w.1 hw i j) x y
  have hP' : ∀ x y, stepPr ha (homPP hp hpb) (T.P' w.1 x) y =
      stepPr ha (homPP hp hpb) (T.P' w.1 y) x :=
    fun x y => stepPr_swap ha hp hpb (fun i j => T.symP' w.1 hw i j) x y
  have hQ : ∀ x y, stepPr ha (homPP hp hpb) (T.Q w.1 x) y =
      stepPr ha (homPP hp hpb) (T.Qt w.1 y) x :=
    fun x y => stepPr_swap ha hp hpb (fun i j => (T.transQ w.1 hw j i).symm) x y
  have e1 : stepPr ha (homPP hp hpb) (T.P w.1 (stepZ W)) (stepZ w) =
      stepPr ha (homPP hp hpb) (T.P w.1 (stepZ w)) (stepZ W) := hP _ _
  have e2 : stepPr ha (homPP hp hpb) (T.P' w.1 (stepZb W)) (stepZb w) =
      stepPr ha (homPP hp hpb) (T.P' w.1 (stepZb w)) (stepZb W) := hP' _ _
  have e3 : stepPr ha (homPP hp hpb) (T.Q w.1 (stepZ W)) (stepZb w) =
      stepPr ha (homPP hp hpb) (T.Qt w.1 (stepZb w)) (stepZ W) := hQ _ _
  have hZ : stepZ W = homSqrt2⁻¹ • (W.2.2.1 + Complex.I • W.2.2.2) := stepZ_apply _ _ _ _
  have hZb : stepZb W = homSqrt2⁻¹ • (W.2.2.1 - Complex.I • W.2.2.2) := stepZb_apply _ _ _ _
  have huv := stepPr_uv ha (homPP hp hpb) T w.1 (stepZ w) (stepZb w) W.2.2.1 W.2.2.2
  rw [← hZ, ← hZb] at huv
  have hRz : homRz_gen T w.1 (stepZ w) (stepZb w) = T.cp w.1 + (2 : ℂ) • T.P w.1 (stepZ w)
      + T.Qt w.1 (stepZb w) := rfl
  have hRzb : homRzb_gen T w.1 (stepZ w) (stepZb w) = T.cm w.1 + T.Q w.1 (stepZ w)
      + (2 : ℂ) • T.P' w.1 (stepZb w) := rfl
  rw [hRz, hRzb] at huv
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at huv
  rw [e1, e2, e3]
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hR : ∀ i, homRtheta_gen ha hp hpb T i w.1 w.2.1 (stepZ w) (stepZb w) =
      homPartial i T.a0 w.1 + ∑ k, homPartial i T.b w.1 k * w.2.1 k
        + stepPr ha (homPP hp hpb) (homPartial i T.cp w.1) (stepZ w)
        + stepPr ha (homPP hp hpb) (homPartial i T.cm w.1) (stepZb w)
        + stepPr ha (homPP hp hpb) (homPartial i T.P w.1 (stepZ w)) (stepZ w)
        + stepPr ha (homPP hp hpb) (homPartial i T.Q w.1 (stepZ w)) (stepZb w)
        + stepPr ha (homPP hp hpb) (homPartial i T.P' w.1 (stepZb w)) (stepZb w) := fun i => rfl
  have sB : 2 * (Real.pi : ℂ) * ∑ i, ((2 * Real.pi : ℂ)⁻¹ * T.b w.1 i) * W.2.1 i =
      ∑ k, T.b w.1 k * W.2.1 k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  have sT : 2 * (Real.pi : ℂ) * ∑ i, (-(2 * Real.pi : ℂ)⁻¹ *
      homRtheta_gen ha hp hpb T i w.1 w.2.1 (stepZ w) (stepZb w)) * W.1 i =
      -∑ i, W.1 i * homRtheta_gen ha hp hpb T i w.1 w.2.1 (stepZ w) (stepZb w) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by field_simp
  have hSig : ∑ i, W.1 i * homRtheta_gen ha hp hpb T i w.1 w.2.1 (stepZ w) (stepZb w) =
      ∑ i, W.1 i * homPartial i T.a0 w.1 + ∑ i, W.1 i * ∑ k, homPartial i T.b w.1 k * w.2.1 k
        + ∑ i, W.1 i * stepPr ha (homPP hp hpb) (homPartial i T.cp w.1) (stepZ w)
        + ∑ i, W.1 i * stepPr ha (homPP hp hpb) (homPartial i T.cm w.1) (stepZb w)
        + ∑ i, W.1 i * stepPr ha (homPP hp hpb) (homPartial i T.P w.1 (stepZ w)) (stepZ w)
        + ∑ i, W.1 i * stepPr ha (homPP hp hpb) (homPartial i T.Q w.1 (stepZ w)) (stepZb w)
        + ∑ i, W.1 i * stepPr ha (homPP hp hpb) (homPartial i T.P' w.1 (stepZb w)) (stepZb w) := by
    simp only [hR, mul_add, Finset.sum_add_distrib]
  have hb : ∑ k, (∑ i, W.1 i * homPartial i T.b w.1 k * w.2.1 k + T.b w.1 k * W.2.1 k) =
      ∑ i, W.1 i * ∑ k, homPartial i T.b w.1 k * w.2.1 k + ∑ k, T.b w.1 k * W.2.1 k := by
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold stepSymp stepField
  simp only [map_neg, neg_apply]
  rw [mul_sub, sB, sT, hSig, hb]
  simp only [sub_neg_eq_add]
  linear_combination huv

end KAM.Wave
