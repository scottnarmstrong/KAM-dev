/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorFunSym
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Differentiability of the polynomial of a Taylor polynomial (blueprint-W `bpW:w5:solve`, `s-class`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- A `ℂ`-linear map on `ℂ²`-arguments is the sum of its coordinate partials. -/
theorem stepFderiv_apply_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : (Fin 2 → ℂ) → E) (θ Θ : Fin 2 → ℂ) :
    fderiv ℂ f θ Θ = ∑ i, Θ i • homPartial i f θ := by
  conv_lhs => rw [pi_eq_sum_univ Θ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  unfold homPartial
  congr 2
  funext j
  by_cases h : i = j <;> simp [Pi.single_apply, h, eq_comm]

/-- The projection `KamPhase → ℂ²` onto `y`. -/
abbrev stepPrY : KamPhase →L[ℂ] (Fin 2 → ℂ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)

theorem homPartial_apply_comp {f : (Fin 2 → ℂ) → (Fin 2 → ℂ)} {θ : Fin 2 → ℂ}
    (hf : DifferentiableAt ℂ f θ) (i k : Fin 2) :
    homPartial i (fun x => f x k) θ = homPartial i f θ k := by
  unfold homPartial
  have e : (fun x => f x k) = ⇑(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) k) ∘ f
      :=
    rfl
  rw [e]
  have := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) k).hasFDerivAt.comp θ
    hf.hasFDerivAt).fderiv
  simpa using congrArg (fun L => L (Pi.single i 1)) this

theorem stepFun_hasFDerivAt (ha : 0 ≤ a) (hpp : 0 ≤ p + pb) (T : HomTaylor_gen a p pb s)
    {w : KamPhase} (hw : w.1 ∈ KAM.complexStrip 2 s) :
    ∃ D : KamPhase →L[ℂ] ℂ, HasFDerivAt (waveStepFun ha hpp T) D w ∧ ∀ W : KamPhase,
      D W = ∑ i, W.1 i * homPartial i T.a0 w.1
        + ∑ k, (∑ i, W.1 i * homPartial i T.b w.1 k * w.2.1 k + T.b w.1 k * W.2.1 k)
        + (∑ i, W.1 i * stepPr ha hpp (homPartial i T.cp w.1) (stepZ w)
            + stepPr ha hpp (T.cp w.1) (stepZ W))
        + (∑ i, W.1 i * stepPr ha hpp (homPartial i T.cm w.1) (stepZb w)
            + stepPr ha hpp (T.cm w.1) (stepZb W))
        + (∑ i, W.1 i * (stepPr ha hpp (homPartial i T.P w.1 (stepZ w)) (stepZ w))
            + stepPr ha hpp (T.P w.1 (stepZ W)) (stepZ w) + stepPr ha hpp (T.P w.1 (stepZ w))
                (stepZ W))
        + (∑ i, W.1 i * (stepPr ha hpp (homPartial i T.Q w.1 (stepZ w)) (stepZb w))
            + stepPr ha hpp (T.Q w.1 (stepZ W)) (stepZb w) + stepPr ha hpp (T.Q w.1 (stepZ w))
                (stepZb W))
        + (∑ i, W.1 i * (stepPr ha hpp (homPartial i T.P' w.1 (stepZb w)) (stepZb w))
            + stepPr ha hpp (T.P' w.1 (stepZb W)) (stepZb w)
            + stepPr ha hpp (T.P' w.1 (stepZb w)) (stepZb W)) := by
  have hn : KAM.complexStrip 2 s ∈ nhds w.1 := (KAM.isOpen_complexStrip 2 s).mem_nhds hw
  have d0 := T.comp_a0.1.differentiableAt hn
  have db := T.comp_b.1.differentiableAt hn
  have dcp := T.comp_cp.1.differentiableAt hn
  have dcm := T.comp_cm.1.differentiableAt hn
  have dP := T.comp_P.1.differentiableAt hn
  have dQ := T.comp_Q.1.differentiableAt hn
  have dP' := T.comp_P'.1.differentiableAt hn
  have h1 := hasFDerivAt_theta_comp (w := w) d0
  have h2 : HasFDerivAt (fun x : KamPhase => ∑ k, T.b x.1 k * x.2.1 k) _ w :=
    HasFDerivAt.fun_sum fun k _ =>
      (((hasFDerivAt_theta_comp (w := w) (differentiableAt_pi.1 db k))).fun_mul
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) k).comp
            stepPrY).hasFDerivAt))
  have hz := (stepZ).hasFDerivAt (x := w)
  have hzb := (stepZb).hasFDerivAt (x := w)
  have h3 := hasFDerivAt_pair_term ha hpp (hasFDerivAt_theta_comp (w := w) dcp) hz
  have h4 := hasFDerivAt_pair_term ha hpp (hasFDerivAt_theta_comp (w := w) dcm) hzb
  have h5 := hasFDerivAt_pair_term ha hpp (hasFDerivAt_op_apply (g := stepZ) dP hz) hz
  have h6 := hasFDerivAt_pair_term ha hpp (hasFDerivAt_op_apply (g := stepZ) dQ hz) hzb
  have h7 := hasFDerivAt_pair_term ha hpp (hasFDerivAt_op_apply (g := stepZb) dP' hzb) hzb
  refine ⟨_, ((((((h1.add h2).add h3).add h4).add h5).add h6).add h7), fun W => ?_⟩
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, FunLike.coe_sum, Finset.sum_apply, smul_apply,
    smul_eq_mul, stepFderiv_apply_eq_sum]
  have hb' : ∀ x k, homPartial x (fun x_2 => T.b x_2 k) w.1 = homPartial x T.b w.1 k :=
    fun x k => homPartial_apply_comp db x k
  simp only [hb', stepPrTheta, ContinuousLinearMap.coe_fst', map_sum, map_smul, map_add,
    add_apply, smul_apply, smul_eq_mul, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, ContinuousLinearMap.coe_snd', ContinuousLinearMap.proj_apply,
    sum_apply]
  have e : ∑ x, ∑ i, w.2.1 x * (W.1 i * homPartial i T.b w.1 x) =
      ∑ x, ∑ i, W.1 i * homPartial i T.b w.1 x * w.2.1 x :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  ring

end KAM.Wave
