/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingDefs

/-!
# P Part 5: the oscillator normalization (`stepP:p5:av-dict`)

`pgOscNormalize` is a diagonal linear map, hence a continuous linear map; `pg_osc_normalization`
records that it is invertible with inverse `pgOscUnnormalize` and conformally symplectic with
factor `2π`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b n : ℕ}

theorem blockFast_append {F : Type*} (x : Fin a → F) (y : Fin b → F) :
    blockFast (Fin.append x y) = x := funext fun i => Fin.append_left x y i

theorem blockSlow_append {F : Type*} (x : Fin a → F) (y : Fin b → F) :
    blockSlow (Fin.append x y) = y := funext fun i => Fin.append_right x y i

theorem append_blocks {F : Type*} (v : Fin (a+b) → F) :
    Fin.append (blockFast v) (blockSlow v) = v := Fin.append_castAdd_natAdd (f := v)

/-- The diagonal scaling `x ↦ (c i * x i)`. -/
def diagCLM (c : Fin n → ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => c i • ContinuousLinearMap.proj i

theorem diagCLM_apply (c x : Fin n → ℂ) (i : Fin n) : diagCLM c x i = c i * x i := rfl

/-- The scaling coefficients of the angle block and of the action block. -/
def oscScaleFst (a b : ℕ) : Fin (a+b) → ℂ :=
  Fin.append (fun _ => (2*Real.pi:ℂ)) (fun _ => (Real.sqrt (2*Real.pi):ℂ))

def oscScaleSnd (a b : ℕ) : Fin (a+b) → ℂ :=
  Fin.append (fun _ => (1:ℂ)) (fun _ => (Real.sqrt (2*Real.pi):ℂ))

/-- `pgOscNormalize` as a continuous linear map. -/
def oscNormCLM (a b : ℕ) : CPhase (a+b) →L[ℂ] CPhase (a+b) :=
  ((diagCLM (oscScaleFst a b)).comp (ContinuousLinearMap.fst ℂ _ _)).prod
    ((diagCLM (oscScaleSnd a b)).comp (ContinuousLinearMap.snd ℂ _ _))

theorem pgOscNormalize_eq (z : CPhase (a+b)) : pgOscNormalize z = oscNormCLM a b z := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
  simp [pgOscNormalize, oscNormCLM, diagCLM_apply, oscScaleFst, oscScaleSnd, blockFast, blockSlow]

theorem pgOscNormalize_eq_fun : (pgOscNormalize : CPhase (a+b) → CPhase (a+b)) = oscNormCLM a b :=
  funext pgOscNormalize_eq

theorem differentiable_pgOscNormalize : Differentiable ℂ (pgOscNormalize : CPhase (a+b) → CPhase (a+b)) := by
  rw [pgOscNormalize_eq_fun]; exact (oscNormCLM a b).differentiable

theorem continuous_pgOscNormalize : Continuous (pgOscNormalize : CPhase (a+b) → CPhase (a+b)) :=
  differentiable_pgOscNormalize.continuous

theorem pgOscUnnormalize_normalize (z : CPhase (a+b)) : pgOscUnnormalize (pgOscNormalize z) = z := by
  have h2 : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (Real.sqrt (2*Real.pi):ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
    exact_mod_cast this.ne'
  refine Prod.ext ?_ ?_
  · simp only [pgOscUnnormalize, pgOscNormalize, blockFast_append, blockSlow_append,
      smul_smul, inv_mul_cancel₀ h2, inv_mul_cancel₀ h3, one_smul]
    exact append_blocks z.1
  · simp only [pgOscUnnormalize, pgOscNormalize, blockFast_append, blockSlow_append,
      smul_smul, inv_mul_cancel₀ h3, one_smul]
    exact append_blocks z.2

theorem pgOscNormalize_unnormalize (z : CPhase (a+b)) : pgOscNormalize (pgOscUnnormalize z) = z := by
  have h2 : (2*Real.pi:ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (Real.sqrt (2*Real.pi):ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.2 (by positivity)
    exact_mod_cast this.ne'
  refine Prod.ext ?_ ?_
  · simp only [pgOscUnnormalize, pgOscNormalize, blockFast_append, blockSlow_append,
      smul_smul, mul_inv_cancel₀ h2, mul_inv_cancel₀ h3, one_smul]
    exact append_blocks z.1
  · simp only [pgOscUnnormalize, pgOscNormalize, blockFast_append, blockSlow_append,
      smul_smul, mul_inv_cancel₀ h3, one_smul]
    exact append_blocks z.2

theorem pg_osc_normalization :
    (∀ z : CPhase (a+b), pgOscUnnormalize (pgOscNormalize z) = z ∧
      pgOscNormalize (pgOscUnnormalize z) = z) ∧
    (∀ z u v : CPhase (a+b),
      KAM.Canonical.symplFormC (fderiv ℂ pgOscNormalize z u) (fderiv ℂ pgOscNormalize z v) =
        (2*Real.pi:ℂ)*KAM.Canonical.symplFormC u v) := by
  refine ⟨fun z => ⟨pgOscUnnormalize_normalize z, pgOscNormalize_unnormalize z⟩, fun z u v => ?_⟩
  rw [pgOscNormalize_eq_fun, ContinuousLinearMap.fderiv]
  simp only [KAM.Canonical.symplFormC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [oscNormCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', diagCLM_apply, oscScaleFst,
      oscScaleSnd, Fin.append_left]
    ring
  · have h : (Real.sqrt (2*Real.pi):ℂ) * (Real.sqrt (2*Real.pi):ℂ) = (2*Real.pi:ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast; ring
    simp only [oscNormCLM, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', diagCLM_apply, oscScaleFst,
      oscScaleSnd, Fin.append_right]
    linear_combination (u.2 (Fin.natAdd a j) * v.1 (Fin.natAdd a j) -
      u.1 (Fin.natAdd a j) * v.2 (Fin.natAdd a j)) * h

end KAM.Planetary

end
