/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.Omega
public import KAM.Wave.KamStep.Flow
public import KAM.Wave.Homological.LieDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Continuous-linear packaging on `StepPhase r` (blueprint-W `bpW:w5:setting`, `bpW:w5:flow`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

The abstract flow calculus of `KAM/Wave/KamStep/Flow*.lean` is stated for a Banach space `F`, a
bilinear form `B : F →L F →L ℂ` and an embedding `ι : G →L F`. This file supplies the concrete data
on `F = G = StepPhase r`: the symplectic form `stepSympCLM` (`bpW:w5:omega`, norm `≤ (4π+1) r²`),
and the inclusion `stepEmbedCLM` of the `p_+`-weighted representatives into the `p`-weighted ones
(the diagonal operator `kamEmbed`, of norm `≤ 1`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {a q q' : ℝ}

theorem stepSymp_add_left (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (W₁ W₂ W : KamPhase) :
    stepSymp ha hqq' (W₁ + W₂) W = stepSymp ha hqq' W₁ W + stepSymp ha hqq' W₂ W := by
  unfold stepSymp
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    map_add, add_apply]
  ring

theorem stepSymp_smul_left (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (c : ℂ) (W₁ W : KamPhase) :
    stepSymp ha hqq' (c • W₁) W = c * stepSymp ha hqq' W₁ W := by
  unfold stepSymp
  have h1 : ∑ i, (c • W₁.1) i * W.2.1 i = c * ∑ i, W₁.1 i * W.2.1 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  have h2 : ∑ i, (c • W₁.2.1) i * W.1 i = c * ∑ i, W₁.2.1 i * W.1 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, map_smul, smul_apply,
    smul_eq_mul]
  ring

theorem stepSymp_add_right (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (W W₁ W₂ : KamPhase) :
    stepSymp ha hqq' W (W₁ + W₂) = stepSymp ha hqq' W W₁ + stepSymp ha hqq' W W₂ := by
  unfold stepSymp
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    map_add]
  ring

theorem stepSymp_smul_right (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (c : ℂ) (W W₁ : KamPhase) :
    stepSymp ha hqq' W (c • W₁) = c * stepSymp ha hqq' W W₁ := by
  unfold stepSymp
  have h1 : ∑ i, W.1 i * (c • W₁.2.1) i = c * ∑ i, W.1 i * W₁.2.1 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  have h2 : ∑ i, W.2.1 i * (c • W₁.1) i = c * ∑ i, W.2.1 i * W₁.1 i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The symplectic form as a bilinear map on `StepPhase r`. -/
def stepSympLin (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (r : ℝ) :
    StepPhase r →ₗ[ℂ] StepPhase r →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun W W' => stepSymp ha hqq' (StepPhase.toK W) (StepPhase.toK W'))
    (fun _ _ _ => stepSymp_add_left ha hqq' _ _ _)
    (fun c _ _ => stepSymp_smul_left ha hqq' c _ _)
    (fun _ _ _ => stepSymp_add_right ha hqq' _ _ _)
    (fun c _ _ => stepSymp_smul_right ha hqq' c _ _)

/-- The symplectic form `ϖ` as a continuous bilinear map on `StepPhase r`
(`bpW:w5:omega`, norm `≤ (4π+1) r²`). -/
def stepSympCLM (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (r : ℝ) [Fact (0 < r)] :
    StepPhase r →L[ℂ] StepPhase r →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂ (stepSympLin ha hqq' r) ((4 * Real.pi + 1) * r ^ 2) fun W W' => by
    have := norm_stepSymp_le ha hqq' (Fact.out : 0 < r) (StepPhase.toK W) (StepPhase.toK W')
    have e : ‖stepSympLin ha hqq' r W W'‖ = ‖stepSymp ha hqq' (StepPhase.toK W) (StepPhase.toK W')‖ :=
      rfl
    rw [e, stepPhase_norm_eq, stepPhase_norm_eq, ← mul_assoc] at *
    exact this

@[simp] theorem stepSympCLM_apply (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (r : ℝ) [Fact (0 < r)]
    (W W' : StepPhase r) :
    stepSympCLM ha hqq' r W W' = stepSymp ha hqq' (StepPhase.toK W) (StepPhase.toK W') := rfl

/-- **`bpW:w5:omega`**: the operator norm of `ϖ` on `StepPhase r` is at most `(4π+1) r²`. -/
theorem norm_stepSympCLM_le (ha : 0 ≤ a) (hqq' : 0 ≤ q + q') (r : ℝ) [Fact (0 < r)] :
    ‖stepSympCLM ha hqq' r‖ ≤ (4 * Real.pi + 1) * r ^ 2 :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- Antisymmetry of `stepSympCLM` (`q = q'`). -/
theorem stepSympCLM_antisymm (ha : 0 ≤ a) (hq : 0 ≤ q + q) (r : ℝ) [Fact (0 < r)]
    (W W' : StepPhase r) : stepSympCLM ha hq r W W' = -stepSympCLM ha hq r W' W := by
  simpa using stepSymp_antisymm ha hq (StepPhase.toK W) (StepPhase.toK W')

/-- The inclusion `𝒫^{a,p_+} → 𝒫^{a,p}` on `KamPhase` (Dirichlet labels `j+2` of W4,
`homEmbed_gen`): the identity on `(θ,y)` and the diagonal operator `ω_{a,p}(J)/ω_{a,p_+}(J)` on
the normal components. -/
def kamHomEmbed (a p pb : ℝ) (hpb : p ≤ pb) : KamPhase →L[ℂ] KamPhase :=
  (ContinuousLinearMap.id ℂ (Fin 2 → ℂ)).prodMap ((ContinuousLinearMap.id ℂ (Fin 2 → ℂ)).prodMap
    ((homEmbed_gen a p pb hpb).prodMap (homEmbed_gen a p pb hpb)))

theorem kamHomEmbed_apply (a p pb : ℝ) (hpb : p ≤ pb) (W : KamPhase) :
    kamHomEmbed a p pb hpb W =
      (W.1, W.2.1, homEmbed_gen a p pb hpb W.2.2.1, homEmbed_gen a p pb hpb W.2.2.2) := rfl

theorem kamNorm_kamHomEmbed_le (a p pb : ℝ) (hpb : p ≤ pb) {r : ℝ} (hr : 0 < r) (W : KamPhase) :
    kamNorm r (kamHomEmbed a p pb hpb W) ≤ kamNorm r W := by
  have hN : ∀ y : HomL2, ‖homEmbed_gen a p pb hpb y‖ ≤ ‖y‖ := fun y =>
    ((homEmbed_gen a p pb hpb).le_opNorm y).trans
      (mul_le_of_le_one_left (norm_nonneg y) (norm_diagCLM_le _ _))
  rw [kamHomEmbed_apply]
  unfold kamNorm
  simp only
  gcongr <;> exact hN _

/-- The inclusion `𝒫^{a,p_+} → 𝒫^{a,p}` as a continuous linear map on `StepPhase r` of norm
`≤ 1`. -/
def stepEmbedCLM (a p pb : ℝ) (hpb : p ≤ pb) (r : ℝ) [Fact (0 < r)] :
    StepPhase r →L[ℂ] StepPhase r :=
  LinearMap.mkContinuous
    { toFun := fun W => kamHomEmbed a p pb hpb (StepPhase.toK W)
      map_add' := fun W W' => (kamHomEmbed a p pb hpb).map_add (StepPhase.toK W) (StepPhase.toK W')
      map_smul' := fun c W => (kamHomEmbed a p pb hpb).map_smul c (StepPhase.toK W) } 1 fun W => by
    rw [one_mul]
    exact kamNorm_kamHomEmbed_le a p pb hpb (Fact.out : 0 < r) (StepPhase.toK W)

theorem stepEmbedCLM_apply (a p pb : ℝ) (hpb : p ≤ pb) (r : ℝ) [Fact (0 < r)] (W : StepPhase r) :
    StepPhase.toK (stepEmbedCLM a p pb hpb r W) = kamHomEmbed a p pb hpb (StepPhase.toK W) := rfl

theorem norm_stepEmbedCLM_apply_le (a p pb : ℝ) (hpb : p ≤ pb) (r : ℝ) [Fact (0 < r)]
    (W : StepPhase r) : ‖stepEmbedCLM a p pb hpb r W‖ ≤ ‖W‖ :=
  kamNorm_kamHomEmbed_le a p pb hpb (Fact.out : 0 < r) (StepPhase.toK W)

end KAM.Wave
