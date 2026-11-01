/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepSympEmbed
public import KAM.Wave.KamStep.FlowSkew
public import KAM.Wave.KamStep.FlowSmooth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The concrete flow setting on `StepPhase r` (blueprint-W `bpW:w5:flow`, `bpW:w5:flow-calc`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

For a W4 Taylor polynomial `T` the abstract flow calculus applies with `F = G = StepPhase r`,
`Z = stepFieldS T` (the field in the `p_+`-representatives), `ι = stepEmbedCLM` (so that the flow
field is `X = ι ∘ Z`), `B = stepSympCLM` with `q = q' = p`:
* `stepFieldS_differentiableOn`: `Z` is holomorphic on `D(s', r)`, `s' ≤ s`;
* `stepFieldS_hasFDerivAt_ham`: `DF = B(X, ·)` for `F = stepFun ∘ toK`;
* `stepFieldS_skew`: `DX(z)` is `B`-skew (`bpW:w5:flow-calc` step `c-skew`, concrete).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Filter Topology

variable {a p pb s : ℝ}

/-- `toK` as a continuous linear map. -/
def stepToKCLM (r : ℝ) [Fact (0 < r)] : StepPhase r →L[ℂ] KamPhase :=
  LinearMap.mkContinuous
    { toFun := StepPhase.toK
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } (max 1 (max (r ^ 2) r))
    fun W => norm_kamPhase_le_kamNorm (Fact.out : 0 < r) (StepPhase.toK W)

/-- `ofK` as a continuous linear map. -/
def stepOfKCLM (r : ℝ) [Fact (0 < r)] : KamPhase →L[ℂ] StepPhase r :=
  LinearMap.mkContinuous
    { toFun := StepPhase.ofK
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } (1 + 1 / r ^ 2 + 2 / r)
    fun W => kamNorm_le_norm_kamPhase (Fact.out : 0 < r) W

@[simp] theorem stepToKCLM_apply (r : ℝ) [Fact (0 < r)] (W : StepPhase r) :
    stepToKCLM r W = StepPhase.toK W := rfl

@[simp] theorem stepOfKCLM_apply (r : ℝ) [Fact (0 < r)] (W : KamPhase) :
    stepOfKCLM r W = StepPhase.ofK W := rfl

/-- The field `Z = X_F` (`p_+`-representatives) as a map on `StepPhase r`. -/
def stepFieldS (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s) (r : ℝ) :
    StepPhase r → StepPhase r :=
  fun W => StepPhase.ofK (stepField ha hp hpb T (StepPhase.toK W))

theorem stepDomain_theta_mem {s' s r' : ℝ} (hs : s' ≤ s) {r : ℝ} {W : StepPhase r}
    (hW : W ∈ stepDomain r s' r') : (StepPhase.toK W).1 ∈ complexStrip 2 s := by
  intro i
  exact (hW.1 i).trans_le hs

theorem stepFieldS_differentiableAt (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (T : HomTaylor_gen a p pb s) (r : ℝ) [Fact (0 < r)] {W : StepPhase r}
    (hW : (StepPhase.toK W).1 ∈ complexStrip 2 s) :
    DifferentiableAt ℂ (stepFieldS ha hp hpb T r) W := by
  have h := stepField_differentiableAt ha hp hpb T hW
  have h2 : DifferentiableAt ℂ (stepField ha hp hpb T) (stepToKCLM r W) := h
  exact (stepOfKCLM r).differentiableAt.comp W (h2.comp W (stepToKCLM r).differentiableAt)

/-- The Hamiltonian `F` as a function on `StepPhase r`. -/
def stepFS (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s) (r : ℝ) :
    StepPhase r → ℂ :=
  fun W => stepFun ha (homPP hp hpb) T (StepPhase.toK W)

/-- **`DF = B(X, ·)`** on `StepPhase r`, with `X = ι Z` and `B = ϖ_{p,p}`. -/
theorem stepFS_hasFDerivAt (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (r : ℝ) [Fact (0 < r)] {W : StepPhase r} (hW : (StepPhase.toK W).1 ∈ complexStrip 2 s) :
    HasFDerivAt (stepFS ha hp hpb T r)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (stepEmbedCLM a p pb hpb r (stepFieldS ha hp hpb T r W))) W := by
  obtain ⟨D, hD, hDW⟩ := stepFun_field ha hp hpb T hW
  have h : HasFDerivAt (stepFS ha hp hpb T r) (D.comp (stepToKCLM r)) W :=
    hD.comp W (stepToKCLM r).hasFDerivAt
  refine h.congr_fderiv (ContinuousLinearMap.ext fun W' => ?_)
  simp only [ContinuousLinearMap.comp_apply, stepToKCLM_apply, hDW, stepSympCLM_apply]
  rw [stepEmbedCLM_apply, stepSymp_embed ha hpb (by linarith) (homPP hp hpb)]
  rfl

/-- **Skewness of `DX_F`** (`bpW:w5:flow-calc` step `c-skew`, concrete): for
`X = ι ∘ Z` the derivative `DX(x)` is `ϖ_{p,p}`-skew at every `x` with `θ ∈ T_s` that has a
neighbourhood on which the field is differentiable. -/
theorem stepFieldS_skew (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (r : ℝ) [Fact (0 < r)] {x : StepPhase r} (hx : (StepPhase.toK x).1 ∈ complexStrip 2 s)
    (A C : StepPhase r) :
    stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (fderiv ℂ (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r)) x A) C
      + stepSympCLM (q := p) (q' := p) ha (by linarith) r A
        (fderiv ℂ (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r)) x C) = 0 :=
            by
  have hopen : IsOpen {y : StepPhase r | (StepPhase.toK y).1 ∈ complexStrip 2 s} :=
    ((isOpen_complexStrip 2 s).preimage (continuous_fst.comp (stepPhase_toK_continuous r)))
  have hG : ∀ᶠ y in 𝓝 x, HasFDerivAt (stepFS ha hp hpb T r)
      (stepSympCLM (q := p) (q' := p) ha (by linarith) r
        (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r) y)) y :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun y hy => stepFS_hasFDerivAt ha hp hpb T r hy
  have hX : HasFDerivAt (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r))
      (fderiv ℂ (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r)) x) x :=
    ((stepEmbedCLM a p pb hpb r).differentiableAt.comp x
      (stepFieldS_differentiableAt ha hp hpb T r hx)).hasFDerivAt
  exact skew_of_hamiltonian _ (fun A C => stepSympCLM_antisymm ha (by linarith) r A C) hG hX A C

end KAM.Wave
