/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFlowConcrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The field norm of a Taylor polynomial is W4's `|X_R|_r` (blueprint-W `bpW:w5:solve`, `bpW:w5:flow`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`kamNorm r (stepField T w) = homXnorm_gen r T θ y z z̄` at `z = stepZ w`, `z̄ = stepZb w`, and the
domain `D(s,r)` of `KamPhase` is W4's `HomDomain` under `z = (u+iv)/√2`. So W4's field bounds
(`HomFieldBound_gen`) are bounds for `stepFieldS` in the norm of `StepPhase r`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem kamNorm_stepField (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    {r : ℝ} (hr : 0 < r) (w : KamPhase) :
    kamNorm r (stepField ha hp hpb T w) =
      homXnorm_gen ha hp hpb r T w.1 w.2.1 (stepZ w) (stepZb w) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have e1 : ‖fun i => (2 * Real.pi : ℂ)⁻¹ * T.b w.1 i‖ = (2 * Real.pi)⁻¹ * ‖T.b w.1‖ := by
    have : (fun i => (2 * Real.pi : ℂ)⁻¹ * T.b w.1 i) = ((2 * Real.pi : ℂ)⁻¹) • T.b w.1 := by
      funext i; simp
    rw [this, norm_smul, norm_inv]
    congr 2
    simp [abs_of_pos Real.pi_pos]
  have e2 : ∀ g : Fin 2 → ℂ, ‖fun i => -(2 * Real.pi : ℂ)⁻¹ * g i‖ = (2 * Real.pi)⁻¹ * ‖g‖ := by
    intro g
    have : (fun i => -(2 * Real.pi : ℂ)⁻¹ * g i) = (-(2 * Real.pi : ℂ)⁻¹) • g := by
      funext i; simp
    rw [this, norm_smul, norm_neg, norm_inv]
    congr 2
    simp [abs_of_pos Real.pi_pos]
  unfold kamNorm homXnorm_gen stepField homRy_gen
  simp only [norm_neg, e1, e2]
  field_simp
  ring

theorem homU_stepZ (w : KamPhase) : homU (stepZ w) (stepZb w) = w.2.2.1 := by
  obtain ⟨θ, y, u, v⟩ := w
  rw [stepZ_apply, stepZb_apply]
  have h2 : homSqrt2 ^ 2 = 2 := by rw [sq]; exact homSqrt2_sq
  have hne := homSqrt2_ne
  unfold homU
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp
  ring_nf
  simp [h2]

theorem homV_stepZ (w : KamPhase) : homV (stepZ w) (stepZb w) = w.2.2.2 := by
  obtain ⟨θ, y, u, v⟩ := w
  rw [stepZ_apply, stepZb_apply]
  have h2 : homSqrt2 ^ 2 = 2 := by rw [sq]; exact homSqrt2_sq
  have hne := homSqrt2_ne
  unfold homV
  ext j
  simp only [lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub, Pi.smul_apply, Pi.add_apply,
    Pi.sub_apply, smul_eq_mul]
  field_simp
  ring_nf
  simp [h2, Complex.I_sq]

theorem homDomain_stepZ {r : ℝ} {w : KamPhase} (hw : w ∈ kamDomain s r) :
    HomDomain s r w.1 w.2.1 (stepZ w) (stepZb w) := by
  refine ⟨fun i => hw.1 i, hw.2.1, ?_⟩
  rw [homU_stepZ, homV_stepZ]
  exact hw.2.2

theorem stepFieldS_norm (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (r : ℝ) [Fact (0 < r)] (W : StepPhase r) :
    ‖stepFieldS ha hp hpb T r W‖ =
      homXnorm_gen ha hp hpb r T (StepPhase.toK W).1 (StepPhase.toK W).2.1
        (stepZ (StepPhase.toK W)) (stepZb (StepPhase.toK W)) := by
  rw [stepPhase_norm_eq]
  exact kamNorm_stepField ha hp hpb T (Fact.out : 0 < r) _

/-- W4's field bound `|X_R|_r ≤ ε` on `D(s,r)` is the bound `‖Z W‖ ≤ ε` on `D(s,r) ⊂ StepPhase r`. -/
theorem stepFieldS_bound (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (r : ℝ) [Fact (0 < r)] {ε : ℝ} (hX : HomFieldBound_gen ha hp hpb r ε T) {s' : ℝ}
    (hs' : s' ≤ s) {W : StepPhase r} (hW : W ∈ stepDomain r s' r) :
    ‖stepFieldS ha hp hpb T r W‖ ≤ ε := by
  rw [stepFieldS_norm]
  have hW' : StepPhase.toK W ∈ kamDomain s r :=
    kamDomain_mono hs' (Fact.out : 0 < r) le_rfl hW
  exact hX _ _ _ _ (homDomain_stepZ hW')

/-- **The flow hypotheses for the field of a Taylor polynomial** (`bpW:w5:flow`, concrete):
`FlowHyp (ι ∘ Z) V U M (σ/4)` with `V = D(s-σ,r)`, `U = D(s-2σ,r/2)` and `M` a bound for `|X_F|_r`. -/
theorem stepFlowHyp_concrete (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (r : ℝ) [Fact (0 < r)] {σ M : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hσs : 2 * σ < s)
    (hX : HomFieldBound_gen ha hp hpb r M T) (hM : 0 < M) (hMδ : M < σ / 4) :
    FlowHyp (smoothField (stepEmbedCLM a p pb hpb r) (stepFieldS ha hp hpb T r))
      (stepDomain r (s - σ) r) (stepDomain r (s - 2 * σ) (r / 2)) M (σ / 4) := by
  refine flowHyp_smooth (norm_stepEmbedCLM_apply_le a p pb hpb r) (stepDomain_isOpen _ _ _)
    (stepDomain_isOpen _ _ _) ?_ (fun z hz => stepFieldS_bound ha hp hpb T r hX (by linarith) hz)
    (fun w hw => stepDomain_margin hσ hσ1 hσs hw) hM hMδ
  intro z hz
  exact (stepFieldS_differentiableAt ha hp hpb T r
    (stepDomain_theta_mem (by linarith) hz)).differentiableWithinAt

end KAM.Wave
