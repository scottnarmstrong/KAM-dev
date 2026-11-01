/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.StepFlowConcrete
public import KAM.Wave.Homological.LieDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The normal form `N` on `KamPhase` and `DN·X_F = -L_N F` (blueprint-W `bpW:w5:flow-calc` (v))

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

`stepNfun` is W4's `homNfun` pulled back along the coordinate change `(θ,y,u,v) ↦ (θ,y,z,z̄)`
(`stepToHom`). `stepNfun_lie`: along the (embedded) field `ι X_F` of a Taylor polynomial,
`D N(w)(ι X_F(w)) = -L_N F(w)` (W4 `homLemma_lie_iv_gen`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- The coordinate change `KamPhase → HomPhase`, `(θ,y,u,v) ↦ (θ,y,z,z̄)`. -/
def stepToHom : KamPhase →L[ℂ] HomPhase :=
  (ContinuousLinearMap.fst ℂ _ _).prod ((ContinuousLinearMap.fst ℂ _ _).comp
      (ContinuousLinearMap.snd ℂ _ _) |>.prod (stepZ.prod stepZb))

theorem stepToHom_apply (w : KamPhase) :
    stepToHom w = (w.1, w.2.1, stepZ w, stepZb w) := rfl

section N

variable {γ K0 : ℝ} {Ω : ℕ+ → ℝ} (hG : HomGuard a p γ) (hK0 : 0 ≤ K0)
  (hΩ : ∀ j : ℕ+, |Ω j| ≤ K0 * ((j : ℝ) + 2)) (ω : Fin 2 → ℝ)

/-- `N` as a function on `KamPhase`. -/
def stepNfun (w : KamPhase) : ℂ := homNfun hG hK0 hΩ ω (stepToHom w)

theorem stepNfun_hasFDerivAt (w : KamPhase) :
    HasFDerivAt (stepNfun hG hK0 hΩ ω) ((homDN hG hK0 hΩ ω (stepToHom w)).comp stepToHom) w :=
  (homNfun_hasFDerivAt hG hK0 hΩ ω (stepToHom w)).comp w stepToHom.hasFDerivAt

/-- **`D N(w)(ι X_F(w)) = -L_N F(w)`** (`bpW:w5:flow-calc` (v), W4 `bpW:w4:lie` (iv)) in the
coordinates of `KamPhase`. -/
theorem stepNfun_lie (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (T : HomTaylor_gen a p pb s)
    (w : KamPhase) :
    (homDN hG hK0 hΩ ω (stepToHom w)).comp stepToHom (kamHomEmbed a p pb hpb
        (stepField ha hp hpb T w)) =
      -homLieN_gen ha hp hpb (homOmegaCarrier_of_guard (γ := γ) ha hp hpb hG hK0 hΩ) ω T w.1 w.2.1
        (stepZ w) (stepZb w) := by
  rw [← homLemma_lie_iv_gen hG hK0 hΩ ω ha hp hpb T w.1 w.2.1 (stepZ w) (stepZb w)]
  rw [ContinuousLinearMap.comp_apply, homDN_apply, homDN_apply]
  have h2 : homSqrt2 ^ 2 = 2 := by rw [sq]; exact homSqrt2_sq
  have hne := homSqrt2_ne
  simp only [stepToHom_apply, kamHomEmbed_apply, stepField, stepZ_apply, stepZb_apply]
  have hz : homSqrt2⁻¹ • (homEmbed_gen a p pb hpb (homRv_gen T w.1 (stepZ w) (stepZb w)) +
      Complex.I • homEmbed_gen a p pb hpb (-homRu_gen T w.1 (stepZ w) (stepZb w))) =
      (-Complex.I) • homEmbed_gen a p pb hpb (homRzb_gen T w.1 (stepZ w) (stepZb w)) := by
    unfold homRu_gen homRv_gen
    ext j
    simp only [map_smul, map_add, map_sub, map_neg, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub,
      lp.coeFn_neg, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    have hs2 : homSqrt2⁻¹ * homSqrt2⁻¹ = 1 / 2 := by
      rw [← mul_inv, homSqrt2_sq]; norm_num
    linear_combination
      (-2 * Complex.I * (homEmbed_gen a p pb hpb (homRzb_gen T w.1 (stepZ w) (stepZb w)) : HomL2) j)
        * hs2
  have hzb : homSqrt2⁻¹ • (homEmbed_gen a p pb hpb (homRv_gen T w.1 (stepZ w) (stepZb w)) -
      Complex.I • homEmbed_gen a p pb hpb (-homRu_gen T w.1 (stepZ w) (stepZb w))) =
      Complex.I • homEmbed_gen a p pb hpb (homRz_gen T w.1 (stepZ w) (stepZb w)) := by
    unfold homRu_gen homRv_gen
    ext j
    simp only [map_smul, map_add, map_sub, map_neg, lp.coeFn_smul, lp.coeFn_add, lp.coeFn_sub,
      lp.coeFn_neg, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    have hs2 : homSqrt2⁻¹ * homSqrt2⁻¹ = 1 / 2 := by
      rw [← mul_inv, homSqrt2_sq]; norm_num
    linear_combination
      (2 * Complex.I * (homEmbed_gen a p pb hpb (homRz_gen T w.1 (stepZ w) (stepZb w)) : HomL2) j)
        * hs2
  rw [hz, hzb]

end N

end KAM.Wave
