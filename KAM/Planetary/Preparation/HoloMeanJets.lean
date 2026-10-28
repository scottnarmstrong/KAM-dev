/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.HoloMeanHolo
public import KAM.Planetary.Preparation.HoloMeanSchwarz
public import KAM.Planetary.Preparation.AnalyticExtension
public import KAM.Strip.AnalyticTaylor
public import KAM.Strip.RealRestriction

/-!
# Complex jets from real bounds, in `(J, z)` (P11A-P2e, `stepP:p11:hc-mean`)

`p11_jets_zero_gen`: a holomorphic `G (J, z)` on the product domain `p11MeanDom J₀ r rz` that is
`O(‖z‖ᵏ)` on real points `(ι J, ι₂ z)` for each real `J` has vanishing `z`-jets of order `< k` at
`z = 0` for every complex `J` in the ball and every direction `v` in `B(0, rz)`. Steps: the line
`s ↦ G (ι J, s v)` (`p11_jets_zero_of_real_bound`); the diagonal polynomial `v ↦ D^j G(v, …, v)`
vanishes on real `v` hence on `ℂ`-points (`p11_real_slice_identity`); finally the identity theorem
in `J`.
-/

@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace KAM.Planetary

section Jets

variable {n : ℕ}

/-- Splitting `ℂ^{n+n} ≅ ℂⁿ × ℂⁿ`. -/
def p11Split (n : ℕ) : P11CVec (n + n) →L[ℂ] P11Phase n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (fun i => w (Fin.castAdd n i), fun i => w (Fin.natAdd n i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem p11Split_apply (w : P11CVec (n + n)) :
    p11Split n w = (fun i => w (Fin.castAdd n i), fun i => w (Fin.natAdd n i)) := rfl

/-- A holomorphic function on `ℂ²ⁿ` vanishing on the real points of a ball vanishes on the ball. -/
theorem p11_phase_real_slice {ρ : ℝ} (hρ : 0 < ρ) {P : P11Phase n → ℂ}
    (hP : Differentiable ℂ P) (hz : ∀ z' : Phase n, ‖z'‖ < ρ → P (KAM.realInclusion₂ n z') = 0) :
    ∀ z : P11Phase n, ‖z‖ < ρ → P z = 0 := by
  have h := p11_real_slice_identity (n := n + n) (x := 0) hρ
    (F := fun w => P (p11Split n w)) (hP.comp (p11Split n).differentiable).differentiableOn
    (fun y hy => by
      have : p11Split n (KAM.realInclusion (n + n) y) = KAM.realInclusion₂ n
          (fun i => y (Fin.castAdd n i), fun i => y (Fin.natAdd n i)) := by
        refine Prod.ext ?_ ?_ <;> funext i <;> simp [p11Split_apply]
      rw [this]
      refine hz _ ?_
      rw [sub_zero] at hy
      rw [Prod.norm_def, max_lt_iff]
      exact ⟨(pi_norm_lt_iff hρ).2 fun i => (norm_le_pi_norm y _).trans_lt hy,
        (pi_norm_lt_iff hρ).2 fun i => (norm_le_pi_norm y _).trans_lt hy⟩)
  intro z hzρ
  have hw : KAM.realInclusion (n + n) 0 = 0 := map_zero _
  have hmem : (Fin.append z.1 z.2 : P11CVec (n + n)) ∈
      Metric.ball (KAM.realInclusion (n + n) (0 : P11Vec (n + n))) ρ := by
    rw [hw, mem_ball_zero_iff, Prod.norm_def, max_lt_iff] at *
    refine (pi_norm_lt_iff hρ).2 fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using (norm_le_pi_norm z.1 j).trans_lt hzρ.1
    · simpa using (norm_le_pi_norm z.2 j).trans_lt hzρ.2
  have := h _ hmem
  have hs : p11Split n (Fin.append z.1 z.2) = z :=
    Prod.ext (funext fun i => by simp [p11Split_apply]) (funext fun i => by simp [p11Split_apply])
  simpa [hs] using this

end Jets

end KAM.Planetary

end
