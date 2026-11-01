/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.TaylorField
public import KAM.Wave.Analytic.HoloAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Holomorphy of the field of a Taylor polynomial (blueprint-W `bpW:w5:solve`, step `s-class`)

Off-frontier, source-faithful infrastructure (W5-STEP); the dependency graph is still being built.

The components of `T ∈ 𝒯_s` are holomorphic on the open strip, hence analytic
(`bpW:w1:holo-analytic-fd`), so their coordinate derivatives are holomorphic too. This gives
`stepField T` complex differentiable at every point with `θ ∈ T_s` (`stepField_differentiableAt`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

theorem differentiableOn_homPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : (Fin 2 → ℂ) → E} (hf : DifferentiableOn ℂ f (complexStrip 2 s))
    (i : Fin 2) : DifferentiableOn ℂ (homPartial i f) (complexStrip 2 s) := by
  have han := analyticOnNhd_of_differentiableOn_banach (isOpen_complexStrip 2 s) hf
  have h1 := (han.fderiv).differentiableOn
  have h2 := (ContinuousLinearMap.apply ℂ E (Pi.single i (1 : ℂ) : Fin 2 → ℂ)).differentiable
  exact h2.comp_differentiableOn h1

theorem stepField_differentiableAt (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb)
    (T : HomTaylor_gen a p pb s) {w : KamPhase} (hw : w.1 ∈ complexStrip 2 s) :
    DifferentiableAt ℂ (stepField ha hp hpb T) w := by
  have hn : complexStrip 2 s ∈ nhds w.1 := (isOpen_complexStrip 2 s).mem_nhds hw
  have hθ : DifferentiableAt ℂ (fun x : KamPhase => x.1) w := differentiableAt_fst
  have hy : DifferentiableAt ℂ (fun x : KamPhase => x.2.1) w :=
    differentiableAt_fst.comp w differentiableAt_snd
  have hz : DifferentiableAt ℂ (fun x : KamPhase => stepZ x) w := stepZ.differentiableAt
  have hzb : DifferentiableAt ℂ (fun x : KamPhase => stepZb x) w := stepZb.differentiableAt
  have c : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {f : (Fin 2 → ℂ) → E}, DifferentiableOn ℂ f (complexStrip 2 s) →
      DifferentiableAt ℂ (fun x : KamPhase => f x.1) w := fun hf =>
    (hf.differentiableAt hn).comp w hθ
  have dpart : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
      {f : (Fin 2 → ℂ) → E}, DifferentiableOn ℂ f (complexStrip 2 s) → ∀ i,
      DifferentiableAt ℂ (fun x : KamPhase => homPartial i f x.1) w := fun hf i =>
    c (differentiableOn_homPartial hf i)
  have dRz : DifferentiableAt ℂ (fun x : KamPhase => homRz_gen T x.1 (stepZ x) (stepZb x)) w := by
    unfold homRz_gen
    have := c T.comp_cp.1; have := c T.comp_P.1; have := c T.comp_Qt.1
    fun_prop
  have dRzb : DifferentiableAt ℂ (fun x : KamPhase => homRzb_gen T x.1 (stepZ x) (stepZb x)) w := by
    unfold homRzb_gen
    have := c T.comp_cm.1; have := c T.comp_Q.1; have := c T.comp_P'.1
    fun_prop
  refine DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ ?_))
  · refine differentiableAt_pi.2 fun i => ?_
    have := differentiableAt_pi.1 (c T.comp_b.1) i
    fun_prop
  · refine differentiableAt_pi.2 fun i => ?_
    unfold homRtheta_gen
    have e : ∀ c z, homPairRep_gen ha (homPP hp hpb) c z = stepPr ha (homPP hp hpb) c z :=
      fun _ _ => rfl
    simp only [e]
    have := dpart T.comp_a0.1 i; have := dpart T.comp_b.1 i; have := dpart T.comp_cp.1 i
    have := dpart T.comp_cm.1 i; have := dpart T.comp_P.1 i; have := dpart T.comp_Q.1 i
    have := dpart T.comp_P'.1 i
    have hb : ∀ k, DifferentiableAt ℂ (fun x : KamPhase => homPartial i T.b x.1 k) w := fun k =>
      (differentiableAt_pi.1 (dpart T.comp_b.1 i)) k
    fun_prop
  · unfold homRv_gen; fun_prop
  · unfold homRu_gen; fun_prop

end KAM.Wave
