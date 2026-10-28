/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakKAM.IterationRecord
public import KAM.Planetary.WeakKAM.IterationAssemble
public import KAM.Planetary.WeakKAM.IterationStep
public import KAM.Planetary.WeakKAM.Budgets

/-! # P11B inductive lemma (`bpP:p11a:inductive-lemma`)

`inductive_lemma` and `inductive_lemma_adapted` build a whole coherent iteration
`SelectionIteration d f a` at the schedule `adm_params d ε` and at the ε-adapted schedule
`selectionAdapted d ε`. The proof is the source induction `(P_ν) ⟹ (P_{ν+1})`: the base case
`iterPre_base`, one step `iterPrefix_step` (retained set `K_{ν+1}`, increments on the whole collar,
canonical step at `E = K_{ν+1}`), and the coherent assembly `selectionIteration_of_step`, which
reads the infinite chain off the sequence of prefixes.

The conditional helpers `selection_iteration_parameter_blocks` (`O4`, separate sup bounds) and
`selection_iteration_parameter_first` (`E4`, `j = 1`, `t' = t/2`) are stated on an output record.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Filter Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
variable {n : ℕ}

/-- One coherent step `(P_ν) ⟹ (P_{ν+1})` at the schedule `selectionSchedGen d s₀ ε₀`. -/
theorem iterPrefix_step (d : SelectionData n) (f : SelectionPhaseC n → ℂ) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (ν : ℕ) (ch : SelectionChain n) (hp : IterPrefix d f (selectionSchedGen d s₀ ε₀) ch ν) :
    ∃ c' : SelectionChain n, ChainAgree ν ch c' ∧
      IterPrefix d f (selectionSchedGen d s₀ ε₀) c' (ν + 1) := by
  have c : WeakBudgetCtx d (selectionSchedGen d s₀ ε₀) :=
    weakBudgetCtx_of d _ hA rfl rfl rfl rfl rfl rfl hs he0
  have hf := stepFacts_of_ctx c ν
  have hpre := (hp ν le_rfl).1
  have hne := selectionRetained_nonempty d s₀ ε₀ hA hs he0 hpre.chain
  have hag := stepChain_agree (ch := ch) hf
  refine ⟨stepChain d _ ch ν hf, hag, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (ν + 1) with h | h
  · refine ⟨(hp j (by omega)).1.transfer (hag.mono (by omega)), fun _ => ?_⟩
    rcases Nat.lt_or_ge j ν with h' | h'
    · exact ((hp j (by omega)).2 h').transfer (hag.mono (by omega))
    · obtain rfl : j = ν := by omega
      exact iterPost_step c hf hpre
  · obtain rfl : j = ν + 1 := by omega
    exact ⟨iterPre_step c hf hpre hne, fun h => absurd h (by omega)⟩

/-- The iteration at the schedule `selectionSchedGen d s₀ ε₀`, for an admissible pair. -/
theorem selectionIteration_gen (d : SelectionData n) (f : SelectionPhaseC n → ℂ) {ε : ℝ}
    (hf : SelectionPerturbation d f ε) (s₀ ε₀ : ℝ)
    (hA : SelectionAdmissibility d (selectionSchedGen d s₀ ε₀)) (hs : 0 < s₀) (he0 : 0 < ε₀)
    (hε₀ : ε + n / 2 * d.C₁ * s₀ ^ 2 ≤ ε₀) :
    Nonempty (SelectionIteration d f (selectionSchedGen d s₀ ε₀)) := by
  have c : WeakBudgetCtx d (selectionSchedGen d s₀ ε₀) :=
    weakBudgetCtx_of d _ hA rfl rfl rfl rfl rfl rfl hs he0
  refine selectionIteration_of_step d f _ (selectionBaseChain d f) ?_
    (fun ν ch hp => iterPrefix_step d f s₀ ε₀ hA hs he0 ν ch hp)
  intro j hj
  obtain rfl : j = 0 := by omega
  exact ⟨iterPre_base c f hf hε₀, fun h => absurd h (by omega)⟩

/-- All finite chains are built coherently by extending the existing chain. -/
theorem inductive_lemma (d : SelectionData n) (ε : ℝ) (he : 0 ≤ ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) : Nonempty (SelectionIteration d f (adm_params d ε)) := by
  obtain ⟨hA, -, hs, he0⟩ := selection_adm_facts d ε he hsmall
  exact selectionIteration_gen d f hf (adm_params d ε).s₀ (adm_params d ε).ε₀ hA hs he0 le_rfl

theorem inductive_lemma_adapted (d : SelectionData n) (ε : ℝ) (he : 0 < ε)
    (hsmall : ε ≤ selectionAdmissible d) (f : SelectionPhaseC n → ℂ)
    (hf : SelectionPerturbation d f ε) :
    Nonempty (SelectionIteration d f (selectionAdapted d ε)) := by
  obtain ⟨hA, hs, -, hε, -, -⟩ := free_radius d ε he hsmall
  have he0 : 0 < (selectionAdapted d ε).ε₀ := by
    show 0 < 2 * ε
    positivity
  exact selectionIteration_gen d f hf (selectionAdapted d ε).s₀ (selectionAdapted d ε).ε₀ hA hs
    he0 hε.ge

/-- Conditional implementation helper for source O4. Apply parameter Cauchy separately to
holomorphic angle/action defects with their separate sup bounds, not to the joint max estimate. -/
theorem selection_iteration_parameter_blocks (d : SelectionData n)
    (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n) (o : SelectionIteration d f a)
    (ν : ℕ) (t' : ℝ) (ht' : 0 < t') (htt : t' < selectiont a (ν + 1))
    (z : SelectionPhaseC n) (hz : z.1 ∈ complexStrip n (selectionr a (ν + 1)))
    (hη : ‖z.2‖ < selections a (ν + 1))
    (b : SelectionC n) (hb : b ∈ actionNbhd (o.K (ν + 1)) t') (j : ℕ) :
    ‖iteratedFDeriv ℂ j (fun c => (o.X ν c z).1 - z.1) b‖ ≤
      (j : ℝ) ^ j * selectionA a ν / (selectiont a (ν + 1) - t') ^ j ∧
    ‖iteratedFDeriv ℂ j (fun c => (o.X ν c z).2 - z.2) b‖ ≤
      (j : ℝ) ^ j * selectionAlpha a ν / (selectiont a (ν + 1) - t') ^ j := by
  have hd : DifferentiableOn ℂ (fun c => o.X ν c z) (actionNbhd (o.K (ν + 1))
      (selectiont a (ν + 1))) :=
    (o.map_holo ν).comp ((differentiableOn_const z).prodMk differentiableOn_id)
      fun c hc => ⟨hz, hη, hc⟩
  have hmem : ∀ c ∈ actionNbhd (o.K (ν + 1)) (selectiont a (ν + 1)),
      ((z, c) : SelectionPoint n) ∈ selectionDomain (selectionr a (ν + 1))
        (selections a (ν + 1)) (actionNbhd (o.K (ν + 1)) (selectiont a (ν + 1))) :=
    fun c hc => ⟨hz, hη, hc⟩
  refine ⟨?_, ?_⟩
  · exact param_cauchy_gen (E := o.K (ν + 1)) ht' htt
      ((differentiable_fst.comp_differentiableOn hd).sub_const _)
      (fun c hc => o.map_angle_bound ν (z, c) (hmem c hc)) j b hb
  · exact param_cauchy_gen (E := o.K (ν + 1)) ht' htt
      ((differentiable_snd.comp_differentiableOn hd).sub_const _)
      (fun c hc => o.map_action_bound ν (z, c) (hmem c hc)) j b hb

/-- Conditional implementation helper exporting E4 from the joint j=1 Cauchy bound. -/
theorem selection_iteration_parameter_first (d : SelectionData n)
    (f : SelectionPhaseC n → ℂ) (a : SelectionSchedule n) (o : SelectionIteration d f a)
    (ν : ℕ) (ht : 0 < selectiont a (ν + 1))
    (z : SelectionPhaseC n) (hz : z.1 ∈ complexStrip n (selectionr a (ν + 1)))
    (hη : ‖z.2‖ < selections a (ν + 1))
    (b : SelectionC n) (hb : b ∈ actionNbhd (o.K (ν + 1)) (selectiont a (ν + 1) / 2)) :
    ‖fderiv ℂ (fun c => o.X ν c z - z) b‖ ≤
      2 * max (selectionA a ν) (selectionAlpha a ν) / selectiont a (ν + 1) := by
  have h := o.map_parameter_bound ν (selectiont a (ν + 1) / 2) (half_pos ht)
    (half_lt_self ht) z hz hη b hb 1
  rw [norm_iteratedFDeriv_one] at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring

/-- `real_angle_derivative` of the extended chain (the collar supplier of the design, N1): for
every real `b` of the collar `K_{ν+1} + t_{ν+1}` (not only `b ∈ K_{ν+1}`) the angle block of the
time-one map has derivative within `exp (selectionRealBudget a ν) - 1` of the identity. -/
theorem selection_real_angle_derivative_on_collar {d : SelectionData n}
    {f : SelectionPhaseC n → ℂ} {a : SelectionSchedule n} (c : WeakBudgetCtx d a)
    {ch : SelectionChain n} {ν : ℕ} (hf : StepFacts a d.C₁ ν) (hpre : IterPre d f a ch ν) :
    ∀ b : SelectionR n,
      selectionReal b ∈ actionNbhd (selectionRetained a d ch ν) (selectiont a (ν + 1)) → ∀ θ,
      ‖fderiv ℝ (fun v : SelectionR n =>
          selectionRe (((stepChain d a ch ν hf).X ν (selectionReal b) (selectionReal v, 0)).1)) θ -
        ContinuousLinearMap.id ℝ (SelectionR n)‖ ≤ Real.exp (selectionRealBudget a ν) - 1 := by
  intro b hb θ
  have := (iterPost_step c hf hpre).real_angle_derivative b (by rwa [stepChain_K_succ]) θ
  exact this

end KAM.Planetary

end
