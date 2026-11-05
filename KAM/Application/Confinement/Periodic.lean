/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Application.Confinement.Level
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Confinement: periodic C¹ maps are Lipschitz and bounded on an action box

`exists_lipschitzOnWith_of_periodic`: a map `V` on a chart `ℝⁿ × ℝᵐ` (angles, actions) that is `C¹`
on an open set containing the action box `ℝⁿ × [α, β]` and `ℤⁿ`-periodic in the angles is
Lipschitz and bounded on the box. Typically `V` is a Hamiltonian vector field in an action–angle
chart, where it is periodic in the angles but defined only for positive actions, so not globally
`C¹`. Its value and derivative are bounded on the compact `[0, 1]ⁿ × [α, β]`, periodicity carries
the bounds to the whole box, and the mean value inequality on the convex box gives the Lipschitz
bound.
-/

public section

open Set
open scoped NNReal

namespace KAM.Application.Confinement

variable {n m : ℕ}

/-- The fractional part of the angles: `(θ − ⌊θ⌋, a)`. -/
@[expose] noncomputable def fractAngles (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    (Fin n → ℝ) × (Fin m → ℝ) :=
  (fun j => Int.fract (p.1 j), p.2)

theorem fractAngles_mem {α β : Fin m → ℝ} {p : (Fin n → ℝ) × (Fin m → ℝ)}
    (hp : p ∈ boxSet α β) :
    fractAngles p ∈ (Icc (0 : Fin n → ℝ) 1 : Set (Fin n → ℝ)) ×ˢ Icc α β :=
  ⟨⟨fun _ => Int.fract_nonneg _, fun _ => (Int.fract_lt_one _).le⟩, hp⟩

theorem fractAngles_add (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    fractAngles p + ((fun j => ((⌊p.1 j⌋ : ℤ) : ℝ)), 0) = p := by
  refine Prod.ext (funext fun j => ?_) ?_
  · simp only [fractAngles, Prod.fst_add, Pi.add_apply]
    exact Int.fract_add_floor _
  · simp [fractAngles]

theorem shift_eq (q : (Fin n → ℝ) × (Fin m → ℝ)) (k : Fin n → ℤ) :
    ((q.1 + fun j => (k j : ℝ)), q.2) = q + ((fun j => (k j : ℝ)), (0 : Fin m → ℝ)) :=
  Prod.ext rfl (add_zero _).symm

theorem convex_boxSet (α β : Fin m → ℝ) :
    Convex ℝ (boxSet α β : Set ((Fin n → ℝ) × (Fin m → ℝ))) := by
  have : (boxSet α β : Set ((Fin n → ℝ) × (Fin m → ℝ))) =
      (univ : Set (Fin n → ℝ)) ×ˢ Icc α β := by
    ext p
    simp [boxSet]
  rw [this]
  exact convex_univ.prod (convex_Icc α β)

/-- **Periodic C¹ maps are Lipschitz and bounded on the action box.** -/
theorem exists_lipschitzOnWith_of_periodic {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {V : (Fin n → ℝ) × (Fin m → ℝ) → F} {α β : Fin m → ℝ}
    {U : Set ((Fin n → ℝ) × (Fin m → ℝ))} (hU : IsOpen U)
    (hBU : boxSet α β ⊆ U) (hV : ContDiffOn ℝ 1 V U)
    (hper : ∀ p : (Fin n → ℝ) × (Fin m → ℝ), ∀ k : Fin n → ℤ,
      V (p.1 + (fun j => (k j : ℝ)), p.2) = V p) :
    ∃ K : ℝ≥0, ∃ C : ℝ, LipschitzOnWith K V (boxSet α β) ∧ ∀ p ∈ boxSet α β, ‖V p‖ ≤ C := by
  set Kc : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
    (Icc (0 : Fin n → ℝ) 1 : Set (Fin n → ℝ)) ×ˢ Icc α β with hKc
  have hKcc : IsCompact Kc := isCompact_Icc.prod isCompact_Icc
  have hKcU : Kc ⊆ U := fun p hp => hBU hp.2
  have hVc : ContinuousOn V U := hV.continuousOn
  have hDc : ContinuousOn (fderiv ℝ V) U := hV.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C, hC⟩ := hKcc.exists_bound_of_continuousOn (hVc.mono hKcU)
  obtain ⟨D, hD⟩ := hKcc.exists_bound_of_continuousOn (hDc.mono hKcU)
  -- periodicity of the value and of the derivative
  have hshift : ∀ k : Fin n → ℤ,
      (fun q : (Fin n → ℝ) × (Fin m → ℝ) => V (q + ((fun j => (k j : ℝ)), 0))) = V := fun k => by
    funext q
    rw [← shift_eq]
    exact hper q k
  have hval : ∀ p : (Fin n → ℝ) × (Fin m → ℝ), V p = V (fractAngles p) := fun p => by
    conv_lhs => rw [← fractAngles_add p]
    rw [← shift_eq]
    exact hper (fractAngles p) fun j => ⌊p.1 j⌋
  have hder : ∀ p : (Fin n → ℝ) × (Fin m → ℝ),
      fderiv ℝ V p = fderiv ℝ V (fractAngles p) := fun p => by
    have h := congrArg (fun f => fderiv ℝ f (fractAngles p)) (hshift fun j => ⌊p.1 j⌋)
    rw [fderiv_comp_add_right, fractAngles_add] at h
    exact h
  have hdiff : ∀ p ∈ boxSet α β, DifferentiableAt ℝ V p := fun p hp =>
    (hV.differentiableOn one_ne_zero p (hBU hp)).differentiableAt (hU.mem_nhds (hBU hp))
  refine ⟨D.toNNReal, C, ?_, fun p hp => ?_⟩
  · refine (convex_boxSet α β).lipschitzOnWith_of_nnnorm_fderiv_le hdiff fun p hp => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal', hder p]
    exact (hD _ (fractAngles_mem hp)).trans (le_max_left _ _)
  · rw [hval p]
    exact hC _ (fractAngles_mem hp)

end KAM.Application.Confinement
