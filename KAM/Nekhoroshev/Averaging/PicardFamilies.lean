/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Picard iteration on bounded continuous families

Blueprint N Part 12 (`bpN:p12:ext-dep#complete-contraction`, `#picard`).

On `[-a, a] × closedBall x₀ r` consider bounded continuous maps `y` into the closed ball
`closedBall x₀ ρ` (the *trap*).  This is a closed subset of a complete space of bounded continuous
functions, and `y ↦ (t, x) ↦ x + ∫₀ᵗ F (y (τ, x)) dτ` maps it to itself and is a contraction with
constant `a * Λ` when `F` is `Λ`-Lipschitz on the trap, `‖F‖ ≤ L` there, `r + a * L ≤ ρ`.

* `KAM.Nekhoroshev.PicardBounds`: the numerical and regularity data of the trap.
* `KAM.Nekhoroshev.picardMap`, `contractingWith_picardMap`: the contraction on the complete trap.
* `KAM.Nekhoroshev.picard_family`: the real-variable output (iterates, limit, integral equation,
  geometric rate, time derivative) consumed by the derivative packages.
-/

@[expose] public noncomputable section

open Set Metric Function Filter
open scoped NNReal Topology BoundedContinuousFunction

namespace KAM.Nekhoroshev

section Picard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Numerical and regularity data for the Picard trap: `‖F‖ ≤ L` and `F` is `Λ`-Lipschitz on
`closedBall x₀ ρ`, `r + a L ≤ ρ`, and `a Λ < 1`. -/
structure PicardBounds (F : E → E) (x₀ : E) (a r ρ L : ℝ) (Λ : ℝ≥0) : Prop where
  nonneg_time : 0 ≤ a
  nonneg_bound : 0 ≤ L
  radius : r + a * L ≤ ρ
  bound : ∀ z ∈ closedBall x₀ ρ, ‖F z‖ ≤ L
  lipschitz : LipschitzOnWith Λ F (closedBall x₀ ρ)
  contracts : a * Λ < 1

/-- The time-space domain `[-a, a] × closedBall x₀ r` as a type. -/
abbrev PicardBase (x₀ : E) (a r : ℝ) : Type _ := Icc (-a) a × closedBall x₀ r

/-- The closed trap: bounded continuous families with values in `closedBall x₀ ρ`. -/
def PicardTrap (x₀ : E) (a r ρ : ℝ) : Set (PicardBase x₀ a r →ᵇ E) :=
  {y | ∀ p, y p ∈ closedBall x₀ ρ}

/-- The trap as a type; complete when `E` is. -/
abbrev PicardSpace (x₀ : E) (a r ρ : ℝ) : Type _ := ↥(PicardTrap x₀ a r ρ)

theorem isClosed_picardTrap (x₀ : E) (a r ρ : ℝ) : IsClosed (PicardTrap x₀ a r ρ) := by
  have : PicardTrap x₀ a r ρ = ⋂ p, {y | y p ∈ closedBall x₀ ρ} := by
    ext y; simp [PicardTrap]
  rw [this]
  exact isClosed_iInter fun p =>
    isClosed_closedBall.preimage (continuous_eval_const (F := PicardBase x₀ a r →ᵇ E) p)

instance [CompleteSpace E] (x₀ : E) (a r ρ : ℝ) : CompleteSpace (PicardSpace x₀ a r ρ) :=
  (isClosed_picardTrap x₀ a r ρ).completeSpace_coe

variable {F : E → E} {x₀ : E} {a r ρ L : ℝ} {Λ : ℝ≥0}

/-- The Picard integrand on the real time line, clamped to `[-a, a]`. -/
def picardIntegrand (F : E → E) (ha : 0 ≤ a) (y : PicardBase x₀ a r →ᵇ E)
    (x : closedBall x₀ r) (τ : ℝ) : E :=
  F (y (Set.projIcc (-a) a (neg_le_self ha) τ, x))

/-- The Picard operator, as a function on the base. -/
def picardFun (F : E → E) (ha : 0 ≤ a) (y : PicardBase x₀ a r →ᵇ E)
    (p : PicardBase x₀ a r) : E :=
  (p.2 : E) + ∫ τ in (0 : ℝ)..p.1, picardIntegrand F ha y p.2 τ

theorem continuous_picardIntegrand (ha : 0 ≤ a) (hF : ContinuousOn F (closedBall x₀ ρ))
    {y : PicardBase x₀ a r →ᵇ E} (hy : y ∈ PicardTrap x₀ a r ρ) :
    Continuous (fun q : PicardBase x₀ a r × ℝ => picardIntegrand F ha y q.1.2 q.2) := by
  refine hF.comp_continuous ?_ fun q => hy _
  exact y.continuous.comp
    ((continuous_projIcc.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst))

theorem continuous_picardFun (ha : 0 ≤ a) (hF : ContinuousOn F (closedBall x₀ ρ))
    {y : PicardBase x₀ a r →ᵇ E} (hy : y ∈ PicardTrap x₀ a r ρ) :
    Continuous (picardFun F ha y) := by
  unfold picardFun
  refine (continuous_subtype_val.comp continuous_snd).add ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : PicardBase x₀ a r) τ => picardIntegrand F ha y p.2 τ)
    (continuous_picardIntegrand ha hF hy) (continuous_subtype_val.comp continuous_fst)

theorem norm_integral_picardIntegrand_le (h : PicardBounds F x₀ a r ρ L Λ)
    {y : PicardBase x₀ a r →ᵇ E} (hy : y ∈ PicardTrap x₀ a r ρ) (p : PicardBase x₀ a r) :
    ‖∫ τ in (0 : ℝ)..p.1, picardIntegrand F h.nonneg_time y p.2 τ‖ ≤ a * L := by
  have h1 : ‖∫ τ in (0 : ℝ)..p.1, picardIntegrand F h.nonneg_time y p.2 τ‖ ≤
      L * |(p.1 : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => h.bound _ (hy _)
  have h2 : |(p.1 : ℝ) - 0| ≤ a := by
    rw [sub_zero, abs_le]; exact ⟨by linarith [p.1.2.1], p.1.2.2⟩
  calc _ ≤ L * |(p.1 : ℝ) - 0| := h1
    _ ≤ L * a := mul_le_mul_of_nonneg_left h2 h.nonneg_bound
    _ = a * L := mul_comm _ _

theorem picardFun_mem (h : PicardBounds F x₀ a r ρ L Λ)
    {y : PicardBase x₀ a r →ᵇ E} (hy : y ∈ PicardTrap x₀ a r ρ) (p : PicardBase x₀ a r) :
    picardFun F h.nonneg_time y p ∈ closedBall x₀ ρ := by
  rw [mem_closedBall, dist_eq_norm]
  have h1 : ‖(p.2 : E) - x₀‖ ≤ r := by
    rw [← dist_eq_norm]; exact mem_closedBall.1 p.2.2
  have h2 := norm_integral_picardIntegrand_le h hy p
  have : picardFun F h.nonneg_time y p - x₀ =
      ((p.2 : E) - x₀) + ∫ τ in (0 : ℝ)..p.1, picardIntegrand F h.nonneg_time y p.2 τ := by
    unfold picardFun; abel
  rw [this]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ r + a * L := add_le_add h1 h2
    _ ≤ ρ := h.radius

/-- The Picard operator on the trap, as a bounded continuous family. -/
def picardMap (h : PicardBounds F x₀ a r ρ L Λ) (y : PicardSpace x₀ a r ρ) :
    PicardSpace x₀ a r ρ :=
  ⟨BoundedContinuousFunction.mkOfBound
      ⟨picardFun F h.nonneg_time y.1,
        continuous_picardFun h.nonneg_time h.lipschitz.continuousOn y.2⟩ (2 * ρ)
      (fun p q => by
        have h1 := picardFun_mem h y.2 p
        have h2 := picardFun_mem h y.2 q
        calc dist _ _ ≤ dist (picardFun F h.nonneg_time y.1 p) x₀ +
              dist x₀ (picardFun F h.nonneg_time y.1 q) := dist_triangle _ _ _
          _ ≤ ρ + ρ := add_le_add (mem_closedBall.1 h1) (by rw [dist_comm]; exact mem_closedBall.1 h2)
          _ = 2 * ρ := by ring),
    fun p => picardFun_mem h y.2 p⟩

theorem picardMap_apply (h : PicardBounds F x₀ a r ρ L Λ) (y : PicardSpace x₀ a r ρ)
    (p : PicardBase x₀ a r) :
    (picardMap h y).1 p = picardFun F h.nonneg_time y.1 p := rfl

/-- `bpN:p12:ext-dep#complete-contraction`: the Picard operator is a contraction of the complete
trap, with constant `a * Λ`. -/
theorem contractingWith_picardMap (h : PicardBounds F x₀ a r ρ L Λ) :
    ContractingWith (Real.toNNReal a * Λ) (picardMap h) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
  · have : ((Real.toNNReal a * Λ : ℝ≥0) : ℝ) = a * Λ := by
      simp [Real.coe_toNNReal _ h.nonneg_time]
    rw [← NNReal.coe_lt_coe, this]; simpa using h.contracts
  · have hK : (((Real.toNNReal a * Λ : ℝ≥0)) : ℝ) = a * Λ := by
      simp [Real.coe_toNNReal _ h.nonneg_time]
    rw [hK, Subtype.dist_eq, Subtype.dist_eq]
    refine (BoundedContinuousFunction.dist_le (by positivity [h.nonneg_time])).2 fun p => ?_
    have hint : ∀ w : PicardSpace x₀ a r ρ, IntervalIntegrable
        (fun τ => picardIntegrand F h.nonneg_time w.1 p.2 τ) MeasureTheory.volume 0 p.1 :=
      fun w => Continuous.intervalIntegrable
        ((continuous_picardIntegrand h.nonneg_time h.lipschitz.continuousOn w.2).comp
          (continuous_const.prodMk continuous_id)) _ _
    rw [picardMap_apply, picardMap_apply, picardFun, picardFun, dist_eq_norm]
    have : ((p.2 : E) + ∫ τ in (0 : ℝ)..p.1, picardIntegrand F h.nonneg_time y.1 p.2 τ) -
        ((p.2 : E) + ∫ τ in (0 : ℝ)..p.1, picardIntegrand F h.nonneg_time z.1 p.2 τ) =
        ∫ τ in (0 : ℝ)..p.1, (picardIntegrand F h.nonneg_time y.1 p.2 τ -
          picardIntegrand F h.nonneg_time z.1 p.2 τ) := by
      rw [intervalIntegral.integral_sub (hint y) (hint z)]; abel
    rw [this]
    have h1 : ‖∫ τ in (0 : ℝ)..p.1, (picardIntegrand F h.nonneg_time y.1 p.2 τ -
          picardIntegrand F h.nonneg_time z.1 p.2 τ)‖ ≤ Λ * dist y.1 z.1 * |(p.1 : ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun τ _ => ?_
      rw [← dist_eq_norm]
      refine (h.lipschitz.dist_le_mul _ (y.2 _) _ (z.2 _)).trans ?_
      gcongr
      exact BoundedContinuousFunction.dist_coe_le_dist _
    have h2 : |(p.1 : ℝ) - 0| ≤ a := by
      rw [sub_zero, abs_le]; exact ⟨by linarith [p.1.2.1], p.1.2.2⟩
    calc _ ≤ Λ * dist y.1 z.1 * |(p.1 : ℝ) - 0| := h1
      _ ≤ Λ * dist y.1 z.1 * a := by gcongr
      _ = a * Λ * dist y.1 z.1 := by ring

end Picard

end KAM.Nekhoroshev
