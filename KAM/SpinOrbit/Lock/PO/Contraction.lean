/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Barrier
public import KAM.SpinOrbit.Lock.PO.Green
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The synchronous-orbit contraction (LOCK-PO)

Unfrozen helper code (design SO-LOCK §2.1).

* `soVq_add_one_add_one`, `soVq_neg_neg`: `∂_q V` is invariant under the diagonal integer shift and
  odd under `(q, φ) ↦ (-q, -φ)`.
* `soLip = 16 π² ε Σ |A_m|` and `soEta = 4 π ε Σ_{m ≠ 2} |A_m|`: the Lipschitz constant of `∂_q V`
  in `q` (`soVq_sub_abs_le`) and the size of the forcing on the diagonal (`soVq_diag_abs_le`).
* `syncForce d φ = -∂_q V(φ + d φ, φ)`: the force along the curve `q = φ + d φ`; it is odd and
  one-periodic when `d` is.
* `poSet`: the closed set of odd one-periodic bounded continuous functions; `syncMap` sends `d`
  to `green (syncForce d)`; `syncMap_contracting`: it is a contraction with constant `1/2`.
-/

@[expose] public noncomputable section

open Real Set
open scoped BoundedContinuousFunction

namespace KAM.SpinOrbit.Lock

/-! ### Symmetries and bounds of `∂_q V` -/

theorem soVq_add_one_add_one (q φ : ℝ) : soVq (q + 1) (φ + 1) = soVq q φ := by
  unfold soVq
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have : 2 * π * (2 * (q + 1) - m * (φ + 1)) =
      2 * π * (2 * q - m * φ) + ((2 - m : ℤ) : ℝ) * (2 * π) := by
    push_cast; ring
  rw [this, Real.sin_add_int_mul_two_pi]

theorem soVq_neg_neg (q φ : ℝ) : soVq (-q) (-φ) = -soVq q φ := by
  unfold soVq
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show 2 * π * (2 * -q - m * -φ) = -(2 * π * (2 * q - m * φ)) by ring, Real.sin_neg]
  ring

/-- The Lipschitz constant `16 π² ε Σ |A_m|` of `∂_q V` in `q`. -/
def soLip : ℝ := 16 * π ^ 2 * soEps * ∑ m ∈ soModes, |soA m|

/-- The forcing on the diagonal: `4 π ε Σ_{m ≠ 2} |A_m|`. -/
def soEta : ℝ := 4 * π * soEps * ∑ m ∈ soModes.erase 2, |soA m|

theorem soLip_nonneg : 0 ≤ soLip := by
  unfold soLip; have := soEps_pos; positivity

theorem soVq_sub_abs_le (a b φ : ℝ) : |soVq a φ - soVq b φ| ≤ soLip * |a - b| := by
  unfold soVq soLip
  have hε := soEps_pos
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * soEps)]
  have h : |∑ m ∈ soModes, (soA m * Real.sin (2 * π * (2 * a - m * φ)) -
      soA m * Real.sin (2 * π * (2 * b - m * φ)))| ≤
      ∑ m ∈ soModes, |soA m| * (4 * π * |a - b|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_)
    rw [show 2 * π * (2 * a - m * φ) - 2 * π * (2 * b - m * φ) = (4 * π) * (a - b) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
  rw [← Finset.sum_mul] at h
  calc 4 * π * soEps * |∑ m ∈ soModes, (soA m * Real.sin (2 * π * (2 * a - m * φ)) -
        soA m * Real.sin (2 * π * (2 * b - m * φ)))|
      ≤ 4 * π * soEps * ((∑ m ∈ soModes, |soA m|) * (4 * π * |a - b|)) := by gcongr
    _ = 16 * π ^ 2 * soEps * (∑ m ∈ soModes, |soA m|) * |a - b| := by ring

theorem soVq_diag_abs_le (φ : ℝ) : |soVq φ φ| ≤ soEta := by
  unfold soVq soEta
  have hε := soEps_pos
  have h2 : (2 : ℕ) ∈ soModes := by decide
  rw [← Finset.add_sum_erase _ _ h2]
  simp only [Nat.cast_ofNat, sub_self, mul_zero, Real.sin_zero, zero_add]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * soEps)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-! ### The force along a curve -/

/-- The force `-∂_q V(φ + d φ, φ)` along the curve `q = φ + d φ`. -/
def syncForce (d : ℝ → ℝ) (φ : ℝ) : ℝ := -soVq (φ + d φ) φ

theorem continuous_syncForce {d : ℝ → ℝ} (hd : Continuous d) : Continuous (syncForce d) := by
  unfold syncForce soVq
  fun_prop

theorem syncForce_periodic {d : ℝ → ℝ} (hd : Function.Periodic d 1) :
    Function.Periodic (syncForce d) 1 := fun φ => by
  simp only [syncForce, hd φ, show φ + 1 + d φ = φ + d φ + 1 by ring, soVq_add_one_add_one]

theorem syncForce_odd {d : ℝ → ℝ} (hd : ∀ x, d (-x) = -d x) (φ : ℝ) :
    syncForce d (-φ) = -syncForce d φ := by
  simp only [syncForce, hd φ, show -φ + -d φ = -(φ + d φ) by ring, soVq_neg_neg]

theorem syncForce_abs_le (d : ℝ → ℝ) (φ : ℝ) : |syncForce d φ| ≤ soForceBound := by
  rw [syncForce, abs_neg]; exact soVq_abs_le _ _

theorem syncForce_sub_abs_le (d e : ℝ → ℝ) (φ : ℝ) :
    |syncForce d φ - syncForce e φ| ≤ soLip * |d φ - e φ| := by
  have := soVq_sub_abs_le (φ + d φ) (φ + e φ) φ
  rw [show φ + d φ - (φ + e φ) = d φ - e φ by ring] at this
  rw [syncForce, syncForce, show -soVq (φ + d φ) φ - -soVq (φ + e φ) φ =
    -(soVq (φ + d φ) φ - soVq (φ + e φ) φ) by ring, abs_neg]
  exact this

theorem syncForce_abs_le_diag (d : ℝ → ℝ) (φ : ℝ) :
    |syncForce d φ| ≤ soEta + soLip * |d φ| := by
  have h1 := syncForce_sub_abs_le d 0 φ
  have h2 : |syncForce 0 φ| ≤ soEta := by
    simpa [syncForce] using soVq_diag_abs_le φ
  simp only [Pi.zero_apply, sub_zero] at h1
  calc |syncForce d φ| ≤ |syncForce d φ - syncForce 0 φ| + |syncForce 0 φ| := by
        simpa using abs_sub_le (syncForce d φ) (syncForce 0 φ) 0
    _ ≤ soEta + soLip * |d φ| := by linarith

/-! ### The space of odd one-periodic functions and the contraction -/

/-- The odd one-periodic bounded continuous functions. -/
def poSet : Set (ℝ →ᵇ ℝ) := {d | Function.Periodic d 1 ∧ ∀ x, d (-x) = -d x}

theorem isClosed_poSet : IsClosed poSet := by
  have hev : ∀ x : ℝ, Continuous fun d : ℝ →ᵇ ℝ => d x := fun x =>
    continuous_eval_const x
  have : poSet = (⋂ x : ℝ, {d : ℝ →ᵇ ℝ | d (x + 1) = d x}) ∩
      ⋂ x : ℝ, {d : ℝ →ᵇ ℝ | d (-x) = -d x} := by
    ext d; simp [poSet, Function.Periodic]
  rw [this]
  exact (isClosed_iInter fun x => isClosed_eq (hev _) (hev _)).inter
    (isClosed_iInter fun x => isClosed_eq (hev _) (hev x).neg)

instance : CompleteSpace poSet := isClosed_poSet.completeSpace_coe

instance : Nonempty poSet := ⟨⟨0, fun _ => rfl, fun _ => by simp⟩⟩

/-- The Green operator applied to the force along an odd one-periodic continuous curve: its
values and derivative are bounded through `dirichlet_bound`. -/
theorem green_syncForce_bound {d : ℝ → ℝ} (hd : Continuous d) (hp : Function.Periodic d 1)
    (ho : ∀ x, d (-x) = -d x) (x : ℝ) :
    |green (syncForce d) x| ≤ soForceBound / 32 := by
  have hf := continuous_syncForce hd
  exact (dirichlet_bound (hasDerivAt_green hf) (hasDerivAt_greenD hf) (syncForce_abs_le d)
    (half_int_zero (green_periodic hf (syncForce_periodic hp) (syncForce_odd ho))
      (green_odd (syncForce_odd ho))) x).1

/-- The synchronous-orbit map `d ↦ green (syncForce d)` on odd one-periodic functions. -/
def syncMap (d : poSet) : poSet :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (green (syncForce d.1))
      (continuous_green (continuous_syncForce d.1.continuous)) (soForceBound / 32)
      (fun x => by
        rw [Real.norm_eq_abs]; exact green_syncForce_bound d.1.continuous d.2.1 d.2.2 x),
    green_periodic (continuous_syncForce d.1.continuous) (syncForce_periodic d.2.1)
      (syncForce_odd d.2.2),
    green_odd (syncForce_odd d.2.2)⟩

theorem syncMap_apply (d : poSet) (x : ℝ) : (syncMap d).1 x = green (syncForce d.1) x := rfl

/-- The Dirichlet estimate for the difference of two images: `‖T d - T e‖ ≤ (L/32) ‖d - e‖`. -/
theorem dist_syncMap_le (d e : poSet) : dist (syncMap d) (syncMap e) ≤ soLip / 32 * dist d e := by
  have hfd := continuous_syncForce d.1.continuous
  have hfe := continuous_syncForce e.1.continuous
  have hD : 0 ≤ dist d e := dist_nonneg
  have hpd := green_periodic hfd (syncForce_periodic d.2.1) (syncForce_odd d.2.2)
  have hpe := green_periodic hfe (syncForce_periodic e.2.1) (syncForce_odd e.2.2)
  have hpt : ∀ x, |d.1 x - e.1 x| ≤ dist d e := fun x => by
    have := BoundedContinuousFunction.dist_coe_le_dist (f := d.1) (g := e.1) x
    rwa [Real.dist_eq, ← Subtype.dist_eq] at this
  have hod := green_odd (syncForce_odd d.2.2)
  have hoe := green_odd (syncForce_odd e.2.2)
  have hb := dirichlet_bound (u := fun x => green (syncForce d.1) x - green (syncForce e.1) x)
    (u' := fun x => greenD (syncForce d.1) x - greenD (syncForce e.1) x)
    (f := fun x => syncForce d.1 x - syncForce e.1 x) (M := soLip * dist d e)
    (fun x => (hasDerivAt_green hfd x).sub (hasDerivAt_green hfe x))
    (fun x => (hasDerivAt_greenD hfd x).sub (hasDerivAt_greenD hfe x))
    (fun x => (syncForce_sub_abs_le _ _ x).trans (mul_le_mul_of_nonneg_left
      (hpt x) soLip_nonneg))
    (half_int_zero (hpd.sub hpe) (fun x => by simp only [Pi.sub_apply, hod, hoe]; ring))
  rw [Subtype.dist_eq, BoundedContinuousFunction.dist_le (by have := soLip_nonneg; positivity)]
  intro x
  rw [Real.dist_eq, syncMap_apply, syncMap_apply]
  have := (hb x).1
  rw [Subtype.dist_eq] at this ⊢
  linarith

/-- Numerical crude bound `L ≤ 16`. -/
theorem soLip_le : soLip ≤ 16 := by
  have hS : ∑ m ∈ soModes, |soA m| ≤ 1 := by
    simp only [soModes, soA, soEcc]
    norm_num [Finset.sum_Icc_succ_top, soCoeffPoly, abs_of_pos, abs_of_neg]
  have hε := soEps_pos
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  unfold soLip
  calc 16 * π ^ 2 * soEps * ∑ m ∈ soModes, |soA m| ≤ 16 * π ^ 2 * soEps * 1 := by gcongr
    _ ≤ 16 := by unfold soEps; nlinarith

/-- `syncMap` is a contraction with constant `1/2`. -/
theorem syncMap_contracting : ContractingWith (1 / 2) syncMap := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun d e => ?_⟩
  refine (dist_syncMap_le d e).trans ?_
  have := soLip_le
  have hD : 0 ≤ dist d e := dist_nonneg
  push_cast
  nlinarith

end KAM.SpinOrbit.Lock

end
