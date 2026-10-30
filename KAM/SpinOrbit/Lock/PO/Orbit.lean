/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.PO.Contraction
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The synchronous periodic orbit ψ* (LOCK-PO)

Unfrozen helper code (design SO-LOCK §1.1, §1.4, §2.1).

* `IsSyncOrbit ψ`: `ψ` is `C²`, one-periodic, odd and solves `ψ'' = -∂_q V(φ + ψ, φ)`.
* `lunarSyncOrbit`: **the** synchronous orbit ψ* (chosen; canonical by uniqueness).
* `lunarSyncOrbit_spec`: existence, from the fixed point of the contraction `syncMap`.
* `lunarSyncOrbit_unique`: every odd one-periodic synchronous orbit is ψ* (every such orbit is a
  fixed point of `syncMap`). Uniqueness among all one-periodic orbits is false (`ψ + 1/2`).
* `lunarSyncOrbit_bound`: `|ψ*| ≤ 17/10⁶`, `|ψ*′| ≤ 27/200000`, from the rational majorants
  `L ≤ 3377/10⁵`, `η ≤ 5355/10⁷` (design §1.4).
-/

@[expose] public noncomputable section

open Real Set

namespace KAM.SpinOrbit.Lock

/-! ### Definitions -/

/-- `ψ` is a synchronous periodic orbit of the physical model: `q(t) = φ(t) + ψ(φ(t))`,
`p(t) = 1 + ψ'(φ(t))`, `φ(t) = φ₀ + t` solves `soField`, i.e. `ψ'' = −∂_q V(φ + ψ, φ)`;
`ψ` is `C²`, one-periodic and odd (reversibility). -/
def IsSyncOrbit (ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 ψ ∧ Function.Periodic ψ 1 ∧ (∀ φ, ψ (-φ) = -ψ φ) ∧
    ∀ φ, deriv (deriv ψ) φ = -soVq (φ + ψ φ) φ

open Classical in
/-- **The** synchronous periodic orbit ψ*, named explicitly (D45 addendum): the unique odd
one-periodic synchronous orbit (`lunarSyncOrbit_unique`; existence `lunarSyncOrbit_spec`). -/
def lunarSyncOrbit : ℝ → ℝ :=
  if h : ∃ ψ, IsSyncOrbit ψ then Classical.choose h else 0

/-! ### Orbits as solutions of the Green problem -/

theorem IsSyncOrbit.hasDerivAt {ψ : ℝ → ℝ} (h : IsSyncOrbit ψ) (x : ℝ) :
    HasDerivAt ψ (deriv ψ x) x :=
  ((h.1.differentiable (by norm_num)) x).hasDerivAt

theorem IsSyncOrbit.hasDerivAt_deriv {ψ : ℝ → ℝ} (h : IsSyncOrbit ψ) (x : ℝ) :
    HasDerivAt (deriv ψ) (syncForce ψ x) x := by
  have h2 : ContDiff ℝ (1 + 1) ψ := h.1
  have h1 : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.1 h2).2.2
  rw [syncForce, ← h.2.2.2 x]
  exact ((h1.differentiable (by norm_num)) x).hasDerivAt

/-- An odd one-periodic solution of `u'' = syncForce u` is the Green image of its force. -/
theorem green_syncForce_eq {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (syncForce u x) x) (hp : Function.Periodic u 1)
    (ho : ∀ x, u (-x) = -u x) : green (syncForce u) = u := by
  have hc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hf := continuous_syncForce hc
  funext x
  have hb := dirichlet_bound (u := fun x => green (syncForce u) x - u x)
    (u' := fun x => greenD (syncForce u) x - u' x) (f := fun _ => 0) (M := 0)
    (fun x => (hasDerivAt_green hf x).sub (hu x))
    (fun x => by
      have := (hasDerivAt_greenD hf x).sub (hu' x); rw [sub_self] at this; exact this)
    (fun _ => by simp)
    (half_int_zero ((green_periodic hf (syncForce_periodic hp) (syncForce_odd ho)).sub hp)
      (fun x => by simp only [Pi.sub_apply, green_odd (syncForce_odd ho), ho]; ring)) x
  have := hb.1
  rw [zero_div, abs_nonpos_iff, sub_eq_zero] at this
  exact this

/-- A uniform bound on any odd one-periodic solution: `|u| ≤ soForceBound / 32`. -/
theorem abs_le_of_syncForce {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (syncForce u x) x) (hp : Function.Periodic u 1)
    (ho : ∀ x, u (-x) = -u x) (x : ℝ) : |u x| ≤ soForceBound / 32 :=
  (dirichlet_bound hu hu' (syncForce_abs_le u) (half_int_zero hp ho) x).1

/-- An odd one-periodic solution as a point of `poSet`. -/
def toPoSet {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (syncForce u x) x) (hp : Function.Periodic u 1)
    (ho : ∀ x, u (-x) = -u x) : poSet :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup u
      (continuous_iff_continuousAt.2 fun x => (hu x).continuousAt) (soForceBound / 32)
      (fun x => by rw [Real.norm_eq_abs]; exact abs_le_of_syncForce hu hu' hp ho x),
    hp, ho⟩

theorem toPoSet_isFixedPt {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (syncForce u x) x) (hp : Function.Periodic u 1)
    (ho : ∀ x, u (-x) = -u x) : Function.IsFixedPt syncMap (toPoSet hu hu' hp ho) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  rw [syncMap_apply]
  exact congrFun (green_syncForce_eq hu hu' hp ho) x

/-! ### Existence and uniqueness -/

/-- The fixed point of the contraction, as a function. -/
def syncFixed : ℝ → ℝ := (ContractingWith.fixedPoint syncMap syncMap_contracting).1

theorem syncFixed_eq : green (syncForce syncFixed) = syncFixed := by
  have h := ContractingWith.fixedPoint_isFixedPt (f := syncMap) syncMap_contracting
  funext x
  exact (congrFun (congrArg (fun d : poSet => (d.1 : ℝ → ℝ)) h) x).symm.trans rfl |>.symm

theorem syncFixed_isSyncOrbit : IsSyncOrbit syncFixed := by
  set d := ContractingWith.fixedPoint syncMap syncMap_contracting
  have hc : Continuous syncFixed := d.1.continuous
  have hf := continuous_syncForce hc
  have hderiv : deriv syncFixed = greenD (syncForce syncFixed) := by
    funext x
    have := hasDerivAt_green hf x
    rw [syncFixed_eq] at this
    exact this.deriv
  have hderiv2 : deriv (deriv syncFixed) = syncForce syncFixed := by
    rw [hderiv]; funext x; exact (hasDerivAt_greenD hf x).deriv
  refine ⟨?_, d.2.1, d.2.2, fun φ => by rw [hderiv2]; rfl⟩
  have h2 : ContDiff ℝ (1 + 1) syncFixed := by
    refine contDiff_succ_iff_deriv.2 ⟨fun x => ?_, by simp, ?_⟩
    · have := hasDerivAt_green hf x
      rw [syncFixed_eq] at this
      exact this.differentiableAt
    · rw [contDiff_one_iff_deriv, hderiv2, hderiv]
      exact ⟨fun x => (hasDerivAt_greenD hf x).differentiableAt, hf⟩
  exact h2

theorem exists_isSyncOrbit : ∃ ψ, IsSyncOrbit ψ := ⟨_, syncFixed_isSyncOrbit⟩

/-- Existence (LOCK-PO, Banach contraction). -/
theorem lunarSyncOrbit_spec : IsSyncOrbit lunarSyncOrbit := by
  simp only [lunarSyncOrbit, exists_isSyncOrbit, ↓reduceDIte]
  exact Classical.choose_spec exists_isSyncOrbit

/-- Every odd one-periodic synchronous orbit is the fixed point of `syncMap`. -/
theorem IsSyncOrbit.eq_syncFixed {ψ : ℝ → ℝ} (h : IsSyncOrbit ψ) : ψ = syncFixed := by
  have hfix := toPoSet_isFixedPt h.hasDerivAt h.hasDerivAt_deriv h.2.1 h.2.2.1
  have := syncMap_contracting.fixedPoint_unique hfix
  exact congrArg (fun d : poSet => (d.1 : ℝ → ℝ)) this

/-- Global uniqueness: every odd one-periodic synchronous orbit is ψ*. -/
theorem lunarSyncOrbit_unique (ψ : ℝ → ℝ) (h : IsSyncOrbit ψ) : ψ = lunarSyncOrbit :=
  h.eq_syncFixed.trans lunarSyncOrbit_spec.eq_syncFixed.symm

/-! ### Location -/

theorem soLip_le_rat : soLip ≤ 3377 / 100000 := by
  have hS : ∑ m ∈ soModes, |soA m| ≤ 61974 / 100000 := by
    simp only [soModes, soA, soEcc]
    norm_num [Finset.sum_Icc_succ_top, soCoeffPoly, abs_of_pos, abs_of_neg]
  have hε := soEps_pos
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  unfold soLip
  calc 16 * π ^ 2 * soEps * ∑ m ∈ soModes, |soA m| ≤ 16 * π ^ 2 * soEps * (61974 / 100000) := by
        gcongr
    _ ≤ 3377 / 100000 := by unfold soEps; nlinarith

theorem soEta_le_rat : soEta ≤ 5355 / 10000000 := by
  have he : soModes.erase 2 = {1, 3, 4, 5, 6, 7} := by decide
  have hS : ∑ m ∈ soModes.erase 2, |soA m| ≤ 12350 / 100000 := by
    rw [he]
    simp only [soA, soEcc]
    norm_num [soCoeffPoly, abs_of_pos, abs_of_neg]
  have hε := soEps_pos
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  unfold soEta
  calc 4 * π * soEps * ∑ m ∈ soModes.erase 2, |soA m| ≤ 4 * π * soEps * (12350 / 100000) := by
        gcongr
    _ ≤ 5355 / 10000000 := by unfold soEps; nlinarith

theorem soForceBound_le_rat : soForceBound ≤ 27 / 10000 := by
  have hS : ∑ m ∈ soModes, |soA m| ≤ 61974 / 100000 := by
    simp only [soModes, soA, soEcc]
    norm_num [Finset.sum_Icc_succ_top, soCoeffPoly, abs_of_pos, abs_of_neg]
  have hε := soEps_pos
  have hπ := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  unfold soForceBound
  calc 4 * π * soEps * ∑ m ∈ soModes, |soA m| ≤ 4 * π * soEps * (61974 / 100000) := by gcongr
    _ ≤ 27 / 10000 := by unfold soEps; nlinarith

/-- The location bounds for any odd one-periodic solution of `u'' = syncForce u`. -/
theorem abs_le_of_syncForce_rat {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (syncForce u x) x) (hp : Function.Periodic u 1)
    (ho : ∀ x, u (-x) = -u x) (x : ℝ) :
    |u x| ≤ 17 / 1000000 ∧ |u' x| ≤ 27 / 200000 := by
  have hL := soLip_le_rat
  have hL0 := soLip_nonneg
  have hη := soEta_le_rat
  have hF := soForceBound_le_rat
  have hz := half_int_zero hp ho
  -- crude bound, then one sharpening step
  have h0 : ∀ y, |u y| ≤ 27 / 320000 := fun y =>
    (abs_le_of_syncForce hu hu' hp ho y).trans (by linarith)
  have hf1 : ∀ y, |syncForce u y| ≤ 5355 / 10000000 + 3377 / 100000 * (27 / 320000) := fun y =>
    (syncForce_abs_le_diag u y).trans (add_le_add hη
      (mul_le_mul hL (h0 y) (abs_nonneg _) (by norm_num)))
  have h1 : ∀ y, |u y| ≤ 17 / 1000000 := fun y =>
    (dirichlet_bound hu hu' hf1 hz y).1.trans (by norm_num)
  have hf2 : ∀ y, |syncForce u y| ≤ 5355 / 10000000 + 3377 / 100000 * (17 / 1000000) := fun y =>
    (syncForce_abs_le_diag u y).trans (add_le_add hη
      (mul_le_mul hL (h1 y) (abs_nonneg _) (by norm_num)))
  exact ⟨h1 x, (dirichlet_bound hu hu' hf2 hz x).2.trans (by norm_num)⟩

/-- Location of ψ* (forced libration ≈ 15.5″), from the rational majorants of design §1.4. -/
theorem lunarSyncOrbit_bound (φ : ℝ) :
    |lunarSyncOrbit φ| ≤ 17 / 1000000 ∧ |deriv lunarSyncOrbit φ| ≤ 27 / 200000 :=
  have h := lunarSyncOrbit_spec
  abs_le_of_syncForce_rat h.hasDerivAt h.hasDerivAt_deriv h.2.1 h.2.2.1 φ

end KAM.SpinOrbit.Lock

end
