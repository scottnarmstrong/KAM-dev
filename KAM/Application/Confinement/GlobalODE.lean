/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Confinement: global solutions of bounded Lipschitz fields, and the box clamp

* `exists_global_solution`: an autonomous field `W` on a Banach space that is globally Lipschitz
  and bounded has a solution through every point, defined for all times. Mathlib's
  Picard–Lindelöf theorem gives a solution on every `[-(n+1), n+1]`; the solutions agree on their
  common intervals (`ODE_solution_unique_of_mem_Icc`) and glue.
* `clampBox α β`: the coordinatewise clamp of `Fin m → ℝ` to the box `[α, β]`; it is 1-Lipschitz
  for the sup norm, maps into the box, and is the identity on it. Composing a field with it turns a
  field that is Lipschitz and bounded on `ℝⁿ × [α, β]` into a globally Lipschitz bounded field.

Used for vector fields known to be well behaved only on a region (e.g. a Hamiltonian field in an
action–angle chart, on an action box): solve the clamped field globally, then show that the
solution never leaves the region (`KAM.Application.Confinement.twoTorus_confinement`).
-/

public section

open Set Filter
open scoped NNReal Topology

namespace KAM.Application.Confinement

section ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Picard–Lindelöf on `[-T, T]` for a bounded globally Lipschitz autonomous field. -/
theorem exists_solution_Icc {W : E → E} {K : ℝ≥0} (hW : LipschitzWith K W) {C : ℝ}
    (hC : ∀ x, ‖W x‖ ≤ C) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Icc (-T) T, HasDerivWithinAt α (W (α t)) (Icc (-T) T) t := by
  have ht0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT⟩
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  let a : ℝ≥0 := ⟨max C 0 * T, mul_nonneg (le_max_right _ _) hT⟩
  have hpl : IsPicardLindelof (fun _ => W) (tmin := -T) (tmax := T) ⟨0, ht0⟩ x₀ a 0 L K :=
    IsPicardLindelof.of_time_independent (fun x _ => (hC x).trans (le_max_left _ _))
      hW.lipschitzOnWith (by simp [L, a]; exact le_rfl)
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **Global existence** for a bounded globally Lipschitz autonomous field. -/
theorem exists_global_solution {W : E → E} {K : ℝ≥0} (hW : LipschitzWith K W) {C : ℝ}
    (hC : ∀ x, ‖W x‖ ≤ C) (x₀ : E) :
    ∃ z : ℝ → E, z 0 = x₀ ∧ ∀ t, HasDerivAt z (W (z t)) t := by
  choose α hα0 hα using fun n : ℕ =>
    exists_solution_Icc hW hC x₀ (T := (n : ℝ) + 1) (by positivity)
  -- interior derivatives and continuity of each piece
  have hder : ∀ n : ℕ, ∀ t ∈ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
      HasDerivAt (α n) (W (α n t)) t := fun n t ht =>
    (hα n t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcont : ∀ n : ℕ, ContinuousOn (α n) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun n t ht => (hα n t ht).continuousWithinAt
  -- the pieces agree on common intervals
  have hagree : ∀ m n : ℕ, m ≤ n →
      EqOn (α m) (α n) (Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1)) := by
    intro m n hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hsub : Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
      Icc_subset_Icc (by linarith) (by linarith)
    have hsubo : Ioo (-((m : ℝ) + 1)) ((m : ℝ) + 1) ⊆ Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    exact ODE_solution_unique_of_mem_Icc (v := fun _ => W) (s := fun _ => univ) (K := K)
      (fun _ _ => hW.lipschitzOnWith) (t₀ := 0) ⟨by linarith, by linarith⟩
      (hcont m) (fun t ht => hder m t ht) (fun _ _ => trivial)
      ((hcont n).mono hsub) (fun t ht => hder n t (hsubo ht)) (fun _ _ => trivial)
      (by rw [hα0, hα0])
  refine ⟨fun t => α ⌈|t|⌉₊ t, by simp [hα0], fun t => ?_⟩
  set N : ℕ := ⌈|t|⌉₊ + 1 with hN
  have htN : |t| < (N : ℝ) := by
    have := Nat.le_ceil |t|
    push_cast [hN]
    linarith
  have hloc : (fun s => α ⌈|s|⌉₊ s) =ᶠ[𝓝 t] α N := by
    have hmem : Ioo (-(N : ℝ)) N ∈ 𝓝 t :=
      Ioo_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t])
    filter_upwards [hmem] with s hs
    have hsN : |s| ≤ (N : ℝ) := (abs_lt.mpr ⟨hs.1, hs.2⟩).le
    have hle : ⌈|s|⌉₊ ≤ N := Nat.ceil_le.mpr hsN
    apply hagree _ _ hle
    have := Nat.le_ceil |s|
    constructor <;> linarith [neg_abs_le s, le_abs_self s]
  have htN' : t ∈ Ioo (-((N : ℝ) + 1)) ((N : ℝ) + 1) :=
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have h := (hder N t htN').congr_of_eventuallyEq hloc
  have he : α ⌈|t|⌉₊ t = α N t := hloc.eq_of_nhds
  show HasDerivAt _ (W (α ⌈|t|⌉₊ t)) t
  rw [he]
  exact h

end ODE

section Clamp

variable {m : ℕ}

/-- The coordinatewise clamp of `a` to the box `[α, β]`. -/
@[expose] def clampBox (α β a : Fin m → ℝ) : Fin m → ℝ := fun j => max (α j) (min (β j) (a j))

theorem clampBox_mem {α β : Fin m → ℝ} (hαβ : α ≤ β) (a : Fin m → ℝ) :
    clampBox α β a ∈ Icc α β :=
  ⟨fun _ => le_max_left _ _, fun j => max_le (hαβ j) (min_le_left _ _)⟩

theorem clampBox_of_mem {α β a : Fin m → ℝ} (ha : a ∈ Icc α β) : clampBox α β a = a := by
  funext j
  simp [clampBox, min_eq_right (ha.2 j), max_eq_right (ha.1 j)]

theorem lipschitzWith_clampBox (α β : Fin m → ℝ) : LipschitzWith 1 (clampBox α β) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro j
  have h1 : dist (max (α j) (min (β j) (a j))) (max (α j) (min (β j) (b j))) ≤
      dist (min (β j) (a j)) (min (β j) (b j)) := by
    rw [Real.dist_eq, Real.dist_eq, max_comm (α j), max_comm (α j)]
    exact abs_max_sub_max_le_abs _ _ _
  have h2 : dist (min (β j) (a j)) (min (β j) (b j)) ≤ dist (a j) (b j) := by
    rw [Real.dist_eq, Real.dist_eq]
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp
  exact h1.trans (h2.trans (dist_le_pi_dist a b j))

end Clamp

end KAM.Application.Confinement
