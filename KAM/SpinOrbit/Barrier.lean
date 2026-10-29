/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Model
public import KAM.ODE.Exit
public import KAM.ODE.Continuation
public import KAM.ODE.Maximal

/-!
# Two barriers confine, globally and uniquely (track SO, package SO-CONF)

Unfrozen helper code (design §6, proposal §7.3).

* `SoBarrier lo hi`: an invariant continuous doubly periodic graph `p = P(q, φ)` of the flow of
  `soField` with values in `[lo, hi]`.
* `soField_contDiff`, `soVq_abs_le`: `soField` is `C¹` and its force is bounded (the field is
  globally Lipschitz and of linear growth in `p`).
* `soSolution_norm_le`: an a priori bound on `[-T, T]` for every solution.
* `so_global_exists_unique`: global existence and uniqueness of the solution through any point.
* `so_confinement`: a solution starting strictly between two barrier graphs stays strictly between
  them for all real times (both directions), and is the unique global solution.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped NNReal

namespace KAM.SpinOrbit

/-- An invariant barrier graph `p = P(q, φ)` of the physical flow with values in `[lo, hi]`. -/
structure SoBarrier (lo hi : ℝ) where
  P : ℝ → ℝ → ℝ
  continuous : Continuous fun x : ℝ × ℝ => P x.1 x.2
  periodic_q : ∀ q φ, P (q + 1) φ = P q φ
  periodic_φ : ∀ q φ, P q (φ + 1) = P q φ
  invariant : KAM.ODE.IsInvariantSet soField Set.univ {x | x.2.1 = P x.1 x.2.2}
  lower : ∀ q φ, lo ≤ P q φ
  upper : ∀ q φ, P q φ ≤ hi

/-! ### The field: smoothness and a force bound -/

theorem soVq_contDiff : ContDiff ℝ 1 fun x : ℝ × ℝ × ℝ => soVq x.1 x.2.2 := by
  unfold soVq
  fun_prop

theorem soField_contDiff : ContDiff ℝ 1 soField := by
  have h : soField = fun x => (x.2.1, -soVq x.1 x.2.2, 1) := funext soField_eq
  rw [h]
  have := soVq_contDiff
  fun_prop

/-- The bound `A = 4π ε Σ |A_m|` on the force. -/
def soForceBound : ℝ := 4 * π * soEps * ∑ m ∈ soModes, |soA m|

theorem soForceBound_nonneg : 0 ≤ soForceBound := by
  unfold soForceBound
  have := soEps_pos
  positivity

theorem soVq_abs_le (q φ : ℝ) : |soVq q φ| ≤ soForceBound := by
  unfold soVq soForceBound
  have hε := soEps_pos
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * soEps)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

/-! ### A priori bound -/

private theorem abs_sub_le_of_hasDerivAt {f g : ℝ → ℝ} {c t : ℝ}
    (hf : ∀ s ∈ uIcc 0 t, HasDerivAt f (g s) s) (hg : ∀ s ∈ uIcc 0 t, |g s| ≤ c) :
    |f t - f 0| ≤ c * |t| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := g) (s := uIcc 0 t)
    (fun s hs => (hf s hs).hasDerivWithinAt) (fun s hs => by simpa using hg s hs)
    (convex_uIcc 0 t) (left_mem_uIcc) (right_mem_uIcc)
  simpa using this

private theorem abs_le_of_mem_uIcc {s t : ℝ} (hs : s ∈ uIcc 0 t) : |s| ≤ |t| := by
  rw [mem_uIcc] at hs
  rw [abs_le]
  constructor <;> rcases hs with h | h <;> linarith [neg_abs_le t, le_abs_self t]

private theorem hasDerivAt_fst' {α β : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [NormedAddCommGroup β] [NormedSpace ℝ β] {f : ℝ → α × β} {f' : α × β} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun r => (f r).1) f'.1 t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (E := α) (F := β) (p := f t)).comp_hasDerivAt t h

private theorem hasDerivAt_snd' {α β : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [NormedAddCommGroup β] [NormedSpace ℝ β] {f : ℝ → α × β} {f' : α × β} {t : ℝ}
    (h : HasDerivAt f f' t) : HasDerivAt (fun r => (f r).2) f'.2 t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (E := α) (F := β) (p := f t)).comp_hasDerivAt t h

/-- The radius of the a priori ball on `[-T, T]` for data of norm at most `N`. -/
def soRadius (N T : ℝ) : ℝ := N + T + soForceBound * T + (N + soForceBound * T) * T

theorem soSolution_norm_le {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → ℝ × ℝ × ℝ} (hy : KAM.ODE.IsSolutionIn soField univ J y) {t T : ℝ} (ht : t ∈ J)
    (htT : |t| ≤ T) : ‖y t‖ ≤ soRadius ‖y 0‖ T := by
  have hsub : uIcc 0 t ⊆ J := hJ.uIcc_subset h0 ht
  have hT : 0 ≤ T := (abs_nonneg t).trans htT
  have hA := soForceBound_nonneg
  have hN := norm_nonneg (y 0)
  set N := ‖y 0‖ with hNdef
  have hder : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).2) (soField (y s)).2 s := fun s hs =>
    hasDerivAt_snd' (hy s (hsub hs)).2
  have hd2 : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).2.1) (-soVq (y s).1 (y s).2.2) s :=
    fun s hs => by
      convert hasDerivAt_fst' (hder s hs) using 1
      simp [soField_eq]
  have hd3 : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).2.2) 1 s := fun s hs => by
    convert hasDerivAt_snd' (hder s hs) using 1
    simp [soField_eq]
  have hd1 : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).1) (y s).2.1 s := fun s hs => by
    convert hasDerivAt_fst' (hy s (hsub hs)).2 using 1
    simp [soField_eq]
  have hq0 : |(y 0).1| ≤ N := by simpa using norm_fst_le (y 0)
  have hp0 : |(y 0).2.1| ≤ N := by
    simpa using (norm_fst_le (y 0).2).trans (norm_snd_le (y 0))
  have hf0 : |(y 0).2.2| ≤ N := by
    simpa using (norm_snd_le (y 0).2).trans (norm_snd_le (y 0))
  have hsT : ∀ s ∈ uIcc 0 t, |s| ≤ T := fun s hs => (abs_le_of_mem_uIcc hs).trans htT
  have hφ : |(y t).2.2| ≤ N + T := by
    have h1 := abs_sub_le_of_hasDerivAt (g := fun _ => 1) (c := 1) hd3 (fun _ _ => by simp)
    have h2 := abs_sub_abs_le_abs_sub (y t).2.2 (y 0).2.2
    nlinarith
  have hp : ∀ s ∈ uIcc 0 t, |(y s).2.1| ≤ N + soForceBound * T := fun s hs => by
    have hds : ∀ r ∈ uIcc 0 s, HasDerivAt (fun r => (y r).2.1) (-soVq (y r).1 (y r).2.2) r :=
      fun r hr => hd2 r (uIcc_subset_uIcc left_mem_uIcc hs hr)
    have h1 := abs_sub_le_of_hasDerivAt hds (fun r _ => by simpa using soVq_abs_le _ _)
    have h2 := abs_sub_abs_le_abs_sub (y s).2.1 (y 0).2.1
    have h3 := mul_le_mul_of_nonneg_left (hsT s hs) hA
    nlinarith
  have hq : |(y t).1| ≤ N + (N + soForceBound * T) * T := by
    have h1 := abs_sub_le_of_hasDerivAt hd1 (fun s hs => hp s hs)
    have h2 := abs_sub_abs_le_abs_sub (y t).1 (y 0).1
    have h3 := mul_le_mul_of_nonneg_left htT (by positivity : 0 ≤ N + soForceBound * T)
    nlinarith
  have hp' := hp t right_mem_uIcc
  have hpt : 0 ≤ soForceBound * T := by positivity
  have hnn : 0 ≤ (N + soForceBound * T) * T := by positivity
  unfold soRadius
  rw [Prod.norm_def, Prod.norm_def]
  simp only [Real.norm_eq_abs, max_le_iff]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end KAM.SpinOrbit

end
