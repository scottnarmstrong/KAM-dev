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

/-! ### Global existence and uniqueness -/

/-- Global existence and uniqueness of the solution of `soField` through any point: the force
is bounded, so solutions stay in a ball on every bounded time interval (`soSolution_norm_le`),
and `gen_confinement` makes the maximal interval infinite. -/
theorem so_global_exists_unique (x₀ : ℝ × ℝ × ℝ) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, z 0 = x₀ ∧ (∀ t, HasDerivAt z (soField (z t)) t) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, y 0 = x₀ → (∀ t, HasDerivAt y (soField (y t)) t) → y = z := by
  have hW : IsOpen (univ : Set (ℝ × ℝ × ℝ)) := isOpen_univ
  have hF : ContDiffOn ℝ 1 soField univ := soField_contDiff.contDiffOn
  obtain ⟨⟨Tm, Tp, z, hz⟩, huniq⟩ := KAM.ODE.gen_maximal hW hF (x₀ := x₀) (mem_univ _)
  have hconf : ∀ τ : ℝ, 0 < τ → (Tm : EReal) < ((-τ : ℝ) : EReal) ∧ ((τ : ℝ) : EReal) < Tp := by
    intro τ hτ
    set R := soRadius ‖x₀‖ τ
    obtain ⟨δ, M, L, hU, -, -⟩ := KAM.ODE.gen_uniform_compact hW hF
      (isCompact_closedBall (0 : ℝ × ℝ × ℝ) R) (subset_univ _)
    obtain ⟨Tm', Tp', z', hz', hTm, hTp, -⟩ := KAM.ODE.gen_confinement hW hF (mem_univ x₀) hτ hU
      (fun J y _ hJ h0 hy0 hy t ht htτ => by
        rw [mem_closedBall_zero_iff]
        have := soSolution_norm_le hJ h0 hy ht htτ
        rwa [hy0] at this)
    obtain ⟨h1, h2, -⟩ := huniq _ _ _ _ _ _ hz hz'
    exact ⟨h1 ▸ hTm, h2 ▸ hTp⟩
  have hTp : Tp = ⊤ := (EReal.eq_top_iff_forall_lt Tp).2 fun r =>
    lt_of_lt_of_le (by exact_mod_cast (show r < max r 0 + 1 by linarith [le_max_left r 0]))
      (hconf (max r 0 + 1) (by linarith [le_max_right r 0])).2.le
  have hTm : Tm = ⊥ := (EReal.eq_bot_iff_forall_lt Tm).2 fun r =>
    lt_of_le_of_lt (hconf (max (-r) 0 + 1) (by linarith [le_max_right (-r) 0])).1.le
      (by exact_mod_cast (show -(max (-r) 0 + 1) < r by linarith [le_max_left (-r) 0]))
  subst hTp hTm
  have hsol := hz.isSolution
  rw [KAM.ODE.eIoo_bot_top] at hsol
  refine ⟨z, hz.init, fun t => (hsol t (mem_univ t)).2, fun y hy0 hy => ?_⟩
  have := KAM.ODE.gen_uniqueness hW hF ordConnected_univ (mem_univ 0) (y₁ := y) (y₂ := z)
    (KAM.ODE.isSolutionIn_univ_iff.2 fun t _ => hy t |> fun h => h)
    hsol (by rw [hy0, hz.init])
  exact funext fun t => this (mem_univ t)

/-! ### Confinement between two barriers -/

/-- Two barrier graphs confine, in both time directions, every solution that starts strictly
between them, and that solution is global and unique. -/
theorem so_confinement {lo₁ hi₁ lo₂ hi₂ : ℝ} (B₁ : SoBarrier lo₁ hi₁) (B₂ : SoBarrier lo₂ hi₂)
    (x₀ : ℝ × ℝ × ℝ) (h₁ : B₁.P x₀.1 x₀.2.2 < x₀.2.1) (h₂ : x₀.2.1 < B₂.P x₀.1 x₀.2.2) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = x₀ ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, B₁.P (z t).1 (z t).2.2 < (z t).2.1 ∧ (z t).2.1 < B₂.P (z t).1 (z t).2.2) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = x₀ ∧ ∀ t, HasDerivAt y (soField (y t)) t) → y = z := by
  obtain ⟨z, hz0, hzd, huniq⟩ := so_global_exists_unique x₀
  refine ⟨z, ⟨hz0, hzd⟩, ?_, fun y hy => huniq y hy.1 hy.2⟩
  have hc₁ : Continuous fun x : ℝ × ℝ × ℝ => B₁.P x.1 x.2.2 :=
    B₁.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hc₂ : Continuous fun x : ℝ × ℝ × ℝ => B₂.P x.1 x.2.2 :=
    B₂.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hp : Continuous fun x : ℝ × ℝ × ℝ => x.2.1 := continuous_fst.comp continuous_snd
  set V : Set (ℝ × ℝ × ℝ) := {x | B₁.P x.1 x.2.2 < x.2.1 ∧ x.2.1 < B₂.P x.1 x.2.2} with hV
  have hVo : IsOpen V := (isOpen_lt hc₁ hp).inter (isOpen_lt hp hc₂)
  have hcl : closure V ⊆ {x | B₁.P x.1 x.2.2 ≤ x.2.1 ∧ x.2.1 ≤ B₂.P x.1 x.2.2} :=
    closure_minimal (fun x hx => ⟨hx.1.le, hx.2.le⟩)
      ((isClosed_le hc₁ hp).inter (isClosed_le hp hc₂))
  have hsol : KAM.ODE.IsSolutionIn soField univ univ z := KAM.ODE.isSolutionIn_univ_iff.2
    fun t _ => hzd t
  have hS := KAM.ODE.isInvariantSet_union B₁.invariant B₂.invariant
  have key := KAM.ODE.gen_barrier (F := soField) (W := univ) ordConnected_univ (mem_univ (0 : ℝ))
    hsol hVo (by rw [hz0]; exact ⟨h₁, h₂⟩) (G := univ) (subset_univ _)
    (S := {x | x.2.1 = B₁.P x.1 x.2.2} ∪ {x | x.2.1 = B₂.P x.1 x.2.2}) hS
    (fun x hx => by
      have hxc := hcl hx.1.1
      have hxV : x ∉ V := fun h => hx.1.2 (by rwa [hVo.interior_eq])
      simp only [hV, mem_ofPred_eq, not_and_or, not_lt] at hxV
      rcases hxV with h | h
      · exact Or.inl (le_antisymm h hxc.1)
      · exact Or.inr (le_antisymm hxc.2 h))
    (by
      rw [hz0]
      simp only [mem_union, mem_ofPred_eq, not_or]
      exact ⟨h₁.ne', h₂.ne⟩)
  exact fun t => key t (mem_univ t)

end KAM.SpinOrbit

end
