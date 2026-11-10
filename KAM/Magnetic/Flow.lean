/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Magnetic.FieldBasic
public import KAM.ODE.Exit
public import KAM.ODE.Continuation
public import KAM.ODE.Maximal

/-!
# Field lines of `magField`: global existence, invariant graphs, side preservation

Unfrozen helper code (the flow conjunct of `KAM.Magnetic.magnetic_barrier`).

* `MagGraphInvariant P`: the graph `p = P(q, φ)` is invariant under the field lines of `magField`
  (the form of `SoBarrier.invariant`).
* `magSolution_norm_le`: an a priori bound on `[-T, T]` for every field line. The field is not
  globally Lipschitz (`h'` is cubic), but the force is bounded, so `p` grows at most linearly and
  then `q' = h'(p)` is bounded on `[-T, T]`.
* `magField_global`: global existence, and agreement of every local field line with the global one.
* `magGraphInvariant_of_orbits`: invariance from global field lines inside the graph through each
  graph point (uniqueness after translating time).
* `magnetic_flow_of_invariant`: the flow conjunct of `magnetic_barrier` for a continuous invariant
  graph (side preservation by the intermediate value theorem).
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped NNReal

namespace KAM.Magnetic

/-- The graph `p = P(q, φ)` is invariant under the field lines of `magField` (the form of
`SoBarrier.invariant`). -/
def MagGraphInvariant (P : ℝ → ℝ → ℝ) : Prop :=
  ∀ (J : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), J.OrdConnected →
    (∀ t ∈ J, HasDerivAt y (magField (y t)) t) →
    ∀ t₁ ∈ J, (y t₁).2.1 = P (y t₁).1 (y t₁).2.2 → ∀ t ∈ J, (y t).2.1 = P (y t).1 (y t).2.2

/-! ### A priori bound -/

/-- A bound for `|h'(p)|` on `|p| ≤ R`. -/
def magH0'Bound (R : ℝ) : ℝ := 1 + 3 / 2 * R + R ^ 2 + R ^ 3 / 4

theorem magH0'_abs_le {p R : ℝ} (h : |p| ≤ R) : |magH0' p| ≤ magH0'Bound R := by
  have hR : 0 ≤ R := (abs_nonneg p).trans h
  have h2 : |p ^ 2| ≤ R ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h3 : |p ^ 3| ≤ R ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 3
  have e : magH0' p = 1 - 3 / 2 * p + p ^ 2 - p ^ 3 / 4 := rfl
  rw [e, magH0'Bound]
  have t1 := abs_sub (1 - 3 / 2 * p + p ^ 2) (p ^ 3 / 4)
  have t2 := abs_add_le (1 - 3 / 2 * p) (p ^ 2)
  have t3 := abs_sub (1 : ℝ) (3 / 2 * p)
  have e1 : |(1 : ℝ)| = 1 := abs_one
  have e2 : |3 / 2 * p| = 3 / 2 * |p| := by rw [abs_mul]; norm_num
  have e3 : |p ^ 3 / 4| = |p ^ 3| / 4 := by rw [abs_div]; norm_num
  rw [e1, e2] at t3
  rw [e3] at t1
  linarith

theorem magH0'Bound_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ magH0'Bound R := by
  unfold magH0'Bound; positivity

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
def magRadius (N T : ℝ) : ℝ :=
  (N + T) + (N + magForceBound * T) + (N + magH0'Bound (N + magForceBound * T) * T)

theorem magSolution_norm_le {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    {y : ℝ → ℝ × ℝ × ℝ} (hy : KAM.ODE.IsSolutionIn magField univ J y) {t T : ℝ} (ht : t ∈ J)
    (htT : |t| ≤ T) : ‖y t‖ ≤ magRadius ‖y 0‖ T := by
  have hsub : uIcc 0 t ⊆ J := hJ.uIcc_subset h0 ht
  have hT : 0 ≤ T := (abs_nonneg t).trans htT
  have hA := magForceBound_nonneg
  have hN := norm_nonneg (y 0)
  set N := ‖y 0‖ with hNdef
  have hder : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).2) (magField (y s)).2 s := fun s hs =>
    hasDerivAt_snd' (hy s (hsub hs)).2
  have hd2 : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).2.1) (-magVq (y s).1 (y s).2.2) s :=
    fun s hs => by
      convert hasDerivAt_fst' (hder s hs) using 1
      simp [magField_eq]
  have hd3 : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).2.2) 1 s := fun s hs => by
    convert hasDerivAt_snd' (hder s hs) using 1
    simp [magField_eq]
  have hd1 : ∀ s ∈ uIcc 0 t, HasDerivAt (fun r => (y r).1) (magH0' (y s).2.1) s := fun s hs => by
    convert hasDerivAt_fst' (hy s (hsub hs)).2 using 1
    simp [magField_eq]
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
  have hp : ∀ s ∈ uIcc 0 t, |(y s).2.1| ≤ N + magForceBound * T := fun s hs => by
    have hds : ∀ r ∈ uIcc 0 s, HasDerivAt (fun r => (y r).2.1) (-magVq (y r).1 (y r).2.2) r :=
      fun r hr => hd2 r (uIcc_subset_uIcc left_mem_uIcc hs hr)
    have h1 := abs_sub_le_of_hasDerivAt hds (fun r _ => by simpa using magVq_abs_le _ _)
    have h2 := abs_sub_abs_le_abs_sub (y s).2.1 (y 0).2.1
    have h3 := mul_le_mul_of_nonneg_left (hsT s hs) hA
    nlinarith
  have hPb : 0 ≤ N + magForceBound * T := by positivity
  have hHb := magH0'Bound_nonneg hPb
  have hq : |(y t).1| ≤ N + magH0'Bound (N + magForceBound * T) * T := by
    have h1 := abs_sub_le_of_hasDerivAt hd1 (fun s hs => magH0'_abs_le (hp s hs))
    have h2 := abs_sub_abs_le_abs_sub (y t).1 (y 0).1
    have h3 := mul_le_mul_of_nonneg_left htT hHb
    nlinarith
  have hp' := hp t right_mem_uIcc
  have hnn : 0 ≤ magH0'Bound (N + magForceBound * T) * T := by positivity
  unfold magRadius
  rw [Prod.norm_def, Prod.norm_def]
  simp only [Real.norm_eq_abs, max_le_iff]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ### Global existence and agreement -/

theorem magField_contDiffOn : ContDiffOn ℝ 1 magField univ := magField_contDiff.contDiffOn

/-- Global existence, and agreement of every local field line with the global one. -/
theorem magField_global (x₀ : ℝ × ℝ × ℝ) : ∃ z : ℝ → ℝ × ℝ × ℝ,
    z 0 = x₀ ∧ (∀ t, HasDerivAt z (magField (z t)) t) ∧
    ∀ (I : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = x₀ →
      (∀ t ∈ I, HasDerivAt y (magField (y t)) t) → ∀ t ∈ I, y t = z t := by
  have hW : IsOpen (univ : Set (ℝ × ℝ × ℝ)) := isOpen_univ
  have hF := magField_contDiffOn
  obtain ⟨⟨Tm, Tp, z, hz⟩, huniq⟩ := KAM.ODE.gen_maximal hW hF (x₀ := x₀) (mem_univ _)
  have hconf : ∀ τ : ℝ, 0 < τ → (Tm : EReal) < ((-τ : ℝ) : EReal) ∧ ((τ : ℝ) : EReal) < Tp := by
    intro τ hτ
    set R := magRadius ‖x₀‖ τ
    obtain ⟨δ, M, L, hU, -, -⟩ := KAM.ODE.gen_uniform_compact hW hF
      (isCompact_closedBall (0 : ℝ × ℝ × ℝ) R) (subset_univ _)
    obtain ⟨Tm', Tp', z', hz', hTm, hTp, -⟩ := KAM.ODE.gen_confinement hW hF (mem_univ x₀) hτ hU
      (fun J y _ hJ h0 hy0 hy t ht htτ => by
        rw [mem_closedBall_zero_iff]
        have := magSolution_norm_le hJ h0 hy ht htτ
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
  refine ⟨z, hz.init, fun t => (hsol t (mem_univ t)).2, fun I y hI h0 hy0 hy => ?_⟩
  exact KAM.ODE.gen_uniqueness hW hF hI h0 (y₁ := y) (y₂ := z)
    (KAM.ODE.isSolutionIn_univ_iff.2 hy) (hsol.mono (subset_univ I)) (by rw [hy0, hz.init])

/-! ### Invariance from orbits -/

/-- Invariance of a graph from global field lines inside it through each of its points. -/
theorem magGraphInvariant_of_orbits {P : ℝ → ℝ → ℝ}
    (horb : ∀ q φ, ∃ z : ℝ → ℝ × ℝ × ℝ, z 0 = (q, P q φ, φ) ∧
      (∀ t, HasDerivAt z (magField (z t)) t) ∧ ∀ t, (z t).2.1 = P (z t).1 (z t).2.2) :
    MagGraphInvariant P := by
  intro J y hJ hy t₁ ht₁ hon t ht
  obtain ⟨z, hz0, hzd, hzP⟩ := horb (y t₁).1 (y t₁).2.2
  set w : ℝ → ℝ × ℝ × ℝ := fun s => z (s - t₁) with hw
  have hwd : ∀ s, HasDerivAt w (magField (w s)) s := fun s => by
    have := (hzd (s - t₁)).comp_sub_const s t₁
    exact this
  have hwt : y t₁ = w t₁ := by
    simp only [hw, sub_self, hz0, ← hon]
  have := KAM.ODE.gen_uniqueness isOpen_univ magField_contDiffOn hJ ht₁ (y₁ := y) (y₂ := w)
    (KAM.ODE.isSolutionIn_univ_iff.2 hy)
    (KAM.ODE.isSolutionIn_univ_iff.2 fun s _ => hwd s) hwt ht
  rw [this]
  exact hzP _

/-! ### Side preservation -/

/-- The flow conjunct of `magnetic_barrier`, for any continuous invariant graph. -/
theorem magnetic_flow_of_invariant {P : ℝ → ℝ → ℝ}
    (hP : Continuous fun x : ℝ × ℝ => P x.1 x.2) (hinv : MagGraphInvariant P) :
    ∀ x₀ : ℝ × ℝ × ℝ, ∃ z : ℝ → ℝ × ℝ × ℝ,
      z 0 = x₀ ∧ (∀ t, HasDerivAt z (magField (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → ℝ × ℝ × ℝ), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = x₀ →
        (∀ t ∈ I, HasDerivAt y (magField (y t)) t) → ∀ t ∈ I, y t = z t) ∧
      ∀ t : ℝ,
        (x₀.2.1 < P x₀.1 x₀.2.2 → (z t).2.1 < P (z t).1 (z t).2.2) ∧
        (x₀.2.1 = P x₀.1 x₀.2.2 → (z t).2.1 = P (z t).1 (z t).2.2) ∧
        (P x₀.1 x₀.2.2 < x₀.2.1 → P (z t).1 (z t).2.2 < (z t).2.1) := by
  intro x₀
  obtain ⟨z, hz0, hzd, hzu⟩ := magField_global x₀
  refine ⟨z, hz0, hzd, hzu, ?_⟩
  set f : ℝ → ℝ := fun t => (z t).2.1 - P (z t).1 (z t).2.2 with hf
  have hzc : Continuous z := continuous_iff_continuousAt.2 fun t => (hzd t).continuousAt
  have hfc : Continuous f :=
    (continuous_fst.comp (continuous_snd.comp hzc)).sub
      (hP.comp ((continuous_fst.comp hzc).prodMk
        (continuous_snd.comp (continuous_snd.comp hzc))))
  have hinvz : ∀ t₁ t, f t₁ = 0 → f t = 0 := fun t₁ t h => by
    have := hinv univ z ordConnected_univ (fun s _ => hzd s) t₁ (mem_univ _)
      (sub_eq_zero.1 h) t (mem_univ _)
    simp only [hf]
    rw [this, sub_self]
  -- if `f` vanishes nowhere, its sign at `t` is its sign at `0`
  have hside : ∀ t, f 0 ≠ 0 → (0 < f 0 ↔ 0 < f t) := by
    intro t h0
    have hne : ∀ s, f s ≠ 0 := fun s hs => h0 (hinvz s 0 hs)
    have hivt := intermediate_value_uIcc (a := (0 : ℝ)) (b := t) hfc.continuousOn
    constructor
    · intro hpos
      by_contra hneg
      push Not at hneg
      obtain ⟨s, -, hs⟩ := hivt (show (0 : ℝ) ∈ uIcc (f 0) (f t) from
        mem_uIcc.2 (Or.inr ⟨hneg, hpos.le⟩))
      exact hne s hs
    · intro hpos
      by_contra hneg
      push Not at hneg
      obtain ⟨s, -, hs⟩ := hivt (show (0 : ℝ) ∈ uIcc (f 0) (f t) from
        mem_uIcc.2 (Or.inl ⟨hneg, hpos.le⟩))
      exact hne s hs
  have hf0 : f 0 = x₀.2.1 - P x₀.1 x₀.2.2 := by simp [hf, hz0]
  intro t
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h0 : f 0 < 0 := by rw [hf0]; linarith
    have hft : ¬ 0 < f t := fun hpos => absurd ((hside t h0.ne).2 hpos) (not_lt.2 h0.le)
    have hft0 : f t ≠ 0 := fun h' => h0.ne (hinvz t 0 h')
    have : f t < 0 := lt_of_le_of_ne (not_lt.1 hft) hft0
    simp only [hf] at this
    linarith
  · have h0 : f 0 = 0 := by rw [hf0, h, sub_self]
    have := hinvz 0 t h0
    simp only [hf] at this
    linarith
  · have h0 : 0 < f 0 := by rw [hf0]; linarith
    have := (hside t h0.ne').1 h0
    simp only [hf] at this
    linarith

end KAM.Magnetic

end
