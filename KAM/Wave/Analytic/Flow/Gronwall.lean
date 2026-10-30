/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gronwall comparison for curves on `[-1, 1]`

Blueprint-W `bpW:w1:flow`, steps `stepW:w1:flowlip` and `stepW:w1:flowpar` (package W1-ANALYTIC).
This is source-faithful infrastructure used by several nodes; the dependency graph is still being
built.

Two curves `γ`, `η` on `[-1, 1]` solving `γ' = X γ`, `η' = Y η` inside a set `B` on which `Y` is
`L`-Lipschitz, with `‖X - Y‖ ≤ N` on `B` and `γ 0 = η 0`, satisfy
`‖γ t - η t‖ ≤ |t| e^{L|t|} N` (`KAM.Wave.norm_sub_le_of_solutions`). A solution of `γ' = X γ` with
`‖X‖ ≤ M` on its range moves at speed at most `M` (`KAM.Wave.norm_sub_le_of_deriv_bound`).
-/

@[expose] public section

open Set Metric Filter Topology

namespace KAM.Wave

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exp_sub_one_div_le (L t : ℝ) (hL : 0 < L) :
    (Real.exp (L * t) - 1) / L ≤ t * Real.exp (L * t) := by
  rw [div_le_iff₀ hL]
  have := Real.add_one_le_exp (-(L * t))
  have h2 : Real.exp (-(L * t)) * Real.exp (L * t) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (L * t)]

/-- Forward Grönwall comparison on `[0, 1]`. -/
theorem norm_sub_le_of_solutions_forward {X Y : F → F} {B : Set F} {L N : ℝ} (hL : 0 ≤ L)
    (hN : 0 ≤ N) (hY : ∀ x ∈ B, ∀ y ∈ B, ‖Y x - Y y‖ ≤ L * ‖x - y‖)
    {γ η : ℝ → F} (hγc : ContinuousOn γ (Icc 0 1))
    (hγd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt γ (X (γ t)) (Ici t) t)
    (hγB : ∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ B) (hηc : ContinuousOn η (Icc 0 1))
    (hηd : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt η (Y (η t)) (Ici t) t)
    (hηB : ∀ t ∈ Ico (0 : ℝ) 1, η t ∈ B) (hXY : ∀ z ∈ B, ‖X z - Y z‖ ≤ N)
    (h0 : γ 0 = η 0) : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - η t‖ ≤ t * Real.exp (L * t) * N := by
  have hLip : LipschitzOnWith L.toNNReal Y B := LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    simpa [dist_eq_norm, Real.coe_toNNReal _ hL] using hY x hx y hy
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => Y) (s := fun _ => B)
    (K := L.toNNReal) (εf := N) (εg := 0) (δ := 0) (a := 0) (b := 1) (f := γ) (g := η)
    (f' := fun t => X (γ t)) (g' := fun t => Y (η t)) (fun _ _ => hLip) hγc hγd
    (fun t ht => by simpa [dist_eq_norm] using hXY _ (hγB t ht)) hγB hηc hηd
    (fun t ht => by simp) hηB (by simp [h0])
  intro t ht
  have h1 := key t ht
  rw [dist_eq_norm, Real.coe_toNNReal _ hL] at h1
  refine h1.trans ?_
  rcases hL.eq_or_lt with rfl | hLpos
  · simp [gronwallBound_K0]
    nlinarith [ht.1]
  · rw [gronwallBound_of_K_ne_0 hLpos.ne']
    simp only [zero_mul, zero_add, add_zero, sub_zero]
    have := exp_sub_one_div_le L t hLpos
    calc N / L * (Real.exp (L * t) - 1) = N * ((Real.exp (L * t) - 1) / L) := by ring
      _ ≤ N * (t * Real.exp (L * t)) := mul_le_mul_of_nonneg_left this hN
      _ = t * Real.exp (L * t) * N := by ring


theorem continuousOn_of_hasDerivWithinAt_Icc {γ : ℝ → F} {d : ℝ → F}
    (h : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt γ (d t) (Icc (-1) 1) t) :
    ContinuousOn γ (Icc (-1) 1) := fun t ht => (h t ht).continuousWithinAt

/-- Grönwall comparison on `[-1, 1]` (blueprint `bpW:w1:flow`, `stepW:w1:flowpar`). -/
theorem norm_sub_le_of_solutions {X Y : F → F} {B : Set F} {L N : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N)
    (hY : ∀ x ∈ B, ∀ y ∈ B, ‖Y x - Y y‖ ≤ L * ‖x - y‖) {γ η : ℝ → F}
    (hγd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt γ (X (γ t)) (Icc (-1) 1) t)
    (hγB : ∀ t ∈ Icc (-1 : ℝ) 1, γ t ∈ B)
    (hηd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt η (Y (η t)) (Icc (-1) 1) t)
    (hηB : ∀ t ∈ Icc (-1 : ℝ) 1, η t ∈ B) (hXY : ∀ z ∈ B, ‖X z - Y z‖ ≤ N) (h0 : γ 0 = η 0) :
    ∀ t ∈ Icc (-1 : ℝ) 1, ‖γ t - η t‖ ≤ |t| * Real.exp (L * |t|) * N := by
  have hγc := continuousOn_of_hasDerivWithinAt_Icc hγd
  have hηc := continuousOn_of_hasDerivWithinAt_Icc hηd
  have hIcc : ∀ s ∈ Ico (0 : ℝ) 1, Icc (-1 : ℝ) 1 ∈ 𝓝[Ici s] s := fun s hs =>
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith [hs.1]) hs.2)
  have hfwd := norm_sub_le_of_solutions_forward hL hN hY (γ := γ) (η := η)
    (hγc.mono (Icc_subset_Icc (by norm_num) le_rfl))
    (fun s hs => (hγd s ⟨by linarith [hs.1], hs.2.le⟩).mono_of_mem_nhdsWithin (hIcc s hs))
    (fun s hs => hγB s ⟨by linarith [hs.1], hs.2.le⟩)
    (hηc.mono (Icc_subset_Icc (by norm_num) le_rfl))
    (fun s hs => (hηd s ⟨by linarith [hs.1], hs.2.le⟩).mono_of_mem_nhdsWithin (hIcc s hs))
    (fun s hs => hηB s ⟨by linarith [hs.1], hs.2.le⟩) hXY h0
  have hrefl := norm_sub_le_of_solutions_forward hL hN
    (X := fun z => -X z) (Y := fun z => -Y z) (B := B)
    (fun x hx y hy => by
      rw [show -Y x - -Y y = -(Y x - Y y) by abel, norm_neg]; exact hY x hx y hy)
    (γ := fun s => γ (-s)) (η := fun s => η (-s))
    ((hγc.comp continuousOn_neg (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)))
    (fun s hs => by
      have h1 : HasDerivAt γ (X (γ (-s))) (-s) :=
        (hγd (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).hasDerivAt
          (Icc_mem_nhds (by linarith [hs.2]) (by linarith [hs.1]))
      have := (h1.scomp s (hasDerivAt_neg s))
      simpa [neg_smul, Function.comp_def] using this.hasDerivWithinAt)
    (fun s hs => hγB _ ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    ((hηc.comp continuousOn_neg (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)))
    (fun s hs => by
      have h1 : HasDerivAt η (Y (η (-s))) (-s) :=
        (hηd (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).hasDerivAt
          (Icc_mem_nhds (by linarith [hs.2]) (by linarith [hs.1]))
      have := (h1.scomp s (hasDerivAt_neg s))
      simpa [neg_smul, Function.comp_def] using this.hasDerivWithinAt)
    (fun s hs => hηB _ ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    (fun z hz => by
      rw [show -X z - -Y z = -(X z - Y z) by abel, norm_neg]; exact hXY z hz) (by simpa using h0)
  intro t ht
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]; exact hfwd t ⟨h, ht.2⟩
  · rw [abs_of_nonpos h]
    simpa using hrefl (-t) ⟨by linarith, by linarith [ht.1]⟩

/-- A solution of `γ' = X γ` with `‖X‖ ≤ M` along `γ` moves with speed at most `M`. -/
theorem norm_sub_le_of_deriv_bound {X : F → F} {M : ℝ} {γ : ℝ → F}
    (hγd : ∀ t ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt γ (X (γ t)) (Icc (-1) 1) t)
    (hX : ∀ t ∈ Icc (-1 : ℝ) 1, ‖X (γ t)‖ ≤ M) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ‖γ t - γ 0‖ ≤ M * |t| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := γ) (f' := fun t => X (γ t))
    (s := Icc (-1 : ℝ) 1) (C := M) hγd hX (convex_Icc _ _)
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨by norm_num, by norm_num⟩) ht
  simpa using this

end KAM.Wave
