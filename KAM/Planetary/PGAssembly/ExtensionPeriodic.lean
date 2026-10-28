/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.ComplexGlue

/-!
# P Part 5: periodic gluing for the extension (`stepP:p5:ext-glue`, `stepP:p5:ext-per`)

Abstract lemmas on `ℝᴺ`, used by `ExtensionExists`:

* `eventually_eq_zero_of_analyticAt_closure`: the identity theorem near a point of the closure of an
  open set on which an analytic function vanishes;
* `exists_delta_shift_eq`: a uniform radius on which `f (y - s) = f y` for finitely many shifts;
* `tube_glue`: a complexification `F` of a shift-periodic `f` satisfies `F x = F (x - ι s)` whenever
  both `x` and `x - ι s` lie in a thin tube.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-EX.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

/-- Identity theorem near a point of the closure of an open set on which `g` vanishes. -/
theorem eventually_eq_zero_of_analyticAt_closure {N : ℕ} {g : (Fin N → ℝ) → ℝ}
    {G : Set (Fin N → ℝ)} {x : Fin N → ℝ} (hG : IsOpen G) (hx : x ∈ closure G)
    (hg : AnalyticAt ℝ g x) (h0 : ∀ y ∈ G, g y = 0) : ∀ᶠ y in 𝓝 x, g y = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hne := mem_closure_iff_nhds.1 hx (ball x ε) (ball_mem_nhds _ hε)
  obtain ⟨z, hzb, hzG⟩ := hne
  have hana : AnalyticOnNhd ℝ g (ball x ε) := fun y hy => hball y hy
  have hz : g =ᶠ[𝓝 z] 0 := Filter.mem_of_superset (hG.mem_nhds hzG) fun y hy => h0 y hy
  have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected
    hzb hz
  exact Filter.mem_of_superset (ball_mem_nhds _ hε) fun y hy => this hy

/-- A uniform radius around a compact set on which finitely many shift identities hold. -/
theorem exists_delta_shift_eq {N : ℕ} {f : (Fin N → ℝ) → ℝ} {X G : Set (Fin N → ℝ)}
    (hX : IsCompact X) (S : Finset (Fin N → ℝ)) (hG : IsOpen G) (hXG : X ⊆ closure G)
    (hf : ∀ x ∈ X, AnalyticAt ℝ f x) (hfs : ∀ x ∈ X, ∀ s ∈ S, AnalyticAt ℝ f (x - s))
    (hper : ∀ y ∈ G, ∀ s ∈ S, f (y - s) = f y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ y : Fin N → ℝ, (∃ J ∈ X, dist y J < δ) → f (y - s) = f y := by
  set E : Set (Fin N → ℝ) := {y | ∀ s ∈ S, f (y - s) = f y} with hE
  have hXE : X ⊆ interior E := by
    intro x hx
    rw [mem_interior_iff_mem_nhds, hE]
    have hall : ∀ s ∈ S, ∀ᶠ y in 𝓝 x, f (y - s) = f y := by
      intro s hs
      have hg : AnalyticAt ℝ (fun y => f (y - s) - f y) x := by
        have h1 : AnalyticAt ℝ (fun y => f (y - s)) x :=
          (hfs x hx s hs).comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
        exact h1.sub (hf x hx)
      have := eventually_eq_zero_of_analyticAt_closure hG (hXG hx) hg
        (fun y hy => by simp [hper y hy s hs])
      exact this.mono fun y hy => sub_eq_zero.1 hy
    exact (Filter.eventually_all_finset S).2 hall
  obtain ⟨δ, hδ, hth⟩ := hX.exists_thickening_subset_open isOpen_interior hXE
  refine ⟨δ, hδ, fun s hs y hy => ?_⟩
  have : y ∈ thickening δ X := Metric.mem_thickening_iff.2 hy
  exact interior_subset (hth this) s hs

theorem mem_actionNbhd_iff {N : ℕ} {X : Set (Fin N → ℝ)} {r : ℝ} {z : Fin N → ℂ} :
    z ∈ KAM.actionNbhd X r ↔ ∃ J ∈ X, ‖z - KAM.realInclusion N J‖ < r := Iff.rfl

/-- A complexification of a shift-periodic function is shift-periodic on a thin tube. -/
theorem tube_glue {N : ℕ} {f : (Fin N → ℝ) → ℝ} {X : Set (Fin N → ℝ)}
    {F : (Fin N → ℂ) → ℂ} {rho rho1 : ℝ} (hrho1 : 0 < rho1) (h3 : 3 * rho1 ≤ rho)
    (hF : DifferentiableOn ℂ F (KAM.actionNbhd X rho))
    (hFr : ∀ y : Fin N → ℝ, KAM.realInclusion N y ∈ KAM.actionNbhd X rho →
      F (KAM.realInclusion N y) = (f y : ℂ))
    {s : Fin N → ℝ} (hper : ∀ y : Fin N → ℝ, (∃ J ∈ X, dist y J < rho1) → f (y - s) = f y)
    {x : Fin N → ℂ} (hx : x ∈ KAM.actionNbhd X rho1)
    (hxs : x - KAM.realInclusion N s ∈ KAM.actionNbhd X rho1) :
    F x = F (x - KAM.realInclusion N s) := by
  obtain ⟨J, hJ, hxJ⟩ := mem_actionNbhd_iff.1 hx
  obtain ⟨J', hJ', hxJ'⟩ := mem_actionNbhd_iff.1 hxs
  set ι := KAM.realInclusion N with hι
  have hB : ball (ι J) rho1 ⊆ KAM.actionNbhd X rho := fun z hz =>
    mem_actionNbhd_iff.2 ⟨J, hJ, by rw [mem_ball_iff_norm] at hz; linarith⟩
  have hBs : ∀ z ∈ ball (ι J) rho1, z - ι s ∈ KAM.actionNbhd X rho := by
    intro z hz
    refine mem_actionNbhd_iff.2 ⟨J', hJ', ?_⟩
    rw [mem_ball_iff_norm] at hz
    have h1 : ‖z - ι J'- ι s‖ ≤ ‖z - x‖ + ‖x - ι s - ι J'‖ := by
      calc ‖z - ι J' - ι s‖ = ‖(z - x) + (x - ι s - ι J')‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖z - x‖ ≤ ‖z - ι J‖ + ‖x - ι J‖ := by
      calc ‖z - x‖ = ‖(z - ι J) - (x - ι J)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have : ‖z - ι s - ι J'‖ = ‖z - ι J' - ι s‖ := by congr 1; abel
    rw [this]
    have hxJ2 : ‖x - ι J‖ < rho1 := hxJ
    linarith
  have hdiffG : DifferentiableOn ℂ (fun z => F (z - ι s)) (ball (ι J) rho1) := by
    refine hF.comp (differentiableOn_id.sub_const _) fun z hz => hBs z hz
  have hdiffF : DifferentiableOn ℂ F (ball (ι J) rho1) := hF.mono hB
  have hxB : x ∈ ball (ι J) rho1 := by rw [mem_ball_iff_norm]; exact hxJ
  have key := real_slice_identity (isOpen_ball) (convex_ball _ _).isPreconnected hdiffF hdiffG
    (V := ball J rho1) isOpen_ball ⟨J, mem_ball_self hrho1⟩
    (by rintro _ ⟨y, hy, rfl⟩; exact KAM.realInclusion_mem_ball_iff.2 hy)
    (by
      intro y hy
      have hyB : ι y ∈ ball (ι J) rho1 := KAM.realInclusion_mem_ball_iff.2 hy
      have h1 := hFr y (hB hyB)
      have h2 : ι y - ι s = ι (y - s) := by simp
      have h3' := hBs _ hyB
      rw [h2] at h3'
      show F (ι y) = F (ι y - ι s)
      rw [h2, h1, hFr (y - s) h3']
      rw [hper y ⟨J, hJ, by simpa using hy⟩])
  exact key hxB

end KAM.Planetary

end
