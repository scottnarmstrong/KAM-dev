/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Strip.Analytic
public import KAM.Frozen.Defs.ActionNbhd

/-!
# P Part 5: real-slice identity and connected complex tubes (`bpP:p5:ext-glue`, `bpP:p5:be-jet`)

* `real_slice_identity`: two holomorphic functions on a connected open `U ⊆ ℂᴺ` that agree on a
  nonempty open real set `V` (with `ι V ⊆ U`) agree on `U`. Proof: coordinatewise one-variable
  identity theorem on a polydisc around a real point (induction on the set of complexified
  coordinates), then analytic continuation.
* `connected_complex_tube`: the complex `ρ`-neighbourhood of a connected real set is connected.

Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-ID.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology Function

namespace KAM.Planetary

theorem mem_ball_realInclusion_iff {N : ℕ} {x₀ : Fin N → ℝ} {r : ℝ} (hr : 0 < r)
    (z : Fin N → ℂ) :
    z ∈ ball (KAM.realInclusion N x₀) r ↔ ∀ i, ‖z i - (x₀ i : ℂ)‖ < r := by
  rw [mem_ball_iff_norm, pi_norm_lt_iff hr]
  simp

/-- Coordinatewise identity: a function holomorphic on the complex polydisc `ball (ι x₀) r` and
vanishing at its real points vanishes on the whole polydisc. -/
theorem polydisc_zero_of_real_zero {N : ℕ} {x₀ : Fin N → ℝ} {r : ℝ} (hr : 0 < r)
    {h : (Fin N → ℂ) → ℂ} (hh : DifferentiableOn ℂ h (ball (KAM.realInclusion N x₀) r))
    (h0 : ∀ x : Fin N → ℝ, KAM.realInclusion N x ∈ ball (KAM.realInclusion N x₀) r →
      h (KAM.realInclusion N x) = 0) :
    ∀ z ∈ ball (KAM.realInclusion N x₀) r, h z = 0 := by
  classical
  have key : ∀ s : Finset (Fin N), ∀ z ∈ ball (KAM.realInclusion N x₀) r,
      (∀ i ∉ s, (z i).im = 0) → h z = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz him
      have hz' : z = KAM.realInclusion N (fun i => (z i).re) := by
        ext i
        simp only [KAM.realInclusion_apply]
        exact Complex.ext (by simp) (by simpa using him i (by simp))
      rw [hz'] at hz ⊢
      exact h0 _ hz
    | insert j s hjs ih =>
      intro z hz him
      set B : Set ℂ := ball (x₀ j : ℂ) r with hB
      have hupd : ∀ w ∈ B, Function.update z j w ∈ ball (KAM.realInclusion N x₀) r := by
        intro w hw
        rw [mem_ball_realInclusion_iff hr] at hz ⊢
        intro i
        by_cases hij : i = j
        · subst hij; simpa [hB, dist_eq_norm] using hw
        · simpa [Function.update_of_ne hij] using hz i
      have hdiff : DifferentiableOn ℂ (fun w => h (Function.update z j w)) B := by
        intro w hw
        have h1 : DifferentiableWithinAt ℂ h (ball (KAM.realInclusion N x₀) r)
            (Function.update z j w) := hh _ (hupd w hw)
        have h2 : DifferentiableAt ℂ (fun w : ℂ => Function.update z j w) w :=
          (hasFDerivAt_update z w).differentiableAt
        exact h1.comp w h2.differentiableWithinAt (fun w' hw' => hupd w' hw')
      have hreal : ∀ t : ℝ, (t : ℂ) ∈ B → h (Function.update z j (t : ℂ)) = 0 := by
        intro t ht
        refine ih _ (hupd _ ht) fun i hi => ?_
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij]
          exact him i (by simp [hij, hi])
      have hz0 : (x₀ j : ℂ) ∈ B := mem_ball_self hr
      have hfreq : ∃ᶠ w in 𝓝[≠] (x₀ j : ℂ), h (Function.update z j w) = 0 := by
        rw [Filter.frequently_iff]
        intro U hU
        obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
        set δ : ℝ := min ε r / 2 with hδ
        have hδpos : 0 < δ := by positivity
        have hδε : δ < ε := by have := min_le_left ε r; linarith
        have hδr : δ < r := by have := min_le_right ε r; linarith
        have hmem : ((x₀ j + δ : ℝ) : ℂ) ∈ B := by
          simp [hB, dist_eq_norm, abs_of_pos hδpos, hδr]
        refine ⟨_, hεU ⟨?_, ?_⟩, hreal _ hmem⟩
        · simp [dist_eq_norm, abs_of_pos hδpos, hδε]
        · simp only [mem_compl_iff, mem_singleton_iff]
          intro h'; have := congrArg Complex.re h'; simp at this; linarith
      have hana := hdiff.analyticOnNhd Metric.isOpen_ball
      have hzero := hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
        (convex_ball _ _).isPreconnected hz0 hfreq
      have := hzero (show z j ∈ B from by
        simpa [hB, dist_eq_norm] using (mem_ball_realInclusion_iff hr z).1 hz j)
      simpa using this
  intro z hz
  exact key Finset.univ z hz fun i hi => absurd (Finset.mem_univ i) hi

/-- Real-slice identity in several variables: not the one-variable theorem with a renamed domain. -/
theorem real_slice_identity {N : ℕ} {U : Set (Fin N → ℂ)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f g : (Fin N → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {V : Set (Fin N → ℝ)} (hV : IsOpen V) (hVne : V.Nonempty)
    (hVU : KAM.realInclusion N '' V ⊆ U)
    (heq : ∀ x ∈ V, f (KAM.realInclusion N x) = g (KAM.realInclusion N x)) : EqOn f g U := by
  obtain ⟨x₀, hx₀⟩ := hVne
  have hx₀U : KAM.realInclusion N x₀ ∈ U := hVU ⟨x₀, hx₀, rfl⟩
  obtain ⟨r₁, hr₁, hr₁U⟩ := Metric.isOpen_iff.1 hU _ hx₀U
  obtain ⟨r₂, hr₂, hr₂V⟩ := Metric.isOpen_iff.1 hV _ hx₀
  set r := min r₁ r₂ with hr
  have hrpos : 0 < r := lt_min hr₁ hr₂
  have hball : ball (KAM.realInclusion N x₀) r ⊆ U :=
    (ball_subset_ball (min_le_left _ _)).trans hr₁U
  have hzero : ∀ z ∈ ball (KAM.realInclusion N x₀) r, (f - g) z = 0 := by
    refine polydisc_zero_of_real_zero hrpos ((hf.mono hball).sub (hg.mono hball)) ?_
    intro x hx
    have hxV : x ∈ V := by
      apply hr₂V
      rw [KAM.realInclusion_mem_ball_iff] at hx
      exact ball_subset_ball (min_le_right _ _) hx
    simp [heq x hxV]
  have hana : AnalyticOnNhd ℂ (f - g) U :=
    KAM.analyticOnNhd_of_differentiableOn hU (hf.sub hg)
  have h := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hx₀U
    (Filter.mem_of_superset (ball_mem_nhds _ hrpos) fun z hz => hzero z hz)
  intro z hz
  have := h hz
  simpa [sub_eq_zero] using this

/-- The complex `ρ`-neighbourhood of a connected real set is connected. -/
theorem connected_complex_tube {N : ℕ} {X : Set (Fin N → ℝ)}
    (hX : IsConnected X) {rho : ℝ} (hrho : 0 < rho) :
    IsConnected (KAM.actionNbhd X rho) := by
  have hB : IsConnected (ball (0 : Fin N → ℂ) rho) :=
    ⟨⟨0, mem_ball_self hrho⟩, (convex_ball _ _).isPreconnected⟩
  have himg := (hX.prod hB).image
    (fun p : (Fin N → ℝ) × (Fin N → ℂ) => KAM.realInclusion N p.1 + p.2)
    ((KAM.realInclusion N).continuous.comp continuous_fst |>.add continuous_snd).continuousOn
  convert himg using 1
  ext I
  simp only [KAM.actionNbhd, mem_ofPred_eq, mem_image, Prod.exists, mem_prod, mem_ball,
    dist_zero_right]
  constructor
  · rintro ⟨J, hJ, hI⟩
    refine ⟨J, I - (fun i => (J i : ℂ)), ⟨hJ, hI⟩, ?_⟩
    ext i; simp
  · rintro ⟨J, w, ⟨hJ, hw⟩, rfl⟩
    refine ⟨J, hJ, ?_⟩
    convert hw using 2
    ext i; simp

end KAM.Planetary

end
