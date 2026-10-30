/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.FrequencyMap
public import KAM.Planetary.PG.Setting
public import KAM.Head.DerivativeBounds
public import KAM.Strip.Analytic
public import KAM.Strip.AnalyticTaylor

/-!
# Track R: the real neighbourhood and analyticity of the frequency map

* `KAM.Planetary.realNbhd B r` (the real `r`-neighbourhood, by witnesses) is open, contains
  `closure B` for `r > 0`, is connected when `B` is, and its points have real inclusion in
  `actionNbhd B r`.
* `analyticOnNhd_frequencyMap`: if `h` is holomorphic on `actionNbhd B r₀`, the frozen frequency
  map `frequencyMap h`, the real gradient of `I ↦ Re h(ι I)`, is real-analytic on
  `realNbhd B r₀` (no realness of `h` is needed).
* `analyticOnNhd_gradC`: the complex gradient `z ↦ (∂ᵢ h(z))ᵢ` is holomorphic on `actionNbhd B r₀`.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Russmann

open KAM KAM.Planetary

variable {n : ℕ}

/-! ### The real neighbourhood -/

theorem isOpen_realNbhd (B : Set (Fin n → ℝ)) (r : ℝ) : IsOpen (realNbhd B r) := by
  have : realNbhd B r = ⋃ J ∈ B, ball J r := by
    ext x; simp [realNbhd, mem_ball]
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

theorem subset_realNbhd {B : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 < r) : B ⊆ realNbhd B r :=
  fun x hx => ⟨x, hx, by simpa using hr⟩

theorem closure_subset_realNbhd {B : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 < r) :
    closure B ⊆ realNbhd B r := by
  intro x hx
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx r hr
  exact ⟨y, hy, hd⟩

/-- The real `r`-neighbourhood of `B` is the Minkowski sum `B + ball 0 r`. -/
theorem realNbhd_eq_image_add (B : Set (Fin n → ℝ)) (r : ℝ) :
    realNbhd B r = (fun p : (Fin n → ℝ) × (Fin n → ℝ) => p.1 + p.2) '' (B ×ˢ ball 0 r) := by
  ext x
  constructor
  · rintro ⟨J, hJ, hx⟩
    exact ⟨(J, x - J), ⟨hJ, by simpa [mem_ball, dist_eq_norm] using hx⟩, by simp⟩
  · rintro ⟨⟨J, w⟩, ⟨hJ, hw⟩, rfl⟩
    exact ⟨J, hJ, by simpa [mem_ball, dist_eq_norm] using hw⟩

/-- The real `r`-neighbourhood of a connected set is connected (`r > 0`). -/
theorem isConnected_realNbhd {B : Set (Fin n → ℝ)} (hB : IsConnected B) {r : ℝ} (hr : 0 < r) :
    IsConnected (realNbhd B r) := by
  rw [realNbhd_eq_image_add]
  exact (hB.prod (isConnected_ball hr)).image _ (continuous_fst.add continuous_snd).continuousOn

theorem realInclusion_mem_actionNbhd {B : Set (Fin n → ℝ)} {r : ℝ} {x : Fin n → ℝ}
    (hx : x ∈ realNbhd B r) : realInclusion n x ∈ actionNbhd B r := by
  obtain ⟨J, hJ, hd⟩ := hx
  refine ⟨J, hJ, ?_⟩
  show ‖realInclusion n x - realInclusion n J‖ < r
  rw [← map_sub, norm_realInclusion, ← dist_eq_norm]
  exact hd

/-! ### Analyticity -/

/-- The frozen frequency map of a function holomorphic on `actionNbhd B r₀` is real-analytic on
the real neighbourhood `realNbhd B r₀`. -/
theorem analyticOnNhd_frequencyMap {B : Set (Fin n → ℝ)} {r₀ : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (actionNbhd B r₀)) :
    AnalyticOnNhd ℝ (frequencyMap h) (realNbhd B r₀) := by
  have hU : IsOpen (actionNbhd B r₀) := KAM.Head.isOpen_actionNbhd B r₀
  have hA : AnalyticOnNhd ℂ h (actionNbhd B r₀) := analyticOnNhd_of_differentiableOn hU hh
  have hW : IsOpen (realNbhd B r₀) := isOpen_realNbhd B r₀
  -- `φ = Re ∘ h ∘ ι` is real-analytic on the real neighbourhood
  have hφ : AnalyticOnNhd ℝ (fun J : Fin n → ℝ => (h fun j => (J j : ℂ)).re) (realNbhd B r₀) :=
    fun x hx => (Complex.reCLM.analyticAt _).comp
      (analyticOnNhd_comp_realInclusion hA x (realInclusion_mem_actionNbhd hx))
  have hdφ := hφ.fderiv
  intro y hy
  refine analyticAt_pi_iff.2 fun i => ?_
  have := ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Fin n → ℝ)).analyticAt _).comp
    (hdφ y hy)
  exact this

/-- The complex gradient `z ↦ (∂ᵢ h(z))ᵢ` of a function holomorphic on `actionNbhd B r₀` is
holomorphic there. -/
theorem analyticOnNhd_gradC {B : Set (Fin n → ℝ)} {r₀ : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (actionNbhd B r₀)) :
    AnalyticOnNhd ℂ (fun x : Fin n → ℂ => fun i => fderiv ℂ h x (Pi.single i 1))
      (actionNbhd B r₀) := by
  have hU : IsOpen (actionNbhd B r₀) := KAM.Head.isOpen_actionNbhd B r₀
  have hA : AnalyticOnNhd ℂ h (actionNbhd B r₀) := analyticOnNhd_of_differentiableOn hU hh
  intro z hz
  refine analyticAt_pi_iff.2 fun i => ?_
  have := ((ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1 : Fin n → ℂ)).analyticAt _).comp
    (hA.fderiv z hz)
  exact this

end KAM.Russmann

end
