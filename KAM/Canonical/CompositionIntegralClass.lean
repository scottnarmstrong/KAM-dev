/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.CompositionDomain
public import KAM.Canonical.CompositionCoeff
public import KAM.Canonical.FlowRegular
public import KAM.Canonical.FlowRegularIntegral
import Mathlib.Tactic.Linarith

/-!
# Holomorphy and periodicity of `∫₀¹ v_t ∘ X^t dt` (`bpN:p5:composition-integral`, class part)

Package C5-8. For `ComposeData` and a family `v_t ∈ O(r, s)`, `t ∈ [0, 1]`, continuous together with
its derivative, the function `z ↦ ∫₀¹ v_t(X^t z) dt` lies in `O(r-ρ, s-σ)`:

* `KAM.Canonical.paramHyp_integrand`: the integrand (with the time clamped to `[0, 1]`, so that it
  is a family on `[-1, 1]`) is a `ParamHyp` family on `𝒟_{r-ρ, s-σ}` (`flow_b`);
* `KAM.Canonical.integral_inClass`: holomorphy (differentiation under the integral,
  `ParamHyp.intervalIntegral`) and periodicity (`flow_d`).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- Time clamped to `[0, 1]`. -/
def clampT (τ : ℝ) : ℝ := max 0 (min τ 1)

theorem continuous_clampT : Continuous clampT := by
  unfold clampT
  fun_prop

theorem clampT_mem (τ : ℝ) : clampT τ ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clampT_of_mem {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : clampT τ = τ := by
  unfold clampT
  rw [min_eq_left hτ.2, max_eq_right hτ.1]

theorem clampT_mem_Icc (τ : ℝ) : clampT τ ∈ Icc (-1 : ℝ) 1 :=
  ⟨by linarith [(clampT_mem τ).1], (clampT_mem τ).2⟩

/-- The integrand with clamped time is a `ParamHyp` family on `𝒟_{r-ρ, s-σ}`. -/
theorem paramHyp_integrand (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {v : ℝ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, InClass D r s (v t))
    (hc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => v p.1 p.2)
      (Icc 0 1 ×ˢ Dom n D r s))
    (hDc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ Dom n D r s)) :
    ParamHyp (Dom n D (r - ρ) (s - σ))
      (fun τ z => v (clampT τ) (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT τ) z)) := by
  obtain ⟨fc, fd, fm, fDc, -⟩ := flow_b hd.smallField
  have hΩG : Dom n D (r - ρ) (s - σ) ⊆ gaugeInterior hd.gauge hd.omega (1 / 2) :=
    hd.gaugeInterior_half
  have hdom := (composition_domain hd).2.2.2
  have hP : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => (clampT p.1, p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n D (r - ρ) (s - σ)) :=
    ((continuous_clampT.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hPm : MapsTo (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => (clampT p.1, p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n D (r - ρ) (s - σ))
      (Icc (-1 : ℝ) 1 ×ˢ gaugeInterior hd.gauge hd.omega (1 / 2)) :=
    fun p hp => ⟨clampT_mem_Icc _, hΩG hp.2⟩
  have hΦ : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) =>
      (clampT p.1, flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT p.1) p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n D (r - ρ) (s - σ)) :=
    (continuous_clampT.comp continuous_fst).continuousOn.prodMk (fc.comp hP hPm)
  have hΦm : MapsTo (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) =>
      (clampT p.1, flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT p.1) p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n D (r - ρ) (s - σ)) (Icc 0 1 ×ˢ Dom n D r s) :=
    fun p hp => ⟨clampT_mem _, hdom p.2 hp.2 _ (clampT_mem_Icc _)⟩
  have hdiffv : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Dom n D (r - ρ) (s - σ),
      DifferentiableAt ℂ (v (clampT τ))
        (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT τ) z) :=
    fun τ hτ z hz => ((hv _ (clampT_mem τ)).differentiableOn.differentiableAt
      ((isOpen_Dom _ _ _).mem_nhds (hdom z hz _ (clampT_mem_Icc _))))
  have hdiffF : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Dom n D (r - ρ) (s - σ),
      DifferentiableAt ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT τ)) z :=
    fun τ hτ z hz => (fd _ (clampT_mem_Icc τ)).differentiableAt
      ((isOpen_gaugeInterior (isOpen_Dom _ _ _) _ _).mem_nhds (hΩG hz))
  refine ⟨hc.comp hΦ hΦm, fun τ hτ => ?_, ?_⟩
  · intro z hz
    exact ((hdiffv τ hτ z hz).comp z (hdiffF τ hτ z hz)).differentiableWithinAt
  · have hcomp : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Dom n D (r - ρ) (s - σ),
        fderiv ℂ (fun z => v (clampT p.1) (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega
          (clampT p.1) z)) p.2 =
        (fderiv ℂ (v (clampT p.1))
          (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT p.1) p.2)).comp
          (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT p.1)) p.2) :=
      fun p hp => fderiv_comp p.2 (hdiffv p.1 hp.1 p.2 hp.2) (hdiffF p.1 hp.1 p.2 hp.2)
    refine ContinuousOn.congr (ContinuousOn.clm_comp (hDc.comp hΦ hΦm) (fDc.comp hP hPm)) hcomp

theorem add_single_eq (j : Fin n) (y : (Fin n → ℂ) × (Fin n → ℂ)) :
    y + (Pi.single j 1, 0) = (y.1 + Pi.single j 1, y.2) :=
  Prod.ext rfl (add_zero _)

/-- Translation by a unit angle step does not change membership in `𝒟_{r,s}`. -/
theorem add_single_mem_Dom_iff {r s : ℝ} (j : Fin n) (w : (Fin n → ℂ) × (Fin n → ℂ)) :
    w + (Pi.single j 1, 0) ∈ Dom n D r s ↔ w ∈ Dom n D r s := by
  have h : ∀ i, ((w + (Pi.single j 1, 0)).1 i).im = (w.1 i).im := fun i => by
    simp [Pi.single_apply, apply_ite Complex.im]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by have := h1 i; rwa [h i] at this, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by rw [h i]; exact h1 i, by simpa using h2⟩

/-- `X_φ` is periodic in the angles on `Ω` if `φ` is. -/
theorem field_periodic (hd : ComposeData D r s r' s' ρ σ Φ φ) (j : Fin n)
    {w : (Fin n → ℂ) × (Fin n → ℂ)} (hw : w ∈ hd.omega) :
    KAM.hamiltonianVectorFieldℂ φ (w + (Pi.single j 1, 0)) = KAM.hamiltonianVectorFieldℂ φ w := by
  have hsub : hd.omega ⊆ Dom n D r' s' :=
    Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ])
  have hper : ∀ y ∈ Dom n D r' s', φ (y + (Pi.single j 1, 0)) = φ y := fun y hy =>
    by rw [add_single_eq]; exact hd.φ_class.periodic j y hy
  have hev : (fun y => φ (y + (Pi.single j 1, 0))) =ᶠ[nhds w] φ :=
    Filter.eventually_of_mem ((isOpen_Dom _ _ _).mem_nhds (hsub hw)) hper
  have hf : fderiv ℂ φ (w + (Pi.single j 1, 0)) = fderiv ℂ φ w := by
    rw [← fderiv_comp_add_right]
    exact hev.fderiv_eq
  simp only [KAM.hamiltonianVectorFieldℂ, hf]

/-- `bpN:p5:composition-integral`, the class part: `z ↦ ∫₀¹ v_t(X^t z) dt ∈ O(r-ρ, s-σ)`. -/
theorem integral_inClass (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {v : ℝ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, InClass D r s (v t))
    (hc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => v p.1 p.2)
      (Icc 0 1 ×ˢ Dom n D r s))
    (hDc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ Dom n D r s)) :
    InClass D (r - ρ) (s - σ)
      (fun z => ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) := by
  have hΩG : Dom n D (r - ρ) (s - σ) ⊆ gaugeInterior hd.gauge hd.omega (1 / 2) :=
    hd.gaugeInterior_half
  have hdom := (composition_domain hd).2.2.2
  have hcg : ∀ z : (Fin n → ℂ) × (Fin n → ℂ),
      ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z) =
      ∫ t in (0 : ℝ)..1,
        v (clampT t) (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega (clampT t) z) :=
    fun z => intervalIntegral.integral_congr fun t ht => by
      rw [clampT_of_mem (by simpa [uIcc_of_le zero_le_one] using ht)]
  refine ⟨?_, fun j z hz => ?_⟩
  · intro z hz
    have h := ((paramHyp_integrand hd hv hc hDc).intervalIntegral (isOpen_Dom _ _ _)).2 1
      ⟨by norm_num, le_rfl⟩ z hz
    simp_rw [hcg]
    exact h.differentiableAt.differentiableWithinAt
  · have hz' : z + (Pi.single j 1, 0) ∈ Dom n D (r - ρ) (s - σ) :=
      (add_single_mem_Dom_iff j z).2 hz
    have hτΩ : (fun w => w + ((Pi.single j 1 : Fin n → ℂ), (0 : Fin n → ℂ))) '' hd.omega =
        hd.omega := by
      ext w
      have hcancel : w + (-(Pi.single j 1 : Fin n → ℂ), (0 : Fin n → ℂ)) +
          (Pi.single j 1, 0) = w := by ext <;> simp
      refine ⟨?_, fun hw => ⟨w + (-(Pi.single j 1 : Fin n → ℂ), (0 : Fin n → ℂ)), ?_, hcancel⟩⟩
      · rintro ⟨w', hw', rfl⟩
        exact (add_single_mem_Dom_iff j w').2 hw'
      · exact (add_single_mem_Dom_iff (D := D) (r := r' - ρ) (s := s' - σ) j _).1
          (by rw [hcancel]; exact hw)
    obtain ⟨-, hflow⟩ := flow_d hd.smallField hτΩ fun w hw => field_periodic hd j hw
    show ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t
        (z.1 + Pi.single j 1, z.2)) = _
    rw [← add_single_eq]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    rw [hflow z (hΩG hz) t ⟨by linarith [ht'.1], ht'.2⟩]
    have hm := hdom z hz t ⟨by linarith [ht'.1], ht'.2⟩
    rw [add_single_eq]
    exact (hv t ht').periodic j _ hm

end KAM.Canonical

end
