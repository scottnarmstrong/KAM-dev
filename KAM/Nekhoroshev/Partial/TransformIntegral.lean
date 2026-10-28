/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Composition
public import KAM.Canonical.CompositionIntegralClass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Integral of a time-dependent family along the extended flow (`bpN:p11:transform`, class part)

Part 11, package N11-F1; the engine of `transform_integral`, ported from
`KAM.Canonical.CompositionIntegral*` to the unequal product `EC n k`. For `ExtCompose` and a family
`v_t ∈ 𝒪_{R,s}`, `|v_t| ≤ U` on `t ∈ [0,1]`, continuous together with its derivative:

* `ext_integral_inClass`: `z ↦ ∫₀¹ v_t(X^t z) dt ∈ 𝒪_{R-ρ,s-σ}` (differentiation under the
  integral, `ParamHyp.intervalIntegral`, and periodicity by translation covariance `flow_d`);
* `coeff_integral_ext`: Fubini on `[0,1] × [0,1]ⁿ`;
* `ext_integral_bound`: the weighted bound `(1 - η)⁻¹ U`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

theorem add_single_eq_ext {m : ℕ} (j : Fin n) (y : (Fin n → ℂ) × (Fin m → ℂ)) :
    y + (Pi.single j 1, 0) = (y.1 + Pi.single j 1, y.2) :=
  Prod.ext rfl (add_zero _)

/-- Translation by a unit angle step does not change membership in `𝒟_{r,s}`. -/
theorem add_single_mem_Dom_iff_ext {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ} (j : Fin n)
    (w : (Fin n → ℂ) × (Fin m → ℂ)) :
    w + (Pi.single j 1, 0) ∈ Dom n D r s ↔ w ∈ Dom n D r s := by
  have h : ∀ i, ((w + (Pi.single j 1, 0)).1 i).im = (w.1 i).im := fun i => by
    simp [Pi.single_apply, apply_ite Complex.im]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by have := h1 i; rwa [h i] at this, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by rw [h i]; exact h1 i, by simpa using h2⟩

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ : EC n k → ℂ}

/-- `X^c_φ` is periodic in the angles on `Ω` if `φ` is. -/
theorem field_periodic (hc : ExtCompose b R' s' R s ρ σ V φ) (j : Fin n) {w : EC n k}
    (hw : w ∈ Dom n b.base (R' - ρ) (s' - σ)) :
    wfield b.c φ (w + (Pi.single j 1, 0)) = wfield b.c φ w := by
  have hper : ∀ y ∈ Dom n b.base R' s', φ (y + (Pi.single j 1, 0)) = φ y := fun y hy => by
    rw [add_single_eq_ext]
    exact hc.hol.periodic j y hy
  have hev : (fun y => φ (y + (Pi.single j 1, 0))) =ᶠ[nhds w] φ :=
    Filter.eventually_of_mem ((isOpen_Dom _ _ _).mem_nhds (hc.dom_sub hw)) hper
  have hf : fderiv ℂ φ (w + (Pi.single j 1, 0)) = fderiv ℂ φ w := by
    rw [← fderiv_comp_add_right]
    exact hev.fderiv_eq
  simp only [wfield, hf]

variable (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) {v : ℝ → EC n k → ℂ}
  (hv : ∀ t ∈ Icc (0 : ℝ) 1, InClass b.base R s (v t))
  (hcont : ContinuousOn (fun p : ℝ × EC n k => v p.1 p.2) (Icc 0 1 ×ˢ Dom n b.base R s))
  (hdcont : ContinuousOn (fun p : ℝ × EC n k => fderiv ℂ (v p.1) p.2)
    (Icc 0 1 ×ˢ Dom n b.base R s))

include hc hk hv hcont hdcont

/-- The integrand with clamped time is a `ParamHyp` family on `𝒟_{R-ρ,s-σ}`. -/
theorem paramHyp_integrand :
    KAM.Canonical.ParamHyp (Dom n b.base (R - ρ) (s - σ))
      (fun τ z => v (KAM.Canonical.clampT τ)
        (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT τ) z)) := by
  obtain ⟨fc, -, -, fDc, -⟩ := KAM.Canonical.flow_b (hc.smallField hk)
  obtain ⟨fd, fm⟩ : (∀ t ∈ Icc (-1 : ℝ) 1, DifferentiableOn ℂ
      (KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R' - ρ) (s' - σ)) t)
      (KAM.Canonical.gaugeInterior (extGauge hc.rho_pos hc.sig_pos)
        (Dom n b.base (R' - ρ) (s' - σ)) (1 / 2))) ∧ True :=
    ⟨(KAM.Canonical.flow_b (hc.smallField hk)).2.1, trivial⟩
  have hΩG := hc.gaugeInterior_half
  have hdom := (composition_domain b hk hc).2
  have hdom' : ∀ z ∈ Dom n b.base (R - ρ) (s - σ), ∀ τ ∈ Icc (-1 : ℝ) 1,
      KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R' - ρ) (s' - σ))
        (KAM.Canonical.clampT τ) z ∈ Dom n b.base R s := fun z hz τ _ =>
    hc.tube_sub (hdom _ (abs_le.2 (KAM.Canonical.clampT_mem_Icc _)) hz)
  have hP : ContinuousOn (fun p : ℝ × EC n k => (KAM.Canonical.clampT p.1, p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n b.base (R - ρ) (s - σ)) :=
    ((KAM.Canonical.continuous_clampT.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hPm : MapsTo (fun p : ℝ × EC n k => (KAM.Canonical.clampT p.1, p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n b.base (R - ρ) (s - σ))
      (Icc (-1 : ℝ) 1 ×ˢ KAM.Canonical.gaugeInterior (extGauge hc.rho_pos hc.sig_pos)
        (Dom n b.base (R' - ρ) (s' - σ)) (1 / 2)) :=
    fun p hp => ⟨KAM.Canonical.clampT_mem_Icc _, hΩG hp.2⟩
  have hΦ : ContinuousOn (fun p : ℝ × EC n k => (KAM.Canonical.clampT p.1,
      KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R' - ρ) (s' - σ))
        (KAM.Canonical.clampT p.1) p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n b.base (R - ρ) (s - σ)) :=
    (KAM.Canonical.continuous_clampT.comp continuous_fst).continuousOn.prodMk (fc.comp hP hPm)
  have hΦm : MapsTo (fun p : ℝ × EC n k => (KAM.Canonical.clampT p.1,
      KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R' - ρ) (s' - σ))
        (KAM.Canonical.clampT p.1) p.2))
      (Icc (-1 : ℝ) 1 ×ˢ Dom n b.base (R - ρ) (s - σ)) (Icc 0 1 ×ˢ Dom n b.base R s) :=
    fun p hp => ⟨KAM.Canonical.clampT_mem _, hdom' p.2 hp.2 _ hp.1⟩
  have hdiffv : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Dom n b.base (R - ρ) (s - σ),
      DifferentiableAt ℂ (v (KAM.Canonical.clampT τ))
        (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT τ) z) :=
    fun τ hτ z hz => ((hv _ (KAM.Canonical.clampT_mem τ)).differentiableOn.differentiableAt
      ((isOpen_Dom _ _ _).mem_nhds (hdom' z hz τ hτ)))
  have hdiffF : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z ∈ Dom n b.base (R - ρ) (s - σ),
      DifferentiableAt ℂ (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT τ)) z :=
    fun τ hτ z hz => (fd _ (KAM.Canonical.clampT_mem_Icc τ)).differentiableAt
      ((KAM.Canonical.isOpen_gaugeInterior (isOpen_Dom _ _ _) _ _).mem_nhds (hΩG hz))
  refine ⟨hcont.comp hΦ hΦm, fun τ hτ => ?_, ?_⟩
  · intro z hz
    exact ((hdiffv τ hτ z hz).comp z (hdiffF τ hτ z hz)).differentiableWithinAt
  · have hcomp : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ Dom n b.base (R - ρ) (s - σ),
        fderiv ℂ (fun z => v (KAM.Canonical.clampT p.1)
          (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT p.1) z)) p.2 =
        (fderiv ℂ (v (KAM.Canonical.clampT p.1))
          (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT p.1) p.2)).comp
          (fderiv ℂ (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT p.1)) p.2) :=
      fun p hp => fderiv_comp p.2 (hdiffv p.1 hp.1 p.2 hp.2) (hdiffF p.1 hp.1 p.2 hp.2)
    exact ContinuousOn.congr (ContinuousOn.clm_comp (hdcont.comp hΦ hΦm) (fDc.comp hP hPm)) hcomp

/-- The class part: `z ↦ ∫₀¹ v_t(X^t z) dt ∈ 𝒪_{R-ρ,s-σ}`. -/
theorem integral_inClass :
    InClass b.base (R - ρ) (s - σ) (fun z => ∫ t in (0 : ℝ)..1, v t (extFlow b R' s' ρ σ φ t z)) := by
  have hΩG := hc.gaugeInterior_half
  have hdom := (composition_domain b hk hc).2
  have hcg : ∀ z : EC n k, ∫ t in (0 : ℝ)..1, v t (extFlow b R' s' ρ σ φ t z) =
      ∫ t in (0 : ℝ)..1, v (KAM.Canonical.clampT t)
        (extFlow b R' s' ρ σ φ (KAM.Canonical.clampT t) z) :=
    fun z => intervalIntegral.integral_congr fun t ht => by
      rw [KAM.Canonical.clampT_of_mem (by simpa [uIcc_of_le zero_le_one] using ht)]
  refine ⟨?_, fun j z hz => ?_⟩
  · intro z hz
    have h := ((hc.paramHyp_integrand hk hv hcont hdcont).intervalIntegral
      (isOpen_Dom _ _ _)).2 1 ⟨by norm_num, le_rfl⟩ z hz
    simp_rw [hcg]
    exact h.differentiableAt.differentiableWithinAt
  · have hz' : z + (Pi.single j 1, 0) ∈ Dom n b.base (R - ρ) (s - σ) :=
      (add_single_mem_Dom_iff_ext j z).2 hz
    have hτΩ : (fun w => w + ((Pi.single j 1 : Fin n → ℂ), (0 : Fin (n + (k + k)) → ℂ))) ''
        Dom n b.base (R' - ρ) (s' - σ) = Dom n b.base (R' - ρ) (s' - σ) := by
      ext w
      have hcancel : w + (-(Pi.single j 1 : Fin n → ℂ), (0 : Fin (n + (k + k)) → ℂ)) +
          (Pi.single j 1, 0) = w := by ext <;> simp
      refine ⟨?_, fun hw => ⟨w + (-(Pi.single j 1 : Fin n → ℂ), (0 : Fin (n + (k + k)) → ℂ)),
        ?_, hcancel⟩⟩
      · rintro ⟨w', hw', rfl⟩
        exact (add_single_mem_Dom_iff_ext j w').2 hw'
      · exact (add_single_mem_Dom_iff_ext (D := b.base) (r := R' - ρ) (s := s' - σ) j _).1
          (by rw [hcancel]; exact hw)
    obtain ⟨-, hflow⟩ := KAM.Canonical.flow_d (hc.smallField hk) hτΩ
      fun w hw => hc.field_periodic j hw
    show ∫ t in (0 : ℝ)..1, v t (extFlow b R' s' ρ σ φ t (z.1 + Pi.single j 1, z.2)) = _
    rw [← add_single_eq_ext]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    have hfl := hflow z (hΩG hz) t ⟨by linarith [ht'.1], ht'.2⟩
    change extFlow b R' s' ρ σ φ t (z + (Pi.single j 1, 0)) = _ at hfl
    rw [hfl]
    have hm := hc.tube_sub (hdom t (abs_le.2 ⟨by linarith [ht'.1], ht'.2⟩) hz)
    rw [add_single_eq_ext]
    exact (hv t ht').periodic j _ hm

end ExtCompose

/-- The unit cube `[0,1]ⁿ`. -/
abbrev cubeE (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

/-- Fubini: the coefficient of `∫₀¹ w_t dt` is `∫₀¹ (coefficient of w_t) dt`, and the coefficients
of the slices are integrable in `t`. -/
theorem coeff_integral_ext {m : ℕ} {w : ℝ → (Fin n → ℂ) × (Fin m → ℂ) → ℂ} {I : Fin m → ℂ}
    (k : Fin n → ℤ)
    (hF : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => w p.1 (fun j => (p.2 j : ℂ), I))
      (Icc (0 : ℝ) 1 ×ˢ cubeE n)) :
    coeff (fun z => ∫ t in (0 : ℝ)..1, w t z) I k = ∫ t in (0 : ℝ)..1, coeff (w t) I k ∧
    IntervalIntegrable (fun t => coeff (w t) I k) volume 0 1 := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt_ext
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ cubeE n) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hf : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      KAM.character (-k) (fun j => (p.2 j : ℂ)) * w p.1 (fun j => (p.2 j : ℂ), I))
      (Icc (0 : ℝ) 1 ×ˢ cubeE n) :=
    (hchar.comp continuous_snd).continuousOn.mul hF
  have hint : Integrable (Function.uncurry fun (t : ℝ) (x : Fin n → ℝ) =>
      KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (cubeE n))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.integrableOn_compact hK).mono_set
      (prod_mono Ioc_subset_Icc_self subset_rfl)
  have hswap := integral_integral_swap hint
  have e1 : coeff (fun z => ∫ t in (0 : ℝ)..1, w t z) I k =
      ∫ x in cubeE n, ∫ t in Ioc (0 : ℝ) 1,
        KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I) := by
    unfold coeff KAM.torusCoeffW KAM.torusAverage
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun x _ => ?_
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  have e2 : ∀ t, coeff (w t) I k = ∫ x in cubeE n,
      KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I) := fun t => by
    unfold coeff KAM.torusCoeffW KAM.torusAverage
    simp only [smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [e1, intervalIntegral.integral_of_le zero_le_one]
    simp_rw [e2]
    exact hswap.symm
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simp_rw [e2]
    exact hint.integral_prod_left

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U : ℝ} {φ : EC n k → ℂ} {v : ℝ → EC n k → ℂ}
  (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k)

include hc hk in
/-- The integrand is jointly continuous in the time and the (real) angles. -/
theorem continuousOn_integrand
    (hcont : ContinuousOn (fun p : ℝ × EC n k => v p.1 p.2) (Icc 0 1 ×ˢ Dom n b.base R s))
    {I : Fin (n + (k + k)) → ℂ} (hI : I ∈ polyNbhd b.base (R - ρ)) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      v p.1 (extFlow b R' s' ρ σ φ p.1 (fun j => (p.2 j : ℂ), I)))
      (Icc (0 : ℝ) 1 ×ˢ cubeE n) := by
  obtain ⟨fc, -, -, -, -⟩ := KAM.Canonical.flow_b (hc.smallField hk)
  have hdom := (composition_domain b hk hc).2
  have hmem : ∀ x : Fin n → ℝ, ((fun j => (x j : ℂ)), I) ∈ Dom n b.base (R - ρ) (s - σ) :=
    fun x => ⟨KAM.ofReal_mem_complexStrip (by linarith [hc.sig_lt]) x, hI⟩
  have hP : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => (p.1, ((fun j => (p.2 j : ℂ)), I)))
      (Icc (0 : ℝ) 1 ×ˢ cubeE n) :=
    (continuous_fst.prodMk ((continuous_realPt_ext.comp continuous_snd).prodMk
      continuous_const)).continuousOn
  have hPm : MapsTo (fun p : ℝ × (Fin n → ℝ) => (p.1, ((fun j => (p.2 j : ℂ)), I)))
      (Icc (0 : ℝ) 1 ×ˢ cubeE n) (Icc (-1 : ℝ) 1 ×ˢ KAM.Canonical.gaugeInterior
        (extGauge hc.rho_pos hc.sig_pos) (Dom n b.base (R' - ρ) (s' - σ)) (1 / 2)) :=
    fun p hp => ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hc.gaugeInterior_half (hmem p.2)⟩
  have hΦ : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      (p.1, extFlow b R' s' ρ σ φ p.1 (fun j => (p.2 j : ℂ), I)))
      (Icc (0 : ℝ) 1 ×ˢ cubeE n) :=
    continuousOn_fst.prodMk (fc.comp hP hPm)
  refine hcont.comp hΦ fun p hp => ⟨hp.1, hc.tube_sub (hdom p.1
    (abs_le.2 ⟨by linarith [hp.1.1], hp.1.2⟩) (hmem p.2))⟩

end ExtCompose

end KAM.Nekhoroshev

end
