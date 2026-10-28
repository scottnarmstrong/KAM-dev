/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Canonical.CompositionIntegralClass
public import KAM.Planetary.Averaging.OscillatorComposition
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Parts 2-3: composition integral for the oscillator class (`stepP:p2:oi-transfer`)

For `OscComposeData` and a family `v_t` of the oscillator class on the one-loss domain `𝒪`,
`|v_t| ≤ B` on `t ∈ [0, 1]`, continuous together with its phase derivative, the function
`z ↦ ∫₀¹ v_t(X^t_φ z) dt` lies in the oscillator class on the two-loss domain with weighted bound
`(1 - η)⁻¹ B`.

* `osc_integral_class`: holomorphy (differentiation under the integral, the integrand with clamped
  time is a `ParamHyp` family on the two-loss domain) and fast-angle periodicity (`flow_d`);
* `coeff_integral_flat`: Fubini on `[0,1] × [0,1]ⁿ`, for an independent parameter dimension;
* `osc_composition_integral`: the weighted bound, from the bound of each slice
  (`osc_composition_t`), the triangle inequality for the integral, and the finite partial sums of
  the coefficient series (no supremum-to-weighted conversion loss).

Design `docs/tracks/P/design/P23-LEAN-DESIGN.md` (Revision 3), package P23-13f.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real Filter

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Flat

variable {n N : ℕ}

/-- The unit cube `[0,1]ⁿ`. -/
abbrev oscCube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

private theorem continuous_realPt'' : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-- Fubini: the coefficient of `∫₀¹ w_t dt` is `∫₀¹ (coefficient of w_t) dt`, and the coefficients
of the slices are integrable in `t`. -/
theorem coeff_integral_flat {w : ℝ → (Fin n → ℂ) × (Fin N → ℂ) → ℂ} {I : Fin N → ℂ}
    (k : Fin n → ℤ)
    (hF : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => w p.1 (fun j => (p.2 j : ℂ), I))
      (Icc (0 : ℝ) 1 ×ˢ oscCube n)) :
    coeff (fun z => ∫ t in (0 : ℝ)..1, w t z) I k = ∫ t in (0 : ℝ)..1, coeff (w t) I k ∧
    IntervalIntegrable (fun t => coeff (w t) I k) volume 0 1 := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt''
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ oscCube n) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hf : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      KAM.character (-k) (fun j => (p.2 j : ℂ)) * w p.1 (fun j => (p.2 j : ℂ), I))
      (Icc (0 : ℝ) 1 ×ˢ oscCube n) :=
    (hchar.comp continuous_snd).continuousOn.mul hF
  have hint : Integrable (Function.uncurry fun (t : ℝ) (x : Fin n → ℝ) =>
      KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (oscCube n))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.integrableOn_compact hK).mono_set
      (prod_mono Ioc_subset_Icc_self subset_rfl)
  have hswap := integral_integral_swap hint
  have e1 : coeff (fun z => ∫ t in (0 : ℝ)..1, w t z) I k =
      ∫ x in oscCube n, ∫ t in Ioc (0 : ℝ) 1,
        KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I) := by
    unfold coeff KAM.torusCoeffW KAM.torusAverage
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun x _ => ?_
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  have e2 : ∀ t, coeff (w t) I k = ∫ x in oscCube n,
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

/-- The weighted bound from the bounds of all finite partial sums of the coefficient series. -/
private theorem wsummable_of_finset_le' {u : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} {s B : ℝ}
    {I : Fin N → ℂ} (h : ∀ Λ : Finset (Fin n → ℤ),
      ∑ k ∈ Λ, ‖coeff u I k‖ * modeWeight s k ≤ B) :
    WSummable u s I ∧ wsum u s I ≤ B :=
  have hnn : 0 ≤ fun k : Fin n → ℤ => ‖coeff u I k‖ * modeWeight s k := fun _ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hsum : WSummable u s I := summable_of_sum_le hnn h
  ⟨hsum, hsum.tsum_le_of_sum_le h⟩

end Flat

section OscCompositionIntegral

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ Φ : ℝ} {φ : CHam (n + m)}

/-- The two-loss domain lies in the `1/2`-gauge interior of the flow domain. -/
theorem OscComposeData.sub_gaugeInterior (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ) :
    oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) ⊆
      gaugeInterior H.toFlowHyp.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (1 / 2) :=
  fun _ hz w hw => H.toFlowHyp.one hz w (hw.trans (by norm_num))

/-- Trajectories from the two-loss domain stay in the flow domain. -/
theorem OscComposeData.flow_mem (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    {z : CPhase (n + m)}
    (hz : z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z ∈
        oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) :=
  (flow_b H.toFlowHyp.smallField).2.2.1 t ht z (H.sub_gaugeInterior hz)

/-- The integrand with clamped time is a `ParamHyp` family on the two-loss domain. -/
theorem osc_paramHyp_integrand (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    {v : ℝ → CHam (n + m)}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t))
    (hc : ContinuousOn (fun p : ℝ × CPhase (n + m) => v p.1 p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)))
    (hDc : ContinuousOn (fun p : ℝ × CPhase (n + m) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ))) :
    ParamHyp (oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ))
      (fun τ z => v (clampT τ) (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT τ) z)) := by
  have F := H.toFlowHyp
  obtain ⟨fc, fd, fm, fDc, -⟩ := flow_b F.smallField
  have hΩG := H.sub_gaugeInterior
  have hdom : ∀ z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
      ∀ t ∈ Icc (-1 : ℝ) 1, flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z ∈
        oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) :=
    fun z hz t ht => H.flow_mem hz ht
  have hP : ContinuousOn (fun p : ℝ × CPhase (n + m) => (clampT p.1, p.2))
      (Icc (-1 : ℝ) 1 ×ˢ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)) :=
    ((continuous_clampT.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hPm : MapsTo (fun p : ℝ × CPhase (n + m) => (clampT p.1, p.2))
      (Icc (-1 : ℝ) 1 ×ˢ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ))
      (Icc (-1 : ℝ) 1 ×ˢ gaugeInterior F.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (1 / 2)) :=
    fun p hp => ⟨clampT_mem_Icc _, hΩG hp.2⟩
  have hΦ : ContinuousOn (fun p : ℝ × CPhase (n + m) =>
      (clampT p.1, flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT p.1) p.2))
      (Icc (-1 : ℝ) 1 ×ˢ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)) :=
    (continuous_clampT.comp continuous_fst).continuousOn.prodMk (fc.comp hP hPm)
  have hΦm : MapsTo (fun p : ℝ × CPhase (n + m) =>
      (clampT p.1, flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT p.1) p.2))
      (Icc (-1 : ℝ) 1 ×ˢ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ))
      (Icc 0 1 ×ˢ oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) :=
    fun p hp => ⟨clampT_mem _, hdom p.2 hp.2 _ (clampT_mem_Icc _)⟩
  have hdiffv : ∀ τ ∈ Icc (-1 : ℝ) 1,
      ∀ z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
      DifferentiableAt ℂ (v (clampT τ)) (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT τ) z) :=
    fun τ hτ z hz => ((hv _ (clampT_mem τ)).1.differentiableAt
      ((isOpen_oscDom _ _ _ _ _).mem_nhds (hdom z hz _ (clampT_mem_Icc _))))
  have hdiffF : ∀ τ ∈ Icc (-1 : ℝ) 1,
      ∀ z ∈ oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
      DifferentiableAt ℂ (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT τ)) z :=
    fun τ hτ z hz => (fd _ (clampT_mem_Icc τ)).differentiableAt
      ((isOpen_gaugeInterior (isOpen_oscDom _ _ _ _ _) _ _).mem_nhds (hΩG hz))
  refine ⟨hc.comp hΦ hΦm, fun τ hτ => ?_, ?_⟩
  · intro z hz
    exact ((hdiffv τ hτ z hz).comp z (hdiffF τ hτ z hz)).differentiableWithinAt
  · have hcomp : ∀ p ∈ Icc (-1 : ℝ) 1 ×ˢ
        oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ),
        fderiv ℂ (fun z => v (clampT p.1) (flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT p.1) z)) p.2 =
        (fderiv ℂ (v (clampT p.1))
          (flow (KAM.hamiltonianVectorFieldℂ φ)
            (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT p.1) p.2)).comp
          (fderiv ℂ (flow (KAM.hamiltonianVectorFieldℂ φ)
            (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT p.1)) p.2) :=
      fun p hp => fderiv_comp p.2 (hdiffv p.1 hp.1 p.2 hp.2) (hdiffF p.1 hp.1 p.2 hp.2)
    exact ContinuousOn.congr (ContinuousOn.clm_comp (hDc.comp hΦ hΦm) (fDc.comp hP hPm)) hcomp

/-- Holomorphy and fast-angle periodicity of `z ↦ ∫₀¹ v_t(X^t z) dt` on the two-loss domain. -/
theorem osc_integral_class (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    {v : ℝ → CHam (n + m)}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t))
    (hc : ContinuousOn (fun p : ℝ × CPhase (n + m) => v p.1 p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)))
    (hDc : ContinuousOn (fun p : ℝ × CPhase (n + m) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ))) :
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
      (fun z => ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)) := by
  have F := H.toFlowHyp
  have hΩG := H.sub_gaugeInterior
  have hcg : ∀ z : CPhase (n + m),
      ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z) =
      ∫ t in (0 : ℝ)..1, v (clampT t) (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) (clampT t) z) :=
    fun z => intervalIntegral.integral_congr fun t ht => by
      rw [clampT_of_mem (by simpa [uIcc_of_le zero_le_one] using ht)]
  refine ⟨?_, fun j z hz => ?_⟩
  · intro z hz
    have h := ((osc_paramHyp_integrand H hv hc hDc).intervalIntegral
      (isOpen_oscDom _ _ _ _ _)).2 1 ⟨by norm_num, le_rfl⟩ z hz
    simp_rw [hcg]
    exact h.differentiableAt.differentiableWithinAt
  · have hk : (fun i => (((Pi.single j (1 : ℤ) : Fin n → ℤ) i : ℤ) : ℂ)) =
        (Pi.single j 1 : Fin n → ℂ) := by
      ext i; by_cases h : i = j <;> simp [h]
    have hτΩ := oscDom_shift_image (m := m) (D := D) (r := r - ρ) (rp := rp - ρp) (rq := rq - ρq)
      (S := S - σ) (a := (Pi.single j 1 : Fin n → ℂ))
      (fun i => by by_cases h : i = j <;> simp [h])
    have hτF : ∀ w ∈ oscO (m := m) D r rp rq S ρ ρp ρq σ,
        KAM.hamiltonianVectorFieldℂ φ (w + fastShift (m := m) (Pi.single j 1)) =
          KAM.hamiltonianVectorFieldℂ φ w := fun w hw => by
      have := F.cls.field_periodic (oscDom_mono (by linarith [F.hρ]) (by linarith [F.hρp])
        (by linarith [F.hρq]) (by linarith [F.hσ])) (Pi.single j 1) hw
      rwa [hk] at this
    obtain ⟨-, hflow⟩ := flow_d F.smallField hτΩ hτF
    have hsh : ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m)) =
        z + fastShift (m := m) (Pi.single j 1) := by
      rw [fastShift_single]; ext <;> simp
    show ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t
        ((z.1 + Pi.single (Fin.castAdd m j) 1, z.2) : CPhase (n + m))) = _
    rw [hsh]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc_of_le zero_le_one] using ht
    have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht'.1], ht'.2⟩
    rw [hflow z (hΩG hz) t htI]
    have hm := H.flow_mem hz htI
    have := (hv t ht').periodic_int (Pi.single j 1) hm
    rwa [hk] at this

/-- Joint continuity of the flat integrand on the real angle cube, at a fixed parameter. -/
theorem osc_continuousOn_integrand (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    {v : ℝ → CHam (n + m)}
    (hc : ContinuousOn (fun p : ℝ × CPhase (n + m) => v p.1 p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)))
    {x : Fin (n + (m + m)) → ℂ}
    (hx : x ∈ oscParams (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq)) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      v p.1 (flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) p.1
        (oscUnpack (fun j => (p.2 j : ℂ), x))))
      (Icc (0 : ℝ) 1 ×ˢ oscCube n) := by
  have F := H.toFlowHyp
  obtain ⟨fc, -, -, -, -⟩ := flow_b F.smallField
  have hS2 : 0 < S - 2 * σ := by linarith [H.widths.2.2.2.2.2.2.1, H.widths.2.2.2.2.2.2.2]
  have hmem : ∀ θ : Fin n → ℝ, oscUnpack (m := m) (fun j => (θ j : ℂ), x) ∈
      oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) := fun θ =>
    oscUnpack_mem_oscDom.2 ⟨KAM.ofReal_mem_complexStrip hS2 θ, hx⟩
  have hP : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      (p.1, oscUnpack (m := m) (fun j => (p.2 j : ℂ), x))) (Icc (0 : ℝ) 1 ×ˢ oscCube n) :=
    (continuous_fst.prodMk ((oscUnpackL (m := m)).continuous.comp
      (continuous_realPt''.prodMk continuous_const) |>.comp continuous_snd)).continuousOn
  have hPm : MapsTo (fun p : ℝ × (Fin n → ℝ) =>
      (p.1, oscUnpack (m := m) (fun j => (p.2 j : ℂ), x))) (Icc (0 : ℝ) 1 ×ˢ oscCube n)
      (Icc (-1 : ℝ) 1 ×ˢ gaugeInterior F.W (oscO (m := m) D r rp rq S ρ ρp ρq σ) (1 / 2)) :=
    fun p hp => ⟨⟨by linarith [hp.1.1], hp.1.2⟩, H.sub_gaugeInterior (hmem p.2)⟩
  have hΦ : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      (p.1, flow (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) p.1
        (oscUnpack (m := m) (fun j => (p.2 j : ℂ), x)))) (Icc (0 : ℝ) 1 ×ˢ oscCube n) :=
    continuousOn_fst.prodMk (fc.comp hP hPm)
  exact hc.comp hΦ fun p hp => ⟨hp.1, H.flow_mem (hmem p.2) ⟨by linarith [hp.1.1], hp.1.2⟩⟩

theorem osc_composition_integral (H : OscComposeData D r rp rq S ρ ρp ρq σ Φ φ)
    {v : ℝ → CHam (n + m)} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1,
      oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t) ∧
      oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (v t) B)
    (hc : ContinuousOn (fun p : ℝ × CPhase (n + m) => v p.1 p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)))
    (hDc : ContinuousOn (fun p : ℝ × CPhase (n + m) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ))) :
    let R := fun z => ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) R ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) R
      ((1 - oscTheta m Φ (min (ρ * σ) (ρp * ρq)))⁻¹ * B) := by
  intro R
  refine ⟨osc_integral_class H (fun t ht => (hv t ht).1) hc hDc, ?_⟩
  obtain ⟨-, hq0, -, hqθ, hθ1⟩ := osc_hat_ratio H
  set θ := oscTheta m Φ (min (ρ * σ) (ρp * ρq)) with hθ
  have hθ0 : 0 ≤ θ := hq0.trans hqθ
  have hpos : 0 < 1 - θ := by linarith
  have hS2 : 0 < S - 2 * σ := by linarith [H.widths.2.2.2.2.2.2.1, H.widths.2.2.2.2.2.2.2]
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1,
      oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
        (fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)) ((1 - θ)⁻¹ * B) := fun t ht => by
    obtain ⟨-, h⟩ := osc_composition_t H (hv t ht).1 (hv t ht).2 hB
      (t := t) ⟨by linarith [ht.1], ht.2⟩
    refine h.mono_gen le_rfl le_rfl le_rfl le_rfl
      (mul_le_mul_of_nonneg_right (inv_anti₀ hpos ?_) hB)
    rw [abs_of_nonneg ht.1]
    nlinarith [ht.2]
  intro x hx
  refine wsummable_of_finset_le' fun Λ => ?_
  have hF := osc_continuousOn_integrand H hc hx
  have hw : ∀ k : Fin n → ℤ, 0 < modeWeight (S - 2 * σ) k := fun k => Real.exp_pos _
  have hcoef : ∀ k, coeff (oscFunction R) x k = ∫ t in (0 : ℝ)..1,
        coeff (oscFunction fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)) x k ∧
      IntervalIntegrable (fun t => coeff (oscFunction fun z => v t (flow
        (KAM.hamiltonianVectorFieldℂ φ)
        (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)) x k) volume 0 1 := fun k =>
    coeff_integral_flat (w := fun t y => v t (flow (KAM.hamiltonianVectorFieldℂ φ)
      (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t (oscUnpack y))) k hF
  calc ∑ k ∈ Λ, ‖coeff (oscFunction R) x k‖ * modeWeight (S - 2 * σ) k
      ≤ ∑ k ∈ Λ, (∫ t in (0 : ℝ)..1, ‖coeff (oscFunction fun z => v t (flow
          (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)) x k‖) *
          modeWeight (S - 2 * σ) k := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (hw k).le
        rw [(hcoef k).1]
        exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ∫ t in (0 : ℝ)..1, ∑ k ∈ Λ, ‖coeff (oscFunction fun z => v t (flow
          (KAM.hamiltonianVectorFieldℂ φ)
          (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) t z)) x k‖ *
          modeWeight (S - 2 * σ) k := by
        rw [intervalIntegral.integral_finsetSum fun k _ => ((hcoef k).2.norm).mul_const _]
        exact Finset.sum_congr rfl fun k _ => (intervalIntegral.integral_mul_const _ _).symm
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - θ)⁻¹ * B := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (by
            have := IntervalIntegrable.sum Λ fun k _ => ((hcoef k).2.norm).mul_const
              (modeWeight (S - 2 * σ) k)
            simpa [Finset.sum_fn] using this)
          intervalIntegrable_const fun t ht => ?_
        obtain ⟨h1, h2⟩ := hslice t ht x hx
        exact (h1.sum_le_tsum Λ fun k _ => mul_nonneg (norm_nonneg _) (hw k).le).trans h2
    _ = (1 - θ)⁻¹ * B := by simp

end OscCompositionIntegral

end KAM.Planetary

end
