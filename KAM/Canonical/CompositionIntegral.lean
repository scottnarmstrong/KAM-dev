/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Composition
public import KAM.Canonical.CompositionIntegralClass
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Composition of a time-dependent family (`bpN:p5:composition-integral`)

Blueprint-N Part 5, node `bpN:p5:composition-integral` (design
`docs/tracks/N/design/PART145-LEAN-DESIGN.md`, package C5-8). For `ComposeData` and a family
`v_t ∈ O(r, s)`, `|v_t|_{r,s} ≤ V` on `t ∈ [0, 1]`, continuous together with its derivative,
`z ↦ ∫₀¹ v_t(X^t z) dt` lies in `O(r-ρ, s-σ)` with norm `≤ (1 - η)⁻¹ V`.

The class part is `KAM.Canonical.integral_inClass` (`Canonical/CompositionIntegralClass`). Here:

* `KAM.Canonical.coeff_integral`: Fubini on `[0,1] × [0,1]ⁿ`, the coefficient of the integral is
  the integral of the coefficients;
* `KAM.Canonical.composition_integral`: the weighted bound, from the bound of each slice
  (`composition_t`), the triangle inequality for the integral, and the finite partial sums of the
  coefficient series (no Tonelli in `k` is needed).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ V : ℝ} {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The unit cube `[0,1]ⁿ`. -/
abbrev compCube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

private theorem continuous_realPt : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-- Fubini: the coefficient of `∫₀¹ w_t dt` is `∫₀¹ (coefficient of w_t) dt`, and the coefficients
of the slices are integrable in `t`. -/
theorem coeff_integral {w : ℝ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {I : Fin n → ℂ} (k : Fin n → ℤ)
    (hF : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => w p.1 (fun j => (p.2 j : ℂ), I))
      (Icc (0 : ℝ) 1 ×ˢ compCube n)) :
    coeff (fun z => ∫ t in (0 : ℝ)..1, w t z) I k = ∫ t in (0 : ℝ)..1, coeff (w t) I k ∧
    IntervalIntegrable (fun t => coeff (w t) I k) volume 0 1 := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ compCube n) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hf : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      KAM.character (-k) (fun j => (p.2 j : ℂ)) * w p.1 (fun j => (p.2 j : ℂ), I))
      (Icc (0 : ℝ) 1 ×ˢ compCube n) :=
    (hchar.comp continuous_snd).continuousOn.mul hF
  have hint : Integrable (Function.uncurry fun (t : ℝ) (x : Fin n → ℝ) =>
      KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (compCube n))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.integrableOn_compact hK).mono_set
      (prod_mono Ioc_subset_Icc_self subset_rfl)
  have hswap := integral_integral_swap hint
  have e1 : coeff (fun z => ∫ t in (0 : ℝ)..1, w t z) I k =
      ∫ x in compCube n, ∫ t in Ioc (0 : ℝ) 1,
        KAM.character (-k) (fun j => (x j : ℂ)) * w t (fun j => (x j : ℂ), I) := by
    unfold coeff KAM.torusCoeffW KAM.torusAverage
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun x _ => ?_
    simp only [smul_eq_mul]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
  have e2 : ∀ t, coeff (w t) I k = ∫ x in compCube n,
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

/-- The integrand is jointly continuous in the time and the (real) angles. -/
theorem continuousOn_integrand (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {v : ℝ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => v p.1 p.2)
      (Icc 0 1 ×ˢ Dom n D r s)) {I : Fin n → ℂ} (hI : I ∈ polyNbhd D (r - ρ)) :
    ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      v p.1 (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega p.1 (fun j => (p.2 j : ℂ), I)))
      (Icc (0 : ℝ) 1 ×ˢ compCube n) := by
  obtain ⟨fc, -, -, -, -⟩ := flow_b hd.smallField
  have hdom := (composition_domain hd).2.2.2
  have hmem : ∀ x : Fin n → ℝ, ((fun j => (x j : ℂ)), I) ∈ Dom n D (r - ρ) (s - σ) := fun x =>
    ⟨KAM.ofReal_mem_complexStrip (by linarith [hd.hσs]) x, hI⟩
  have hP : ContinuousOn (fun p : ℝ × (Fin n → ℝ) => (p.1, ((fun j => (p.2 j : ℂ)), I)))
      (Icc (0 : ℝ) 1 ×ˢ compCube n) :=
    (continuous_fst.prodMk ((continuous_realPt.comp continuous_snd).prodMk
      continuous_const)).continuousOn
  have hPm : MapsTo (fun p : ℝ × (Fin n → ℝ) => (p.1, ((fun j => (p.2 j : ℂ)), I)))
      (Icc (0 : ℝ) 1 ×ˢ compCube n) (Icc (-1 : ℝ) 1 ×ˢ gaugeInterior hd.gauge hd.omega (1 / 2)) :=
    fun p hp => ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hd.gaugeInterior_half (hmem p.2)⟩
  have hΦ : ContinuousOn (fun p : ℝ × (Fin n → ℝ) =>
      (p.1, flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega p.1 (fun j => (p.2 j : ℂ), I)))
      (Icc (0 : ℝ) 1 ×ˢ compCube n) :=
    continuousOn_fst.prodMk (fc.comp hP hPm)
  refine hc.comp hΦ fun p hp => ⟨hp.1, hdom _ (hmem p.2) _ ⟨by linarith [hp.1.1], hp.1.2⟩⟩

/-- `bpN:p5:composition-integral`. -/
theorem composition_integral {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ V : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {v : ℝ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, InClass D r s (v t) ∧ WBound D r s (v t) V)
    (hc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => v p.1 p.2)
      (Icc 0 1 ×ˢ Dom n D r s))
    (hDc : ContinuousOn (fun p : ℝ × ((Fin n → ℂ) × (Fin n → ℂ)) => fderiv ℂ (v p.1) p.2)
      (Icc 0 1 ×ˢ Dom n D r s)) :
    InClass D (r - ρ) (s - σ)
      (fun z => ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) ∧
    WBound D (r - ρ) (s - σ)
      (fun z => ∫ t in (0 : ℝ)..1, v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z))
      ((1 - 2 * Φ / (ρ * σ))⁻¹ * V) := by
  refine ⟨integral_inClass hd (fun t ht => (hv t ht).1) hc hDc, ?_⟩
  by_cases hV : V < 0
  · exact wbound_of_neg (hv 0 ⟨le_rfl, zero_le_one⟩).2 hV (by linarith [hd.hρ])
  replace hV := not_lt.1 hV
  have hη := hd.eta_le
  have hη0 := hd.eta_nonneg
  have hpos : 0 < 1 - 2 * Φ / (ρ * σ) := by linarith
  -- each slice has weighted norm `≤ (1-η)⁻¹ V`
  have hslice : ∀ t ∈ Icc (0 : ℝ) 1, WBound D (r - ρ) (s - σ)
      (fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z))
      ((1 - 2 * Φ / (ρ * σ))⁻¹ * V) := fun t ht => by
    have h := (composition_t hd (hv t ht).1 (hv t ht).2 (t := t)
      ⟨by linarith [ht.1], ht.2⟩).2
    refine h.mono le_rfl le_rfl (mul_le_mul_of_nonneg_right (inv_anti₀ hpos ?_) hV)
    rw [abs_of_nonneg ht.1]
    nlinarith [ht.2]
  refine wbound_of_finset_le fun I hI Λ => ?_
  have hF := continuousOn_integrand hd hc hI
  have hw : ∀ k : Fin n → ℤ, 0 < modeWeight (s - σ) k := fun k => Real.exp_pos _
  have hcoef : ∀ k, coeff (fun z => ∫ t in (0 : ℝ)..1,
      v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) I k =
      ∫ t in (0 : ℝ)..1,
        coeff (fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) I k
      ∧ IntervalIntegrable (fun t => coeff (fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ)
        hd.omega t z)) I k) volume 0 1 := fun k =>
    coeff_integral (w := fun t z => v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) k hF
  calc ∑ k ∈ Λ, ‖coeff (fun z => ∫ t in (0 : ℝ)..1,
        v t (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) I k‖ * modeWeight (s - σ) k
      ≤ ∑ k ∈ Λ, (∫ t in (0 : ℝ)..1, ‖coeff (fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ)
          hd.omega t z)) I k‖) * modeWeight (s - σ) k := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (hw k).le
        rw [(hcoef k).1]
        exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ∫ t in (0 : ℝ)..1, ∑ k ∈ Λ, ‖coeff (fun z => v t (flow (KAM.hamiltonianVectorFieldℂ φ)
          hd.omega t z)) I k‖ * modeWeight (s - σ) k := by
        rw [intervalIntegral.integral_finsetSum fun k _ => ((hcoef k).2.norm).mul_const _]
        exact Finset.sum_congr rfl fun k _ => (intervalIntegral.integral_mul_const _ _).symm
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - 2 * Φ / (ρ * σ))⁻¹ * V := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (by
            have := IntervalIntegrable.sum Λ fun k _ => ((hcoef k).2.norm).mul_const
              (modeWeight (s - σ) k)
            simpa [Finset.sum_fn] using this)
          intervalIntegrable_const fun t ht => ?_
        obtain ⟨h1, h2⟩ := hslice t ht I hI
        exact (h1.sum_le_tsum Λ fun k _ => mul_nonneg (norm_nonneg _) (hw k).le).trans h2
    _ = (1 - 2 * Φ / (ρ * σ))⁻¹ * V := by simp

end KAM.Canonical

end
