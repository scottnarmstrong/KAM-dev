/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.Holomorphic
public import KAM.Planetary.Poincare.Lattice

/-!
# The total chart (P11A-P2, `bpP:p11:total-chart`)

The period-one polar chart `p11PolarC` (complex) and `p11PolarR` (its real restriction), and the
lattice compatibility `total_chart` and `total_chart_transport`. The real chart is the existing
Part 7 polar map `polarMap` conjugated by the canonical period conversion `(ζ, ρ) ↦ (2πζ, ρ/2π)`
on the slow block (`tc-polar`); lattice compatibility is the existing `polarMap_shift` and
`polarMap_eq_shift`, applied after a translation of the fast actions, which `polarMap` commutes
with, so that its `polarDom` hypotheses hold (`tc-lat`).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ComplexOrder
namespace KAM.Planetary

section PolarChart

variable {n : ℕ}

/-- Canonical polar chart in period one; no new real polar representation. -/
def p11PolarC {n : ℕ} (z : P11Phase (n+n)) : P11Phase (n+n) :=
  (Fin.append (fun i : Fin n => z.1 (Fin.castAdd n i))
    (fun i : Fin n => Complex.sqrt (z.2 (Fin.natAdd n i)/Real.pi)*
      Complex.sin (2*Real.pi*z.1 (Fin.natAdd n i))),
   Fin.append (fun i : Fin n => z.2 (Fin.castAdd n i))
    (fun i : Fin n => Complex.sqrt (z.2 (Fin.natAdd n i)/Real.pi)*
      Complex.cos (2*Real.pi*z.1 (Fin.natAdd n i))))
def p11PolarR {n : ℕ} (z : Phase (n+n)) : Phase (n+n) :=
  ((fun i => (p11PolarC (KAM.realInclusion₂ (n+n) z)).1 i |>.re),
   (fun i => (p11PolarC (KAM.realInclusion₂ (n+n) z)).2 i |>.re))

/-- Translation of the fast actions. -/
private def polTrans (c : Fin n → ℝ) : Phase (n + n) := (0, Fin.append c 0)

private theorem fastShift_zero : fastShift (a := n) (b := n) (0 : Fin n → ℤ) = 0 := by
  refine Prod.ext ?_ rfl
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [fastShift]

private theorem polarMap_add_trans (c : Fin n → ℝ) (z : Phase (n + n)) :
    polarMap (z + polTrans c) = polarMap z + polTrans c := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [polarMap, assemble, polTrans, fast, slow, Fin.append_left]

private theorem polarMap_eq_comp_trans (c : Fin n → ℝ) :
    (polarMap : Phase (n + n) → Phase (n + n)) =
      fun w => polarMap (w + polTrans c) - polTrans c := by
  funext w
  rw [polarMap_add_trans, add_sub_cancel_right]

/-- Translating both points by the same fast actions puts them into `polarDom`. -/
private theorem exists_trans {z z' : Phase (n + n)} (hz : ∀ i, 0 < slow z.2 i)
    (hz' : ∀ i, 0 < slow z'.2 i) :
    ∃ c : Fin n → ℝ, z + polTrans c ∈ polarDom n ∧ z' + polTrans c ∈ polarDom n := by
  refine ⟨fun i => |fast z.2 i| + |fast z'.2 i| + slow z.2 i + slow z'.2 i + 1,
    fun i => ?_, fun i => ?_⟩ <;>
  · have h1 := abs_nonneg (fast z.2 i)
    have h2 := abs_nonneg (fast z'.2 i)
    have h3 := neg_abs_le (fast z.2 i)
    have h4 := neg_abs_le (fast z'.2 i)
    have h5 := hz i
    have h6 := hz' i
    simp only [polTrans, fast, slow, Prod.snd_add, Pi.add_apply, Fin.append_left,
      Fin.append_right, Pi.zero_apply, add_zero] at *
    refine ⟨?_, ?_, ?_⟩ <;> linarith

private theorem polarMap_analyticAt {z : Phase (n + n)} (hz : ∀ i, 0 < slow z.2 i) :
    AnalyticAt ℝ (polarMap : Phase (n + n) → Phase (n + n)) z := by
  obtain ⟨c, hc, -⟩ := exists_trans hz hz
  rw [polarMap_eq_comp_trans c]
  have h : AnalyticAt ℝ (polarMap : Phase (n + n) → Phase (n + n)) (z + polTrans c) :=
    analyticOnNhd_polarMap n _ hc
  exact (AnalyticAt.comp (f := fun w : Phase (n + n) => w + polTrans c) h
    (analyticAt_id.add analyticAt_const)).sub analyticAt_const

private theorem fderiv_polarMap_eq (c : Fin n → ℝ) (z : Phase (n + n)) :
    fderiv ℝ (polarMap : Phase (n + n) → Phase (n + n)) z =
      fderiv ℝ (polarMap : Phase (n + n) → Phase (n + n)) (z + polTrans c) := by
  conv_lhs => rw [polarMap_eq_comp_trans c]
  rw [fderiv_sub_const, fderiv_comp_add_right]

private theorem polarMap_symplectic_pos {z : Phase (n + n)} (hz : ∀ i, 0 < slow z.2 i) :
    ∀ u v : Phase (n + n), KAM.symplecticForm (fderiv ℝ polarMap z u) (fderiv ℝ polarMap z v) =
      1 * KAM.symplecticForm u v := by
  obtain ⟨c, hc, -⟩ := exists_trans hz hz
  rw [fderiv_polarMap_eq c]
  exact polarMap_symplectic n _ hc

/-- The canonical period conversion `(ζ, ρ) ↦ (2πζ, ρ/2π)` on the slow block. -/
def p11PolarScaleL : Phase (n + n) →ₗ[ℝ] Phase (n + n) where
  toFun z := (Fin.append (fast z.1) ((2 * Real.pi) • slow z.1),
    Fin.append (fast z.2) ((2 * Real.pi)⁻¹ • slow z.2))
  map_add' u v := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [fast, slow, mul_add]
  map_smul' c u := by
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [fast, slow, mul_left_comm]

def p11PolarScale : Phase (n + n) →L[ℝ] Phase (n + n) :=
  LinearMap.toContinuousLinearMap p11PolarScaleL

theorem p11PolarScale_apply (z : Phase (n + n)) :
    p11PolarScale z = (Fin.append (fast z.1) ((2 * Real.pi) • slow z.1),
      Fin.append (fast z.2) ((2 * Real.pi)⁻¹ • slow z.2)) := rfl

private theorem p11PolarScale_symplectic (u v : Phase (n + n)) :
    KAM.symplecticForm (p11PolarScale u) (p11PolarScale v) = KAM.symplecticForm u v := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [p11PolarScale_apply, KAM.symplecticForm, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_)
    (Finset.sum_congr rfl fun i _ => ?_)
  · simp [fast]
  · simp [slow]
    field_simp

private theorem p11PolarScale_slow_pos {z : Phase (n + n)}
    (hz : ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)) (i : Fin n) : 0 < slow (p11PolarScale z).2 i := by
  simp only [p11PolarScale_apply, slow, Fin.append_right, Pi.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.2 (by positivity)) (hz i)

private theorem re_sqrt_mul_sin {ρ ζ : ℝ} (hρ : 0 < ρ) :
    ((Complex.sqrt ((ρ : ℂ) / (Real.pi : ℂ)) * Complex.sin (2 * (Real.pi : ℂ) * (ζ : ℂ))).re) =
      √(2 * ((2 * Real.pi)⁻¹ * ρ)) * Real.sin (2 * Real.pi * ζ) := by
  have h0 : (0 : ℂ) ≤ ((ρ / Real.pi : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; exact (div_pos hρ Real.pi_pos).le
  have hs := Complex.sqrt_of_nonneg h0
  have e1 : (ρ : ℂ) / (Real.pi : ℂ) = ((ρ / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  have e2 : Complex.sin (2 * (Real.pi : ℂ) * (ζ : ℂ)) = ((Real.sin (2 * Real.pi * ζ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sin]; push_cast; rfl
  have e3 : 2 * ((2 * Real.pi)⁻¹ * ρ) = ρ / Real.pi := by field_simp
  rw [e1, hs, e2, e3, Complex.ofReal_re]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

private theorem re_sqrt_mul_cos {ρ ζ : ℝ} (hρ : 0 < ρ) :
    ((Complex.sqrt ((ρ : ℂ) / (Real.pi : ℂ)) * Complex.cos (2 * (Real.pi : ℂ) * (ζ : ℂ))).re) =
      √(2 * ((2 * Real.pi)⁻¹ * ρ)) * Real.cos (2 * Real.pi * ζ) := by
  have h0 : (0 : ℂ) ≤ ((ρ / Real.pi : ℝ) : ℂ) := by
    rw [Complex.zero_le_real]; exact (div_pos hρ Real.pi_pos).le
  have hs := Complex.sqrt_of_nonneg h0
  have e1 : (ρ : ℂ) / (Real.pi : ℂ) = ((ρ / Real.pi : ℝ) : ℂ) := by push_cast; rfl
  have e2 : Complex.cos (2 * (Real.pi : ℂ) * (ζ : ℂ)) = ((Real.cos (2 * Real.pi * ζ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cos]; push_cast; rfl
  have e3 : 2 * ((2 * Real.pi)⁻¹ * ρ) = ρ / Real.pi := by field_simp
  rw [e1, hs, e2, e3, Complex.ofReal_re]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- `tc-polar`: the real polar chart is the Part 7 polar map after the period conversion. -/
theorem p11PolarR_eq {z : Phase (n + n)} (hz : ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)) :
    p11PolarR z = polarMap (p11PolarScale z) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [p11PolarR, p11PolarC, polarMap, p11PolarScale_apply, assemble, fast, slow]
  · simp only [p11PolarR, p11PolarC, polarMap, p11PolarScale_apply, assemble, slow,
      Fin.append_right, Pi.smul_apply, smul_eq_mul, KAM.realInclusion₂_apply,
      KAM.realInclusion_apply]
    exact re_sqrt_mul_sin (hz i)
  · simp [p11PolarR, p11PolarC, polarMap, p11PolarScale_apply, assemble, fast, slow]
  · simp only [p11PolarR, p11PolarC, polarMap, p11PolarScale_apply, assemble, slow,
      Fin.append_right, Pi.smul_apply, smul_eq_mul, KAM.realInclusion₂_apply,
      KAM.realInclusion_apply]
    exact re_sqrt_mul_cos (hz i)

private theorem isOpen_pos :
    IsOpen {z : Phase (n + n) | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)} := by
  have : {z : Phase (n + n) | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)} =
      ⋂ i : Fin n, {z : Phase (n + n) | 0 < z.2 (Fin.natAdd n i)} := by ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)

private theorem p11PolarScale_shift (z : Phase (n + n)) (k : Fin n → ℤ) :
    p11PolarScale (z.1 + Fin.append 0 (fun i => (k i : ℝ)), z.2) =
      p11PolarScale z + fullShift (Fin.append (0 : Fin n → ℤ) k) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [p11PolarScale_apply, fullShift, fast, slow, mul_add]

theorem total_chart {n : ℕ} :
    let O : Set (Phase (n+n)) := {z | ∀ i : Fin n, 0 < z.2 (Fin.natAdd n i)}
    AnalyticOnNhd ℝ p11PolarR O ∧ KAM.Kepler.IsSymplecticOn 1 p11PolarR O ∧
    (∀ z ∈ O, ∀ k : Fin n → ℤ,
      p11PolarR (z.1+Fin.append 0 (fun i => (k i : ℝ)),z.2)=p11PolarR z) ∧
    ∀ z ∈ O, ∀ z' ∈ O, p11PolarR z=p11PolarR z' →
      ∃ k : Fin n → ℤ, z'=(z.1+Fin.append 0 (fun i => (k i : ℝ)),z.2) := by
  intro O
  have hO : IsOpen O := isOpen_pos
  have hev : ∀ z ∈ O, (polarMap ∘ p11PolarScale : Phase (n + n) → Phase (n + n)) =ᶠ[𝓝 z]
      p11PolarR := fun z hz =>
    Filter.eventuallyEq_of_mem (hO.mem_nhds hz) fun w hw => (p11PolarR_eq hw).symm
  have han : AnalyticOnNhd ℝ p11PolarR O := fun z hz =>
    ((polarMap_analyticAt (p11PolarScale_slow_pos hz)).comp
      (p11PolarScale.analyticAt z)).congr (hev z hz)
  refine ⟨han, fun z hz u v => ?_, fun z hz k => ?_, fun z hz z' hz' h => ?_⟩
  · have hd : fderiv ℝ p11PolarR z = (fderiv ℝ polarMap (p11PolarScale z)).comp p11PolarScale := by
      rw [← Filter.EventuallyEq.fderiv_eq (hev z hz)]
      exact fderiv_comp z ((polarMap_analyticAt (p11PolarScale_slow_pos hz)).differentiableAt)
        p11PolarScale.differentiableAt |>.trans (by rw [p11PolarScale.fderiv])
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply]
    rw [polarMap_symplectic_pos (p11PolarScale_slow_pos hz), p11PolarScale_symplectic]
  · have hz2 : (z.1 + Fin.append 0 (fun i => (k i : ℝ)), z.2) ∈ O := hz
    rw [p11PolarR_eq hz2, p11PolarR_eq hz, p11PolarScale_shift, polarMap_shift]
    have h0 : (fun i : Fin n => (Fin.append (0 : Fin n → ℤ) k) (Fin.castAdd n i)) = 0 := by
      funext i; simp
    rw [h0, fastShift_zero, add_zero]
  · rw [p11PolarR_eq hz, p11PolarR_eq hz'] at h
    obtain ⟨c, hc, hc'⟩ := exists_trans (p11PolarScale_slow_pos hz) (p11PolarScale_slow_pos hz')
    have hf0 := fastShift_zero (n := n)
    have h2 : polarMap (p11PolarScale z' + polTrans c) =
        polarMap (p11PolarScale z + polTrans c) + fastShift (a := n) (b := n) (0 : Fin n → ℤ) := by
      rw [polarMap_add_trans, polarMap_add_trans, ← h, hf0, add_zero]
    obtain ⟨k, hk⟩ := polarMap_eq_shift hc hc' h2
    rw [add_right_comm] at hk
    have hk' := add_right_cancel hk
    have hφ : ∀ i : Fin n, z'.1 (Fin.castAdd n i) = z.1 (Fin.castAdd n i) := fun i => by
      have := congrArg (fun w : Phase (n + n) => w.1 (Fin.castAdd n i)) h
      simpa [polarMap, assemble, p11PolarScale_apply, fast, Fin.append_left] using this.symm
    have hψ : ∀ i : Fin n,
        z'.1 (Fin.natAdd n i) = z.1 (Fin.natAdd n i) + (k (Fin.natAdd n i) : ℝ) := by
      intro i
      have := congrArg (fun w : Phase (n + n) => w.1 (Fin.natAdd n i)) hk'
      simp only [p11PolarScale_apply, fullShift, Prod.fst_add, Pi.add_apply, slow,
        Fin.append_right, Pi.smul_apply, smul_eq_mul] at this
      have h2pi : (2 * Real.pi) ≠ 0 := by positivity
      refine mul_left_cancel₀ h2pi ?_
      linarith
    have hI : ∀ j, z'.2 j = z.2 j := fun j => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · have := congrArg (fun w : Phase (n + n) => w.2 (Fin.castAdd n i)) hk'
        simpa [p11PolarScale_apply, fullShift, fast, Fin.append_left] using this
      · have := congrArg (fun w : Phase (n + n) => w.2 (Fin.natAdd n i)) hk'
        simp only [p11PolarScale_apply, fullShift, Prod.snd_add, Pi.add_apply, slow,
          Fin.append_right, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at this
        exact mul_left_cancel₀ (inv_ne_zero (by positivity)) this
    refine ⟨fun i => k (Fin.natAdd n i), Prod.ext (funext fun j => ?_) (funext hI)⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa using hφ i
    · simpa using hψ i

end PolarChart

end KAM.Planetary

end
