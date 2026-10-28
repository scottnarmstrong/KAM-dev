/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.TransformSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Lie transform of `h + f₀` (`bpN:p5:transform`)

Blueprint-N Part 5, node `bpN:p5:transform` (design `docs/tracks/N/design/PART145-LEAN-DESIGN.md`,
package C5-9). For `ComposeData`, `h ∈ O(r, s)` of any norm, `w = {h, φ}` and `f₀ ∈ O(r, s)` of
finite norms `Mw`, `F₀`:

`(h + f₀) ∘ X¹_φ = h + {h, φ} + f₀ + 𝓡` on `𝒟_{r-ρ, s-σ}`,

`𝓡 = ∑_{j ≥ 1} (ad_φ^j w / (j+1)! + ad_φ^j f₀ / j!)`, the sum converging pointwise and in the
weighted norm, and `|𝓡|_{r-ρ,s-σ} ≤ η/(1-η) (Mw/2 + F₀)`.

* the series engine (class, bound, tails) is `Canonical/TransformSeries`;
* `KAM.Canonical.flow_series`, `integral_flow_hasSum`: `u ∘ X^t = ∑ t^j ad_φ^j u / j!` and its
  time integral (`series_eq` for `tφ`, `X^t_φ = X¹_{tφ}`, dominated convergence);
* `KAM.Canonical.transform`: the identities (`h ∘ X¹ = h + ∫₀¹ w ∘ X^t` by `taylor_lie`, `N = 1`;
  `f₀ ∘ X¹` by `series_eq`), and the integral form of `𝓡` from `taylor_poschel`.
-/

@[expose] public noncomputable section

open Set Metric Filter Finset MeasureTheory
open scoped Topology

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ Mw F₀ : ℝ}
  {φ h f₀ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- The remainder series of `bpN:p5:transform`,
`𝓡 = ∑_{j ≥ 1} (ad^j w / (j+1)! + ad^j f₀ / j!)` with `w = {h, φ}` (indexed by `i = j - 1`). -/
def liftRemainder (φ h f₀ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => ∑' i : ℕ, ((((i + 2).factorial : ℂ)⁻¹) * adPow φ (i + 1) (poissonBracket h φ) z +
    (((i + 1).factorial : ℂ)⁻¹) * adPow φ (i + 1) f₀ z)

theorem liftRemainder_eq_tsum (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    liftRemainder φ h f₀ z = ∑' i : ℕ, remTerm φ h f₀ i z := rfl

/-! ### Scaling `φ` -/

theorem poissonBracket_mul_mul (a b : ℂ) (u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    poissonBracket (fun z => a * u z) (fun z => b * v z) z = a * b * poissonBracket u v z := by
  simp only [poissonBracket, fderiv_fun_const_mul, smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem adPow_const_mul (c : ℂ) (j : ℕ) (u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    adPow (fun z => c * φ z) j u z = c ^ j * adPow φ j u z := by
  induction j generalizing z with
  | zero => simp [adPow]
  | succ j ih =>
    have e : adPow (fun z => c * φ z) j u = fun z => c ^ j * adPow φ j u z := funext ih
    show poissonBracket (adPow (fun z => c * φ z) j u) (fun z => c * φ z) z = _
    rw [e, poissonBracket_mul_mul, pow_succ]
    rfl

/-! ### `u ∘ X^t` as a Lie series -/

section Flow

variable (hd : ComposeData D r s r' s' ρ σ Φ φ) {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {U : ℝ}
  (hu : InClass D r s u) (hb : WBound D r s u U)
include hd hu hb

/-- `u ∘ X^t = ∑ t^j ad_φ^j u / j!` on `𝒟_{r-ρ, s-σ}`, `|t| ≤ 1`. -/
theorem flow_series {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z) =
      ∑' j : ℕ, (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * adPow φ j u z) := by
  have h1 := series_eq (hd.smul ht) hu hb hz
  rw [flow_smul hd ht hz] at h1
  rw [h1]
  exact tsum_congr fun j => by rw [adPow_const_mul]; ring

/-- The time integral of `u ∘ X^t`, `t ∈ [0, 1]`, termwise: `∑ ad_φ^j u / (j+1)!`. -/
theorem integral_flow_hasSum {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    HasSum (fun j : ℕ => ((j : ℂ) + 1)⁻¹ * (((j.factorial : ℂ)⁻¹) * adPow φ j u z))
      (∫ t in (0 : ℝ)..1, u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) := by
  have hterm := lieTerm_bound hd hu hb
  set q := Real.exp 1 * (2 * Φ / (ρ * σ)) / 4 with hq
  have hsum := lieSeries_summable (U := U) hd
  have hcb : ∀ j, ‖((j.factorial : ℂ)⁻¹) * adPow φ j u z‖ ≤ q ^ j * U := fun j =>
    sup_le_wbound (hterm j).1 (hterm j).2 z hz
  have hFb : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * adPow φ j u z)‖ ≤ q ^ j * U := fun j t ht => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc t ^ j * ‖((j.factorial : ℂ)⁻¹) * adPow φ j u z‖ ≤ 1 * ‖((j.factorial : ℂ)⁻¹) *
          adPow φ j u z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hcb j
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := (0 : ℝ)) (b := 1)
    (F := fun (j : ℕ) (t : ℝ) => (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * adPow φ j u z))
    (f := fun t => u (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z))
    (fun j _ => q ^ j * U)
    (fun j => ((Complex.continuous_ofReal.pow j).mul continuous_const).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact hFb j t ⟨ht.1.le, ht.2⟩)
    (Filter.Eventually.of_forall fun _ _ => hsum)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
      rw [flow_series hd hu hb ht' hz]
      exact (Summable.of_norm_bounded hsum fun j => hFb j t ⟨ht.1.le, ht.2⟩).hasSum)
  convert key using 1
  funext j
  have h1 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * adPow φ j u z) =
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ j) * (((j.factorial : ℂ)⁻¹) * adPow φ j u z) :=
    intervalIntegral.integral_mul_const _ _
  have h2 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ j = ((j : ℂ) + 1)⁻¹ := by
    have : ∀ t : ℝ, (t : ℂ) ^ j = ((t ^ j : ℝ) : ℂ) := fun t => by push_cast; rfl
    simp_rw [this]
    rw [intervalIntegral.integral_ofReal, integral_pow]
    simp
  rw [h1, h2]

end Flow

/-! ### The identity -/

section Identity

variable (hd : ComposeData D r s r' s' ρ σ Φ φ) (hh : InClass D r s h) (hf : InClass D r s f₀)
  (hw : WBound D r s (poissonBracket h φ) Mw) (hf₀ : WBound D r s f₀ F₀)
include hd hh hf hw hf₀

/-- On `𝒟_{r-ρ, s-σ}`: `h ∘ X¹ + f₀ ∘ X¹ = h + w + f₀ + V` with
`V = (∫₀¹ w ∘ X^t - w) + (f₀ ∘ X¹ - f₀)`, and `V` is the sum of the series of `𝓡`. -/
theorem transform_identity {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    HasSum (fun i : ℕ => remTerm φ h f₀ i z)
      (((∫ t in (0 : ℝ)..1, poissonBracket h φ
          (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) - poissonBracket h φ z) +
        (f₀ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) - f₀ z)) ∧
    h (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) =
      h z + ∫ t in (0 : ℝ)..1, poissonBracket h φ
        (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z) := by
  have hwc := hd.bracket_class hh
  have HW := integral_flow_hasSum hd hwc hw hz
  have HW1 := (hasSum_nat_add_iff' 1).2 HW
  have hsw : ∑ i ∈ range 1, ((i : ℂ) + 1)⁻¹ * (((i.factorial : ℂ)⁻¹) *
      adPow φ i (poissonBracket h φ) z) = poissonBracket h φ z := by simp [adPow]
  rw [hsw] at HW1
  have hsum := lieSeries_summable (U := F₀) hd
  have hterm := lieTerm_bound hd hf hf₀
  have hs' : Summable fun j : ℕ => ((j.factorial : ℂ)⁻¹) * adPow φ j f₀ z :=
    Summable.of_norm_bounded hsum fun j => sup_le_wbound (hterm j).1 (hterm j).2 z hz
  have HF := hs'.hasSum
  rw [← series_eq hd hf hf₀ hz] at HF
  have HF1 := (hasSum_nat_add_iff' 1).2 HF
  have hsf : ∑ i ∈ range 1, ((i.factorial : ℂ)⁻¹) * adPow φ i f₀ z = f₀ z := by simp [adPow]
  rw [hsf] at HF1
  have hA : (fun i : ℕ => ((((i + 1 : ℕ) : ℂ) + 1)⁻¹) * (((((i + 1).factorial : ℕ) : ℂ)⁻¹) *
      adPow φ (i + 1) (poissonBracket h φ) z)) =
      fun i : ℕ => (((i + 2).factorial : ℂ)⁻¹) * adPow φ (i + 1) (poissonBracket h φ) z := by
    funext i
    rw [Nat.factorial_succ (i + 1), Nat.cast_mul, mul_inv, ← mul_assoc,
      mul_comm (((i + 1 : ℕ) : ℂ) + 1)⁻¹]
    push_cast
    ring_nf
  rw [hA] at HW1
  refine ⟨HW1.add HF1, ?_⟩
  have hφd : DifferentiableOn ℂ φ hd.omega := hd.φ_class.differentiableOn.mono
    (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ]))
  have T := (taylor_lie (u := h) hφd hd.smallField (isOpen_Dom _ _ _)
    (Dom_mono (by linarith [hd.hr]) (by linarith [hd.hs])) hh.differentiableOn
    (hd.gaugeInterior_half hz) (fun t ht => (composition_domain hd).2.2.2 z hz t ht)
    (N := 1) le_rfl).1
  simpa [adPow] using T

end Identity

/-! ### The bounds, for arbitrary real `Mw`, `F₀` -/

section Bounds

variable (hd : ComposeData D r s r' s' ρ σ Φ φ) (hh : InClass D r s h) (hf : InClass D r s f₀)
  (hw : WBound D r s (poissonBracket h φ) Mw) (hf₀ : WBound D r s f₀ F₀)
include hd hh hf hw hf₀

/-- Both norm bounds of `𝓡`; a negative `Mw` or `F₀` makes them vacuous. -/
theorem remSeries_bounds :
    WBound D (r - ρ) (s - σ) (fun z => ∑' i, remTerm φ h f₀ i z)
      (∑' i, remBound Φ ρ σ Mw F₀ i) ∧
    WBound D (r - ρ) (s - σ) (fun z => ∑' i, remTerm φ h f₀ i z)
      ((2 * Φ / (ρ * σ)) / (1 - 2 * Φ / (ρ * σ)) * (Mw / 2 + F₀)) := by
  by_cases hM : 0 ≤ Mw
  · by_cases hF : 0 ≤ F₀
    · exact ⟨remSeries_bound hd hh hf hw hf₀ hM hF,
        (remSeries_bound hd hh hf hw hf₀ hM hF).mono le_rfl le_rfl (remBound_tsum_le hd hM hF)⟩
    · exact ⟨wbound_of_neg hf₀ (not_le.1 hF) (by linarith [hd.hρ]),
        wbound_of_neg hf₀ (not_le.1 hF) (by linarith [hd.hρ])⟩
  · exact ⟨wbound_of_neg hw (not_le.1 hM) (by linarith [hd.hρ]),
      wbound_of_neg hw (not_le.1 hM) (by linarith [hd.hρ])⟩

end Bounds

/-- `bpN:p5:transform` (`Canonical/Transform.lean`): `h` of any norm, `w = {h, φ}` and `f₀` of
finite norm `Mw`, `F₀` (`η = 2Φ/(ρσ)`). -/
theorem transform {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ Mw F₀ : ℝ}
    {φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hd : ComposeData D r s r' s' ρ σ Φ φ)
    {h f₀ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hh : InClass D r s h) (hf : InClass D r s f₀)
    (hw : WBound D r s (poissonBracket h φ) Mw) (hf₀ : WBound D r s f₀ F₀) :
    (∀ z ∈ Dom n D (r - ρ) (s - σ),
      h (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) +
        f₀ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) =
        h z + poissonBracket h φ z + f₀ z + liftRemainder φ h f₀ z) ∧
    (∀ z ∈ Dom n D (r - ρ) (s - σ), liftRemainder φ h f₀ z =
      ∫ t in (0 : ℝ)..1, poissonBracket
        (fun w => ((1 - t : ℝ) : ℂ) * poissonBracket h φ w + f₀ w) φ
        (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) ∧
    (∀ z ∈ Dom n D (r - ρ) (s - σ), HasSum (fun i : ℕ =>
      (((i + 2).factorial : ℂ)⁻¹) * adPow φ (i + 1) (poissonBracket h φ) z +
        (((i + 1).factorial : ℂ)⁻¹) * adPow φ (i + 1) f₀ z) (liftRemainder φ h f₀ z)) ∧
    InClass D (r - ρ) (s - σ) (liftRemainder φ h f₀) ∧
    WBound D (r - ρ) (s - σ) (liftRemainder φ h f₀)
      (∑' i : ℕ, (Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ (i + 1) * (Mw / ((i : ℝ) + 2) + F₀)) ∧
    WBound D (r - ρ) (s - σ) (liftRemainder φ h f₀)
      ((2 * Φ / (ρ * σ)) / (1 - 2 * Φ / (ρ * σ)) * (Mw / 2 + F₀)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N,
      WBound D (r - ρ) (s - σ)
        (fun z => liftRemainder φ h f₀ z - ∑ i ∈ Finset.range N',
          ((((i + 2).factorial : ℂ)⁻¹) * adPow φ (i + 1) (poissonBracket h φ) z +
            (((i + 1).factorial : ℂ)⁻¹) * adPow φ (i + 1) f₀ z)) ε) := by
  have hM : 0 ≤ max Mw 0 := le_max_right _ _
  have hF : 0 ≤ max F₀ 0 := le_max_right _ _
  have hw' := hw.mono le_rfl le_rfl (le_max_left Mw 0)
  have hf' := hf₀.mono le_rfl le_rfl (le_max_left F₀ 0)
  have hHS : ∀ z ∈ Dom n D (r - ρ) (s - σ), HasSum (fun i : ℕ => remTerm φ h f₀ i z)
      (liftRemainder φ h f₀ z) := fun z hz =>
    (liftRemainder_eq_tsum z).symm ▸ (transform_identity hd hh hf hw hf₀ hz).1.summable.hasSum
  have hV : ∀ z ∈ Dom n D (r - ρ) (s - σ), liftRemainder φ h f₀ z =
      ((∫ t in (0 : ℝ)..1, poissonBracket h φ
          (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega t z)) - poissonBracket h φ z) +
        (f₀ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) - f₀ z) := fun z hz =>
    ((hHS z hz).unique (transform_identity hd hh hf hw hf₀ hz).1)
  have hC1 : ∀ z ∈ Dom n D (r - ρ) (s - σ),
      h (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) +
        f₀ (flow (KAM.hamiltonianVectorFieldℂ φ) hd.omega 1 z) =
        h z + poissonBracket h φ z + f₀ z + liftRemainder φ h f₀ z := fun z hz => by
    rw [hV z hz, (transform_identity hd hh hf hw hf₀ hz).2]
    ring
  refine ⟨hC1, fun z hz => ?_, hHS, remSeries_class hd hh hf hw' hf' hM hF, ?_⟩
  · have hφd : DifferentiableOn ℂ φ hd.omega := hd.φ_class.differentiableOn.mono
      (Dom_mono (by linarith [hd.hρ]) (by linarith [hd.hσ]))
    have T := taylor_poschel hφd hd.smallField (isOpen_Dom _ _ _)
      (Dom_mono (by linarith [hd.hr]) (by linarith [hd.hs])) hh.differentiableOn hf.differentiableOn
      (hd.gaugeInterior_half hz) (fun t ht => (composition_domain hd).2.2.2 z hz t ht)
    have := hC1 z hz
    rw [T] at this
    exact (add_left_cancel (a := h z + poissonBracket h φ z + f₀ z) this).symm
  · obtain ⟨b1, b2⟩ := remSeries_bounds hd hh hf hw hf₀
    exact ⟨b1, b2, remSeries_tail hd hh hf hw' hf' hM hF⟩

end KAM.Canonical

end
