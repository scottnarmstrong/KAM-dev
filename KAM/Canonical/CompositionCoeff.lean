/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Coefficients
public import KAM.Weighted.SupWeighted
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coefficient bookkeeping for the composition estimates (`bpN:p5:composition`, helpers)

Package C5-8 (design `docs/tracks/N/design/PART145-LEAN-DESIGN.md`). Scalar functions on
`ℂⁿ × ℂⁿ` (angles and actions of equal dimension `n`).

* `KAM.Canonical.coeff_congr`, `wbound_congr`, `inClass_congr`: the class, the coefficients and the
  weighted bound only see the values on `𝒟_{r,s}` (for `0 < s`);
* `KAM.Canonical.wbound_of_finset_le`: the weighted bound from the bounds of the finite partial
  sums;
* `KAM.Canonical.hasSum_coeff`: coefficients commute with a uniformly dominated series;
* `KAM.Canonical.wbound_tsum`: a series of class members with summable weighted bounds is in the
  class with the summed bound (the series is the sum of the functions, pointwise on `𝒟_{r,s}`).
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s : ℝ}

private theorem realPt_mem {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) {I : Fin n → ℂ}
    (hI : I ∈ polyNbhd D r) : ((fun j => (x j : ℂ)), I) ∈ Dom n D r s :=
  ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

private theorem continuous_realPt : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

private abbrev cube (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Icc (0 : ℝ) 1

/-- The coefficients only see the values on `𝒟_{r,s}`. -/
theorem coeff_congr (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (h : EqOn u v (Dom n D r s)) {I : Fin n → ℂ} (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    coeff u I k = coeff v I k := by
  unfold coeff
  congr 2
  funext x
  rw [h (realPt_mem hs x hI)]

theorem wbound_congr (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {M : ℝ}
    (h : EqOn u v (Dom n D r s)) (hb : WBound D r s u M) : WBound D r s v M := by
  intro I hI
  obtain ⟨h1, h2⟩ := hb I hI
  have hc := coeff_congr hs h hI
  refine ⟨?_, ?_⟩
  · simpa only [WSummable, ← hc] using h1
  · simpa only [wsum, ← hc] using h2

theorem inClass_congr {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (h : EqOn u v (Dom n D r s))
    (hu : InClass D r s u) : InClass D r s v := by
  refine ⟨hu.differentiableOn.congr fun x hx => (h hx).symm, fun j z hz => ?_⟩
  have hz' : (z.1 + Pi.single j 1, z.2) ∈ Dom n D r s := by
    refine ⟨fun i => ?_, hz.2⟩
    have := hz.1 i
    simpa [Pi.single_apply, apply_ite Complex.im] using this
  rw [← h hz', ← h hz]
  exact hu.periodic j z hz

/-- The weighted bound from the bounds of all finite partial sums of the coefficient series. -/
theorem wbound_of_finset_le {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {B : ℝ}
    (h : ∀ I ∈ polyNbhd D r, ∀ Λ : Finset (Fin n → ℤ),
      ∑ k ∈ Λ, ‖coeff u I k‖ * modeWeight s k ≤ B) : WBound D r s u B := fun I hI =>
  have hnn : 0 ≤ fun k : Fin n → ℤ => ‖coeff u I k‖ * modeWeight s k := fun _ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hsum : WSummable u s I := summable_of_sum_le hnn (h I hI)
  ⟨hsum, hsum.tsum_le_of_sum_le (h I hI)⟩

/-- Coefficients commute with a uniformly dominated series. -/
theorem hasSum_coeff (hs : 0 < s) {g : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {T : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {b : ℕ → ℝ} (hg : ∀ j, InClass D r s (g j))
    (hbd : ∀ j, ∀ z ∈ Dom n D r s, ‖g j z‖ ≤ b j) (hb : Summable b)
    (hT : ∀ z ∈ Dom n D r s, HasSum (fun j => g j z) (T z)) {I : Fin n → ℂ}
    (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    HasSum (fun j => coeff (g j) I k) (coeff T I k) := by
  have : IsFiniteMeasure (volume.restrict (cube n)) :=
    ⟨by rw [Measure.restrict_apply_univ, KAM.volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt
  have hcont : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun j => (x j : ℂ), I) := fun j =>
    (hg j).differentiableOn.continuousOn.comp_continuous (continuous_realPt.prodMk continuous_const)
      fun x => realPt_mem hs x hI
  have := hasSum_integral_of_dominated_convergence (μ := volume.restrict (cube n))
    (F := fun j x => KAM.character (-k) (fun j => (x j : ℂ)) • g j (fun j => (x j : ℂ), I))
    (f := fun x => KAM.character (-k) (fun j => (x j : ℂ)) • T (fun j => (x j : ℂ), I))
    (fun j _ => b j)
    (fun j => (hchar.smul (hcont j)).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall fun x => by
      rw [norm_smul, KAM.norm_character_real, one_mul]
      exact hbd j _ (realPt_mem hs x hI))
    (Filter.Eventually.of_forall fun _ => hb)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x => (hT _ (realPt_mem hs x hI)).const_smul _)
  exact this

/-- A series of class members, with summable weighted bounds, is in the class with the summed
weighted bound. -/
theorem wbound_tsum (hs : 0 < s) {g : ℕ → (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {b : ℕ → ℝ}
    (hg : ∀ j, InClass D r s (g j)) (hgb : ∀ j, WBound D r s (g j) (b j)) (hb : Summable b) :
    WBound D r s (fun z => ∑' j, g j z) (∑' j, b j) := by
  have hbd : ∀ j, ∀ z ∈ Dom n D r s, ‖g j z‖ ≤ b j := fun j => sup_le_wbound (hg j) (hgb j)
  have hT : ∀ z ∈ Dom n D r s, HasSum (fun j => g j z) (∑' j, g j z) := fun z hz =>
    (Summable.of_norm_bounded hb fun j => hbd j z hz).hasSum
  refine wbound_of_finset_le fun I hI Λ => ?_
  have hw : ∀ k : Fin n → ℤ, 0 < modeWeight s k := fun k => Real.exp_pos _
  -- each coefficient series is absolutely summable
  have hsumk : ∀ k, Summable fun j => ‖coeff (g j) I k‖ := fun k => by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      (hb.mul_right (modeWeight s k)⁻¹)
    have h1 := (hgb j I hI).1.le_tsum k (fun _ _ => mul_nonneg (norm_nonneg _) (hw _).le)
    have h2 := h1.trans (hgb j I hI).2
    rw [← div_eq_mul_inv, le_div_iff₀ (hw k)]
    exact h2
  have hnorm : ∀ k, ‖coeff (fun z => ∑' j, g j z) I k‖ ≤ ∑' j, ‖coeff (g j) I k‖ := fun k => by
    rw [← (hasSum_coeff hs hg hbd hb hT hI k).tsum_eq]
    exact norm_tsum_le_tsum_norm (hsumk k)
  have hterm : ∀ k, Summable fun j => ‖coeff (g j) I k‖ * modeWeight s k := fun k =>
    (hsumk k).mul_right _
  calc ∑ k ∈ Λ, ‖coeff (fun z => ∑' j, g j z) I k‖ * modeWeight s k
      ≤ ∑ k ∈ Λ, (∑' j, ‖coeff (g j) I k‖) * modeWeight s k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hnorm k) (hw k).le
    _ = ∑ k ∈ Λ, ∑' j, ‖coeff (g j) I k‖ * modeWeight s k :=
        Finset.sum_congr rfl fun k _ => (tsum_mul_right).symm
    _ = ∑' j, ∑ k ∈ Λ, ‖coeff (g j) I k‖ * modeWeight s k :=
        (Summable.tsum_finsetSum fun k _ => hterm k).symm
    _ ≤ ∑' j, b j := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun k _ => hterm k) hb
        exact ((hgb j I hI).1.sum_le_tsum Λ (fun k _ => mul_nonneg (norm_nonneg _) (hw k).le)).trans
          (hgb j I hI).2

end KAM.Canonical

end
