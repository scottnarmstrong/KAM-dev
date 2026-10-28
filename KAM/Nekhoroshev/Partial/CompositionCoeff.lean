/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Coefficients
public import KAM.Weighted.SupWeighted
public import KAM.Weighted.Parametric
public import KAM.Strip.Bridges
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Coefficient bookkeeping for the extended composition (Part 11, package N11-F1, helpers)

Independent-dimension versions (angles `Fin n`, actions `Fin m`) of the Part 5 helpers of
`KAM.Canonical.CompositionCoeff`/`TransformSeries`: the class, the coefficients and the weighted
bound only see the values on `𝒟_{r,s}`; the weighted norm is subadditive and homogeneous; a series
of class members with summable weighted bounds is in the class with the summed bound.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}

theorem realPt_mem_ext {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) : ((fun j => (x j : ℂ)), I) ∈ Dom n D r s :=
  ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

theorem continuous_realPt_ext : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-- The coefficients only see the values on `𝒟_{r,s}`. -/
theorem coeff_congr_ext (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (h : EqOn u v (Dom n D r s)) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    coeff u I k = coeff v I k := by
  unfold coeff
  congr 2
  funext x
  rw [h (realPt_mem_ext hs x hI)]

theorem wbound_congr_ext (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} {M : ℝ}
    (h : EqOn u v (Dom n D r s)) (hb : WBound D r s u M) : WBound D r s v M := by
  intro I hI
  obtain ⟨h1, h2⟩ := hb I hI
  have hc := coeff_congr_ext hs h hI
  refine ⟨?_, ?_⟩
  · simpa only [WSummable, ← hc] using h1
  · simpa only [wsum, ← hc] using h2

theorem inClass_congr_ext {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (h : EqOn u v (Dom n D r s))
    (hu : InClass D r s u) : InClass D r s v := by
  refine ⟨hu.differentiableOn.congr fun x hx => (h hx).symm, fun j z hz => ?_⟩
  have hz' : (z.1 + Pi.single j 1, z.2) ∈ Dom n D r s := by
    refine ⟨fun i => ?_, hz.2⟩
    have := hz.1 i
    simpa [Pi.single_apply, apply_ite Complex.im] using this
  rw [← h hz', ← h hz]
  exact hu.periodic j z hz

/-- The weighted bound from the bounds of all finite partial sums of the coefficient series. -/
theorem wbound_of_finset_le_ext {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} {B : ℝ}
    (h : ∀ I ∈ polyNbhd D r, ∀ Λ : Finset (Fin n → ℤ),
      ∑ k ∈ Λ, ‖coeff u I k‖ * modeWeight s k ≤ B) : WBound D r s u B := fun I hI =>
  have hnn : 0 ≤ fun k : Fin n → ℤ => ‖coeff u I k‖ * modeWeight s k := fun _ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hsum : WSummable u s I := summable_of_sum_le hnn (h I hI)
  ⟨hsum, hsum.tsum_le_of_sum_le (h I hI)⟩

/-- A negative bound is vacuous when some action is admitted. -/
theorem wbound_of_neg_ext {r₀ r₁ s₀ s₁ M M' : ℝ} {v w : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hb : WBound D r₀ s₀ v M) (hM : M < 0) (hr : r₁ ≤ r₀) : WBound D r₁ s₁ w M' := by
  intro I hI
  obtain ⟨-, h2⟩ := hb I (polyNbhd_mono hr hI)
  have : 0 ≤ wsum v s₀ I :=
    tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  linarith

/-- Coefficients commute with a uniformly dominated series. -/
theorem hasSum_coeff_ext (hs : 0 < s) {g : ℕ → (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    {T : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} {b : ℕ → ℝ} (hg : ∀ j, InClass D r s (g j))
    (hbd : ∀ j, ∀ z ∈ Dom n D r s, ‖g j z‖ ≤ b j) (hb : Summable b)
    (hT : ∀ z ∈ Dom n D r s, HasSum (fun j => g j z) (T z)) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    HasSum (fun j => coeff (g j) I k) (coeff T I k) := by
  have : IsFiniteMeasure
      (volume.restrict (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, KAM.volume_unitCube]; exact ENNReal.one_lt_top⟩
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt_ext
  have hcont : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun j => (x j : ℂ), I) := fun j =>
    (hg j).differentiableOn.continuousOn.comp_continuous
      (continuous_realPt_ext.prodMk continuous_const) fun x => realPt_mem_ext hs x hI
  exact hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Set.pi Set.univ fun _ : Fin n => Icc (0 : ℝ) 1))
    (F := fun j x => KAM.character (-k) (fun j => (x j : ℂ)) • g j (fun j => (x j : ℂ), I))
    (f := fun x => KAM.character (-k) (fun j => (x j : ℂ)) • T (fun j => (x j : ℂ), I))
    (fun j _ => b j)
    (fun j => (hchar.smul (hcont j)).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall fun x => by
      rw [norm_smul, KAM.norm_character_real, one_mul]
      exact hbd j _ (realPt_mem_ext hs x hI))
    (Filter.Eventually.of_forall fun _ => hb)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x => (hT _ (realPt_mem_ext hs x hI)).const_smul _)

/-- A series of class members, with summable weighted bounds, is in the class with the summed
weighted bound. -/
theorem wbound_tsum_ext (hs : 0 < s) {g : ℕ → (Fin n → ℂ) × (Fin m → ℂ) → ℂ} {b : ℕ → ℝ}
    (hg : ∀ j, InClass D r s (g j)) (hgb : ∀ j, WBound D r s (g j) (b j)) (hb : Summable b) :
    WBound D r s (fun z => ∑' j, g j z) (∑' j, b j) := by
  have hbd : ∀ j, ∀ z ∈ Dom n D r s, ‖g j z‖ ≤ b j := fun j => sup_le_wbound (hg j) (hgb j)
  have hT : ∀ z ∈ Dom n D r s, HasSum (fun j => g j z) (∑' j, g j z) := fun z hz =>
    (Summable.of_norm_bounded hb fun j => hbd j z hz).hasSum
  refine wbound_of_finset_le_ext fun I hI Λ => ?_
  have hw : ∀ k : Fin n → ℤ, 0 < modeWeight s k := fun k => Real.exp_pos _
  have hsumk : ∀ k, Summable fun j => ‖coeff (g j) I k‖ := fun k => by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      (hb.mul_right (modeWeight s k)⁻¹)
    have h1 := (hgb j I hI).1.le_tsum k (fun _ _ => mul_nonneg (norm_nonneg _) (hw _).le)
    have h2 := h1.trans (hgb j I hI).2
    rw [← div_eq_mul_inv, le_div_iff₀ (hw k)]
    exact h2
  have hnorm : ∀ k, ‖coeff (fun z => ∑' j, g j z) I k‖ ≤ ∑' j, ‖coeff (g j) I k‖ := fun k => by
    rw [← (hasSum_coeff_ext hs hg hbd hb hT hI k).tsum_eq]
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
        exact ((hgb j I hI).1.sum_le_tsum Λ
          (fun k _ => mul_nonneg (norm_nonneg _) (hw k).le)).trans (hgb j I hI).2

/-- The coefficient of a sum of class members is the sum of the coefficients. -/
theorem coeff_add_ext (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hu : InClass D r s u) (hv : InClass D r s v) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r)
    (k : Fin n → ℤ) : coeff (fun z => u z + v z) I k = coeff u I k + coeff v I k := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt_ext
  have hcont : ∀ w : (Fin n → ℂ) × (Fin m → ℂ) → ℂ, InClass D r s w →
      Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) •
        w (fun j => (x j : ℂ), I) := fun w hw =>
    hchar.smul (hw.differentiableOn.continuousOn.comp_continuous
      (continuous_realPt_ext.prodMk continuous_const) fun x => realPt_mem_ext hs x hI)
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  simp only [smul_add]
  exact integral_add (KAM.integrableOn_unitCube_of_continuous (hcont u hu))
    (KAM.integrableOn_unitCube_of_continuous (hcont v hv))

/-- Subadditivity of the weighted norm. -/
theorem wbound_add_ext (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} {M N : ℝ}
    (hu : InClass D r s u) (hv : InClass D r s v) (hbu : WBound D r s u M)
    (hbv : WBound D r s v N) : WBound D r s (fun z => u z + v z) (M + N) := by
  intro I hI
  obtain ⟨hu1, hu2⟩ := hbu I hI
  obtain ⟨hv1, hv2⟩ := hbv I hI
  have hw : ∀ k : Fin n → ℤ, 0 ≤ modeWeight s k := fun k => (Real.exp_pos _).le
  have hle : ∀ k, ‖coeff (fun z => u z + v z) I k‖ * modeWeight s k ≤
      ‖coeff u I k‖ * modeWeight s k + ‖coeff v I k‖ * modeWeight s k := fun k => by
    rw [coeff_add_ext hs hu hv hI, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hw k)
  have hsum : WSummable (fun z => u z + v z) s I :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (hw k)) hle (hu1.add hv1)
  refine ⟨hsum, ?_⟩
  calc wsum (fun z => u z + v z) s I
      ≤ ∑' k, (‖coeff u I k‖ * modeWeight s k + ‖coeff v I k‖ * modeWeight s k) :=
        Summable.tsum_le_tsum hle hsum (hu1.add hv1)
    _ = wsum u s I + wsum v s I := hu1.tsum_add hv1
    _ ≤ M + N := add_le_add hu2 hv2

theorem coeff_const_mul_ext (c : ℂ) (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) (I : Fin m → ℂ)
    (k : Fin n → ℤ) : coeff (fun z => c * u z) I k = c * coeff u I k := by
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  have : ∀ x : Fin n → ℝ, KAM.character (-k) (fun j => (x j : ℂ)) •
      (c * u (fun j => (x j : ℂ), I)) =
      c * (KAM.character (-k) (fun j => (x j : ℂ)) • u (fun j => (x j : ℂ), I)) := by
    intro x
    simp only [smul_eq_mul]
    ring
  simp_rw [this]
  exact MeasureTheory.integral_const_mul c _

theorem inClass_const_mul_ext (c : ℂ) {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hu : InClass D r s u) : InClass D r s (fun z => c * u z) :=
  ⟨hu.differentiableOn.const_mul c, fun j z hz => by simp only [hu.periodic j z hz]⟩

theorem wbound_const_mul_ext (c : ℂ) {M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hu : WBound D r s u M) : WBound D r s (fun z => c * u z) (‖c‖ * M) := by
  intro I hI
  obtain ⟨h1, h2⟩ := hu I hI
  have hterm : ∀ k, ‖coeff (fun z => c * u z) I k‖ * modeWeight s k =
      ‖c‖ * (‖coeff u I k‖ * modeWeight s k) := fun k => by
    rw [coeff_const_mul_ext, norm_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simpa only [WSummable, hterm] using h1.mul_left ‖c‖
  · unfold wsum
    simp only [hterm]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

end KAM.Nekhoroshev

end
