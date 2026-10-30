/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Norms
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The row-sum ℓ¹ Cauchy estimate (package B10a)

Blueprint `bp:p2s2l1:toolkit`(c) of `blueprint/parts/p2s2-l1hybrid.tex`.

* The bridge `hasSum_fderiv_fourierSum_single`: on `T_ρ` the derivative of a Fourier series with
    coefficients
  summable at radius `2πρ` is the series of the termwise derivatives,
  `∂_j ∑ₖ aₖ χₖ = ∑ₖ aₖ χₖ 2πi kⱼ` (the termwise differentiation of
      `KAM.differentiableOn_fourierSum`, made explicit).
* `sum_norm_fderiv_fourierSum_le`: on `T_{r-δ}`, `∑ⱼ |∂ⱼ ∑ₖ aₖ χₖ| ≤ ‖a‖_{2πr}/(e δ)`, since
  `∑ⱼ 2π|kⱼ| e^{-2πδ|k|₁} = 2π|k|₁ e^{-2πδ|k|₁} ≤ 1/(e δ)` (`KAM.Fourier.mul_exp_radius_sub_le`).
* `L1Vec.norm_jac_le` (factor `1/(e δ)`, against `n/δ` in sup norms), `L1Vec.norm_jac_transpose_le`
    (factor
  `p/(e δ)`), `L1Vec.norm_jac_antisymm_le` (factor `n/(e δ)`: the diagonal of `Df - (Df)ᵀ`
      vanishes, which leaves
  `1 + (n - 1)` row terms).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.L1

open KAM KAM.Torus

variable {n : ℕ}

/-! ### The derivative of a Fourier series -/

/-- The derivative of a Fourier series on the strip is the series of the termwise derivatives. -/
theorem hasFDerivAt_fourierSum {ρ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * ρ) a) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ)
        :
    HasFDerivAt (fourierSum a)
        (∑' k, a k • (character k θ • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))) θ ∧
      Summable fun k => a k • (character k θ • ((2 * Real.pi * Complex.I : ℂ) • modeForm k)) := by
  obtain ⟨ε, hε, hθε⟩ := exists_mem_complexStrip_sub hθ
  set C : ℝ := 2 * Real.pi * (Real.exp (-1) / (2 * Real.pi * ε)) with hC
  have hδ : 0 < 2 * Real.pi * ε := by positivity
  have hderiv : ∀ (k : Fin n → ℤ) (z : Fin n → ℂ), z ∈ complexStrip n (ρ - ε) →
      HasFDerivAt (fun z => a k * character k z)
        (a k • (character k z • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))) z :=
    fun k z _ => (hasFDerivAt_character k z).const_mul (a k)
  have hbound : ∀ (k : Fin n → ℤ) (z : Fin n → ℂ), z ∈ complexStrip n (ρ - ε) →
      ‖a k • (character k z • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))‖ ≤
        C * (‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) := by
    intro k z hz
    have hI : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    have hM := Fourier.mul_exp_radius_sub_le (2 * Real.pi * ρ) (Fourier.modeSize k) hδ
    have hexp : Real.exp ((2 * Real.pi * ρ - 2 * Real.pi * ε) * Fourier.modeSize k) =
        Real.exp (2 * Real.pi * (ρ - ε) * Fourier.modeSize k) := by
      congr 1
      ring
    rw [hexp] at hM
    calc ‖a k • (character k z • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))‖
        = ‖a k‖ * (‖character k z‖ * (2 * Real.pi * ‖modeForm k‖)) := by
          rw [norm_smul, norm_smul, norm_smul, hI]
      _ ≤ ‖a k‖ * (Real.exp (2 * Real.pi * (ρ - ε) * Fourier.modeSize k) *
            (2 * Real.pi * Fourier.modeSize k)) := by
          gcongr
          · exact norm_character_le k hz
          · exact norm_modeForm_le k
      _ = 2 * Real.pi * ‖a k‖ * (Fourier.modeSize k *
            Real.exp (2 * Real.pi * (ρ - ε) * Fourier.modeSize k)) := by ring
      _ ≤ 2 * Real.pi * ‖a k‖ * (Real.exp (-1) / (2 * Real.pi * ε) *
            Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) := by
          gcongr
      _ = C * (‖a k‖ * Real.exp (2 * Real.pi * ρ * Fourier.modeSize k)) := by
          rw [hC]
          ring
  have hsub : complexStrip n (ρ - ε) ⊆ complexStrip n ρ := fun z hz j => by
    have := hz j
    linarith
  refine ⟨hasFDerivAt_tsum_of_isPreconnected (ha.mul_left C) (isOpen_complexStrip n _)
    (convex_complexStrip n _).isPreconnected hderiv hbound hθε
    (summable_coeff_mul_character ha (hsub hθε)) hθε, ?_⟩
  exact Summable.of_norm_bounded (ha.mul_left C) (fun k => hbound k θ hθε)

/-- The value at `e_j` of one term of the derivative series. -/
theorem fderiv_term_apply_single (a : (Fin n → ℤ) → ℂ) (θ : Fin n → ℂ) (k : Fin n → ℤ) (j : Fin n) :
    (a k • (character k θ • ((2 * Real.pi * Complex.I : ℂ) • modeForm k))) (Pi.single j 1) =
      a k * (character k θ * (2 * Real.pi * Complex.I * (k j : ℂ))) := by
  rw [_root_.smul_apply, _root_.smul_apply, _root_.smul_apply,
    modeForm_apply, Finset.sum_eq_single j (fun l _ hl => by simp [hl])
      (fun h => absurd (Finset.mem_univ j) h)]
  simp only [Pi.single_eq_same, mul_one, smul_eq_mul]

/-- The directional derivative `∂_j` of a Fourier series: `∑ₖ aₖ χₖ(θ) 2πi kⱼ`. -/
theorem hasSum_fderiv_fourierSum_single {ρ : ℝ} {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * ρ) a) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n ρ)
    (j : Fin n) :
    HasSum (fun k => a k * (character k θ * (2 * Real.pi * Complex.I * (k j : ℂ))))
      (fderiv ℂ (fourierSum a) θ (Pi.single j 1)) := by
  obtain ⟨hD, hS⟩ := hasFDerivAt_fourierSum ha hθ
  rw [hD.fderiv]
  have h := hS.hasSum.mapL (ContinuousLinearMap.apply ℂ ℂ (Pi.single j (1 : ℂ)))
  simp only [ContinuousLinearMap.apply_apply, fderiv_term_apply_single] at h
  exact h

/-! ### The row-sum bound -/

/-- `2π|k|₁ e^{2π(r-δ)|k|₁} ≤ e^{2πr|k|₁}/(e δ)`. -/
theorem two_pi_modeSize_mul_exp_le {r δ : ℝ} (hδ : 0 < δ) (k : Fin n → ℤ) :
    2 * Real.pi * Fourier.modeSize k * Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) ≤
      Real.exp (2 * Real.pi * r * Fourier.modeSize k) / (Real.exp 1 * δ) := by
  have hδ' : 0 < 2 * Real.pi * δ := by positivity
  have hM := Fourier.mul_exp_radius_sub_le (2 * Real.pi * r) (Fourier.modeSize k) hδ'
  have hexp : Real.exp ((2 * Real.pi * r - 2 * Real.pi * δ) * Fourier.modeSize k) =
      Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) := by
    congr 1
    ring
  rw [hexp] at hM
  have hpi : 0 < 2 * Real.pi := by positivity
  calc 2 * Real.pi * Fourier.modeSize k * Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k)
      = 2 * Real.pi * (Fourier.modeSize k * Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k))
          := by
        ring
    _ ≤ 2 * Real.pi * (Real.exp (-1) / (2 * Real.pi * δ) *
          Real.exp (2 * Real.pi * r * Fourier.modeSize k)) :=
        mul_le_mul_of_nonneg_left hM hpi.le
    _ = Real.exp (2 * Real.pi * r * Fourier.modeSize k) / (Real.exp 1 * δ) := by
        rw [Real.exp_neg]
        field_simp

/-- **The row-sum Cauchy estimate for a Fourier series**: on `T_{r-δ}`,
`∑ⱼ |∂ⱼ ∑ₖ aₖ χₖ| ≤ ‖a‖_{2πr}/(e δ)`. -/
theorem sum_norm_fderiv_fourierSum_le {r δ : ℝ} (hδ : 0 < δ) {a : (Fin n → ℤ) → ℂ}
    (ha : Fourier.SummableWeighted (2 * Real.pi * r) a) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n (r - δ)) :
    ∑ j, ‖fderiv ℂ (fourierSum a) θ (Pi.single j 1)‖ ≤
      Fourier.weightedNorm (2 * Real.pi * r) a / (Real.exp 1 * δ) := by
  have hθr : θ ∈ complexStrip n r := fun i => (hθ i).trans_le (by linarith)
  set t : (Fin n → ℤ) → Fin n → ℝ := fun k j =>
    ‖a k‖ * Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k) * (2 * Real.pi * |(k j : ℝ)|)
        with ht
  have hw : ∀ k, ∑ j, t k j ≤
      ‖a k‖ * Real.exp (2 * Real.pi * r * Fourier.modeSize k) / (Real.exp 1 * δ) := fun k => by
    have hsum : ∑ j, t k j = ‖a k‖ * (2 * Real.pi * Fourier.modeSize k *
        Real.exp (2 * Real.pi * (r - δ) * Fourier.modeSize k)) := by
      simp only [ht, Fourier.modeSize, ← Finset.mul_sum]
      ring
    rw [hsum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (two_pi_modeSize_mul_exp_le hδ k) (norm_nonneg _)
  have htle : ∀ k j, t k j ≤
      ‖a k‖ * Real.exp (2 * Real.pi * r * Fourier.modeSize k) / (Real.exp 1 * δ) := fun k j =>
    (Finset.single_le_sum (f := fun j => t k j)
      (fun _ _ => by simp only [ht]; positivity) (Finset.mem_univ j)).trans (hw k)
  have hmaj : Summable fun k =>
      ‖a k‖ * Real.exp (2 * Real.pi * r * Fourier.modeSize k) / (Real.exp 1 * δ) :=
    ha.div_const _
  have hts : ∀ j, Summable fun k => t k j := fun j =>
    Summable.of_nonneg_of_le (fun k => by simp only [ht]; positivity) (fun k => htle k j) hmaj
  -- each derivative is bounded by its majorant series
  have hD : ∀ j, ‖fderiv ℂ (fourierSum a) θ (Pi.single j 1)‖ ≤ ∑' k, t k j := fun j => by
    refine (hasSum_fderiv_fourierSum_single ha hθr j).norm_le_of_bounded (hts j).hasSum fun k => ?_
    have hI : ‖(2 * Real.pi * Complex.I * (k j : ℂ))‖ = 2 * Real.pi * |(k j : ℝ)| := by
      rw [norm_mul, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      simp [abs_of_pos Real.pi_pos]
    rw [norm_mul, norm_mul, hI, ht]
    simp only
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_character_le k hθ) (norm_nonneg _)) (by positivity)
  have hsumj : HasSum (fun k => ∑ j, t k j) (∑ j, ∑' k, t k j) :=
    hasSum_sum fun j _ => (hts j).hasSum
  calc ∑ j, ‖fderiv ℂ (fourierSum a) θ (Pi.single j 1)‖ ≤ ∑ j, ∑' k, t k j :=
        Finset.sum_le_sum fun j _ => hD j
    _ ≤ Fourier.weightedNorm (2 * Real.pi * r) a / (Real.exp 1 * δ) :=
        hasSum_le hw hsumj (by
          unfold Fourier.weightedNorm
          simp only [mul_div_assoc]
          exact (ha.hasSum.mul_right _).congr_fun fun k => by ring)

/-! ### Jacobians of ℓ¹ data -/

/-- The entries of the Jacobian of ℓ¹ data are the derivatives of the Fourier series of the
    components. -/
theorem jac_apply_eq_fderiv_fourierSum {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    {f : (Fin n → ℂ) → ι → ℂ} (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f
        r)
    (hs : ∀ i, Fourier.SummableWeighted (2 * Real.pi * r) (coeffR f i)) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) (i : ι) (j : Fin n) :
    jac f θ i j = fderiv ℂ (fourierSum (coeffR f i)) θ (Pi.single j 1) := by
  have hfθ : DifferentiableAt ℂ f θ := hf.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθ)
  have h1 : fderiv ℂ (fun z => f z i) θ = (ContinuousLinearMap.proj i).comp (fderiv ℂ f θ) :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).hasFDerivAt.comp θ
      hfθ.hasFDerivAt).fderiv
  have h2 : fderiv ℂ (fun z => f z i) θ = fderiv ℂ (fourierSum (coeffR f i)) θ := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(isOpen_complexStrip n r).mem_nhds hθ] with z hz
    exact eq_fourierSum_of_summableWeighted hr (differentiableOn_pi.mp hf i)
      (fun l z hz => congrFun (hfp l z hz) i) (hs i) z hz
  rw [← h2, h1]
  simp [jac]

/-- The row sums of the Jacobian of ℓ¹ data on `T_{r-δ}`. -/
theorem L1Vec.sum_norm_jac_le {ι : Type*} [Fintype ι] {r δ A : ℝ} {f : (Fin n → ℂ) → ι → ℂ} (hδ : 0
    < δ)
    (hδr : δ < r) (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f r)
    (h : L1Vec r f A) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - δ)) (i : ι) :
    ∑ j, ‖jac f θ i j‖ ≤ A / (Real.exp 1 * δ) := by
  have hr : 0 < r := hδ.trans hδr
  have hθr : θ ∈ complexStrip n r := fun l => (hθ l).trans_le (by linarith)
  have heq : ∀ j, jac f θ i j = fderiv ℂ (fourierSum (coeffR f i)) θ (Pi.single j 1) := fun j =>
    jac_apply_eq_fderiv_fourierSum hr hf hfp (fun i => (h.2 i).1) hθr i j
  simp only [heq]
  exact (sum_norm_fderiv_fourierSum_le hδ (h.2 i).1 hθ).trans
    (div_le_div_of_nonneg_right (h.2 i).2 (by positivity))

/-- Blueprint `bp:p2s2l1:toolkit`(c): the row-sum ℓ¹ Cauchy estimate `|Df| ≤ ‖f‖_{1,r}/(e δ)` on
    `T_{r-δ}`. -/
theorem L1Vec.norm_jac_le {ι : Type*} [Fintype ι] {r δ A : ℝ} {f : (Fin n → ℂ) → ι → ℂ} (hδ : 0 < δ)
    (hδr : δ < r) (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f r) (h :
        L1Vec r f A) :
    ∀ θ ∈ complexStrip n (r - δ), ‖jac f θ‖ ≤ A / (Real.exp 1 * δ) := fun θ hθ =>
  (norm_le_iff_forall_rowSum (div_nonneg h.1 (by positivity))).2 fun i =>
    L1Vec.sum_norm_jac_le hδ hδr hf hfp h hθ i

/-- Every entry of the Jacobian of ℓ¹ data is at most `A/(e δ)` on `T_{r-δ}`. -/
theorem L1Vec.norm_jac_entry_le {ι : Type*} [Fintype ι] {r δ A : ℝ} {f : (Fin n → ℂ) → ι → ℂ} (hδ :
    0 < δ)
    (hδr : δ < r) (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f r)
    (h : L1Vec r f A) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - δ)) (i : ι) (j : Fin n) :
    ‖jac f θ i j‖ ≤ A / (Real.exp 1 * δ) :=
  (Finset.single_le_sum (f := fun j => ‖jac f θ i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans (L1Vec.sum_norm_jac_le hδ hδr hf hfp h hθ i)

/-- Blueprint `bp:p2s2l1:toolkit`(c): the transpose, `|(Df)ᵀ| ≤ p ‖f‖_{1,r}/(e δ)` (`p`
    components). -/
theorem L1Vec.norm_jac_transpose_le {ι : Type*} [Fintype ι] {r δ A : ℝ} {f : (Fin n → ℂ) → ι → ℂ}
    (hδ : 0 < δ)
    (hδr : δ < r) (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f r) (h :
        L1Vec r f A) :
    ∀ θ ∈ complexStrip n (r - δ), ‖(jac f θ)ᵀ‖ ≤ Fintype.card ι * A / (Real.exp 1 * δ) := fun θ hθ
        => by
  have hA : 0 ≤ A / (Real.exp 1 * δ) := div_nonneg h.1 (by positivity)
  refine (norm_le_iff_forall_rowSum (by rw [mul_div_assoc]; positivity)).2 fun j => ?_
  calc ∑ i, ‖(jac f θ)ᵀ j i‖ = ∑ i, ‖jac f θ i j‖ := by simp [Matrix.transpose_apply]
    _ ≤ ∑ _i : ι, A / (Real.exp 1 * δ) := Finset.sum_le_sum fun i _ =>
        L1Vec.norm_jac_entry_le hδ hδr hf hfp h hθ i j
    _ = Fintype.card ι * A / (Real.exp 1 * δ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]

/-- Blueprint `bp:p2s2l1:toolkit`(c): the antisymmetric part, `|Df - (Df)ᵀ| ≤ n ‖f‖_{1,r}/(e δ)`. -/
theorem L1Vec.norm_jac_antisymm_le {r δ A : ℝ} {f : (Fin n → ℂ) → Fin n → ℂ} (hδ : 0 < δ) (hδr : δ
    < r)
    (hf : DifferentiableOn ℂ f (complexStrip n r)) (hfp : IsPeriodicOn f r) (h : L1Vec r f A) :
    ∀ θ ∈ complexStrip n (r - δ), ‖jac f θ - (jac f θ)ᵀ‖ ≤ n * A / (Real.exp 1 * δ) := fun θ hθ =>
        by
  set c := A / (Real.exp 1 * δ) with hc
  have hc0 : 0 ≤ c := div_nonneg h.1 (by positivity)
  have hnA : n * A / (Real.exp 1 * δ) = n * c := by rw [hc, mul_div_assoc]
  rw [hnA]
  refine (norm_le_iff_forall_rowSum (by positivity)).2 fun i => ?_
  set J := jac f θ with hJ
  have hdiag : ‖(J - Jᵀ) i i‖ = 0 := by simp
  have hrow : ∑ j, ‖(J - Jᵀ) i j‖ = ∑ j ∈ Finset.univ.erase i, ‖(J - Jᵀ) i j‖ :=
    (Finset.sum_erase (f := fun j => ‖(J - Jᵀ) i j‖) (a := i) Finset.univ hdiag).symm
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr fun hn => by subst hn; exact Fin.elim0 i
  have hcard : ((Finset.univ.erase i).card : ℝ) = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hn1, Nat.cast_one]
  calc ∑ j, ‖(J - Jᵀ) i j‖ = ∑ j ∈ Finset.univ.erase i, ‖(J - Jᵀ) i j‖ := hrow
    _ ≤ ∑ j ∈ Finset.univ.erase i, (‖J i j‖ + ‖J j i‖) := Finset.sum_le_sum fun j _ => by
        simpa [Matrix.sub_apply, Matrix.transpose_apply] using norm_sub_le (J i j) (J j i)
    _ = ∑ j ∈ Finset.univ.erase i, ‖J i j‖ + ∑ j ∈ Finset.univ.erase i, ‖J j i‖ :=
        Finset.sum_add_distrib
    _ ≤ ∑ j, ‖J i j‖ + ∑ _j ∈ Finset.univ.erase i, c :=
        add_le_add (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i _)
            fun _ _ _ => norm_nonneg _)
          (Finset.sum_le_sum fun j _ => L1Vec.norm_jac_entry_le hδ hδr hf hfp h hθ j i)
    _ ≤ c + (n - 1) * c := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        exact add_le_add (L1Vec.sum_norm_jac_le hδ hδr hf hfp h hθ i) le_rfl
    _ = n * c := by ring

end KAM.Sharp2.L1

end
