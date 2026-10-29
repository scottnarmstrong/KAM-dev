/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Coefficients
public import KAM.Fourier.Convolution
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The algebra property of the weighted norm (`bpN:p4:algebra`)

Scalar values. At fixed `I` the Fourier coefficients of a product are the convolution of the
coefficients (Cauchy product of the absolutely convergent series, `KAM.Fourier.convolution`), and
the weighted sum is submultiplicative:

* `coeff_mul`: the pointwise-in-`I` statement;
* `wbound_mul`: `|uv|_{r,s} ≤ |u|_{r,s} |v|_{r,s}`;
* `wbound_pow`: `|uʲ|_{r,s} ≤ |u|_{r,s}ʲ`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Weighted

-- The signatures keep the common instance block; not every lemma uses all of it.
set_option linter.unusedSectionVars false

variable {n m : ℕ}

/-! ### The Cauchy product of two Fourier series -/

/-- `(k, l) ↦ (l, k - l)`: output mode and summation index to the two input modes. -/
private def cauchyEquiv : ((Fin n → ℤ) × (Fin n → ℤ)) ≃ ((Fin n → ℤ) × (Fin n → ℤ)) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext j <;> simp
  right_inv p := by ext j <;> simp

/-- Weighted summability in the `KAM.Fourier` convention, from ours. -/
private theorem summableWeighted_of {s : ℝ} {a : (Fin n → ℤ) → ℂ}
    (h : Summable fun k : Fin n → ℤ => ‖a k‖ * modeWeight s k) :
    KAM.Fourier.SummableWeighted (2 * Real.pi * s) a := by
  unfold KAM.Fourier.SummableWeighted
  simpa only [modeWeight] using h

/-- The Cauchy product `(∑ aₗ χₗ)(∑ bₗ χₗ) = ∑ₖ (∑ₗ a_{k-l} b_l) χₖ` on the strip. -/
private theorem fourierSum_mul {s : ℝ} {a b : (Fin n → ℤ) → ℂ}
    (ha : KAM.Fourier.SummableWeighted (2 * Real.pi * s) a)
    (hb : KAM.Fourier.SummableWeighted (2 * Real.pi * s) b) {θ : Fin n → ℂ}
    (hθ : θ ∈ KAM.complexStrip n s) :
    KAM.fourierSum a θ * KAM.fourierSum b θ =
      KAM.fourierSum (fun k => ∑' l, a (k - l) * b l) θ := by
  set F : (Fin n → ℤ) × (Fin n → ℤ) → ℂ := fun p =>
    (a p.1 * KAM.character p.1 θ) * (b p.2 * KAM.character p.2 θ) with hF
  have hnA := KAM.summable_coeff_mul_character ha hθ
  have hnB := KAM.summable_coeff_mul_character hb hθ
  have hAn : Summable fun k => ‖a k * KAM.character k θ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (KAM.norm_coeff_mul_character_le a hθ) ha
  have hBn : Summable fun k => ‖b k * KAM.character k θ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (KAM.norm_coeff_mul_character_le b hθ) hb
  have hFn : Summable fun p => ‖F p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      (hAn.mul_of_nonneg hBn (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    simp only [hF, norm_mul]
    exact le_rfl
  have hFs : Summable F := hFn.of_norm
  have hprod : KAM.fourierSum a θ * KAM.fourierSum b θ = ∑' p, F p :=
    tsum_mul_tsum_of_summable_norm hAn hBn
  -- reindex
  have hterm : ∀ q : (Fin n → ℤ) × (Fin n → ℤ), F (cauchyEquiv q) =
      (a q.2 * b (q.1 - q.2)) * KAM.character q.1 θ := by
    intro q
    simp only [hF, cauchyEquiv, Equiv.coe_fn_mk]
    have : KAM.character q.2 θ * KAM.character (q.1 - q.2) θ = KAM.character q.1 θ := by
      rw [KAM.character_mul]; simp
    rw [← this]; ring
  have hFq : Summable fun q => F (cauchyEquiv q) := cauchyEquiv.summable_iff.mpr hFs
  rw [hprod, ← cauchyEquiv.tsum_eq F, hFq.tsum_prod]
  unfold KAM.fourierSum
  refine tsum_congr fun k => ?_
  simp only [hterm]
  rw [tsum_mul_right]
  congr 1
  exact (Equiv.subLeft k).tsum_eq (fun l => a l * b (k - l)) |>.symm.trans <| by
    refine tsum_congr fun l => ?_
    simp [Equiv.subLeft_apply]

/-- The coefficient convolution in the orientation of the statement. -/
private theorem convolution_eq (a b : (Fin n → ℤ) → ℂ) :
    KAM.Fourier.convolution a b = fun k => ∑' l, a (k - l) * b l := by
  funext k
  unfold KAM.Fourier.convolution
  rw [← (Equiv.subLeft k).tsum_eq (fun l => a (k - l) * b l)]
  refine tsum_congr fun l => ?_
  simp [Equiv.subLeft_apply]

/-! ### Representation at fixed `I` -/

variable {D : Set (Fin m → ℂ)} {r s : ℝ}

private theorem continuous_real_restrict' {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s)
    (hu : InClass D r s u) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) :
    Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
  hu.differentiableOn.continuousOn.comp_continuous
    ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).prodMk
      continuous_const) fun x => ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

/-- At fixed `I` a scalar class function is the Fourier series of its coefficients on the strip. -/
private theorem eq_fourierSum_coeff {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hs : 0 < s)
    (hu : InClass D r s u) {I : Fin m → ℂ} (hI : I ∈ polyNbhd D r) (ha : WSummable u s I)
    {θ : Fin n → ℂ} (hθ : θ ∈ KAM.complexStrip n s) :
    u (θ, I) = KAM.fourierSum (coeff u I) θ := by
  have ha' := summableWeighted_of ha
  have hmaps : MapsTo (fun θ : Fin n → ℂ => (θ, I)) (KAM.complexStrip n s) (Dom n D r s) :=
    fun θ hθ => ⟨hθ, hI⟩
  have hud : DifferentiableOn ℂ (fun θ : Fin n → ℂ => u (θ, I)) (KAM.complexStrip n s) :=
    hu.differentiableOn.comp (differentiableOn_id.prodMk (differentiableOn_const I)) hmaps
  have hdiff := KAM.differentiableOn_fourierSum ha'
  have hc0 := continuous_real_restrict' hs hu hI
  have hc1 : Continuous fun x : Fin n → ℝ => KAM.fourierSum (coeff u I) fun j => (x j : ℂ) :=
    hdiff.continuousOn.comp_continuous
      (continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j))
      (KAM.ofReal_mem_complexStrip hs)
  have hg := KAM.eq_zero_of_torusCoeff_holomorphic hs
    (v := fun θ => u (θ, I) - KAM.fourierSum (coeff u I) θ) (hud.sub hdiff)
    (fun i z hz => by
      show u (z + Pi.single i 1, I) - KAM.fourierSum (coeff u I) (z + Pi.single i 1) =
        u (z, I) - KAM.fourierSum (coeff u I) z
      rw [hu.periodic i (z, I) ⟨hz, hI⟩, KAM.fourierSum_add_single])
    (fun k => by
      show KAM.torusCoeff (fun x => u (fun j => (x j : ℂ), I) -
        KAM.fourierSum (coeff u I) fun j => (x j : ℂ)) k = 0
      rw [KAM.torusCoeff_sub hc0 hc1 k, KAM.torusCoeff_fourierSum hs.le ha' k]
      exact sub_self _) θ hθ
  exact sub_eq_zero.mp hg

/-! ### Lemma B.2 -/

private theorem inClass_mul {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u)
    (hv : InClass D r s v) : InClass D r s (fun z => u z * v z) :=
  ⟨hu.differentiableOn.mul hv.differentiableOn, fun j z hz => by
    simp only [hu.periodic j z hz, hv.periodic j z hz]⟩

/-- Pointwise in `I`, with the coefficient convolution (`KAM.Fourier.convolution`). -/
theorem coeff_mul {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass D r s u) (hv : InClass D r s v) {I : Fin m → ℂ}
    (hI : I ∈ polyNbhd D r) (hu' : WSummable u s I) (hv' : WSummable v s I) :
    InClass D r s (fun z => u z * v z) ∧
    (∀ k, Summable fun l => ‖coeff u I (k - l) * coeff v I l‖) ∧
    (∀ k, coeff (fun z => u z * v z) I k = ∑' l, coeff u I (k - l) * coeff v I l) ∧
    WSummable (fun z => u z * v z) s I ∧
    wsum (fun z => u z * v z) s I ≤ wsum u s I * wsum v s I := by
  have ha := summableWeighted_of hu'
  have hb := summableWeighted_of hv'
  have hs' : 0 ≤ 2 * Real.pi * s := by positivity
  have hconv := convolution_eq (coeff u I) (coeff v I)
  have hcoeff : ∀ k, coeff (fun z => u z * v z) I k =
      KAM.Fourier.convolution (coeff u I) (coeff v I) k := by
    intro k
    rw [hconv]
    have hx : (fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) * v (fun j => (x j : ℂ), I)) =
        fun x => KAM.fourierSum (fun k => ∑' l, coeff u I (k - l) * coeff v I l)
          (fun j => (x j : ℂ)) := by
      funext x
      have hθ := KAM.ofReal_mem_complexStrip hs x
      rw [eq_fourierSum_coeff hs hu hI hu' hθ, eq_fourierSum_coeff hs hv hI hv' hθ,
        fourierSum_mul ha hb hθ]
    show KAM.torusCoeff (fun x : Fin n → ℝ =>
      u (fun j => (x j : ℂ), I) * v (fun j => (x j : ℂ), I)) k = _
    rw [hx]
    exact KAM.torusCoeff_fourierSum hs.le (by rw [← hconv]; exact ha.convolution hs' hb) k
  have hsw : KAM.Fourier.SummableWeighted (2 * Real.pi * s) (coeff (fun z => u z * v z) I) := by
    rw [funext hcoeff]; exact ha.convolution hs' hb
  refine ⟨inClass_mul hu hv, fun k => ?_, fun k => ?_, ?_, ?_⟩
  · have := KAM.Fourier.summable_norm_convolution hs' ha hb k
    rw [← (Equiv.subLeft k).summable_iff]
    simpa [Function.comp_def, Equiv.subLeft_apply, mul_comm] using this
  · rw [hcoeff, hconv]
  · simpa only [WSummable, KAM.Fourier.SummableWeighted, modeWeight] using hsw
  · have h := KAM.Fourier.weightedNorm_convolution_le hs' ha hb
    unfold wsum modeWeight
    simp only [← funext hcoeff] at h
    exact h

theorem wbound_mul {Mu Mv : ℝ} {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass D r s u) (hv : InClass D r s v) (hbu : WBound D r s u Mu)
    (hbv : WBound D r s v Mv) : WBound D r s (fun z => u z * v z) (Mu * Mv) := by
  intro I hI
  obtain ⟨h1, h2, h3, h4, h5⟩ := coeff_mul hs hu hv hI (hbu I hI).1 (hbv I hI).1
  refine ⟨h4, h5.trans ?_⟩
  have h0u : 0 ≤ wsum u s I := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  exact mul_le_mul (hbu I hI).2 (hbv I hI).2
    (tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (h0u.trans (hbu I hI).2)

private theorem inClass_pow {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u)
    (j : ℕ) : InClass D r s (fun z => u z ^ j) := by
  induction j with
  | zero => exact ⟨differentiableOn_const _, fun _ _ _ => rfl⟩
  | succ j ih => simpa only [pow_succ] using inClass_mul ih hu

/-- The coefficients of the constant `1` are those of `χ₀`. -/
private theorem wbound_one :
    WBound D r s (fun _ : (Fin n → ℂ) × (Fin m → ℂ) => (1 : ℂ)) 1 := by
  intro I _
  have hc : ∀ k : Fin n → ℤ, coeff (fun _ : (Fin n → ℂ) × (Fin m → ℂ) => (1 : ℂ)) I k =
      if k = 0 then 1 else 0 := fun k => by
    show KAM.torusAverage (fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) * 1) = _
    simp only [mul_one]
    rw [KAM.torusAverage_character]
    simp
  have hz : ∀ k : Fin n → ℤ, k ≠ 0 →
      ‖coeff (fun _ : (Fin n → ℂ) × (Fin m → ℂ) => (1 : ℂ)) I k‖ * modeWeight s k = 0 :=
    fun k hk => by simp [hc, hk]
  have hw : WSummable (fun _ : (Fin n → ℂ) × (Fin m → ℂ) => (1 : ℂ)) s I :=
    summable_of_ne_finset_zero (s := {0}) fun k hk => hz k (by simpa using hk)
  refine ⟨hw, le_of_eq ?_⟩
  unfold wsum
  rw [tsum_eq_single 0 hz]
  simp [hc, modeWeight, KAM.Fourier.modeSize]

theorem wbound_pow {M : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hs : 0 < s) (hu : InClass D r s u) (hb : WBound D r s u M) (j : ℕ) :
    WBound D r s (fun z => u z ^ j) (M ^ j) := by
  induction j with
  | zero => simpa using wbound_one
  | succ j ih =>
    simpa only [pow_succ] using wbound_mul hs (inClass_pow hu j) hu ih hb

end KAM.Weighted

end
