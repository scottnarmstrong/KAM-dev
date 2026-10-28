/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.TransformIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Lie transform of `h + f` (`bpN:p11:transform`, Part 11, package N11-F1)

For `ExtCompose b R' s' R s ρ σ V φ`, `h, f ∈ 𝒪_{R,s}` with `w = {h, φ}_c ∈ 𝒪_{R,s}` of norms
`W`, `U`:

`(h + f) ∘ X¹ = h + {h, φ}_c + f + 𝓡` on `𝒟_{R-ρ,s-σ}`, with the integral remainder
`𝓡 z = ∫₀¹ {(1-t){h,φ}_c + f, φ}_c (X^t z) dt` (step `tr-taylor`, `ext_taylor_second`), which is in
`𝒪_{R-ρ,s-σ}` with `|𝓡| ≤ η/(1-η) (W/2 + U)` (step `tr-int`): the remainder is also the sum of the
series `∑_{j ≥ 1} (ad^j w/(j+1)! + ad^j f/j!)` (engine below, ported from
`KAM.Canonical.TransformSeries`), whose terms are bounded by `adjoint`.

`transform_integral` is the separate statement for a time-dependent family (jointly continuous
with its derivative), proved in `TransformIntegral`.
-/

@[expose] public noncomputable section

open Set Metric Filter Finset MeasureTheory
open scoped Topology

namespace KAM.Nekhoroshev

open KAM.Weighted

variable {n k : ℕ}

/-! ### Scaling `φ` -/

theorem fderiv_fun_const_mul_ext (c : ℂ) (f : EC n k → ℂ) (z : EC n k) :
    fderiv ℂ (fun z => c * f z) z = c • fderiv ℂ f z := by
  by_cases hc : c = 0
  · subst hc
    have h0 : fderiv ℂ (fun _ : EC n k => (0 : ℂ)) z = 0 := fderiv_const_apply 0
    simp only [zero_mul, h0]
    exact (zero_smul ℂ (fderiv ℂ f z)).symm
  · let _ : Invertible c := invertibleOfNonzero hc
    exact fderiv_const_smul_of_invertible c (f := f)

theorem wfield_const_mul_ext (c : ℝ) (a : ℂ) (φ : EC n k → ℂ) (z : EC n k) :
    wfield c (fun z => a * φ z) z = a • wfield c φ z := by
  unfold wfield
  simp only [fderiv_fun_const_mul_ext, smul_apply, smul_eq_mul]
  refine Prod.ext (funext fun i => by simp) (funext fun j => ?_)
  simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left]
    ring
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_right, Fin.append_left]
      ring
    · simp only [Fin.append_right]
      ring

theorem extAd_const_mul_ext (c : ℝ) (a : ℂ) (φ : EC n k → ℂ) (j : ℕ) (u : EC n k → ℂ)
    (z : EC n k) : extAd c (fun z => a * φ z) j u z = a ^ j * extAd c φ j u z := by
  induction j generalizing z with
  | zero => simp [extAd]
  | succ j ih =>
    have e : extAd c (fun z => a * φ z) j u = fun z => a ^ j * extAd c φ j u z := funext ih
    show extBracket c (extAd c (fun z => a * φ z) j u) (fun z => a * φ z) z = _
    unfold extBracket
    rw [e, wfield_const_mul_ext, fderiv_fun_const_mul_ext]
    simp only [map_smul, smul_apply, smul_eq_mul, pow_succ]
    show _ = a ^ j * a * extBracket c (extAd c φ j u) φ z
    unfold extBracket
    ring

/-! ### `u ∘ X^t` as a Lie series -/

namespace ExtCompose

variable {b : PartialBlock n k} {R' s' R s ρ σ V U W : ℝ} {φ u h f : EC n k → ℂ}

section Flow

variable (hc : ExtCompose b R' s' R s ρ σ V φ) (hk : 1 ≤ k) (hU : 0 ≤ U)
  (hu : InClass b.base R s u) (hb : WBound b.base R s u U)
include hc hk hU hu hb

/-- `u ∘ X^t = ∑ t^j ad_φ^j u / j!` on `𝒟_{R-ρ,s-σ}`, `|t| ≤ 1`. -/
theorem flow_series {t : ℝ} (ht : |t| ≤ 1) {z : EC n k} (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) :
    u (extFlow b R' s' ρ σ φ t z) =
      ∑' j : ℕ, (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) := by
  have h1 := (hc.smul ht).series_eq hk hU hu hb hz
  rw [hc.flow_smul hk ht hz] at h1
  rw [h1]
  exact tsum_congr fun j => by rw [extAd_const_mul_ext]; ring

/-- The time integral of `u ∘ X^t`, `t ∈ [0, 1]`, termwise: `∑ ad_φ^j u / (j+1)!`. -/
theorem integral_flow_hasSum {z : EC n k} (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) :
    HasSum (fun j : ℕ => ((j : ℂ) + 1)⁻¹ * (((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z))
      (∫ t in (0 : ℝ)..1, u (extFlow b R' s' ρ σ φ t z)) := by
  have hterm := hc.lieTerm_bound hU hu hb
  set q := Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8 with hq
  have hsum := hc.lieSeries_summable (U := U)
  have hcb : ∀ j, ‖((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z‖ ≤ q ^ j * U := fun j =>
    sup_le_wbound (hterm j).1 (hterm j).2 z hz
  have hFb : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖(t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z)‖ ≤ q ^ j * U :=
    fun j t ht => by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.1]
    calc t ^ j * ‖((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z‖ ≤ 1 * ‖((j.factorial : ℂ)⁻¹) *
          extAd b.c φ j u z‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hcb j
  have key := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := (0 : ℝ)) (b := 1)
    (F := fun (j : ℕ) (t : ℝ) =>
      (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z))
    (f := fun t => u (extFlow b R' s' ρ σ φ t z))
    (fun j _ => q ^ j * U)
    (fun j => ((Complex.continuous_ofReal.pow j).mul continuous_const).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      exact hFb j t ⟨ht.1.le, ht.2⟩)
    (Filter.Eventually.of_forall fun _ _ => hsum)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t ht => by
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
      rw [hc.flow_series hk hU hu hb ht' hz]
      exact (Summable.of_norm_bounded hsum fun j => hFb j t ⟨ht.1.le, ht.2⟩).hasSum)
  convert key using 1
  funext j
  have h1 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ j * (((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) =
      (∫ t in (0 : ℝ)..1, (t : ℂ) ^ j) * (((j.factorial : ℂ)⁻¹) * extAd b.c φ j u z) :=
    intervalIntegral.integral_mul_const _ _
  have h2 : ∫ t in (0 : ℝ)..1, (t : ℂ) ^ j = ((j : ℂ) + 1)⁻¹ := by
    have : ∀ t : ℝ, (t : ℂ) ^ j = ((t ^ j : ℝ) : ℂ) := fun t => by push_cast; rfl
    simp_rw [this]
    rw [intervalIntegral.integral_ofReal, integral_pow]
    simp
  rw [h1, h2]

end Flow

/-! ### The remainder series -/

/-- The `i`-th term of `𝓡 = ∑_{j ≥ 1} (ad^j w/(j+1)! + ad^j f/j!)`, `w = {h, φ}_c`
(indexed by `i = j - 1`). -/
def extRemTerm (c : ℝ) (φ h f : EC n k → ℂ) (i : ℕ) (z : EC n k) : ℂ :=
  (((i + 2).factorial : ℂ)⁻¹) * extAd c φ (i + 1) (extBracket c h φ) z +
    (((i + 1).factorial : ℂ)⁻¹) * extAd c φ (i + 1) f z

/-- The bound of the `i`-th term. -/
def extRemBound (V ρ σ W U : ℝ) (i : ℕ) : ℝ :=
  (Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ (i + 1) * (W / ((i : ℝ) + 2) + U)

variable (hc : ExtCompose b R' s' R s ρ σ V φ) (hU : 0 ≤ U) (hW : 0 ≤ W)
  (hf : InClass b.base R s f) (hw : InClass b.base R s (extBracket b.c h φ))
  (hfb : WBound b.base R s f U) (hwb : WBound b.base R s (extBracket b.c h φ) W)

include hc hU hW hf hw hfb hwb in
/-- `a_i ∈ 𝒪_{R-ρ,s-σ}` with `|a_i| ≤ q^{i+1}(W/(i+2) + U)`. -/
theorem extRemTerm_bound (i : ℕ) :
    InClass b.base (R-ρ) (s-σ) (extRemTerm b.c φ h f i) ∧
    WBound b.base (R-ρ) (s-σ) (extRemTerm b.c φ h f i) (extRemBound V ρ σ W U i) := by
  obtain ⟨hc1, hb1⟩ := hc.lieTerm_bound hW hw hwb (i + 1)
  obtain ⟨hc2, hb2⟩ := hc.lieTerm_bound hU hf hfb (i + 1)
  have hfac : (((i + 2).factorial : ℂ)⁻¹) = ((i : ℂ) + 2)⁻¹ * (((i + 1).factorial : ℂ)⁻¹) := by
    rw [Nat.factorial_succ (i + 1), Nat.cast_mul, mul_inv]
    push_cast
    ring
  have heq : extRemTerm b.c φ h f i = fun z =>
      ((i : ℂ) + 2)⁻¹ * (((i + 1).factorial : ℂ)⁻¹ * extAd b.c φ (i + 1) (extBracket b.c h φ) z) +
        (((i + 1).factorial : ℂ)⁻¹ * extAd b.c φ (i + 1) f z) := by
    funext z
    simp only [extRemTerm, hfac]
    ring
  have hn : ‖((i : ℂ) + 2)⁻¹‖ = 1 / ((i : ℝ) + 2) := by
    have : ((i : ℂ) + 2) = (((i : ℝ) + 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  have hs0 : 0 < s - σ := by linarith [hc.sig_lt]
  rw [heq]
  have hc1' := inClass_const_mul_ext (((i : ℂ) + 2)⁻¹) hc1
  refine ⟨⟨hc1'.differentiableOn.add hc2.differentiableOn, fun j z hz => ?_⟩, ?_⟩
  · simp only [hc1'.periodic j z hz, hc2.periodic j z hz]
  · have := wbound_add_ext hs0 hc1' hc2 (wbound_const_mul_ext (((i : ℂ) + 2)⁻¹) hb1) hb2
    rw [hn] at this
    refine this.mono le_rfl le_rfl (le_of_eq ?_)
    unfold extRemBound
    ring

include hc hW hU in
omit hf hw hfb hwb in
theorem extRemBound_summable : Summable (extRemBound V ρ σ W U) := by
  obtain ⟨h0, -, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.eta_nonneg
    (hc.small.trans (by norm_num))
  have hg : Summable fun i : ℕ => (Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8) ^ (i + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 hq)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hg.mul_right (W / 2 + U))
  · unfold extRemBound
    positivity
  · unfold extRemBound
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 _)
    have : W / ((i : ℝ) + 2) ≤ W / 2 :=
      div_le_div_of_nonneg_left hW (by norm_num) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    linarith

include hc hW hU in
omit hf hw hfb hwb in
theorem extRemBound_tsum_le :
    ∑' i, extRemBound V ρ σ W U i ≤ (2 * V / (ρ * σ)) / (1 - 2 * V / (ρ * σ)) * (W / 2 + U) := by
  obtain ⟨h0, hqη, hq⟩ := q_facts_ext (η := 2 * V / (ρ * σ)) hc.eta_nonneg
    (hc.small.trans (by norm_num))
  set q := Real.exp 1 ^ 2 * (2 * V / (ρ * σ)) / 8 with hqdef
  set η := 2 * V / (ρ * σ) with hη
  have hη1 : η < 1 := by linarith [hc.small]
  have hg : Summable fun i : ℕ => q ^ (i + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 hq)
  have hle : ∑' i, extRemBound V ρ σ W U i ≤ ∑' i : ℕ, q ^ (i + 1) * (W / 2 + U) := by
    refine Summable.tsum_le_tsum (fun i => ?_) (hc.extRemBound_summable hU hW) (hg.mul_right _)
    unfold extRemBound
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 _)
    have : W / ((i : ℝ) + 2) ≤ W / 2 :=
      div_le_div_of_nonneg_left hW (by norm_num) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    linarith
  have hsum : ∑' i : ℕ, q ^ (i + 1) * (W / 2 + U) = q / (1 - q) * (W / 2 + U) := by
    rw [tsum_mul_right]
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one h0 hq]
    ring
  refine hle.trans (hsum.le.trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

include hc hU hW hf hw hfb hwb

theorem extRemSeries_class : InClass b.base (R-ρ) (s-σ)
    (fun z => ∑' i, extRemTerm b.c φ h f i z) := by
  have hterm := hc.extRemTerm_bound hU hW hf hw hfb hwb
  have hbd : ∀ i, ∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      ‖extRemTerm b.c φ h f i z‖ ≤ extRemBound V ρ σ W U i := fun i =>
    sup_le_wbound (hterm i).1 (hterm i).2
  refine ⟨?_, fun j z hz => ?_⟩
  · refine (uniform_limit_holomorphic (isOpen_Dom _ _ _) (K := fun N z =>
      ∑ i ∈ range N, extRemTerm b.c φ h f i z) (fun N => ?_)
      (tendstoUniformlyOn_tsum_nat (hc.extRemBound_summable hU hW) hbd)).1
    exact DifferentiableOn.fun_sum fun i _ => (hterm i).1.differentiableOn
  · exact tsum_congr fun i => by rw [(hterm i).1.periodic j z hz]

theorem extRemSeries_bound : WBound b.base (R-ρ) (s-σ)
    (fun z => ∑' i, extRemTerm b.c φ h f i z)
    ((2 * V / (ρ * σ)) / (1 - 2 * V / (ρ * σ)) * (W / 2 + U)) :=
  ((wbound_tsum_ext (by linarith [hc.sig_lt]) (fun i => (hc.extRemTerm_bound hU hW hf hw hfb hwb i).1)
    (fun i => (hc.extRemTerm_bound hU hW hf hw hfb hwb i).2) (hc.extRemBound_summable hU hW))).mono
    le_rfl le_rfl (hc.extRemBound_tsum_le hU hW)

theorem extRemSeries_hasSum {z : EC n k} (hz : z ∈ Dom n b.base (R-ρ) (s-σ)) :
    HasSum (fun i => extRemTerm b.c φ h f i z) (∑' i, extRemTerm b.c φ h f i z) :=
  (Summable.of_norm_bounded (hc.extRemBound_summable hU hW) fun i =>
    sup_le_wbound (hc.extRemTerm_bound hU hW hf hw hfb hwb i).1
      (hc.extRemTerm_bound hU hW hf hw hfb hwb i).2 z hz).hasSum

end ExtCompose

end KAM.Nekhoroshev

end
