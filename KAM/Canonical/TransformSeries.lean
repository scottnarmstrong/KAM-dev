/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Canonical.Composition
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The remainder series of the transform (`bpN:p5:transform`, the engine)

Package C5-9. For `ComposeData`, `h`, `f₀ ∈ O(r, s)` with `w = {h, φ}` and `f₀` of finite norms
`Mw`, `F₀`, write `a_i = ad_φ^{i+1} w / (i+2)! + ad_φ^{i+1} f₀ / (i+1)!` and `q = e η / 4`
(`η = 2Φ/(ρσ) ≤ 1/2`).

* `KAM.Canonical.wbound_add`: the weighted norm is subadditive (coefficients of sums);
* `KAM.Canonical.inClass_poissonBracket`: `{u, v} ∈ O(r, s)` for `u ∈ O(r, s)`, `v ∈ O(r', s')`;
* `KAM.Canonical.remTerm_bound`: `a_i ∈ O(r-ρ, s-σ)` with `|a_i| ≤ q^{i+1} (Mw/(i+2) + F₀)`;
* `KAM.Canonical.remSeries_*`: the sum is in the class, with the stated bounds, pointwise
  `HasSum`, and its tails are small in the weighted norm.

The statements assume `0 ≤ Mw`, `0 ≤ F₀`; a negative bound is vacuous (`wbound_of_neg`).
-/

@[expose] public noncomputable section

open Set Metric Filter Finset MeasureTheory
open scoped Topology

namespace KAM.Canonical

open KAM.Weighted

variable {n : ℕ} {D : Set (Fin n → ℂ)} {r s r' s' ρ σ Φ Mw F₀ : ℝ}
  {φ h f₀ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

private theorem realPt_mem' {s : ℝ} (hs : 0 < s) (x : Fin n → ℝ) {I : Fin n → ℂ}
    (hI : I ∈ polyNbhd D r) : ((fun j => (x j : ℂ)), I) ∈ Dom n D r s :=
  ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

private theorem continuous_realPt' : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
  continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)

/-! ### Sums in the weighted norm -/

/-- The coefficient of a sum of class members is the sum of the coefficients. -/
theorem coeff_add (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r s u)
    (hv : InClass D r s v) {I : Fin n → ℂ} (hI : I ∈ polyNbhd D r) (k : Fin n → ℤ) :
    coeff (fun z => u z + v z) I k = coeff u I k + coeff v I k := by
  have hchar : Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) :=
    (KAM.differentiable_character (-k)).continuous.comp continuous_realPt'
  have hcont : ∀ w : (Fin n → ℂ) × (Fin n → ℂ) → ℂ, InClass D r s w →
      Continuous fun x : Fin n → ℝ => KAM.character (-k) (fun j => (x j : ℂ)) •
        w (fun j => (x j : ℂ), I) := fun w hw =>
    hchar.smul (hw.differentiableOn.continuousOn.comp_continuous
      (continuous_realPt'.prodMk continuous_const) fun x => realPt_mem' hs x hI)
  unfold coeff KAM.torusCoeffW KAM.torusAverage
  simp only [smul_add]
  exact integral_add (KAM.integrableOn_unitCube_of_continuous (hcont u hu))
    (KAM.integrableOn_unitCube_of_continuous (hcont v hv))

/-- Subadditivity of the weighted norm. -/
theorem wbound_add (hs : 0 < s) {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {M N : ℝ}
    (hu : InClass D r s u) (hv : InClass D r s v) (hbu : WBound D r s u M)
    (hbv : WBound D r s v N) :
    WBound D r s (fun z => u z + v z) (M + N) := by
  intro I hI
  obtain ⟨hu1, hu2⟩ := hbu I hI
  obtain ⟨hv1, hv2⟩ := hbv I hI
  have hw : ∀ k : Fin n → ℤ, 0 ≤ modeWeight s k := fun k => (Real.exp_pos _).le
  have hle : ∀ k, ‖coeff (fun z => u z + v z) I k‖ * modeWeight s k ≤
      ‖coeff u I k‖ * modeWeight s k + ‖coeff v I k‖ * modeWeight s k := fun k => by
    rw [coeff_add hs hu hv hI, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (hw k)
  have hsum : WSummable (fun z => u z + v z) s I :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg _) (hw k)) hle (hu1.add hv1)
  refine ⟨hsum, ?_⟩
  calc wsum (fun z => u z + v z) s I
      ≤ ∑' k, (‖coeff u I k‖ * modeWeight s k + ‖coeff v I k‖ * modeWeight s k) :=
        Summable.tsum_le_tsum hle hsum (hu1.add hv1)
    _ = wsum u s I + wsum v s I := hu1.tsum_add hv1
    _ ≤ M + N := add_le_add hu2 hv2

/-! ### The bracket stays in the class -/

theorem fderiv_fun_const_mul (c : ℂ) (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    fderiv ℂ (fun z => c * f z) z = c • fderiv ℂ f z := by
  by_cases hc : c = 0
  · subst hc
    have h0 : fderiv ℂ (fun _ : (Fin n → ℂ) × (Fin n → ℂ) => (0 : ℂ)) z = 0 := fderiv_const_apply 0
    simp only [zero_mul, h0]
    exact (zero_smul ℂ (fderiv ℂ f z)).symm
  · let _ : Invertible c := invertibleOfNonzero hc
    exact fderiv_const_smul_of_invertible c (f := f)

/-- `{u, v} ∈ O(r, s)` for `u ∈ O(r, s)`, `v ∈ O(r', s')` and `r ≤ r'`, `s ≤ s'`. -/
theorem inClass_poissonBracket {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r s u)
    (hv : InClass D r' s' v) (hr : r ≤ r') (hs : s ≤ s') :
    InClass D r s (poissonBracket u v) := by
  have hv' : InClass D r s v :=
    ⟨hv.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hv.periodic j z (Dom_mono hr hs hz)⟩
  refine ⟨differentiableOn_poissonBracket (isOpen_Dom D r s) hu.differentiableOn
    hv'.differentiableOn, fun j z hz => ?_⟩
  have hper : ∀ w : (Fin n → ℂ) × (Fin n → ℂ) → ℂ, InClass D r s w →
      fderiv ℂ w (z.1 + Pi.single j 1, z.2) = fderiv ℂ w z := fun w hw => by
    have h2 : ∀ y : (Fin n → ℂ) × (Fin n → ℂ),
        y + (Pi.single j 1, 0) = (y.1 + Pi.single j 1, y.2) := fun y => Prod.ext rfl (add_zero _)
    have hev : (fun y : (Fin n → ℂ) × (Fin n → ℂ) => w (y + (Pi.single j 1, 0))) =ᶠ[nhds z] w :=
      Filter.eventually_of_mem ((isOpen_Dom D r s).mem_nhds hz) fun y hy => by
        beta_reduce; rw [h2 y]; exact hw.periodic j y hy
    have h1 : fderiv ℂ w (z + (Pi.single j 1, 0)) = fderiv ℂ w z := by
      rw [← fderiv_comp_add_right]
      exact hev.fderiv_eq
    rwa [h2 z] at h1
  simp only [poissonBracket, hper u hu, hper v hv']

/-! ### The terms of the series -/

/-- The `i`-th term of the remainder series `𝓡` of `bpN:p5:transform`. -/
def remTerm (φ h f₀ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (i : ℕ) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  (((i + 2).factorial : ℂ)⁻¹) * adPow φ (i + 1) (poissonBracket h φ) z +
    (((i + 1).factorial : ℂ)⁻¹) * adPow φ (i + 1) f₀ z

/-- The bracket `w = {h, φ}` lies in `O(r, s)`. -/
theorem ComposeData.bracket_class (hd : ComposeData D r s r' s' ρ σ Φ φ) (hh : InClass D r s h) :
    InClass D r s (poissonBracket h φ) :=
  inClass_poissonBracket hh hd.φ_class (by linarith [hd.hr, hd.hρ]) (by linarith [hd.hs, hd.hσ])

/-- The bound of the `i`-th term. -/
def remBound (Φ ρ σ Mw F₀ : ℝ) (i : ℕ) : ℝ :=
  (Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ (i + 1) * (Mw / ((i : ℝ) + 2) + F₀)

/-- `a_i ∈ O(r-ρ, s-σ)` with `|a_i| ≤ q^{i+1}(Mw/(i+2) + F₀)`. -/
theorem remTerm_bound (hd : ComposeData D r s r' s' ρ σ Φ φ) (hh : InClass D r s h)
    (hf : InClass D r s f₀) (hw : WBound D r s (poissonBracket h φ) Mw)
    (hf₀ : WBound D r s f₀ F₀) (i : ℕ) :
    InClass D (r - ρ) (s - σ) (remTerm φ h f₀ i) ∧
    WBound D (r - ρ) (s - σ) (remTerm φ h f₀ i) (remBound Φ ρ σ Mw F₀ i) := by
  obtain ⟨hc1, hb1⟩ := lieTerm_bound hd (hd.bracket_class hh) hw (i + 1)
  obtain ⟨hc2, hb2⟩ := lieTerm_bound hd hf hf₀ (i + 1)
  have hfac : (((i + 2).factorial : ℂ)⁻¹) = ((i : ℂ) + 2)⁻¹ * (((i + 1).factorial : ℂ)⁻¹) := by
    rw [Nat.factorial_succ (i + 1), Nat.cast_mul, mul_inv]
    push_cast
    ring
  have heq : remTerm φ h f₀ i = fun z =>
      ((i : ℂ) + 2)⁻¹ * (((i + 1).factorial : ℂ)⁻¹ * adPow φ (i + 1) (poissonBracket h φ) z) +
        (((i + 1).factorial : ℂ)⁻¹ * adPow φ (i + 1) f₀ z) := by
    funext z
    simp only [remTerm, hfac]
    ring
  have hn : ‖((i : ℂ) + 2)⁻¹‖ = 1 / ((i : ℝ) + 2) := by
    have : ((i : ℂ) + 2) = (((i : ℝ) + 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  have hs0 : 0 < s - σ := by linarith [hd.hσs]
  rw [heq]
  have hc1' := inClass_const_mul (((i : ℂ) + 2)⁻¹) hc1
  refine ⟨⟨hc1'.differentiableOn.add hc2.differentiableOn, fun j z hz => ?_⟩, ?_⟩
  · simp only [hc1'.periodic j z hz, hc2.periodic j z hz]
  · have := wbound_add hs0 hc1' hc2 (wbound_const_mul (((i : ℂ) + 2)⁻¹) hb1) hb2
    rw [hn] at this
    refine this.mono le_rfl le_rfl (le_of_eq ?_)
    unfold remBound
    ring

/-! ### The sum of the series -/

section Series

variable (hd : ComposeData D r s r' s' ρ σ Φ φ) (hh : InClass D r s h) (hf : InClass D r s f₀)
  (hw : WBound D r s (poissonBracket h φ) Mw) (hf₀ : WBound D r s f₀ F₀)
  (hM : 0 ≤ Mw) (hF : 0 ≤ F₀)
include hd hM hF

omit hh hf hw hf₀ in
theorem remBound_summable : Summable (remBound Φ ρ σ Mw F₀) := by
  obtain ⟨h0, -, hq⟩ := q_facts (η := 2 * Φ / (ρ * σ)) hd.eta_nonneg (hd.eta_le.trans (by norm_num))
  have hg : Summable fun i : ℕ => (Real.exp 1 * (2 * Φ / (ρ * σ)) / 4) ^ (i + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 hq)
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (hg.mul_right (Mw / 2 + F₀))
  · unfold remBound
    positivity
  · unfold remBound
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 _)
    have : Mw / ((i : ℝ) + 2) ≤ Mw / 2 :=
      div_le_div_of_nonneg_left hM (by norm_num) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    linarith

omit hh hf hw hf₀ in
theorem remBound_tsum_le :
    ∑' i, remBound Φ ρ σ Mw F₀ i ≤ (2 * Φ / (ρ * σ)) / (1 - 2 * Φ / (ρ * σ)) * (Mw / 2 + F₀) := by
  obtain ⟨h0, hqη, hq⟩ := q_facts (η := 2 * Φ / (ρ * σ)) hd.eta_nonneg
    (hd.eta_le.trans (by norm_num))
  set q := Real.exp 1 * (2 * Φ / (ρ * σ)) / 4 with hqdef
  set η := 2 * Φ / (ρ * σ) with hη
  have hη1 : η < 1 := by linarith [hd.eta_le]
  have hg : Summable fun i : ℕ => q ^ (i + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 hq)
  have hle : ∑' i, remBound Φ ρ σ Mw F₀ i ≤ ∑' i : ℕ, q ^ (i + 1) * (Mw / 2 + F₀) := by
    refine Summable.tsum_le_tsum (fun i => ?_) (remBound_summable hd hM hF) (hg.mul_right _)
    unfold remBound
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 _)
    have : Mw / ((i : ℝ) + 2) ≤ Mw / 2 :=
      div_le_div_of_nonneg_left hM (by norm_num) (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    linarith
  have hsum : ∑' i : ℕ, q ^ (i + 1) * (Mw / 2 + F₀) = q / (1 - q) * (Mw / 2 + F₀) := by
    rw [tsum_mul_right]
    simp_rw [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_lt_one h0 hq]
    ring
  refine hle.trans (hsum.le.trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

include hh hf hw hf₀

omit hM hF in
/-- Pointwise domination of the terms on `𝒟_{r-ρ, s-σ}`. -/
theorem remTerm_norm_le (i : ℕ) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    ‖remTerm φ h f₀ i z‖ ≤ remBound Φ ρ σ Mw F₀ i :=
  sup_le_wbound (remTerm_bound hd hh hf hw hf₀ i).1 (remTerm_bound hd hh hf hw hf₀ i).2 z hz

theorem remSeries_hasSum {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ Dom n D (r - ρ) (s - σ)) :
    HasSum (fun i => remTerm φ h f₀ i z) (∑' i, remTerm φ h f₀ i z) :=
  (Summable.of_norm_bounded (remBound_summable hd hM hF) fun i =>
    remTerm_norm_le hd hh hf hw hf₀ i hz).hasSum

/-- The sum of the remainder series lies in the class `O(r-ρ, s-σ)`. -/
theorem remSeries_class : InClass D (r - ρ) (s - σ) (fun z => ∑' i, remTerm φ h f₀ i z) := by
  have hterm := remTerm_bound hd hh hf hw hf₀
  have hbd : ∀ i, ∀ z ∈ Dom n D (r - ρ) (s - σ), ‖remTerm φ h f₀ i z‖ ≤ remBound Φ ρ σ Mw F₀ i :=
    fun i z hz => remTerm_norm_le hd hh hf hw hf₀ i hz
  refine ⟨?_, fun j z hz => ?_⟩
  · refine (uniform_limit_holomorphic (isOpen_Dom _ _ _) (K := fun N z =>
      ∑ i ∈ range N, remTerm φ h f₀ i z) (fun N => ?_)
      (tendstoUniformlyOn_tsum_nat (remBound_summable hd hM hF) hbd)).1
    exact DifferentiableOn.fun_sum fun i _ => (hterm i).1.differentiableOn
  · exact tsum_congr fun i => by rw [(hterm i).1.periodic j z hz]

/-- `|𝓡|_{r-ρ,s-σ} ≤ ∑ q^{i+1}(Mw/(i+2) + F₀)`. -/
theorem remSeries_bound : WBound D (r - ρ) (s - σ) (fun z => ∑' i, remTerm φ h f₀ i z)
    (∑' i, remBound Φ ρ σ Mw F₀ i) :=
  wbound_tsum (by linarith [hd.hσs]) (fun i => (remTerm_bound hd hh hf hw hf₀ i).1)
    (fun i => (remTerm_bound hd hh hf hw hf₀ i).2) (remBound_summable hd hM hF)

/-- The tails of the remainder series are small in the weighted norm. -/
theorem remSeries_tail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N, WBound D (r - ρ) (s - σ)
    (fun z => (∑' i, remTerm φ h f₀ i z) - ∑ i ∈ range N', remTerm φ h f₀ i z) ε := by
  intro ε hε
  have hsum := remBound_summable hd hM hF
  have hlim := _root_.tendsto_sum_nat_add (remBound Φ ρ σ Mw F₀)
  obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨N, fun N' hN' => ?_⟩
  have h := wbound_tsum (by linarith [hd.hσs]) (fun i => (remTerm_bound hd hh hf hw hf₀ (i + N')).1)
    (fun i => (remTerm_bound hd hh hf hw hf₀ (i + N')).2) ((summable_nat_add_iff N').2 hsum)
  refine wbound_congr (by linarith [hd.hσs]) (fun z hz => ?_) (h.mono le_rfl le_rfl (hN N' hN').le)
  rw [← (remSeries_hasSum hd hh hf hw hf₀ hM hF hz).summable.sum_add_tsum_nat_add N',
    add_sub_cancel_left]

end Series

end KAM.Canonical

end
