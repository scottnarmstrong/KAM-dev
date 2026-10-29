/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Defs
import KAM.Head.CoverMono
import KAM.Head.HeadQ
import KAM.Head.MainMeasure
import KAM.Head.Parameters

/-!
# The HEAD assembly from the constants of G1 to G3

Blueprint Part 4, the proof of `bp:p0:head` (steps `step:p4:head-empty`, `step:p4:head-constants`,
`step:p4:head-negative`, `step:p4:head-positive`, `step:p4:head-zero`), as the conditional helper
`KAM.Head.head_of_gValid`. The premise `GValid`
carries the constants of the frozen G1, G2 and G3; the HEAD provider supplies it. This module
imports neither a frozen theorem nor a provider.

* `KAM.Head.head_empty` is `step:p4:head-empty`: `F_∅ = ∅`.
* `KAM.Head.headC` is `C = max (1, A₀ c_*^{1/2}, C_meas c_*^{-1/4})` of `step:p4:head-constants`,
  with the three facts about it that the proof uses (`one_le_headC`, `A0_mul_le_headC`,
  `Cmeas_div_le_headC`). The other constant is `ε₀ = c_*`.
* `KAM.Head.nonneg_of_bound_nonempty` (in `KAM.Head.HeadQ`) is `step:p4:head-negative`.
* `KAM.Head.head_positive` is `step:p4:head-positive`: `γ = (ε/c_*)^{1/4}`, `(SA)`, cover
  monotonicity and `main_measure`.
* `KAM.Head.head_zero` is `step:p4:head-zero`: `(SA)` holds for every `γ ∈ (0, 1]`, so the measure
  is `0`.
* `KAM.Head.head_of_gValid` is the assembly.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Head

variable {n : ℕ} {τ s₀ r₀ Lh : ℝ} {B : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ}
  {f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ε : ℝ} {gc : GConsts}

/-! ### Step `head-empty` -/

/-- Blueprint `step:p4:head-empty`: if `B = ∅`, then `F_B = ∅`, and `C = ε₀ = 1` work. -/
theorem head_empty (hB : B = ∅) : HeadConclusion τ s₀ r₀ B h := by
  subst hB
  refine ⟨1, 1, one_pos, one_pos, fun f ε _ _ _ _ _ => ?_⟩
  simp [KAM.fundamentalDomain]

/-! ### Step `head-constants` -/

/-- Blueprint `step:p4:head-constants`: `C = max (1, A₀ c_*^{1/2}, C_meas c_*^{-1/4})`. -/
def headC (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh CB : ℝ)
    (gc : GConsts) : ℝ :=
  max 1 (max (A0 n τ s₀ r₀ gc * cStar τ s₀ r₀ B h Lh gc ^ ((1 : ℝ) / 2))
    (Cmeas n Lh CB gc.C3 * cStar τ s₀ r₀ B h Lh gc ^ (-((1 : ℝ) / 4))))

/-- `x^{1/2} = (x^{1/4})²` for `x ≥ 0`. -/
theorem rpow_half_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((1 : ℝ) / 2) = (x ^ ((1 : ℝ) / 4)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- `x^{-1/4} = (x^{1/4})⁻¹` for `x ≥ 0`. -/
theorem rpow_neg_quarter_eq {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-((1 : ℝ) / 4)) = (x ^ ((1 : ℝ) / 4))⁻¹ :=
  Real.rpow_neg hx _

/-- `C_meas ≥ 0`. -/
theorem Cmeas_nonneg (n : ℕ) (Lh CB C3 : ℝ) : 0 ≤ Cmeas n Lh CB C3 := by
  have h1 := CBplus_nonneg CB
  have h2 := (Parameters.Lplus_pos Lh).le
  have h3 : 0 ≤ max C3 0 := le_max_right _ _
  unfold Cmeas
  have h4 : 0 ≤ Lplus Lh ^ n * max C3 0 := mul_nonneg (pow_nonneg h2 n) h3
  have h5 : 0 ≤ (9 / 2 : ℝ) ^ n := by positivity
  nlinarith [mul_nonneg h5 (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h1) h4)]

/-- `1 ≤ C`. -/
theorem one_le_headC {CB : ℝ} {gc : GConsts} :
    1 ≤ headC τ s₀ r₀ B h Lh CB gc := le_max_left _ _

/-- `A₀ c_*^{1/2} ≤ C`, with `c_*^{1/2}` written as `(c_*^{1/4})²`. -/
theorem A0_mul_le_headC {CB : ℝ} (hcs : 0 < cStar τ s₀ r₀ B h Lh gc) :
    A0 n τ s₀ r₀ gc * (cStar τ s₀ r₀ B h Lh gc ^ ((1 : ℝ) / 4)) ^ 2 ≤
      headC τ s₀ r₀ B h Lh CB gc := by
  rw [← rpow_half_eq hcs.le]
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- `C_meas c_*^{-1/4} ≤ C`, with `c_*^{-1/4}` written as `(c_*^{1/4})⁻¹`. -/
theorem Cmeas_div_le_headC {CB : ℝ} (hcs : 0 < cStar τ s₀ r₀ B h Lh gc) :
    Cmeas n Lh CB gc.C3 / cStar τ s₀ r₀ B h Lh gc ^ ((1 : ℝ) / 4) ≤
      headC τ s₀ r₀ B h Lh CB gc := by
  rw [div_eq_mul_inv, ← rpow_neg_quarter_eq hcs.le]
  exact (le_max_right _ _).trans' (le_max_right _ _)

/-! ### Step `head-positive` -/

/-- Blueprint `step:p4:head-positive`: for `0 < ε ≤ c_*`, put `γ = (ε/c_*)^{1/4}`. Then `(SA)`
holds, `η₀ = A₀ c_*^{1/2} ε^{1/2} ≤ C √ε`, and `main_measure` with `kamCover_mono` gives
`meas (F_B ∖ 𝒦(C √ε)) ≤ C_meas γ ≤ C ε^{1/4}`. -/
theorem head_positive {CB C : ℝ} (hD : Data τ s₀ r₀ B h Lh) (hCB : Layer B CB)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hP : Pert s₀ r₀ B f ε) (hne : B.Nonempty)
    (hε : 0 < ε) (hεc : ε ≤ cStar τ s₀ r₀ B h Lh gc)
    (hC1 : A0 n τ s₀ r₀ gc * (cStar τ s₀ r₀ B h Lh gc ^ ((1 : ℝ) / 4)) ^ 2 ≤ C)
    (hC2 : Cmeas n Lh CB gc.C3 / cStar τ s₀ r₀ B h Lh gc ^ ((1 : ℝ) / 4) ≤ C) :
    volume (fundamentalDomain B \ kamCover h f B r₀ τ (C * Real.sqrt ε)) ≤
      ENNReal.ofReal (C * ε ^ ((1 : ℝ) / 4)) := by
  set cs := cStar τ s₀ r₀ B h Lh gc with hcs_def
  have hcs : 0 < cs := Parameters.cStar_pos hD.two_le hD.s₀_pos hD.r₀_pos hgc.toPos
  set a := ε ^ ((1 : ℝ) / 4) with ha_def
  set b := cs ^ ((1 : ℝ) / 4) with hb_def
  have ha : 0 < a := Real.rpow_pos_of_pos hε _
  have hb : 0 < b := Real.rpow_pos_of_pos hcs _
  have ha4 : a ^ 4 = ε := by
    rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    norm_num
  have hb4 : b ^ 4 = cs := by
    rw [hb_def, ← Real.rpow_natCast, ← Real.rpow_mul hcs.le]
    norm_num
  have hab : a ≤ b := by
    by_contra hlt
    have hlt' := pow_lt_pow_left₀ (not_le.1 hlt) hb.le (by norm_num : (4 : ℕ) ≠ 0)
    rw [ha4, hb4] at hlt'
    exact absurd hεc (not_le.2 hlt')
  set γ := a / b with hγ_def
  have hγ : 0 < γ := div_pos ha hb
  have hγ4 : γ ^ 4 = ε / cs := by rw [hγ_def, div_pow, ha4, hb4]
  have hSA : SA τ s₀ r₀ B h Lh gc ε γ := by
    refine ⟨hγ, (div_le_one hb).2 hab, hε.le, ?_⟩
    rw [hγ4, mul_div_cancel₀ _ hcs.ne']
  -- `η₀ = A₀ a² b²` and `√ε = a²`
  have hsqrt : Real.sqrt ε = a ^ 2 := by
    rw [← ha4, show a ^ 4 = a ^ 2 * a ^ 2 by ring, Real.sqrt_mul_self (sq_nonneg a)]
  have heta : eta0 n τ s₀ r₀ gc ε γ = A0 n τ s₀ r₀ gc * b ^ 2 * a ^ 2 := by
    unfold eta0
    rw [hγ_def, ← ha4]
    field_simp
  have hκ : eta0 n τ s₀ r₀ gc ε γ ≤ C * Real.sqrt ε := by
    rw [heta, hsqrt]
    exact mul_le_mul_of_nonneg_right hC1 (sq_nonneg a)
  have hmm := main_measure hD hCB hP hgc hSA hne
  refine (measure_mono (Set.sdiff_subset_sdiff_right
    (kamCover_mono h f (subset_refl B) r₀ τ hκ))).trans (hmm.trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  calc Cmeas n Lh CB gc.C3 * γ = (Cmeas n Lh CB gc.C3 / b) * a := by rw [hγ_def]; ring
    _ ≤ C * a := mul_le_mul_of_nonneg_right hC2 ha.le

/-! ### Step `head-zero` -/

/-- Blueprint `step:p4:head-zero`: if `ε = 0`, then `(SA)` holds for every `γ ∈ (0, 1]` with
`η₀ = 0`, so `meas (F_B ∖ 𝒦(0)) ≤ C_meas γ` for every such `γ`, and the measure is `0`. -/
theorem head_zero {CB C : ℝ} (hD : Data τ s₀ r₀ B h Lh) (hCB : Layer B CB)
    (hgc : GValid τ s₀ r₀ B h Lh gc) (hP : Pert s₀ r₀ B f ε) (hne : B.Nonempty)
    (hε : ε = 0) :
    volume (fundamentalDomain B \ kamCover h f B r₀ τ (C * Real.sqrt ε)) ≤
      ENNReal.ofReal (C * ε ^ ((1 : ℝ) / 4)) := by
  subst hε
  have hcs : 0 < cStar τ s₀ r₀ B h Lh gc :=
    Parameters.cStar_pos hD.two_le hD.s₀_pos hD.r₀_pos hgc.toPos
  have hCm := Cmeas_nonneg n Lh CB gc.C3
  have key : ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
      volume (fundamentalDomain B \ kamCover h f B r₀ τ 0) ≤
        ENNReal.ofReal (Cmeas n Lh CB gc.C3 * γ) := by
    intro γ hγ hγ1
    have hSA : SA τ s₀ r₀ B h Lh gc 0 γ := ⟨hγ, hγ1, le_rfl, by positivity⟩
    have := main_measure hD hCB hP hgc hSA hne
    simpa [eta0] using this
  rw [Real.sqrt_zero, mul_zero, Real.zero_rpow (by norm_num : ((1 : ℝ) / 4) ≠ 0), mul_zero,
    ENNReal.ofReal_zero]
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := NNReal.coe_pos.2 hδ
  have hγ : 0 < min 1 ((δ : ℝ) / (Cmeas n Lh CB gc.C3 + 1)) :=
    lt_min one_pos (div_pos hδ' (by linarith))
  refine (key _ hγ (min_le_left _ _)).trans ?_
  rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Cmeas n Lh CB gc.C3 * min 1 ((δ : ℝ) / (Cmeas n Lh CB gc.C3 + 1))
      ≤ Cmeas n Lh CB gc.C3 * ((δ : ℝ) / (Cmeas n Lh CB gc.C3 + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hCm
    _ ≤ δ := by
        rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
        nlinarith

/-! ### The assembly -/

/-- Blueprint `bp:p0:head`, steps `head-empty` … `head-zero`: HEAD for the data, given constants
of the frozen G1, G2, G3 (conditional helper; the provider supplies `gc`). -/
theorem head_of_gValid {CB : ℝ} (hD : Data τ s₀ r₀ B h Lh) (hCB : Layer B CB)
    (hgc : GValid τ s₀ r₀ B h Lh gc) : HeadConclusion τ s₀ r₀ B h := by
  by_cases hB : B = ∅
  · exact head_empty hB
  have hne : B.Nonempty := Set.nonempty_iff_ne_empty.2 hB
  have hcs : 0 < cStar τ s₀ r₀ B h Lh gc :=
    Parameters.cStar_pos hD.two_le hD.s₀_pos hD.r₀_pos hgc.toPos
  refine ⟨headC τ s₀ r₀ B h Lh CB gc, cStar τ s₀ r₀ B h Lh gc,
    one_pos.trans_le one_le_headC, hcs, ?_⟩
  intro f ε hf hper hreal hbound hε
  have hP : Pert s₀ r₀ B f ε := ⟨hf, hper, hreal, hbound⟩
  have hε0 : 0 ≤ ε := nonneg_of_bound_nonempty hD.s₀_pos hD.r₀_pos hne hbound
  rcases hε0.eq_or_lt with h0 | hpos
  · exact head_zero hD hCB hgc hP hne h0.symm
  · exact head_positive hD hCB hgc hP hne hpos hε (A0_mul_le_headC hcs)
      (Cmeas_div_le_headC hcs)

end KAM.Head

end
