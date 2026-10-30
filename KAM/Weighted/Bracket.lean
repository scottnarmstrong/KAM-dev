/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.Algebra
public import KAM.Weighted.Cauchy
public import KAM.Canonical.Setting
import KAM.Strip.FourierDerivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The Poisson bracket in the weighted norm (`bpN:p4:bracket`)

Lemma B.4 of blueprint-N Part 4 (`m = n`): for `u ∈ O(r₀, s₀)` and `v ∈ O(r, s)` with bounds
`Mu`, `Mv`, the bracket `{u, v} = ∑ᵢ (∂θᵢu ∂Iᵢv - ∂Iᵢu ∂θᵢv)` lies in `O(r - ρ, s - σ)` with

`|{u, v}|_{r-ρ,s-σ} ≤ e⁻¹ (1/((r₀ - r + ρ) σ) + 1/((s₀ - s + σ) ρ)) Mu Mv`.

Pointwise in `I`: the coefficients of a finite sum are the sums of coefficients (`wsum_sum_le`),
each product is handled by `coeff_mul`, and `∑ᵢ aᵢ bᵢ ≤ (∑ᵢ aᵢ) max bᵢ` is combined with
`cauchy_theta` (summed over `j` inside the supremum) and `cauchy_action` (global).
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Weighted

variable {n : ℕ}

/-- Restriction of the class to smaller widths. -/
theorem inClass_mono {D : Set (Fin n → ℂ)} {r₀ s₀ r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) :
    InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

theorem wsum_nonneg (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (s : ℝ) (I : Fin n → ℂ) :
    0 ≤ wsum f s I :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-- Along the real angles a class function is continuous. -/
theorem continuous_real_slice {D : Set (Fin n → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hu : InClass D r s u) {I : Fin n → ℂ}
    (hI : I ∈ polyNbhd D r) : Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
  hu.differentiableOn.continuousOn.comp_continuous
    ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).prodMk
      continuous_const) fun x => ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

/-- The weighted sum is subadditive for finite linear combinations (coefficients are linear). -/
private theorem wsum_sum_le {ι : Type*} [Fintype ι] {s : ℝ} {I : Fin n → ℂ} (a : ι → ℂ)
    (g : ι → (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (hc : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun l => (x l : ℂ), I))
    (hg : ∀ j, WSummable (g j) s I) :
    WSummable (fun z => ∑ j, a j * g j z) s I ∧
      wsum (fun z => ∑ j, a j * g j z) s I ≤ ∑ j, ‖a j‖ * wsum (g j) s I := by
  have hcoeff : ∀ k, coeff (fun z => ∑ j, a j * g j z) I k = ∑ j, a j * coeff (g j) I k :=
    fun k => KAM.torusCoeff_finset_sum_mul Finset.univ hc a k
  have hterm : ∀ k, ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k ≤
      ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) := fun k => by
    rw [hcoeff]
    calc ‖∑ j, a j * coeff (g j) I k‖ * modeWeight s k
        ≤ (∑ j, ‖a j * coeff (g j) I k‖) * modeWeight s k :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
      _ = ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, mul_assoc]
  have hsum : Summable fun k : Fin n → ℤ =>
      ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) :=
    summable_sum fun j _ => (hg j).mul_left _
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k :=
    fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsum, ?_⟩
  unfold wsum
  calc ∑' k, ‖coeff (fun z => ∑ j, a j * g j z) I k‖ * modeWeight s k
      ≤ ∑' k, ∑ j, ‖a j‖ * (‖coeff (g j) I k‖ * modeWeight s k) :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le hnn hterm hsum) hsum
    _ = ∑ j, ‖a j‖ * ∑' k, ‖coeff (g j) I k‖ * modeWeight s k := by
        rw [Summable.tsum_finsetSum fun j _ => (hg j).mul_left _]
        exact Finset.sum_congr rfl fun j _ => tsum_mul_left

/-- The bracket as a signed sum over `Fin n ⊕ Fin n`. -/
private theorem poissonBracket_eq_sum (u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) :
    KAM.Canonical.poissonBracket u v = fun z =>
      ∑ j : Fin n ⊕ Fin n, (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)) j) *
        (Sum.elim (fun i z => dtheta i u z * dI i v z)
          (fun i z => dI i u z * dtheta i v z) j) z := by
  funext z
  rw [Fintype.sum_sum_type]
  simp only [KAM.Canonical.poissonBracket, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
    dtheta, dI, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]

-- `hρr : ρ < r` is part of the signature (not needed: for `r ≤ ρ` the region `V_{r-ρ} D` is empty).
set_option linter.unusedVariables false in
/-- `bpN:p4:bracket` (Lemma B.4): `|{u, v}|_{r-ρ,s-σ}` in terms of `|u|_{r₀,s₀}` and `|v|_{r,s}`. -/
theorem wbound_bracket {D : Set (Fin n → ℂ)} {r₀ s₀ r s ρ σ Mu Mv : ℝ}
    {u v : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    (hu : InClass D r₀ s₀ u) (hv : InClass D r s v) (hbu : WBound D r₀ s₀ u Mu)
    (hbv : WBound D r s v Mv) (hρ : 0 < ρ) (hρr : ρ < r) (hσ : 0 < σ) (hσs : σ < s)
    (h1 : r - ρ < r₀) (h2 : s - σ < s₀) :
    InClass D (r - ρ) (s - σ) (KAM.Canonical.poissonBracket u v) ∧
    WBound D (r - ρ) (s - σ) (KAM.Canonical.poissonBracket u v)
      (1 / Real.exp 1 * (1 / ((r₀ - r + ρ) * σ) + 1 / ((s₀ - s + σ) * ρ)) * Mu * Mv) := by
  have hs : 0 < s := hσ.trans hσs
  have hs' : 0 < s - σ := sub_pos.mpr hσs
  have hu' : InClass D (r - ρ) (s - σ) u := inClass_mono hu h1.le h2.le
  have hv' : InClass D (r - ρ) (s - σ) v := inClass_mono hv (by linarith) (by linarith)
  have hs₀ : 0 < s₀ := hs'.trans h2
  have hd1 : 0 < r₀ - r + ρ := by linarith
  have hd2 : 0 < s₀ - s + σ := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have e1 : r₀ - (r - ρ) = r₀ - r + ρ := by ring
  have e2 : s₀ - (s - σ) = s₀ - s + σ := by ring
  have e3 : s - (s - σ) = σ := by ring
  have e4 : r - (r - ρ) = ρ := by ring
  have hθu := cauchy_theta hu hbu hs' h2
  have hθv := cauchy_theta hv hbv hs' (by linarith : s - σ < s)
  have hau := cauchy_action hs₀ hu hbu h1
  have hav := cauchy_action hs hv hbv (by linarith : r - ρ < r)
  rw [e1] at hau
  rw [e4] at hav
  rw [e2] at hθu
  rw [e3] at hθv
  have key : ∀ I ∈ polyNbhd D (r - ρ), WSummable (KAM.Canonical.poissonBracket u v) (s - σ) I ∧
      wsum (KAM.Canonical.poissonBracket u v) (s - σ) I ≤
        1 / Real.exp 1 * (1 / ((r₀ - r + ρ) * σ) + 1 / ((s₀ - s + σ) * ρ)) * Mu * Mv := by
    intro I hI
    have hIu : I ∈ polyNbhd D r₀ := polyNbhd_mono h1.le hI
    have hIv : I ∈ polyNbhd D r := polyNbhd_mono (by linarith) hI
    have hMu : 0 ≤ Mu := (wsum_nonneg u s₀ I).trans (hbu I hIu).2
    have hMv : 0 ≤ Mv := (wsum_nonneg v s I).trans (hbv I hIv).2
    obtain ⟨hθu_s, hθu_sum⟩ := hθu.1 I hIu
    obtain ⟨hθv_s, hθv_sum⟩ := hθv.1 I hIv
    have hdIu : ∀ i, WBound D (r - ρ) (s - σ) (dI i u) (Mu / (r₀ - r + ρ)) := fun i =>
      (hau i).mono le_rfl h2.le le_rfl
    have hdIv : ∀ i, WBound D (r - ρ) (s - σ) (dI i v) (Mv / ρ) := fun i =>
      (hav i).mono le_rfl (by linarith) le_rfl
    have hdθu : ∀ i, InClass D (r - ρ) (s - σ) (dtheta i u) := fun i =>
      inClass_fderiv_apply hu' (Pi.single i 1, 0)
    have hdθv : ∀ i, InClass D (r - ρ) (s - σ) (dtheta i v) := fun i =>
      inClass_fderiv_apply hv' (Pi.single i 1, 0)
    have hdIu' : ∀ i, InClass D (r - ρ) (s - σ) (dI i u) := fun i =>
      inClass_fderiv_apply hu' (0, Pi.single i 1)
    have hdIv' : ∀ i, InClass D (r - ρ) (s - σ) (dI i v) := fun i =>
      inClass_fderiv_apply hv' (0, Pi.single i 1)
    have hP := fun i => coeff_mul hs' (hdθu i) (hdIv' i) hI (hθu_s i) (hdIv i I hI).1
    have hQ := fun i => coeff_mul hs' (hdIu' i) (hdθv i) hI (hdIu i I hI).1 (hθv_s i)
    obtain ⟨hws, hwle⟩ := wsum_sum_le (s := s - σ) (I := I)
      (Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)))
      (Sum.elim (fun i z => dtheta i u z * dI i v z) (fun i z => dI i u z * dtheta i v z))
      (fun j => by
        rcases j with i | i
        · exact continuous_real_slice hs' (hP i).1 hI
        · exact continuous_real_slice hs' (hQ i).1 hI)
      (fun j => by
        rcases j with i | i
        · exact (hP i).2.2.2.1
        · exact (hQ i).2.2.2.1)
    rw [← poissonBracket_eq_sum] at hws hwle
    refine ⟨hws, hwle.trans ?_⟩
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, norm_one, norm_neg, one_mul]
    -- the two sums
    have hA : ∑ i, wsum (fun z => dtheta i u z * dI i v z) (s - σ) I ≤
        Mu / (Real.exp 1 * (s₀ - s + σ)) * (Mv / ρ) := by
      calc ∑ i, wsum (fun z => dtheta i u z * dI i v z) (s - σ) I
          ≤ ∑ i, wsum (dtheta i u) (s - σ) I * (Mv / ρ) :=
            Finset.sum_le_sum fun i _ =>
              (hP i).2.2.2.2.trans (mul_le_mul_of_nonneg_left (hdIv i I hI).2
                (wsum_nonneg _ _ _))
        _ = (∑ i, wsum (dtheta i u) (s - σ) I) * (Mv / ρ) := by rw [Finset.sum_mul]
        _ ≤ Mu / (Real.exp 1 * (s₀ - s + σ)) * (Mv / ρ) := by
            refine mul_le_mul_of_nonneg_right (hθu_sum.trans ?_) (by positivity)
            exact div_le_div_of_nonneg_right (hbu I hIu).2 (by positivity)
    have hB : ∑ i, wsum (fun z => dI i u z * dtheta i v z) (s - σ) I ≤
        Mu / (r₀ - r + ρ) * (Mv / (Real.exp 1 * σ)) := by
      calc ∑ i, wsum (fun z => dI i u z * dtheta i v z) (s - σ) I
          ≤ ∑ i, Mu / (r₀ - r + ρ) * wsum (dtheta i v) (s - σ) I :=
            Finset.sum_le_sum fun i _ =>
              (hQ i).2.2.2.2.trans (mul_le_mul_of_nonneg_right (hdIu i I hI).2
                (wsum_nonneg _ _ _))
        _ = Mu / (r₀ - r + ρ) * ∑ i, wsum (dtheta i v) (s - σ) I := by rw [Finset.mul_sum]
        _ ≤ Mu / (r₀ - r + ρ) * (Mv / (Real.exp 1 * σ)) := by
            refine mul_le_mul_of_nonneg_left (hθv_sum.trans ?_) (by positivity)
            exact div_le_div_of_nonneg_right (hbv I hIv).2 (by positivity)
    refine (add_le_add hA hB).trans (le_of_eq ?_)
    field_simp
    ring
  refine ⟨⟨?_, ?_⟩, key⟩
  · exact KAM.Canonical.differentiableOn_poissonBracket (isOpen_Dom D (r - ρ) (s - σ))
      hu'.differentiableOn hv'.differentiableOn
  · intro j z hz
    have hper : ∀ (w : (Fin n → ℂ) × (Fin n → ℂ) → ℂ), InClass D (r - ρ) (s - σ) w →
        ∀ a, fderiv ℂ w (z.1 + Pi.single j 1, z.2) a = fderiv ℂ w z a := fun w hw a =>
      (inClass_fderiv_apply hw a).periodic j z hz
    simp only [KAM.Canonical.poissonBracket, hper u hu', hper v hv']

end KAM.Weighted

end
