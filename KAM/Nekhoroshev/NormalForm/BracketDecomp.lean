/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.NormalForm.Setting
public import KAM.Weighted.Bracket
import KAM.Strip.FourierDerivative
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The bracket with a decomposed `g` (`bpN:p6:bracket-g`)

For `g = ∑ⱼ gⱼ` with `gⱼ ∈ O(rⱼ, sⱼ)`, `|gⱼ| ≤ Mⱼ`, and `φ ∈ O(r, s)` with `|φ| ≤ Φ`, the bracket
`{g, φ}` lies in `O(r-ρ, s-σ)` with `|{g, φ}| ≤ (2/(eρσ)) |g|_* Φ`. Per term `wbound_bracket`; the
decomposition weights satisfy
`1/e (1/((rⱼ-r+ρ)σ) + 1/((sⱼ-s+σ)ρ)) = 2/(eρσ) · ½(ρ/(rⱼ-r+ρ) + σ/(sⱼ-s+σ))`.
Design `docs/tracks/N/design/PART67-LEAN-DESIGN.md`, package N6-3.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.NormalForm

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

private theorem wsum_nonneg' (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (s : ℝ) (I : Fin n → ℂ) :
    0 ≤ wsum f s I :=
  tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

private theorem continuous_slice {D : Set (Fin n → ℂ)} {r s : ℝ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hs : 0 < s) (hu : InClass D r s u) {I : Fin n → ℂ}
    (hI : I ∈ polyNbhd D r) : Continuous fun x : Fin n → ℝ => u (fun j => (x j : ℂ), I) :=
  hu.differentiableOn.continuousOn.comp_continuous
    ((continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)).prodMk
      continuous_const) fun x => ⟨KAM.ofReal_mem_complexStrip hs x, hI⟩

/-- A finite sum (on real slices) of weighted-summable functions is weighted-summable, and its
weighted sum is bounded by the sum of the weighted sums. -/
private theorem wsum_finset_sum_le {N : ℕ} {s : ℝ} {I : Fin n → ℂ}
    {u : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (g : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (hu : ∀ x : Fin n → ℝ, u (fun l => (x l : ℂ), I) = ∑ j, g j (fun l => (x l : ℂ), I))
    (hc : ∀ j, Continuous fun x : Fin n → ℝ => g j (fun l => (x l : ℂ), I))
    (hg : ∀ j, WSummable (g j) s I) :
    WSummable u s I ∧ wsum u s I ≤ ∑ j, wsum (g j) s I := by
  have hcoeff : ∀ k, coeff u I k = ∑ j, coeff (g j) I k := fun k => by
    have := KAM.torusCoeff_finset_sum_mul Finset.univ hc (fun _ => (1 : ℂ)) k
    simp only [one_mul] at this
    simp only [coeff, KAM.torusCoeffW_complex]
    rw [show (fun x : Fin n → ℝ => u (fun l => (x l : ℂ), I)) =
      fun x => ∑ j, g j (fun l => (x l : ℂ), I) from funext hu]
    exact this
  have hterm : ∀ k, ‖coeff u I k‖ * modeWeight s k ≤
      ∑ j, ‖coeff (g j) I k‖ * modeWeight s k := fun k => by
    rw [hcoeff, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le
  have hsum : Summable fun k : Fin n → ℤ => ∑ j, ‖coeff (g j) I k‖ * modeWeight s k :=
    summable_sum fun j _ => hg j
  have hnn : ∀ k : Fin n → ℤ, 0 ≤ ‖coeff u I k‖ * modeWeight s k :=
    fun k => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsum, ?_⟩
  unfold wsum
  calc ∑' k, ‖coeff u I k‖ * modeWeight s k
      ≤ ∑' k, ∑ j, ‖coeff (g j) I k‖ * modeWeight s k :=
        Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le hnn hterm hsum) hsum
    _ = ∑ j, ∑' k, ‖coeff (g j) I k‖ * modeWeight s k := Summable.tsum_finsetSum fun j _ => hg j

/-- The bracket `{g, φ}` for `g = ∑ gⱼ` is the sum of the brackets on `Dom r s`. -/
private theorem poissonBracket_sum {D : Set (Fin n → ℂ)} {r s : ℝ} {N : ℕ}
    (gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (hd : ∀ j, DifferentiableOn ℂ (gj j) (Dom n D r s)) {z : (Fin n → ℂ) × (Fin n → ℂ)}
    (hz : z ∈ Dom n D r s) :
    poissonBracket (fun z => ∑ j, gj j z) φ z = ∑ j, poissonBracket (gj j) φ z := by
  have hat : ∀ j, DifferentiableAt ℂ (gj j) z := fun j =>
    (hd j).differentiableAt ((isOpen_Dom D r s).mem_nhds hz)
  have hf : fderiv ℂ (fun z => ∑ j, gj j z) z = ∑ j, fderiv ℂ (gj j) z :=
    fderiv_fun_sum fun j _ => hat j
  simp only [poissonBracket, hf, sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_sub_distrib, Finset.sum_mul]


theorem bracket_g {D : Set (Fin n → ℂ)} {r s ρ σ Φ : ℝ} {g φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {N : ℕ} {gj : Fin N → (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {rj sj Mj : Fin N → ℝ}
    (hg : IsDecomp D r s g gj rj sj Mj) (hφ : InClass D r s φ) (hbφ : WBound D r s φ Φ)
    (hρ : 0 < ρ) (hρr : ρ < r) (hσ : 0 < σ) (hσs : σ < s) :
    InClass D (r - ρ) (s - σ) (poissonBracket g φ) ∧
    WBound D (r - ρ) (s - σ) (poissonBracket g φ)
      (2 / (Real.exp 1 * ρ * σ) * starNorm r s ρ σ rj sj Mj * Φ) ∧
    WBound D (r - ρ) (s - σ) (poissonBracket g φ)
      (2 / (ρ * σ) * starNorm r s ρ σ rj sj Mj * Φ) := by
  obtain rfl := hg.eq_sum
  have hb : 0 < s - σ := sub_pos.mpr hσs
  have hs : 0 < s := hσ.trans hσs
  have h1 : ∀ j, r - ρ < rj j := fun j => by linarith [hg.r_le j]
  have h2 : ∀ j, s - σ < sj j := fun j => by linarith [hg.s_le j]
  have hB := fun j => wbound_bracket (hg.inClass j) hφ (hg.bound j) hbφ hρ hρr hσ hσs (h1 j) (h2 j)
  have hdj : ∀ j, DifferentiableOn ℂ (gj j) (Dom n D r s) := fun j =>
    (hg.inClass j).differentiableOn.mono (Dom_mono (hg.r_le j) (hg.s_le j))
  have hdj' : ∀ j, DifferentiableOn ℂ (gj j) (Dom n D (r - ρ) (s - σ)) := fun j =>
    (hdj j).mono (Dom_mono (by linarith) (by linarith))
  have hgc : InClass D (r - ρ) (s - σ) (fun z => ∑ j, gj j z) :=
    ⟨DifferentiableOn.fun_sum fun j _ => hdj' j, fun i z hz => by
      exact Finset.sum_congr rfl fun j _ =>
        (hg.inClass j).periodic i z
          (Dom_mono (by linarith [hg.r_le j]) (by linarith [hg.s_le j]) hz)⟩
  have hφ' : InClass D (r - ρ) (s - σ) φ :=
    ⟨hφ.differentiableOn.mono (Dom_mono (by linarith) (by linarith)), fun i z hz =>
      hφ.periodic i z (Dom_mono (by linarith) (by linarith) hz)⟩
  have hcls : InClass D (r - ρ) (s - σ) (poissonBracket (fun z => ∑ j, gj j z) φ) := by
    refine ⟨differentiableOn_poissonBracket (isOpen_Dom D (r - ρ) (s - σ))
      hgc.differentiableOn hφ'.differentiableOn, fun j z hz => ?_⟩
    have hper : ∀ (w : (Fin n → ℂ) × (Fin n → ℂ) → ℂ), InClass D (r - ρ) (s - σ) w →
        ∀ a, fderiv ℂ w (z.1 + Pi.single j 1, z.2) a = fderiv ℂ w z a := fun w hw a =>
      (inClass_fderiv_apply hw a).periodic j z hz
    simp only [poissonBracket, hper _ hgc, hper _ hφ']
  have hsumB : ∀ I ∈ polyNbhd D (r - ρ),
      WSummable (poissonBracket (fun z => ∑ j, gj j z) φ) (s - σ) I ∧
      wsum (poissonBracket (fun z => ∑ j, gj j z) φ) (s - σ) I ≤
        2 / (Real.exp 1 * ρ * σ) * starNorm r s ρ σ rj sj Mj * Φ := by
    intro I hI
    obtain ⟨hws, hwle⟩ := wsum_finset_sum_le (s := s - σ) (I := I)
      (u := poissonBracket (fun z => ∑ j, gj j z) φ) (fun j => poissonBracket (gj j) φ)
      (fun x => poissonBracket_sum (D := D) (r := r) (s := s) gj φ hdj
        (Dom_mono (by linarith) (by linarith) ⟨KAM.ofReal_mem_complexStrip hb x, hI⟩))
      (fun j => continuous_slice hb (hB j).1 hI) (fun j => ((hB j).2 I hI).1)
    refine ⟨hws, hwle.trans ?_⟩
    have he : 0 < Real.exp 1 := Real.exp_pos 1
    calc ∑ j, wsum (poissonBracket (gj j) φ) (s - σ) I
        ≤ ∑ j, 1 / Real.exp 1 * (1 / ((rj j - r + ρ) * σ) + 1 / ((sj j - s + σ) * ρ)) *
            Mj j * Φ := Finset.sum_le_sum fun j _ => ((hB j).2 I hI).2
      _ = 2 / (Real.exp 1 * ρ * σ) * starNorm r s ρ σ rj sj Mj * Φ := by
          unfold starNorm
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          have a1 : 0 < rj j - r + ρ := by linarith [hg.r_le j]
          have a2 : 0 < sj j - s + σ := by linarith [hg.s_le j]
          field_simp
  refine ⟨hcls, hsumB, fun I hI => ⟨(hsumB I hI).1, (hsumB I hI).2.trans ?_⟩⟩
  have hΦ : 0 ≤ Φ := (wsum_nonneg' φ s I).trans ((hbφ I (polyNbhd_mono (by linarith) hI)).2)
  have hS : 0 ≤ starNorm r s ρ σ rj sj Mj := by
    refine Finset.sum_nonneg fun j _ => ?_
    have a1 : 0 < rj j - r + ρ := by linarith [hg.r_le j]
    have a2 : 0 < sj j - s + σ := by linarith [hg.s_le j]
    have hM : 0 ≤ Mj j := (wsum_nonneg' _ _ I).trans
      ((hg.bound j I (polyNbhd_mono (by linarith [hg.r_le j]) hI)).2)
    positivity
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have : 2 / (Real.exp 1 * ρ * σ) ≤ 2 / (ρ * σ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [mul_pos hρ hσ]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hS) hΦ

end KAM.NormalForm

end
