/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedBasic
public import KAM.Planetary.Preparation.PreparedFreq

/-!
# The chosen frequency datum of the prepared assembly (P11A-P8e)

`p11PrepChk D nu eps` is the normalized frequency `checkW`: the derivative of `h₀ + g₂` at the
rescaled point (head as is, tail divided by `eps`). The chosen prepared data is
`p11PrepQ D nu eps = p11PreparedCore D nu eps (p11PrepChk D nu eps)`. Here are the two clauses
that tie `checkW` to the data: the identification with `p11SlowNormalizedFreq` and the relation
between `p11PreparedFreqR` and `checkW` on `‖y‖ ≤ 5/4`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section Choice

variable {n : ℕ}

/-- The normalized frequency datum `checkW` of the assembly. -/
def p11PrepChk (D : P11Physical n) (nu eps : ℝ) (y : P11Vec (n + n)) : P11Vec (n + n) :=
  let A := p11SlowData D nu eps
  let W : P11CVec (n + n) := fun i => fderiv ℂ (A.h0 + A.g2)
    (p11Rescale (p11SecularData D).J0 eps (0, KAM.realInclusion (n + n) y)).2 (Pi.single i 1)
  Fin.append (fun i : Fin n => (W (Fin.castAdd n i)).re)
    (fun i : Fin n => (W (Fin.natAdd n i)).re / eps)

/-- The chosen prepared data of the assembly. -/
def p11PrepQ (D : P11Physical n) (nu eps : ℝ) : P11PreparedData n :=
  p11PreparedCore D nu eps (p11PrepChk D nu eps)

theorem p11PrepQ_checkW (D : P11Physical n) (nu eps : ℝ) :
    (p11PrepQ D nu eps).checkW = p11PrepChk D nu eps := rfl

theorem p11PrepQ_N_formula (D : P11Physical n) (nu eps : ℝ) :
    ∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, (p11PrepQ D nu eps).N I =
      ((p11SlowData D nu eps).h0 (p11Rescale (p11SecularData D).J0 eps (0, I)).2 +
        (p11SlowData D nu eps).g2 (p11Rescale (p11SecularData D).J0 eps (0, I)).2) /
          (eps : ℂ) := fun _ _ => rfl

/-- The rescaled point of the slice `(J, ρ)`. -/
theorem p11_prep_pt (J0 J ρ : P11Vec n) {eps : ℝ} (heps : eps ≠ 0) :
    (p11Rescale J0 eps (0, KAM.realInclusion (n + n)
      (Fin.append ((eps : ℝ)⁻¹ • (J - J0)) ρ))).2 =
      Fin.append (KAM.realInclusion n J) (fun i : Fin n => (eps * (2 * Real.pi + ρ i) : ℂ)) := by
  have hc : (eps : ℂ) ≠ 0 := by exact_mod_cast heps
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [p11Rescale, Fin.append_left, KAM.realInclusion_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply]
    push_cast
    field_simp
    ring
  · simp [p11Rescale]

/-- Clause 2 of `P11PreparedFullSpec`: `checkW` is the slow normalized frequency. -/
theorem p11_prep_chk_eq (D : P11Physical n) (nu : ℝ) {eps : ℝ} (heps : eps ≠ 0)
    (J ρ : P11Vec n) :
    p11PrepChk D nu eps (Fin.append ((eps : ℝ)⁻¹ • (J - (p11SecularData D).J0)) ρ) =
      p11SlowNormalizedFreq D nu eps J ρ := by
  unfold p11PrepChk p11SlowNormalizedFreq
  rw [p11_prep_pt _ _ _ heps]

/-- Points of norm `≤ 5/4` lie in the one-neighbourhood of the prepared box. -/
theorem p11_prep_ball_mem {y : P11Vec (n + n)} (hy : ‖y‖ ≤ 5 / 4) :
    KAM.realInclusion (n + n) y ∈ KAM.actionNbhd (p11PreparedBox n) 1 := by
  refine ⟨fun i => max (-1 / 2) (min (1 / 2) (y i)), fun i _ => ?_, ?_⟩
  · constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  · refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)).2
      fun i => ?_) (by norm_num)
    have h1 : ‖y i‖ ≤ 5 / 4 := (norm_le_pi_norm y i).trans hy
    rw [Real.norm_eq_abs, abs_le] at h1
    simp only [Pi.sub_apply, KAM.realInclusion_apply]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    rcases le_total (y i) (1 / 2) with h2 | h2
    · rcases le_total (-1 / 2) (y i) with h3 | h3
      · rw [min_eq_right h2, max_eq_right h3]; constructor <;> linarith
      · rw [min_eq_right (by linarith), max_eq_left h3]; constructor <;> linarith
    · rw [min_eq_left h2, max_eq_right (by norm_num)]; constructor <;> linarith

theorem p11_fderiv_pi_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ}
    {x : E} (hf : DifferentiableAt ℂ f x) (v : E) :
    fderiv ℂ (fun I (_ : Fin 1) => f I) x v 0 = fderiv ℂ f x v := by
  have : HasFDerivAt (fun I (_ : Fin 1) => f I)
      (ContinuousLinearMap.pi fun _ : Fin 1 => fderiv ℂ f x) x :=
    hasFDerivAt_pi'.2 fun _ => by simpa using hf.hasFDerivAt
  rw [this.fderiv]
  rfl

/-- Clause 11 of `P11PreparedSpec`: the prepared frequency is `diag(1, eps) checkW` on `‖y‖ ≤ 5/4`. -/
theorem p11_prep_freqR_eq {D : P11Physical n} {nu eps : ℝ} (heps : 0 < eps)
    (h5 : 5 * eps ≤ p11s2 (p11SecularData D) nu eps) (hs2 : 0 ≤ p11s2 (p11SecularData D) nu eps)
    (hA : P11SlowSpecOf (p11SecularData D) (p11FastData D eps) nu eps (p11SlowConstant D nu)
      (p11SlowData D nu eps)) :
    ∀ y : P11Vec (n + n), ‖y‖ ≤ 5 / 4 →
      p11PreparedFreqR (p11PrepQ D nu eps) y = Fin.append
        (fun i : Fin n => (p11PrepQ D nu eps).checkW y (Fin.castAdd n i))
        (fun i : Fin n => eps * (p11PrepQ D nu eps).checkW y (Fin.natAdd n i)) := by
  intro y hy
  have hU1 := p11_prep_ball_mem hy
  have hfd : ∀ c : Fin (n + n), p11PreparedFreq (p11PrepQ D nu eps) (KAM.realInclusion (n + n) y)
      c = fderiv ℂ ((p11SlowData D nu eps).h0 + (p11SlowData D nu eps).g2)
        (p11Rescale (p11SecularData D).J0 eps (0, KAM.realInclusion (n + n) y)).2
        (Pi.single c 1) := by
    intro c
    have h := p11_freq_partial_eq (C := p11SecularData D) heps h5 hs2 hA
      (p11PrepQ_N_formula D nu eps) hU1 (0 : Fin (n + n) → ℕ) c
    rw [p11PartialVec_zero] at h
    simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero, one_mul, zero_add] at h
    rw [p11PartialVec_single] at h
    rw [h]
    have hHd := p11_freq_H_diff (C := p11SecularData D) hs2 heps.le hA
    have hVo := p11_dev_box_isOpen (p11DevCenter (p11SecularData D) eps)
      (p11s2 (p11SecularData D) nu eps / 2) (Real.pi * eps / 2)
    have hmem := p11_freq_U1_sub (C := p11SecularData D) (nu := nu) heps h5 hU1
    have hd : DifferentiableAt ℂ ((p11SlowData D nu eps).h0 + (p11SlowData D nu eps).g2)
        (p11Rescale (p11SecularData D).J0 eps (0, KAM.realInclusion (n + n) y)).2 :=
      ((differentiableOn_pi.1 hHd 0).differentiableAt (hVo.mem_nhds hmem))
    exact p11_fderiv_pi_one hd _
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [p11PreparedFreqR, hfd, p11PrepQ_checkW, p11PrepChk]
  · simp only [p11PreparedFreqR, hfd, p11PrepQ_checkW, p11PrepChk, Fin.append_right]
    field_simp

end Choice

end KAM.Planetary

end
