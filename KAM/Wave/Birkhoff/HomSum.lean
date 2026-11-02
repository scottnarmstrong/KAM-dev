/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.FForm

/-!
# Absolute convergence of the Euler sums (blueprint-W `bpW:w3:homological`, Step Euler identity)

Package W3-DIVISOR-F, blueprint label `bpW:w3:homological`.

`summable_birkLamQuartTerm`: for a coefficient `c` with `|c_x| ≤ |𝔤_x|` and `w ∈ 𝔚`, the series
`Σ_x λ_{|x₄|} c_x ∏_t w_{x_t}` converges absolutely (the factor `λ_{|x₄|} ≤ √(1+m)|x₄|` is absorbed
by the
one-smoothing of `∇𝔓`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ}

section

variable (ha : 0 ≤ a) (hp : 1 / 2 ≤ p) {c : (Fin 4 → BirkIdx) → ℂ}
  (hc : ∀ x, ‖c x‖ ≤ |birkG m hm x|)

include ha hp hc in
theorem summable_birkLamQuartTerm (w : BirkSpace) :
    Summable fun x : Fin 4 → BirkIdx =>
      ‖(lam m hm (x 3).2 : ℂ) * (c x * birkAtom a p x (fun _ => w))‖ := by
  set wv : Fin 4 → BirkSpace := fun _ => w with hwv
  set w' := birkInit4 wv with hw'
  set M := birkMajorant m hm (birkFoldNorm a p (w' 0)) (birkFoldNorm a p (w' 1))
    (birkFoldNorm a p (w' 2)) with hM
  have hmaj := birkMajorant_bound m hm ha hp (isEll_birkFoldNorm a p (w' 0))
    (isEll_birkFoldNorm a p (w' 1)) (isEll_birkFoldNorm a p (w' 2))
  have hs : Summable fun j : ℕ+ => (ellWeight a (p + 1) j * ‖M j‖) ^ 2 :=
    (wave_isEll_iff_summable a (p + 1) M).1 hmaj.2.1
  have hBs : Summable fun z : BirkIdx => (ellWeight a (p + 1) z.2 * ‖M z.2‖) ^ 2 := by
    rw [birk_summable_iff (fun l => by positivity)]; exact ⟨hs, hs⟩
  have hM0 : ∀ j, 0 ≤ M j := fun j => by
    rw [hM]; unfold birkMajorant waveSelSum
    exact tsum_nonneg fun t => mul_nonneg (abs_nonneg _) (mul_nonneg
      (birkFoldNorm_nonneg a p _ _) (mul_nonneg (birkFoldNorm_nonneg a p _ _)
        (birkFoldNorm_nonneg a p _ _)))
  have key0 : ∀ z y, ‖c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) wv‖ =
      ‖birkGradTerm a p c (birkNeg z) w' y‖ * ‖birkCoord a p (wv 3) z‖ := fun z y => by
    rw [birkAtom_split4, birkAtom_apply]
    simp only [hw', birkGradTerm, norm_mul, birkNeg_birkNeg, birkSplit4, Equiv.coe_fn_mk, birkInit4]
    ring
  have key : ∀ z y, ‖(lam m hm (birkSplit4 (z, y) 3).2 : ℂ) *
      (c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) wv)‖ =
      lam m hm z.2 * (‖birkGradTerm a p c (birkNeg z) w' y‖ * ‖birkCoord a p (wv 3) z‖) :=
    fun z y => by
      have : (birkSplit4 (z, y) 3) = z := rfl
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (wave_lam_pos m hm _),
        key0]
  have hfib : ∀ z : BirkIdx, Summable fun y : Fin 3 → BirkIdx =>
      ‖(lam m hm (birkSplit4 (z, y) 3).2 : ℂ) *
        (c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) wv)‖ := fun z => by
    simp only [key]
    exact ((birkGrad_majorize m hm ha hp hc (birkNeg z) w').1.mul_right _).mul_left _
  have hout : Summable fun z : BirkIdx => ∑' y : Fin 3 → BirkIdx,
      ‖(lam m hm (birkSplit4 (z, y) 3).2 : ℂ) *
        (c (birkSplit4 (z, y)) * birkAtom a p (birkSplit4 (z, y)) wv)‖ := by
    have hcs := waveCauchySchwarz_tsum (f := fun z : BirkIdx => ‖wv 3 z‖)
      (g := fun z : BirkIdx => ellWeight a (p + 1) z.2 * ‖M z.2‖) (fun _ => norm_nonneg _)
      (fun z => mul_nonneg (ellWeight_pos _ _ _).le (norm_nonneg _))
      (lp_two_hasSum_sq (wv 3)).summable hBs
    refine Summable.of_nonneg_of_le (fun z => tsum_nonneg fun _ => norm_nonneg _) (fun z => ?_)
      (hcs.1.mul_left (Real.sqrt (1 + m)))
    simp only [key]
    rw [tsum_mul_left, tsum_mul_right]
    have h1 := (birkGrad_majorize m hm ha hp hc (birkNeg z) w').2
    rw [← hM] at h1
    simp only [birkNeg_snd] at h1
    have h3 : ‖birkCoord a p (wv 3) z‖ = ‖wv 3 z‖ / ellWeight a p z.2 := by
      rw [birkCoord, norm_div, norm_ellWeight_cast]
    have hw1 : 1 ≤ ellWeight a p z.2 := birk_one_le_weight ha (by linarith) _
    have hlam := lam_le_sqrt_mul hm z.2
    have hsucc := birk_weight_succ a p z.2
    have hz0 : (0 : ℝ) < (z.2 : ℝ) := by exact_mod_cast z.2.pos
    rw [Real.norm_eq_abs, abs_of_nonneg (hM0 _)]
    have hw0 : 0 < ellWeight a p z.2 := ellWeight_pos _ _ _
    have e1 : lam m hm z.2 * ((∑' y, ‖birkGradTerm a p c (birkNeg z) w' y‖) *
        ‖birkCoord a p (wv 3) z‖) ≤ (Real.sqrt (1 + m) * z.2) * (M z.2 * (‖wv 3 z‖ /
          ellWeight a p z.2)) := by
      rw [h3] at *
      refine mul_le_mul hlam (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
        (by positivity)
    refine e1.trans ?_
    have e2 : (z.2 : ℝ) / ellWeight a p z.2 ≤ ellWeight a (p + 1) z.2 := by
      rw [hsucc, div_le_iff₀ hw0]
      nlinarith [mul_nonneg hz0.le (sub_nonneg.2 hw1), mul_pos hz0 hw0]
    have := mul_le_mul_of_nonneg_left e2 (mul_nonneg (Real.sqrt_nonneg (1 + m)) (norm_nonneg (wv 3
        z)))
    have hMz := hM0 z.2
    calc (Real.sqrt (1 + m) * z.2) * (M z.2 * (‖wv 3 z‖ / ellWeight a p z.2))
        = (Real.sqrt (1 + m) * ‖wv 3 z‖) * ((z.2 : ℝ) / ellWeight a p z.2) * M z.2 := by ring
      _ ≤ (Real.sqrt (1 + m) * ‖wv 3 z‖) * ellWeight a (p + 1) z.2 * M z.2 := by gcongr
      _ = Real.sqrt (1 + m) * (‖wv 3 z‖ * (ellWeight a (p + 1) z.2 * M z.2)) := by ring
  have hprod : Summable fun q : BirkIdx × (Fin 3 → BirkIdx) =>
      ‖(lam m hm (birkSplit4 q 3).2 : ℂ) *
        (c (birkSplit4 q) * birkAtom a p (birkSplit4 q) wv)‖ :=
    (summable_prod_of_nonneg (fun q => norm_nonneg _)).2 ⟨hfib, hout⟩
  exact (birkSplit4.summable_iff (f := fun x : Fin 4 → BirkIdx =>
    ‖(lam m hm (x 3).2 : ℂ) * (c x * birkAtom a p x wv)‖)).1 hprod

end

end KAM.Wave

end
