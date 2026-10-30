/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Sound.Ham

/-!
# The cosh bound for a pair of conjugate characters

The landed ball pass bounds `c₁ χ_k + c₂ χ_{-k}` (a cosine or sine mode, and every derivative of
one) termwise by `(|c₁| + |c₂|) w^{|k|}` with `w ≥ e^{2πρ}`. On the strip `|Im θ| < ρ` the exact
sizes are `‖χ_k‖ = s = e^{-t}` and `‖χ_{-k}‖ = s⁻¹` with `|t| ≤ 2πρ|k|`, so the pair is bounded by
`a s + b s⁻¹`, and that is convex in `s ∈ [h⁻¹, h]`: it is at most `max (a h⁻¹ + b h) (a h + b
h⁻¹)`, which is `(a + b) cosh` for `a = b`.

* `trig_pair_le`: the real inequality.
* `expLoQ`, `expLoQ_le_exp`: a rational lower bound of `e^x`, `x ≥ 0` (Taylor partial sum), the
  source of the rational upper bound `1/lo` of `e^{-x}`.
* `trigRad WH N k a b`: the rational radius, `max (a L + b W) (a W + b L)` with `W = w^{|k|}`
  and `L = 1/expLoQ(2 π_lo ρ |k|)`.
* `charNorm`, `charNorm_negKey`, `charNorm_le`: the norm of the compiled character.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate CertArith

/-- `a s + b s⁻¹ ≤ max (a L + b W) (a W + b L)` for `s` between `l = h⁻¹` and `h`, `l ≤ L`,
`h ≤ W`: the sum is convex in `s`, and the chord through `(l, h⁻¹)`, `(h, l)` lies above `s⁻¹`. -/
theorem trig_pair_le {a b s l h L W : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l)
    (hls : l ≤ s) (hsh : s ≤ h) (hlh : l * h = 1) (hL : l ≤ L) (hW : h ≤ W) :
    a * s + b * s⁻¹ ≤ max (a * L + b * W) (a * W + b * L) := by
  have hs : 0 < s := hl.trans_le hls
  have hh : 0 < h := hs.trans_le hsh
  have hinv : s⁻¹ ≤ l + h - s := by
    rw [inv_eq_one_div, div_le_iff₀ hs]
    nlinarith [mul_nonneg (sub_nonneg.2 hls) (sub_nonneg.2 hsh)]
  rcases le_total b a with hab | hab
  · refine le_max_of_le_right ?_
    have h1 : a * s + b * s⁻¹ ≤ a * s + b * (l + h - s) := by gcongr
    have h2 : a * s + b * (l + h - s) = b * (l + h) + (a - b) * s := by ring
    have h3 : (a - b) * s ≤ (a - b) * h := mul_le_mul_of_nonneg_left hsh (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hL hb, mul_le_mul_of_nonneg_left hW ha,
      mul_le_mul_of_nonneg_left hW (sub_nonneg.2 hab)]
  · refine le_max_of_le_left ?_
    have h1 : a * s + b * s⁻¹ ≤ a * s + b * (l + h - s) := by gcongr
    have h2 : a * s + b * (l + h - s) = b * (l + h) + (a - b) * s := by ring
    have h3 : (b - a) * l ≤ (b - a) * s := mul_le_mul_of_nonneg_left hls (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hL ha, mul_le_mul_of_nonneg_left hW hb,
      mul_le_mul_of_nonneg_left hL (sub_nonneg.2 hab)]

/-- The Taylor partial sum `∑_{i<N} x^i/i!`. -/
def expLoQ (x : ℚ) (N : ℕ) : ℚ := sumRangeQ N fun i => x ^ i / (i.factorial : ℚ)

theorem expLoQ_le_exp {x : ℚ} (hx : 0 ≤ x) (N : ℕ) : (expLoQ x N : ℝ) ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg (x := (x : ℝ)) (by exact_mod_cast hx) N
  rw [expLoQ, sumRangeQ_eq]
  push_cast
  exact h

/-- The rational upper bound `1/lo` of `e^{-x}` from the lower bound `lo` of `e^x` (and `1` when
`lo ≤ 0`). -/
def expNegUpQ (x : ℚ) (N : ℕ) : ℚ := if 0 < expLoQ x N then 1 / expLoQ x N else 1

theorem exp_neg_le_expNegUpQ {x : ℚ} (hx : 0 ≤ x) (N : ℕ) :
    Real.exp (-(x : ℝ)) ≤ (expNegUpQ x N : ℝ) := by
  unfold expNegUpQ
  split_ifs with h
  · have h' : (0 : ℝ) < expLoQ x N := by exact_mod_cast h
    rw [Real.exp_neg]
    push_cast
    rw [one_div]
    exact inv_anti₀ h' (expLoQ_le_exp hx N)
  · have : (0 : ℝ) ≤ x := by exact_mod_cast hx
    have h1 : Real.exp (-(x : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    simpa using h1

/-- The radius bound for `‖c₁ χ_k + c₂ χ_{-k}‖` from `‖c₁‖ ≤ a`, `‖c₂‖ ≤ b` (as bounds relative
to `‖χ_{±k}‖`). -/
def trigRad (WH : CertWeight) (N : ℕ) (k : CertKey) (a b : ℚ) : ℚ :=
  max (a * expNegUpQ (2 * piLoQ * WH.rho * (k.map Int.natAbs).sum) N +
      b * WH.w ^ (k.map Int.natAbs).sum)
    (a * WH.w ^ (k.map Int.natAbs).sum +
      b * expNegUpQ (2 * piLoQ * WH.rho * (k.map Int.natAbs).sum) N)

/-- The norm of the value of `char k`. -/
noncomputable def charNorm (n : ℕ) (k : CertKey) (z : (Fin n → ℂ) × (Fin n → ℂ)) : ℝ :=
  ‖Complex.exp (Complex.I * modePhase n k z.1)‖

theorem charNorm_pos (n : ℕ) (k : CertKey) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    0 < charNorm n k z := norm_pos_iff.2 (Complex.exp_ne_zero _)

theorem charNorm_negKey (n : ℕ) (k : CertKey) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    charNorm n (negKey k) z = (charNorm n k z)⁻¹ := by
  unfold charNorm
  rw [modePhase_negKey, mul_neg, Complex.exp_neg, norm_inv]

theorem sum_natAbs_negKey (k : CertKey) :
    ((negKey k).map Int.natAbs).sum = (k.map Int.natAbs).sum := by
  simp [negKey, List.map_map, Function.comp_def]

theorem charNorm_le {n : ℕ} {WH : CertWeight} {s N : ℕ} (hW : checkWeight WH s N = true)
    (k : CertKey) {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z.1 ∈ complexStrip n WH.rho) :
    charNorm n k z ≤ Real.exp (2 * Real.pi * WH.rho * (k.map Int.natAbs).sum) := by
  have hc : Complex.exp (Complex.I * modePhase n k z.1) = character (certKeyFun n k) z.1 := by
    unfold character modePhase
    congr 1
    ring
  unfold charNorm
  rw [hc]
  refine (norm_character_le (certKeyFun n k) hz).trans (Real.exp_le_exp.2 ?_)
  have h1 : Fourier.modeSize (certKeyFun n k) ≤ ((k.map Int.natAbs).sum : ℝ) := by
    have h := sum_natAbs_certKeyFun_le n k
    have : Fourier.modeSize (certKeyFun n k) =
        ((∑ i : Fin n, (certKeyFun n k i).natAbs : ℕ) : ℝ) := by
      simp [Fourier.modeSize, Nat.cast_sum, Nat.cast_natAbs]
    rw [this]
    exact_mod_cast h
  have hρ : 0 ≤ 2 * Real.pi * (WH.rho : ℝ) := by
    have := CertWeight.rho_pos hW
    positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hρ]

end KAM.CertificateSharp

end
