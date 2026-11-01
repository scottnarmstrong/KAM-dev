/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamStep.ActionAngle
public import KAM.Wave.Birkhoff.MainYSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The action–angle substitution: the domain check (blueprint-W `bpW:w5:action-angle` (ii), (vi))

Off-frontier, source-faithful infrastructure (W5-AA); the dependency graph is still being built.
Blueprint label `bpW:w5:action-angle` (ii), step `a-dom`, and the norm comparisons of (vi).

At `a = p = 1`, for `0 < s ≤ 1/8`, `r > 0`, `t > 0`, `|ξ|_∞ ≤ t`, `Re ξ_i ≥ 2r²` and
`w ∈ D(s,r)`: `‖𝒜_ξ(w)‖² < c_A (t + r²)`, `c_A = 2200` (`aaCA`), i.e.
`𝒜_ξ(D(s,r)) ⊂ B_ρ` with `ρ² = c_A (t + r²)` (`aaMap_mem_ball`), and `𝒜_ξ(D(s,r)) ⊂ B_{ρ₁}` whenever
`c_A (t + r²) < ρ₁(m)²` (`aaMap_mem_birkBall1`). Also `Re(ξ_i + y_i) > r²` there, so `w` lies in the
domain of `𝒜_ξ`.

The proof splits `‖𝒜_ξ(w)‖² = ‖tangential‖² + ‖ŵ‖²` (`norm_sq_aaMap`, disjoint supports), with
`‖ŵ‖² = ‖u‖² + ‖v‖²` (`norm_sq_aaNormal`; this is the comparison `‖ŵ‖ ≤ ‖u‖ + ‖v‖ ≤ √2 ‖ŵ‖` of (vi),
`aaNormal_norm_le`, `aaNormal_norm_ge`), and the four tangential terms
`ω_{1,1}(i)² |ξ_i + y_i| |e^{∓2πiθ_i}|² ≤ ω_{1,1}(i)² (t + r²) e^{4πs}` with
`2(e² + 4e⁴) e^{π/2} ≤ 2199`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM Complex

/-- The absolute constant `c_A = 2200` of `bpW:w5:action-angle` (ii). -/
def aaCA : ℝ := 2200

/-! ### The norm of `𝒜_ξ(w)` -/

theorem aaTan_sq_hasSum (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) :
    HasSum (fun l => ‖aaTan a p ξ w l‖ ^ 2)
      (∑ i : Fin 2, ∑ b : Bool, ‖(ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i‖ ^ 2) := by
  classical
  have hpt : ∀ l : BirkIdx, ‖aaTan a p ξ w l‖ ^ 2 = ∑ i : Fin 2, ∑ b : Bool,
      if l = (b, modeIdx i) then ‖(ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i‖ ^ 2
        else 0 := fun l => by
    rcases l with ⟨b, J⟩
    rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [aaTan_tan]
      have hinj := modeIdx_injective (N := 2)
      fin_cases i <;> cases b <;> simp [Prod.ext_iff, hinj.eq_iff]
    · rw [aaTan_nor]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      refine (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b' _ => ?_).symm
      exact ite_eq_right_iff.2 fun h => absurd (congrArg Prod.snd h).symm (modeIdx_ne_add_two i j)
  simp_rw [hpt]
  exact hasSum_sum fun i _ => hasSum_sum fun b _ => hasSum_ite_eq _ _

theorem norm_sq_aaNormal (w : KamPhase) : ‖aaNormal w‖ ^ 2 = ‖w.2.2.1‖ ^ 2 + ‖w.2.2.2‖ ^ 2 := by
  have h := norm_sq_birkZ (aaShift w.2.2.1, aaShift w.2.2.2)
  rw [norm_aaShift, norm_aaShift] at h
  exact h

/-- (`bpW:w5:action-angle` (vi)) `‖ŵ‖ ≤ ‖u‖ + ‖v‖`. -/
theorem aaNormal_norm_le (w : KamPhase) : ‖aaNormal w‖ ≤ ‖w.2.2.1‖ + ‖w.2.2.2‖ := by
  have h := norm_sq_aaNormal w
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [h]
  nlinarith [norm_nonneg w.2.2.1, norm_nonneg w.2.2.2]

/-- (`bpW:w5:action-angle` (vi)) `‖u‖ + ‖v‖ ≤ √2 ‖ŵ‖`. -/
theorem aaNormal_norm_ge (w : KamPhase) :
    ‖w.2.2.1‖ + ‖w.2.2.2‖ ≤ Real.sqrt 2 * ‖aaNormal w‖ := by
  have h := norm_sq_aaNormal w
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt (by norm_num), h]
  nlinarith [sq_nonneg (‖w.2.2.1‖ - ‖w.2.2.2‖)]

/-- `‖𝒜_ξ(w)‖² = Σ_{i,±} ω_{a,p}(i)² |𝒜_ξ(w)_{±i}|² + ‖u‖² + ‖v‖²` (disjoint supports). -/
theorem norm_sq_aaMap (a p : ℝ) (ξ : Fin 2 → ℂ) (w : KamPhase) :
    ‖aaMap a p ξ w‖ ^ 2 =
      (∑ i : Fin 2, ∑ b : Bool, ‖(ellWeight a p (modeIdx i) : ℂ) * aaTanCoord ξ w b i‖ ^ 2) +
        (‖w.2.2.1‖ ^ 2 + ‖w.2.2.2‖ ^ 2) := by
  have hpt : ∀ l, ‖aaMap a p ξ w l‖ ^ 2 = ‖aaTan a p ξ w l‖ ^ 2 + ‖aaNormal w l‖ ^ 2 := by
    rintro ⟨b, J⟩
    rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · simp [aaMap, aaNormal_tan]
    · simp [aaMap, aaTan_nor]
  have h1 := lp_two_hasSum_sq (aaMap a p ξ w)
  simp_rw [hpt] at h1
  have h2 := (aaTan_sq_hasSum a p ξ w).add (lp_two_hasSum_sq (aaNormal w))
  rw [h1.unique h2, norm_sq_aaNormal]

/-! ### Numerics -/

theorem exp_half_le : Real.exp (1 / 2) ≤ 1.6488 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

theorem exp_pi_half_le : Real.exp (Real.pi / 2) ≤ 1.6488 ^ 3 * 1.0762 := by
  have hpi := Real.pi_lt_d4
  have hx : Real.pi / 2 - 3 / 2 ≤ 0.0708 := by linarith
  have hsplit : Real.exp (Real.pi / 2) = Real.exp (1 / 2) ^ 3 * Real.exp (Real.pi / 2 - 3 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hsmall : Real.exp (Real.pi / 2 - 3 / 2) ≤ 1.0762 := by
    have h := Real.add_one_le_exp (-(Real.pi / 2 - 3 / 2))
    have hpos := Real.exp_pos (Real.pi / 2 - 3 / 2)
    have hmul : Real.exp (-(Real.pi / 2 - 3 / 2)) * Real.exp (Real.pi / 2 - 3 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  rw [hsplit]
  have he := exp_half_le
  have he0 := Real.exp_pos (1 / 2)
  have h3 : Real.exp (1 / 2) ^ 3 ≤ 1.6488 ^ 3 := pow_le_pow_left₀ he0.le he 3
  have := Real.exp_pos (Real.pi / 2 - 3 / 2)
  calc Real.exp (1 / 2) ^ 3 * Real.exp (Real.pi / 2 - 3 / 2) ≤ 1.6488 ^ 3 * 1.0762 :=
        mul_le_mul h3 hsmall this.le (by norm_num)

/-- `2 (ω_{1,1}(1)² + ω_{1,1}(2)²) e^{π/2} = 2 (e² + 4 e⁴) e^{π/2} ≤ 2199`. -/
theorem aaTan_const_le :
    2 * (ellWeight 1 1 1 ^ 2 + ellWeight 1 1 2 ^ 2) * Real.exp (Real.pi / 2) ≤ 2199 := by
  have h1 : ellWeight 1 1 1 = Real.exp (1 / 2) ^ 2 := by
    simp only [ellWeight, PNat.one_coe, Nat.cast_one, Real.rpow_one, one_mul, mul_one]
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : ellWeight 1 1 2 = 2 * Real.exp (1 / 2) ^ 4 := by
    simp only [ellWeight, PNat.val_ofNat, Nat.cast_ofNat, Real.rpow_one, one_mul]
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1, h2]
  have he := exp_half_le
  have he0 := Real.exp_pos (1 / 2)
  have hp := exp_pi_half_le
  have hp0 := Real.exp_pos (Real.pi / 2)
  set x := Real.exp (1 / 2)
  have hx4 : x ^ 4 ≤ 1.6488 ^ 4 := pow_le_pow_left₀ he0.le he 4
  have hx8 : x ^ 8 ≤ 1.6488 ^ 8 := pow_le_pow_left₀ he0.le he 8
  calc 2 * ((x ^ 2) ^ 2 + (2 * x ^ 4) ^ 2) * Real.exp (Real.pi / 2)
      = 2 * (x ^ 4 + 4 * x ^ 8) * Real.exp (Real.pi / 2) := by ring
    _ ≤ 2 * (1.6488 ^ 4 + 4 * 1.6488 ^ 8) * (1.6488 ^ 3 * 1.0762) := by
        apply mul_le_mul _ hp hp0.le (by norm_num)
        linarith
    _ ≤ 2199 := by norm_num

/-! ### The domain check -/

theorem norm_aaTanCoord_sq_le {s r t : ℝ} (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ t) {w : KamPhase}
    (hw : w ∈ kamDomain s r) (b : Bool) (i : Fin 2) :
    ‖aaTanCoord ξ w b i‖ ^ 2 ≤ (t + r ^ 2) * Real.exp (4 * Real.pi * s) := by
  obtain ⟨hθ, hy, -⟩ := hw
  unfold aaTanCoord
  rw [norm_mul, mul_pow, ← norm_pow, aaSqrt_sq, Complex.norm_exp]
  have hξi : ‖ξ i‖ ≤ t := (norm_le_pi_norm ξ i).trans hξ
  have hyi : ‖w.2.1 i‖ < r ^ 2 := lt_of_le_of_lt (norm_le_pi_norm w.2.1 i) hy
  have h1 : ‖ξ i + w.2.1 i‖ ≤ t + r ^ 2 := (norm_add_le _ _).trans (by linarith)
  have hre : (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * w.1 i)).re ≤ 2 * Real.pi * s := by
    have hs := hθ i
    have hpi := Real.pi_pos
    cases b <;> simp [birkSgn, Complex.mul_re] <;> nlinarith [abs_lt.1 hs]
  have h2 : Real.exp (-(birkSgn (b, modeIdx i)) * (2 * Real.pi * I * w.1 i)).re ^ 2 ≤
      Real.exp (4 * Real.pi * s) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  exact mul_le_mul h1 h2 (by positivity) (by linarith [norm_nonneg (ξ i + w.2.1 i)])

/-- **Domain** (`bpW:w5:action-angle` (ii), `a = p = 1`): for `s ≤ 1/8`, `t > 0`, `|ξ|_∞ ≤ t`,
`Re ξ_i ≥ 2r²` and `w ∈ D(s,r)`: `Re(ξ_i + y_i) > r²` (so `w` is in the domain of `𝒜_ξ`) and
`‖𝒜_ξ(w)‖² < c_A (t + r²)`. -/
theorem aaMap_domain {s r t : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r) (ht : 0 < t) (ξ : Fin 2 → ℂ)
    (hξ : ‖ξ‖ ≤ t) (hre : ∀ i, 2 * r ^ 2 ≤ (ξ i).re) {w : KamPhase} (hw : w ∈ kamDomain s r) :
    (∀ i, r ^ 2 < (ξ i + w.2.1 i).re) ∧ ‖aaMap 1 1 ξ w‖ ^ 2 < aaCA * (t + r ^ 2) := by
  refine ⟨fun i => ?_, ?_⟩
  · have hyi : ‖w.2.1 i‖ < r ^ 2 := lt_of_le_of_lt (norm_le_pi_norm w.2.1 i) hw.2.1
    have := Complex.abs_re_le_norm (w.2.1 i)
    rw [Complex.add_re]
    linarith [hre i, abs_le.1 this]
  rw [norm_sq_aaMap]
  have hE : Real.exp (4 * Real.pi * s) ≤ Real.exp (Real.pi / 2) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have hT : 0 ≤ t + r ^ 2 := by positivity
  have hterm : ∀ (i : Fin 2) (b : Bool), ‖(ellWeight 1 1 (modeIdx i) : ℂ) * aaTanCoord ξ w b i‖ ^ 2
      ≤ ellWeight 1 1 (modeIdx i) ^ 2 * ((t + r ^ 2) * Real.exp (Real.pi / 2)) := fun i b => by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_aaTanCoord_sq_le ξ hξ hw b i).trans
      (mul_le_mul_of_nonneg_left hE hT)) (sq_nonneg _)
  have hsum : (∑ i : Fin 2, ∑ b : Bool, ‖(ellWeight 1 1 (modeIdx i) : ℂ) * aaTanCoord ξ w b i‖ ^ 2)
      ≤ 2199 * (t + r ^ 2) := by
    calc _ ≤ ∑ i : Fin 2, ∑ _b : Bool,
          ellWeight 1 1 (modeIdx i) ^ 2 * ((t + r ^ 2) * Real.exp (Real.pi / 2)) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hterm i b
      _ = 2 * (ellWeight 1 1 1 ^ 2 + ellWeight 1 1 2 ^ 2) * Real.exp (Real.pi / 2) *
          (t + r ^ 2) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
            Fin.sum_univ_two]
          have h0 : modeIdx (0 : Fin 2) = 1 := rfl
          have h1 : modeIdx (1 : Fin 2) = 2 := rfl
          rw [h0, h1]; push_cast; ring
      _ ≤ 2199 * (t + r ^ 2) := mul_le_mul_of_nonneg_right aaTan_const_le hT
  obtain ⟨-, -, hn⟩ := hw
  have hnor : ‖w.2.2.1‖ ^ 2 + ‖w.2.2.2‖ ^ 2 < t + r ^ 2 := by
    have : ‖w.2.2.1‖ ^ 2 + ‖w.2.2.2‖ ^ 2 ≤ (‖w.2.2.1‖ + ‖w.2.2.2‖) ^ 2 := by
      nlinarith [norm_nonneg w.2.2.1, norm_nonneg w.2.2.2]
    have h2 : (‖w.2.2.1‖ + ‖w.2.2.2‖) ^ 2 < r ^ 2 := by
      have := add_nonneg (norm_nonneg w.2.2.1) (norm_nonneg w.2.2.2)
      nlinarith
    linarith
  unfold aaCA
  linarith

/-- (`bpW:w5:action-angle` (ii)) `𝒜_ξ(D(s,r)) ⊂ B_ρ`, `ρ² = c_A (t + r²)`. -/
theorem aaMap_mem_ball {s r t : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r) (ht : 0 < t) (ξ : Fin 2 → ℂ)
    (hξ : ‖ξ‖ ≤ t) (hre : ∀ i, 2 * r ^ 2 ≤ (ξ i).re) {w : KamPhase} (hw : w ∈ kamDomain s r) :
    aaMap 1 1 ξ w ∈ Metric.ball 0 (Real.sqrt (aaCA * (t + r ^ 2))) := by
  rw [mem_ball_zero_iff]
  exact Real.lt_sqrt (norm_nonneg _) |>.2 (aaMap_domain hs hr ht ξ hξ hre hw).2

/-- (`bpW:w5:action-angle` (ii)) `𝒜_ξ(D(s,r)) ⊂ B_{ρ₁}` whenever `c_A (t + r²) < ρ₁(m)²`. -/
theorem aaMap_mem_birkBall1 (m : ℝ) (hm : 0 < m) {s r t : ℝ} (hs : s ≤ 1 / 8) (hr : 0 < r)
    (ht : 0 < t) (hρ₁ : aaCA * (t + r ^ 2) < birkRho1 m 1 ^ 2) (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ t)
    (hre : ∀ i, 2 * r ^ 2 ≤ (ξ i).re) {w : KamPhase} (hw : w ∈ kamDomain s r) :
    aaMap 1 1 ξ w ∈ birkBall1 m 1 := by
  rw [birkBall1_eq_ball (m := m) (hm := hm) (hp := (by norm_num : (1:ℝ) / 2 ≤ 1)),
    mem_ball_zero_iff]
  have h := (aaMap_domain hs hr ht ξ hξ hre hw).2
  have hρ : 0 ≤ birkRho1 m 1 := birkRho1_pos (m := m) (hm := hm) (hp := by norm_num) |>.le
  nlinarith [norm_nonneg (aaMap 1 1 ξ w)]

end KAM.Wave

end
