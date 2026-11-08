/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellEmbed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: closeness and size on one shell (blueprint `bpW:w8:shell-close`)

Blueprint label `bpW:w8:shell-close` (milestone W8).

For `ξ ∈ Γ_n` and real `θ`, with `w = Ψ̃^{(n)}_ξ(θ)`, `w⁰ = 𝒜_ξ(θ, 0, 0, 0)`, `x = 𝒵⁻¹w`,
`x⁰ = 𝒵⁻¹w⁰ = K⁰_ξ(θ)` (W5 `aaMap_linearTorus`):
* Step `stepW:w8:sc-tan`: `|w_{±i} - w⁰_{±i}| ≤ (1/4 + 2π)√t_n e` (we use `r_n² ≤ α_n/4 ≤ ξ_i/4`,
  so `|y_i|/√ξ_i ≤ √ξ_i e/4`, instead of the blueprint's `r_n²/√α_n ≤ √t_n`);
* Step `stepW:w8:sc-dist`: `‖x - x⁰‖ ≤ ‖w - w⁰‖ ≤ 22(1/4 + 2π)√t_n e + r_n e ≤ 162 √t_n e`;
* Step `stepW:w8:sc-gamma`: `‖Γ^ℝ(x) - x‖ ≤ ‖𝒵ψ‖ ≤ √2 · 6√2 C_F ‖x‖³` (the `√2` of
  `‖𝒵ψ‖ ≤ √2‖ψ‖` is absorbed by `√2 t_n^{3/2} ≤ t_n^{33/64}`);
* **`w8_shellClose`**: `‖K^{(n)}_ξ(θ) - linearTorus ξ θ‖ ≤ E₇ t_n^{33/64}` and
  `‖K^{(n)}_ξ(θ)‖ ≤ 2ρ_n`.
-/

@[expose] public noncomputable section

open Set Real Complex

namespace KAM.Wave

open KAM

/-- The tangential weights: `2(ω_{1,1}(1)² + ω_{1,1}(2)²) = 2(e² + 4e⁴) ≤ 484 = 22²`. -/
theorem w8_tan_weights : 2 * (ellWeight 1 1 1 ^ 2 + ellWeight 1 1 2 ^ 2) ≤ 484 := by
  have h1 : ellWeight 1 1 1 = Real.exp (1 / 2) ^ 2 := by
    simp only [ellWeight, PNat.one_coe, Nat.cast_one, Real.rpow_one, one_mul, mul_one]
    rw [← Real.exp_nat_mul]; norm_num
  have h2 : ellWeight 1 1 2 = 2 * Real.exp (1 / 2) ^ 4 := by
    simp only [ellWeight, PNat.val_ofNat, Nat.cast_ofNat, Real.rpow_one, one_mul]
    rw [← Real.exp_nat_mul]; norm_num
  rw [h1, h2]
  have he := exp_half_le
  have he0 := Real.exp_pos (1 / 2)
  set x := Real.exp (1 / 2)
  have hx4 : x ^ 4 ≤ 1.6488 ^ 4 := pow_le_pow_left₀ he0.le he 4
  have hx8 : x ^ 8 ≤ 1.6488 ^ 8 := pow_le_pow_left₀ he0.le he 8
  have e : 2 * ((x ^ 2) ^ 2 + (2 * x ^ 4) ^ 2) = 2 * x ^ 4 + 8 * x ^ 8 := by ring
  rw [e]
  norm_num at hx4 hx8
  linarith

/-- The squared norm of a difference of tangential parts of `𝒜_ξ` (`a = p = 1`). -/
theorem w8_tanDiff_hasSum (ξ : Fin 2 → ℂ) (w w' : KamPhase) :
    HasSum (fun l => ‖(aaTan 1 1 ξ w - aaTan 1 1 ξ w') l‖ ^ 2)
      (∑ i : Fin 2, ∑ b : Bool, ‖(ellWeight 1 1 (modeIdx i) : ℂ) *
        (aaTanCoord ξ w b i - aaTanCoord ξ w' b i)‖ ^ 2) := by
  classical
  have hpt : ∀ l : BirkIdx, ‖(aaTan 1 1 ξ w - aaTan 1 1 ξ w') l‖ ^ 2 = ∑ i : Fin 2, ∑ b : Bool,
      if l = (b, modeIdx i) then ‖(ellWeight 1 1 (modeIdx i) : ℂ) *
        (aaTanCoord ξ w b i - aaTanCoord ξ w' b i)‖ ^ 2 else 0 := fun l => by
    rcases l with ⟨b, J⟩
    rcases modeIdx_cases J with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [lp.coeFn_sub, _root_.Pi.sub_apply, aaTan_tan, aaTan_tan, ← mul_sub]
      have hinj := modeIdx_injective (N := 2)
      fin_cases i <;> cases b <;> simp [Prod.ext_iff, hinj.eq_iff]
    · rw [lp.coeFn_sub, _root_.Pi.sub_apply, aaTan_nor, aaTan_nor, sub_zero]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      refine (Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b' _ => ?_).symm
      exact ite_eq_right_iff.2 fun h => absurd (congrArg Prod.snd h).symm (modeIdx_ne_add_two i j)
  simp_rw [hpt]
  exact hasSum_sum fun i _ => hasSum_sum fun b _ => hasSum_ite_eq _ _

/-- If every tangential coordinate difference is `≤ δ`, the tangential difference has norm
`≤ 22 δ` (Step `stepW:w8:sc-dist`). -/
theorem w8_tanDiff_norm_le (ξ : Fin 2 → ℂ) (w w' : KamPhase) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ b i, ‖aaTanCoord ξ w b i - aaTanCoord ξ w' b i‖ ≤ δ) :
    ‖aaTan 1 1 ξ w - aaTan 1 1 ξ w'‖ ≤ 22 * δ := by
  have hs := (lp_two_hasSum_sq (aaTan 1 1 ξ w - aaTan 1 1 ξ w')).unique (w8_tanDiff_hasSum ξ w w')
  have hterm : ∀ (i : Fin 2) (b : Bool), ‖(ellWeight 1 1 (modeIdx i) : ℂ) *
      (aaTanCoord ξ w b i - aaTanCoord ξ w' b i)‖ ^ 2 ≤ ellWeight 1 1 (modeIdx i) ^ 2 * δ ^ 2 :=
      fun i b => by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h b i) 2) (sq_nonneg _)
  have hsum : ‖aaTan 1 1 ξ w - aaTan 1 1 ξ w'‖ ^ 2 ≤ (22 * δ) ^ 2 := by
    rw [hs]
    calc _ ≤ ∑ i : Fin 2, ∑ _b : Bool, ellWeight 1 1 (modeIdx i) ^ 2 * δ ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun b _ => hterm i b
      _ = 2 * (ellWeight 1 1 1 ^ 2 + ellWeight 1 1 2 ^ 2) * δ ^ 2 := by
          simp only [Fin.sum_univ_two, Fintype.univ_bool, Finset.mem_singleton,
            Bool.true_eq_false, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
          have h0 : modeIdx (0 : Fin 2) = 1 := rfl
          have h1 : modeIdx (1 : Fin 2) = 2 := rfl
          rw [h0, h1]; ring
      _ ≤ 484 * δ ^ 2 := mul_le_mul_of_nonneg_right w8_tan_weights (sq_nonneg _)
      _ = (22 * δ) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsum

/-- Step `stepW:w8:sc-tan` for one coordinate: for `a > 0`, `a + y ≥ 0`, `σ = ±1`,
`|√(a+y) e^{-iσ2πφ} - √a e^{-iσ2πθ}| ≤ |y|/√a + 2π √a |φ - θ|`. -/
theorem w8_coord_diff_le {a y φ θ σ : ℝ} (ha : 0 < a) (hay : 0 ≤ a + y) (hσ : |σ| = 1) :
    ‖((Real.sqrt (a + y) : ℝ) : ℂ) * cexp (-(σ : ℂ) * (2 * π * I * φ)) -
        ((Real.sqrt a : ℝ) : ℂ) * cexp (-(σ : ℂ) * (2 * π * I * θ))‖ ≤
      |y| / Real.sqrt a + 2 * π * Real.sqrt a * |φ - θ| := by
  have hE : ∀ u : ℝ, cexp (-(σ : ℂ) * (2 * π * I * u)) = cexp (((-(σ * 2 * π * u)) : ℝ) * I) :=
    fun u => by congr 1; push_cast; ring
  rw [hE, hE]
  set u := -(σ * 2 * π * φ)
  set v := -(σ * 2 * π * θ)
  have h1 : ‖cexp ((u : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I u
  have h2 : ‖cexp ((u : ℂ) * I) - cexp ((v : ℂ) * I)‖ ≤ 2 * π * |φ - θ| := by
    have e : cexp ((u : ℂ) * I) - cexp ((v : ℂ) * I) =
        cexp ((v : ℂ) * I) * (cexp (I * ((u - v : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine (w8ext_norm_exp_I (u - v)).2.trans (le_of_eq ?_)
    have : u - v = -(σ * 2 * π) * (φ - θ) := by simp only [u, v]; ring
    rw [this, abs_mul, abs_neg, abs_mul, abs_mul, hσ, abs_of_pos Real.pi_pos]
    norm_num
  have e : ((Real.sqrt (a + y) : ℝ) : ℂ) * cexp ((u : ℂ) * I) -
      ((Real.sqrt a : ℝ) : ℂ) * cexp ((v : ℂ) * I) =
      ((Real.sqrt (a + y) - Real.sqrt a : ℝ) : ℂ) * cexp ((u : ℂ) * I) +
        ((Real.sqrt a : ℝ) : ℂ) * (cexp ((u : ℂ) * I) - cexp ((v : ℂ) * I)) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, h1, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a)]
  have h3 := w8ext_abs_sqrt_sub_le ha hay
  have h4 := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg a)
  linarith

theorem w8_birkSgn_real (l : BirkIdx) : ∃ σ : ℝ, |σ| = 1 ∧ birkSgn l = (σ : ℂ) := by
  rcases l with ⟨b, J⟩
  cases b
  · exact ⟨-1, by norm_num, by simp [birkSgn]⟩
  · exact ⟨1, by norm_num, by simp [birkSgn]⟩

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

/-- `𝒵⁻¹ 𝒜_ξ(θ, 0, 0, 0) = K⁰_ξ(θ)` on real points (W5 `bpW:w5:action-angle` (i)). -/
theorem w8_birkPi_linearTorus (ξ : Fin 2 → ℝ) (hξ : ∀ i, 0 < ξ i) (θ : Fin 2 → ℝ) :
    birkPi (aaMap 1 1 (aaOfReal ξ) (aaOfReal θ, 0, 0, 0)) = linearTorus ξ hξ θ := by
  rw [w8_birkPi_eq_reWave, aaMap_linearTorus ξ hξ θ]
  refine Prod.ext ?_ ?_ <;> simp [reWave, birkReal_apply]

/-- Steps `stepW:w8:sc-tan`, `stepW:w8:sc-dist`: `‖Ψ̃(θ) - 𝒜_ξ(θ,0,0,0)‖ ≤ 162 √t_n e`. -/
theorem w8_shellDist (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) :
    ‖w8Psi hm n ξ θ - aaMap 1 1 (aaOfReal ξ) (aaOfReal θ, 0, 0, 0)‖ ≤
      162 * Real.sqrt (w8tn 𝔱 n) * w8ShellEtor m hm n := by
  obtain ⟨he0, -, hr2, hr1, hαt, ht1, ht, hα, hr⟩ := w8_shell_consts hm n
  obtain ⟨hX, hY, hN⟩ := w8_torusShape_bounds hm n hξ θ
  have hξP : ξ ∈ w8Pi 𝔱 n := w8ShellGamma_subset_Pi (w8HW hm n) hξ
  set e := w8ShellEtor m hm n
  set w' := w8TK hm n (aaOfReal θ) ξ
  have hsplit : w8Psi hm n ξ θ - aaMap 1 1 (aaOfReal ξ) (aaOfReal θ, 0, 0, 0) =
      (aaTan 1 1 (aaOfReal ξ) w' - aaTan 1 1 (aaOfReal ξ) (aaOfReal θ, 0, 0, 0)) +
        birkNormalPart (w8Psi hm n ξ θ) := by
    have h0 : aaNormal ((aaOfReal θ, 0, 0, 0) : KamPhase) = 0 := aaNormal_w6TorusPt _
    rw [show birkNormalPart (w8Psi hm n ξ θ) = aaNormal w' from birkNormalPart_aaMap 1 1 _ _]
    change aaTan 1 1 (aaOfReal ξ) w' + aaNormal w' -
      (aaTan 1 1 (aaOfReal ξ) (aaOfReal θ, 0, 0, 0) + aaNormal (aaOfReal θ, 0, 0, 0)) = _
    rw [h0]; abel
  have hst : Real.sqrt (w8tn 𝔱 n) ≥ 0 := Real.sqrt_nonneg _
  -- tangential coordinates
  have hcoord : ∀ b i, ‖aaTanCoord (aaOfReal ξ) w' b i -
      aaTanCoord (aaOfReal ξ) (aaOfReal θ, 0, 0, 0) b i‖ ≤
        (1 / 4 + 2 * π) * Real.sqrt (w8tn 𝔱 n) * e := fun b i => by
    obtain ⟨σ, hσ, hs⟩ := w8_birkSgn_real (b, modeIdx i)
    have hc := (w8Pi_coord hξP i)
    have hξi : 0 < ξ i := hα.trans hc.1
    have hpos := w8_torusShape_real hm n hξ θ i
    have e1 : aaTanCoord (aaOfReal ξ) w' b i = ((Real.sqrt (ξ i + w8Yact hm n ξ θ i) : ℝ) : ℂ) *
        cexp (-(σ : ℂ) * (2 * π * I * ((w8Phase hm n ξ θ i : ℝ) : ℂ))) := by
      unfold aaTanCoord
      rw [(w8TK_real hm n hξ θ).1, (w8TK_real hm n hξ θ).2, ← hs]
      simp only [aaOfReal]
      rw [← Complex.ofReal_add, aaSqrt_ofReal (by linarith)]
    have e2 : aaTanCoord (aaOfReal ξ) (aaOfReal θ, 0, 0, 0) b i =
        ((Real.sqrt (ξ i) : ℝ) : ℂ) * cexp (-(σ : ℂ) * (2 * π * I * ((θ i : ℝ) : ℂ))) := by
      unfold aaTanCoord
      rw [← hs]
      simp only [aaOfReal, _root_.Pi.zero_apply, add_zero]
      rw [aaSqrt_ofReal hξi.le]
    rw [e1, e2]
    refine (w8_coord_diff_le hξi (by linarith) hσ).trans ?_
    have hYi : |w8Yact hm n ξ θ i| ≤ w8rn 𝔱 n ^ 2 * e :=
      (norm_le_pi_norm (w8Yact hm n ξ θ) i).trans hY
    have hXi : |w8Phase hm n ξ θ i - θ i| ≤ e := (norm_le_pi_norm (w8Xang hm n ξ θ) i).trans hX
    have hsξ : 0 < Real.sqrt (ξ i) := Real.sqrt_pos.2 hξi
    have hsξt : Real.sqrt (ξ i) ≤ Real.sqrt (w8tn 𝔱 n) := Real.sqrt_le_sqrt (by linarith)
    -- `|y_i|/√ξ_i ≤ r² e/√ξ_i ≤ (ξ_i/4) e/√ξ_i = √ξ_i e/4`
    have hy : |w8Yact hm n ξ θ i| / Real.sqrt (ξ i) ≤ Real.sqrt (ξ i) * e / 4 := by
      rw [div_le_iff₀ hsξ]
      have hsq := Real.mul_self_sqrt hξi.le
      have : w8rn 𝔱 n ^ 2 * e ≤ ξ i / 4 * e := mul_le_mul_of_nonneg_right (by linarith) he0
      nlinarith
    have h2 : 2 * π * Real.sqrt (ξ i) * |w8Phase hm n ξ θ i - θ i| ≤
        2 * π * Real.sqrt (w8tn 𝔱 n) * e := by
      have := Real.pi_pos
      have := abs_nonneg (w8Phase hm n ξ θ i - θ i)
      calc 2 * π * Real.sqrt (ξ i) * |w8Phase hm n ξ θ i - θ i|
          ≤ 2 * π * Real.sqrt (w8tn 𝔱 n) * |w8Phase hm n ξ θ i - θ i| := by gcongr
        _ ≤ _ := by gcongr
    have h3 : Real.sqrt (ξ i) * e / 4 ≤ Real.sqrt (w8tn 𝔱 n) * e / 4 := by gcongr
    nlinarith
  have hT := w8_tanDiff_norm_le (aaOfReal ξ) w' (aaOfReal θ, 0, 0, 0)
    (by have := Real.pi_pos; positivity) hcoord
  have hrt : w8rn 𝔱 n ≤ Real.sqrt (w8tn 𝔱 n) := by
    rw [show w8rn 𝔱 n = Real.sqrt (w8rn 𝔱 n ^ 2) from (Real.sqrt_sq hr.le).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hN' : ‖birkNormalPart (w8Psi hm n ξ θ)‖ ≤ Real.sqrt (w8tn 𝔱 n) * e :=
    hN.trans (mul_le_mul_of_nonneg_right hrt he0)
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hpi := Real.pi_lt_d2
  have hse : 0 ≤ Real.sqrt (w8tn 𝔱 n) * e := mul_nonneg hst he0
  nlinarith

/-- Step `stepW:w8:sc-gamma` (W3 `bpW:w3:gamma-real` (ii)): on `B^E_{r₁}`,
`‖Γ^ℝ x - x‖ ≤ √2 · 6√2 C_F ‖x‖³` and `‖Γ^ℝ x‖ ≤ 2‖x‖`. -/
theorem w8_gammaR_bounds (x : birkRealBall1 m 1) :
    ‖birkGammaR m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) x - (x : BirkReal)‖ ≤
        Real.sqrt 2 * (6 * Real.sqrt 2 * birkCF m 1 * ‖(x : BirkReal)‖ ^ 3) ∧
      ‖birkGammaR m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) x‖ ≤ 2 * ‖(x : BirkReal)‖ := by
  obtain ⟨ψ, hψ, hψb, hΓb⟩ :=
    birkGammaR_sub (hm := hm) (ha := zero_le_one) (hp := (by norm_num : (1 / 2 : ℝ) ≤ 1)) x
  refine ⟨?_, ?_⟩
  · have hΓx : birkGammaR m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1) x - (x : BirkReal) =
        birkPi (birkEmbed 1 (1 + 1) 1 (by norm_num) (birkZR ψ)) := by
      have := congrArg birkPi hψ
      rw [birkPi_birkZR, map_add, birkPi_birkZR] at this
      rw [this]; abel
    rw [hΓx]
    refine (norm_birkPi_le _).trans ?_
    refine (ContinuousLinearMap.le_of_opNorm_le _ (norm_birkEmbed_le 1 (1 + 1) 1 _) _).trans ?_
    rw [one_mul]
    exact (norm_birkZR_le ψ).trans (mul_le_mul_of_nonneg_left hψb (Real.sqrt_nonneg _))
  · have hs2 : Real.sqrt 2 ≤ 9 / 5 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have := norm_nonneg (x : BirkReal)
    calc _ ≤ 10 / 9 * Real.sqrt 2 * ‖(x : BirkReal)‖ := hΓb
      _ ≤ 10 / 9 * (9 / 5) * ‖(x : BirkReal)‖ := by gcongr
      _ = 2 * ‖(x : BirkReal)‖ := by ring

/-- Step `stepW:w8:sc-gamma`, arithmetic: if `X² ≤ 2c_A t`, `0 < t`, `2t ≤ 1`, then
`√2 · 6√2 C_F X³ ≤ E₆ t^{33/64}`. -/
theorem w8_gamma_arith (hm : 0 < m) {t X : ℝ} (ht : 0 < t) (ht2 : 2 * t ≤ 1) (hX : 0 ≤ X)
    (hX2 : X ^ 2 ≤ 2 * aaCA * t) :
    Real.sqrt 2 * (6 * Real.sqrt 2 * birkCF m 1 * X ^ 3) ≤ w8E6 m * t ^ (33 / 64 : ℝ) := by
  have hcA : (0 : ℝ) < aaCA := by unfold aaCA; norm_num
  have hCF := birkCF_pos m hm (p := 1) (by norm_num)
  have ht1 : t ≤ 1 := by linarith
  have hwS : X ≤ Real.sqrt (2 * aaCA * t) := Real.le_sqrt_of_sq_le hX2
  have hx3 : X ^ 3 ≤ Real.sqrt (2 * aaCA * t) ^ 3 := pow_le_pow_left₀ hX hwS 3
  have hcube : Real.sqrt (2 * aaCA * t) ^ 3 = (2 * w8cA) ^ (3 / 2 : ℝ) * t ^ (3 / 2 : ℝ) := by
    have e : (2 * aaCA * t) = (2 * w8cA) * t := rfl
    have hc2 : (0 : ℝ) ≤ 2 * w8cA := by unfold w8cA; norm_num
    rw [e, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.mul_rpow hc2 ht.le]
    norm_num
  have hE6 : w8E6 m = 6 * Real.sqrt 2 * birkCF m 1 * (2 * w8cA) ^ (3 / 2 : ℝ) := rfl
  have h32 : Real.sqrt 2 * t ^ (3 / 2 : ℝ) ≤ t ^ (33 / 64 : ℝ) := by
    have e1 : t ^ (3 / 2 : ℝ) = t ^ (33 / 64 : ℝ) * t ^ (63 / 64 : ℝ) := by
      rw [← Real.rpow_add ht]; norm_num
    have e2 : t ^ (63 / 64 : ℝ) ≤ t ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
    have e3 : Real.sqrt 2 * t ^ (1 / 2 : ℝ) ≤ 1 := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num), Real.sqrt_le_one]
      exact ht2
    have hp : 0 ≤ t ^ (33 / 64 : ℝ) := Real.rpow_nonneg ht.le _
    rw [e1]
    have := mul_le_mul_of_nonneg_left e2 (Real.sqrt_nonneg 2)
    nlinarith [Real.rpow_nonneg ht.le (63 / 64 : ℝ)]
  have hc0 : 0 ≤ 6 * Real.sqrt 2 * birkCF m 1 := by positivity
  have hq := mul_le_mul_of_nonneg_left hx3 (mul_nonneg (Real.sqrt_nonneg 2) hc0)
  rw [hcube] at hq
  have hE6p : 0 ≤ w8E6 m := by rw [hE6]; unfold w8cA; positivity
  calc Real.sqrt 2 * (6 * Real.sqrt 2 * birkCF m 1 * X ^ 3)
      = Real.sqrt 2 * (6 * Real.sqrt 2 * birkCF m 1) * X ^ 3 := by ring
    _ ≤ _ := hq
    _ = w8E6 m * (Real.sqrt 2 * t ^ (3 / 2 : ℝ)) := by rw [hE6]; ring
    _ ≤ w8E6 m * t ^ (33 / 64 : ℝ) := mul_le_mul_of_nonneg_left h32 hE6p

/-- Step `stepW:w8:sc-close`, arithmetic: `e ≤ E₅ t^{1/64}` gives
`162 √t e ≤ 162 E₅ t^{33/64}`. -/
theorem w8_tan_arith {t e E : ℝ} (ht : 0 < t) (he : e ≤ E * t ^ (1 / 64 : ℝ)) :
    162 * Real.sqrt t * e ≤ 162 * E * t ^ (33 / 64 : ℝ) := by
  have e1 : t ^ (33 / 64 : ℝ) = Real.sqrt t * t ^ (1 / 64 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; norm_num
  rw [e1]
  have := Real.sqrt_nonneg t
  have : Real.sqrt t * e ≤ Real.sqrt t * (E * t ^ (1 / 64 : ℝ)) :=
    mul_le_mul_of_nonneg_left he this
  nlinarith

/-- **Closeness and size on one shell** (blueprint `bpW:w8:shell-close`): for `ξ ∈ Γ_n` and real
`θ`, `‖K^{(n)}_ξ(θ) - τ_E K⁰_ξ(θ)‖ ≤ E₇ t_n^{33/64}` and `‖K^{(n)}_ξ(θ)‖ ≤ 2ρ_n`. -/
theorem w8_shellClose (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (hξp : ∀ i, 0 < ξ i) (θ : Fin 2 → ℝ) :
    ‖w8Kshell w8AA (w8HW hm n) ξ θ - linearTorus ξ hξp θ‖ ≤
        w8E7 m hm (w8Upstream m hm) * w8tn 𝔱 n ^ (33 / 64 : ℝ) ∧
      ‖w8Kshell w8AA (w8HW hm n) ξ θ‖ ≤ 2 * w8rho 𝔱 n := by
  obtain ⟨hn2, h1, h2, -, -, hb, -⟩ := w8Psi_ball hm n hξ θ
  have ht := (w8_shell_consts hm n).2.2.2.2.2.2.1
  have heE : w8ShellEtor m hm n ≤ w8E5 m hm (w8Upstream m hm) * w8tn 𝔱 n ^ (1 / 64 : ℝ) :=
    (w8_etor hm n).2.1 ▸ (w8_etor hm n).1
  have ht2 : 2 * w8tn 𝔱 n ≤ 1 := by
    have := (w8tn_facts hm (w8Upstream m hm) n).2.1
    have := (w8tn_facts hm (w8Upstream m hm) n).2.2.1
    norm_num at *
    linarith
  rw [w8Kshell_eq, w8KOfBirk_of_mem hb]
  obtain ⟨hΓ, hsz⟩ := w8_gammaR_bounds hm ⟨birkPi (w8Psi hm n ξ θ), hb⟩
  have hxw : ‖birkPi (w8Psi hm n ξ θ)‖ ≤ ‖w8Psi hm n ξ θ‖ := norm_birkPi_le _
  refine ⟨?_, ?_⟩
  · have hX2 : ‖birkPi (w8Psi hm n ξ θ)‖ ^ 2 ≤ 2 * aaCA * w8tn 𝔱 n :=
      (pow_le_pow_left₀ (norm_nonneg _) hxw 2).trans (by linarith)
    have hg := hΓ.trans (w8_gamma_arith hm ht ht2 (norm_nonneg _) hX2)
    have hx0 : ‖birkPi (w8Psi hm n ξ θ) - linearTorus ξ hξp θ‖ ≤
        162 * Real.sqrt (w8tn 𝔱 n) * w8ShellEtor m hm n := by
      rw [← w8_birkPi_linearTorus ξ hξp θ, ← map_sub]
      exact (norm_birkPi_le _).trans (w8_shellDist hm n hξ θ)
    have htan := w8_tan_arith ht heE
    refine (norm_sub_le_norm_sub_add_norm_sub _ (birkPi (w8Psi hm n ξ θ)) _).trans ?_
    have : w8E7 m hm (w8Upstream m hm) * w8tn 𝔱 n ^ (33 / 64 : ℝ) =
        w8E6 m * w8tn 𝔱 n ^ (33 / 64 : ℝ) +
          162 * w8E5 m hm (w8Upstream m hm) * w8tn 𝔱 n ^ (33 / 64 : ℝ) := by
      unfold w8E7; ring
    rw [this]
    linarith
  · have hρ : ‖w8Psi hm n ξ θ‖ ≤ w8rho 𝔱 n := Real.le_sqrt_of_sq_le hn2.le
    linarith

end KAM.Wave

end
