/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.FT.Bracket
public import KAM.EffectiveStability.Poly.Bound
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Fourier–Taylor polynomials: computable majorants (track B, B4-FT)

With rational data `πub ≥ π` (`ftPiUB = 3.1416`), a strip parameter `lam > 0` and radii `b`:

* `ftSupBound P πub lam b = ∑ (2 πub)^e (|c| + |s|) lam^{|k|₁} ∏ b_i^{α_i}` (exact `ℚ`);
* `norm_ftEvalC_le_supBound`: `‖ftEvalC P z‖ ≤ ftSupBound P πub lam b` whenever `P` fits in `n`
  variables, `|Im φ_i| ≤ log lam / (2π)` and `‖J_i‖ ≤ b_i`;
* `abs_ftEvalR_le_supBound`: the real version (`lam = 1`, angles arbitrary);
* `ftAngleDriftBound P j πub b = ∑ (2 πub)^{e+1} |k_j| (|c| + |s|) ∏ b_i^{α_i}` and
  `abs_fderiv_ftEvalR_le`: `|fderiv ℝ (ftEvalR P) x (Pi.single j 1, 0)| ≤ ftAngleDriftBound …`
  whenever `|J_i| ≤ b_i` (the angle-drift form of B1-T).

The file ends with kernel-evaluation smoke tests of `ftEqCheck`.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability

/-- The rational upper bound `3.1416` for `π`. -/
def ftPiUB : ℚ := 31416 / 10000

theorem pi_le_ftPiUB : Real.pi ≤ ((ftPiUB : ℚ) : ℝ) := by
  have := Real.pi_lt_d4
  unfold ftPiUB
  norm_num at this ⊢
  linarith

/-- `|k|₁ = ∑ |k_i|` of a frequency list. -/
def ftL1 (k : List ℤ) : ℕ := ∑ i ∈ Finset.range k.length, (k.getD i 0).natAbs

/-- The action majorant `∏ b_i^{α_i}`. -/
def ftBPow (α : List ℕ) (b : List ℚ) : ℚ :=
  ∏ i ∈ Finset.range α.length, b.getD i 0 ^ α.getD i 0

/-- The majorant of one monomial. -/
def ftMonoBound (m : FTMono) (πub lam : ℚ) (b : List ℚ) : ℚ :=
  (2 * πub) ^ m.e * (|m.c| + |m.s|) * lam ^ ftL1 m.k * ftBPow m.α b

/-- Computable majorant of `‖ftEvalC P z‖` on the strip of width `log lam` with action radii `b`. -/
def ftSupBound (P : FTPoly) (πub lam : ℚ) (b : List ℚ) : ℚ :=
  (P.map fun m => ftMonoBound m πub lam b).sum

/-- The angle-drift majorant `∑ (2 πub)^{e+1} |k_j| (|c| + |s|) ∏ b_i^{α_i}`. -/
def ftAngleDriftBound (P : FTPoly) (j : ℕ) (πub : ℚ) (b : List ℚ) : ℚ :=
  (P.map fun m => (2 * πub) ^ (m.e + 1) * |(m.k.getD j 0 : ℚ)| * (|m.c| + |m.s|) *
    ftBPow m.α b).sum

/-! ### Complex trigonometric bounds -/

theorem norm_cos_le_exp_im (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp]
  have a1 : Real.exp (w * Complex.I).re ≤ Real.exp |w.im| :=
    Real.exp_le_exp.2 (by simp [neg_le_abs])
  have a2 : Real.exp (-w * Complex.I).re ≤ Real.exp |w.im| :=
    Real.exp_le_exp.2 (by simp [le_abs_self])
  linarith

theorem norm_sin_le_exp_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin, norm_div, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, Complex.norm_I, mul_one, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_exp, Complex.norm_exp]
  have a1 : Real.exp (w * Complex.I).re ≤ Real.exp |w.im| :=
    Real.exp_le_exp.2 (by simp [neg_le_abs])
  have a2 : Real.exp (-w * Complex.I).re ≤ Real.exp |w.im| :=
    Real.exp_le_exp.2 (by simp [le_abs_self])
  linarith

/-! ### Generic monomial bound -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

theorem ftNorm_jProd_le (α : List ℕ) (b : List ℚ) (hα : ∀ k, n ≤ k → α.getD k 0 = 0)
    (J : Fin n → 𝕜) (hJ : ∀ i : Fin n, ‖J i‖ ≤ ((b.getD i 0 : ℚ) : ℝ)) :
    ‖ftJProd α J‖ ≤ ((ftBPow α b : ℚ) : ℝ) := by
  unfold ftJProd ftBPow
  rw [Rat.cast_prod]
  set f : ℕ → ℝ := fun k => (((b.getD k 0 ^ α.getD k 0 : ℚ)) : ℝ) with hf
  have hz : ∏ k ∈ Finset.range α.length, f k = ∏ i : Fin n, f i := by
    refine CartPoly.prod_range_eq_univ f _ n fun k hk => ?_
    have h0 : α.getD k 0 = 0 := by
      rcases hk with hk | hk
      · exact hα k hk
      · exact ftGetD_zero_of_length_le α k hk
    simp only [hf, h0, pow_zero, Rat.cast_one]
  rw [hz, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  simp only [hf]
  push_cast
  exact pow_le_pow_left₀ (norm_nonneg _) (hJ i) _

variable (cf sf : 𝕜 → 𝕜) (p : 𝕜)

theorem norm_ftMonoEvalG_le (πub lam : ℚ) (b : List ℚ) (m : FTMono)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (hp : ‖2 * p‖ ≤ ((2 * πub : ℚ) : ℝ))
    (hc : ‖cf (2 * p * ftPhase m.k z.1)‖ ≤ ((lam ^ ftL1 m.k : ℚ) : ℝ))
    (hs : ‖sf (2 * p * ftPhase m.k z.1)‖ ≤ ((lam ^ ftL1 m.k : ℚ) : ℝ))
    (hα : ∀ k, n ≤ k → m.α.getD k 0 = 0)
    (hJ : ∀ i : Fin n, ‖z.2 i‖ ≤ ((b.getD i 0 : ℚ) : ℝ)) :
    ‖ftMonoEvalG cf sf p m z‖ ≤ ((ftMonoBound m πub lam b : ℚ) : ℝ) := by
  unfold ftMonoEvalG ftMonoBound
  have hnc : ∀ r : ℚ, ‖(r : 𝕜)‖ = |(r : ℝ)| := fun r => by
    rw [← RCLike.ofReal_ratCast, RCLike.norm_ofReal]
  have hX : ‖(m.c : 𝕜) * cf (2 * p * ftPhase m.k z.1) + (m.s : 𝕜) * sf (2 * p * ftPhase m.k z.1)‖
      ≤ (|(m.c : ℝ)| + |(m.s : ℝ)|) * ((lam ^ ftL1 m.k : ℚ) : ℝ) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hnc, hnc]
    nlinarith [abs_nonneg (m.c : ℝ), abs_nonneg (m.s : ℝ),
      norm_nonneg (cf (2 * p * ftPhase m.k z.1)),
      norm_nonneg (sf (2 * p * ftPhase m.k z.1)),
      mul_le_mul_of_nonneg_left hc (abs_nonneg (m.c : ℝ)),
      mul_le_mul_of_nonneg_left hs (abs_nonneg (m.s : ℝ))]
  have hJp := ftNorm_jProd_le m.α b hα z.2 hJ
  rw [norm_mul, norm_mul, norm_pow]
  have h1 : ‖2 * p‖ ^ m.e ≤ (((2 * πub : ℚ) : ℝ)) ^ m.e :=
    pow_le_pow_left₀ (norm_nonneg _) hp _
  have h0 : 0 ≤ (((2 * πub : ℚ) : ℝ)) ^ m.e := (pow_nonneg (norm_nonneg _) _).trans h1
  have h2 := mul_le_mul h1 hX (norm_nonneg _) h0
  have h3 := mul_le_mul h2 hJp (norm_nonneg _) (by
    have h5 : 0 ≤ ((lam ^ ftL1 m.k : ℚ) : ℝ) := (norm_nonneg _).trans hc
    positivity)
  refine h3.trans (le_of_eq ?_)
  push_cast
  ring

omit [RCLike 𝕜] in
theorem ftSupBound_cons (m : FTMono) (P : FTPoly) (πub lam : ℚ) (b : List ℚ) :
    ftSupBound (m :: P) πub lam b = ftMonoBound m πub lam b + ftSupBound P πub lam b := by
  simp [ftSupBound]

theorem norm_ftEvalG_le_supBound (πub lam : ℚ) (b : List ℚ) (P : FTPoly) (hP : FTFits n P)
    (z : (Fin n → 𝕜) × (Fin n → 𝕜)) (hp : ‖2 * p‖ ≤ ((2 * πub : ℚ) : ℝ))
    (hc : ∀ m ∈ P, ‖cf (2 * p * ftPhase m.k z.1)‖ ≤ ((lam ^ ftL1 m.k : ℚ) : ℝ))
    (hs : ∀ m ∈ P, ‖sf (2 * p * ftPhase m.k z.1)‖ ≤ ((lam ^ ftL1 m.k : ℚ) : ℝ))
    (hJ : ∀ i : Fin n, ‖z.2 i‖ ≤ ((b.getD i 0 : ℚ) : ℝ)) :
    ‖ftEvalG cf sf p P z‖ ≤ ((ftSupBound P πub lam b : ℚ) : ℝ) := by
  induction P with
  | nil => simp [ftSupBound]
  | cons m P ih =>
    have h1 := norm_ftMonoEvalG_le cf sf p πub lam b m z hp (hc m (List.mem_cons_self ..))
      (hs m (List.mem_cons_self ..)) (fun k hk => (hP m (List.mem_cons_self ..) k hk).2) hJ
    have h2 := ih (fun m' hm' => hP m' (List.mem_cons_of_mem _ hm'))
      (fun m' hm' => hc m' (List.mem_cons_of_mem _ hm'))
      (fun m' hm' => hs m' (List.mem_cons_of_mem _ hm'))
    rw [ftSupBound_cons, Rat.cast_add, ftEvalG_cons]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)

end Generic

/-! ### Complex and real sup bounds -/

variable {n : ℕ}

theorem ftSum_range_eq_fin (g : ℕ → ℝ) (W : ℕ) (h : ∀ i, n ≤ i ∨ W ≤ i → g i = 0) :
    ∑ i ∈ Finset.range W, g i = ∑ i : Fin n, g i := by
  rw [CartPoly.sum_range_eq_of_zero g W n h, Finset.sum_range g]

/-- The imaginary part of the phase is controlled by the strip width. -/
theorem abs_im_phase_le (k : List ℤ) (hk : ∀ i, n ≤ i → k.getD i 0 = 0) (lam : ℚ)
    (z : (Fin n → ℂ)) (hφ : ∀ i, |(z i).im| ≤ Real.log lam / (2 * Real.pi)) :
    |(2 * (Real.pi : ℂ) * ftPhase k z).im| ≤ (ftL1 k : ℝ) * Real.log lam := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have him : (2 * (Real.pi : ℂ) * ftPhase k z).im =
      ∑ i : Fin n, (2 * Real.pi * ((k.getD i 0 : ℤ) : ℝ)) * (z i).im := by
    simp only [ftPhase, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (2 * (Real.pi : ℂ) * (((k.getD i 0 : ℤ) : ℂ) * z i)) =
        ((2 * Real.pi * ((k.getD i 0 : ℤ) : ℝ) : ℝ) : ℂ) * z i := by push_cast; ring
    rw [this, Complex.im_ofReal_mul]
  have hL : (ftL1 k : ℝ) * Real.log lam =
      ∑ i : Fin n, (|((k.getD i 0 : ℤ) : ℝ)| * Real.log lam) := by
    unfold ftL1
    push_cast
    rw [Finset.sum_mul]
    rw [ftSum_range_eq_fin (n := n) (fun i => ((k.getD i 0).natAbs : ℝ) * Real.log lam) k.length
      (fun i hi => by
        rcases hi with hi | hi
        · simp only [hk i hi, Int.natAbs_zero, Nat.cast_zero, zero_mul]
        · simp only [ftGetD_zero_of_length_le k i hi, Int.natAbs_zero, Nat.cast_zero, zero_mul])]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [him, hL]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have := hφ i
  have h2 : 2 * Real.pi * |(z i).im| ≤ Real.log lam := by
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    rwa [mul_div_cancel₀ _ (by positivity : (2 * Real.pi) ≠ 0)] at this
  nlinarith [abs_nonneg (((k.getD i 0 : ℤ) : ℝ))]

/-- `‖P.ftEvalC z‖ ≤ ftSupBound P πub lam b` on the strip. -/
theorem norm_ftEvalC_le_supBound (P : FTPoly) (hP : FTFits n P) {πub lam : ℚ} (b : List ℚ)
    (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (hlam : 0 < lam) (z : (Fin n → ℂ) × (Fin n → ℂ))
    (hφ : ∀ i, |(z.1 i).im| ≤ Real.log lam / (2 * Real.pi))
    (hJ : ∀ i : Fin n, ‖z.2 i‖ ≤ ((b.getD i 0 : ℚ) : ℝ)) :
    ‖ftEvalC P z‖ ≤ ((ftSupBound P πub lam b : ℚ) : ℝ) := by
  have hp : ‖2 * (Real.pi : ℂ)‖ ≤ ((2 * πub : ℚ) : ℝ) := by
    have : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; simp
    rw [this]; push_cast; linarith
  have hex : ∀ m ∈ P, Real.exp |(2 * (Real.pi : ℂ) * ftPhase m.k z.1).im| ≤
      ((lam ^ ftL1 m.k : ℚ) : ℝ) := by
    intro m hm
    have h1 := abs_im_phase_le m.k (fun i hi => (hP m hm i hi).1) lam z.1 hφ
    have h2 := Real.exp_le_exp.2 h1
    rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hlam)] at h2
    push_cast
    exact h2
  exact norm_ftEvalG_le_supBound Complex.cos Complex.sin (Real.pi : ℂ) πub lam b P hP z hp
    (fun m hm => (norm_cos_le_exp_im _).trans (hex m hm))
    (fun m hm => (norm_sin_le_exp_im _).trans (hex m hm)) hJ

/-- Real version of `norm_ftEvalC_le_supBound` (`lam = 1`; the angles are arbitrary). -/
theorem abs_ftEvalR_le_supBound (P : FTPoly) (hP : FTFits n P) {πub : ℚ} (b : List ℚ)
    (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (x : (Fin n → ℝ) × (Fin n → ℝ))
    (hJ : ∀ i : Fin n, |x.2 i| ≤ ((b.getD i 0 : ℚ) : ℝ)) :
    |ftEvalR P x| ≤ ((ftSupBound P πub 1 b : ℚ) : ℝ) := by
  have hp : ‖2 * Real.pi‖ ≤ ((2 * πub : ℚ) : ℝ) := by
    rw [Real.norm_of_nonneg (by positivity)]; push_cast; linarith
  have h1 : ∀ m ∈ P, ‖Real.cos (2 * Real.pi * ftPhase m.k x.1)‖ ≤ (((1 : ℚ) ^ ftL1 m.k : ℚ) : ℝ) :=
    fun m _ => by simpa using Real.abs_cos_le_one _
  have h2 : ∀ m ∈ P, ‖Real.sin (2 * Real.pi * ftPhase m.k x.1)‖ ≤ (((1 : ℚ) ^ ftL1 m.k : ℚ) : ℝ) :=
    fun m _ => by simpa using Real.abs_sin_le_one _
  show |ftEvalG Real.cos Real.sin Real.pi P x| ≤ _
  simpa using norm_ftEvalG_le_supBound Real.cos Real.sin Real.pi πub 1 b P hP x hp h1 h2
    (fun i => by simpa using hJ i)

theorem ftSupBound_dφ (P : FTPoly) (j : ℕ) (πub : ℚ) (b : List ℚ) :
    ftSupBound (ftDφ j P) πub 1 b = ftAngleDriftBound P j πub b := by
  unfold ftSupBound ftAngleDriftBound ftDφ
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp, ftMonoBound, ftMonoDφ, abs_mul, abs_neg, one_pow, mul_one]
  ring

/-- The B1-T drift form: `|∂_{φ_j} P| ≤ ftAngleDriftBound P j πub b` whenever `|J_i| ≤ b_i`. -/
theorem abs_fderiv_ftEvalR_le (P : FTPoly) (hP : FTFits n P) {πub : ℚ} (b : List ℚ)
    (hπ : Real.pi ≤ ((πub : ℚ) : ℝ)) (x : (Fin n → ℝ) × (Fin n → ℝ))
    (hJ : ∀ i : Fin n, |x.2 i| ≤ ((b.getD i 0 : ℚ) : ℝ)) (j : Fin n) :
    |fderiv ℝ (fun x : (Fin n → ℝ) × (Fin n → ℝ) => ftEvalR P x) x (Pi.single j 1, 0)| ≤
      ((ftAngleDriftBound P j πub b : ℚ) : ℝ) := by
  rw [ftEvalR_fderiv_dφ, ← ftSupBound_dφ]
  exact abs_ftEvalR_le_supBound _ (ftFits_dφ j hP) b hπ x hJ

/-! ### Smoke tests: kernel evaluation of the identity checker -/

section Test

example : ftFitsCheck 2 (ftMul (ftCosMode [1, 1]) (ftJVar 1)) = true := by decide +kernel
-- `{cos(2πφ₀), J₀} = -2π sin(2πφ₀)`
example : ftEqCheck (ftBracket (ftCosMode [1]) (ftJVar 0)) [⟨[1], [], 1, 0, -1⟩] = true := by
  decide +kernel
-- `{J₀, cos(2πφ₀)} = 2π sin(2πφ₀)`
example : ftEqCheck (ftBracket (ftJVar 0) (ftCosMode [1])) [⟨[1], [], 1, 0, 1⟩] = true := by
  decide +kernel
-- `sin² = (1 - cos 2·)/2`
example : ftEqCheck (ftMul (ftSinMode [1]) (ftSinMode [1]))
    (ftSmul (1 / 2) (ftSub (ftConst 1) (ftCosMode [2]))) = true := by decide +kernel
-- `cos² + sin² = 1`
example : ftEqCheck (ftAdd (ftMul (ftCosMode [1, 2]) (ftCosMode [1, 2]))
    (ftMul (ftSinMode [1, 2]) (ftSinMode [1, 2]))) (ftConst 1) = true := by decide +kernel
-- canonical sign: `sin(-x) = -sin x`
example : ftEqCheck (ftSinMode [-1, 2]) (ftNeg (ftSinMode [1, -2])) = true := by decide +kernel
-- Leibniz in the first slot: `{cos(2πφ₀)·J₀, J₀} = -2π sin(2πφ₀)·J₀`
example : ftEqCheck (ftBracket (ftMul (ftCosMode [1]) (ftJVar 0)) (ftJVar 0))
    [⟨[1], unitExp 0 1, 1, 0, -1⟩] = true := by decide +kernel
-- `{cos(2π(φ₀+φ₁)), J₀ J₁}` : two modes
example : ftEqCheck (ftBracket (ftCosMode [1, 1]) (ftMul (ftJVar 0) (ftJVar 1)))
    (ftAdd [⟨[1, 1], unitExp 1 1, 1, 0, -1⟩] [⟨[1, 1], unitExp 0 1, 1, 0, -1⟩]) = true := by
  decide +kernel
example : ftEqCheck (ftCosMode [1]) (ftSinMode [1]) = false := by decide +kernel

end Test

end KAM.EffectiveStability
