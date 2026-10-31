/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK2e

/-!
# The bound for the field of `K₂` (blueprint-W `bpW:w3:main`, Step XK2)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`norm_birkY_le`: `‖V_s - V_0‖ ≤ 44 s C_* C_F ‖w‖⁵` for `0 ≤ s ≤ 1` (`V_s = DΓ_s⁻¹ X_{Z'}(Γ_s w)`),
`norm_birkXK2_le`: `‖X_{K₂}(w)‖₊ ≤ 22 C_* C_F ‖w‖⁵`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem norm_birkY_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (w : BirkSpace)
    (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖(∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w)) - birkHamZX m hm ha hp w‖ ≤
      44 * s * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hCs := waveCubicConst_nonneg p
  have hCF := (birkCF_pos m hm hp).le
  have hw0 := norm_nonneg w
  have hs2 : |s| < 2 := by rw [abs_lt]; constructor <;> linarith
  have hq := birk_q_le (hm := hm) (hp := hp) s w hs2 hw40
  obtain ⟨Ξ, B, BF, Ξ', hAB, hBA, hB2, hΞ, hΞn, hAι, hF1, hF2, hF3, hιB, hΞ'e, hΞ'n⟩ :=
    birkGammaD_inverse_plus (ha := ha) (hm := hm) (hp := hp) s w hq
  have hinj := birkEmbed_injective a (p + 1) p (by linarith)
  set Vs := ∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w) with hVs
  set y := birkGamma m hm ha hp s w with hy
  have hid := birkV_identity (ha := ha) (hm := hm) (hp := hp) s hs2 w hw
  -- `(1 + Ξ ι) Vs = X_{Z'}(Γ_s w)`
  have h1 : Vs + Ξ (birkEmbed a (p + 1) p (by linarith) Vs) = birkHamZX m hm ha hp y := by
    refine hinj ?_
    have h2 := DFunLike.congr_fun hΞ (birkEmbed a (p + 1) p (by linarith) Vs)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at h2
    rw [map_add, h2, ← hid]
    abel
  have h3 : Vs = BF (birkHamZX m hm ha hp y) := by
    have := DFunLike.congr_fun hF2 Vs
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply] at this
    rw [← h1]
    exact this.symm
  have hξ : ∀ f, BF f - f = Ξ' (birkEmbed a (p + 1) p (by linarith) f) := fun f => by
    refine hinj ?_
    have e1 := DFunLike.congr_fun hιB f
    have e2 := DFunLike.congr_fun hΞ'e (birkEmbed a (p + 1) p (by linarith) f)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at e1 e2
    rw [map_sub, e1, e2]
  have hι0 := norm_birkEmbed_le a (p + 1) p (by linarith)
  have hιf : ∀ f : BirkSpace, ‖birkEmbed a (p + 1) p (by linarith) f‖ ≤ ‖f‖ := fun f => by
    refine ((birkEmbed a (p + 1) p (by linarith)).le_opNorm f).trans ?_
    calc ‖birkEmbed a (p + 1) p (by linarith)‖ * ‖f‖ ≤ 1 * ‖f‖ :=
          mul_le_mul_of_nonneg_right hι0 (norm_nonneg f)
      _ = ‖f‖ := one_mul _
  have hBFn : ∀ f, ‖BF f - f‖ ≤ 20 * s * birkCF m p * ‖w‖ ^ 2 * ‖f‖ := fun f => by
    rw [hξ f]
    refine (Ξ'.le_opNorm _).trans ?_
    rw [abs_of_nonneg hs0] at hΞ'n
    exact mul_le_mul hΞ'n (hιf f) (norm_nonneg _) (by positivity)
  have hΓ := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) s w hq
  have hd := norm_birkGamma_sub_le (ha := ha) (hm := hm) (hp := hp) s w hq
  rw [abs_of_nonneg hs0] at hd
  have hX1 := norm_birkQuartX_sub_le m hm ha hp (birkCoefZ_isCoef m hm) y w
  have hX2 := norm_birkHamZX_le m hm ha hp w
  have hmax : max ‖y‖ ‖w‖ ≤ 10 / 9 * ‖w‖ := max_le hΓ (by linarith)
  have hmax2 : (max ‖y‖ ‖w‖) ^ 2 ≤ (10 / 9 * ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (le_trans (norm_nonneg _) (le_max_left _ _)) hmax 2
  have hdiff : ‖birkHamZX m hm ha hp y - birkHamZX m hm ha hp w‖ ≤
      3 * waveCubicConst p * (10 / 9 * ‖w‖) ^ 2 * (3 * s * birkCF m p * ‖w‖ ^ 3) := by
    calc _ ≤ 3 * waveCubicConst p * (max ‖y‖ ‖w‖) ^ 2 * ‖y - w‖ := hX1
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hmax2 (by positivity))
          hd (norm_nonneg _) (by positivity)
  have hsplit : Vs - birkHamZX m hm ha hp w =
      BF (birkHamZX m hm ha hp y - birkHamZX m hm ha hp w) +
        (BF (birkHamZX m hm ha hp w) - birkHamZX m hm ha hp w) := by
    rw [h3, map_sub]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have t1 : ‖BF (birkHamZX m hm ha hp y - birkHamZX m hm ha hp w)‖ ≤
      2 * (3 * waveCubicConst p * (10 / 9 * ‖w‖) ^ 2 * (3 * s * birkCF m p * ‖w‖ ^ 3)) :=
    (BF.le_opNorm _).trans (mul_le_mul hF3 hdiff (norm_nonneg _) (by norm_num))
  have t2 : ‖BF (birkHamZX m hm ha hp w) - birkHamZX m hm ha hp w‖ ≤
      20 * s * birkCF m p * ‖w‖ ^ 2 * (waveCubicConst p * ‖w‖ ^ 3) :=
    (hBFn _).trans (mul_le_mul_of_nonneg_left hX2 (by positivity))
  have hnn : 0 ≤ s * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by positivity
  nlinarith [t1, t2]

include hm hp in
theorem birkXK2_eq_Q (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    (∑' k : ℕ, ((1 : ℝ) ^ k) • uqF m hm ha hp w k) - (1 : ℝ) • birkVn m hm ha hp 0 (fun _ => w) =
      birkXK2 m hm ha hp w := by
  have hsu : Summable fun k : ℕ => uqF m hm ha hp w k := by
    refine (summable_nat_add_iff 1).1 ?_
    have hs1 := summable_birkVn (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw
    refine Summable.of_norm_bounded hs1 fun n => ?_
    simp only [uqF, norm_smul, one_pow, one_smul, Real.norm_eq_abs]
    have : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) this
  have : (∑' k : ℕ, ((1 : ℝ) ^ k) • uqF m hm ha hp w k) =
      ∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)) • birkVn m hm ha hp n (fun _ => w) := by
    simp only [one_pow, one_smul]
    rw [hsu.tsum_eq_zero_add]
    simp only [uqF, zero_add]
    refine tsum_congr fun n => ?_
    rw [show ((1 : ℂ) / ((n : ℂ) + 1)) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) by push_cast; rfl,
      Complex.coe_smul]
    rfl
  rw [this, one_smul]; rfl

include hm hp in
/-- (`bpW:w3:main`, Step XK2) `‖X_{K₂}(w)‖₊ ≤ 22 C_* C_F ‖w‖⁵`. -/
theorem norm_birkXK2_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkXK2 m hm ha hp w‖ ≤ 22 * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by
  have hCs := waveCubicConst_nonneg p
  have hCF := (birkCF_pos m hm hp).le
  set M : ℝ := waveCubicConst p * birkCF m p * ‖w‖ ^ 5 with hM
  have hM0 : 0 ≤ M := by positivity
  set v0 : BirkSpace := birkVn m hm ha hp 0 (fun _ => w) with hv0
  set Q : ℝ → BirkSpace := fun r => ∑' k : ℕ, (r ^ k) • uqF m hm ha hp w k with hQ
  set X2 : ℝ → BirkSpace := fun r => Q r - r • v0 with hX2
  have hX2d : ∀ s : ℝ, |s| < 2 → HasDerivAt X2
      ((∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w)) - v0) s := fun s hs => by
    have dQ := hasDerivAt_Qseries (ha := ha) (hm := hm) (hp := hp) w hw s hs
    have h5 := (hasDerivAt_id s).smul_const v0
    rw [one_smul] at h5
    exact dQ.sub h5
  have hcont : ContinuousOn X2 (Set.Icc 0 1) := fun s hs =>
    (hX2d s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])).continuousAt.continuousWithinAt
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := X2) (f' := fun s => (∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w)) - v0)
    hcont (fun s hs => (hX2d s (by rw [abs_lt]; constructor <;> linarith [hs.1, hs.2])
      ).hasDerivWithinAt) (B := fun s => 22 * M * s ^ 2) (B' := fun s => 44 * M * s)
    (by
      have e3 : Q 0 = 0 := by
        simp only [hQ]
        rw [tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
        simp [uqF]
      simp [hX2, e3])
    (fun s => by
      have := ((hasDerivAt_pow 2 s).const_mul (22 * M))
      refine this.congr_deriv ?_
      simp; ring)
    (fun s hs => by
      have := norm_birkY_le (ha := ha) (hm := hm) (hp := hp) s hs.1 hs.2.le w hw
      have hv0z : v0 = birkHamZX m hm ha hp w := birkVn_zero_const w
      rw [hv0z]
      calc _ ≤ 44 * s * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := this
        _ = 44 * M * s := by rw [hM]; ring)
  have h1 := hbound (x := 1) ⟨zero_le_one, le_rfl⟩
  have e : X2 1 = birkXK2 m hm ha hp w := birkXK2_eq_Q (ha := ha) (hm := hm) (hp := hp) w hw
  rw [e] at h1
  calc ‖birkXK2 m hm ha hp w‖ ≤ 22 * M * 1 ^ 2 := h1
    _ = 22 * waveCubicConst p * birkCF m p * ‖w‖ ^ 5 := by rw [hM]; ring

end KAM.Wave

end
