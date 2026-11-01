/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK2c

/-!
# The field of `K₂`: the series identities (blueprint-W `bpW:w3:main`, Step XK2)

Package W3-MAIN, blueprint label `bpW:w3:main`.

`birkVn_zero_const`: `V_0(w,…,w) = X_{Z'}(w)`. `birkV_identity`: for `|s| < 2`,
`DΓ_s(w)(ι V_s) = ι X_{Z'}(Γ_s w)` with `V_s = Σ_n s^n V_n(w,…,w)`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include ha hp in
theorem birkVn_zero_const (w : BirkSpace) :
    birkVn m hm ha hp 0 (fun _ => w) = birkHamZX m hm ha hp w := by
  rw [← birkNz_const m hm ha hp]
  unfold birkVn
  rw [lieV_eval]
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero]
  unfold lieNsum
  rw [Finset.Nat.antidiagonalTuple_zero_right]
  simp only [Finset.sum_singleton, ContinuousMultilinearMap.sum_apply]
  rw [lieBlockT, dif_pos (by simp), lieBlock_const]
  congr 1
  funext j
  rw [lieMulti_const]
  simp [lieSeq_zero]

include hm hp in
theorem birkV_identity (s : ℝ) (hs : |s| < 2) (w : BirkSpace)
    (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    birkGammaD m hm ha hp s w (birkEmbed a (p + 1) p (by linarith)
      (∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w))) =
      birkEmbed a (p + 1) p (by linarith) (birkHamZX m hm ha hp (birkGamma m hm ha hp s w)) := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  obtain ⟨ρ, hρ, hwρ, hq⟩ := exists_rho1 (hm := hm) (hp := hp) w hw
  have h := lieV_identity (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkNz m hm ha hp) hCp.le (norm_birkEmbed_le _ _ _ _) hSn ρ hρ hq s hs.le w hwρ.le
  have e : (fun _ : Fin 3 => lieGamma (lieT (birkEmbed a (p + 1) p (by linarith))
      (birkS m hm ha hp)) s w) = fun _ => birkGamma m hm ha hp s w := rfl
  rw [e] at h
  have e2 : birkNz m hm ha hp (fun _ => birkGamma m hm ha hp s w) =
      birkHamZX m hm ha hp (birkGamma m hm ha hp s w) := birkNz_const m hm ha hp _
  rw [e2] at h
  exact h

variable (m hm ha hp) in
/-- `u_0 = 0`, `u_{n+1} = V_n(w,…,w)/(n+1)`: the coefficients of `Q(s) = Σ_k s^k u_k`
(`Q' = V_s`). -/
def uqF (w : BirkSpace) : ℕ → BirkSpace
  | 0 => 0
  | n + 1 => ((1 : ℝ) / ((n : ℝ) + 1)) • birkVn m hm ha hp n (fun _ => w)

include hm hp in
theorem summable_birkVn (t : ℝ) (ht : |t| ≤ 2) (w : BirkSpace)
    (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    Summable fun n : ℕ => ‖(t ^ n) • birkVn m hm ha hp n (fun _ => w)‖ := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  obtain ⟨ρ, hρ, hwρ, hq⟩ := exists_rho1 (hm := hm) (hp := hp) w hw
  exact summable_lieV (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkNz m hm ha hp) hCp.le (norm_birkEmbed_le _ _ _ _) hSn ρ hρ hq t ht w hwρ.le

include hm hp in
theorem hasDerivAt_Qseries (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) (s : ℝ)
    (hs : |s| < 2) :
    HasDerivAt (fun r : ℝ => ∑' k : ℕ, (r ^ k) • uqF m hm ha hp w k)
      (∑' n : ℕ, (s ^ n) • birkVn m hm ha hp n (fun _ => w)) s := by
  have hsum2 := summable_birkVn (ha := ha) (hm := hm) (hp := hp) 2 (by norm_num) w hw
  have hnorm : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (n + 1 - 1)) *
      ‖uqF m hm ha hp w (n + 1)‖ = ‖((2 : ℝ) ^ n) • birkVn m hm ha hp n (fun _ => w)‖ :=
    fun n => by
    simp only [uqF, Nat.add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_pow, abs_two]
    have : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1))]
    push_cast
    field_simp
  have hsum : Summable fun k : ℕ => (k : ℝ) * (2 : ℝ) ^ (k - 1) * ‖uqF m hm ha hp w k‖ := by
    refine (summable_nat_add_iff 1).1 ?_
    refine hsum2.congr fun n => ?_
    exact (hnorm n).symm
  have h := hasDerivAt_powSeries (uqF m hm ha hp w) s 2 (by simpa using hs) hsum
  refine h.congr_deriv ?_
  have hs2 : Summable fun k : ℕ => (((k : ℝ) * s ^ (k - 1))) • uqF m hm ha hp w k := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => (k : ℝ) * (2 : ℝ) ^ (k - 1) *
      ‖uqF m hm ha hp w k‖) hsum fun k => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, Nat.abs_cast]
    have : |s| ^ (k - 1) ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_left₀ (abs_nonneg _) hs.le _
    gcongr
  rw [hs2.tsum_eq_zero_add]
  simp only [uqF, smul_zero, zero_add, Nat.add_sub_cancel]
  refine tsum_congr fun n => ?_
  rw [smul_smul]
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  congr 1
  field_simp

end KAM.Wave

end
