/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.LieAnalytic
public import KAM.Wave.Birkhoff.LiePlus

/-!
# Analyticity of `Γ_t - id` into `𝔚⁺` (blueprint-W `bpW:w3:flow` (i))

Package W3-FLOW, blueprint label `bpW:w3:flow`.

In the two-space setting of `LiePlus` (`ι : F → E`, `S : E³ → F`, `T = ι ∘ S`):
`lieMultiF ι S k : E^{2(k+1)+1} → F` is the `F`-valued Lie coefficient `Φ_{k+1}`
(`ι ∘ Φ^F_k = Φ_{k+1}`, bound `m_{k+1} C^{k+1}`), `lieSeriesF` the power series with coefficient
`t^{k+1} Φ^F_k` in degree `2(k+1)+1`, and `liePsiSum` the sum `ψ_t(w)` with `ι ψ_t(w) = Γ_t(w) - w`.
`liePsiSum_hasFPowerSeriesOnBall`: `ψ_t` is given by this series on `‖w‖ < ρ`, hence analytic
as a map into `F`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  (ι : F →L[ℂ] E) (S : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) F)

/-- The `F`-valued Lie coefficient `Φ^F_k`: `(k+1) Φ^F_k = Σ_{a+b+c=k} S(Φ_a, Φ_b, Φ_c)`. -/
def lieMultiF (k : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin (2 * (k + 1) + 1) => E) F :=
  ((1 : ℂ) / ((k : ℂ) + 1)) • ∑ x ∈ Finset.Nat.antidiagonalTuple 3 k,
    lieBlockT S x (fun j => lieMulti (lieT ι S) (x j)) (2 * (k + 1) + 1)

theorem lieMultiF_const (w : E) (k : ℕ) :
    lieMultiF ι S k (fun _ => w) = liePsi ι S w (k + 1) := by
  unfold lieMultiF liePsi
  simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
  simp only [Fin.sum_univ_three] at hx'
  rw [lieBlockT, dif_pos (sum_blocks hx), lieBlock_const, lieVec_eq]
  congr 1
  funext j
  exact lieMulti_const _ _ _

variable {C : ℝ} (hC : 0 ≤ C) (hι : ‖ι‖ ≤ 1) (hS : ‖S‖ ≤ C)

include hC hι hS in
theorem norm_lieMultiF_le (k : ℕ) : ‖lieMultiF ι S k‖ ≤ birkLieM (k + 1) * C ^ (k + 1) := by
  have hT : ‖lieT ι S‖ ≤ C := by
    refine ContinuousMultilinearMap.opNorm_le_bound hC fun v => ?_
    rw [lieT_apply]
    have hSv : ‖S v‖ ≤ C * ∏ i, ‖v i‖ :=
      (S.le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (by positivity))
    calc ‖ι (S v)‖ ≤ ‖ι‖ * ‖S v‖ := ι.le_opNorm _
      _ ≤ 1 * ‖S v‖ := mul_le_mul_of_nonneg_right hι (norm_nonneg _)
      _ ≤ C * ∏ i, ‖v i‖ := by rw [one_mul]; exact hSv
  have := lie_step_A (G := ContinuousMultilinearMap ℂ (fun _ : Fin (2 * (k + 1) + 1) => E) F)
    k C 1 (fun x => lieBlockT S x (fun j => lieMulti (lieT ι S) (x j)) (2 * (k + 1) + 1))
    (fun x hx => ?_)
  · simpa [lieMultiF] using this
  · have hx' := Finset.Nat.mem_antidiagonalTuple.1 hx
    simp only [Fin.sum_univ_three] at hx'
    rw [lieBlockT, dif_pos (sum_blocks hx)]
    refine (norm_lieBlock_le S x _ _ _).trans ?_
    simp only [Fin.prod_univ_three, one_pow, mul_one]
    have u0 := norm_lieMulti_le (lieT ι S) hC hT (x 0)
    have u1 := norm_lieMulti_le (lieT ι S) hC hT (x 1)
    have u2 := norm_lieMulti_le (lieT ι S) hC hT (x 2)
    have m0 := birkLieM_nonneg (x 0)
    have m1 := birkLieM_nonneg (x 1)
    have hb : ‖lieMulti (lieT ι S) (x 0)‖ * ‖lieMulti (lieT ι S) (x 1)‖ *
        ‖lieMulti (lieT ι S) (x 2)‖ ≤
        (birkLieM (x 0) * C ^ x 0) * (birkLieM (x 1) * C ^ x 1) * (birkLieM (x 2) * C ^ x 2) :=
      mul_le_mul (mul_le_mul u0 u1 (norm_nonneg _) (by positivity)) u2 (norm_nonneg _)
        (by positivity)
    refine (mul_le_mul hS hb (by positivity) hC).trans (le_of_eq ?_)
    have : C ^ (k + 1) = C * (C ^ x 0 * C ^ x 1 * C ^ x 2) := by
      rw [← pow_add, ← pow_add, pow_succ']; congr 2; omega
    rw [this]; ring

/-- The power series of `ψ_t = Γ_t - id` in `F`: coefficient `t^{k+1} Φ^F_k` in degree
`2(k+1)+1`, zero otherwise. -/
def lieSeriesF (t : ℝ) : FormalMultilinearSeries ℂ E F := fun n =>
  if h : n % 2 = 1 ∧ 3 ≤ n then
    ContinuousMultilinearMap.domDomCongr (finCongr (by omega : 2 * (n / 2 - 1 + 1) + 1 = n))
      (((t : ℂ) ^ (n / 2)) • lieMultiF ι S (n / 2 - 1))
  else 0

theorem lieSeriesF_const (t : ℝ) (n : ℕ) (y : E) :
    lieSeriesF ι S t n (fun _ => y) =
      if n % 2 = 1 ∧ 3 ≤ n then ((t : ℂ) ^ (n / 2)) • liePsi ι S y (n / 2) else 0 := by
  unfold lieSeriesF
  split_ifs with h
  · simp only [ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.smul_apply,
      lieMultiF_const]
    rw [show n / 2 - 1 + 1 = n / 2 by omega]
  · simp

include hC hι hS in
theorem norm_lieSeriesF_le (t : ℝ) (n : ℕ) :
    ‖lieSeriesF ι S t n‖ ≤ if n % 2 = 1 ∧ 3 ≤ n then (2 * |t| * C) ^ (n / 2) else 0 := by
  unfold lieSeriesF
  split_ifs with h
  · rw [ContinuousMultilinearMap.norm_domDomCongr, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    have hn : n / 2 - 1 + 1 = n / 2 := by omega
    have hm := birkLieM_le_pow (n / 2)
    have := norm_lieMultiF_le ι S hC hι hS (n / 2 - 1)
    have e1 : birkLieM (n / 2 - 1 + 1) = birkLieM (n / 2) := by rw [hn]
    have e2 : C ^ (n / 2 - 1 + 1) = C ^ (n / 2) := by rw [hn]
    rw [e1, e2] at this
    calc |t| ^ (n / 2) * ‖lieMultiF ι S (n / 2 - 1)‖ ≤
        |t| ^ (n / 2) * (2 ^ (n / 2) * C ^ (n / 2)) := by
          gcongr
          exact this.trans (by gcongr)
      _ = (2 * |t| * C) ^ (n / 2) := by rw [mul_pow, mul_pow]; ring
  · simp

/-- `ψ_t(w) = Σ_{k ≥ 1} t^k ψ_k(w)`, with `ι ψ_t(w) = Γ_t(w) - w`. -/
def liePsiSum (t : ℝ) (w : E) : F := ∑' k : ℕ, (t ^ (k + 1)) • liePsi ι S w (k + 1)

include hC hι hS in
theorem summable_liePsi (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    Summable fun k : ℕ => (t ^ (k + 1)) • liePsi ι S w (k + 1) := by
  have hT : ∀ v : Fin 3 → E, ‖S v‖ ≤ C * ∏ i, ‖v i‖ := fun v =>
    (S.le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (by positivity))
  have hz : ∀ k : ℕ, ‖(t ^ (k + 1)) • liePsi ι S w (k + 1)‖ ≤
      (2 * |t| * C * ‖w‖ ^ 2) ^ (k + 1) * ‖w‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    refine (mul_le_mul_of_nonneg_left (norm_liePsi_le ι S hC hι hT w k)
      (by positivity)).trans ?_
    have := lie_geom_bound (C := C) t ‖w‖ hC (norm_nonneg w) (k + 1)
    rwa [show 2 * (k + 1) + 1 = 2 * k + 3 by ring] at this
  exact (lie_tail_one (z := fun k => (t ^ k) • liePsi ι S w k) t ‖w‖ hC (norm_nonneg w) hq hz).1

include hC hι hS in
theorem liePsiSum_hasFPowerSeriesOnBall (t ρ : ℝ) (hρ : 0 < ρ)
    (hq : 2 * |t| * C * ρ ^ 2 ≤ 1 / 10) :
    HasFPowerSeriesOnBall (liePsiSum ι S t) (lieSeriesF ι S t) 0 (ENNReal.ofReal ρ) := by
  have h0 : 0 ≤ 2 * |t| * C * ρ ^ 2 := by positivity
  refine ⟨?_, by simpa using hρ, ?_⟩
  · show ((ρ.toNNReal : NNReal) : ENNReal) ≤ _
    refine FormalMultilinearSeries.le_radius_of_bound _ ρ fun n => ?_
    have := norm_lieSeriesF_le ι S hC hι hS t n
    rw [Real.coe_toNNReal ρ hρ.le]
    split_ifs at this with h
    · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      have e : (2 * k + 1) / 2 = k := by omega
      rw [e] at this
      calc ‖lieSeriesF ι S t (2 * k + 1)‖ * ρ ^ (2 * k + 1) ≤
          (2 * |t| * C) ^ k * ρ ^ (2 * k + 1) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = (2 * |t| * C * ρ ^ 2) ^ k * ρ := by
            rw [pow_succ, pow_mul, mul_pow]; ring
        _ ≤ 1 * ρ := by
            gcongr
            exact pow_le_one₀ h0 (by linarith)
        _ = ρ := one_mul ρ
    · have : ‖lieSeriesF ι S t n‖ ≤ 0 := this
      calc ‖lieSeriesF ι S t n‖ * ρ ^ n ≤ 0 * ρ ^ n :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = 0 := zero_mul _
        _ ≤ ρ := hρ.le
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have h2 : ENNReal.ofReal ‖y‖ < ENNReal.ofReal ρ := by rwa [ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 h2
    have hqy : 2 * |t| * C * ‖y‖ ^ 2 ≤ 1 / 10 := by
      have h1 : ‖y‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy'.le 2
      have h2 : 0 ≤ 2 * |t| * C := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    have hs := (summable_liePsi ι S hC hι hS t y hqy).hasSum
    rw [zero_add]
    have hinj : Function.Injective (fun k : ℕ => 2 * (k + 1) + 1) := fun a b h => by
      simp only at h; omega
    rw [← hinj.hasSum_iff (f := fun n : ℕ => lieSeriesF ι S t n fun _ => y)]
    · have e : ((fun n : ℕ => lieSeriesF ι S t n fun _ => y) ∘ fun k : ℕ => 2 * (k + 1) + 1) =
          fun k => (t ^ (k + 1)) • liePsi ι S y (k + 1) := by
        funext k
        simp only [Function.comp, lieSeriesF_const]
        rw [if_pos (by omega), show (2 * (k + 1) + 1) / 2 = k + 1 by omega, ← Complex.coe_smul]
        push_cast; rfl
      rw [e]; exact hs
    · intro n hn
      rw [lieSeriesF_const, if_neg]
      intro h
      exact hn ⟨n / 2 - 1, by show 2 * (n / 2 - 1 + 1) + 1 = n; omega⟩

omit [CompleteSpace E] [CompleteSpace F] in
theorem exists_lie_rho {C : ℝ} (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2)
    (hw : 40 * C * ‖w‖ ^ 2 < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ‖w‖ < ρ ∧ 2 * |t| * C * ρ ^ 2 ≤ 1 / 10 := by
  have h40 : 0 < 40 * C := by positivity
  have hw' : ‖w‖ ^ 2 < 1 / (40 * C) := by rw [lt_div_iff₀ h40]; linarith
  set r2 : ℝ := (‖w‖ ^ 2 + 1 / (40 * C)) / 2 with hr2
  have hr2a : ‖w‖ ^ 2 < r2 := by rw [hr2]; linarith
  have hr2b : r2 < 1 / (40 * C) := by rw [hr2]; linarith
  have hr2p : 0 < r2 := lt_of_le_of_lt (sq_nonneg _) hr2a
  refine ⟨Real.sqrt r2, Real.sqrt_pos.2 hr2p, Real.lt_sqrt (norm_nonneg w) |>.2 hr2a, ?_⟩
  rw [Real.sq_sqrt hr2p.le]
  have h1 : r2 * (40 * C) < 1 := by rwa [lt_div_iff₀ h40] at hr2b
  have h2 : 0 ≤ C * r2 := by positivity
  nlinarith [abs_nonneg t]

include hC hι hS in
theorem map_liePsiSum (t : ℝ) (w : E) (hq : 2 * |t| * C * ‖w‖ ^ 2 ≤ 1 / 10) :
    ι (liePsiSum ι S t w) = lieGamma (lieT ι S) t w - w := by
  have hT : ∀ v : Fin 3 → E, ‖lieT ι S v‖ ≤ C * ∏ i, ‖v i‖ := fun v => by
    rw [lieT_apply]
    have hSv : ‖S v‖ ≤ C * ∏ i, ‖v i‖ :=
      (S.le_opNorm v).trans (mul_le_mul_of_nonneg_right hS (by positivity))
    calc ‖ι (S v)‖ ≤ ‖ι‖ * ‖S v‖ := ι.le_opNorm _
      _ ≤ 1 * ‖S v‖ := mul_le_mul_of_nonneg_right hι (norm_nonneg _)
      _ ≤ C * ∏ i, ‖v i‖ := by rw [one_mul]; exact hSv
  unfold liePsiSum
  rw [ι.map_tsum (summable_liePsi ι S hC hι hS t w hq)]
  have hE := summable_lieTerm (lieT ι S) hC hT t w hq
  have hsplit : lieGamma (lieT ι S) t w - w =
      ∑' k, (t ^ (k + 1)) • lieSeq (lieT ι S) w (k + 1) := by
    unfold lieGamma
    rw [hE.tsum_eq_zero_add]
    simp only [pow_zero, one_smul, lieSeq_zero, add_sub_cancel_left]
  rw [hsplit]
  refine tsum_congr fun k => ?_
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul, map_liePsi]

include hC hι hS in
/-- (`bpW:w3:flow` (i)) `Γ_t - id`, as the `F`-valued `ψ_t`, is analytic at `w`
(`|t| < 2`, `40 C ‖w‖² < 1`). -/
theorem analyticAt_liePsiSum (hCp : 0 < C) (t : ℝ) (w : E) (ht : |t| < 2)
    (hw : 40 * C * ‖w‖ ^ 2 < 1) : AnalyticAt ℂ (liePsiSum ι S t) w := by
  obtain ⟨ρ, hρ, hwρ, hq⟩ := exists_lie_rho (E := E) hCp t w ht hw
  refine (liePsiSum_hasFPowerSeriesOnBall ι S hC hι hS t ρ hρ hq).analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 hwρ

end KAM.Wave

end
