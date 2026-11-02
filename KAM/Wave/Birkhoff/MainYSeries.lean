/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainYInt

/-!
# Power series of the integrand `Y(t,w)` (blueprint-W `bpW:w3:Yseries`)

Package W3-MAIN, blueprint label `bpW:w3:Yseries`.

With `ρ₁ = birkRho1 m p = ½(40 C_F)^{-1/2}` (`birkBall1_eq_ball`: `B_{ρ₁}` is the open ball of
radius `ρ₁`):
* `birkYj j : 𝔚^{2j+3} → 𝔚⁺`, continuous `(2j+3)`-linear: `Y_0 = 0`, `Y_j = V_j` (`j ≥ 1`);
* `summable_norm_birkYj`, `tsum_norm_birkYj_le`: `Σ_j ‖Y_j‖ ρ₁^{2j+3} ≤ 4 C_* ρ₁³`;
* `birkY_hasSum`, `summable_norm_birkY_terms`: `Y(t,w) = Σ_j t^j Y_j(w,…,w)` for `0 ≤ t ≤ 1`,
  `w ∈ B_{ρ₁}`, absolutely convergent;
* `birkYInt w = ∫₀¹ Y(t,w) dt` (Bochner interval integral of `t ↦ Y(t,w)` on `[0,1]`) and
  `birkYInt_hasSum`: `∫₀¹ Y(t,w) dt = Σ_j Y_j(w,…,w)/(j+1)`;
* `birkYSeries` (`q_{2j+3} = Y_j/(j+1)`: `birkYSeries_odd`; `q_n = 0` otherwise:
  `birkYSeries_eq_zero`); `hasFPowerSeriesOnBall_birkYInt`, `analyticOnNhd_birkYInt`: every
  extension of `w ↦ ∫₀¹ Y(t,w) dt` from `B_{ρ₁}` has the power series `q` on `B_{ρ₁}` and is
  analytic there;
* `birkYInt_rho`: `∫₀¹ Y(t,ϱw) dt = ϱ ∫₀¹ Y(t,w) dt`;
* `birkYInt_eq_birkXK2Ext`: `∫₀¹ Y(t,w) dt = X_{K₂}(w)` (the series used in `bpW:w3:main`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- `ρ₁ = ½ (40 C_F)^{-1/2}`. -/
def birkRho1 (m p : ℝ) : ℝ := 1 / (2 * Real.sqrt (40 * birkCF m p))

/-- (`bpW:w3:Yseries`) The coefficients `Y_j : 𝔚^{2j+3} → 𝔚⁺` of the integrand:
`Y_0 = 0` and `Y_j = V_j` for `j ≥ 1`. -/
def birkYj (j : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin (2 * j + 3) => BirkSpace) BirkSpace :=
  if j = 0 then 0 else birkVn m hm ha hp j

/-- (`bpW:w3:Yseries`) The formal series `q` with `q_{2j+3} = Y_j/(j+1)` and `q_n = 0`
otherwise. -/
def birkYSeries : FormalMultilinearSeries ℂ BirkSpace BirkSpace :=
  lieSeriesV (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) (birkNz m hm ha hp)
    (fun n => if n = 0 then 0 else 1 / ((n : ℂ) + 1))

variable {m hm ha hp}

theorem birkYj_zero : birkYj m hm ha hp 0 = 0 := by
  unfold birkYj; simp

theorem birkYj_of_ne_zero {j : ℕ} (hj : j ≠ 0) : birkYj m hm ha hp j = birkVn m hm ha hp j := by
  unfold birkYj; simp [hj]

include hm hp in
theorem birkRho1_pos : 0 < birkRho1 m p := by
  have := birkCF_pos m hm hp
  unfold birkRho1; positivity

include hm hp in
theorem birkRho1_sq : birkRho1 m p ^ 2 = 1 / (160 * birkCF m p) := by
  have h := birkCF_pos m hm hp
  unfold birkRho1
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

include hm hp in
theorem birkRho1_q : 2 * birkCF m p * birkRho1 m p ^ 2 = 1 / 80 := by
  have h := birkCF_pos m hm hp
  rw [birkRho1_sq (hm := hm) (hp := hp)]
  field_simp
  ring

include hm hp in
/-- `B_{ρ₁} = {160 C_F ‖w‖² < 1}` is the open ball of radius `ρ₁`. -/
theorem birkBall1_eq_ball : birkBall1 m p = Metric.ball 0 (birkRho1 m p) := by
  have hC := birkCF_pos m hm hp
  have hρ := birkRho1_pos (hm := hm) (hp := hp)
  ext w
  rw [mem_ball_zero_iff]
  show 160 * birkCF m p * ‖w‖ ^ 2 < 1 ↔ _
  rw [← pow_lt_pow_iff_left₀ (norm_nonneg w) hρ.le (two_ne_zero), birkRho1_sq (hm := hm) (hp := hp),
    lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> linarith

include hm hp in
theorem norm_lt_birkRho1 {w : BirkSpace} (hw : w ∈ birkBall1 m p) : ‖w‖ < birkRho1 m p := by
  rw [birkBall1_eq_ball (hm := hm) (hp := hp), mem_ball_zero_iff] at hw; exact hw

section Coef

include hm hp in
theorem norm_birkYj_le (j : ℕ) :
    ‖birkYj m hm ha hp j‖ * birkRho1 m p ^ (2 * j + 3) ≤
      2 * waveCubicConst p * birkRho1 m p ^ 3 * (1 / 2) ^ j := by
  have hCp := birkCF_pos m hm hp
  have hρ := birkRho1_pos (hm := hm) (hp := hp)
  have hCs : 0 ≤ waveCubicConst p := by unfold waveCubicConst; positivity
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [birkYj_zero, norm_zero, zero_mul]; positivity
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [birkYj_of_ne_zero (by omega)]
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  have h := norm_lieV_le (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkNz m hm ha hp) hCp.le (norm_birkEmbed_le _ _ _ _) hSn (birkRho1 m p) hρ (k + 1)
  rw [birkRho1_q (hm := hm) (hp := hp)] at h
  have hN := norm_birkNz_le m hm ha hp
  have h8 : ((1 : ℝ) / 8) ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  calc ‖birkVn m hm ha hp (k + 1)‖ * birkRho1 m p ^ (2 * (k + 1) + 3)
      = (‖birkVn m hm ha hp (k + 1)‖ * birkRho1 m p ^ (2 * (k + 1))) * birkRho1 m p ^ 3 := by
        rw [pow_add]; ring
    _ ≤ (4 * ‖birkNz m hm ha hp‖ * (10 * (1 / 80)) ^ (k + 1)) * birkRho1 m p ^ 3 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ ≤ (4 * waveCubicConst p * (10 * (1 / 80)) ^ (k + 1)) * birkRho1 m p ^ 3 := by gcongr
    _ = waveCubicConst p * birkRho1 m p ^ 3 * (1 / 2) * ((1 : ℝ) / 8) ^ k := by
        rw [show (10 : ℝ) * (1 / 80) = 1 / 8 by norm_num, pow_succ]; ring
    _ ≤ waveCubicConst p * birkRho1 m p ^ 3 * (1 / 2) * (1 / 2) ^ k := by gcongr
    _ ≤ 2 * waveCubicConst p * birkRho1 m p ^ 3 * (1 / 2) ^ (k + 1) := by
        have h0 : 0 ≤ waveCubicConst p * birkRho1 m p ^ 3 * (1 / 2 : ℝ) ^ k := by positivity
        rw [pow_succ (1 / 2 : ℝ) k]; linarith

include hm hp in
/-- (`bpW:w3:Yseries`) `Σ_j ‖Y_j‖ ρ₁^{2j+3} < ∞`. -/
theorem summable_norm_birkYj :
    Summable fun j : ℕ => ‖birkYj m hm ha hp j‖ * birkRho1 m p ^ (2 * j + 3) :=
  Summable.of_nonneg_of_le (fun _ => by have := (birkRho1_pos (hm := hm) (hp := hp)).le; positivity)
    (norm_birkYj_le (hm := hm) (hp := hp)) (summable_geometric_two.mul_left _)

include hm hp in
/-- (`bpW:w3:Yseries`) `Σ_j ‖Y_j‖ ρ₁^{2j+3} ≤ 4 C_* ρ₁³`. -/
theorem tsum_norm_birkYj_le :
    ∑' j : ℕ, ‖birkYj m hm ha hp j‖ * birkRho1 m p ^ (2 * j + 3) ≤
      4 * waveCubicConst p * birkRho1 m p ^ 3 := by
  refine (Summable.tsum_le_tsum (norm_birkYj_le (hm := hm) (hp := hp))
    (summable_norm_birkYj (hm := hm) (hp := hp))
    (summable_geometric_two.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_two]; ring

end Coef

section Series

variable (t : Set.Icc (0 : ℝ) 1) (w : birkBall1 m p)

theorem abs_le_two_of_mem_Icc01 : |(t : ℝ)| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [t.2.1, t.2.2]

/-- `t^j Y_j(w,…,w) = t^j V_j(w,…,w) - [j = 0] V_0(w,…,w)`. -/
theorem birkYj_term_eq (s : ℝ) (y : BirkSpace) (j : ℕ) :
    (s ^ j) • birkYj m hm ha hp j (fun _ => y) =
      (s ^ j) • birkVn m hm ha hp j (fun _ => y) -
        (if j = 0 then birkVn m hm ha hp 0 (fun _ => y) else 0) := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [birkYj_zero]; simp
  · rw [birkYj_of_ne_zero hj]; simp only [hj, ↓reduceIte, sub_zero]

theorem norm_birkYj_apply_le (y : BirkSpace) (j : ℕ) :
    ‖birkYj m hm ha hp j (fun _ => y)‖ ≤ ‖birkVn m hm ha hp j (fun _ => y)‖ := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [birkYj_zero]; simp
  · rw [birkYj_of_ne_zero hj]

/-- (`bpW:w3:Yseries`) The series `Σ_j t^j Y_j(w,…,w)` converges absolutely. -/
theorem summable_norm_birkY_terms :
    Summable fun j : ℕ => ‖((t : ℝ) ^ j) • birkYj m hm ha hp j (fun _ => (w : BirkSpace))‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    (summable_birkVn (ha := ha) (hm := hm) (hp := hp) t (abs_le_two_of_mem_Icc01 t) w w.2)
  rw [norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_birkYj_apply_le _ j) (norm_nonneg _)

/-- (`bpW:w3:Yseries`) `Y(t,w) = Σ_j t^j Y_j(w,…,w)` for `0 ≤ t ≤ 1`, `w ∈ B_{ρ₁}`. -/
theorem birkY_hasSum :
    HasSum (fun j : ℕ => ((t : ℝ) ^ j) • birkYj m hm ha hp j (fun _ => (w : BirkSpace)))
      (birkY m hm ha hp t w) := by
  have hs := (summable_birkVn (ha := ha) (hm := hm) (hp := hp) t (abs_le_two_of_mem_Icc01 t) w
    w.2).of_norm.hasSum
  have h := hs.sub (hasSum_ite_eq 0 (birkVn m hm ha hp 0 (fun _ => (w : BirkSpace))))
  rw [birkY_eq_tsum]
  convert h using 1
  funext j
  exact birkYj_term_eq _ _ j

end Series

section Integral

variable (m hm ha hp) in
/-- (`bpW:w3:Yseries`) `∫₀¹ Y(t,w) dt` for `w ∈ B_{ρ₁}` (Bochner interval integral of the
integrand `t ↦ Y(t,w)` on `[0,1]`). -/
def birkYInt (w : birkBall1 m p) : BirkSpace :=
  ∫ t in (0 : ℝ)..1, Set.IccExtend zero_le_one (fun t => birkY m hm ha hp t w) t

/-- (`bpW:w3:Yseries`) `∫₀¹ Y(t,w) dt = Σ_j Y_j(w,…,w)/(j+1)` (termwise integration). -/
theorem birkYInt_hasSum (w : birkBall1 m p) :
    HasSum (fun j : ℕ => (1 / ((j : ℝ) + 1)) • birkYj m hm ha hp j (fun _ => (w : BirkSpace)))
      (birkYInt m hm ha hp w) := by
  set v : ℕ → BirkSpace := fun j => birkYj m hm ha hp j (fun _ => (w : BirkSpace)) with hv
  have hsv : Summable fun j => ‖v j‖ := by
    have := summable_norm_birkY_terms (hm := hm) (ha := ha) (hp := hp)
      ⟨1, by norm_num, le_rfl⟩ w
    simpa [one_pow, one_smul] using this
  have hI0 : Set.uIoc (0 : ℝ) 1 = Set.Ioc 0 1 := Set.uIoc_of_le zero_le_one
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := 1) (F := fun j t => (t ^ j) • v j)
    (f := Set.IccExtend zero_le_one (fun t => birkY m hm ha hp t w))
    (fun j _ => ‖v j‖)
    (fun j => ((continuous_pow j).smul continuous_const).aestronglyMeasurable)
    (fun j => ae_of_all _ fun t ht => by
      rw [hI0] at ht
      rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.1.le ht.2))
    (ae_of_all _ fun _ _ => hsv) intervalIntegrable_const
    (ae_of_all _ fun t ht => by
      rw [hI0] at ht
      rw [Set.IccExtend_of_mem _ _ ⟨ht.1.le, ht.2⟩]
      exact birkY_hasSum ⟨t, ht.1.le, ht.2⟩ w)
  convert h using 1
  · funext j
    rw [intervalIntegral.integral_smul_const, integral_pow]
    simp [hv]
  · rfl

/-- (`bpW:w3:Yseries`) `∫₀¹ Y(t,w) dt = Σ_j Y_j(w,…,w)/(j+1)`. -/
theorem birkYInt_eq_tsum (w : birkBall1 m p) :
    birkYInt m hm ha hp w =
      ∑' j : ℕ, (1 / ((j : ℝ) + 1)) • birkYj m hm ha hp j (fun _ => (w : BirkSpace)) :=
  (birkYInt_hasSum w).tsum_eq.symm

/-- The coefficientwise identity `c_j V_j = Y_j/(j+1)` (`c_0 = 0`, `c_j = 1/(j+1)`). -/
theorem birkYSeries_coef_eq (y : BirkSpace) (j : ℕ) :
    (if j = 0 then (0 : ℂ) else 1 / ((j : ℂ) + 1)) • birkVn m hm ha hp j (fun _ => y) =
      (1 / ((j : ℝ) + 1)) • birkYj m hm ha hp j (fun _ => y) := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [birkYj_zero]; simp
  · simp only [hj, ↓reduceIte]
    rw [birkYj_of_ne_zero hj,
      show ((1 : ℂ) / ((j : ℂ) + 1)) = (((1 / ((j : ℝ) + 1)) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.coe_smul _ _

end Integral

section PowerSeries

/-- (`bpW:w3:Yseries`) `q_{2j+3} = Y_j/(j+1)`. -/
theorem birkYSeries_odd (j : ℕ) :
    birkYSeries m hm ha hp (2 * j + 3) = (1 / ((j : ℂ) + 1)) • birkYj m hm ha hp j := by
  set c : ℕ → ℂ := fun n => if n = 0 then 0 else 1 / ((n : ℂ) + 1) with hc
  have key : ∀ k (hk : k = j) (h : 2 * k + 3 = 2 * j + 3),
      ContinuousMultilinearMap.domDomCongr (finCongr h) (c k • birkVn m hm ha hp k) =
        c j • birkVn m hm ha hp j := by
    rintro k rfl h
    ext v
    simp
  unfold birkYSeries lieSeriesV
  split_ifs with h
  · refine (key _ (by omega) _).trans ?_
    rcases eq_or_ne j 0 with rfl | hj
    · rw [birkYj_zero]
      ext v
      simp [hc]
    · rw [birkYj_of_ne_zero hj]; simp [hc, hj]
  · exact absurd ⟨by omega, by omega⟩ h

/-- (`bpW:w3:Yseries`) `q_n = 0` unless `n = 2j + 3`. -/
theorem birkYSeries_eq_zero (n : ℕ) (hn : ∀ j : ℕ, n ≠ 2 * j + 3) :
    birkYSeries m hm ha hp n = 0 := by
  unfold birkYSeries lieSeriesV
  split_ifs with h
  · exact absurd (by omega) (hn ((n - 3) / 2))
  · rfl

include hm hp in
/-- (`bpW:w3:Yseries`) `w ↦ ∫₀¹ Y(t,w) dt` has on `B_{ρ₁}` the formal power series `q`: every map
`f` agreeing with it on `B_{ρ₁}` satisfies `HasFPowerSeriesOnBall f q 0 ρ₁`. -/
theorem hasFPowerSeriesOnBall_birkYInt (f : BirkSpace → BirkSpace)
    (hf : ∀ w : birkBall1 m p, f w = birkYInt m hm ha hp w) :
    HasFPowerSeriesOnBall f (birkYSeries m hm ha hp) 0 (ENNReal.ofReal (birkRho1 m p)) := by
  have hCp := birkCF_pos m hm hp
  have hρ := birkRho1_pos (hm := hm) (hp := hp)
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  have hc : ∀ n : ℕ, ‖(if n = 0 then (0 : ℂ) else 1 / ((n : ℂ) + 1))‖ ≤ 1 := fun n => by
    split_ifs
    · simp
    · rw [norm_div, norm_one]
      have h1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
        have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]
      exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  have h := hasFPowerSeriesOnBall_lieV (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkNz m hm ha hp) hCp.le (norm_birkEmbed_le _ _ _ _) hSn _ hc (birkRho1 m p) hρ
    (birkRho1_q (hm := hm) (hp := hp)).le
  refine h.congr fun y hy => ?_
  have hy' : y ∈ birkBall1 m p := by
    rw [birkBall1_eq_ball (hm := hm) (hp := hp), mem_ball_zero_iff]
    rw [Metric.mem_eball, edist_zero_right] at hy
    have h2 : ENNReal.ofReal ‖y‖ < ENNReal.ofReal (birkRho1 m p) := by rwa [ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).1 h2
  rw [hf ⟨y, hy'⟩, birkYInt_eq_tsum]
  exact tsum_congr fun j => birkYSeries_coef_eq y j

include hm hp in
/-- (`bpW:w3:Yseries`) `w ↦ ∫₀¹ Y(t,w) dt` is analytic on `B_{ρ₁}`: every map agreeing with it on
`B_{ρ₁}` is `AnalyticOnNhd ℂ` there. -/
theorem analyticOnNhd_birkYInt (f : BirkSpace → BirkSpace)
    (hf : ∀ w : birkBall1 m p, f w = birkYInt m hm ha hp w) :
    AnalyticOnNhd ℂ f (birkBall1 m p) := by
  intro y hy
  refine (hasFPowerSeriesOnBall_birkYInt (hm := hm) (hp := hp) f hf).analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff (birkRho1_pos (hm := hm) (hp := hp))).2
    (norm_lt_birkRho1 (hm := hm) (hp := hp) hy)

end PowerSeries

section XK2

/-- `X_{K₂}(w) = Σ_j Y_j(w,…,w)/(j+1)` on `B_{ρ₁}`. -/
theorem birkXK2Ext_hasSum (w : birkBall1 m p) :
    HasSum (fun j : ℕ => (1 / ((j : ℝ) + 1)) • birkYj m hm ha hp j (fun _ => (w : BirkSpace)))
      (birkXK2Ext m hm ha hp w) := by
  have hs1 := summable_birkVn (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w w.2
  have hs : Summable fun n : ℕ =>
      ‖((1 : ℂ) / ((n : ℂ) + 1)) • birkVn m hm ha hp n (fun _ => (w : BirkSpace))‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs1
    rw [norm_smul, norm_smul, one_pow, norm_one, one_mul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [norm_div, norm_one]
    have h1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  have h := hs.of_norm.hasSum.sub (hasSum_ite_eq 0 (birkVn m hm ha hp 0
    (fun _ => (w : BirkSpace))))
  unfold birkXK2Ext
  convert h using 1
  funext j
  rw [← birkYSeries_coef_eq]
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · simp [hj]

/-- (`bpW:w3:Yseries`, `bpW:w3:main` Step XK2) `∫₀¹ Y(t,w) dt = X_{K₂}(w)` on `B_{ρ₁}`. -/
theorem birkYInt_eq_birkXK2Ext (w : birkBall1 m p) :
    birkYInt m hm ha hp w = birkXK2Ext m hm ha hp w :=
  (birkYInt_hasSum w).unique (birkXK2Ext_hasSum w)

include hm hp in
/-- (`bpW:w3:main` (i)) `K₂` is real on `B_{ρ₁}`. -/
theorem birkK2Ext_rho (w : BirkSpace) (hw : w ∈ birkBall1 m p) :
    birkK2Ext m hm ha hp (birkRho w) = starRingEnd ℂ (birkK2Ext m hm ha hp w) := by
  have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    have hw' : 160 * birkCF m p * ‖w‖ ^ 2 < 1 := hw
    rw [abs_one]
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hΓ : birkGamma m hm ha hp 1 (birkRho w) = birkRho (birkGamma m hm ha hp 1 w) :=
    birkGamma_rho (ha := ha) (hm := hm) (hp := hp) 1 w hq
  unfold birkK2Ext
  rw [hΓ, birkLambda_rho m hm ha hp, birkLambda_rho m hm ha hp]
  have e := birkQuartP_rho m hm ha hp (birkCoefZ_isCoef m hm)
  unfold birkHamZ
  rw [e]
  simp only [map_sub]

include hm hp in
/-- `K₂ ∈ 𝒜(B_{ρ₁})` with field `X_{K₂}`. -/
theorem birkK2Ext_isClassA :
    IsBirkClassA a p ha (by linarith) (birkBall1 m p) (birkK2Ext m hm ha hp)
      (birkXK2Ext m hm ha hp) where
  isOpen := isOpen_birkBall1 m p
  rho_mem _ hw := birkRho_mem_birkBall1 m hw
  real w hw := birkK2Ext_rho (hm := hm) (hp := hp) w hw
  analytic w hw := by
    have hw40 := birkBall1_subset_birkBall0 m hm hp hw
    have hΓa : AnalyticAt ℂ (birkGamma m hm ha hp 1) w :=
      birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw40
    have hΛa : ∀ y, AnalyticAt ℂ (birkLambda m hm ha hp) y := fun y =>
      (birkLambda_analyticOnNhd (m := m) (hm := hm) (ha := ha) (hp := hp)) y (Set.mem_univ _)
    have hZa : ∀ y, AnalyticAt ℂ (birkHamZ m hm ha hp) y := fun y =>
      (birkHamZ_isClassA m hm ha hp).analytic y (Set.mem_univ _)
    unfold birkK2Ext
    exact (((hΛa _).comp hΓa).sub (hΛa w)).sub (hZa w)
  field w hw v := birkK2Ext_field (ha := ha) (hm := hm) (hp := hp) w hw v
  analytic_field w hw := birkXK2Ext_analyticAt (ha := ha) (hm := hm) (hp := hp) w hw

include hm hp in
/-- (`bpW:w3:Yseries`) Reality: `∫₀¹ Y(t,ϱw) dt = ϱ ∫₀¹ Y(t,w) dt`. -/
theorem birkYInt_rho (w : birkBall1 m p) :
    birkYInt m hm ha hp ⟨birkRho w, birkRho_mem_birkBall1 m w.2⟩ =
      birkRho (birkYInt m hm ha hp w) := by
  rw [birkYInt_eq_birkXK2Ext, birkYInt_eq_birkXK2Ext]
  exact (birkK2Ext_isClassA (hm := hm) (hp := hp)).field_rho w.2

end XK2

end KAM.Wave

end
