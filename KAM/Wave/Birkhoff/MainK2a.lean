/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainK1
public import KAM.Wave.Birkhoff.YSeries4

/-!
# The field of `K₂`: the series (blueprint-W `bpW:w3:main`, Step XK2; `bpW:w3:Yseries`)

Package W3-MAIN, blueprint labels `bpW:w3:main`, `bpW:w3:Yseries`.

`birkNz`: the cubic `X_{Z'} = 4∇𝔷 : 𝔚³ → 𝔚⁺`; `birkV n = V_n` the coefficients of `YSeries`
for `ι = birkEmbed`, `S = birkS`, `N = birkNz`; `birkXK2Ext = Σ_{n ≥ 1} V_n(w,…,w)/(n+1)`
(the series for `∫₀¹ Y dt`), analytic on `B_{ρ₁}` (`birkXK2Ext_analyticAt`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- `X_{Z'} = 4 ∇𝔷` as a trilinear map `𝔚³ → 𝔚⁺`. -/
def birkNz : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => BirkSpace) BirkSpace :=
  ((3 + 1 : ℕ) : ℂ) • birkGradML m hm ha hp (birkCoefZ_isCoef m hm).bound

include ha hp in
theorem birkNz_const (w : BirkSpace) :
    birkNz m hm ha hp (fun _ => w) = birkHamZX m hm ha hp w := by
  unfold birkNz birkHamZX birkQuartX birkDiagField
  rfl

include ha hp in
theorem norm_birkNz_le : ‖birkNz m hm ha hp‖ ≤ waveCubicConst p := by
  unfold birkNz
  rw [norm_smul]
  have h := norm_birkGradML_le m hm ha hp (birkCoefZ_isCoef m hm).bound
  have : ‖(((3 + 1 : ℕ) : ℂ))‖ = 4 := by norm_num
  rw [this]
  linarith

/-- The coefficients `V_n`. -/
abbrev birkVn (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (2 * n + 3) => BirkSpace) BirkSpace :=
  lieV (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp) (birkNz m hm ha hp) n

/-- Internal totalized helper (a bare `tsum`, convergent on `B_{ρ₁}`; public object `birkXK2`):
`X_{K₂}(w) = Σ_{n ≥ 1} V_n(w,…,w)/(n+1)`. -/
def birkXK2Ext (w : BirkSpace) : BirkSpace :=
  ∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)) • birkVn m hm ha hp n (fun _ => w) -
    birkVn m hm ha hp 0 (fun _ => w)

variable {m hm ha hp}

include hm hp in
/-- For `‖w‖ < ρ₁` there is `ρ` with `‖w‖ < ρ` and `2 C_F ρ² ≤ 1/80`. -/
theorem exists_rho1 (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ‖w‖ < ρ ∧ 2 * birkCF m p * ρ ^ 2 ≤ 1 / 80 := by
  have hCp := birkCF_pos m hm hp
  have h160 : 0 < 160 * birkCF m p := by positivity
  have hw' : ‖w‖ ^ 2 < 1 / (160 * birkCF m p) := by rw [lt_div_iff₀ h160]; linarith
  set r2 : ℝ := (‖w‖ ^ 2 + 1 / (160 * birkCF m p)) / 2 with hr2
  have hr2a : ‖w‖ ^ 2 < r2 := by rw [hr2]; linarith
  have hr2b : r2 < 1 / (160 * birkCF m p) := by rw [hr2]; linarith
  have hr2p : 0 < r2 := lt_of_le_of_lt (sq_nonneg _) hr2a
  refine ⟨Real.sqrt r2, Real.sqrt_pos.2 hr2p, Real.lt_sqrt (norm_nonneg w) |>.2 hr2a, ?_⟩
  rw [Real.sq_sqrt hr2p.le]
  have h1 : r2 * (160 * birkCF m p) < 1 := by rwa [lt_div_iff₀ h160] at hr2b
  nlinarith [mul_pos hCp hr2p]

include hm hp in
theorem birkXK2Ext_analyticAt (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    AnalyticAt ℂ (birkXK2Ext m hm ha hp) w := by
  have hCp := birkCF_pos m hm hp
  have hSn : ‖birkS m hm ha hp‖ ≤ birkCF m p :=
    ContinuousMultilinearMap.opNorm_le_bound hCp.le (norm_birkS_le m hm ha hp)
  obtain ⟨ρ, hρ, hwρ, hq⟩ := exists_rho1 (hm := hm) (hp := hp) w hw
  have hc : ∀ n : ℕ, ‖((1 : ℂ) / ((n : ℂ) + 1))‖ ≤ 1 := fun n => by
    rw [norm_div, norm_one]
    have : (1 : ℝ) ≤ ‖(n : ℂ) + 1‖ := by
      have h1 : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
        have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact div_le_one_of_le₀ this (by positivity)
  have h1 := analyticAt_lieV (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkNz m hm ha hp) hCp.le (norm_birkEmbed_le _ _ _ _) hSn
    (fun n => (1 : ℂ) / ((n : ℂ) + 1)) hc ρ hρ hq w hwρ
  have h2 := analyticAt_lieV (birkEmbed a (p + 1) p (by linarith)) (birkS m hm ha hp)
    (birkNz m hm ha hp) hCp.le (norm_birkEmbed_le _ _ _ _) hSn
    (fun n => if n = 0 then 1 else 0) (fun n => by split_ifs <;> simp) ρ hρ hq w hwρ
  have e : (fun y : BirkSpace => ∑' n : ℕ, (if n = 0 then (1 : ℂ) else 0) •
      birkVn m hm ha hp n (fun _ => y)) = fun y => birkVn m hm ha hp 0 (fun _ => y) := by
    funext y
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  rw [e] at h2
  unfold birkXK2Ext
  exact h1.sub h2

end KAM.Wave

end
