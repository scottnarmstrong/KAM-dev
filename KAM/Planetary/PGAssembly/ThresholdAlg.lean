/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Parameters

/-!
# P Part 5: parameter algebra for the thresholds (`bpP:p5:param-facts`, `bpP:p5:rK`)

Pointwise inequalities for `params d r mu` on the range `r ≤ e⁻¹`, `0 < mu < r^6/(log 1/r)^c`,
`LP ≤ log 1/r`, `r^2 (log 1/r)^(τ+1) ≤ 1`: the bound `gammaBar ≤ Cγ √r`, the displacement ratio
`LP mu Kbar^τ/gammaBar ≤ √r r^5/(G κ^{1/2})`, and the numerical consequences of `PGScaleSpec`
(`ĉ Ê < 1`, `rK < ρ̂/(256 n)`). Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-TH.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {a b : ℕ}

theorem pgWidth_lt_one (d : PGData a b) : pgWidth d < 1 := by
  unfold pgWidth; linarith [(pgExtension d).delta_lt]

theorem one_le_pgKappa (d : PGData a b) : 1 ≤ 30 / pgWidth d := by
  rw [le_div_iff₀ (pgWidth_pos d)]; linarith [pgWidth_lt_one d]

theorem one_le_log_inv {r : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1)) :
    1 ≤ Real.log (1/r) := by
  rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hr0]
  have := mul_le_mul_of_nonneg_left hr (Real.exp_pos 1).le
  rw [← Real.exp_add] at this
  simpa using this

theorem LP_mul_mu_le {LP mu r τ : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1)) (hmu0 : 0 < mu)
    (hLP : LP ≤ Real.log (1/r)) (hmu : mu < r^6/(Real.log (1/r))^(2*τ+2)) :
    LP*mu ≤ r^6 * (Real.log (1/r))^(-(2*τ+1)) := by
  have hL : 1 ≤ Real.log (1/r) := one_le_log_inv hr0 hr
  set L := Real.log (1/r)
  have hL0 : 0 < L := by linarith
  have hX : 0 < L^(2*τ+1) := Real.rpow_pos_of_pos hL0 _
  have h1 : mu * L^(2*τ+2) < r^6 := by
    rwa [lt_div_iff₀ (Real.rpow_pos_of_pos hL0 _)] at hmu
  have h2 : L^(2*τ+2) = L * L^(2*τ+1) := by
    rw [show 2*τ+2 = 1 + (2*τ+1) by ring, Real.rpow_add hL0, Real.rpow_one]
  rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ hX]
  calc LP*mu*L^(2*τ+1) ≤ L*mu*L^(2*τ+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLP hmu0.le) hX.le
    _ = mu * L^(2*τ+2) := by rw [h2]; ring
    _ ≤ r^6 := h1.le

theorem sqrt_LP_mu_le {LP mu r τ : ℝ} (hr0 : 0 < r) (hr : r ≤ Real.exp (-1))
    (h : LP*mu ≤ r^6 * (Real.log (1/r))^(-(2*τ+1))) :
    Real.sqrt (LP*mu) ≤ r^3 * (Real.log (1/r))^(-(τ+1/2)) := by
  have hL0 : 0 < Real.log (1/r) := by linarith [one_le_log_inv hr0 hr]
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e : (Real.log (1/r) ^ (-(τ+1/2)))^2 = Real.log (1/r) ^ (-(2*τ+1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1; push_cast; ring
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, e, ← pow_mul]

theorem B1_le {κ L r τ s : ℝ} (hκ : 1 ≤ κ) (hL : 1 ≤ L) (hr0 : 0 < r)
    (hs : s ≤ r^3 * L^(-(τ+1/2))) :
    s * (κ*L)^(τ+1/2) * r^(-5/2:ℝ) ≤ κ^(τ+1) * r^(1/2:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hκ0 : 0 < κ := by linarith
  have e1 : L^(-(τ+1/2)) * L^(τ+1/2) = 1 := by
    rw [← Real.rpow_add hL0]; simp
  have e2 : r^3 * r^(-5/2:ℝ) = r^(1/2:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0]; norm_num
  have h3 : κ^(τ+1/2) ≤ κ^(τ+1) := Real.rpow_le_rpow_of_exponent_le hκ (by linarith)
  have hp : 0 ≤ (κ*L)^(τ+1/2) * r^(-5/2:ℝ) := by positivity
  calc s * (κ*L)^(τ+1/2) * r^(-5/2:ℝ) = s * ((κ*L)^(τ+1/2) * r^(-5/2:ℝ)) := by ring
    _ ≤ (r^3 * L^(-(τ+1/2))) * ((κ*L)^(τ+1/2) * r^(-5/2:ℝ)) := mul_le_mul_of_nonneg_right hs hp
    _ = κ^(τ+1/2) * (L^(-(τ+1/2)) * L^(τ+1/2)) * (r^3 * r^(-5/2:ℝ)) := by
        rw [Real.mul_rpow hκ0.le hL0.le]; ring
    _ = κ^(τ+1/2) * r^(1/2:ℝ) := by rw [e1, e2]; ring
    _ ≤ _ := by gcongr

theorem B2_le {κ L r τ : ℝ} (hκ : 1 ≤ κ) (hL : 1 ≤ L) (hr0 : 0 < r)
    (h8 : r^2 * L^(τ+1) ≤ 1) :
    r^(5/2:ℝ) * (κ*L)^(τ+1) ≤ κ^(τ+1) * r^(1/2:ℝ) := by
  have hL0 : 0 < L := by linarith
  have hκ0 : 0 < κ := by linarith
  have e : r^(5/2:ℝ) = r^(1/2:ℝ) * r^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0]; norm_num
  rw [e, Real.mul_rpow hκ0.le hL0.le]
  have h1 : 0 ≤ κ^(τ+1) * r^(1/2:ℝ) := by positivity
  calc r^(1/2:ℝ) * r^2 * (κ^(τ+1) * L^(τ+1))
      = (κ^(τ+1) * r^(1/2:ℝ)) * (r^2 * L^(τ+1)) := by ring
    _ ≤ (κ^(τ+1) * r^(1/2:ℝ)) * 1 := mul_le_mul_of_nonneg_left h8 h1
    _ = _ := mul_one _

theorem ratio_le {LPmu κ L r τ G g s : ℝ} (hP : 0 < LPmu) (hG : 0 < G) (hκ : 1 ≤ κ) (hL : 1 ≤ L)
    (hr0 : 0 < r) (hs : s = Real.sqrt LPmu) (hsr : s ≤ r^3)
    (hg : G * (s * (κ*L)^(τ+1/2) * r^(-5/2:ℝ)) ≤ g) :
    LPmu * (κ*L)^τ / g ≤ r^3 * r^(5/2:ℝ) / (G * κ^(1/2:ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hκ0 : 0 < κ := by linarith
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.2 hP
  have hss : LPmu = s * s := by rw [hs, Real.mul_self_sqrt hP.le]
  have hK0 : 0 < κ*L := by positivity
  have hq : (κ*L)^(τ+1/2) = (κ*L)^τ * (κ*L)^(1/2:ℝ) := Real.rpow_add hK0 _ _
  have hr52 : r^(-5/2:ℝ) = (r^(5/2:ℝ))⁻¹ := by
    rw [show (-5/2:ℝ) = -(5/2) by ring, Real.rpow_neg hr0.le]
  have h52 : 0 < r^(5/2:ℝ) := Real.rpow_pos_of_pos hr0 _
  have hKτ : 0 < (κ*L)^τ := Real.rpow_pos_of_pos hK0 _
  have hK12 : 0 < (κ*L)^(1/2:ℝ) := Real.rpow_pos_of_pos hK0 _
  have hg1 : 0 < G * (s * (κ*L)^(τ+1/2) * r^(-5/2:ℝ)) := by
    rw [hq, hr52]; positivity
  calc LPmu * (κ*L)^τ / g ≤ LPmu * (κ*L)^τ / (G * (s * (κ*L)^(τ+1/2) * r^(-5/2:ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) hg1 hg
    _ = s * r^(5/2:ℝ) / (G * (κ*L)^(1/2:ℝ)) := by
        rw [hss, hq, hr52]; field_simp
    _ ≤ r^3 * r^(5/2:ℝ) / (G * κ^(1/2:ℝ)) := by
        have hk : κ^(1/2:ℝ) ≤ (κ*L)^(1/2:ℝ) :=
          Real.rpow_le_rpow hκ0.le (by nlinarith) (by norm_num)
        have hk0 : 0 < κ^(1/2:ℝ) := Real.rpow_pos_of_pos hκ0 _
        gcongr

/-- The data-only threshold constant `C_γ = G (30/s_*)^(τ+1)`. -/
def pgCgamma (d : PGData a b) : ℝ :=
  (pgScales d).G*(30/pgWidth d)^(pgTau a b+1)

/-- The range of `(r, mu)` on which the parameter estimates of `bpP:p5:param-facts` hold. -/
def ThrRange (d : PGData a b) (r mu : ℝ) : Prop :=
  0 < r ∧ r ≤ Real.exp (-1) ∧ 0 < mu ∧ (pgAnalytic d).LP ≤ Real.log (1/r) ∧
    mu < r^6/(Real.log (1/r))^(2*pgTau a b+2) ∧ r^2*(Real.log (1/r))^(pgTau a b+1) ≤ 1

theorem pgScales_G_pos (d : PGData a b) : 0 < (pgScales d).G := by
  obtain ⟨-, hk1, -, -, hG⟩ := pgScales_spec d
  obtain ⟨-, -, -, hM0, -⟩ := pgAnalytic_spec d
  have := (le_max_left _ _).trans hG
  nlinarith

theorem pgCgamma_pos (d : PGData a b) : 0 < pgCgamma d := by
  unfold pgCgamma
  have := pgWidth_pos d
  have := pgScales_G_pos d
  positivity

theorem params_gammaBar (d : PGData a b) (r mu : ℝ) : (params d r mu).gammaBar =
    (pgScales d).G * max (Real.sqrt ((pgAnalytic d).LP*mu) *
      (30/pgWidth d*Real.log (1/r))^(pgTau a b+1/2) * r^(-5/2:ℝ))
      (r^(5/2:ℝ) * (30/pgWidth d*Real.log (1/r))^(pgTau a b+1)) := rfl

theorem gammaBar_le {d : PGData a b} {r mu : ℝ} (h : ThrRange d r mu) :
    (params d r mu).gammaBar ≤ pgCgamma d * Real.sqrt r := by
  obtain ⟨hr0, hr, hmu0, hLP, hmu, h8⟩ := h
  have hL := one_le_log_inv hr0 hr
  have hκ := one_le_pgKappa d
  have hG := pgScales_G_pos d
  have hP := LP_mul_mu_le hr0 hr hmu0 hLP hmu
  have hs := sqrt_LP_mu_le hr0 hr hP
  have b1 := B1_le hκ hL hr0 hs
  have b2 := B2_le (τ := pgTau a b) hκ hL hr0 h8
  rw [params_gammaBar, pgCgamma, Real.sqrt_eq_rpow r]
  exact (mul_le_mul_of_nonneg_left (max_le b1 b2) hG.le).trans (le_of_eq (mul_assoc _ _ _).symm)

theorem gammaBar_ratio {d : PGData a b} {r mu : ℝ} (h : ThrRange d r mu) :
    (pgAnalytic d).LP*mu*(params d r mu).Kbar^(pgTau a b) / (params d r mu).gammaBar ≤
      Real.sqrt r * r^5 / ((pgScales d).G * (30/pgWidth d)^(1/2:ℝ)) := by
  obtain ⟨hr0, hr, hmu0, hLP, hmu, h8⟩ := h
  have hL := one_le_log_inv hr0 hr
  have hκ := one_le_pgKappa d
  have hG := pgScales_G_pos d
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hLP1, -⟩ := pgAnalytic_spec d
  have hP := LP_mul_mu_le hr0 hr hmu0 hLP hmu
  have hs := sqrt_LP_mu_le hr0 hr hP
  have hs3 : Real.sqrt ((pgAnalytic d).LP*mu) ≤ r^3 :=
    hs.trans (mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith [pgTau_pos a b])))
  have key := ratio_le (LPmu := (pgAnalytic d).LP*mu) (κ := 30/pgWidth d)
    (L := Real.log (1/r)) (τ := pgTau a b) (G := (pgScales d).G)
    (g := (params d r mu).gammaBar) (by positivity) hG hκ hL hr0 rfl hs3
    (by rw [params_gammaBar]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hG.le)
  refine key.trans (le_of_eq ?_)
  rw [Real.sqrt_eq_rpow r]
  congr 1
  rw [← Real.rpow_natCast r 3, ← Real.rpow_natCast r 5, ← Real.rpow_add hr0, ← Real.rpow_add hr0]
  norm_num

end KAM.Planetary

end
