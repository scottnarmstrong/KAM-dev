/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainReal

/-!
# The real change of coordinates `Γ^ℝ` (blueprint-W `bpW:w3:gamma-real`)

Package W3-MAIN, blueprint label `bpW:w3:gamma-real`.

`birkGammaRExt x = Π Γ(𝒵 x)` on `{x ∈ E | 320 C_F ‖x‖² < 1}` (the ball `‖x‖ < r₁ = ρ₁/√2`):
real analytic (`birkGammaRExt_analyticOnNhd`), `‖Γ^ℝ x‖ ≤ (10/9)√2‖x‖` and
`𝒵 Γ^ℝ x = 𝒵 x + ι 𝒵 ψ` with `‖ψ‖_{E_{a,p+1}} ≤ 6√2 C_F ‖x‖³` (`birkGammaRExt_sub`), injective
(`birkGammaRExt_injOn`) with the inverse `Π Γ_{-1} 𝒵`, `Γ^ℝ(B_{r₁}) ⊃ B_{r₁/2}`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

/-- Internal totalized helper (meaningful on `{320 C_F ‖x‖² < 1}`; public object `birkGammaR`
on that ball, `MainBallReal`): `Γ^ℝ = Π ∘ Γ ∘ 𝒵`. -/
def birkGammaRExt (x : BirkReal) : BirkReal := birkPi (birkGamma m hm ha hp 1 (birkZR x))

variable {m hm ha hp}

theorem norm_birkZR_sq_le (x : BirkReal) : ‖birkZR x‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
  have h := norm_birkZR_le x
  calc ‖birkZR x‖ ^ 2 ≤ (Real.sqrt 2 * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = 2 * ‖x‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]

include hm hp in
theorem birkZR_dom (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) :
    160 * birkCF m p * ‖birkZR x‖ ^ 2 < 1 := by
  have hCp := birkCF_pos m hm hp
  have := norm_birkZR_sq_le x
  nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 160 * birkCF m p)]

include hm hp in
/-- (`bpW:w3:gamma-real` (i)) `Γ^ℝ` is real analytic. -/
theorem birkGammaRExt_analyticOnNhd :
    AnalyticOnNhd ℝ (birkGammaRExt m hm ha hp) {x : BirkReal | 320 * birkCF m p * ‖x‖ ^ 2 < 1} := by
  have h := (real_restrict (U := {w : BirkSpace | 160 * birkCF m p * ‖w‖ ^ 2 < 1})
    (f := birkGamma m hm ha hp 1)
    (fun w hw => birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w (by
      have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
      show 40 * birkCF m p * ‖w‖ ^ 2 < 1
      have hw' : 160 * birkCF m p * ‖w‖ ^ 2 < 1 := hw
      nlinarith))
    (fun w hw => by
      have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
        rw [abs_one]
        have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
        have hw' : 160 * birkCF m p * ‖w‖ ^ 2 < 1 := hw
        nlinarith
      exact birkGamma_rho (ha := ha) (hm := hm) (hp := hp) 1 w hq)).1
  intro x hx
  exact h x (birkZR_dom (hm := hm) (hp := hp) x hx)

include hm hp in
theorem birkGamma_one_fixed (w : BirkSpace) (hw : birkRho w = w)
    (hw160 : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    birkRho (birkGamma m hm ha hp 1 w) = birkGamma m hm ha hp 1 w := by
  have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_one]
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have := birkGamma_rho (ha := ha) (hm := hm) (hp := hp) 1 w hq
  rw [hw] at this
  exact this.symm

include hm hp in
/-- (`bpW:w3:gamma-real` (ii)) The estimates for `Γ^ℝ`. -/
theorem birkGammaRExt_sub (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) :
    ∃ ψR : BirkReal, birkZR (birkGammaRExt m hm ha hp x) =
        birkZR x + birkEmbed a (p + 1) p (by linarith) (birkZR ψR) ∧
      ‖ψR‖ ≤ 6 * Real.sqrt 2 * birkCF m p * ‖x‖ ^ 3 ∧
      ‖birkGammaRExt m hm ha hp x‖ ≤ 10 / 9 * Real.sqrt 2 * ‖x‖ := by
  have hCp := birkCF_pos m hm hp
  set w := birkZR x with hw
  have hw160 := birkZR_dom (hm := hm) (hp := hp) x hx
  have hwρ : birkRho w = w := birkRho_birkZR x
  have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_one]
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg hCp.le (sq_nonneg _)
    nlinarith
  obtain ⟨ψ, hψ, hψn⟩ := birkGamma_sub_plus (ha := ha) (hm := hm) (hp := hp) 1 w hq
  have hΓρ := birkGamma_one_fixed (ha := ha) (hm := hm) (hp := hp) w hwρ hw160
  have hψρ : birkRho ψ = ψ := by
    refine birkEmbed_injective a (p + 1) p (by linarith) ?_
    rw [← birkRho_birkEmbed, hψ, map_sub, hΓρ, hwρ]
  have hZψ : birkZR (birkPi ψ) = ψ := birkZR_birkPi ψ hψρ
  have hZΓ : birkZR (birkGammaRExt m hm ha hp x) = birkGamma m hm ha hp 1 w :=
    birkZR_birkPi _ hΓρ
  refine ⟨birkPi ψ, ?_, ?_, ?_⟩
  · rw [hZΓ, hZψ, hψ]; abel
  · refine (norm_birkPi_le ψ).trans ?_
    rw [abs_one] at hψn
    refine hψn.trans ?_
    have h1 := norm_birkZR_le x
    have h2 : ‖w‖ ^ 3 ≤ (Real.sqrt 2 * ‖x‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) h1 3
    have h3 : (Real.sqrt 2 * ‖x‖) ^ 3 = 2 * Real.sqrt 2 * ‖x‖ ^ 3 := by
      rw [mul_pow, show Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 by
        rw [pow_succ, Real.sq_sqrt (by norm_num)]]
    calc 3 * 1 * birkCF m p * ‖w‖ ^ 3 ≤ 3 * 1 * birkCF m p * (2 * Real.sqrt 2 * ‖x‖ ^ 3) := by
          rw [← h3]; gcongr
      _ = 6 * Real.sqrt 2 * birkCF m p * ‖x‖ ^ 3 := by ring
  · refine (norm_birkPi_le _).trans ?_
    have h1 := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) 1 w hq
    have h2 := norm_birkZR_le x
    calc _ ≤ 10 / 9 * ‖w‖ := h1
      _ ≤ 10 / 9 * (Real.sqrt 2 * ‖x‖) := by gcongr
      _ = 10 / 9 * Real.sqrt 2 * ‖x‖ := by ring

include hm hp in
/-- (`bpW:w3:gamma-real` (iii)) The inverse of `Γ^ℝ` is `Π Γ_{-1} 𝒵`. -/
theorem birkGammaRExt_inv (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) :
    birkPi (birkGamma m hm ha hp (-1) (birkZR (birkGammaRExt m hm ha hp x))) = x := by
  have hw160 := birkZR_dom (hm := hm) (hp := hp) x hx
  have hZΓ : birkZR (birkGammaRExt m hm ha hp x) = birkGamma m hm ha hp 1 (birkZR x) :=
    birkZR_birkPi _ (birkGamma_one_fixed (ha := ha) (hm := hm) (hp := hp) _
      (birkRho_birkZR x) hw160)
  rw [hZΓ, birkGamma_neg_birkGamma (ha := ha) (hm := hm) (hp := hp) 1 (birkZR x) (by norm_num)
    hw160, birkPi_birkZR]

include hm hp in
/-- (`bpW:w3:gamma-real` (iii)) `Γ^ℝ` is injective. -/
theorem birkGammaRExt_injOn :
    Set.InjOn (birkGammaRExt m hm ha hp) {x : BirkReal | 320 * birkCF m p * ‖x‖ ^ 2 < 1} := by
  intro x hx x' hx' h
  rw [← birkGammaRExt_inv (ha := ha) (hm := hm) (hp := hp) x hx,
    ← birkGammaRExt_inv (ha := ha) (hm := hm) (hp := hp) x' hx', h]

include hm hp in
/-- (`bpW:w3:gamma-real` (iii)) `Γ^ℝ(B_{r₁}) ⊃ B_{r₁/2}`. -/
theorem birkGammaRExt_surj (y : BirkReal) (hy : 1280 * birkCF m p * ‖y‖ ^ 2 < 1) :
    ∃ x : BirkReal, 320 * birkCF m p * ‖x‖ ^ 2 < 1 ∧ birkGammaRExt m hm ha hp x = y := by
  have hCp := birkCF_pos m hm hp
  have hZ2 := norm_birkZR_sq_le y
  have hv := mul_le_mul_of_nonneg_left hZ2 (by positivity : (0 : ℝ) ≤ 160 * birkCF m p)
  have hv160 : 160 * birkCF m p * ‖birkZR y‖ ^ 2 < 1 := by nlinarith
  have hq : 2 * |(-1 : ℝ)| * birkCF m p * ‖birkZR y‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_neg, abs_one]; nlinarith
  set v := birkZR y with hvdef
  set w := birkGamma m hm ha hp (-1) v with hwdef
  have hvρ : birkRho v = v := birkRho_birkZR y
  have hwρ : birkRho w = w := by
    have := birkGamma_rho (ha := ha) (hm := hm) (hp := hp) (-1) v hq
    rw [hvρ] at this
    exact this.symm
  have hΓv := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) (-1) v hq
  have hZP : birkZR (birkPi w) = w := birkZR_birkPi w hwρ
  refine ⟨birkPi w, ?_, ?_⟩
  · have h1 : ‖birkPi w‖ ≤ 10 / 9 * ‖v‖ := (norm_birkPi_le w).trans hΓv
    have h2 : ‖birkPi w‖ ^ 2 ≤ (10 / 9 * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (10 / 9 * ‖v‖) ^ 2 = 100 / 81 * ‖v‖ ^ 2 := by ring
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 320 * birkCF m p)
    nlinarith
  · unfold birkGammaRExt
    rw [hZP, hwdef]
    have h5 := birkGamma_neg_birkGamma (ha := ha) (hm := hm) (hp := hp) (-1) v
      (by norm_num) hv160
    rw [neg_neg] at h5
    rw [h5, hvdef, birkPi_birkZR]

end KAM.Wave

end
