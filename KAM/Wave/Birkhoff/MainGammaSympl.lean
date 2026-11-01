/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainGamma

/-!
# `Γ^ℝ` is symplectic (blueprint-W `bpW:w3:gamma-real` (iii))

Package W3-MAIN, blueprint label `bpW:w3:gamma-real`.

`birkGammaD_rho`: `ϱ DΓ(w) v = DΓ(ϱ w)(ϱ v)`. `birkGammaRExt_hasFDerivAt`: the real derivative of
`Γ^ℝ` is `Π DΓ(𝒵 x) 𝒵`. `birkGammaRExt_symplectic`: `ω(DΓ^ℝ ξ, DΓ^ℝ η) = ω(ξ, η)` for
`ω(x, x') = Σ_j (q_j p'_j - p_j q'_j)` (the form `Σ dq_j ∧ dp_j`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} {hm : 0 < m} {a p : ℝ} {ha : 0 ≤ a} {hp : 1 / 2 ≤ p}

include hm hp in
theorem birkGammaD_rho (w : BirkSpace) (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) (v : BirkSpace) :
    birkRho (birkGammaD m hm ha hp 1 w v) =
      birkGammaD m hm ha hp 1 (birkRho w) (birkRho v) := by
  have hρw : 40 * birkCF m p * ‖birkRho w‖ ^ 2 < 1 := by rwa [birkRho.norm_map]
  have h1 := birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 (birkRho w)
    (by norm_num) hρw
  have h2 : HasFDerivAt (fun w' => birkRho (birkGamma m hm ha hp 1 (birkRho w')))
      (birkRhoR.comp (((birkGammaD m hm ha hp 1 (birkRho w)).restrictScalars ℝ).comp
        birkRhoR)) w :=
    birkRhoR.hasFDerivAt.comp w (h1.comp w birkRhoR.hasFDerivAt)
  have hopen : IsOpen {w' : BirkSpace | 40 * birkCF m p * ‖w'‖ ^ 2 < 1} :=
    isOpen_lt (by fun_prop) continuous_const
  have hev : (fun w' => birkRho (birkGamma m hm ha hp 1 (birkRho w'))) =ᶠ[nhds w]
      fun w' => birkGamma m hm ha hp 1 w' := by
    filter_upwards [hopen.mem_nhds hw] with w' hw'
    have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w'‖ ^ 2 ≤ 1 / 10 := by
      rw [abs_one]
      have : 0 ≤ birkCF m p * ‖w'‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
      have hw'' : 40 * birkCF m p * ‖w'‖ ^ 2 < 1 := hw'
      nlinarith
    have := birkGamma_rho (ha := ha) (hm := hm) (hp := hp) 1 w' hq
    rw [this, birkRho_birkRho]
  have h3 := (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 w (by norm_num) hw)
  have h4 := (h2.congr_of_eventuallyEq hev.symm).unique h3
  have h5 := DFunLike.congr_fun h4 v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    birkRhoR_apply] at h5
  rw [← h5, birkRho_birkRho]

variable (a p) in
/-- The form `Σ_j dq_j ∧ dp_j` on `E_{a,p}` (weighted coordinates): `Σ_j (q_j p'_j - p_j q'_j)`. -/
def birkOmegaR (x x' : BirkReal) : ℝ :=
  ∑' j : ℕ+, (coeffW (K := ℝ) a p x.1 j * coeffW (K := ℝ) a p x'.2 j -
    coeffW (K := ℝ) a p x.2 j * coeffW (K := ℝ) a p x'.1 j)

theorem birkOmega_birkZR (ha : 0 ≤ a) (hp : 0 ≤ p) (x x' : BirkReal) :
    birkOmega ha hp (birkZR x) (birkZR x') = ((birkOmegaR a p x x' : ℝ) : ℂ) := by
  rw [birkZR_apply, birkZR_apply]
  exact birkOmega_birkZ_real ha hp x x'

include hm hp in
theorem birkGammaRExt_hasFDerivAt (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1) :
    HasFDerivAt (birkGammaRExt m hm ha hp)
      ((birkPi.comp ((birkGammaD m hm ha hp 1 (birkZR x)).restrictScalars ℝ)).comp birkZR) x := by
  have hw160 := birkZR_dom (hm := hm) (hp := hp) x hx
  have hw40 : 40 * birkCF m p * ‖birkZR x‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖birkZR x‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have h1 := (birkGamma_hasFDerivAt (ha := ha) (hm := hm) (hp := hp) 1 (birkZR x) (by norm_num)
    hw40).comp x birkZR.hasFDerivAt
  have h2 := birkPi.hasFDerivAt.comp x h1
  refine h2.congr_fderiv ?_
  exact ContinuousLinearMap.ext fun ξ => rfl

include hm hp in
/-- (`bpW:w3:gamma-real` (iii)) `Γ^ℝ` is symplectic for `Σ dq_j ∧ dp_j`. -/
theorem birkGammaRExt_symplectic (x : BirkReal) (hx : 320 * birkCF m p * ‖x‖ ^ 2 < 1)
    (ξ η : BirkReal) :
    birkOmegaR a p
        (((birkPi.comp ((birkGammaD m hm ha hp 1 (birkZR x)).restrictScalars ℝ)).comp birkZR) ξ)
        (((birkPi.comp ((birkGammaD m hm ha hp 1 (birkZR x)).restrictScalars ℝ)).comp birkZR) η)
      = birkOmegaR a p ξ η := by
  have hw160 := birkZR_dom (hm := hm) (hp := hp) x hx
  have hw40 : 40 * birkCF m p * ‖birkZR x‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖birkZR x‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hfix : ∀ ζ : BirkReal, birkRho (birkGammaD m hm ha hp 1 (birkZR x) (birkZR ζ)) =
      birkGammaD m hm ha hp 1 (birkZR x) (birkZR ζ) := fun ζ => by
    rw [birkGammaD_rho (ha := ha) (hm := hm) (hp := hp) _ hw40, birkRho_birkZR, birkRho_birkZR]
  have hZ : ∀ ζ : BirkReal, birkZR (((birkPi.comp ((birkGammaD m hm ha hp 1
      (birkZR x)).restrictScalars ℝ)).comp birkZR) ζ) =
      birkGammaD m hm ha hp 1 (birkZR x) (birkZR ζ) := fun ζ => by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    exact birkZR_birkPi _ (hfix ζ)
  have h1 := birkGammaD_symplectic (ha := ha) (hm := hm) (hp := hp) 1 (birkZR x) (birkZR ξ)
    (birkZR η) (by norm_num) hw40
  refine Complex.ofReal_injective ?_
  rw [← birkOmega_birkZR ha (by linarith : 0 ≤ p), ← birkOmega_birkZR ha (by linarith : 0 ≤ p),
    hZ, hZ]
  exact h1

end KAM.Wave

end
