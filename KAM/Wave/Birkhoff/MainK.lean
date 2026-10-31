/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Birkhoff.MainQuart
public import KAM.Wave.Birkhoff.LieBirkAnalytic

/-!
# The remainder `K` and its size (blueprint-W `bpW:w3:main` (i))

Package W3-MAIN, blueprint label `bpW:w3:main`.

`birkK = H ∘ Γ - Λ - Ḡ - G^{nor}` on `B_{ρ₁}` (`Γ = Γ_1`, `H = Λ + G`), `K = K₁ + K₂` with
`K₁ = G ∘ Γ - G` and `K₂ = Λ ∘ Γ - Λ - Z'`; `norm_birkK1_le`, `norm_birkK2_le` (each
`≤ 5 C_* C_F ‖w‖⁶`), `norm_birkK_le` (`|K| ≤ 10 C_* C_F ‖w‖⁶`), analyticity and reality.
-/

@[expose] public noncomputable section

namespace KAM.Wave

open scoped ComplexConjugate

variable (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)

include ha hp in
theorem birkLambda_rho (w : BirkSpace) :
    birkLambda m hm ha hp (birkRho w) = conj (birkLambda m hm ha hp w) := by
  rw [birkLambda_eq, birkLambda_eq, Complex.conj_tsum]
  refine tsum_congr fun j => ?_
  simp only [birkCoord_birkRho, birkNeg, map_mul, Complex.conj_ofReal]
  simp only [Bool.not_true, Bool.not_false]
  ring

variable {m hm ha hp}

include hp in
/-- Mean value inequality for a quartic form with cubic field `‖X y‖₊ ≤ C ‖y‖³`. -/
theorem norm_sub_le_quart {P : BirkSpace → ℂ} {X : BirkSpace → BirkSpace} {C : ℝ} (hC : 0 ≤ C)
    (hP : IsBirkClassA a p ha (by linarith) Set.univ P X) (hX : ∀ y, ‖X y‖ ≤ C * ‖y‖ ^ 3)
    (y y' : BirkSpace) :
    ‖P y' - P y‖ ≤ C * (max ‖y‖ ‖y'‖) ^ 3 * ‖y' - y‖ := by
  set R := max ‖y‖ ‖y'‖ with hR
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (le_max_left _ _)
  have hderiv : ∀ z ∈ Metric.closedBall (0 : BirkSpace) R,
      HasFDerivWithinAt P ((fderiv ℂ P z).restrictScalars ℝ) (Metric.closedBall (0 : BirkSpace) R)
        z := fun z _ =>
    (((hP.analytic z (Set.mem_univ _)).differentiableAt.hasFDerivAt).restrictScalars ℝ
      ).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall (0 : BirkSpace) R,
      ‖(fderiv ℂ P z).restrictScalars ℝ‖ ≤ C * R ^ 3 := fun z hz => by
    have hzR : ‖z‖ ≤ R := by simpa using hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    show ‖fderiv ℂ P z v‖ ≤ _
    rw [hP.field z (Set.mem_univ _) v]
    refine (norm_birkOmegaPlus_le ha (by linarith) _ _).trans ?_
    calc ‖X z‖ * ‖v‖ ≤ (C * ‖z‖ ^ 3) * ‖v‖ := mul_le_mul_of_nonneg_right (hX z) (norm_nonneg _)
      _ ≤ (C * R ^ 3) * ‖v‖ := by gcongr
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (convex_closedBall _ _) (by rw [mem_closedBall_zero_iff]; exact le_max_left _ _)
    (by rw [mem_closedBall_zero_iff]; exact le_max_right _ _)

section K

variable (m hm ha hp)

/-- `K₁ = G ∘ Γ - G`. -/
def birkK1 (w : BirkSpace) : ℂ :=
  birkHamG m hm ha hp (birkGamma m hm ha hp 1 w) - birkHamG m hm ha hp w

/-- `K₂ = Λ ∘ Γ - Λ - Z'`. -/
def birkK2 (w : BirkSpace) : ℂ :=
  birkLambda m hm ha hp (birkGamma m hm ha hp 1 w) - birkLambda m hm ha hp w -
    birkHamZ m hm ha hp w

/-- `K = H ∘ Γ - Λ - Ḡ - G^{nor}` with `H = Λ + G`. -/
def birkK (w : BirkSpace) : ℂ :=
  (birkLambda m hm ha hp (birkGamma m hm ha hp 1 w) +
      birkHamG m hm ha hp (birkGamma m hm ha hp 1 w))
    - birkLambda m hm ha hp w - birkHamBar m hm ha hp w - birkHamNor m hm ha hp w

include ha hp in
theorem birkK_eq (w : BirkSpace) :
    birkK m hm ha hp w = birkK1 m hm ha hp w + birkK2 m hm ha hp w := by
  unfold birkK birkK1 birkK2
  rw [birkHamZ_eq m hm ha hp w, birkHamG_eq m hm ha hp w]
  ring

end K

variable (m hm ha hp) in
include ha hp in
theorem birkHamG_isClassA :
    IsBirkClassA a p ha (by linarith) Set.univ (birkHamG m hm ha hp) (birkHamGX m hm ha hp) :=
  birkQuart_isClassA m hm ha hp (birkCoefAll_isCoef m hm)

variable (m hm ha hp) in
include ha hp in
theorem birkHamZ_isClassA :
    IsBirkClassA a p ha (by linarith) Set.univ (birkHamZ m hm ha hp) (birkHamZX m hm ha hp) :=
  birkQuart_isClassA m hm ha hp (birkCoefZ_isCoef m hm)

variable (m hm ha hp) in
include ha hp in
theorem norm_birkHamGX_le (y : BirkSpace) :
    ‖birkHamGX m hm ha hp y‖ ≤ waveCubicConst p * ‖y‖ ^ 3 :=
  norm_birkQuartX_le m hm ha hp (birkCoefAll_isCoef m hm) y

variable (m hm ha hp) in
include ha hp in
theorem norm_birkHamZX_le (y : BirkSpace) :
    ‖birkHamZX m hm ha hp y‖ ≤ waveCubicConst p * ‖y‖ ^ 3 :=
  norm_birkQuartX_le m hm ha hp (birkCoefZ_isCoef m hm) y

include hm hp in
/-- The mean-value bound along the flow for a quartic with cubic field of constant `C_*`:
`|P(Γ_t w) - P(w)| ≤ 5 C_* C_F t ‖w‖⁶` for `t ∈ [0,1]`, `‖w‖ < ρ₁`. -/
theorem norm_quart_comp_sub_le {P : BirkSpace → ℂ} {X : BirkSpace → BirkSpace}
    (hP : IsBirkClassA a p ha (by linarith) Set.univ P X)
    (hX : ∀ y, ‖X y‖ ≤ waveCubicConst p * ‖y‖ ^ 3) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖P (birkGamma m hm ha hp t w) - P w‖ ≤
      5 * waveCubicConst p * birkCF m p * t * ‖w‖ ^ 6 := by
  have hCs := waveCubicConst_nonneg p
  have hCF := (birkCF_pos m hm hp).le
  have hw0 := norm_nonneg w
  have hq : 2 * |t| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_of_nonneg ht0]
    have h1 : 0 ≤ birkCF m p * ‖w‖ ^ 2 := by positivity
    nlinarith
  have hΓ := norm_birkGamma_le (ha := ha) (hm := hm) (hp := hp) t w hq
  have hd := norm_birkGamma_sub_le (ha := ha) (hm := hm) (hp := hp) t w hq
  have h := norm_sub_le_quart (hp := hp) hCs hP hX w (birkGamma m hm ha hp t w)
  have hmax : max ‖w‖ ‖birkGamma m hm ha hp t w‖ ≤ 10 / 9 * ‖w‖ :=
    max_le (by linarith) hΓ
  rw [abs_of_nonneg ht0] at hd
  have h3 : (max ‖w‖ ‖birkGamma m hm ha hp t w‖) ^ 3 ≤ (10 / 9 * ‖w‖) ^ 3 :=
    pow_le_pow_left₀ (le_trans hw0 (le_max_left _ _)) hmax 3
  calc _ ≤ waveCubicConst p * (max ‖w‖ ‖birkGamma m hm ha hp t w‖) ^ 3 *
        ‖birkGamma m hm ha hp t w - w‖ := h
    _ ≤ waveCubicConst p * (10 / 9 * ‖w‖) ^ 3 * (3 * t * birkCF m p * ‖w‖ ^ 3) := by
        gcongr
    _ = (3000 / 729) * waveCubicConst p * birkCF m p * t * ‖w‖ ^ 6 := by ring
    _ ≤ 5 * waveCubicConst p * birkCF m p * t * ‖w‖ ^ 6 := by
        have : 0 ≤ waveCubicConst p * birkCF m p * t * ‖w‖ ^ 6 := by positivity
        nlinarith

include hm hp in
/-- (`bpW:w3:main` (i)) `|K₁(w)| ≤ 5 C_* C_F ‖w‖⁶`. -/
theorem norm_birkK1_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkK1 m hm ha hp w‖ ≤ 5 * waveCubicConst p * birkCF m p * ‖w‖ ^ 6 := by
  have := norm_quart_comp_sub_le (ha := ha) (hm := hm) (hp := hp)
    (birkHamG_isClassA m hm ha hp) (norm_birkHamGX_le m hm ha hp) 1 zero_le_one le_rfl w hw
  simpa [birkK1, birkGamma] using this

include hm hp in
/-- `∂_t Λ(Γ_t w) = Z'(Γ_t w)` (flow equation and homological identity). -/
theorem hasDerivAt_birkLambda_gamma (s : ℝ) (w : BirkSpace) (hs : |s| < 2)
    (hw : 40 * birkCF m p * ‖w‖ ^ 2 < 1) :
    HasDerivAt (fun r : ℝ => birkLambda m hm ha hp (birkGamma m hm ha hp r w))
      (birkHamZ m hm ha hp (birkGamma m hm ha hp s w)) s := by
  have hflow := birkGamma_flow (ha := ha) (hm := hm) (hp := hp) s w hs hw
  set y := birkGamma m hm ha hp s w with hy
  have hΛ : HasFDerivAt (birkLambda m hm ha hp) (fderiv ℂ (birkLambda m hm ha hp) y) y :=
    ((birkLambda_analyticOnNhd (m := m) (hm := hm) (ha := ha) (hp := hp)) y
      (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have h := (hΛ.restrictScalars ℝ).comp_hasDerivAt s hflow
  refine h.congr_deriv ?_
  have e : (![y, y, y] : Fin 3 → BirkSpace) = fun _ => y := by
    funext i; fin_cases i <;> rfl
  rw [← birk_homological_Z m hm ha hp y, birkT_apply, e, ← birkXF_eq m hm ha hp y]
  rfl

include hm hp in
/-- (`bpW:w3:main` (i)) `|K₂(w)| ≤ 5 C_* C_F ‖w‖⁶`. -/
theorem norm_birkK2_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkK2 m hm ha hp w‖ ≤ 5 * waveCubicConst p * birkCF m p * ‖w‖ ^ 6 := by
  have hw40 : 40 * birkCF m p * ‖w‖ ^ 2 < 1 := by
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  set h : ℝ → ℂ := fun t => birkLambda m hm ha hp (birkGamma m hm ha hp t w) -
    birkLambda m hm ha hp w - (t : ℂ) * birkHamZ m hm ha hp w with hh
  have hder : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt h
      (birkHamZ m hm ha hp (birkGamma m hm ha hp t w) - birkHamZ m hm ha hp w) (Set.Icc 0 1) t :=
    fun t ht => by
      have h1 := hasDerivAt_birkLambda_gamma (ha := ha) (hm := hm) (hp := hp) t w
        (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]) hw40
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * birkHamZ m hm ha hp w)
          (birkHamZ m hm ha hp w) t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (birkHamZ m hm ha hp w)
      exact ((h1.sub_const _).sub h2).hasDerivWithinAt
  have hbd : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖birkHamZ m hm ha hp (birkGamma m hm ha hp t w) -
      birkHamZ m hm ha hp w‖ ≤ 5 * waveCubicConst p * birkCF m p * ‖w‖ ^ 6 := fun t ht => by
    have := norm_quart_comp_sub_le (ha := ha) (hm := hm) (hp := hp)
      (birkHamZ_isClassA m hm ha hp) (norm_birkHamZX_le m hm ha hp) t ht.1 ht.2.le w hw
    refine this.trans ?_
    have : 0 ≤ waveCubicConst p * birkCF m p * ‖w‖ ^ 6 :=
      mul_nonneg (mul_nonneg (waveCubicConst_nonneg p) (birkCF_pos m hm hp).le) (by positivity)
    nlinarith [ht.2]
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd 1 ⟨zero_le_one, le_rfl⟩
  have e0 : h 0 = 0 := by simp [hh, birkGamma, lieGamma_zero]
  have e1 : h 1 = birkK2 m hm ha hp w := by simp [hh, birkK2, birkGamma]
  rw [e0, e1] at this
  simpa using this

include hm hp in
/-- (`bpW:w3:main` (i)) `|K(w)| ≤ C_K ‖w‖⁶`, `C_K = 10 C_* C_F`. -/
theorem norm_birkK_le (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    ‖birkK m hm ha hp w‖ ≤ 10 * waveCubicConst p * birkCF m p * ‖w‖ ^ 6 := by
  rw [birkK_eq m hm ha hp w]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_birkK1_le (ha := ha) (hm := hm) (hp := hp) w hw
  have h2 := norm_birkK2_le (ha := ha) (hm := hm) (hp := hp) w hw
  linarith

include hm hp in
/-- (`bpW:w3:main` (i)) `K` is analytic on `B_{ρ₀}` (in particular on `B_{ρ₁}`). -/
theorem birkK_analyticOnNhd :
    AnalyticOnNhd ℂ (birkK m hm ha hp) {w | 40 * birkCF m p * ‖w‖ ^ 2 < 1} := by
  intro w hw
  have hΓ := birkGamma_analyticOnNhd (ha := ha) (hm := hm) (hp := hp) 1 (by norm_num) w hw
  have hΛ := fun y => (birkLambda_analyticOnNhd (m := m) (hm := hm) (ha := ha) (hp := hp)) y
    (Set.mem_univ _)
  have hG := fun y => (birkHamG_isClassA m hm ha hp).analytic y (Set.mem_univ _)
  have hB := fun y => (birkQuart_isClassA m hm ha hp (birkCoefBar_isCoef m hm)).analytic y
    (Set.mem_univ _)
  have hN := fun y => (birkQuart_isClassA m hm ha hp (birkCoefNor_isCoef m hm)).analytic y
    (Set.mem_univ _)
  have hΓ' : AnalyticAt ℂ (birkGamma m hm ha hp 1) w := hΓ
  unfold birkK
  exact ((((hΛ _).comp hΓ').add ((hG _).comp hΓ')).sub (hΛ w)).sub (hB w) |>.sub (hN w)

include hm hp in
/-- (`bpW:w3:main` (i)) `K` is real. -/
theorem birkK_rho (w : BirkSpace) (hw : 160 * birkCF m p * ‖w‖ ^ 2 < 1) :
    birkK m hm ha hp (birkRho w) = conj (birkK m hm ha hp w) := by
  have hq : 2 * |(1 : ℝ)| * birkCF m p * ‖w‖ ^ 2 ≤ 1 / 10 := by
    rw [abs_one]
    have : 0 ≤ birkCF m p * ‖w‖ ^ 2 := mul_nonneg (birkCF_pos m hm hp).le (sq_nonneg _)
    nlinarith
  have hΓ : birkGamma m hm ha hp 1 (birkRho w) = birkRho (birkGamma m hm ha hp 1 w) :=
    birkGamma_rho (ha := ha) (hm := hm) (hp := hp) 1 w hq
  unfold birkK
  rw [hΓ, birkLambda_rho m hm ha hp, birkLambda_rho m hm ha hp]
  have e1 := birkQuartP_rho m hm ha hp (birkCoefAll_isCoef m hm)
  have e2 := birkQuartP_rho m hm ha hp (birkCoefBar_isCoef m hm)
  have e3 := birkQuartP_rho m hm ha hp (birkCoefNor_isCoef m hm)
  unfold birkHamG birkHamBar birkHamNor
  rw [e1, e2, e3]
  simp only [map_sub, map_add]

end KAM.Wave

end
