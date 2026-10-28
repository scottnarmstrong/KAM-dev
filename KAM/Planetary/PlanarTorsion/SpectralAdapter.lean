/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Planetary.PlanarTorsion.LaplaceReduction
public import KAM.Planetary.SecularForm.Quadratic

/-!
# Planar quartic torsion: the physical quadratic form and its spectral data (P11C, package T12)

Blueprint P, Part 11b (`bpP:p11b:sec-beta#data`): the explicit physical matrix `p11c_Q`, its sorted
eigenvalues `p11c_sigma` and its spectral projector `p11c_projector`, together with
`quadratic_physical_bridge`: the second homogeneous jet at `z = 0` of the actual secular average
`p11c_secular (p11c_hatFix p)` at the actions of the axes `a` equals the two quadratic blocks of
`p11c_Q p a`.

The matrix is never assumed.  `p11c_Q_eq_coeffs` identifies `p11c_Q` with the Part-8 matrix
`SecularForm.coeffs` (via `p11c_laplace_eq_laplace_def`), and the bridge subtracts the polynomial
part given by Part 8's `quadratic_form` from the secular average: the remainder is analytic at `0`
and `O(‖z‖⁴)`, so its second iterated derivative vanishes (`p11c_iteratedFDeriv_two_of_isBigO`).
-/

@[expose] public noncomputable section
open Set Metric Real Function Filter Asymptotics
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler

/- Coefficients and global spectral projector are explicit and independent of a chosen
eigenbasis. -/
def p11c_Q (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let I := p.actions a
  let alpha := a 0 / a 1
  let A := p.G * p.m 0 * p.m 1 / (4 * a 1) * alpha * p11c_laplace (3 / 2) 1 alpha
  let B := p.G * p.m 0 * p.m 1 / (4 * a 1) * alpha * p11c_laplace (3 / 2) 2 alpha
  !![-A / I 0, B / sqrt (I 0 * I 1); B / sqrt (I 0 * I 1), -A / I 1]

def p11c_sigma (p : PlanarData) (a : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let Q := p11c_Q p a
  let R := sqrt ((Q 0 0 - Q 1 1) ^ 2 + 4 * Q 0 1 ^ 2)
  ![(Q 0 0 + Q 1 1 - R) / 2, (Q 0 0 + Q 1 1 + R) / 2]

def p11c_projector (p : PlanarData) (a : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (p11c_sigma p a 0 - p11c_sigma p a 1)⁻¹ •
    (p11c_Q p a - p11c_sigma p a 1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-! ### The Laplace adapter -/

theorem p11c_laplace_eq_laplace_def (s : ℝ) (k : ℤ) (a : ℝ) :
    p11c_laplace s k a = SecularForm.laplace_def s k a := by
  unfold p11c_laplace SecularForm.laplace_def
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hk : 0 ≤ 1 + a ^ 2 - 2 * a * cos t := by
    nlinarith [sq_nonneg (a - cos t), sin_sq_add_cos_sq t]
  rw [Real.rpow_neg hk, div_eq_mul_inv, mul_comm]

/-! ### Identification of `p11c_Q` with the Part-8 matrix -/

/-- The Part-8 data attached to valid physical data in two degrees of freedom. -/
def p11cSecularData (p : PlanarData) (hp : p.Valid) : SecularForm.Data 2 where
  G := p.G
  m0 := p.m0
  m := p.m
  hG := hp.1
  hm0 := hp.2.1
  hm := hp.2.2
  hn := by norm_num

theorem p11c_axes_mem {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) : a ∈ SecularForm.axes 2 := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · exact ha.1
    · exact ha.1.trans ha.2
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact ha.2 | (exfalso; revert hij; decide)

theorem p11c_Q_eq_coeffs (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    p11c_Q p a = SecularForm.coeffs (p11cSecularData p hp) a := by
  have h0 : 0 < a 0 := ha.1
  have h1 : 0 < a 1 := h0.trans ha.2
  have hI : ∀ i, 0 < p.actions a i := by
    intro i
    have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
    have := hp.2.2 i
    unfold PlanarData.actions
    have : 0 < a i := by fin_cases i <;> simp [h0, h1]
    positivity
  have e : ∀ i j, √(SecularForm.action (p11cSecularData p hp) a i) *
      √(SecularForm.action (p11cSecularData p hp) a j) = √(p.actions a i * p.actions a j) :=
    fun i j => (Real.sqrt_mul (hI i).le _).symm
  have e0 := hI 0
  have e1 := hI 1
  have h00 : √(p.actions a 0 * p.actions a 0) = p.actions a 0 := Real.sqrt_mul_self e0.le
  have h11 : √(p.actions a 1 * p.actions a 1) = p.actions a 1 := Real.sqrt_mul_self e1.le
  have hc : ∀ i j, SecularForm.coeffs (p11cSecularData p hp) a i j =
      SecularForm.qhat (p11cSecularData p hp) a i j / √(p.actions a i * p.actions a j) := by
    intro i j; rw [SecularForm.coeffs, e]
  ext i j
  rw [hc]
  fin_cases i <;> fin_cases j <;>
    simp [p11c_Q, SecularForm.qhat, SecularForm.pairA, SecularForm.pairB, h00, h11,
      p11c_laplace_eq_laplace_def, Fin.sum_univ_two, p11cSecularData, mul_comm (p.actions a 1)]
  all_goals field_simp

/-! ### A remainder of order four has no second derivative -/

private theorem p11c_eq_zero_of_isBigO {j : ℕ} {c : ℝ}
    (h : (fun t : ℝ => t ^ j * c) =O[𝓝 0] fun t : ℝ => t ^ (j + 1)) : c = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] 0, ‖c‖ ≤ C * |t| := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hC, self_mem_nhdsWithin] with t ht ht0
    have ht0' : t ≠ 0 := ht0
    simp only [norm_mul, norm_pow, Real.norm_eq_abs] at ht
    have hp : 0 < |t| ^ j := pow_pos (abs_pos.2 ht0') j
    rw [pow_succ] at ht
    have : |t| ^ j * ‖c‖ ≤ |t| ^ j * (C * |t|) := by
      rw [Real.norm_eq_abs]; linarith
    exact le_of_mul_le_mul_left this hp
  have hlim : Tendsto (fun t : ℝ => C * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * |t|) (𝓝 0) (𝓝 (C * |0|)) :=
      (continuous_const.mul continuous_abs).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  exact norm_eq_zero.1 (le_antisymm (ge_of_tendsto hlim hev) (norm_nonneg _))

private theorem p11c_diag_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} {p : FormalMultilinearSeries ℝ E ℝ} (hp : HasFPowerSeriesAt h p 0) {C : ℝ}
    (hl : ∀ᶠ z in 𝓝 (0 : E), |h z| ≤ C * ‖z‖ ^ 4) :
    ∀ j ≤ 3, ∀ w, p j (fun _ => w) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj w
    have hps : p.partialSum (j + 1) = fun y => p j fun _ => y := by
      funext y
      refine Finset.sum_eq_single_of_mem j (Finset.mem_range.2 (Nat.lt_succ_self j)) ?_
      intro k hk hne
      have hk' := Finset.mem_range.1 hk
      exact ih k (by omega) (by omega) y
    have h1 := hp.isBigO_sub_partialSum_pow (j + 1)
    rw [hps] at h1
    have hc : Continuous fun t : ℝ => t • w := by fun_prop
    have h2 : Tendsto (fun t : ℝ => t • w) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
    have h3 := h1.comp_tendsto h2
    simp only [Function.comp_def, zero_add] at h3
    have h4 : (fun t : ℝ => ‖t • w‖ ^ (j + 1)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      refine IsBigO.of_bound (‖w‖ ^ (j + 1)) (Eventually.of_forall fun t => ?_)
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
      rw [abs_of_nonneg (by positivity), mul_comm]
    have h5 := h3.trans h4
    have h6 : (fun t : ℝ => h (t • w)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      have hb : (fun t : ℝ => h (t • w)) =O[𝓝 0] fun t : ℝ => ‖t • w‖ ^ 4 := by
        refine IsBigO.of_bound C ?_
        filter_upwards [h2.eventually hl] with t ht
        simpa using ht
      refine hb.trans ?_
      have h7 : (fun t : ℝ => ‖t • w‖ ^ 4) =O[𝓝 0] fun t : ℝ => t ^ 4 := by
        refine IsBigO.of_bound (‖w‖ ^ 4) (Eventually.of_forall fun t => ?_)
        simp only [norm_smul, mul_pow, Real.norm_eq_abs, norm_pow]
        rw [abs_of_nonneg (by positivity), mul_comm]
      refine h7.trans (IsBigO.of_bound 1 ?_)
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
      have ht' : |t| < 1 := by simpa using ht
      simp only [norm_pow, Real.norm_eq_abs, one_mul]
      exact pow_le_pow_of_le_one (abs_nonneg t) ht'.le (by omega)
    have h8 : (fun t : ℝ => t ^ j * p j (fun _ => w)) =O[𝓝 0] fun t : ℝ => t ^ (j + 1) := by
      refine (h6.sub h5).congr_left fun t => ?_
      have : p j (fun _ => t • w) = t ^ j * p j (fun _ => w) := by
        have := (p j).map_smul_univ (fun _ : Fin j => (t : ℝ)) (fun _ => w)
        simpa [Finset.prod_const, Finset.card_fin] using this
      simp only [sub_sub_cancel, this]
    exact p11c_eq_zero_of_isBigO h8

theorem p11c_iteratedFDeriv_two_of_isBigO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (hh : AnalyticAt ℝ h 0) {C : ℝ} (hl : ∀ᶠ z in 𝓝 (0 : E), |h z| ≤ C * ‖z‖ ^ 4)
    (z : E) : iteratedFDeriv ℝ 2 h 0 (fun _ => z) = 0 := by
  obtain ⟨p, r, hp⟩ := hh
  have h2 := hp.factorial_smul z 2
  rw [p11c_diag_eq_zero hp.hasFPowerSeriesAt hl 2 (by norm_num) z] at h2
  simpa using h2.symm

/-- The second iterated derivative of a constant plus a form quadratic in each of two blocks. -/
theorem p11c_iteratedFDeriv_two_quad (Q : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) (z : Phase 2) :
    iteratedFDeriv ℝ 2
      (fun w : Phase 2 => c + SecularForm.quad Q w.1 + SecularForm.quad Q w.2) 0 (fun _ => z) =
      2 * (SecularForm.quad Q z.1 + SecularForm.quad Q z.2) := by
  set P : Phase 2 → ℝ := fun w => c + SecularForm.quad Q w.1 + SecularForm.quad Q w.2 with hP
  have hq : ∀ (t : ℝ) (x : Fin 2 → ℝ),
      SecularForm.quad Q (t • x) = t ^ 2 * SecularForm.quad Q x := by
    intro t x
    simp only [SecularForm.quad, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hcd : ContDiff ℝ 2 P := by
    simp only [hP, SecularForm.quad]
    fun_prop
  let g : ℝ →L[ℝ] Phase 2 := ContinuousLinearMap.toSpanSingleton ℝ z
  have hcomp := g.iteratedFDeriv_comp_right hcd (0 : ℝ) (i := 2) le_rfl
  have hfun : (P ∘ g) =
      fun t : ℝ => c + t ^ 2 * (SecularForm.quad Q z.1 + SecularForm.quad Q z.2) := by
    funext t
    simp only [Function.comp, hP, g, ContinuousLinearMap.toSpanSingleton_apply, Prod.smul_fst,
      Prod.smul_snd, hq]
    ring
  have hev := congrArg (fun L => L (fun _ : Fin 2 => (1 : ℝ))) hcomp
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, g,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_zero] at hev
  rw [hfun] at hev
  rw [← hev, ← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_succ, iteratedDeriv_one]
  have hd : deriv (fun t : ℝ => c + t ^ 2 * (SecularForm.quad Q z.1 + SecularForm.quad Q z.2)) =
      fun t => 2 * t * (SecularForm.quad Q z.1 + SecularForm.quad Q z.2) := by
    funext t
    simp
  rw [hd]
  simp

/-! ### The physical bridge -/

theorem quadratic_physical_bridge (p : PlanarData) (hp : p.Valid) (a : Fin 2 → ℝ)
    (ha : a ∈ p11c_axes) (z : Phase 2) :
    p11c_homogeneousPart 2 (p11c_secular (p11c_hatFix p) (p.actions a)) z =
      (∑ i, ∑ j, z.1 i * p11c_Q p a i j * z.1 j) +
      (∑ i, ∑ j, z.2 i * p11c_Q p a i j * z.2 j) := by
  set D := p11cSecularData p hp with hD
  have haD : a ∈ SecularForm.axes 2 := p11c_axes_mem ha
  rw [p11c_Q_eq_coeffs p hp ha]
  obtain ⟨r, C, hr, -, -, hAn, hbd⟩ := SecularForm.quadratic_form D haD
  set I : Fin 2 → ℝ := SecularForm.action D a with hI
  have hax : SecularForm.axis D I = a := SecularForm.axis_action D haD
  let Q := SecularForm.coeffs D a
  let ι : Phase 2 → SecularForm.Slow 2 := fun w => (w.1, I, w.2)
  let R : Phase 2 → ℝ := fun w =>
    SecularForm.secular D false (ι w) - SecularForm.constantTerm D a -
      SecularForm.quad Q w.1 - SecularForm.quad Q w.2
  have hmem : ∀ w : Phase 2, ‖w‖ < r → ι w ∈ SecularForm.realDisc D a r := by
    intro w hw i
    have h1 : ‖w.1 i‖ ≤ ‖w‖ := (norm_le_pi_norm w.1 i).trans (le_max_left _ _)
    have h2 : ‖w.2 i‖ ≤ ‖w‖ := (norm_le_pi_norm w.2 i).trans (le_max_right _ _)
    refine ⟨?_, ?_, ?_⟩
    · simpa [ι, SecularForm.inclusion] using h1.trans_lt hw
    · simpa [ι, SecularForm.inclusion, hI] using hr
    · simpa [ι, SecularForm.inclusion] using h2.trans_lt hw
  have hιan : AnalyticAt ℝ ι 0 := by
    exact (analyticAt_fst (𝕜 := ℝ)).prod (analyticAt_const.prod (analyticAt_snd (𝕜 := ℝ)))
  have hR : AnalyticAt ℝ R 0 := by
    have h0 : ι 0 ∈ SecularForm.realDisc D a r := hmem 0 (by simpa using hr)
    have h1 := (hAn (ι 0) h0).comp_of_eq hιan rfl
    refine h1.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Function.comp, ι, R, hax, Q]
  have hRb : ∀ᶠ w in 𝓝 (0 : Phase 2), |R w| ≤ C * ‖w‖ ^ 4 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Phase 2) hr] with w hw
    have hw' : ‖w‖ < r := by simpa using hw
    have h1 := hbd (ι w) (hmem w hw')
    have h2 : ‖((ι w).1, (ι w).2.2)‖ = ‖w‖ := rfl
    simpa only [ι, R, hax, Q, h2] using h1
  have hsplit : p11c_secular (p11c_hatFix p) (p.actions a) =
      (fun w : Phase 2 => SecularForm.constantTerm D a + SecularForm.quad Q w.1 +
        SecularForm.quad Q w.2) + R := by
    funext w
    simp only [Pi.add_apply, R]
    show SecularForm.secular D false (ι w) = _
    ring
  unfold p11c_homogeneousPart
  rw [hsplit, iteratedFDeriv_add_apply, add_apply,
    p11c_iteratedFDeriv_two_quad,
    p11c_iteratedFDeriv_two_of_isBigO hR hRb]
  · have h2 : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
    rw [h2, add_zero, mul_div_cancel_left₀ _ two_ne_zero]
    rfl
  · refine ContDiff.contDiffAt ?_
    simp only [SecularForm.quad, Q]
    fun_prop
  · exact hR.contDiffAt

end KAM.Planetary

end
