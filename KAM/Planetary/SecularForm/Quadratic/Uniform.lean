/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.Jet
public import KAM.Planetary.SecularForm.Quadratic.Schwarz

/-!
# Quadratic part: the locally uniform fourth-order bound

Blueprint P, Part 8, `stepP:p8:qf-assembly` (package S8-Q). The remainder
`S - C₀(axis Λ) - ξᵀQξ - ηᵀQη` is bounded by `C |(ξ, η)|⁴` uniformly for `Λ` near `action D a`:
on the complex line through `(ξ, Λ, η)` the remainder extends holomorphically to a disc, with a
bound uniform in `Λ`, and vanishes to order four at the origin (`iteratedDeriv_rayRemainder`), so
the Schwarz lemma `uniform_ray_bound` applies.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function Metric
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

/-- The remainder of the quadratic form. -/
def remainder (D : Data n) (x : Slow n) : ℝ :=
  secular D false x - constantTerm D (axis D x.2.1) - quad (coeffs D (axis D x.2.1)) x.1 -
    quad (coeffs D (axis D x.2.1)) x.2.2

theorem quad_smul (M : Mat n) (c : ℝ) (x : Vec n) : quad M (c • x) = c ^ 2 * quad M x := by
  unfold quad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem quad_zero (M : Mat n) : quad M 0 = 0 := by
  simp [quad]

theorem abs_quad_le (M : Mat n) {x : Vec n} (hx : ‖x‖ ≤ 1) :
    |quad M x| ≤ ∑ i, ∑ j, |M i j| := by
  unfold quad
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hi : |x i| ≤ 1 := by simpa using (norm_le_pi_norm x i).trans hx
  have hj : |x j| ≤ 1 := by simpa using (norm_le_pi_norm x j).trans hx
  rw [abs_mul, abs_mul]
  have := abs_nonneg (M i j)
  nlinarith [abs_nonneg (x i), abs_nonneg (x j), mul_le_mul hi hj (abs_nonneg _) zero_le_one]

theorem analyticAt_remainder (D : Data n) {x : Slow n} (hS : AnalyticAt ℝ (secular D false) x)
    (hb : axis D x.2.1 ∈ axes n) : AnalyticAt ℝ (remainder D) x := by
  have h1 : AnalyticAt ℝ (fun y : Slow n => y.1) x := analyticAt_fst
  have h2 : AnalyticAt ℝ (fun y : Slow n => y.2.1) x := analyticAt_fst.comp analyticAt_snd
  have h3 : AnalyticAt ℝ (fun y : Slow n => y.2.2) x := analyticAt_snd.comp analyticAt_snd
  have haxis : AnalyticAt ℝ (fun y : Slow n => axis D y.2.1) x :=
    (analyticAt_axis D _).comp h2
  have hT : AnalyticAt ℝ (fun y : Slow n => constantTerm D (axis D y.2.1)) x :=
    (analyticAt_constantTerm D hb).comp_of_eq haxis rfl
  have hE : AnalyticAt ℝ (fun y : Slow n => coeffs D (axis D y.2.1)) x :=
    (coeffs_analytic D _ hb).comp_of_eq haxis rfl
  have hq1 : AnalyticAt ℝ (fun y : Slow n => quad (coeffs D (axis D y.2.1)) y.1) x :=
    (analyticAt_quad (coeffs D (axis D x.2.1)) x.1).comp_of_eq (hE.prod h1) rfl
  have hq2 : AnalyticAt ℝ (fun y : Slow n => quad (coeffs D (axis D y.2.1)) y.2.2) x :=
    (analyticAt_quad (coeffs D (axis D x.2.1)) x.2.2).comp_of_eq (hE.prod h3) rfl
  exact ((hS.sub hT).sub hq1).sub hq2

/-- The coordinates of a point of `realDisc`. -/
theorem realDisc_coord (D : Data n) (a : Vec n) {r : ℝ} {x : Slow n} (hx : x ∈ realDisc D a r)
    (i : Fin n) : |x.1 i| < r ∧ |x.2.1 i - action D a i| < r ∧ |x.2.2 i| < r := by
  have h := hx i
  simp only [inclusion, Complex.norm_real, Real.norm_eq_abs] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
  exact ⟨h1, h2, h3⟩

theorem polydisc_mono (D : Data n) (a : Vec n) {r r' : ℝ} (h : r ≤ r') :
    polydisc D a r ⊆ polydisc D a r' := fun z hz i =>
  ⟨(hz i).1.trans_le h, (hz i).2.1.trans_le h, (hz i).2.2.trans_le h⟩

theorem realDisc_mono (D : Data n) (a : Vec n) {r r' : ℝ} (h : r ≤ r') :
    realDisc D a r ⊆ realDisc D a r' := fun _ hx => polydisc_mono D a h hx

/-- The point of the complex line through `(ξ, Λ, η)` with parameter `z`. -/
def linePt (Λ ξ η : Vec n) (z : ℂ) : CSlow n :=
  (fun i => z * (ξ i : ℂ), fun i => (Λ i : ℂ), fun i => z * (η i : ℂ))

theorem differentiable_linePt (Λ ξ η : Vec n) : Differentiable ℂ (linePt Λ ξ η) := by
  unfold linePt
  refine Differentiable.prodMk ?_ (Differentiable.prodMk ?_ ?_)
  · exact differentiable_pi.2 fun i => differentiable_id.mul_const _
  · exact differentiable_const _
  · exact differentiable_pi.2 fun i => differentiable_id.mul_const _

theorem linePt_mem_polydisc (D : Data n) (a : Vec n) {r : ℝ} {Λ ξ η : Vec n} {z : ℂ}
    (hz : ‖z‖ < r) (hξ : ‖ξ‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hΛ : ∀ i, |Λ i - action D a i| < r) : linePt Λ ξ η z ∈ polydisc D a r := by
  intro i
  have hξi : |ξ i| ≤ 1 := by simpa using (norm_le_pi_norm ξ i).trans hξ
  have hηi : |η i| ≤ 1 := by simpa using (norm_le_pi_norm η i).trans hη
  have hr : 0 ≤ r := (norm_nonneg z).trans hz.le
  refine ⟨?_, ?_, ?_⟩
  · show ‖z * (ξ i : ℂ)‖ < r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖z‖ * |ξ i| ≤ ‖z‖ * 1 := by gcongr
      _ < r := by linarith
  · show ‖(Λ i : ℂ) - (action D a i : ℂ)‖ < r
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hΛ i
  · show ‖z * (η i : ℂ)‖ < r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖z‖ * |η i| ≤ ‖z‖ * 1 := by gcongr
      _ < r := by linarith

theorem remainder_pointwise (D : Data n) {a : Vec n} (ha : a ∈ axes n)
    {r0 r M1 MT ME : ℝ} (hr : 0 < r) (hrr0 : r < r0) (hrho0 : r0 < rho D a)
    (hSD : DifferentiableOn ℂ (secularC D false) (polydisc D a r0))
    (hreal : ∀ x ∈ realDisc D a r0, secularC D false (inclusion x) = (secular D false x : ℂ))
    (hM1 : ∀ z ∈ polydisc D a r, ‖secularC D false z‖ ≤ M1)
    (hK : ∀ Λ : Vec n, dist Λ (action D a) < r → axis D Λ ∈ axes n ∧
      |constantTerm D (axis D Λ)| ≤ MT ∧ ∑ i, ∑ j, |coeffs D (axis D Λ) i j| ≤ ME)
    {x : Slow n} (hx : x ∈ realDisc D a r) :
    |remainder D x| ≤ (M1 + MT + 2 * r ^ 2 * ME) / r ^ 4 * ‖(x.1, x.2.2)‖ ^ 4 := by
  have hxs : x ∈ slowDom D :=
    mem_slowDom_of_realDisc D ha (hrr0.trans hrho0) hx
  have hxΛ : ∀ i, |x.2.1 i - action D a i| < r := fun i => (realDisc_coord D a hx i).2.1
  have hdist : dist x.2.1 (action D a) < r := by
    rw [dist_pi_lt_iff hr]
    intro i; rw [Real.dist_eq]; exact hxΛ i
  obtain ⟨hb, hTb, hEb⟩ := hK _ hdist
  have hΛpos : ∀ i, 0 < x.2.1 i := fun i => ((mem_slowDom_iff D x).1 hxs i).1
  have hact : action D (axis D x.2.1) = x.2.1 := action_axis D hΛpos
  set b := axis D x.2.1 with hbdef
  set ε := ‖(x.1, x.2.2)‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  have hx1 : ‖x.1‖ ≤ ε := by rw [hε, Prod.norm_def]; exact le_max_left _ _
  have hx3 : ‖x.2.2‖ ≤ ε := by rw [hε, Prod.norm_def]; exact le_max_right _ _
  have hεr : ε < r := by
    rw [hε, Prod.norm_def, max_lt_iff]
    exact ⟨(pi_norm_lt_iff hr).2 fun i => by simpa using (realDisc_coord D a hx i).1,
      (pi_norm_lt_iff hr).2 fun i => by simpa using (realDisc_coord D a hx i).2.2⟩
  rcases hε0.eq_or_lt with h0 | hpos
  · -- the point lies on the axis: the remainder is its value there
    have e1 : x.1 = 0 := norm_le_zero_iff.1 (by rw [← h0] at hx1; exact hx1)
    have e3 : x.2.2 = 0 := norm_le_zero_iff.1 (by rw [← h0] at hx3; exact hx3)
    have hxeq : x = ((0 : ℝ) • (0 : Vec n), action D b, (0 : ℝ) • (0 : Vec n)) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [e1, e3, hact]
    have : remainder D x = rayRemainder D b 0 0 0 := by
      unfold remainder rayRemainder raySlow
      rw [← hxeq, e1, e3, quad_zero]
      simp [hbdef]
    rw [this, rayRemainder_zero D hb]
    rw [← h0]
    simp
  · set ξ' : Vec n := ε⁻¹ • x.1 with hξ'
    set η' : Vec n := ε⁻¹ • x.2.2 with hη'
    have hnorm : ∀ v : Vec n, ‖v‖ ≤ ε → ‖ε⁻¹ • v‖ ≤ 1 := fun v hv => by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hε0]
      calc ε⁻¹ * ‖v‖ ≤ ε⁻¹ * ε := by gcongr
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    have hξ1 : ‖ξ'‖ ≤ 1 := hnorm _ hx1
    have hη1 : ‖η'‖ ≤ 1 := hnorm _ hx3
    set T := constantTerm D b with hT
    set Q' := quad (coeffs D b) ξ' + quad (coeffs D b) η' with hQ'
    set g : ℂ → ℂ := fun z => secularC D false (linePt x.2.1 ξ' η' z) - (T : ℂ) -
      z ^ 2 * (Q' : ℂ) with hg
    have hmaps : ∀ z ∈ ball (0 : ℂ) r, linePt x.2.1 ξ' η' z ∈ polydisc D a r := fun z hz =>
      linePt_mem_polydisc D a (by simpa using hz) hξ1 hη1 hxΛ
    have hgd : DifferentiableOn ℂ g (ball 0 r) := by
      have h1 : DifferentiableOn ℂ (fun z => secularC D false (linePt x.2.1 ξ' η' z))
          (ball 0 r) :=
        hSD.comp (differentiable_linePt _ _ _).differentiableOn
          (fun z hz => polydisc_mono D a hrr0.le (hmaps z hz))
      exact (h1.sub (differentiableOn_const _)).sub
        ((differentiableOn_id.pow 2).mul (differentiableOn_const _))
    have hQb : |Q'| ≤ 2 * ME := by
      have h1 := abs_quad_le (coeffs D b) hξ1
      have h2 := abs_quad_le (coeffs D b) hη1
      have := abs_add_le (quad (coeffs D b) ξ') (quad (coeffs D b) η')
      linarith
    have hbd : ∀ z ∈ ball (0 : ℂ) r, ‖g z‖ ≤ M1 + MT + 2 * r ^ 2 * ME := by
      intro z hz
      have hzr : ‖z‖ < r := by simpa using hz
      have h1 := hM1 _ (hmaps z hz)
      have h2 : ‖(T : ℂ)‖ ≤ MT := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hTb
      have h3 : ‖z ^ 2 * (Q' : ℂ)‖ ≤ 2 * r ^ 2 * ME := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        have : ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzr.le 2
        calc ‖z‖ ^ 2 * |Q'| ≤ r ^ 2 * (2 * ME) := by
              gcongr
          _ = 2 * r ^ 2 * ME := by ring
      calc ‖g z‖ ≤ ‖secularC D false (linePt x.2.1 ξ' η' z) - (T : ℂ)‖ + ‖z ^ 2 * (Q' : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ (‖secularC D false (linePt x.2.1 ξ' η' z)‖ + ‖(T : ℂ)‖) + ‖z ^ 2 * (Q' : ℂ)‖ := by
            gcongr; exact norm_sub_le _ _
        _ ≤ M1 + MT + 2 * r ^ 2 * ME := by linarith
    have hM : 0 ≤ M1 + MT + 2 * r ^ 2 * ME :=
      (norm_nonneg _).trans (hbd 0 (mem_ball_self hr))
    have hψa := analyticAt_rayRemainder D hb ξ' η'
    have hψ : (fun s : ℝ => g s) =ᶠ[𝓝 0] fun s => (rayRemainder D b ξ' η' s : ℂ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
      have hsr : ‖(s : ℂ)‖ < r := by simpa using hs
      have hpt : linePt x.2.1 ξ' η' (s : ℂ) = inclusion (raySlow D b ξ' η' s) := by
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i <;> simp [linePt, inclusion, raySlow, hact]
      have hmem : raySlow D b ξ' η' s ∈ realDisc D a r0 := by
        have := polydisc_mono D a hrr0.le
          (linePt_mem_polydisc D a hsr hξ1 hη1 hxΛ)
        rw [hpt] at this
        exact this
      simp only [hg]
      rw [hpt, hreal _ hmem]
      unfold rayRemainder
      push_cast
      simp only [hT, hQ']
      push_cast
      ring
    have hz := uniform_ray_bound hr hM hgd hbd hψa hψ
      (fun k hk => iteratedDeriv_rayRemainder D hb ξ' η' hk) (ε : ℂ) (by simpa [abs_of_nonneg hε0] using hεr)
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hpt : linePt x.2.1 ξ' η' (ε : ℂ) = inclusion x := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext i
      · simp only [linePt, inclusion, hξ', Pi.smul_apply, smul_eq_mul]
        push_cast
        field_simp
      · simp [linePt, inclusion]
      · simp only [linePt, inclusion, hη', Pi.smul_apply, smul_eq_mul]
        push_cast
        field_simp
    have hgε : g (ε : ℂ) = (remainder D x : ℂ) := by
      simp only [hg]
      rw [hpt, hreal x (realDisc_mono D a hrr0.le hx)]
      unfold remainder
      have hq : (ε : ℝ) ^ 2 * Q' = quad (coeffs D b) x.1 + quad (coeffs D b) x.2.2 := by
        rw [hQ', hξ', hη', quad_smul, quad_smul]
        field_simp
      push_cast
      have : ((ε : ℂ) ^ 2 * (Q' : ℂ)) = ((quad (coeffs D b) x.1 + quad (coeffs D b) x.2.2 : ℝ) : ℂ) := by
        rw [← hq]; push_cast; ring
      rw [this]
      push_cast
      ring
    rw [hgε, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hε0] at hz
    exact hz

end SecularForm
end KAM.Planetary
end
