/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Quartic.Jet
public import KAM.Planetary.PlanarTorsion.Quartic.Reduce
public import KAM.Planetary.PlanarTorsion.SpectralAdapter
public import KAM.Planetary.SecularForm.DiagonalJet
public import KAM.Planetary.SecularForm.Quadratic.PairDiag

/-!
# Planar quartic torsion: the diagonal coefficients against Part 8 (P11C, package T6)

Blueprint P, Part 11b (`stepP:p11b:qe-c12`).  Along a ray with one planet circular, the physical
fixed secular average is the literal pair average `pairSlowSecular` of Part 8 (for the swapped
case after exchanging the planets), so `pairSlowSecular_diag_jet` gives its fourth coefficient
on the ray; `qeDiag_fix_first` and `qeDiag_fix_second` read off the fourth diagonal derivative.
-/

@[expose] public noncomputable section
open Set Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler SecularForm
variable {n : ℕ}

/-! ### Calculus on a line -/

private theorem qeDiag_deriv_poly (c0 c1 c2 c3 c4 : ℝ) :
    deriv (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4) =
      fun t => c1 + (2 * c2) * t + (3 * c3) * t ^ 2 + (4 * c4) * t ^ 3 + 0 * t ^ 4 := by
  funext t
  have h : HasDerivAt (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4)
      (c1 + (2 * c2) * t + (3 * c3) * t ^ 2 + (4 * c4) * t ^ 3 + 0 * t ^ 4) t := by
    have h1 := ((((hasDerivAt_const t c0).add ((hasDerivAt_id t).const_mul c1)).add
      ((hasDerivAt_pow 2 t).const_mul c2)).add ((hasDerivAt_pow 3 t).const_mul c3)).add
      ((hasDerivAt_pow 4 t).const_mul c4)
    convert h1 using 1
    · funext x; simp
    · push_cast; ring
  exact h.deriv

private theorem qeDiag_poly4 (c0 c2 c4 : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => c0 + c2 * t ^ 2 + c4 * t ^ 4) 0 = 24 * c4 := by
  have h : (fun t : ℝ => c0 + c2 * t ^ 2 + c4 * t ^ 4) =
      fun t : ℝ => c0 + 0 * t + c2 * t ^ 2 + 0 * t ^ 3 + c4 * t ^ 4 := by
    funext t; ring
  rw [h, iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
    iteratedDeriv_zero, qeDiag_deriv_poly, qeDiag_deriv_poly, qeDiag_deriv_poly,
    qeDiag_deriv_poly]
  simp
  ring

/-- The fourth derivative of a function with the expansion `A + c s² + A₄ s⁴ + O(|s|⁶)`. -/
theorem qeDiag_iteratedDeriv_four {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0) {A c A4 C r : ℝ}
    (hr : 0 < r) (h : ∀ s : ℝ, |s| < r → |φ s - (A + c * s ^ 2 + A4 * s ^ 4)| ≤ C * |s| ^ 6) :
    iteratedDeriv 4 φ 0 = 24 * A4 := by
  have hpoly : AnalyticAt ℝ (fun s : ℝ => A + c * s ^ 2 + A4 * s ^ 4) 0 := by fun_prop
  have hρ : AnalyticAt ℝ (fun s : ℝ => φ s - (A + c * s ^ 2 + A4 * s ^ 4)) 0 := hφ.sub hpoly
  have hl : ∀ᶠ s in 𝓝 (0 : ℝ), |φ s - (A + c * s ^ 2 + A4 * s ^ 4)| ≤ C * ‖s‖ ^ 6 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with s hs
    rw [Real.norm_eq_abs]
    exact h s (by simpa using hs)
  have h4 := qeJet_iteratedFDeriv_eq_zero hρ hl (j := 4) (by norm_num) 1
  rw [← iteratedDeriv_eq_iteratedFDeriv] at h4
  have hsplit : φ = (fun s : ℝ => A + c * s ^ 2 + A4 * s ^ 4) +
      fun s : ℝ => φ s - (A + c * s ^ 2 + A4 * s ^ 4) := by
    funext s; simp
  have hc1 : ContDiffAt ℝ 4 (fun s : ℝ => A + c * s ^ 2 + A4 * s ^ 4) 0 :=
    hpoly.contDiffAt
  have hc2 : ContDiffAt ℝ 4 (fun s : ℝ => φ s - (A + c * s ^ 2 + A4 * s ^ 4)) 0 :=
    hρ.contDiffAt
  rw [hsplit, iteratedDeriv_add hc1 hc2, h4, qeDiag_poly4, add_zero]

/-- The diagonal `j`-th derivative at `0` of an analytic function is the derivative along a line. -/
theorem qeDiag_iteratedFDeriv_line {P : Phase 2 → ℝ} (hP : AnalyticAt ℝ P 0) (z : Phase 2)
    (j : ℕ) :
    iteratedFDeriv ℝ j P 0 (fun _ => z) = iteratedDeriv j (fun t : ℝ => P (t • z)) 0 := by
  obtain ⟨U, hU, hUo, h0U⟩ := eventually_nhds_iff.1 hP.eventually_analyticAt
  let g : ℝ →L[ℝ] Phase 2 := ContinuousLinearMap.toSpanSingleton ℝ z
  have hf : ContDiffOn ℝ j P U := fun y hy => (hU y hy).contDiffAt.contDiffWithinAt
  have hg0 : g 0 ∈ U := by simpa [g] using h0U
  have hUg : IsOpen (g ⁻¹' U) := hUo.preimage g.continuous
  have hcomp := g.iteratedFDerivWithin_comp_right hf hUo.uniqueDiffOn hUg.uniqueDiffOn hg0 le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hUg (show (0 : ℝ) ∈ g ⁻¹' U from hg0),
    iteratedFDerivWithin_of_isOpen j hUo hg0] at hcomp
  have hev := congrArg (fun L => L (fun _ : Fin j => (1 : ℝ))) hcomp
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, g,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_zero] at hev
  have hfun : (fun t : ℝ => P (t • z)) = P ∘ g := by
    funext t; simp [g]
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun]
  exact hev.symm

/-! ### The fourth derivative of the pair average along a ray -/

/-- The fourth derivative of the pair average along `s ↦ (s u, 0)` (Part 8 diagonal jet). -/
theorem qeDiag_pair_ray (D : Data n) (p q : Fin n) {I J : ℝ} (hI : 0 < I) (hJ : 0 < J)
    (hab : I ^ 2 / (D.m p ^ 2 * (D.G * D.m0)) ≠ J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)))
    (u : Vec 2)
    (hφ : AnalyticAt ℝ (fun s : ℝ => pairSlowSecular D p q I J (s • (u, 0))) 0) :
    iteratedDeriv 4 (fun s : ℝ => pairSlowSecular D p q I J (s • (u, 0))) 0 =
      24 * (-D.G * D.m p * D.m q *
        (iteratedDeriv 4 (radialH (I ^ 2 / (D.m p ^ 2 * (D.G * D.m0)))
          (J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)))) 0 / 64 -
        iteratedDeriv 2 (radialH (I ^ 2 / (D.m p ^ 2 * (D.G * D.m0)))
          (J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)))) 0 / 16) * (planeSq u / I) ^ 2) := by
  obtain ⟨r, C, hr, hC, hbd⟩ := pairSlowSecular_diag_jet D p q hI hJ hab
  set H := radialH (I ^ 2 / (D.m p ^ 2 * (D.G * D.m0))) (J ^ 2 / (D.m q ^ 2 * (D.G * D.m0)))
    with hH
  set P := planeSq u with hP
  have hL : 0 ≤ planeLength u := planeLength_nonneg u
  have hε : 0 < min 1 (r / (planeLength u + 1)) := lt_min one_pos (by positivity)
  refine qeDiag_iteratedDeriv_four hφ
    (A := -D.G * D.m p * D.m q * H 0)
    (c := -D.G * D.m p * D.m q * (iteratedDeriv 2 H 0 / 4) * (P / I))
    (A4 := -D.G * D.m p * D.m q * (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) *
      (P / I) ^ 2)
    (C := C * planeLength u ^ 6) hε fun s hs => ?_
  have hs2 : |s| < r / (planeLength u + 1) := lt_of_lt_of_le hs (min_le_right _ _)
  have hsL : |s| * planeLength u < r := by
    have := (lt_div_iff₀ (by positivity : 0 < planeLength u + 1)).1 hs2
    nlinarith [abs_nonneg s]
  have hlen : planeLength (s • u) = |s| * planeLength u := planeLength_smul s u
  have hsq : planeSq (s • u) = s ^ 2 * P := planeSq_smul' s u
  have h := hbd (s • u) (by rw [hlen]; exact hsL)
  rw [hlen, hsq] at h
  simp only [Prod.smul_mk, smul_zero]
  calc _ = |pairSlowSecular D p q I J (s • u, 0) - (-D.G * D.m p * D.m q *
          (H 0 + iteratedDeriv 2 H 0 / 4 * (s ^ 2 * P / I) +
            (iteratedDeriv 4 H 0 / 64 - iteratedDeriv 2 H 0 / 16) * (s ^ 2 * P / I) ^ 2))| := by
        congr 2
        ring
    _ ≤ C * (|s| * planeLength u) ^ 6 := h
    _ = C * planeLength u ^ 6 * |s| ^ 6 := by ring

/-! ### The physical secular average on a ray -/

/-- Near `0`, the physical fixed secular average on a ray is the literal pair average. -/
theorem qeDiag_secular_ray (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (z : Phase 2) :
    ∀ᶠ s in 𝓝 (0 : ℝ), p11c_secular (p11c_hatFix p) (p.actions a) (s • z) =
      pairSlowSecular (p11cSecularData p hp) 0 1 (p.actions a 0) (p.actions a 1)
        (s • ((![z.1 0, z.2 0] : Vec 2), (![z.1 1, z.2 1] : Vec 2))) := by
  obtain ⟨W, hW, -, hgood⟩ := exists_pair_nbhd (p11cSecularData p hp) (p11c_axes_mem ha)
    (i := 0) (j := 1) (by decide)
  have hc : Continuous fun s : ℝ => s • ((![z.1 0, z.2 0] : Vec 2), (![z.1 1, z.2 1] : Vec 2)) :=
    continuous_id.smul continuous_const
  have h0 := hc.tendsto 0
  rw [zero_smul] at h0
  filter_upwards [h0.eventually hW] with s hs
  obtain ⟨hx, hsep⟩ := hgood _ hs
  have h := secular_embedSlow_eq (p11cSecularData p hp) 0 1 (p.actions a 0) (p.actions a 1) _ hx
    hsep
  rw [pairData_self] at h
  rw [← h]
  have hI : (![p.actions a 0, p.actions a 1] : Vec 2) = p.actions a := by
    funext k; fin_cases k <;> rfl
  have hz : embedSlow (p.actions a 0) (p.actions a 1)
      (s • ((![z.1 0, z.2 0] : Vec 2), (![z.1 1, z.2 1] : Vec 2))) = (s • z.1, p.actions a, s • z.2)
      := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> funext k <;> fin_cases k <;> simp [embedSlow]
  rw [hz]
  rfl

/-! ### The diagonal coefficients -/

/-- `stepP:p11b:qe-c12` (inner-eccentric case): the fourth diagonal derivative of the physical
fixed secular average along the first planet's `ξ`-direction is
`24 · (-G m₁ m₂ (h⁗(0)/64 - h''(0)/16) / Λ₁²)` with `h = radialH a₁ a₂` (analyticity at `0` is
the premise `hP`, discharged in `quartic_diagonal`). -/
theorem qeDiag_fix_first (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (hP : AnalyticAt ℝ (p11c_secular (p11c_hatFix p) (p.actions a)) 0) :
    iteratedFDeriv ℝ 4 (p11c_secular (p11c_hatFix p) (p.actions a)) 0
        (fun _ => ((![1, 0], ![0, 0]) : Phase 2)) =
      24 * (-p.G * p.m 0 * p.m 1 * (iteratedDeriv 4 (radialH (a 0) (a 1)) 0 / 64 -
        iteratedDeriv 2 (radialH (a 0) (a 1)) 0 / 16) / p.actions a 0 ^ 2) := by
  have ha' := p11c_axes_mem ha
  have hI0 : 0 < p.actions a 0 := qe_actions_pos p hp ha 0
  have hI1 : 0 < p.actions a 1 := qe_actions_pos p hp ha 1
  have e0 : p.actions a 0 ^ 2 / ((p11cSecularData p hp).m 0 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) = a 0 :=
    action_sq_div (p11cSecularData p hp) ha' 0
  have e1 : p.actions a 1 ^ 2 / ((p11cSecularData p hp).m 1 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) = a 1 :=
    action_sq_div (p11cSecularData p hp) ha' 1
  have hab : p.actions a 0 ^ 2 / ((p11cSecularData p hp).m 0 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) ≠
      p.actions a 1 ^ 2 / ((p11cSecularData p hp).m 1 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) := by
    rw [e0, e1]; exact ha.2.ne
  have hφ : AnalyticAt ℝ (fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 0 1
      (p.actions a 0) (p.actions a 1) (s • ((![1, 0] : Vec 2), 0))) 0 :=
    (analyticAt_pairSlowSecular (p11cSecularData p hp) ha' (i := 0) (j := 1) (by decide)).comp_of_eq
      (analyticAt_id.smul analyticAt_const) (by simp)
  have hev : (fun t : ℝ => p11c_secular (p11c_hatFix p) (p.actions a)
      (t • ((![1, 0], ![0, 0]) : Phase 2))) =ᶠ[𝓝 0]
      fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 0 1 (p.actions a 0) (p.actions a 1)
        (s • ((![1, 0] : Vec 2), 0)) := by
    filter_upwards [qeDiag_secular_ray p hp ha ((![1, 0], ![0, 0]) : Phase 2)] with s hs
    rw [hs]
    have : (![0, 0] : Vec 2) = 0 := by funext k; fin_cases k <;> rfl
    simp [this]
  rw [qeDiag_iteratedFDeriv_line hP, hev.iteratedDeriv_eq,
    qeDiag_pair_ray (p11cSecularData p hp) 0 1 hI0 hI1 hab _ hφ, e0, e1]
  have : planeSq (![1, 0] : Vec 2) = 1 := by simp [planeSq, Fin.sum_univ_two]
  rw [this]
  change 24 * (-p.G * p.m 0 * p.m 1 * _ * (1 / p.actions a 0) ^ 2) = _
  field_simp

/-- `stepP:p11b:qe-c12` (outer-eccentric case): the same along the second planet's `ξ`-direction,
`24 · (-G m₁ m₂ (h⁗(0)/64 - h''(0)/16) / Λ₂²)` with the swapped `h = radialH a₂ a₁`. -/
theorem qeDiag_fix_second (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (hP : AnalyticAt ℝ (p11c_secular (p11c_hatFix p) (p.actions a)) 0) :
    iteratedFDeriv ℝ 4 (p11c_secular (p11c_hatFix p) (p.actions a)) 0
        (fun _ => ((![0, 1], ![0, 0]) : Phase 2)) =
      24 * (-p.G * p.m 0 * p.m 1 * (iteratedDeriv 4 (radialH (a 1) (a 0)) 0 / 64 -
        iteratedDeriv 2 (radialH (a 1) (a 0)) 0 / 16) / p.actions a 1 ^ 2) := by
  have ha' := p11c_axes_mem ha
  have hI0 : 0 < p.actions a 0 := qe_actions_pos p hp ha 0
  have hI1 : 0 < p.actions a 1 := qe_actions_pos p hp ha 1
  have e0 : p.actions a 0 ^ 2 / ((p11cSecularData p hp).m 0 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) = a 0 :=
    action_sq_div (p11cSecularData p hp) ha' 0
  have e1 : p.actions a 1 ^ 2 / ((p11cSecularData p hp).m 1 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) = a 1 :=
    action_sq_div (p11cSecularData p hp) ha' 1
  have hab : p.actions a 1 ^ 2 / ((p11cSecularData p hp).m 1 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) ≠
      p.actions a 0 ^ 2 / ((p11cSecularData p hp).m 0 ^ 2 *
      ((p11cSecularData p hp).G * (p11cSecularData p hp).m0)) := by
    rw [e0, e1]; exact ha.2.ne'
  have hc : Tendsto (fun s : ℝ => s • (((0 : Vec 2), (![1, 0] : Vec 2)) : Vec 2 × Vec 2)) (𝓝 0)
      (𝓝 0) := by
    have : Continuous fun s : ℝ => s • (((0 : Vec 2), (![1, 0] : Vec 2)) : Vec 2 × Vec 2) :=
      continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hφ' : AnalyticAt ℝ (fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 0 1
      (p.actions a 0) (p.actions a 1) (s • (((0 : Vec 2), (![1, 0] : Vec 2)) : Vec 2 × Vec 2)))
      0 :=
    (analyticAt_pairSlowSecular (p11cSecularData p hp) ha' (i := 0) (j := 1) (by decide)).comp_of_eq
      (analyticAt_id.smul analyticAt_const) (by simp)
  have hswap : (fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 1 0 (p.actions a 1)
      (p.actions a 0) (s • ((![1, 0] : Vec 2), 0))) =ᶠ[𝓝 0]
      fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 0 1 (p.actions a 0) (p.actions a 1)
        (s • (((0 : Vec 2), (![1, 0] : Vec 2)) : Vec 2 × Vec 2)) := by
    filter_upwards [hc.eventually (pair_swap_nbhd (p11cSecularData p hp) ha'
      (i := 0) (j := 1) (by decide))] with s hs
    have h := hs
    simp only [Prod.smul_mk, smul_zero] at h ⊢
    exact h
  have hφ : AnalyticAt ℝ (fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 1 0
      (p.actions a 1) (p.actions a 0) (s • ((![1, 0] : Vec 2), 0))) 0 := hφ'.congr hswap.symm
  have hev : (fun t : ℝ => p11c_secular (p11c_hatFix p) (p.actions a)
      (t • ((![0, 1], ![0, 0]) : Phase 2))) =ᶠ[𝓝 0]
      fun s : ℝ => pairSlowSecular (p11cSecularData p hp) 1 0 (p.actions a 1) (p.actions a 0)
        (s • ((![1, 0] : Vec 2), 0)) := by
    filter_upwards [qeDiag_secular_ray p hp ha ((![0, 1], ![0, 0]) : Phase 2),
      hswap] with s hs hs2
    rw [hs, hs2]
    have : (![0, 0] : Vec 2) = 0 := by funext k; fin_cases k <;> rfl
    simp [this]
  rw [qeDiag_iteratedFDeriv_line hP, hev.iteratedDeriv_eq,
    qeDiag_pair_ray (p11cSecularData p hp) 1 0 hI1 hI0 hab _ hφ, e0, e1]
  have : planeSq (![1, 0] : Vec 2) = 1 := by simp [planeSq, Fin.sum_univ_two]
  rw [this]
  change 24 * (-p.G * p.m 1 * p.m 0 * _ * (1 / p.actions a 1) ^ 2) = _
  field_simp

end KAM.Planetary

end
