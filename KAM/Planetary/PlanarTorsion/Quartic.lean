/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Quartic.Defs
public import KAM.Planetary.PlanarTorsion.Quartic.Bounds
public import KAM.Planetary.PlanarTorsion.Quartic.Diagonal
public import KAM.Planetary.SecularForm.ModelTransfer
public import KAM.Planetary.PlanarTorsion.SpectralAdapter

/-!
# Planar quartic torsion: the six quartic coefficients (P11C, package T6)

Blueprint P, Part 11b (`bpP:p11b:quartic-explicit`; steps `qe-conv`, `qe-an`, `qe-c12`).  The
coefficients `p11c_coeffs p a` (`Quartic/Defs`) are real analytic on the admissible axes, and the
degree-four homogeneous part of the actual fixed and moving secular averages at the actions of `a`
is the quartic `p11c_quartic (p11c_coeffs p a)`.

*Proof.*  `qe_secular_eq` writes the fixed secular average as `pref · pairAverage α (qeV I u)`; with
the jet of `pairAverage` (`pair_jet`, package T5) and the exact conversion algebra (`qe_alg`),
the difference with the polynomial `qePoly p a` is analytic and `O(‖u‖⁶)`
(`qe_remainder_bound`), so its fourth jet vanishes (`qeJet_iteratedFDeriv_eq_zero`).  The fourth
homogeneous part of `qePoly` is read off along lines.  The moving secular average has the same
positive-order jets (`same_jets`, Part 8), the two differing by an action-only constant.
-/

@[expose] public noncomputable section
open Set Real Function Filter
open scoped Topology ContDiff
namespace KAM.Planetary

/-! ### Fourth derivative along a line -/

private theorem qe_deriv_poly4 (c0 c1 c2 c3 c4 : ℝ) :
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

private theorem qe_iteratedDeriv_four (c0 c1 c2 c3 c4 : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => c0 + c1 * t + c2 * t ^ 2 + c3 * t ^ 3 + c4 * t ^ 4) 0 =
      24 * c4 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ',
    iteratedDeriv_zero, qe_deriv_poly4, qe_deriv_poly4, qe_deriv_poly4, qe_deriv_poly4]
  simp
  ring

/-- The fourth diagonal derivative of a function that is a quartic polynomial along a line. -/
theorem qe_iteratedFDeriv_four (P : Phase 2 → ℝ) (hP : ContDiff ℝ 4 P) (z : Phase 2)
    (c q2 q4 : ℝ) (h : ∀ t : ℝ, P (t • z) = c + t ^ 2 * q2 + t ^ 4 * q4) :
    iteratedFDeriv ℝ 4 P 0 (fun _ => z) = 24 * q4 := by
  let g : ℝ →L[ℝ] Phase 2 := ContinuousLinearMap.toSpanSingleton ℝ z
  have hcomp := g.iteratedFDeriv_comp_right hP (0 : ℝ) (i := 4) le_rfl
  have hfun : (P ∘ g) = fun t : ℝ => c + 0 * t + q2 * t ^ 2 + 0 * t ^ 3 + q4 * t ^ 4 := by
    funext t
    simp only [Function.comp, g, ContinuousLinearMap.toSpanSingleton_apply, h]
    ring
  have hev := congrArg (fun L => L (fun _ : Fin 4 => (1 : ℝ))) hcomp
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, g,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, map_zero] at hev
  rw [hfun] at hev
  rw [← hev, ← iteratedDeriv_eq_iteratedFDeriv]
  exact qe_iteratedDeriv_four _ _ _ _ _

/-! ### The polynomial part -/

theorem qe_quartic_smul (c : Fin 6 → ℝ) (t : ℝ) (z : Phase 2) :
    p11c_quartic c (t • z) = t ^ 4 * p11c_quartic c z := by
  unfold p11c_quartic p11c_pairDot
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring

theorem qePoly_line (p : PlanarData) (a : Fin 2 → ℝ) (z : Phase 2) :
    ∃ c q2 : ℝ, ∀ t : ℝ,
      qePoly p a (t • z) = c + t ^ 2 * q2 + t ^ 4 * p11c_quartic (p11c_coeffs p a) z := by
  refine ⟨-p.G * p.m 0 * p.m 1 / a 1 * p11c_laplace (1 / 2) 0 (a 0 / a 1),
    -p.G * p.m 0 * p.m 1 / a 1 * (p11c_pairCoeffs (a 0 / a 1) 0 *
      (qeA (p.actions a) z 0 + qeA (p.actions a) z 1) +
      p11c_pairCoeffs (a 0 / a 1) 1 * qeD (p.actions a) z), fun t => ?_⟩
  have hA : ∀ i, qeA (p.actions a) (t • z) i = t ^ 2 * qeA (p.actions a) z i := by
    intro i
    unfold qeA
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    ring
  have hD : qeD (p.actions a) (t • z) = t ^ 2 * qeD (p.actions a) z := by
    unfold qeD p11c_pairDot
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    ring
  unfold qePoly
  rw [hA, hA, hD, qe_quartic_smul]
  ring

theorem qePoly_contDiff (p : PlanarData) (a : Fin 2 → ℝ) : ContDiff ℝ 4 (qePoly p a) := by
  unfold qePoly qeA qeD p11c_quartic p11c_pairDot
  fun_prop

/-! ### The fixed secular average -/

theorem qe_eventually_small (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) :
    ∀ᶠ u in 𝓝 (0 : Phase 2), ∀ i, (u.1 i ^ 2 + u.2 i ^ 2) / 2 < p.actions a i := by
  rw [Filter.eventually_all]
  intro i
  have hc : Continuous fun u : Phase 2 => (u.1 i ^ 2 + u.2 i ^ 2) / 2 := by fun_prop
  exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using qe_actions_pos p hp ha i)

theorem qe_fix_jet (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (z : Phase 2) :
    iteratedFDeriv ℝ 4 (p11c_secular (p11c_hatFix p) (p.actions a)) 0 (fun _ => z) =
      24 * p11c_quartic (p11c_coeffs p a) z := by
  have hev : p11c_secular (p11c_hatFix p) (p.actions a) =ᶠ[𝓝 0] qeS p a := by
    filter_upwards [qe_eventually_small p hp ha] with u hu
    exact qe_secular_eq p hp ha hu
  rw [(hev.iteratedFDeriv ℝ 4).eq_of_nhds]
  obtain ⟨C, hC⟩ := qe_remainder_bound p hp ha
  have hR : AnalyticAt ℝ (fun u => qeS p a u - qePoly p a u) 0 :=
    (qeS_analyticAt p hp ha).sub (qePoly_analyticAt p a)
  have hR4 := qeJet_iteratedFDeriv_eq_zero hR hC (j := 4) (by norm_num) z
  have hsplit : qeS p a = qePoly p a + fun u => qeS p a u - qePoly p a u := by
    funext u; simp
  have hcd : ContDiffAt ℝ 4 (qePoly p a) 0 := (qePoly_contDiff p a).contDiffAt
  have hRd : ContDiffAt ℝ 4 (fun u => qeS p a u - qePoly p a u) 0 := hR.contDiffAt
  rw [hsplit, iteratedFDeriv_add_apply hcd hRd]
  simp only [add_apply, hR4, add_zero]
  obtain ⟨c, q2, hline⟩ := qePoly_line p a z
  exact qe_iteratedFDeriv_four _ (qePoly_contDiff p a) z c q2 _ hline

/-! ### The moving secular average and the analyticity of the coefficients -/

theorem qe_mov_jet (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    iteratedFDeriv ℝ 4 (p11c_secular (p11c_hatMov p) (p.actions a)) 0 =
      iteratedFDeriv ℝ 4 (p11c_secular (p11c_hatFix p) (p.actions a)) 0 := by
  have h := SecularForm.same_jets (p11cSecularData p hp) (I := p.actions a)
    ⟨a, p11c_axes_mem ha, rfl⟩ 4 (by norm_num)
  exact h

private theorem qeC_proj (i : Fin 2) (a : Fin 2 → ℝ) : AnalyticAt ℝ (fun a : Fin 2 → ℝ => a i) a :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).analyticAt a

theorem qe_coeffs_analyticAt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ}
    (ha : a ∈ p11c_axes) : AnalyticAt ℝ (p11c_coeffs p) a := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have ha0 : 0 < a 0 := ha.1
  have ha1 : 0 < a 1 := ha.1.trans ha.2
  have hI0 := qe_actions_pos p hp ha 0
  have hI1 := qe_actions_pos p hp ha 1
  have hIan : ∀ i, 0 < a i → AnalyticAt ℝ (fun a : Fin 2 → ℝ => p.actions a i) a := by
    intro i hai
    have h : AnalyticAt ℝ (fun a : Fin 2 → ℝ => p.kappa * a i) a :=
      analyticAt_const.mul (qeC_proj i a)
    have h2 := ((h.contDiffAt (n := ω)).sqrt (by positivity)).analyticAt
    exact analyticAt_const.mul h2
  have hI0a := hIan 0 ha0
  have hI1a := hIan 1 ha1
  have hα : AnalyticAt ℝ (fun a : Fin 2 → ℝ => a 0 / a 1) a :=
    (qeC_proj 0 a).div (qeC_proj 1 a) ha1.ne'
  have hco : ∀ k, AnalyticAt ℝ (fun a : Fin 2 → ℝ => p11c_pairCoeffs (a 0 / a 1) k) a := by
    intro k
    have h := analyticAt_pi_iff.1 (pair_series.1 _ ⟨by linarith [(qe_alpha_mem ha).1],
      (qe_alpha_mem ha).2⟩) k
    exact h.comp_of_eq hα rfl
  have hpref : AnalyticAt ℝ (fun a : Fin 2 → ℝ => -p.G * p.m 0 * p.m 1 / a 1) a :=
    analyticAt_const.div (qeC_proj 1 a) ha1.ne'
  have hr : ∀ i (c : ℝ), 0 < a i → AnalyticAt ℝ (fun a : Fin 2 → ℝ => p.actions a i ^ c) a := by
    intro i c hai
    exact (((hIan i hai).contDiffAt (n := ω)).rpow_const_of_ne
      (qe_actions_pos p hp ha i).ne').analyticAt
  have r00 := hr 0 (3 / 2) ha0
  have r01 := hr 0 (1 / 2) ha0
  have r10 := hr 1 (3 / 2) ha1
  have r11 := hr 1 (1 / 2) ha1
  have c0 := hco 0
  have c1 := hco 1
  have c2 := hco 2
  have c3 := hco 3
  have c4 := hco 4
  have c5 := hco 5
  have c6 := hco 6
  have c7 := hco 7
  have p0 : 0 < p.actions a 0 := hI0
  have p1 : 0 < p.actions a 1 := hI1
  rw [analyticAt_pi_iff]
  intro i
  fin_cases i <;> simp only [p11c_coeffs, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk] <;>
    fun_prop (disch := positivity)

theorem quartic_explicit (p : PlanarData) (hp : p.Valid) :
    AnalyticOnNhd ℝ (p11c_coeffs p) p11c_axes ∧ ∀ a ∈ p11c_axes, ∀ z : Phase 2,
      p11c_homogeneousPart 4 (p11c_secular (p11c_hatFix p) (p.actions a)) z =
        p11c_quartic (p11c_coeffs p a) z ∧
      p11c_homogeneousPart 4 (p11c_secular (p11c_hatMov p) (p.actions a)) z =
        p11c_quartic (p11c_coeffs p a) z := by
  refine ⟨fun a ha => qe_coeffs_analyticAt p hp ha, fun a ha z => ?_⟩
  have hfix := qe_fix_jet p hp ha z
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  have hf : p11c_homogeneousPart 4 (p11c_secular (p11c_hatFix p) (p.actions a)) z =
      p11c_quartic (p11c_coeffs p a) z := by
    unfold p11c_homogeneousPart
    rw [hfix, h4]
    ring
  refine ⟨hf, ?_⟩
  unfold p11c_homogeneousPart at hf ⊢
  rw [qe_mov_jet p hp ha]
  exact hf

/-- `stepP:p11b:qe-c12` (`bpP:p11b:quartic-explicit`, comparison with Part 8): the coefficients
`c₁, c₂` of `p11c_coeffs` are `-G m₁ m₂ (h⁗(0)/64 - h''(0)/16)/Λ_i²` with `h = radialH aᵢ aⱼ`
for the eccentric planet `i` (for `c₂` the swapped `h = radialH a₂ a₁`). -/
theorem quartic_diagonal (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes) :
    p11c_coeffs p a 0 = -p.G * p.m 0 * p.m 1 * (iteratedDeriv 4 (SecularForm.radialH (a 0) (a 1))
        0 / 64 - iteratedDeriv 2 (SecularForm.radialH (a 0) (a 1)) 0 / 16) / p.actions a 0 ^ 2 ∧
    p11c_coeffs p a 1 = -p.G * p.m 0 * p.m 1 * (iteratedDeriv 4 (SecularForm.radialH (a 1) (a 0))
        0 / 64 - iteratedDeriv 2 (SecularForm.radialH (a 1) (a 0)) 0 / 16) / p.actions a 1 ^ 2 := by
  have hev : p11c_secular (p11c_hatFix p) (p.actions a) =ᶠ[𝓝 0] qeS p a := by
    filter_upwards [qe_eventually_small p hp ha] with u hu
    exact qe_secular_eq p hp ha hu
  have hP : AnalyticAt ℝ (p11c_secular (p11c_hatFix p) (p.actions a)) 0 :=
    (qeS_analyticAt p hp ha).congr hev.symm
  have h1 := (qe_fix_jet p hp ha ((![1, 0], ![0, 0]) : Phase 2)).symm.trans
    (qeDiag_fix_first p hp ha hP)
  have h2 := (qe_fix_jet p hp ha ((![0, 1], ![0, 0]) : Phase 2)).symm.trans
    (qeDiag_fix_second p hp ha hP)
  simp only [p11c_quartic, p11c_pairDot, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  constructor
  · linarith
  · linarith

end KAM.Planetary

end
