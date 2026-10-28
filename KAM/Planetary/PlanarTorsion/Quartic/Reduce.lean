/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Setting
public import KAM.Planetary.PlanarTorsion.PairJet.Defs
public import KAM.Planetary.PlanarTorsion.PairJet.Bridge
public import KAM.Planetary.PlanarTorsion.OrbitJet.Analytic
public import KAM.Planetary.SecularForm.Symmetry
public import KAM.Planetary.SecularForm.Momentum

/-!
# Planar quartic torsion: the physical secular average as the pair average (P11C, package T6)

Blueprint P, Part 11b (`stepP:p11b:qe-conv`, `qe-an`).  For two planets with axes `a` and actions
`I = p.actions a`, the fixed-center secular average at the Poincaré variables `u = (ξ, η)` is
`pref · p11c_pairAverage (a₀/a₁) (qeV I u)`, where `pref = -G m₀ m₁ / a₁` and `qeV I u` is the
regular eccentricity vector `v_i = √((1 - Γ_i/(2 I_i))/I_i) u_i`, `Γ_i = |u_i|²/2`.  The moving
secular average differs from it by the action-only constant `modelDelta`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Real Function Filter
open scoped Topology
namespace KAM.Planetary
open KAM KAM.Kepler

/-- The scale `c_i(u) = √((1 - Γ_i/(2 I_i))/I_i)` taking `(ξ_i, η_i)` to the eccentricity vector. -/
def qeScale (I : Fin 2 → ℝ) (u : Phase 2) (i : Fin 2) : ℝ :=
  √((1 - (u.1 i ^ 2 + u.2 i ^ 2) / 2 / (2 * I i)) / I i)

/-- The regular eccentricity vectors of the two planets, in the `Phase 2` layout. -/
def qeV (I : Fin 2 → ℝ) (u : Phase 2) : Phase 2 :=
  (fun i => qeScale I u i * u.1 i, fun i => qeScale I u i * u.2 i)

theorem qe_pairPotential_two (G : ℝ) (m : Fin 2 → ℝ) (q : Fin (2 * 2) → ℝ) :
    pairPotential G m q = G * m 0 * m 1 / planeLength (bodyVector q 0 - bodyVector q 1) := by
  have e0 : Finset.univ.filter (fun j : Fin 2 => (0 : Fin 2) < j) = {1} := by decide
  have e1 : Finset.univ.filter (fun j : Fin 2 => (1 : Fin 2) < j) = ∅ := by decide
  simp [pairPotential, Fin.sum_univ_two, e0, e1]

/-- The position of a planet is the axis times the unit-axis orbit at the eccentricity vector. -/
theorem qe_position {m κ L : ℝ} (hm : m ≠ 0) (hκ : κ ≠ 0) (hL : 0 < L) (lam ξ η : ℝ)
    (hu : (ξ ^ 2 + η ^ 2) / 2 < L) :
    let q := (poincare m κ (![lam, ξ], ![L, η])).1
    (q 0 : ℂ) + Complex.I * (q 1 : ℂ) =
      ((L ^ 2 / (m ^ 2 * κ) : ℝ) : ℂ) *
        p11c_orbit lam (poincareV (![lam, ξ], ![L, η])) := by
  intro q
  have hb := orbit_poincare_bridge lam L hL ![ξ, η] (by
    simpa [planeSq, Fin.sum_univ_two] using hu)
  simp only at hb
  have hq : q = (L ^ 2 / (m ^ 2 * κ)) • (poincare 1 (L ^ 2) (![lam, ξ], ![L, η])).1 := by
    have h1 : (1 : ℝ) ^ 2 * L ^ 2 ≠ 0 := by positivity
    simp only [q, poincare, one_pow, one_mul, smul_smul]
    congr 1
    simp only [Matrix.cons_val_zero]
    field_simp
  rw [hq]
  have hb' := hb
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb'
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  rw [← hb']
  ring

theorem qe_poincareV (I : Fin 2 → ℝ) (u : Phase 2) (i : Fin 2) (lam : ℝ) :
    poincareV (![lam, u.1 i], ![I i, u.2 i]) = ![(qeV I u).1 i, (qeV I u).2 i] := by
  ext j
  fin_cases j <;> simp [poincareV, poincareGamma, qeV, qeScale]

theorem qe_axis_sq (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (i : Fin 2) : p.actions a i ^ 2 / (p.m i ^ 2 * p.kappa) = a i := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hai : 0 < a i := by
    fin_cases i
    · exact ha.1
    · exact ha.1.trans ha.2
  have hm := hp.2.2 i
  unfold PlanarData.actions
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

theorem qe_actions_pos (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (i : Fin 2) : 0 < p.actions a i := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have hai : 0 < a i := by
    fin_cases i
    · exact ha.1
    · exact ha.1.trans ha.2
  have := hp.2.2 i
  unfold PlanarData.actions
  positivity

theorem qe_integrand (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    {u : Phase 2} (hu : ∀ i, (u.1 i ^ 2 + u.2 i ^ 2) / 2 < p.actions a i) (φ : Fin 2 → ℝ) :
    (fFix p.G p.m ∘ poincareProd p.m p.kappa) (assemble (p.actions a) φ u.2 u.1) =
      -p.G * p.m 0 * p.m 1 / a 1 *
        ‖((a 0 / a 1 : ℝ) : ℂ) * p11c_orbit (φ 0) ![(qeV (p.actions a) u).1 0,
            (qeV (p.actions a) u).2 0] -
          p11c_orbit (φ 1) ![(qeV (p.actions a) u).1 1, (qeV (p.actions a) u).2 1]‖⁻¹ := by
  have hk : 0 < p.kappa := mul_pos hp.1 hp.2.1
  have ha0 : 0 < a 0 := ha.1
  have ha1 : 0 < a 1 := ha.1.trans ha.2
  have hb : ∀ i : Fin 2,
      (((bodyVector (poincareProd p.m p.kappa (assemble (p.actions a) φ u.2 u.1)).1 i 0 : ℝ) : ℂ) +
        Complex.I * ((bodyVector (poincareProd p.m p.kappa
          (assemble (p.actions a) φ u.2 u.1)).1 i 1 : ℝ) : ℂ)) =
        ((a i : ℝ) : ℂ) * p11c_orbit (φ i)
          ![(qeV (p.actions a) u).1 i, (qeV (p.actions a) u).2 i] := by
    intro i
    have h1 : bodyVector (poincareProd p.m p.kappa (assemble (p.actions a) φ u.2 u.1)).1 i =
        (poincare (p.m i) p.kappa (planetBlock (assemble (p.actions a) φ u.2 u.1) i)).1 :=
      congrArg Prod.fst (poincareProd_block p.m p.kappa (assemble (p.actions a) φ u.2 u.1) i)
    rw [SecularForm.planetBlock_assemble] at h1
    rw [h1]
    have := qe_position (m := p.m i) (κ := p.kappa) (L := p.actions a i)
      (hp.2.2 i).ne' hk.ne' (qe_actions_pos p hp ha i) (φ i) (u.1 i) (u.2 i) (hu i)
    simp only at this
    rw [this, qe_axis_sq p hp ha i, qe_poincareV]
  simp only [Function.comp, fFix, qe_pairPotential_two]
  rw [p11cPJ_planeLength_sub, hb 0, hb 1]
  have h : ((a 0 : ℝ) : ℂ) * p11c_orbit (φ 0) ![(qeV (p.actions a) u).1 0,
        (qeV (p.actions a) u).2 0] -
      ((a 1 : ℝ) : ℂ) * p11c_orbit (φ 1) ![(qeV (p.actions a) u).1 1,
        (qeV (p.actions a) u).2 1] =
      ((a 1 : ℝ) : ℂ) * (((a 0 / a 1 : ℝ) : ℂ) * p11c_orbit (φ 0) ![(qeV (p.actions a) u).1 0,
        (qeV (p.actions a) u).2 0] - p11c_orbit (φ 1) ![(qeV (p.actions a) u).1 1,
        (qeV (p.actions a) u).2 1]) := by
    have : ((a 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha1.ne'
    push_cast
    field_simp
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha1]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem qe_secular_eq (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    {u : Phase 2} (hu : ∀ i, (u.1 i ^ 2 + u.2 i ^ 2) / 2 < p.actions a i) :
    p11c_secular (p11c_hatFix p) (p.actions a) u =
      -p.G * p.m 0 * p.m 1 / a 1 * p11c_pairAverage (a 0 / a 1) (qeV (p.actions a) u) := by
  unfold p11c_secular secularAverage p11c_pairAverage p11c_hatFix
  simp only [qe_integrand p hp ha hu]
  rw [integral_const_mul]
  simp only [Nat.cast_ofNat]
  ring

end KAM.Planetary

end
