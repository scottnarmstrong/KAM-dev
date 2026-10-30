/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Kepler.Plane
public import KAM.Kepler.Energy
public import KAM.Kepler.Orbit
public import KAM.Kepler.DelaunaySymplectic
public import KAM.Kepler.DelaunayChart
public import KAM.Kepler.Means

/-!
# Mass and strength: the scaled Delaunay chart

The mass/strength chart `delaunayMK m κ = 𝖲_{m,κ} ∘ 𝖰 ∘ (id, m⁻¹ ·)` and its properties
(`bpI:p7:scaling`, `bpP:p7:kepler-data`, `bpP:p7:range`, `bpP:p7:kepler`).  The scaling maps
`scaleMK`, the energy `energyMK`, the region `regionMK` and their elementary properties live in
`KAM.Kepler.Energy`; this module adds the range inequality `C ≤ Λ`, the chart `delaunayMK`
(symplectic of factor one, analytic, periodic, injective modulo the lattice, onto
`{C < Λ} ∩ 𝒦_{m,κ}`, local analytic diffeomorphism), the identities, the means, and the
Hamilton-flow clause of the scaling.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Kepler

open KAM KAM.Planetary

/-- `𝖰_{m,κ}(ℓ, g, Λ, C) = 𝖲_{m,κ} ∘ 𝖰(ℓ, g, Λ/m, C/m)`. -/
def delaunayMK (m κ : ℝ) (w : Phase 2) : Phase 2 := scaleMK m κ (delaunay (w.1, m⁻¹ • w.2))

section Linear

/-- The linear map `scaleMK m κ`. -/
private def scaleL (m κ : ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (κ⁻¹ • ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).prod
    ((m * κ) • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

/-- The inverse of `scaleL m κ`. -/
private def scaleInvL (m κ : ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (κ • ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).prod
    ((m * κ)⁻¹ • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

/-- The momentum rescaling `(q, p) ↦ (q, m⁻¹ p)`. -/
private def momL (m : ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).prod
    (m⁻¹ • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

/-- The inverse of `momL m`. -/
private def momInvL (m : ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).prod
    (m • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

private theorem scaleL_apply (m κ : ℝ) (z : Phase 2) : scaleL m κ z = scaleMK m κ z := rfl

private theorem scaleInvL_apply (m κ : ℝ) (z : Phase 2) :
    scaleInvL m κ z = (κ • z.1, (m * κ)⁻¹ • z.2) := rfl

private theorem momL_apply (m : ℝ) (z : Phase 2) : momL m z = (z.1, m⁻¹ • z.2) := rfl

private theorem momInvL_apply (m : ℝ) (z : Phase 2) : momInvL m z = (z.1, m • z.2) := rfl

private theorem scale_left_inv {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (z : Phase 2) :
    scaleInvL m κ (scaleMK m κ z) = z := by
  simp only [scaleInvL_apply, scaleMK, smul_smul, inv_mul_cancel₀ (mul_pos hm hκ).ne',
    mul_inv_cancel₀ hκ.ne', one_smul]

private theorem scale_right_inv {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (z : Phase 2) :
    scaleMK m κ (scaleInvL m κ z) = z := by
  simp only [scaleInvL_apply, scaleMK, smul_smul, mul_inv_cancel₀ (mul_pos hm hκ).ne',
    inv_mul_cancel₀ hκ.ne', one_smul]

private theorem mom_left_inv {m : ℝ} (hm : 0 < m) (z : Phase 2) : momInvL m (momL m z) = z := by
  simp only [momInvL_apply, momL_apply, smul_smul, mul_inv_cancel₀ hm.ne', one_smul]

private theorem mom_right_inv {m : ℝ} (hm : 0 < m) (z : Phase 2) : momL m (momInvL m z) = z := by
  simp only [momInvL_apply, momL_apply, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]

private def scaleE {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) : Phase 2 ≃L[ℝ] Phase 2 :=
  ContinuousLinearEquiv.equivOfInverse (scaleL m κ) (scaleInvL m κ)
    (fun z => scale_left_inv hm hκ z) (fun z => scale_right_inv hm hκ z)

private def momE {m : ℝ} (hm : 0 < m) : Phase 2 ≃L[ℝ] Phase 2 :=
  ContinuousLinearEquiv.equivOfInverse (momL m) (momInvL m)
    (fun z => mom_left_inv hm z) (fun z => mom_right_inv hm z)

/-- The momentum rescaling preserves `deDom`. -/
private theorem momL_mem {m : ℝ} (hm : 0 < m) {w : Phase 2} (hw : w ∈ deDom) :
    momL m w ∈ deDom := by
  obtain ⟨h1, h2⟩ := hw
  simp only [momL_apply]
  exact ⟨mul_pos (inv_pos.2 hm) h1, mul_lt_mul_of_pos_left h2 (inv_pos.2 hm)⟩

/-- The inverse momentum rescaling preserves `deDom`. -/
private theorem momInvL_mem {m : ℝ} (hm : 0 < m) {w : Phase 2} (hw : w ∈ deDom) :
    momInvL m w ∈ deDom := by
  obtain ⟨h1, h2⟩ := hw
  simp only [momInvL_apply]
  exact ⟨mul_pos hm h1, mul_lt_mul_of_pos_left h2 hm⟩

private theorem scale_sf {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (a b : Phase 2) :
    symplecticForm (scaleMK m κ a) (scaleMK m κ b) = m * symplecticForm a b := by
  simp only [symplecticForm, scaleMK, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

private theorem mom_sf {m : ℝ} (a b : Phase 2) :
    symplecticForm (momL m a) (momL m b) = m⁻¹ * symplecticForm a b := by
  simp only [symplecticForm, momL_apply, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The derivative of `delaunayMK` is `𝖲 ∘ D𝖰 ∘ (id, m⁻¹ ·)`. -/
private theorem hasFDerivAt_delaunayMK {m κ : ℝ} (hm : 0 < m) {w : Phase 2} (hw : w ∈ deDom) :
    HasFDerivAt (delaunayMK m κ)
      ((scaleL m κ).comp ((fderiv ℝ delaunay (momL m w)).comp (momL m))) w := by
  have h1 : HasFDerivAt (momL m) (momL m) w := (momL m).hasFDerivAt
  have h2 : HasFDerivAt delaunay (fderiv ℝ delaunay (momL m w)) (momL m w) :=
    delaunay_hasFDerivAt (momL_mem hm hw)
  have h3 : HasFDerivAt (scaleL m κ) (scaleL m κ) (delaunay (momL m w)) :=
    (scaleL m κ).hasFDerivAt
  have e : delaunayMK m κ = (scaleL m κ) ∘ delaunay ∘ (momL m) := rfl
  rw [e]
  exact h3.comp w (h2.comp w h1)

end Linear

section Chart

theorem delaunayMK_symplectic {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    IsSymplecticOn 1 (delaunayMK m κ) deDom := by
  intro w hw u v
  rw [(hasFDerivAt_delaunayMK hm hw).fderiv]
  simp only [ContinuousLinearMap.comp_apply, scaleL_apply]
  rw [scale_sf hm hκ, delaunay_symplectic _ (momL_mem hm hw), mom_sf]
  field_simp

theorem analyticOnNhd_delaunayMK {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    AnalyticOnNhd ℝ (delaunayMK m κ) deDom := by
  intro w hw
  have h1 : AnalyticAt ℝ (momL m) w := (momL m).analyticAt w
  have h2 : AnalyticAt ℝ delaunay (momL m w) := analyticOnNhd_delaunay _ (momL_mem hm hw)
  have h3 : AnalyticAt ℝ (scaleL m κ) (delaunay (momL m w)) :=
    (scaleL m κ).analyticAt _
  exact AnalyticAt.comp (g := scaleL m κ) (f := delaunay ∘ momL m) h3 (h2.comp h1)

/-- The chart is periodic in the angles. -/
theorem delaunayMK_periodic {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2} (hw : w ∈ deDom)
    (k k' : ℤ) :
    delaunayMK m κ (w.1 + ![2 * π * k, 2 * π * k'], w.2) = delaunayMK m κ w :=
  congrArg (scaleMK m κ) (delaunay_periodic (momL_mem hm hw) k k')

theorem delaunayMK_eq_iff {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w w' : Phase 2} (hw : w ∈ deDom)
    (hw' : w' ∈ deDom) : delaunayMK m κ w = delaunayMK m κ w' ↔
      ∃ k k' : ℤ, w'.1 = w.1 + ![2 * π * k, 2 * π * k'] ∧ w'.2 = w.2 := by
  have hinj := (scaleMK_bijective hm hκ).1
  have h := delaunay_eq_iff (momL_mem hm hw) (momL_mem hm hw')
  simp only [momL_apply] at h
  unfold delaunayMK
  rw [hinj.eq_iff, h]
  refine exists_congr fun k => exists_congr fun k' => and_congr Iff.rfl ?_
  constructor
  · intro h
    exact (smul_right_injective (Fin 2 → ℝ) (inv_ne_zero hm.ne')) h
  · intro h
    rw [h]

/-- The local analytic diffeomorphism structure: `D𝖰_{m,κ}` is invertible. -/
private theorem delaunayMK_fderiv_equiv {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ deDom) :
    ∃ B : Phase 2 ≃L[ℝ] Phase 2, (B : Phase 2 →L[ℝ] Phase 2) = fderiv ℝ (delaunayMK m κ) w := by
  obtain ⟨A, hA⟩ := delaunay_fderiv_equiv (momL_mem hm hw)
  refine ⟨(momE hm).trans (A.trans (scaleE hm hκ)), ?_⟩
  rw [(hasFDerivAt_delaunayMK hm hw).fderiv, ← hA]
  exact ContinuousLinearMap.ext fun z => rfl

/-- `bpP:p7:kepler` (a), completing the interface for the mass chart: local analytic
diffeomorphism at every point of `deDom`. -/
theorem delaunayMK_localDiffeo {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ deDom) :
    ∃ φ : OpenPartialHomeomorph (Phase 2) (Phase 2), w ∈ φ.source ∧
      (φ : Phase 2 → Phase 2) = delaunayMK m κ ∧ AnalyticOnNhd ℝ φ.symm φ.target := by
  obtain ⟨A, hA⟩ := delaunayMK_fderiv_equiv hm hκ hw
  have hc : ContDiffAt ℝ ω (delaunayMK m κ) w :=
    (analyticOnNhd_delaunayMK hm hκ w hw).contDiffAt
  have hf' : HasFDerivAt (delaunayMK m κ) (A : Phase 2 →L[ℝ] Phase 2) w := by
    rw [hA]; exact (analyticOnNhd_delaunayMK hm hκ w hw).differentiableAt.hasFDerivAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let φ0 := hc.toOpenPartialHomeomorph (delaunayMK m κ) hf' hn
  let φ := φ0.restrOpen deDom isOpen_deDom
  have hcoe : (φ : Phase 2 → Phase 2) = delaunayMK m κ := rfl
  refine ⟨φ, ⟨hc.mem_toOpenPartialHomeomorph_source hf' hn, hw⟩, hcoe, ?_⟩
  intro y hy
  have hxs : φ.symm y ∈ φ.source := φ.map_target hy
  have hx : φ.symm y ∈ deDom := hxs.2
  obtain ⟨B, hB⟩ := delaunayMK_fderiv_equiv hm hκ hx
  have hB' : HasFDerivAt φ (B : Phase 2 →L[ℝ] Phase 2) (φ.symm y) := by
    rw [hcoe, hB]
    exact (analyticOnNhd_delaunayMK hm hκ _ hx).differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℝ ω φ (φ.symm y) := by
    rw [hcoe]; exact (analyticOnNhd_delaunayMK hm hκ _ hx).contDiffAt
  exact (φ.contDiffAt_symm hy hB' hcd).analyticAt

end Chart

section Range

/-- The algebraic identity behind `bpP:p7:range` (Lagrange):
`m³κ² - D c² = (m²κ - rP)²/m + D d²` for `D = 2κm/r - P/m` and `c² = r²P - d²`. -/
private theorem range_identity {m κ r P d c : ℝ} (hm : 0 < m) (hr : 0 < r)
    (hc : c ^ 2 = r ^ 2 * P - d ^ 2) :
    m ^ 3 * κ ^ 2 - (2 * κ * m / r - P / m) * c ^ 2 =
      (m ^ 2 * κ - r * P) ^ 2 / m + (2 * κ * m / r - P / m) * d ^ 2 := by
  rw [hc]
  field_simp
  ring

/-- Data of a point of `regionMK`: the positive quantity `D = -2E`. -/
private theorem regionMK_data {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) :
    0 < planeLength z.1 ∧ 0 < -2 * energyMK m κ z ∧
      -2 * energyMK m κ z = 2 * κ * m / planeLength z.1 - planeSq z.2 / m ∧
      axisMK m κ z = κ * m / (-2 * energyMK m κ z) ∧
      planeCross z.1 z.2 ^ 2 = planeLength z.1 ^ 2 * planeSq z.2 - planeDot z.1 z.2 ^ 2 := by
  obtain ⟨hr, hE, hc⟩ := hz
  refine ⟨hr, by linarith, ?_, ?_, ?_⟩
  · unfold energyMK
    field_simp
    ring
  · unfold axisMK
    have : (2 : ℝ) * energyMK m κ z ≠ 0 := by linarith
    field_simp
  · have := planeSq_mul_planeSq z.1 z.2
    rw [planeLength_sq]
    linarith

/-- `actionMK² = m³κ²/D`. -/
private theorem actionMK_sq {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) :
    actionMK m κ z ^ 2 = m ^ 3 * κ ^ 2 / (-2 * energyMK m κ z) := by
  obtain ⟨hr, hD, -, hax, -⟩ := regionMK_data hm hκ hz
  have hax' : 0 ≤ κ * axisMK m κ z := by
    rw [hax]; positivity
  unfold actionMK
  rw [mul_pow, Real.sq_sqrt hax', hax]
  field_simp

private theorem actionMK_nonneg {m κ : ℝ} {z : Phase 2} (hm : 0 < m) : 0 ≤ actionMK m κ z := by
  unfold actionMK; positivity

/-- `bpP:p7:range`: on `𝒦_{m,κ}`, `C ≤ Λ`. -/
theorem cross_le_action {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) : planeCross z.1 z.2 ≤ actionMK m κ z := by
  obtain ⟨hr, hD, hDe, -, hcr⟩ := regionMK_data hm hκ hz
  have key := range_identity (m := m) (κ := κ) (r := planeLength z.1) (P := planeSq z.2)
    (d := planeDot z.1 z.2) (c := planeCross z.1 z.2) hm hr hcr
  rw [← hDe] at key
  have hsq : -2 * energyMK m κ z * planeCross z.1 z.2 ^ 2 ≤ m ^ 3 * κ ^ 2 := by
    have : 0 ≤ (m ^ 2 * κ - planeLength z.1 * planeSq z.2) ^ 2 / m := by positivity
    have : 0 ≤ -2 * energyMK m κ z * planeDot z.1 z.2 ^ 2 := by positivity
    linarith
  have hA := actionMK_sq hm hκ hz
  have hA' : -2 * energyMK m κ z * actionMK m κ z ^ 2 = m ^ 3 * κ ^ 2 := by
    rw [hA]; exact mul_div_cancel₀ _ hD.ne'
  have hnn := actionMK_nonneg (z := z) (κ := κ) hm
  by_contra h
  push Not at h
  have : actionMK m κ z ^ 2 < planeCross z.1 z.2 ^ 2 := by nlinarith
  nlinarith

/-- `bpP:p7:range`, equality case: `C = Λ` iff `q · p = 0` and `|q| = a`. -/
theorem cross_eq_action_iff {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {z : Phase 2}
    (hz : z ∈ regionMK m κ) :
    planeCross z.1 z.2 = actionMK m κ z ↔
      planeDot z.1 z.2 = 0 ∧ planeLength z.1 = axisMK m κ z := by
  obtain ⟨hr, hD, hDe, hax, hcr⟩ := regionMK_data hm hκ hz
  have hcpos : 0 < planeCross z.1 z.2 := hz.2.2
  have key := range_identity (m := m) (κ := κ) (r := planeLength z.1) (P := planeSq z.2)
    (d := planeDot z.1 z.2) (c := planeCross z.1 z.2) hm hr hcr
  rw [← hDe] at key
  have hA := actionMK_sq hm hκ hz
  have hA' : -2 * energyMK m κ z * actionMK m κ z ^ 2 = m ^ 3 * κ ^ 2 := by
    rw [hA]; exact mul_div_cancel₀ _ hD.ne'
  have hnn := actionMK_nonneg (z := z) (κ := κ) hm
  constructor
  · intro h
    have h2 : -2 * energyMK m κ z * planeCross z.1 z.2 ^ 2 = m ^ 3 * κ ^ 2 := by
      rw [h]; exact hA'
    have h3 : (m ^ 2 * κ - planeLength z.1 * planeSq z.2) ^ 2 / m +
        -2 * energyMK m κ z * planeDot z.1 z.2 ^ 2 = 0 := by linarith
    have t1 : 0 ≤ (m ^ 2 * κ - planeLength z.1 * planeSq z.2) ^ 2 / m := by positivity
    have t2 : 0 ≤ -2 * energyMK m κ z * planeDot z.1 z.2 ^ 2 := by positivity
    have e1 : (m ^ 2 * κ - planeLength z.1 * planeSq z.2) ^ 2 / m = 0 := by linarith
    have e2 : -2 * energyMK m κ z * planeDot z.1 z.2 ^ 2 = 0 := by linarith
    have hd : planeDot z.1 z.2 = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact absurd h hD.ne'
      · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    refine ⟨hd, ?_⟩
    have ht : m ^ 2 * κ = planeLength z.1 * planeSq z.2 := by
      have : (m ^ 2 * κ - planeLength z.1 * planeSq z.2) ^ 2 = 0 := by
        rcases div_eq_zero_iff.1 e1 with h | h
        · exact h
        · exact absurd h hm.ne'
      have := pow_eq_zero_iff (two_ne_zero) |>.1 this
      linarith
    rw [hax, hDe]
    have hP : planeSq z.2 = m ^ 2 * κ / planeLength z.1 := by
      field_simp; linarith
    rw [hP]
    field_simp
    ring
  · rintro ⟨hd, hrA⟩
    have hE0 : energyMK m κ z ≠ 0 := by
      intro h; rw [h] at hD; simp at hD
    have hrA' : planeLength z.1 * (-2 * energyMK m κ z) = κ * m := by
      rw [hax] at hrA
      rw [hrA]; field_simp
    have ht : m ^ 2 * κ = planeLength z.1 * planeSq z.2 := by
      rw [hDe] at hrA'
      field_simp at hrA'
      have : planeLength z.1 * planeSq z.2 = m ^ 2 * κ := by nlinarith
      linarith
    have h2 : -2 * energyMK m κ z * planeCross z.1 z.2 ^ 2 = m ^ 3 * κ ^ 2 := by
      rw [hd, ht] at key
      simp at key
      linarith
    have h3 : planeCross z.1 z.2 ^ 2 = actionMK m κ z ^ 2 := by
      have : -2 * energyMK m κ z * planeCross z.1 z.2 ^ 2 =
          -2 * energyMK m κ z * actionMK m κ z ^ 2 := by rw [h2, hA']
      exact mul_left_cancel₀ hD.ne' this
    exact (sq_eq_sq₀ hcpos.le hnn).1 h3

end Range

section Image

private theorem delaunay_image_eq : delaunay '' deDom = keplerRegion :=
  Set.Subset.antisymm (by rintro _ ⟨w, hw, rfl⟩; exact delaunay_mem_region hw)
    keplerRegion_subset_image

private theorem planeLength_scale_fst {m κ : ℝ} (hκ : 0 < κ) (y : Phase 2) :
    planeLength (scaleMK m κ y).1 = κ⁻¹ * planeLength y.1 := by
  simp only [scaleMK]
  rw [planeLength_smul, abs_of_pos (inv_pos.2 hκ)]

/-- `κ · a_{m,κ}(𝖲 y) = -1/(2E(y))` (the strength-one axis). -/
private theorem kappa_axis_scale {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (y : Phase 2) :
    κ * axisMK m κ (scaleMK m κ y) = -1 / (2 * kE y) := by
  unfold axisMK
  rw [scaleMK_energy hm hκ]
  by_cases h : kE y = 0
  · simp [h]
  · field_simp

private theorem actionMK_scale {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (y : Phase 2) :
    actionMK m κ (scaleMK m κ y) = m * √(-1 / (2 * kE y)) := by
  unfold actionMK
  rw [kappa_axis_scale hm hκ]

/-- `𝖲` carries `𝒞` onto `{z ∈ 𝒦_{m,κ} | C < Λ}`: pointwise equivalence. -/
private theorem scale_mem_iff {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (y : Phase 2) :
    (scaleMK m κ y ∈ regionMK m κ ∧
      planeCross (scaleMK m κ y).1 (scaleMK m κ y).2 < actionMK m κ (scaleMK m κ y)) ↔
      y ∈ keplerRegion := by
  have hlen := planeLength_scale_fst (m := m) hκ y
  have hE := scaleMK_energy hm hκ y
  have hC := scaleMK_cross hm hκ y
  have hact := actionMK_scale hm hκ y
  simp only [regionMK, keplerRegion, mem_ofPred_eq]
  rw [hlen, hE, hC, hact]
  have hmκ : 0 < m * κ ^ 2 := by positivity
  have h1 : 0 < κ⁻¹ * planeLength y.1 ↔ 0 < planeLength y.1 :=
    mul_pos_iff_of_pos_left (inv_pos.2 hκ)
  have h3 : 0 < m * planeCross y.1 y.2 ↔ 0 < planeCross y.1 y.2 := mul_pos_iff_of_pos_left hm
  have h2 : m * κ ^ 2 * kE y < 0 ↔ kE y < 0 := by
    constructor
    · intro h; by_contra h'; push Not at h'; nlinarith [mul_nonneg hmκ.le h']
    · intro h; nlinarith
  have h4 : kE y < 0 → planeCross y.1 y.2 > 0 →
      (m * planeCross y.1 y.2 < m * √(-1 / (2 * kE y)) ↔
        planeCross y.1 y.2 ^ 2 < -1 / (2 * kE y)) := by
    intro _ hc
    rw [mul_lt_mul_iff_right₀ hm]
    exact Real.lt_sqrt hc.le
  rw [h1, h2, h3]
  constructor
  · rintro ⟨⟨a1, a2, a3⟩, a4⟩
    exact ⟨a1, a2, a3, (h4 a2 a3).1 a4⟩
  · rintro ⟨a1, a2, a3, a4⟩
    exact ⟨⟨a1, a2, a3⟩, (h4 a2 a3).2 a4⟩

theorem delaunayMK_image {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    delaunayMK m κ '' deDom =
      {z | z ∈ regionMK m κ ∧ planeCross z.1 z.2 < actionMK m κ z} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hy : delaunay (momL m w) ∈ keplerRegion := delaunay_mem_region (momL_mem hm hw)
    exact (scale_mem_iff hm hκ _).2 hy
  · intro hz
    obtain ⟨y, hy, hyz⟩ : ∃ y, y ∈ keplerRegion ∧ scaleMK m κ y = z := by
      refine ⟨scaleInvL m κ z, ?_, scale_right_inv hm hκ z⟩
      refine (scale_mem_iff hm hκ _).1 ?_
      rw [scale_right_inv hm hκ z]
      exact hz
    obtain ⟨w', hw', rfl⟩ := keplerRegion_subset_image hy
    refine ⟨momInvL m w', momInvL_mem hm hw', ?_⟩
    have : momL m (momInvL m w') = w' := mom_right_inv hm w'
    unfold delaunayMK
    rw [← hyz]
    exact congrArg (fun x => scaleMK m κ (delaunay x)) this

end Image

section Identities

/-- Rescaling `(Λ, C) ↦ (Λ/m, C/m)` does not change the eccentricity. -/
private theorem eccOf_inv_mul {m : ℝ} (hm : 0 < m) (L G : ℝ) :
    eccOf (m⁻¹ * L) (m⁻¹ * G) = eccOf L G := by
  unfold eccOf
  congr 1
  field_simp

private theorem kE_delaunay {w : Phase 2} (hw : w ∈ deDom) :
    kE (delaunay w) = -1 / (2 * w.2 0 ^ 2) := by
  have h1 := delaunay_hamiltonian hw
  have h2 := (delaunay_elements hw).2.1
  rw [h2] at h1
  linarith

private theorem kE_delaunay_mom {m : ℝ} (hm : 0 < m) {w : Phase 2} (hw : w ∈ deDom) :
    kE (delaunay (momL m w)) = -m ^ 2 / (2 * w.2 0 ^ 2) := by
  have hΛ : 0 < w.2 0 := hw.1.trans hw.2
  rw [kE_delaunay (momL_mem hm hw)]
  simp only [momL_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- `bpP:p7:kepler` (b), (d): identities and `E ∘ 𝖰 = h_m(Λ) = -κ²m³/(2Λ²)`. -/
theorem delaunayMK_identities {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ deDom) :
    energyMK m κ (delaunayMK m κ w) = -(κ ^ 2 * m ^ 3) / (2 * w.2 0 ^ 2) ∧
    planeCross (delaunayMK m κ w).1 (delaunayMK m κ w).2 = w.2 1 ∧
    actionMK m κ (delaunayMK m κ w) = w.2 0 ∧
    axisMK m κ (delaunayMK m κ w) = w.2 0 ^ 2 / (m ^ 2 * κ) ∧
    planeLength (delaunayMK m κ w).1 =
      (w.2 0 ^ 2 / (m ^ 2 * κ)) * (1 - eccOf (w.2 0) (w.2 1) *
        Real.cos (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1)))) := by
  have hΛ : 0 < w.2 0 := hw.1.trans hw.2
  have hM := momL_mem hm hw
  have hE := kE_delaunay_mom hm hw
  have hC : planeCross (delaunay (momL m w)).1 (delaunay (momL m w)).2 = m⁻¹ * w.2 1 := by
    have := (delaunay_elements hM).2.1
    simpa [momL_apply] using this
  have hEn : energyMK m κ (delaunayMK m κ w) = -(κ ^ 2 * m ^ 3) / (2 * w.2 0 ^ 2) := by
    show energyMK m κ (scaleMK m κ (delaunay (momL m w))) = _
    rw [scaleMK_energy hm hκ, hE]
    field_simp
  refine ⟨hEn, ?_, ?_, ?_, ?_⟩
  · show planeCross (scaleMK m κ (delaunay (momL m w))).1 (scaleMK m κ (delaunay (momL m w))).2 = _
    rw [scaleMK_cross hm hκ, hC]
    field_simp
  · show actionMK m κ (scaleMK m κ (delaunay (momL m w))) = _
    rw [actionMK_scale hm hκ, hE]
    have : -1 / (2 * (-m ^ 2 / (2 * w.2 0 ^ 2))) = (w.2 0 / m) ^ 2 := by
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
    field_simp
  · unfold axisMK
    rw [hEn]
    field_simp
  · show planeLength (scaleMK m κ (delaunay (momL m w))).1 = _
    rw [planeLength_scale_fst hκ]
    have hL : 0 < m⁻¹ * w.2 0 := by positivity
    have hdeD : delaunay (momL m w) =
        orbitMapR (w.1 0) (w.1 1) (m⁻¹ * w.2 0) (eccOf (m⁻¹ * w.2 0) (m⁻¹ * w.2 1)) := by
      simp [delaunay, momL_apply]
    have he := eccOf_mem_Ioo (L := m⁻¹ * w.2 0) (G := m⁻¹ * w.2 1)
      (by simpa using mul_lt_mul_of_pos_left hw.2 (inv_pos.2 hm)) (mul_pos (inv_pos.2 hm) hw.1)
    rw [hdeD, orbitMapR_radius hL he.1.le he.2, eccOf_inv_mul hm]
    field_simp

private theorem rot_smul (g c : ℝ) (v : Fin 2 → ℝ) : rot g (c • v) = c • rot g v := by
  ext i; fin_cases i <;> simp [rot] <;> ring

theorem delaunayMK_position {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) {w : Phase 2}
    (hw : w ∈ deDom) :
    (delaunayMK m κ w).1 =
      (w.2 0 ^ 2 / (m ^ 2 * κ)) • rot (w.1 1)
        ![Real.cos (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1))) - eccOf (w.2 0) (w.2 1),
          √(1 - eccOf (w.2 0) (w.2 1) ^ 2) *
            Real.sin (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1)))] := by
  have hdeD : delaunay (momL m w) =
      orbitMapR (w.1 0) (w.1 1) (m⁻¹ * w.2 0) (eccOf (m⁻¹ * w.2 0) (m⁻¹ * w.2 1)) := by
    simp [delaunay, momL_apply]
  show (scaleMK m κ (delaunay (momL m w))).1 = _
  rw [hdeD, eccOf_inv_mul hm]
  simp only [scaleMK, orbitMapR, orbitFrame]
  have hv : (![(m⁻¹ * w.2 0) ^ 2 * (Real.cos (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1))) -
        eccOf (w.2 0) (w.2 1)),
      (m⁻¹ * w.2 0) ^ 2 * √(1 - eccOf (w.2 0) (w.2 1) ^ 2) *
        Real.sin (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1)))] : Fin 2 → ℝ) =
      (m⁻¹ * w.2 0) ^ 2 • ![Real.cos (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1))) -
        eccOf (w.2 0) (w.2 1), √(1 - eccOf (w.2 0) (w.2 1) ^ 2) *
          Real.sin (eccAnom (w.1 0) (eccOf (w.2 0) (w.2 1)))] := by
    ext i; fin_cases i <;> simp [mul_assoc]
  rw [hv, rot_smul, smul_smul]
  congr 1
  field_simp

theorem hasDerivAt_keplerEnergy_action {m κ Λ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hΛ : 0 < Λ) :
    HasDerivAt (fun x => -(κ ^ 2 * m ^ 3) / (2 * x ^ 2)) (κ ^ 2 * m ^ 3 / Λ ^ 3) Λ := by
  have h2 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * Λ)) Λ := by
    simpa using (hasDerivAt_pow 2 Λ).const_mul 2
  have h := (hasDerivAt_const Λ (-(κ ^ 2 * m ^ 3))).div h2 (by positivity)
  convert h using 1
  field_simp
  ring

/-- `bpP:p7:kepler` (c), including the circular endpoint `C = Λ` (`e = 0`). -/
theorem delaunayMK_means {m κ g Λ e : ℝ} (hm : 0 < m) (hκ : 0 < κ) (hΛ : 0 < Λ) (he0 : 0 ≤ e)
    (he1 : e < 1) :
    let a := Λ ^ 2 / (m ^ 2 * κ)
    let f := fun ℓ => scaleMK m κ (orbitMapR ℓ g (Λ / m) e)
    (2 * π)⁻¹ * (∫ ℓ in (0 : ℝ)..2 * π, 1 / planeLength (f ℓ).1) = 1 / a ∧
    (2 * π)⁻¹ * (∫ ℓ in (0 : ℝ)..2 * π, planeSq (f ℓ).2) = m ^ 2 * κ / a ∧
    (2 * π)⁻¹ * (∫ ℓ in (0 : ℝ)..2 * π, planeLength (f ℓ).1) = a * (1 + e ^ 2 / 2) := by
  intro a f
  have hL : 0 < Λ / m := by positivity
  have hpi : (2 * π)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ∀ ℓ, 1 / planeLength (f ℓ).1 = κ * (1 / planeLength (orbitMapR ℓ g (Λ / m) e).1) :=
      fun ℓ => by
        simp only [f, planeLength_scale_fst hκ]
        field_simp
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm _ κ, mul_assoc,
      orbitMapR_mean_inv_radius hL he0 he1]
    simp only [a]
    field_simp
  · have h1 : ∀ ℓ, planeSq (f ℓ).2 = (m * κ) ^ 2 * planeSq (orbitMapR ℓ g (Λ / m) e).2 :=
      fun ℓ => by simp only [f, scaleMK]; exact planeSq_smul _ _
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm _ ((m * κ) ^ 2), mul_assoc,
      orbitMapR_mean_speed_sq hL he0 he1]
    simp only [a]
    field_simp
  · have h1 : ∀ ℓ, planeLength (f ℓ).1 = κ⁻¹ * planeLength (orbitMapR ℓ g (Λ / m) e).1 :=
      fun ℓ => planeLength_scale_fst hκ _
    simp_rw [h1]
    rw [intervalIntegral.integral_const_mul, ← mul_assoc, mul_comm _ κ⁻¹, mul_assoc,
      orbitMapR_mean_radius hL he0 he1]
    simp only [a]
    field_simp

end Identities

section Scaling

/-- `bpI:p7:scaling`: the mass dictionary `E_{m,κ}(q, p) = m E_{1,κ}(q, p/m)`. -/
theorem energyMK_eq_mul_energy (m κ : ℝ) (hm : 0 < m) (z : Phase 2) :
    energyMK m κ z = m * energyMK 1 κ (z.1, m⁻¹ • z.2) := by
  unfold energyMK
  simp only [planeSq_smul]
  field_simp

/-- For `m = 1` the scaling is symplectic of factor one and carries `X_{H ∘ 𝖲}` to `X_H`. -/
theorem scaleMK_hamiltonianVectorField {κ : ℝ} (hκ : 0 < κ) {H : Phase 2 → ℝ} {z : Phase 2}
    (hH : DifferentiableAt ℝ H (scaleMK 1 κ z)) :
    (scaleMK 1 κ) (hamiltonianVectorField (H ∘ scaleMK 1 κ) z) =
      hamiltonianVectorField H (scaleMK 1 κ z) := by
  have hcomp : fderiv ℝ (H ∘ scaleMK 1 κ) z =
      (fderiv ℝ H (scaleMK 1 κ z)).comp (scaleL 1 κ) := by
    have e : scaleMK 1 κ = scaleL 1 κ := rfl
    rw [e] at hH ⊢
    rw [fderiv_comp z hH (scaleL 1 κ).differentiableAt, (scaleL 1 κ).fderiv]
  have h1 : ∀ i : Fin 2,
      scaleMK 1 κ (0, Pi.single i 1) = κ • ((0 : Fin 2 → ℝ), Pi.single i 1) := by
    intro i; ext j <;> simp [scaleMK]
  have h2 : ∀ i : Fin 2,
      scaleMK 1 κ (Pi.single i 1, 0) = κ⁻¹ • (Pi.single i 1, (0 : Fin 2 → ℝ)) := by
    intro i; ext j <;> simp [scaleMK]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [hamiltonianVectorField, hcomp, ContinuousLinearMap.comp_apply, scaleL_apply]
    simp only [h1, map_smul, smul_eq_mul]
    simp only [scaleMK, Pi.smul_apply, smul_eq_mul]
    field_simp
  · simp only [hamiltonianVectorField, hcomp, ContinuousLinearMap.comp_apply, scaleL_apply]
    simp only [h2, map_smul, smul_eq_mul]
    simp only [scaleMK, Pi.smul_apply, smul_eq_mul]
    field_simp

private theorem hamiltonianVectorField_const_mul {c : ℝ} {H : Phase 2 → ℝ} {z : Phase 2}
    (hH : DifferentiableAt ℝ H z) :
    hamiltonianVectorField (fun w => c * H w) z = c • hamiltonianVectorField H z := by
  have h := fderiv_const_mul hH c
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [hamiltonianVectorField, h]

/-- The strength-`κ` energy is `κ²` times the strength-one energy, in the scaled coordinates. -/
private theorem energyMK_one_eq {κ : ℝ} (hκ : 0 < κ) (z : Phase 2) :
    energyMK 1 κ z = κ ^ 2 * kE (scaleInvL 1 κ z) := by
  have h := scaleMK_energy one_pos hκ (scaleInvL 1 κ z)
  rw [scale_right_inv one_pos hκ] at h
  rw [h]; ring

/-- `bpI:p7:scaling`, flow clause: if `Z` solves the strength-one Hamilton equations at
`τ = κ² t`, then `t ↦ 𝖲_κ(Z(κ² t))` solves those of `E_κ` (time change by `κ²`). -/
theorem scaleMK_flow {κ : ℝ} (hκ : 0 < κ) {Zc : ℝ → Phase 2} {t : ℝ}
    (hZ : HasDerivAt Zc (hamiltonianVectorField kE (Zc (κ ^ 2 * t))) (κ ^ 2 * t))
    (hE : DifferentiableAt ℝ kE (Zc (κ ^ 2 * t))) :
    HasDerivAt (fun s => scaleMK 1 κ (Zc (κ ^ 2 * s)))
      (hamiltonianVectorField (energyMK 1 κ) (scaleMK 1 κ (Zc (κ ^ 2 * t)))) t := by
  set y := Zc (κ ^ 2 * t) with hy
  have h1 : HasDerivAt (fun s => Zc (κ ^ 2 * s)) (κ ^ 2 • hamiltonianVectorField kE y) t :=
    HasDerivAt.scomp (g₁ := Zc) (h := fun s => κ ^ 2 * s) t hZ
      (by simpa using (hasDerivAt_id t).const_mul (κ ^ 2))
  have h2 : HasDerivAt (fun s => scaleL 1 κ (Zc (κ ^ 2 * s)))
      (scaleL 1 κ (κ ^ 2 • hamiltonianVectorField kE y)) t :=
    (scaleL 1 κ).hasFDerivAt.comp_hasDerivAt t h1
  have hdiff : DifferentiableAt ℝ (energyMK 1 κ) (scaleMK 1 κ y) := by
    have hfun : energyMK 1 κ = fun z => κ ^ 2 * kE (scaleInvL 1 κ z) :=
      funext (energyMK_one_eq hκ)
    rw [hfun]
    have hE' : DifferentiableAt ℝ kE (scaleInvL 1 κ (scaleMK 1 κ y)) := by
      rw [scale_left_inv one_pos hκ]; exact hE
    exact (hE'.comp _ (scaleInvL 1 κ).differentiableAt).const_mul _
  have key := scaleMK_hamiltonianVectorField hκ hdiff
  have hcomp : energyMK 1 κ ∘ scaleMK 1 κ = fun w => κ ^ 2 * kE w := by
    funext w; simp only [Function.comp_apply, scaleMK_energy one_pos hκ w, one_mul]
  rw [hcomp, hamiltonianVectorField_const_mul hE] at key
  have e : (fun s => scaleMK 1 κ (Zc (κ ^ 2 * s))) = fun s => scaleL 1 κ (Zc (κ ^ 2 * s)) := rfl
  rw [e, ← key]
  exact h2

end Scaling

end KAM.Kepler

end
