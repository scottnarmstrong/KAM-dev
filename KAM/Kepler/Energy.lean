/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Basic
public import KAM.Kepler.Plane

/-!
# Kepler energy and regions

The strength-one energy `kE`, the Delaunay domain `deDom`, the prograde bound region `keplerRegion`
with its elements, and the mass/strength-scaled versions `scaleMK`, `energyMK`, `axisMK`,
`actionMK`, `regionMK`, together with openness and scaling lemmas.
-/

@[expose] public noncomputable section

open Set Metric Real
open scoped ContDiff

namespace KAM.Kepler

open KAM KAM.Planetary

/-- Eccentricity `e(L, G) = √(1 - G²/L²)`. -/
def eccOf (L G : ℝ) : ℝ := √(1 - G ^ 2 / L ^ 2)

/-- Strength-one Kepler energy `E(q, p) = ½|p|² - 1/|q|`, `z = (q, p)`. -/
def kE (z : Phase 2) : ℝ := planeSq z.2 / 2 - 1 / planeLength z.1

/-- Domain of the Delaunay variables: `w = ((ℓ, g), (L, G))` with `0 < G < L`. -/
def deDom : Set (Phase 2) := {w | 0 < w.2 1 ∧ w.2 1 < w.2 0}

/-- Bound prograde non-circular region `𝒞` (`bpI:p7:elements`). -/
def keplerRegion : Set (Phase 2) :=
  {z | 0 < planeLength z.1 ∧ kE z < 0 ∧ 0 < planeCross z.1 z.2 ∧
    planeCross z.1 z.2 ^ 2 < -1 / (2 * kE z)}
/-- Elements on `𝒞`: `L = 1/√(-2E)`, `G = cr`, `a = L²`, `e = √(1 + 2 E cr²)`. -/
def elemL (z : Phase 2) : ℝ := 1 / √(-2 * kE z)
def elemA (z : Phase 2) : ℝ := 1 / (-2 * kE z)
def elemEcc (z : Phase 2) : ℝ := √(1 + 2 * kE z * planeCross z.1 z.2 ^ 2)

/-- `𝖲_{m,κ}(Q, P) = (Q/κ, mκ P)` (for `m = 1` this is `𝖲_κ` of `bpI:p7:scaling`). -/
def scaleMK (m κ : ℝ) (z : Phase 2) : Phase 2 := (κ⁻¹ • z.1, (m * κ) • z.2)
/-- `E_{m,κ}(q, p) = |p|²/(2m) - κ m/|q|` (the frozen `keplerEnergy` at `κ = 1`). -/
def energyMK (m κ : ℝ) (z : Phase 2) : ℝ := planeSq z.2 / (2 * m) - κ * m / planeLength z.1
def axisMK (m κ : ℝ) (z : Phase 2) : ℝ := -(κ * m) / (2 * energyMK m κ z)
def actionMK (m κ : ℝ) (z : Phase 2) : ℝ := m * √(κ * axisMK m κ z)
/-- `𝒦_{m,κ}`: prograde bound region (`q ≠ 0`, `E < 0`, `cr > 0`). -/
def regionMK (m κ : ℝ) : Set (Phase 2) :=
  {z | 0 < planeLength z.1 ∧ energyMK m κ z < 0 ∧ 0 < planeCross z.1 z.2}

private theorem continuous_planeSq : Continuous planeSq := by
  have : planeSq = fun w : Fin 2 → ℝ => ∑ k, w k ^ 2 := rfl
  rw [this]; fun_prop

private theorem continuous_planeLength : Continuous planeLength :=
  Real.continuous_sqrt.comp continuous_planeSq

private theorem continuous_planeCross : Continuous (fun z : Phase 2 => planeCross z.1 z.2) := by
  unfold planeCross; fun_prop

private theorem isOpen_pos_length : IsOpen {z : Phase 2 | 0 < planeLength z.1} :=
  isOpen_lt continuous_const (continuous_planeLength.comp continuous_fst)

private theorem continuousOn_kE : ContinuousOn kE {z : Phase 2 | 0 < planeLength z.1} := by
  unfold kE
  refine ContinuousOn.sub ?_ ?_
  · exact ((continuous_planeSq.comp continuous_snd).div_const 2).continuousOn
  · refine ContinuousOn.div continuousOn_const
      (continuous_planeLength.comp continuous_fst).continuousOn ?_
    intro z hz; exact hz.ne'

theorem isOpen_keplerRegion : IsOpen keplerRegion := by
  have hF : ContinuousOn
      (fun z : Phase 2 => (kE z, planeCross z.1 z.2, 1 + 2 * kE z * planeCross z.1 z.2 ^ 2))
      {z : Phase 2 | 0 < planeLength z.1} :=
    continuousOn_kE.prodMk (continuous_planeCross.continuousOn.prodMk
      ((continuousOn_const.add ((continuousOn_const.mul continuousOn_kE).mul
        (continuous_planeCross.pow 2).continuousOn))))
  have hT : IsOpen (Iio (0 : ℝ) ×ˢ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    isOpen_Iio.prod (isOpen_Ioi.prod isOpen_Ioi)
  have := hF.isOpen_inter_preimage isOpen_pos_length hT
  convert this using 1
  ext z
  simp only [keplerRegion, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_prod, mem_Iio, mem_Ioi]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [lt_div_iff_of_neg (by linarith)] at h4
    nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, h3, ?_⟩
    rw [lt_div_iff_of_neg (by linarith)]
    nlinarith

theorem isOpen_deDom : IsOpen deDom := by
  have h1 : Continuous (fun w : Phase 2 => w.2 1) := (continuous_apply 1).comp continuous_snd
  have h0 : Continuous (fun w : Phase 2 => w.2 0) := (continuous_apply 0).comp continuous_snd
  exact (isOpen_lt continuous_const h1).inter (isOpen_lt h1 h0)

theorem isOpen_regionMK {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) : IsOpen (regionMK m κ) := by
  have hE : ContinuousOn (fun z : Phase 2 => energyMK m κ z)
      {z : Phase 2 | 0 < planeLength z.1} := by
    unfold energyMK
    refine ContinuousOn.sub ?_ ?_
    · exact ((continuous_planeSq.comp continuous_snd).div_const _).continuousOn
    · refine ContinuousOn.div continuousOn_const
        (continuous_planeLength.comp continuous_fst).continuousOn ?_
      intro z hz; exact hz.ne'
  have hF : ContinuousOn (fun z : Phase 2 => (energyMK m κ z, planeCross z.1 z.2))
      {z : Phase 2 | 0 < planeLength z.1} := hE.prodMk continuous_planeCross.continuousOn
  have hT : IsOpen (Iio (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Iio.prod isOpen_Ioi
  have := hF.isOpen_inter_preimage isOpen_pos_length hT
  convert this using 1
  ext z
  simp [regionMK]

theorem planeSq_smul (c : ℝ) (v : Fin 2 → ℝ) : planeSq (c • v) = c ^ 2 * planeSq v := by
  simp [planeSq, mul_pow]
  ring

theorem scaleMK_energy {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (z : Phase 2) :
    energyMK m κ (scaleMK m κ z) = m * κ ^ 2 * kE z := by
  unfold energyMK scaleMK kE
  simp only [planeSq_smul, planeLength_smul, abs_inv, abs_of_pos hκ]
  have : 0 < planeLength z.1 ∨ planeLength z.1 = 0 := (planeLength_nonneg _).lt_or_eq.imp id Eq.symm
  rcases this with h | h
  · field_simp
  · simp [h]
    field_simp

theorem scaleMK_cross {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) (z : Phase 2) :
    planeCross (scaleMK m κ z).1 (scaleMK m κ z).2 = m * planeCross z.1 z.2 := by
  unfold planeCross scaleMK
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

private def scaleCLM (m κ : ℝ) : Phase 2 →L[ℝ] Phase 2 :=
  (κ⁻¹ • ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).prod
    ((m * κ) • ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 2 → ℝ))

private theorem scaleMK_eq_clm (m κ : ℝ) : scaleMK m κ = scaleCLM m κ := rfl

theorem scaleMK_symplectic {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    IsSymplecticOn m (scaleMK m κ) univ := by
  intro z _ u v
  rw [scaleMK_eq_clm, ContinuousLinearMap.fderiv]
  simp only [symplecticForm, scaleCLM, Finset.mul_sum, ContinuousLinearMap.prod_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem scaleMK_bijective {m κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    Function.Bijective (scaleMK m κ) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun z => (κ • z.1, (m * κ)⁻¹ • z.2), ?_, ?_⟩
  · intro z
    simp only [scaleMK, smul_smul, inv_mul_cancel₀ (mul_pos hm hκ).ne', mul_inv_cancel₀ hκ.ne',
      one_smul]
  · intro z
    simp only [scaleMK, smul_smul, mul_inv_cancel₀ (mul_pos hm hκ).ne', inv_mul_cancel₀ hκ.ne',
      one_smul]

end KAM.Kepler

end
