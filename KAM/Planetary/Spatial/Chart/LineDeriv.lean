/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Spatial.Chart.Defs
public import KAM.Planetary.Spatial.Chart.RotAlgebra

/-!
# The spatial chart: derivative of the rotation along a line

Source: `LP:MAIN L17 (562–569)`, track LP, non-frozen. Along the line
`τ ↦ w + τ • h` the rotation `spatialRot` has entries `rot3 a b c` with `a = u/(2√G)`,
`b = −v/(2√G)`, `c = incCos u v G`; this module computes their derivatives at `τ = 0`
(`spatialRot_line_hasDerivAt`) and the algebraic relations between the resulting numbers
(used by `rot3_form_identity` in the symplecticity proof).

-/

@[expose] public noncomputable section

open Matrix Filter Topology

namespace KAM.Planetary.Spatial

open KAM KAM.Kepler KAM.Planetary

/-- A function along a line has the line derivative of `fderiv`. -/
theorem hasDerivAt_fderiv_spatialLine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {w : E} (hf : DifferentiableAt ℝ f w)
    (h : E) : HasDerivAt (fun τ : ℝ => f (w + τ • h)) (fderiv ℝ f w h) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => w + τ • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add w
  have hf' : HasFDerivAt f (fderiv ℝ f w) (w + (0 : ℝ) • h) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl

theorem hasDerivAt_affine (x d : ℝ) : HasDerivAt (fun τ : ℝ => x + τ * d) d 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add x

/-- Derivative of the entries of `rot3` along a curve. -/
theorem rot3_hasDerivAt {a b c : ℝ → ℝ} {da db dc : ℝ} {x : ℝ}
    (ha : HasDerivAt a da x) (hb : HasDerivAt b db x) (hc : HasDerivAt c dc x) (i j : Fin 3) :
    HasDerivAt (fun τ => rot3 (a τ) (b τ) (c τ) i j)
      (rot3Deriv (a x) (b x) (c x) da db dc i j) x := by
  fin_cases i <;> fin_cases j <;> simp only [rot3, rot3Deriv] <;> simp
  · exact (((hb.mul hb).const_mul 2).const_sub 1).congr_deriv (by ring) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.mul_apply]; ring)
  · exact ((ha.const_mul 2).mul hb).congr_deriv (by ring)
  · exact ((hc.const_mul 2).mul hb).congr_deriv (by ring)
  · exact ((ha.const_mul 2).mul hb).congr_deriv (by ring)
  · exact (((ha.mul ha).const_mul 2).const_sub 1).congr_deriv (by ring) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.mul_apply]; ring)
  · exact ((hc.const_mul 2).mul ha).neg.congr_deriv (by ring)
  · exact ((hc.const_mul 2).mul hb).neg.congr_deriv (by ring)
  · exact ((hc.const_mul 2).mul ha).congr_deriv (by ring)
  · exact ((((ha.mul ha).add (hb.mul hb)).const_mul 2).const_sub 1).congr_deriv (by ring)
      |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun τ => by simp only [Pi.mul_apply, Pi.add_apply]; ring)

section Line

/-- `s = √G` at the chart point. -/
def spatialS (w : Phase 3) : ℝ := Real.sqrt (spatialAngMom w)

/-- `a = u/(2s)`, the first component of the tilt `t` of (46). -/
def spatialA (w : Phase 3) : ℝ := w.2 2 / (2 * spatialS w)

/-- `b = −v/(2s)`, the second component of the tilt `t` of (46). -/
def spatialB (w : Phase 3) : ℝ := -w.1 2 / (2 * spatialS w)

/-- `c = √(1 − |t|²)`. -/
def spatialC (w : Phase 3) : ℝ := incCos (w.2 2) (w.1 2) (spatialAngMom w)

/-- `dG` along the direction `h`. -/
def spatialDG (w h : Phase 3) : ℝ := h.2 0 - (w.1 1 * h.1 1 + w.2 1 * h.2 1)

/-- `ds` along the direction `h`. -/
def spatialDS (w h : Phase 3) : ℝ := spatialDG w h / (2 * spatialS w)

/-- `da` along the direction `h`. -/
def spatialDA (w h : Phase 3) : ℝ :=
  (h.2 2 * (2 * spatialS w) - w.2 2 * (2 * spatialDS w h)) / (2 * spatialS w) ^ 2

/-- `db` along the direction `h`. -/
def spatialDB (w h : Phase 3) : ℝ :=
  (-h.1 2 * (2 * spatialS w) - -w.1 2 * (2 * spatialDS w h)) / (2 * spatialS w) ^ 2

/-- `dc` along the direction `h`. -/
def spatialDC (w h : Phase 3) : ℝ :=
  -(2 * spatialA w * spatialDA w h + 2 * spatialB w * spatialDB w h) / (2 * spatialC w)

variable {w : Phase 3}

lemma spatialS_pos (hw : w ∈ spatialPoincareDom) : 0 < spatialS w :=
  Real.sqrt_pos.2 (spatialAngMom_pos hw)

lemma spatialS_sq (hw : w ∈ spatialPoincareDom) : spatialS w ^ 2 = spatialAngMom w :=
  Real.sq_sqrt (spatialAngMom_pos hw).le

lemma spatialRot_eq_rot3 (w : Phase 3) :
    spatialRot w = rot3 (spatialA w) (spatialB w) (spatialC w) := by
  unfold spatialRot
  rw [incRotation_eq_rot3, incTilt_apply_zero, incTilt_apply_one]
  rfl

lemma incCos_eq_sqrt_ab (u v G : ℝ) :
    incCos u v G = Real.sqrt (1 - (u / (2 * Real.sqrt G) * (u / (2 * Real.sqrt G)) +
      -v / (2 * Real.sqrt G) * (-v / (2 * Real.sqrt G)))) := by
  unfold incCos
  simp [dotProduct, Fin.sum_univ_three, incTilt_apply_zero, incTilt_apply_one, incTilt_apply_two]

lemma spatialC_sq (hw : w ∈ spatialPoincareDom) :
    spatialC w ^ 2 + spatialA w ^ 2 + spatialB w ^ 2 = 1 := by
  have hc := spatial_carrier hw
  have h := incCos_sq hc.1 hc.2
  have hdot : incTilt (w.2 2) (w.1 2) (spatialAngMom w) ⬝ᵥ
      incTilt (w.2 2) (w.1 2) (spatialAngMom w) = spatialA w ^ 2 + spatialB w ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three, incTilt_apply_zero, incTilt_apply_one,
      incTilt_apply_two, spatialA, spatialB, spatialS]
    ring
  unfold spatialC
  rw [h, hdot]; ring

lemma spatialC_pos (hw : w ∈ spatialPoincareDom) : 0 < spatialC w :=
  incCos_pos (spatial_carrier hw).1 (spatial_carrier hw).2

lemma spatial_rel_d (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    spatialA w * spatialDA w h + spatialB w * spatialDB w h + spatialC w * spatialDC w h = 0 := by
  have := (spatialC_pos hw).ne'
  unfold spatialDC
  field_simp
  ring

lemma spatial_rel_u (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    h.2 2 = 2 * spatialS w * spatialDA w h + 2 * spatialA w * spatialDS w h := by
  have := (spatialS_pos hw).ne'
  unfold spatialDA spatialA
  field_simp
  ring

lemma spatial_rel_v (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    h.1 2 = -(2 * spatialS w * spatialDB w h) - 2 * spatialB w * spatialDS w h := by
  have := (spatialS_pos hw).ne'
  unfold spatialDB spatialB
  field_simp
  ring

lemma spatial_rel_G (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    spatialDG w h = 2 * spatialS w * spatialDS w h := by
  have := (spatialS_pos hw).ne'
  unfold spatialDS
  field_simp

lemma hasDerivAt_line_angMom (w h : Phase 3) :
    HasDerivAt (fun τ : ℝ => spatialAngMom (w + τ • h)) (spatialDG w h) 0 := by
  have h0 := hasDerivAt_affine (w.2 0) (h.2 0)
  have h1 := hasDerivAt_affine (w.1 1) (h.1 1)
  have h2 := hasDerivAt_affine (w.2 1) (h.2 1)
  have := h0.sub (((h1.pow 2).add (h2.pow 2)).div_const 2)
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
  · unfold spatialDG; simp; ring
  · simp [spatialAngMom, spatialGamma]

lemma hasDerivAt_line_S (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    HasDerivAt (fun τ : ℝ => Real.sqrt (spatialAngMom (w + τ • h))) (spatialDS w h) 0 := by
  have := (hasDerivAt_line_angMom w h).sqrt (by simpa using (spatialAngMom_pos hw).ne')
  simpa [spatialDS, spatialS] using this

lemma hasDerivAt_line_u (w h : Phase 3) :
    HasDerivAt (fun τ : ℝ => (w + τ • h).2 2) (h.2 2) 0 :=
  (hasDerivAt_affine (w.2 2) (h.2 2)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ => by simp)

lemma hasDerivAt_line_v (w h : Phase 3) :
    HasDerivAt (fun τ : ℝ => (w + τ • h).1 2) (h.1 2) 0 :=
  (hasDerivAt_affine (w.1 2) (h.1 2)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ => by simp)

lemma hasDerivAt_line_A (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    HasDerivAt (fun τ : ℝ => (w + τ • h).2 2 / (2 * Real.sqrt (spatialAngMom (w + τ • h))))
      (spatialDA w h) 0 := by
  have hs := (hasDerivAt_line_S hw h).const_mul 2
  have hne : 2 * Real.sqrt (spatialAngMom (w + (0 : ℝ) • h)) ≠ 0 := by
    simpa [spatialS] using (spatialS_pos hw).ne'
  have := (hasDerivAt_line_u w h).div hs hne
  convert this using 1
  simp [spatialDA, spatialS]

lemma hasDerivAt_line_B (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    HasDerivAt (fun τ : ℝ => -(w + τ • h).1 2 / (2 * Real.sqrt (spatialAngMom (w + τ • h))))
      (spatialDB w h) 0 := by
  have hs := (hasDerivAt_line_S hw h).const_mul 2
  have hne : 2 * Real.sqrt (spatialAngMom (w + (0 : ℝ) • h)) ≠ 0 := by
    simpa [spatialS] using (spatialS_pos hw).ne'
  have := (hasDerivAt_line_v w h).neg.div hs hne
  convert this using 1
  simp [spatialDB, spatialS]

lemma hasDerivAt_line_C (hw : w ∈ spatialPoincareDom) (h : Phase 3) :
    HasDerivAt (fun τ : ℝ => incCos ((w + τ • h).2 2) ((w + τ • h).1 2)
      (spatialAngMom (w + τ • h))) (spatialDC w h) 0 := by
  have hA := hasDerivAt_line_A hw h
  have hB := hasDerivAt_line_B hw h
  have hf := (((hA.mul hA).add (hB.mul hB)).const_sub 1)
  have hc := spatialC_sq hw
  have hcpos := spatialC_pos hw
  have hA0 : w.2 2 / (2 * Real.sqrt (spatialAngMom w)) = spatialA w := rfl
  have hB0 : -w.1 2 / (2 * Real.sqrt (spatialAngMom w)) = spatialB w := rfl
  have hC0 : Real.sqrt (1 - (spatialA w * spatialA w + spatialB w * spatialB w)) =
      spatialC w := by
    simp [spatialA, spatialB, spatialS, spatialC, incCos_eq_sqrt_ab]
  have hne : (1 - (spatialA w * spatialA w + spatialB w * spatialB w)) ≠ 0 := by
    have : 1 - (spatialA w * spatialA w + spatialB w * spatialB w) = spatialC w ^ 2 := by
      nlinarith
    rw [this]; positivity
  have key := hf.sqrt (by
    simpa only [Pi.mul_apply, Pi.add_apply, hA0, hB0, zero_smul, add_zero] using hne)
  refine (key.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun τ => incCos_eq_sqrt_ab _ _ _)
  simp only [Pi.mul_apply, Pi.add_apply, hA0, hB0, zero_smul, add_zero]
  rw [hC0]
  unfold spatialDC
  ring

lemma spatialRot_line_eq (w h : Phase 3) (τ : ℝ) :
    spatialRot (w + τ • h) =
      rot3 ((w + τ • h).2 2 / (2 * Real.sqrt (spatialAngMom (w + τ • h))))
        (-(w + τ • h).1 2 / (2 * Real.sqrt (spatialAngMom (w + τ • h))))
        (incCos ((w + τ • h).2 2) ((w + τ • h).1 2) (spatialAngMom (w + τ • h))) :=
  spatialRot_eq_rot3 (w + τ • h)

/-- The entries of `spatialRot` along the line `w + τ h` and their derivatives. -/
theorem spatialRot_line_hasDerivAt (hw : w ∈ spatialPoincareDom) (h : Phase 3) (i j : Fin 3) :
    HasDerivAt (fun τ : ℝ => spatialRot (w + τ • h) i j)
      (rot3Deriv (spatialA w) (spatialB w) (spatialC w) (spatialDA w h) (spatialDB w h)
        (spatialDC w h) i j) 0 := by
  have := rot3_hasDerivAt (hasDerivAt_line_A hw h) (hasDerivAt_line_B hw h)
    (hasDerivAt_line_C hw h) i j
  have hA0 : (w + (0 : ℝ) • h).2 2 / (2 * Real.sqrt (spatialAngMom (w + (0 : ℝ) • h))) =
      spatialA w := by simp [spatialA, spatialS]
  have hB0 : -(w + (0 : ℝ) • h).1 2 / (2 * Real.sqrt (spatialAngMom (w + (0 : ℝ) • h))) =
      spatialB w := by simp [spatialB, spatialS]
  have hC0 : incCos ((w + (0 : ℝ) • h).2 2) ((w + (0 : ℝ) • h).1 2)
      (spatialAngMom (w + (0 : ℝ) • h)) = spatialC w := by simp [spatialC]
  simp only [hA0, hB0, hC0] at this
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => ?_)
  simp only [spatialRot_line_eq]

end Line

end KAM.Planetary.Spatial
