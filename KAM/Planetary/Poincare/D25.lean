/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Equation
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.EllipsePhase
public import KAM.Frozen.Planetary.Defs.EllipsePosition
public import KAM.Frozen.Planetary.Defs.EllipseMomentum
public import KAM.Frozen.Planetary.Defs.SecularAxis
public import KAM.Frozen.Planetary.Defs.SecularRoot
public import KAM.Frozen.Planetary.Defs.SecularGamma
public import KAM.Frozen.Planetary.Defs.SecularEccVector
public import KAM.Frozen.Planetary.Defs.LongitudeJacobian
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import KAM.Frozen.Planetary.Defs.KeplerEnergy
public import KAM.Frozen.Planetary.Defs.KeplerAxis
public import KAM.Frozen.Planetary.Defs.KeplerAction
public import KAM.Frozen.Planetary.Defs.KeplerEccVector
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Frozen.Planetary.Defs.ProgradeElliptic

/-!
# The D25 dictionary and the angular averages

Blueprint P, Part 7 (`bpP:p7:d25`, `bpP:p7:average`).  The frozen secular definitions
(`secularGamma`, `secularRoot`, `secularEccVector`, `secularAxis`, `ellipsePhase`) are, by
unfolding, the chart quantities `Γ, k, v` of `poincare` on each planet block; the frozen
`ellipsePhase` at `F_j = Φ(v_j, ·)`-preimages is the product chart.  The change of variable
`λ_i ↔ F_i` in angular averages is `intervalIntegral.integral_comp_mul_deriv'` with
`f = keplerPhi v_i`, `f' = keplerJac v_i`, followed by a periodic shift of the window; the three
mean values reduce blockwise to `poincare_means`.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM KAM.Kepler

section D25

/-! ### Block calculus -/

theorem planetBlock_assemble {n : ℕ} (I phi p q : Fin n → ℝ) (j : Fin n) :
    planetBlock (assemble I phi p q : Phase (n + n)) j = (![phi j, q j], ![I j, p j]) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [planetBlock, assemble, fast, slow, Fin.append_left]

/-- `bpP:p7:d25` (a): the frozen secular definitions are the chart's `Γ, k, v` (all `w`, no domain needed). -/
theorem secularGamma_eq (w : Phase (2 + 2)) (i : Fin 2) :
    secularGamma w i = poincareGamma (planetBlock w i) := by
  simp only [secularGamma, oscillatorAction, poincareGamma, planetBlock]
  show _ = ((slow w.1 i) ^ 2 + (slow w.2 i) ^ 2) / 2
  ring

theorem secularRoot_eq (w : Phase (2 + 2)) (i : Fin 2) :
    secularRoot w i = poincareK (planetBlock w i) := by
  simp only [secularRoot, poincareK, secularGamma_eq]
  rfl

theorem secularEccVector_eq (w : Phase (2 + 2)) (i : Fin 2) :
    secularEccVector w i = poincareV (planetBlock w i) := by
  simp only [secularEccVector, poincareV, secularGamma_eq]
  rfl

theorem secularAxis_eq (m : Fin 2 → ℝ) (w : Phase (2 + 2)) (i : Fin 2) :
    secularAxis m w i = fast w.2 i ^ 2 / (m i ^ 2 * 1) := by
  simp [secularAxis, div_pow]

/-- The chart on a block whose coordinates match those of `w` except for the angle. -/
theorem poincare_block_eq_ellipse (m : Fin 2 → ℝ) (w : Phase (2 + 2)) (i : Fin 2) (P : Phase 2)
    (F : ℝ) (h1 : P.1 1 = slow w.1 i) (h2 : P.2 = ![fast w.2 i, slow w.2 i])
    (hF : poincareF P = F) :
    poincare (m i) 1 P = (ellipsePosition m w i F, ellipseMomentum m w i F) := by
  have h20 : P.2 0 = fast w.2 i := by rw [h2]; rfl
  have h21 : P.2 1 = slow w.2 i := by rw [h2]; rfl
  have hΓ : poincareGamma P = secularGamma w i := by
    simp only [poincareGamma, secularGamma, oscillatorAction, h1, h21]; ring
  have hK : poincareK P = secularRoot w i := by
    simp only [poincareK, secularRoot, hΓ, h20]
  have hV : poincareV P = secularEccVector w i := by
    simp only [poincareV, secularEccVector, hΓ, h20, h1, h21]
  have hJ : keplerJac (secularEccVector w i) F = longitudeJacobian w i F := rfl
  unfold poincare ellipsePosition ellipseMomentum
  dsimp only
  rw [hF, hK, hV, h20, secularAxis_eq, hJ]
  simp only [mul_one]

theorem ellipsePhase_eq_poincareProd {m : Fin 2 → ℝ} (hm : ∀ i, 0 < m i) {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2) (F : Fin 2 → ℝ) :
    ellipsePhase m w F =
      poincareProd m 1 (assemble (fast w.2)
        (fun j => keplerPhi (poincareV (planetBlock w j)) (F j)) (slow w.2) (slow w.1)) := by
  have hb : ∀ j, poincare (m j) 1 (planetBlock (assemble (fast w.2)
        (fun j => keplerPhi (poincareV (planetBlock w j)) (F j)) (slow w.2) (slow w.1)
        : Phase (2 + 2)) j) = (ellipsePosition m w j (F j), ellipseMomentum m w j (F j)) := by
    intro j
    have hv : planeLength (poincareV (planetBlock w j)) < 1 := (poincare_facts (hw j)).2.2.2.2.2.1
    refine poincare_block_eq_ellipse m w j _ (F j) ?_ ?_ ?_
    · rw [planetBlock_assemble]; rfl
    · rw [planetBlock_assemble]
    · have hV : poincareV (planetBlock (assemble (fast w.2)
          (fun j => keplerPhi (poincareV (planetBlock w j)) (F j)) (slow w.2) (slow w.1)
          : Phase (2 + 2)) j) = poincareV (planetBlock w j) := by
        rw [planetBlock_assemble]; rfl
      unfold poincareF
      rw [hV, planetBlock_assemble]
      exact keplerLong_unique hv rfl
  rw [poincareProd_eq_ofPlanets]
  simp only [hb]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · simp [ofPlanets, ofBodies, ellipsePhase]
  · simp [ofPlanets, ofBodies, ellipsePhase]

theorem ellipsePhase_eq_poincareProd_self {m : Fin 2 → ℝ} (hm : ∀ i, 0 < m i) {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2) :
    ellipsePhase m w (fun j => poincareF (planetBlock w j)) = poincareProd m 1 w := by
  rw [poincareProd_eq_ofPlanets]
  have hb : ∀ j, poincare (m j) 1 (planetBlock w j) =
      (ellipsePosition m w j (poincareF (planetBlock w j)),
        ellipseMomentum m w j (poincareF (planetBlock w j))) := fun j =>
    poincare_block_eq_ellipse m w j _ _ rfl rfl rfl
  simp only [hb]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · simp [ofPlanets, ofBodies, ellipsePhase]
  · simp [ofPlanets, ofBodies, ellipsePhase]

/-- (d): the Kepler functions of the physical point. -/
theorem keplerFunctions_poincareProd {m : Fin 2 → ℝ} (hm : ∀ i, 0 < m i) {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2) (i : Fin 2) :
    ProgradeElliptic m (poincareProd m 1 w) ∧
    keplerEnergy m (poincareProd m 1 w) i = -(m i) ^ 3 / (2 * fast w.2 i ^ 2) ∧
    keplerAxis m (poincareProd m 1 w) i = secularAxis m w i ∧
    keplerAction m (poincareProd m 1 w) i = fast w.2 i ∧
    planeCross (bodyVector (poincareProd m 1 w).1 i) (bodyVector (poincareProd m 1 w).2 i) =
      fast w.2 i - secularGamma w i ∧
    keplerEccVector m (poincareProd m 1 w) i = secularEccVector w i := by
  have hb := poincareProd_block m 1 w i
  have hq : bodyVector (poincareProd m 1 w).1 i = (poincare (m i) 1 (planetBlock w i)).1 := by
    rw [← hb]
  have hp : bodyVector (poincareProd m 1 w).2 i = (poincare (m i) 1 (planetBlock w i)).2 := by
    rw [← hb]
  obtain ⟨-, hE, hA, hAct, hCr, hLRL⟩ := poincare_elements (hm i) one_pos (hw i)
  have hPE : ProgradeElliptic m (poincareProd m 1 w) :=
    (regionProd_one_iff hm _).1 (poincareProd_mem_regionProd hm one_pos hw)
  have hEn : keplerEnergy m (poincareProd m 1 w) i =
      energyMK (m i) 1 (poincare (m i) 1 (planetBlock w i)) := by
    simp only [keplerEnergy, energyMK, hq, hp, one_mul]
  have hAx : keplerAxis m (poincareProd m 1 w) i =
      axisMK (m i) 1 (poincare (m i) 1 (planetBlock w i)) := by
    simp only [keplerAxis, axisMK, hEn, one_mul]
  refine ⟨hPE, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEn, hE]
    simp only [one_pow, one_mul]
    rfl
  · rw [hAx, hA, secularAxis_eq]
    rfl
  · have h := hAct
    unfold actionMK at h
    unfold keplerAction
    rw [hAx]
    simp only [one_mul] at h
    exact h
  · rw [hq, hp, secularGamma_eq]
    exact hCr
  · rw [secularEccVector_eq, ← hLRL]
    simp only [keplerEccVector, hq, hp, inv_one, one_smul]

theorem exists_poincareProd_of_progradeElliptic {m : Fin 2 → ℝ} (hm : ∀ i, 0 < m i)
    {z : Phase (2 * 2)} (hz : ProgradeElliptic m z) : ∃ w ∈ poincareProdDom 2, poincareProd m 1 w = z := by
  have h : z ∈ regionProd m 1 := (regionProd_one_iff hm z).2 hz
  rw [← poincareProd_image hm one_pos] at h
  obtain ⟨w, hw, hwz⟩ := h
  exact ⟨w, hw, hwz⟩

end D25

end KAM.Planetary

end
