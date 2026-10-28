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

variable {n : ℕ}

/-! ### Block calculus -/

theorem planetBlock_assemble (I phi p q : Fin n → ℝ) (j : Fin n) :
    planetBlock (assemble I phi p q : Phase (n + n)) j = (![phi j, q j], ![I j, p j]) := by
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_) <;> fin_cases k <;>
    simp [planetBlock, assemble, fast, slow, Fin.append_left]

/-- `bpP:p7:d25` (a): the frozen secular definitions are the chart's `Γ, k, v`
(all `w`, no domain needed). -/
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
    {z : Phase (2 * 2)} (hz : ProgradeElliptic m z) :
    ∃ w ∈ poincareProdDom 2, poincareProd m 1 w = z := by
  have h : z ∈ regionProd m 1 := (regionProd_one_iff hm z).2 hz
  rw [← poincareProd_image hm one_pos] at h
  obtain ⟨w, hw, hwz⟩ := h
  exact ⟨w, hw, hwz⟩

/-! ### Averages -/

/-- Change of variable `x = Φ(s, v)` over one period. -/
theorem integral_via_keplerPhi {v : Fin 2 → ℝ} (hv : planeLength v < 1) {g : ℝ → ℝ}
    (hg : Continuous g)
    (hper : Function.Periodic (fun s => g (keplerPhi v s) * keplerJac v s) (2 * π)) :
    ∫ x in (0 : ℝ)..2 * π, g x = ∫ s in (0 : ℝ)..2 * π, g (keplerPhi v s) * keplerJac v s := by
  have hJc : Continuous (keplerJac v) := by
    have : keplerJac v = fun F => 1 - v 0 * Real.cos F - v 1 * Real.sin F :=
      funext (keplerJac_eq v)
    rw [this]; fun_prop
  have h := intervalIntegral.integral_comp_mul_deriv' (a := keplerLong 0 v)
    (b := keplerLong 0 v + 2 * π) (f := keplerPhi v) (f' := keplerJac v) (g := g)
    (fun s _ => hasDerivAt_keplerPhi v s) hJc.continuousOn hg.continuousOn
  have e0 : keplerPhi v (keplerLong 0 v) = 0 := keplerPhi_keplerLong hv 0
  have e1 : keplerPhi v (keplerLong 0 v + 2 * π) = 2 * π := by
    rw [keplerPhi_shift, e0, zero_add]
  rw [e0, e1] at h
  rw [← h]
  have := hper.intervalIntegral_add_eq (keplerLong 0 v) 0
  rw [zero_add] at this
  simpa only [Function.comp_apply] using this

theorem orbitalUnit_add_two_pi (F : ℝ) : orbitalUnit (F + 2 * π) = orbitalUnit F := by
  simp [orbitalUnit]

theorem ellipsePosition_add_two_pi (m : Fin 2 → ℝ) (w : Phase (2 + 2)) (j : Fin 2) (F : ℝ) :
    ellipsePosition m w j (F + 2 * π) = ellipsePosition m w j F := by
  simp only [ellipsePosition, orbitalUnit_add_two_pi]

theorem longitudeJacobian_add_two_pi (w : Phase (2 + 2)) (j : Fin 2) (F : ℝ) :
    longitudeJacobian w j (F + 2 * π) = longitudeJacobian w j F := by
  simp only [longitudeJacobian, orbitalUnit_add_two_pi]

theorem ellipseMomentum_add_two_pi (m : Fin 2 → ℝ) (w : Phase (2 + 2)) (j : Fin 2) (F : ℝ) :
    ellipseMomentum m w j (F + 2 * π) = ellipseMomentum m w j F := by
  simp only [ellipseMomentum, orbitalUnit_add_two_pi, longitudeJacobian_add_two_pi]

theorem ellipsePhase_update_add_two_pi (m : Fin 2 → ℝ) (w : Phase (2 + 2)) (F : Fin 2 → ℝ)
    (i : Fin 2) (s : ℝ) :
    ellipsePhase m w (Function.update F i (s + 2 * π)) =
      ellipsePhase m w (Function.update F i s) := by
  have h : ∀ j, ellipsePosition m w j (Function.update F i (s + 2 * π) j) =
      ellipsePosition m w j (Function.update F i s j) ∧
      ellipseMomentum m w j (Function.update F i (s + 2 * π) j) =
      ellipseMomentum m w j (Function.update F i s j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self, ellipsePosition_add_two_pi, ellipseMomentum_add_two_pi,
        and_self]
    · simp only [Function.update_of_ne hj, and_self]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact congrFun (h _).1 _
  · exact congrFun (h _).2 _

theorem continuous_assemble_update (I p q : Fin n → ℝ) (phi : Fin n → ℝ) (i : Fin n) :
    Continuous (fun y : ℝ => (assemble I (Function.update phi i y) p q : Phase (n + n))) := by
  unfold assemble
  refine Continuous.prodMk (continuous_pi fun k => ?_) continuous_const
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [Fin.append_left]
    by_cases hj : j = i
    · subst hj; simpa only [Function.update_self] using continuous_id'
    · simpa [Function.update_of_ne hj] using continuous_const
  · simp only [Fin.append_right]
    exact continuous_const

/-- `bpP:p7:average`: the change of variable `λ_i ↔ F_i` in angular averages
(other `F_j = F_j(w)` fixed). -/
theorem average_via_eccentric_longitude {m : Fin 2 → ℝ} (hm : ∀ i, 0 < m i) {w : Phase (2 + 2)}
    (hw : w ∈ poincareProdDom 2) (i : Fin 2) {φ : Phase (2 * 2) → ℝ} (hφ : Continuous φ) :
    (2 * π)⁻¹ * ∫ x in (0 : ℝ)..2 * π,
        φ (poincareProd m 1
          (assemble (fast w.2) (Function.update (fast w.1) i x) (slow w.2) (slow w.1))) =
      (2 * π)⁻¹ * ∫ s in (0 : ℝ)..2 * π,
        φ (ellipsePhase m w (Function.update (fun j => poincareF (planetBlock w j)) i s)) *
          longitudeJacobian w i s := by
  have hv : planeLength (poincareV (planetBlock w i)) < 1 := (poincare_facts (hw i)).2.2.2.2.2.1
  set g : ℝ → ℝ := fun y => φ (poincareProd m 1
    (assemble (fast w.2) (Function.update (fast w.1) i y) (slow w.2) (slow w.1))) with hg
  have hgc : Continuous g := by
    have hpath := continuous_assemble_update (fast w.2) (slow w.2) (slow w.1) (fast w.1) i
    have hmem : ∀ y : ℝ, (assemble (fast w.2) (Function.update (fast w.1) i y) (slow w.2)
        (slow w.1) : Phase (2 + 2)) ∈ poincareProdDom 2 := by
      intro y j
      have := hw j
      rw [planetBlock_assemble]
      simpa [poincareDom, poincareGamma, planetBlock] using this
    exact hφ.comp ((analyticOnNhd_poincareProd hm one_pos).continuousOn.comp_continuous hpath hmem)
  have key : ∀ s,
      φ (ellipsePhase m w (Function.update (fun j => poincareF (planetBlock w j)) i s)) *
      longitudeJacobian w i s = g (keplerPhi (poincareV (planetBlock w i)) s) *
        keplerJac (poincareV (planetBlock w i)) s := by
    intro s
    rw [ellipsePhase_eq_poincareProd hm hw, hg]
    have hJ : longitudeJacobian w i s = keplerJac (poincareV (planetBlock w i)) s := by
      rw [longitudeJacobian_eq, secularEccVector_eq]
    rw [hJ]
    have hφ : (fun j => keplerPhi (poincareV (planetBlock w j))
        (Function.update (fun j => poincareF (planetBlock w j)) i s j)) =
        Function.update (fast w.1) i (keplerPhi (poincareV (planetBlock w i)) s) := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp only [Function.update_of_ne hj]
        exact keplerPhi_keplerLong (poincare_facts (hw j)).2.2.2.2.2.1 _
    rw [hφ]
  simp only [key]
  congr 1
  refine integral_via_keplerPhi hv hgc ?_
  have hfun : (fun s => g (keplerPhi (poincareV (planetBlock w i)) s) *
      keplerJac (poincareV (planetBlock w i)) s) = fun s =>
      φ (ellipsePhase m w (Function.update (fun j => poincareF (planetBlock w j)) i s)) *
        longitudeJacobian w i s := funext fun s => (key s).symm
  rw [hfun]
  intro s
  simp only [ellipsePhase_update_add_two_pi, longitudeJacobian_add_two_pi]

/-- The three mean values of the average corollary, for general `n` and `κ`. -/
theorem poincareProd_means {m : Fin n → ℝ} {κ : ℝ} (hm : ∀ i, 0 < m i) (hκ : 0 < κ)
    {w : Phase (n + n)}
    (hw : w ∈ poincareProdDom n) (i : Fin n) :
    let a := fast w.2 i ^ 2 / (m i ^ 2 * κ)
    let pt := fun x : ℝ => poincareProd m κ
      (assemble (fast w.2) (Function.update (fast w.1) i x) (slow w.2) (slow w.1))
    (2 * π)⁻¹ * (∫ x in (0 : ℝ)..2 * π, 1 / planeLength (bodyVector (pt x).1 i)) = 1 / a ∧
    (2 * π)⁻¹ * (∫ x in (0 : ℝ)..2 * π, planeSq (bodyVector (pt x).2 i)) = m i ^ 2 * κ / a ∧
    (2 * π)⁻¹ * (∫ x in (0 : ℝ)..2 * π, planeLength (bodyVector (pt x).1 i)) =
      a * (1 + planeSq (poincareV (planetBlock w i)) / 2) := by
  intro a pt
  have hblk : ∀ x, (bodyVector (pt x).1 i, bodyVector (pt x).2 i) =
      poincare (m i) κ (![x, (planetBlock w i).1 1], (planetBlock w i).2) := by
    intro x
    simp only [pt, poincareProd_block, planetBlock_assemble]
    simp only [Function.update_self]
    rfl
  have h1 : ∀ x, bodyVector (pt x).1 i = (poincare (m i) κ (![x, (planetBlock w i).1 1],
      (planetBlock w i).2)).1 := fun x => by rw [← hblk x]
  have h2 : ∀ x, bodyVector (pt x).2 i = (poincare (m i) κ (![x, (planetBlock w i).1 1],
      (planetBlock w i).2)).2 := fun x => by rw [← hblk x]
  obtain ⟨m1, m2, m3⟩ := poincare_means (hm i) hκ (hw i)
  simp only [h1, h2]
  obtain ⟨-, hK, -⟩ := poincare_facts (hw i)
  have hsq := (poincare_facts (hw i)).2.2.2.2.1
  rw [hsq]
  exact ⟨m1, m2, m3⟩

end D25

end KAM.Planetary

end
