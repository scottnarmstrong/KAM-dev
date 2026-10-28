/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Frozen.Planetary.Defs.EllipsePosition
public import KAM.Frozen.Planetary.Defs.LongitudeJacobian
public import KAM.Frozen.Planetary.Defs.SecularRoot
public import KAM.Frozen.Planetary.Defs.SecularGamma
public import KAM.Frozen.Planetary.Defs.SecularAxis
public import KAM.Frozen.Planetary.Defs.SecularEccVector

/-!
# Algebra of the explicit secular chart

`sb_chart` (blueprint `bpP:p14:sb-chart`): on elliptic points the secular root is in `(0, 1]`, the
eccentricity vector has length `< 1`, the longitude Jacobian is positive, and the ellipse
position has radius `a (1 - x)`. Steps `sb-ch-a`..`sb-ch-d` are internal to the single theorem.
-/

public section

open KAM.Kepler

namespace KAM.Planetary

private theorem sbChart_planeLength_orbitalUnit (F : ℝ) : planeLength (orbitalUnit F) = 1 := by
  unfold planeLength planeSq orbitalUnit
  simp [Fin.sum_univ_two, Real.cos_sq_add_sin_sq]

private theorem sbChart_planeSq_orbitalUnit (F : ℝ) :
    (orbitalUnit F 0) ^ 2 + (orbitalUnit F 1) ^ 2 = 1 := by
  simp [orbitalUnit, Real.cos_sq_add_sin_sq]

/-- Pure algebra of step `sb-ch-c`. -/
private theorem sbChart_identity {k x s c0 c1 v0 v1 : ℝ} (hk : 0 < k) (hc : c0 ^ 2 + c1 ^ 2 = 1)
    (hx : v0 * c0 + v1 * c1 = x) (hv : v0 ^ 2 + v1 ^ 2 = 1 - k ^ 2) (hs : s = x / (1 + k)) :
    (k * c0 - v0 + s * v0) ^ 2 + (k * c1 - v1 + s * v1) ^ 2 = (1 - x) ^ 2 := by
  have h1 : (k * c0 - v0 + s * v0) ^ 2 + (k * c1 - v1 + s * v1) ^ 2 =
      k ^ 2 * (c0 ^ 2 + c1 ^ 2) + 2 * k * (s - 1) * (v0 * c0 + v1 * c1) +
        (s - 1) ^ 2 * (v0 ^ 2 + v1 ^ 2) := by ring
  rw [h1, hc, hx, hv, hs]
  have : (1 + k) ≠ 0 := by positivity
  field_simp
  ring

theorem sb_chart (m : Fin 2 → ℝ) (hm : ∀ i, 0 < m i) {w : Phase (2+2)}
    (hw : ∀ i, 0 < fast w.2 i ∧ 0 ≤ secularGamma w i ∧ secularGamma w i < fast w.2 i) :
    ∀ i, 0 < ((1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i) ∧
      0 < secularRoot w i ∧ secularRoot w i ≤ 1 ∧
      secularRoot w i = Real.sqrt (1 - planeLength (secularEccVector w i)^2) ∧
      planeLength (secularEccVector w i)^2 = 1 - secularRoot w i ^ 2 ∧
      planeLength (secularEccVector w i) < 1 ∧
      secularGamma w i = fast w.2 i * (1 - secularRoot w i) ∧
      ∀ F : ℝ, 0 < longitudeJacobian w i F ∧
        1 - planeLength (secularEccVector w i) ≤ longitudeJacobian w i F ∧
        planeLength (ellipsePosition m w i F) = secularAxis m w i * longitudeJacobian w i F ∧
        secularAxis m w i * (1-planeLength (secularEccVector w i)) ≤
          planeLength (ellipsePosition m w i F) ∧
        planeLength (ellipsePosition m w i F) ≤
          secularAxis m w i * (1+planeLength (secularEccVector w i)) := by
  intro i
  obtain ⟨hL, hG0, hGL⟩ := hw i
  set L := fast w.2 i with hLdef
  set G := secularGamma w i with hGdef
  set k := secularRoot w i with hkdef
  have hk : k = 1 - G / L := rfl
  have hGL' : G / L < 1 := (div_lt_one hL).2 hGL
  have hG0' : 0 ≤ G / L := div_nonneg hG0 hL.le
  have hkpos : 0 < k := by rw [hk]; linarith
  have hk1 : k ≤ 1 := by rw [hk]; linarith
  have hR : 0 < (1 - G / (2 * L)) / L := by
    have : G / (2 * L) = G / L / 2 := by field_simp
    apply div_pos _ hL
    rw [this]; linarith
  -- the slow data
  set ξ := slow w.1 i with hξ
  set η := slow w.2 i with hη
  have hGeq : G = (η ^ 2 + ξ ^ 2) / 2 := rfl
  set R := (1 - G / (2 * L)) / L with hRdef
  have hvdef : secularEccVector w i = Real.sqrt R • ![ξ, η] := rfl
  have hv0 : secularEccVector w i 0 = Real.sqrt R * ξ := by simp [hvdef]
  have hv1 : secularEccVector w i 1 = Real.sqrt R * η := by simp [hvdef]
  have hsqR : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR.le
  have hvsq : (secularEccVector w i 0) ^ 2 + (secularEccVector w i 1) ^ 2 = 1 - k ^ 2 := by
    rw [hv0, hv1]
    have : (Real.sqrt R * ξ) ^ 2 + (Real.sqrt R * η) ^ 2 = R * (ξ ^ 2 + η ^ 2) := by
      rw [mul_pow, mul_pow, hsqR]; ring
    rw [this, hRdef, hk]
    have : ξ ^ 2 + η ^ 2 = 2 * G := by rw [hGeq]; ring
    rw [this]
    field_simp
    ring
  set v := secularEccVector w i with hvD
  set e := planeLength v with hedef
  have he2 : e ^ 2 = 1 - k ^ 2 := by
    rw [hedef, planeLength_sq]
    simpa [planeSq, Fin.sum_univ_two] using hvsq
  have he0 : 0 ≤ e := planeLength_nonneg v
  have hk2 : 0 < k ^ 2 := by positivity
  have he1 : e < 1 := by nlinarith
  have hxF : ∀ F : ℝ, |planeDot v (orbitalUnit F)| ≤ e := by
    intro F
    simpa [sbChart_planeLength_orbitalUnit] using abs_planeDot_le v (orbitalUnit F)
  refine ⟨hR, hkpos, hk1, ?_, he2, he1, ?_, ?_⟩
  · have : 1 - e ^ 2 = k ^ 2 := by rw [he2]; ring
    rw [this, Real.sqrt_sq hkpos.le]
  · rw [hk]; field_simp; ring
  intro F
  have hJ : longitudeJacobian w i F = 1 - planeDot v (orbitalUnit F) := rfl
  have hx := abs_le.1 (hxF F)
  have hJpos : 1 - e ≤ longitudeJacobian w i F := by rw [hJ]; linarith [hx.2]
  have hJ0 : 0 < longitudeJacobian w i F := by linarith
  have haxis : 0 < secularAxis m w i := by
    unfold secularAxis; exact pow_pos (div_pos hL (hm i)) 2
  have hq : ellipsePosition m w i F = secularAxis m w i •
      (k • orbitalUnit F - v + (planeDot v (orbitalUnit F) / (1 + k)) • v) := rfl
  have hq' : planeLength (k • orbitalUnit F - v + (planeDot v (orbitalUnit F) / (1 + k)) • v) =
      longitudeJacobian w i F := by
    set u := k • orbitalUnit F - v + (planeDot v (orbitalUnit F) / (1 + k)) • v with hu
    have hsq : planeLength u ^ 2 = longitudeJacobian w i F ^ 2 := by
      rw [planeLength_sq, hJ]
      have := sbChart_identity (k := k) (x := planeDot v (orbitalUnit F))
        (s := planeDot v (orbitalUnit F) / (1 + k)) (c0 := orbitalUnit F 0) (c1 := orbitalUnit F 1)
        (v0 := v 0) (v1 := v 1) hkpos (sbChart_planeSq_orbitalUnit F)
        (by simp [planeDot, Fin.sum_univ_two]) hvsq rfl
      simpa [planeSq, Fin.sum_univ_two, hu] using this
    exact (pow_left_inj₀ (planeLength_nonneg u) hJ0.le two_ne_zero).1 hsq
  have hlen : planeLength (ellipsePosition m w i F) =
      secularAxis m w i * longitudeJacobian w i F := by
    rw [hq, planeLength_smul, hq', abs_of_pos haxis]
  refine ⟨hJ0, hJpos, hlen, ?_, ?_⟩
  · rw [hlen]; exact mul_le_mul_of_nonneg_left hJpos haxis.le
  · rw [hlen]; apply mul_le_mul_of_nonneg_left _ haxis.le
    rw [hJ]; linarith [hx.1]

end KAM.Planetary

end
