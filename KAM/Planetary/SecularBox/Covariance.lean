/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Frozen.Planetary.Defs.Assemble
public import KAM.Frozen.Planetary.Defs.EllipsePosition
public import KAM.Frozen.Planetary.Defs.EllipseMomentum
public import KAM.Frozen.Planetary.Defs.LongitudeJacobian
public import KAM.Frozen.Planetary.Defs.SecularRoot
public import KAM.Frozen.Planetary.Defs.SecularGamma
public import KAM.Frozen.Planetary.Defs.SecularEccVector
public import KAM.Frozen.Planetary.Defs.SecularAxis
public import KAM.Frozen.Planetary.Defs.OscillatorAction
public import KAM.Frozen.Planetary.Defs.QuarterTurn

/-!
# Rotation covariance of the explicit secular chart

`secularRotation` rotates each slow pair `(xi, eta)` by the angle `theta` and fixes the fast block.
`sb_cov` (blueprint `bpP:p14:sb-cov`) states that the slow action is invariant, the eccentricity
vector rotates, the longitude Jacobian shifts by `theta`, and the ellipse position and momentum
rotate while their eccentric longitude shifts. It holds at all points (steps `sb-cv-1`..`sb-cv-3`
are internal), as the identities are algebraic.
-/

@[expose] public noncomputable section

open KAM.Kepler

namespace KAM.Planetary

/-- Rotation of the slow `(xi, eta)` pairs by `theta`, fixing the fast angles and actions. -/
def secularRotation (theta : ℝ) (w : Phase (2+2)) : Phase (2+2) :=
  assemble (fast w.2) (fast w.1)
    (fun i => (KAM.Kepler.rot theta ![slow w.1 i, slow w.2 i]) 1)
    (fun i => (KAM.Kepler.rot theta ![slow w.1 i, slow w.2 i]) 0)

private theorem sbCov_fast_snd (theta : ℝ) (w : Phase (2+2)) :
    fast (secularRotation theta w).2 = fast w.2 := by
  ext i; simp [secularRotation, assemble, fast]

private theorem sbCov_slow_fst (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) :
    slow (secularRotation theta w).1 i = (rot theta ![slow w.1 i, slow w.2 i]) 0 := by
  simp only [secularRotation, assemble, slow]
  exact Fin.append_right _ _ i

private theorem sbCov_slow_snd (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) :
    slow (secularRotation theta w).2 i = (rot theta ![slow w.1 i, slow w.2 i]) 1 := by
  simp only [secularRotation, assemble, slow]
  exact Fin.append_right _ _ i

private theorem sbCov_pair (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) :
    ![slow (secularRotation theta w).1 i, slow (secularRotation theta w).2 i] =
      rot theta ![slow w.1 i, slow w.2 i] := by
  rw [sbCov_slow_fst, sbCov_slow_snd]
  ext j; fin_cases j <;> rfl

private theorem sbCov_rot_smul (g c : ℝ) (v : Fin 2 → ℝ) : rot g (c • v) = c • rot g v := by
  ext i; fin_cases i <;> simp [rot] <;> ring

private theorem sbCov_rot_sub (g : ℝ) (u v : Fin 2 → ℝ) : rot g (u - v) = rot g u - rot g v := by
  ext i; fin_cases i <;> simp [rot] <;> ring

private theorem sbCov_rot_add (g : ℝ) (u v : Fin 2 → ℝ) : rot g (u + v) = rot g u + rot g v := by
  ext i; fin_cases i <;> simp [rot] <;> ring

private theorem sbCov_gamma (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) :
    secularGamma (secularRotation theta w) i = secularGamma w i := by
  simp only [secularGamma, oscillatorAction]
  rw [sbCov_slow_fst, sbCov_slow_snd]
  have := Real.sin_sq_add_cos_sq theta
  simp only [rot, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination (slow w.2 i ^ 2 + slow w.1 i ^ 2) / 2 * this

private theorem sbCov_ecc (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) :
    secularEccVector (secularRotation theta w) i = rot theta (secularEccVector w i) := by
  unfold secularEccVector
  rw [sbCov_gamma, sbCov_fast_snd, sbCov_pair, sbCov_rot_smul]

private theorem sbCov_orbitalUnit (theta F : ℝ) :
    orbitalUnit F = rot theta (orbitalUnit (F - theta)) := by
  have := rot_ex theta (F - theta)
  rw [show theta + (F - theta) = F by ring] at this
  exact this.symm

private theorem sbCov_root (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) :
    secularRoot (secularRotation theta w) i = secularRoot w i := by
  unfold secularRoot
  rw [sbCov_gamma, sbCov_fast_snd]

private theorem sbCov_jac (theta : ℝ) (w : Phase (2+2)) (i : Fin 2) (F : ℝ) :
    longitudeJacobian (secularRotation theta w) i F = longitudeJacobian w i (F - theta) := by
  unfold longitudeJacobian
  rw [sbCov_ecc, sbCov_orbitalUnit theta F, planeDot_rot]

theorem sb_cov (m : Fin 2 → ℝ) (w : Phase (2+2)) (theta : ℝ) :
    (∀ i, secularGamma (secularRotation theta w) i = secularGamma w i ∧
      secularEccVector (secularRotation theta w) i = KAM.Kepler.rot theta (secularEccVector w i)) ∧
    ∀ i F, longitudeJacobian (secularRotation theta w) i F = longitudeJacobian w i (F-theta) ∧
      ellipsePosition m (secularRotation theta w) i F =
        KAM.Kepler.rot theta (ellipsePosition m w i (F-theta)) ∧
      ellipseMomentum m (secularRotation theta w) i F =
        KAM.Kepler.rot theta (ellipseMomentum m w i (F-theta)) := by
  refine ⟨fun i => ⟨sbCov_gamma theta w i, sbCov_ecc theta w i⟩,
    fun i F => ⟨sbCov_jac theta w i F, ?_, ?_⟩⟩
  · have hax : secularAxis m (secularRotation theta w) i = secularAxis m w i := by
      unfold secularAxis; rw [sbCov_fast_snd]
    unfold ellipsePosition
    simp only [hax, sbCov_root, sbCov_ecc theta w i]
    rw [sbCov_orbitalUnit theta F, planeDot_rot, sbCov_rot_smul, sbCov_rot_add, sbCov_rot_sub,
      sbCov_rot_smul, sbCov_rot_smul]
  · unfold ellipseMomentum
    simp only [sbCov_fast_snd, sbCov_jac, sbCov_root, sbCov_ecc theta w i]
    rw [sbCov_orbitalUnit theta F, planeDot_rot, sbCov_rot_smul, sbCov_rot_sub, sbCov_rot_smul,
      rot_quarterTurn, rot_quarterTurn]

end KAM.Planetary

end
