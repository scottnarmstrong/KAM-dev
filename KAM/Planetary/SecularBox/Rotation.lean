/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularBox.Covariance
public import KAM.Planetary.SecularBox.Region
public import KAM.Planetary.SecularBox.Smooth
public import KAM.Frozen.Planetary.Defs.ExactSecularHamiltonian
public import KAM.Frozen.Planetary.Defs.SecularIntegrand
public import KAM.Frozen.Planetary.Defs.MovingHamiltonian
public import KAM.Frozen.Planetary.Defs.EllipsePhase

/-!
# Rotation invariance of the secular region and Hamiltonian

`sb_rot` (blueprint `bpP:p14:sb-rot`): for `w` in `S` the rotated point `secularRotation theta w`
lies in `S` and has the same exact secular Hamiltonian. Steps `sb-rot-1` (membership), `sb-rot-2`
(the moving Hamiltonian is rotation invariant), `sb-rot-3` (the explicit integrand shifts by
`theta` in every eccentric longitude) and `sb-rot-4` (a periodic integrand has the same integral
over the box after a common shift) are internal.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open KAM.Kepler

namespace KAM.Planetary

private theorem sbRot_fast_snd (theta : ℝ) (w : Phase (2+2)) :
    fast (secularRotation theta w).2 = fast w.2 := by
  ext i; simp [secularRotation, assemble, fast]

/-- Step `sb-rot-1`: membership of the rotated point. -/
private theorem sbRot_mem (saturn : ℝ) {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) (theta : ℝ) :
    secularRotation theta w ∈ sb_sdef saturn := by
  have hg : ∀ i, secularGamma (secularRotation theta w) i = secularGamma w i :=
    fun i => ((sb_cov (jupiterSaturnWeights saturn) w theta).1 i).1
  have hax : ∀ m i, secularAxis m (secularRotation theta w) i = secularAxis m w i := by
    intro m i; unfold secularAxis; rw [sbRot_fast_snd]
  obtain ⟨h, h1, h2, h3, h4⟩ := hw
  refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg, sbRot_fast_snd]; exact h i
  · rw [hax]; exact h1
  · rw [hax]; exact h2
  · rw [hax]; exact h3
  · rw [hax]; exact h4

private theorem sbRot_rot_sub (g : ℝ) (u v : Fin 2 → ℝ) : rot g (u - v) = rot g u - rot g v := by
  ext i; fin_cases i <;> simp [rot] <;> ring

private theorem sbRot_bodyVector_fst (m : Fin 2 → ℝ) (w : Phase (2+2)) (F : Fin 2 → ℝ)
    (i : Fin 2) : bodyVector (ellipsePhase m w F).1 i = ellipsePosition m w i (F i) := by
  funext k; simp [bodyVector, ellipsePhase]

private theorem sbRot_bodyVector_snd (m : Fin 2 → ℝ) (w : Phase (2+2)) (F : Fin 2 → ℝ)
    (i : Fin 2) : bodyVector (ellipsePhase m w F).2 i = ellipseMomentum m w i (F i) := by
  funext k; simp [bodyVector, ellipsePhase]

/-- Step `sb-rot-2`: the moving Hamiltonian is invariant under a common rotation. -/
private theorem sbRot_moving (m : Fin 2 → ℝ) (mu theta : ℝ) (z z' : Phase (2 * 2))
    (hq : ∀ i, bodyVector z'.1 i = rot theta (bodyVector z.1 i))
    (hp : ∀ i, bodyVector z'.2 i = rot theta (bodyVector z.2 i)) :
    movingHamiltonian 1 1 m mu z' = movingHamiltonian 1 1 m mu z := by
  unfold movingHamiltonian
  simp only [hq, hp, planeSq_eq_planeDot, planeDot_rot, planeLength_rot, ← sbRot_rot_sub]

/-- Step `sb-rot-3`: the explicit integrand of the rotated point is shifted by `theta`. -/
private theorem sbRot_explicit (m : Fin 2 → ℝ) (mu : ℝ) (w : Phase (2+2)) (theta : ℝ)
    (F : Fin 2 → ℝ) :
    explicitSecularIntegrand m mu (secularRotation theta w) F =
      explicitSecularIntegrand m mu w (fun i => F i - theta) := by
  have hc := sb_cov m w theta
  unfold explicitSecularIntegrand
  rw [sbRot_moving m mu theta (ellipsePhase m w (fun i => F i - theta))
    (ellipsePhase m (secularRotation theta w) F)]
  · congr 1
    exact Finset.prod_congr rfl fun i _ => (hc.2 i (F i)).1
  · intro i
    rw [sbRot_bodyVector_fst, sbRot_bodyVector_fst]
    exact (hc.2 i (F i)).2.1
  · intro i
    rw [sbRot_bodyVector_snd, sbRot_bodyVector_snd]
    exact (hc.2 i (F i)).2.2

private theorem sbRot_interval_shift (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi))
    (theta : ℝ) :
    ∫ x in (0:ℝ)..2 * Real.pi, f (x - theta) = ∫ x in (0:ℝ)..2 * Real.pi, f x := by
  rw [intervalIntegral.integral_comp_sub_right (fun x => f x) theta]
  have := hf.intervalIntegral_add_eq (-theta) 0
  simpa [sub_eq_add_neg, add_comm] using this

private theorem sbRot_Icc (f : ℝ → ℝ) :
    ∫ x in Icc 0 (2 * Real.pi), f x = ∫ x in (0:ℝ)..2 * Real.pi, f x := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity)]

/-- Step `sb-rot-4` (planar form): a continuous function periodic in each variable has the same
integral over the box `[0, 2π]²` after a common shift. -/
private theorem sbRot_box_shift (h : ℝ × ℝ → ℝ) (hc : Continuous h)
    (hx : ∀ x y, h (x + 2 * Real.pi, y) = h (x, y))
    (hy : ∀ x y, h (x, y + 2 * Real.pi) = h (x, y)) (theta : ℝ) :
    ∫ p in Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi), h (p.1 - theta, p.2 - theta) =
      ∫ p in Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi), h p := by
  have hint : ∀ g : ℝ × ℝ → ℝ, Continuous g →
      IntegrableOn g (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) (volume.prod volume) :=
    fun g hg => hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ (hint _ (by fun_prop)),
    setIntegral_prod _ (hint _ hc)]
  simp only [sbRot_Icc]
  have hphi : Function.Periodic (fun x => ∫ y in (0:ℝ)..2 * Real.pi, h (x, y)) (2 * Real.pi) :=
    fun x => by simp only [hx]
  have inner : ∀ x, ∫ y in (0:ℝ)..2 * Real.pi, h (x - theta, y - theta) =
      ∫ y in (0:ℝ)..2 * Real.pi, h (x - theta, y) :=
    fun x => sbRot_interval_shift (fun y => h (x - theta, y)) (fun y => hy _ _) theta
  simp only [inner]
  exact sbRot_interval_shift _ hphi theta

private theorem sbRot_pi_shift (g : (Fin 2 → ℝ) → ℝ) (hc : Continuous g)
    (hper : ∀ F i, g (F + Pi.single i (2 * Real.pi)) = g F) (theta : ℝ) :
    ∫ F in Set.pi univ (fun _ : Fin 2 => Icc 0 (2 * Real.pi)), g (fun i => F i - theta) =
      ∫ F in Set.pi univ (fun _ : Fin 2 => Icc 0 (2 * Real.pi)), g F := by
  let e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have he : MeasurePreserving e volume volume := volume_preserving_finTwoArrow ℝ
  have hset : Set.pi univ (fun _ : Fin 2 => Icc 0 (2 * Real.pi)) =
      e ⁻¹' (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) := by
    ext F
    simp only [Set.mem_pi, mem_univ, true_implies, Fin.forall_fin_two, mem_preimage,
      mem_prod, mem_Icc]
    simp [e, MeasurableEquiv.finTwoArrow]
  have h1 : ∀ F : Fin 2 → ℝ, g (fun i => F i - theta) =
      (fun p : ℝ × ℝ => g (e.symm (p.1 - theta, p.2 - theta))) (e F) := by
    intro F; congr 1; funext i; fin_cases i <;> simp [e, MeasurableEquiv.finTwoArrow]
  have h2 : ∀ F : Fin 2 → ℝ, g F = (fun p : ℝ × ℝ => g (e.symm p)) (e F) := by
    intro F; simp
  have hemb := e.measurableEmbedding
  rw [hset]
  have k1 := he.setIntegral_preimage_emb hemb
    (fun p : ℝ × ℝ => g (e.symm (p.1 - theta, p.2 - theta)))
    (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi))
  have k2 := he.setIntegral_preimage_emb hemb (fun p : ℝ × ℝ => g (e.symm p))
    (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi))
  simp only [← h1, ← h2] at k1 k2
  rw [k1, k2]
  have hes : Continuous e.symm := continuous_pi fun i => by
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  refine sbRot_box_shift (fun p => g (e.symm p)) (hc.comp hes) ?_ ?_ theta
  · intro x y
    rw [← hper (e.symm (x, y)) 0]
    congr 1; funext i; fin_cases i <;> simp [e, MeasurableEquiv.finTwoArrow]
  · intro x y
    rw [← hper (e.symm (x, y)) 1]
    congr 1; funext i; fin_cases i <;> simp [e, MeasurableEquiv.finTwoArrow]

/-- The exact secular Hamiltonian as the average of the explicit integrand. -/
private theorem sbRot_exact (m : Fin 2 → ℝ) (mu : ℝ) (w : Phase (2+2)) :
    exactSecularHamiltonian m mu w = (2 * Real.pi) ^ (-(2:ℕ):ℤ) *
      ∫ F in Set.pi univ (fun _ : Fin 2 => Icc 0 (2 * Real.pi)),
        explicitSecularIntegrand m mu w F := by
  unfold exactSecularHamiltonian secularAverage
  simp only [secular_integrand_identity]

theorem sb_rot (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {w : Phase (2+2)} (hw : w ∈ sb_sdef saturn) (theta : ℝ) :
    secularRotation theta w ∈ sb_sdef saturn ∧
      exactSecularHamiltonian (jupiterSaturnWeights saturn) mu (secularRotation theta w) =
        exactSecularHamiltonian (jupiterSaturnWeights saturn) mu w := by
  refine ⟨sbRot_mem saturn hw theta, ?_⟩
  obtain ⟨hsm, hper⟩ := secular_integrand_smooth saturn mu hs
  have hcont : Continuous fun F : Fin 2 → ℝ =>
      explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w F := by
    have := hsm.continuousOn.comp_continuous (f := fun F : Fin 2 → ℝ => (w, F))
      (by fun_prop) (fun F => ⟨hw, mem_univ F⟩)
    exact this
  rw [sbRot_exact, sbRot_exact]
  congr 1
  simp only [sbRot_explicit]
  exact sbRot_pi_shift _ hcont (fun F i => hper w F i) theta

end KAM.Planetary

end
