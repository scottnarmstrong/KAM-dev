/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarTorsion.Birkhoff.Defs
public import KAM.Planetary.PlanarTorsion.Birkhoff.Domain
public import KAM.Planetary.PlanarTorsion.Lift
public import KAM.Planetary.PlanarTorsion.QuarticFlow

/-!
# Planar quartic torsion: the composite map `T = rotationLift ∘ liftFlow` (package T16)

Blueprint P, Part 11b (`stepP:p11b:bt-rot#lift`, `stepP:p11b:bt-avg`).  On a point
`assemble I φ z.2 z.1` of the tube, `T` only translates the angles by a vector independent of `φ`
(`p11cB_T_assemble`), moves the slow part to the frame-rotated flow image
`U(I) · Y(I, z)` (`Y = p11c_flow chi I 1 z`), and preserves the actions.
-/

@[expose] public noncomputable section

open Set Metric Real MeasureTheory Function Filter
open scoped Topology

namespace KAM.Planetary

open KAM KAM.Kepler KAM.ODE

theorem p11cB_rotationLift_assemble (p : PlanarData) (I φ : Fin 2 → ℝ) (y : Phase 2) :
    p11c_rotationLift p (assemble I φ y.2 y.1) =
      assemble I (φ + fun l => ∑ i, ∑ j, ∑ k, y.2 i * p11c_frame p (p.axes I) k i *
          fderiv ℝ (fun J => p11c_frame p (p.axes J) k j) I (Pi.single l 1) * y.1 j)
        (p11c_rotateSlow (p11c_frame p (p.axes I)) y).2
        (p11c_rotateSlow (p11c_frame p (p.axes I)) y).1 := by
  have h1 : (fun i : Fin 2 => (assemble I φ y.2 y.1 : Phase (2 + 2)).2 (Fin.castAdd 2 i)) = I :=
    p11cL_act_assemble I φ y
  have h2 : (fun i : Fin 2 => (assemble I φ y.2 y.1 : Phase (2 + 2)).1 (Fin.castAdd 2 i)) = φ :=
    p11cL_ang_assemble I φ y
  have h3 : ((fun i : Fin 2 => (assemble I φ y.2 y.1 : Phase (2 + 2)).1 (Fin.natAdd 2 i)),
      (fun i : Fin 2 => (assemble I φ y.2 y.1 : Phase (2 + 2)).2 (Fin.natAdd 2 i))) = y :=
    p11cL_slow_assemble I φ y
  unfold p11c_rotationLift
  simp only [h1, h2]
  have h31 : (fun i : Fin 2 => (assemble I φ y.2 y.1 : Phase (2 + 2)).1 (Fin.natAdd 2 i)) = y.1 :=
    congrArg Prod.fst h3
  have h32 : (fun i : Fin 2 => (assemble I φ y.2 y.1 : Phase (2 + 2)).2 (Fin.natAdd 2 i)) = y.2 :=
    congrArg Prod.snd h3
  have h31' : ∀ i : Fin 2, (assemble I φ y.2 y.1 : Phase (2 + 2)).1 (Fin.natAdd 2 i) = y.1 i :=
    fun i => congrFun h31 i
  have h32' : ∀ i : Fin 2, (assemble I φ y.2 y.1 : Phase (2 + 2)).2 (Fin.natAdd 2 i) = y.2 i :=
    fun i => congrFun h32 i
  simp only [h31', h32', Prod.mk.eta]

/-- `T` translates the angles by a vector independent of `φ` and moves the slow part to the
frame rotation of the flow image. -/
theorem p11cB_T_assemble (p : PlanarData) (chi : (Fin 2 → ℝ) → Phase 2 → ℝ) (I : Fin 2 → ℝ)
    (z : Phase 2) :
    ∃ c : Fin 2 → ℝ, ∀ φ : Fin 2 → ℝ,
      (p11c_rotationLift p ∘ p11c_liftFlow chi) (assemble I φ z.2 z.1) =
        assemble I (φ + c)
          (p11c_rotateSlow (p11c_frame p (p.axes I)) (p11c_flow chi I 1 z)).2
          (p11c_rotateSlow (p11c_frame p (p.axes I)) (p11c_flow chi I 1 z)).1 := by
  set Y := p11c_flow chi I 1 z with hY
  set g : Fin 2 → ℝ := fun i => ∫ t in (0 : ℝ)..1,
    fderiv ℝ (fun J => chi J (p11c_flow chi I t z)) I (Pi.single i 1) with hg
  set H : Fin 2 → ℝ := fun l => ∑ i, ∑ j, ∑ k, Y.2 i * p11c_frame p (p.axes I) k i *
    fderiv ℝ (fun J => p11c_frame p (p.axes J) k j) I (Pi.single l 1) * Y.1 j with hH
  refine ⟨g + H, fun φ => ?_⟩
  have h1 : p11c_liftFlow chi (assemble I φ z.2 z.1) = assemble I (φ + g) Y.2 Y.1 := by
    rw [p11cL_liftFlow_eq, p11cL_act_assemble, p11cL_ang_assemble, p11cL_slow_assemble]
  show p11c_rotationLift p (p11c_liftFlow chi (assemble I φ z.2 z.1)) = _
  rw [h1, p11cB_rotationLift_assemble, add_assoc]

theorem p11cB_assemble_eta (w : Phase (2 + 2)) :
    assemble (p11cL_act w) (p11cL_ang w) (p11cL_slow w).2 (p11cL_slow w).1 = w := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;>
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp [assemble, p11cL_act, p11cL_ang, p11cL_slow, Fin.append_left]

theorem p11cB_slowLength_sq (z : Phase 2) :
    p11c_slowLength z ^ 2 = ∑ i, (z.1 i ^ 2 + z.2 i ^ 2) := p11cQ_slowLength_sq z

/-- The frame rotation preserves the Euclidean length of a vector. -/
theorem p11cB_rot_sq (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (v : Fin 2 → ℝ) :
    ((p11c_frame p a).mulVec v 0) ^ 2 + ((p11c_frame p a).mulVec v 1) ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  have h := ((global_planar_frame p hp).2 a ha).1
  have e : ∀ k l, ((p11c_frame p a).transpose * p11c_frame p a) k l = (1 : Matrix (Fin 2) (Fin 2) ℝ) k l :=
    fun k l => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at e00 e01 e11
  simp at e00 e01 e11
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination v 0 ^ 2 * e00 + 2 * v 0 * v 1 * e01 + v 1 ^ 2 * e11

/-- The slow components of a rotated vector are bounded by the Euclidean length. -/
theorem p11cB_rot_abs_lt (p : PlanarData) (hp : p.Valid) {a : Fin 2 → ℝ} (ha : a ∈ p11c_axes)
    (v : Fin 2 → ℝ) {δ : ℝ} (hδ : 0 < δ) (hv : v 0 ^ 2 + v 1 ^ 2 < δ ^ 2) (i : Fin 2) :
    |(p11c_frame p a).mulVec v i| < δ := by
  have h := p11cB_rot_sq p hp ha v
  refine abs_lt_of_sq_lt_sq ?_ hδ.le
  fin_cases i
  · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ((p11c_frame p a).mulVec v 1)]
  · simp only [Fin.mk_one]; nlinarith [sq_nonneg ((p11c_frame p a).mulVec v 0)]

/-- Points of the tube are mapped into the good physical domain. -/
theorem p11cB_T_good (p : PlanarData) (hp : p.Valid) (chi : (Fin 2 → ℝ) → Phase 2 → ℝ)
    {K : Set (Fin 2 → ℝ)} (hKd : K ⊆ p11c_frameActionDomain p) {δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ w : Phase (2 + 2), (fun i => w.2 (Fin.castAdd 2 i)) ∈ K →
      (∀ i, |w.1 (Fin.natAdd 2 i)| < δ) → (∀ i, |w.2 (Fin.natAdd 2 i)| < δ) → w ∈ p11cB_good p)
    {r : ℝ} (hr : 2 * r ≤ δ)
    (hflow : ∀ I ∈ K, ∀ z : Phase 2, p11c_slowLength z < r →
      p11c_slowLength (p11c_flow chi I 1 z) ^ 2 ≤ 2 * p11c_slowLength z ^ 2) :
    ∀ w ∈ p11c_tube K r, (p11c_rotationLift p ∘ p11c_liftFlow chi) w ∈ p11cB_good p := by
  intro w hw
  obtain ⟨hIK, hz⟩ := hw
  set I : Fin 2 → ℝ := fun i => w.2 (Fin.castAdd 2 i) with hI
  set z : Phase 2 := (fun i => w.1 (Fin.natAdd 2 i), fun i => w.2 (Fin.natAdd 2 i)) with hzdef
  have hw' : w = assemble I (p11cL_ang w) z.2 z.1 := (p11cB_assemble_eta w).symm
  obtain ⟨c, hc⟩ := p11cB_T_assemble p chi I z
  rw [hw', hc]
  set Y := p11c_flow chi I 1 z with hY
  set Zs := p11c_rotateSlow (p11c_frame p (p.axes I)) Y with hZs
  have hax : p.axes I ∈ p11c_axes := hKd hIK
  have hz0 : 0 ≤ p11c_slowLength z := Real.sqrt_nonneg _
  have hY2 := hflow I hIK z hz
  have hlt : p11c_slowLength Y ^ 2 < δ ^ 2 := by nlinarith
  have hY1 : Y.1 0 ^ 2 + Y.1 1 ^ 2 < δ ^ 2 := by
    rw [p11cB_slowLength_sq, Fin.sum_univ_two] at hlt
    nlinarith [sq_nonneg (Y.2 0), sq_nonneg (Y.2 1)]
  have hY2' : Y.2 0 ^ 2 + Y.2 1 ^ 2 < δ ^ 2 := by
    rw [p11cB_slowLength_sq, Fin.sum_univ_two] at hlt
    nlinarith [sq_nonneg (Y.1 0), sq_nonneg (Y.1 1)]
  have hZ1 : ∀ i, |Zs.1 i| < δ := fun i => p11cB_rot_abs_lt p hp hax Y.1 hδ hY1 i
  have hZ2 : ∀ i, |Zs.2 i| < δ := fun i => p11cB_rot_abs_lt p hp hax Y.2 hδ hY2' i
  refine hdom _ ?_ ?_ ?_
  · have h : (fun i : Fin 2 => ((assemble I (p11cL_ang w + c) Zs.2 Zs.1 : Phase (2 + 2))).2
        (Fin.castAdd 2 i)) = I := by
      funext i; simp [assemble, Fin.append_left]
    rw [h]; exact hIK
  · intro i
    simpa [assemble, Fin.append_right] using hZ1 i
  · intro i
    simpa [assemble, Fin.append_right] using hZ2 i

end KAM.Planetary

end
