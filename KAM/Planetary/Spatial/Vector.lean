/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Planetary.Spatial.Defs.BodyVector3
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceCross
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceDot
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceLength
public import KAM.Frozen.Planetary.Spatial.Defs.SpaceSq

/-!
# Three-dimensional vectors and body blocks

Source: support for `LP:MAIN §1 (9–93)` with `d = 3`; track LP, non-frozen.

Euclidean dot product, squared length, length and cross product on `Fin 3 → ℝ` (never
`EuclideanSpace`; physical lengths are Euclidean, never the Pi sup norm), the body block map
`bodyVector3 : (Fin (n * 3) → ℝ) → Fin n → Fin 3 → ℝ`, and the elementary algebra and calculus of
these (Lagrange's identity, Cauchy–Schwarz, analyticity and derivative of `1/|v|`).
-/

@[expose] public noncomputable section

namespace KAM.Planetary.Spatial

open KAM.Planetary
open scoped ContDiff

section Algebra

theorem spaceSq_def (v : Fin 3 → ℝ) : spaceSq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [spaceSq, Fin.sum_univ_three]

theorem spaceDot_def (v w : Fin 3 → ℝ) :
    spaceDot v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
  simp [spaceDot, Fin.sum_univ_three]

theorem spaceCross_apply_zero (v w : Fin 3 → ℝ) : spaceCross v w 0 = v 1 * w 2 - v 2 * w 1 := rfl

theorem spaceCross_apply_one (v w : Fin 3 → ℝ) : spaceCross v w 1 = v 2 * w 0 - v 0 * w 2 := rfl

theorem spaceCross_apply_two (v w : Fin 3 → ℝ) : spaceCross v w 2 = v 0 * w 1 - v 1 * w 0 := rfl

/-- The explicit `spaceCross` is Mathlib's `crossProduct`. -/
theorem spaceCross_eq_crossProduct (v w : Fin 3 → ℝ) : spaceCross v w = crossProduct v w := by
  ext k; fin_cases k <;> simp [spaceCross, cross_apply]

/-- The explicit `spaceDot` is Mathlib's `dotProduct` (`⬝ᵥ`). -/
theorem spaceDot_eq_dotProduct (v w : Fin 3 → ℝ) : spaceDot v w = v ⬝ᵥ w := by
  simp [spaceDot, dotProduct]

/-- `spaceSq v = v ⬝ᵥ v`. -/
theorem spaceSq_eq_dotProduct (v : Fin 3 → ℝ) : spaceSq v = v ⬝ᵥ v := by
  simp [spaceSq, dotProduct, sq]

theorem spaceSq_eq_spaceDot (v : Fin 3 → ℝ) : spaceSq v = spaceDot v v := by
  simp [spaceSq_def, spaceDot_def, sq]

theorem spaceSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ spaceSq v := by
  rw [spaceSq_def]; positivity

theorem spaceLength_sq (v : Fin 3 → ℝ) : spaceLength v ^ 2 = spaceSq v :=
  Real.sq_sqrt (spaceSq_nonneg v)

theorem spaceLength_nonneg (v : Fin 3 → ℝ) : 0 ≤ spaceLength v := Real.sqrt_nonneg _

theorem spaceSq_eq_zero_iff {v : Fin 3 → ℝ} : spaceSq v = 0 ↔ v = 0 := by
  rw [spaceSq_def]
  constructor
  · intro h
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    ext i; fin_cases i <;> simp [h0, h1, h2]
  · rintro rfl; simp

theorem spaceLength_eq_zero_iff {v : Fin 3 → ℝ} : spaceLength v = 0 ↔ v = 0 := by
  unfold spaceLength
  rw [Real.sqrt_eq_zero (spaceSq_nonneg v), spaceSq_eq_zero_iff]

theorem spaceLength_pos_iff {v : Fin 3 → ℝ} : 0 < spaceLength v ↔ v ≠ 0 := by
  rw [(spaceLength_nonneg v).lt_iff_ne, ne_comm, Ne, spaceLength_eq_zero_iff]

theorem spaceLength_neg (v : Fin 3 → ℝ) : spaceLength (-v) = spaceLength v := by
  simp [spaceLength, spaceSq_def]

theorem spaceLength_sub_comm (v w : Fin 3 → ℝ) : spaceLength (v - w) = spaceLength (w - v) := by
  rw [← neg_sub, spaceLength_neg]

theorem spaceLength_smul (c : ℝ) (v : Fin 3 → ℝ) : spaceLength (c • v) = |c| * spaceLength v := by
  unfold spaceLength
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
  congr 1
  simp [spaceSq_def]; ring

/-- Lagrange's identity `|q|²|p|² = (q·p)² + |q × p|²`. -/
theorem spaceSq_mul_spaceSq (q p : Fin 3 → ℝ) :
    spaceSq q * spaceSq p = spaceDot q p ^ 2 + spaceSq (spaceCross q p) := by
  simp only [spaceSq_def, spaceDot_def, spaceCross_apply_zero, spaceCross_apply_one,
    spaceCross_apply_two]; ring

theorem abs_spaceDot_le (v w : Fin 3 → ℝ) : |spaceDot v w| ≤ spaceLength v * spaceLength w := by
  unfold spaceLength
  rw [← Real.sqrt_mul (spaceSq_nonneg v)]
  apply Real.abs_le_sqrt
  rw [spaceSq_mul_spaceSq]; nlinarith [spaceSq_nonneg (spaceCross v w)]

theorem spaceDot_add_right (v a b : Fin 3 → ℝ) :
    spaceDot v (a + b) = spaceDot v a + spaceDot v b := by
  simp only [spaceDot_def, Pi.add_apply]; ring

theorem spaceDot_sub_right (v a b : Fin 3 → ℝ) :
    spaceDot v (a - b) = spaceDot v a - spaceDot v b := by
  simp only [spaceDot_def, Pi.sub_apply]; ring

theorem spaceDot_smul_right (c : ℝ) (v w : Fin 3 → ℝ) :
    spaceDot v (c • w) = c * spaceDot v w := by
  simp only [spaceDot_def, Pi.smul_apply, smul_eq_mul]; ring

theorem spaceDot_zero_right (v : Fin 3 → ℝ) : spaceDot v 0 = 0 := by simp [spaceDot]

theorem spaceSq_sub (v w : Fin 3 → ℝ) :
    spaceSq (v - w) = spaceSq v - 2 * spaceDot v w + spaceSq w := by
  simp only [spaceSq_def, spaceDot_def, Pi.sub_apply]; ring

theorem spaceSq_add (v w : Fin 3 → ℝ) :
    spaceSq (v + w) = spaceSq v + 2 * spaceDot v w + spaceSq w := by
  simp only [spaceSq_def, spaceDot_def, Pi.add_apply]; ring

theorem spaceLength_add_le (v w : Fin 3 → ℝ) :
    spaceLength (v + w) ≤ spaceLength v + spaceLength w := by
  have h2 := (abs_le.mp (abs_spaceDot_le v w)).2
  have hv := spaceLength_sq v
  have hw := spaceLength_sq w
  apply le_of_sq_le_sq _ (add_nonneg (spaceLength_nonneg v) (spaceLength_nonneg w))
  rw [spaceLength_sq, spaceSq_add, ← hv, ← hw]
  nlinarith

/-! ### Cross product -/

theorem spaceCross_anticomm (v w : Fin 3 → ℝ) : spaceCross v w = -spaceCross w v := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_self (v : Fin 3 → ℝ) : spaceCross v v = 0 := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_add_left (a b w : Fin 3 → ℝ) :
    spaceCross (a + b) w = spaceCross a w + spaceCross b w := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_add_right (w a b : Fin 3 → ℝ) :
    spaceCross w (a + b) = spaceCross w a + spaceCross w b := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_sub_right (w a b : Fin 3 → ℝ) :
    spaceCross w (a - b) = spaceCross w a - spaceCross w b := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_smul_left (c : ℝ) (v w : Fin 3 → ℝ) :
    spaceCross (c • v) w = c • spaceCross v w := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_smul_right (c : ℝ) (v w : Fin 3 → ℝ) :
    spaceCross v (c • w) = c • spaceCross v w := by
  ext k; fin_cases k <;> simp [spaceCross] <;> ring

theorem spaceCross_zero_right (v : Fin 3 → ℝ) : spaceCross v 0 = 0 := by
  ext k; fin_cases k <;> simp [spaceCross]

theorem spaceDot_cross_self_left (v w : Fin 3 → ℝ) : spaceDot v (spaceCross v w) = 0 := by
  simp only [spaceDot_def, spaceCross_apply_zero, spaceCross_apply_one, spaceCross_apply_two]; ring

theorem spaceDot_cross_self_right (v w : Fin 3 → ℝ) : spaceDot w (spaceCross v w) = 0 := by
  simp only [spaceDot_def, spaceCross_apply_zero, spaceCross_apply_one, spaceCross_apply_two]; ring

end Algebra

section Calculus

/-- The differential of `spaceSq` at `v` is `2 v·`; `spaceDotCLM v` is the functional `w ↦ v·w`. -/
def spaceDotCLM (v : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ k, v k • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k

theorem spaceDotCLM_apply (v w : Fin 3 → ℝ) : spaceDotCLM v w = spaceDot v w := by
  simp [spaceDotCLM, spaceDot]

theorem hasFDerivAt_spaceSq (v : Fin 3 → ℝ) :
    HasFDerivAt spaceSq ((2 : ℝ) • spaceDotCLM v) v := by
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) k).hasFDerivAt (x := v)).pow 2)
  refine h.congr_fderiv ?_
  unfold spaceDotCLM
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext w
  simp [smul_smul]

theorem analyticAt_spaceSq (v : Fin 3 → ℝ) : AnalyticAt ℝ spaceSq v := by
  have h : spaceSq = fun w : Fin 3 → ℝ => w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 :=
    funext fun w => spaceSq_def w
  rw [h]
  have h0 : AnalyticAt ℝ (fun w : Fin 3 → ℝ => w 0) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).analyticAt v
  have h1 : AnalyticAt ℝ (fun w : Fin 3 → ℝ => w 1) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).analyticAt v
  have h2 : AnalyticAt ℝ (fun w : Fin 3 → ℝ => w 2) v :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).analyticAt v
  exact ((h0.pow 2).add (h1.pow 2)).add (h2.pow 2)

theorem analyticAt_spaceLength {v : Fin 3 → ℝ} (hv : v ≠ 0) : AnalyticAt ℝ spaceLength v := by
  have hne : spaceSq v ≠ 0 := fun h => hv (spaceSq_eq_zero_iff.mp h)
  have hpoly : ContDiffAt ℝ ω spaceSq v := by
    have : spaceSq = fun w : Fin 3 → ℝ => w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := funext spaceSq_def
    rw [this]
    have h0 : ContDiff ℝ ω (fun w : Fin 3 → ℝ => w 0) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff
    have h1 : ContDiff ℝ ω (fun w : Fin 3 → ℝ => w 1) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).contDiff
    have h2 : ContDiff ℝ ω (fun w : Fin 3 → ℝ => w 2) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).contDiff
    exact (((h0.pow 2).add (h1.pow 2)).add (h2.pow 2)).contDiffAt
  exact (hpoly.sqrt hne).analyticAt

theorem analyticAt_inv_spaceLength {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    AnalyticAt ℝ (fun w => (spaceLength w)⁻¹) v :=
  (analyticAt_spaceLength hv).inv (spaceLength_pos_iff.mpr hv).ne'

/-- `D |v| h = v·h / |v|`. -/
theorem hasFDerivAt_spaceLength {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    HasFDerivAt spaceLength (((spaceLength v)⁻¹) • spaceDotCLM v) v := by
  have hne : spaceSq v ≠ 0 := fun h => hv (spaceSq_eq_zero_iff.mp h)
  have hpos := spaceLength_pos_iff.mpr hv
  have := (hasFDerivAt_spaceSq v).sqrt hne
  refine this.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  unfold spaceLength
  have : Real.sqrt (spaceSq v) ≠ 0 := hpos.ne'
  field_simp

/-- `D (1/|v|)(v) h = - v·h / |v|³`. -/
theorem hasFDerivAt_inv_spaceLength {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    HasFDerivAt (fun w => (spaceLength w)⁻¹)
      (-((spaceLength v ^ 3)⁻¹) • spaceDotCLM v) v := by
  have hpos := spaceLength_pos_iff.mpr hv
  have h1 := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt v (hasFDerivAt_spaceLength hv)
  refine h1.congr_fderiv ?_
  rw [smul_smul]
  congr 1
  field_simp

theorem continuous_spaceLength : Continuous spaceLength := by
  unfold spaceLength spaceSq
  fun_prop

end Calculus

section Blocks

variable {n : ℕ}

theorem bodyVector3_zero (i : Fin n) : bodyVector3 (0 : Fin (n * 3) → ℝ) i = 0 := rfl

theorem bodyVector3_add (q r : Fin (n * 3) → ℝ) (i : Fin n) :
    bodyVector3 (q + r) i = bodyVector3 q i + bodyVector3 r i := rfl

theorem bodyVector3_smul (c : ℝ) (q : Fin (n * 3) → ℝ) (i : Fin n) :
    bodyVector3 (c • q) i = c • bodyVector3 q i := rfl

/-- Body-wise assembly of a coordinate vector (inverse of `bodyVector3`). -/
def ofBodies3 {N : ℕ} (Q : Fin N → Fin 3 → ℝ) : Fin (N * 3) → ℝ :=
  fun k => Q (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem bodyVector3_ofBodies3 {N : ℕ} (Q : Fin N → Fin 3 → ℝ) (i : Fin N) :
    bodyVector3 (ofBodies3 Q) i = Q i := by
  ext k
  simp [bodyVector3, ofBodies3]

theorem ofBodies3_bodyVector3 {N : ℕ} (q : Fin (N * 3) → ℝ) :
    ofBodies3 (fun i => bodyVector3 q i) = q := by
  ext k
  show q (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = q k
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

/-- Position block of body `i`, as a continuous linear map. -/
def posCLM3 (i : Fin n) : Phase (n * 3) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 3) => ℝ)
      (finProdFinEquiv (i, k))).comp
      (ContinuousLinearMap.fst ℝ (Fin (n * 3) → ℝ) (Fin (n * 3) → ℝ))

/-- Momentum block of body `i`, as a continuous linear map. -/
def momCLM3 (i : Fin n) : Phase (n * 3) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n * 3) => ℝ)
      (finProdFinEquiv (i, k))).comp
      (ContinuousLinearMap.snd ℝ (Fin (n * 3) → ℝ) (Fin (n * 3) → ℝ))

theorem posCLM3_apply (i : Fin n) (z : Phase (n * 3)) : posCLM3 i z = bodyVector3 z.1 i := rfl

theorem momCLM3_apply (i : Fin n) (z : Phase (n * 3)) : momCLM3 i z = bodyVector3 z.2 i := rfl

/-- Curve statement: a `HasDerivAt` into `Phase (n * 3)` is a family of `HasDerivAt` of the body
vectors. -/
theorem hasDerivAt_bodyVector3 {z : ℝ → Phase (n * 3)} {v : Phase (n * 3)} {t : ℝ}
    (h : HasDerivAt z v t) (i : Fin n) :
    HasDerivAt (fun s => bodyVector3 (z s).1 i) (bodyVector3 v.1 i) t ∧
      HasDerivAt (fun s => bodyVector3 (z s).2 i) (bodyVector3 v.2 i) t :=
  ⟨(posCLM3 i).hasFDerivAt.comp_hasDerivAt t h, (momCLM3 i).hasFDerivAt.comp_hasDerivAt t h⟩

end Blocks

end KAM.Planetary.Spatial

end
