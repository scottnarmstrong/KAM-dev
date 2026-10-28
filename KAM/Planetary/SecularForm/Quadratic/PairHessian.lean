/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Quadratic.PairDiag
public import KAM.Planetary.SecularForm.CrossJet

/-!
# Quadratic part: the Hessian of the pair average

Blueprint P, Part 8, `stepP:p8:qf-pair` and `stepP:p8:qf-assembly` (package S8-Q). A `C²` function
of `(u, v) ∈ ℝ² × ℝ²` that is invariant (near `0`) under the reflection `η ↦ -η` and the quarter
turn of both planets, whose second derivatives along the rays `(s u, 0)`, `(0, s v)` are
`2 cᵢ |u|²`, `2 cⱼ |v|²` and whose mixed derivative `∂ₛ∂ₜ G(s e₀, t e₀)` is `2 c`, has second
derivative `2 cᵢ|u|² + 2 cⱼ|v|² + 4 c u·v` along every ray (the quadratic invariants of two planar
vectors, derived here by hand from the two symmetries).
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology
namespace KAM.Planetary
open KAM KAM.Kepler
namespace SecularForm
variable {n : ℕ}

/-- The embedding `y ↦ ((y₀, 0), (y₁, 0))` of the cross slice. -/
def crossSlice : Vec 2 →L[ℝ] Vec 2 × Vec 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => (![y 0, 0], ![y 1, 0])
      map_add' := fun y z => by
        refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp
      map_smul' := fun c y => by
        refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp }

theorem crossSlice_apply (y : Vec 2) : crossSlice y = (![y 0, 0], ![y 1, 0]) := rfl

section Generic
variable {G : Vec 2 × Vec 2 → ℝ}

/-- The mixed second derivative along the cross slice is the Hessian form of `G`. -/
theorem hessian_cross (hC : ContDiffAt ℝ 2 G 0) :
    iteratedFDeriv ℝ 2 (fun y : Vec 2 => G (crossSlice y)) 0 ![Pi.single 0 1, Pi.single 1 1] =
      fderiv ℝ (fderiv ℝ G) 0 (crossSlice (Pi.single 0 1)) (crossSlice (Pi.single 1 1)) := by
  have hGs : ContDiffAt ℝ 2 (fun y : Vec 2 => G (crossSlice y)) 0 :=
    (show ContDiffAt ℝ 2 G (crossSlice 0) by rwa [map_zero]).comp (0 : Vec 2)
      crossSlice.contDiff.contDiffAt
  have hs1 := hC.isSymmSndFDerivAt (by simp)
  have hs2 := hGs.isSymmSndFDerivAt (by simp)
  have hray : ∀ y : Vec 2, fderiv ℝ (fderiv ℝ fun y : Vec 2 => G (crossSlice y)) 0 y y =
      fderiv ℝ (fderiv ℝ G) 0 (crossSlice y) (crossSlice y) := by
    intro y
    rw [← iteratedDeriv_two_ray hGs y, ← iteratedDeriv_two_ray hC (crossSlice y)]
    congr 1; funext s; simp [map_smul]
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h := hray (Pi.single 0 1 + Pi.single 1 1)
  have h0 := hray (Pi.single 0 1)
  have h1 := hray (Pi.single 1 1)
  simp only [map_add, add_apply] at h
  have a1 := hs1 (crossSlice (Pi.single 0 1)) (crossSlice (Pi.single 1 1))
  have a2 := hs2 (Pi.single 0 1) (Pi.single 1 1)
  linarith

theorem pairReflect_smul (s : ℝ) (w : Vec 2 × Vec 2) :
    pairReflect (s • w) = s • pairReflect w := by
  unfold pairReflect
  refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp

theorem pairQuarter_smul (s : ℝ) (w : Vec 2 × Vec 2) :
    pairQuarter (s • w) = s • pairQuarter w := by
  unfold pairQuarter
  refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp

/-- The Hessian form of a symmetric pair function, from the diagonal, cross and symmetry data. -/
theorem hessian_pair_form (hC : ContDiffAt ℝ 2 G 0) (ci cj cf : ℝ)
    (hd1 : ∀ u : Vec 2, iteratedDeriv 2 (fun s : ℝ => G (s • (u, 0))) 0 = 2 * ci * planeSq u)
    (hd2 : ∀ v : Vec 2, iteratedDeriv 2 (fun s : ℝ => G (s • ((0 : Vec 2), v))) 0 =
      2 * cj * planeSq v)
    (hx : iteratedFDeriv ℝ 2 (fun y : Vec 2 => G (crossSlice y)) 0
      ![Pi.single 0 1, Pi.single 1 1] = 2 * cf)
    (hrefl : ∀ᶠ w in 𝓝 (0 : Vec 2 × Vec 2), G (pairReflect w) = G w)
    (hquart : ∀ᶠ w in 𝓝 (0 : Vec 2 × Vec 2), G (pairQuarter w) = G w) (w : Vec 2 × Vec 2) :
    iteratedDeriv 2 (fun s : ℝ => G (s • w)) 0 =
      2 * ci * planeSq w.1 + 2 * cj * planeSq w.2 + 4 * cf * planeDot w.1 w.2 := by
  set H := fderiv ℝ (fderiv ℝ G) 0 with hH
  have hs : ∀ v w, H v w = H w v := hC.isSymmSndFDerivAt (by simp)
  have hA : ∀ w, iteratedDeriv 2 (fun s : ℝ => G (s • w)) 0 = H w w := fun w =>
    iteratedDeriv_two_ray hC w
  have hsm : Tendsto (fun s : ℝ => s • w) (𝓝 0) (𝓝 0) := by
    have : Continuous fun s : ℝ => s • w := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hsmL : ∀ w : Vec 2 × Vec 2, Tendsto (fun s : ℝ => s • w) (𝓝 0) (𝓝 0) := fun w => by
    have : Continuous fun s : ℝ => s • w := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hrf : ∀ w, H (pairReflect w) (pairReflect w) = H w w := by
    intro w
    rw [← hA, ← hA]
    refine Filter.EventuallyEq.iteratedDeriv_eq 2 ?_
    filter_upwards [(hsmL w).eventually hrefl] with s hs
    rw [← pairReflect_smul]; exact hs
  have hqt : ∀ w, H (pairQuarter w) (pairQuarter w) = H w w := by
    intro w
    rw [← hA, ← hA]
    refine Filter.EventuallyEq.iteratedDeriv_eq 2 ?_
    filter_upwards [(hsmL w).eventually hquart] with s hs
    rw [← pairQuarter_smul]; exact hs
  have hcross := hessian_cross hC
  rw [hx] at hcross
  set a0 : Vec 2 × Vec 2 := (![1, 0], 0) with ha0
  set a1 : Vec 2 × Vec 2 := (![0, 1], 0) with ha1
  set b0 : Vec 2 × Vec 2 := (0, ![1, 0]) with hb0
  set b1 : Vec 2 × Vec 2 := (0, ![0, 1]) with hb1
  have hd1' : ∀ u : Vec 2, H (u, 0) (u, 0) = 2 * ci * planeSq u := fun u => by
    rw [← hA]; exact hd1 u
  have hd2' : ∀ v : Vec 2, H (0, v) (0, v) = 2 * cj * planeSq v := fun v => by
    rw [← hA]; exact hd2 v
  have hps : ∀ u : Vec 2, planeSq u = u 0 ^ 2 + u 1 ^ 2 := fun u => by
    simp [planeSq, Fin.sum_univ_two]
  have e00 : H a0 a0 = 2 * ci := by simpa [hps] using hd1' ![1, 0]
  have e11 : H a1 a1 = 2 * ci := by simpa [hps] using hd1' ![0, 1]
  have e01 : H a0 a1 = 0 := by
    have h := hd1' ![1, 1]
    have : ((![1, 1] : Vec 2), (0 : Vec 2)) = a0 + a1 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [ha0, ha1]
    rw [this] at h
    simp only [map_add, add_apply, hps] at h
    have := hs a1 a0
    simp at h
    linarith
  have f00 : H b0 b0 = 2 * cj := by simpa [hps] using hd2' ![1, 0]
  have f11 : H b1 b1 = 2 * cj := by simpa [hps] using hd2' ![0, 1]
  have f01 : H b0 b1 = 0 := by
    have h := hd2' ![1, 1]
    have : ((0 : Vec 2), (![1, 1] : Vec 2)) = b0 + b1 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [hb0, hb1]
    rw [this] at h
    simp only [map_add, add_apply, hps] at h
    have := hs b1 b0
    simp at h
    linarith
  have g00 : H a0 b0 = 2 * cf := by
    have e0 : crossSlice (Pi.single 0 1) = a0 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [crossSlice_apply, ha0]
    have e1 : crossSlice (Pi.single 1 1) = b0 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [crossSlice_apply, hb0]
    rw [e0, e1] at hcross
    exact hcross.symm
  have g01 : H a0 b1 = 0 := by
    have := hrf (a0 + b1)
    have hr : pairReflect (a0 + b1) = a0 + (-1 : ℝ) • b1 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [pairReflect, ha0, hb1]
    rw [hr] at this
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at this
    have := hs b1 a0
    linarith
  have g10 : H a1 b0 = 0 := by
    have := hrf (a1 + b0)
    have hr : pairReflect (a1 + b0) = (-1 : ℝ) • a1 + b0 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [pairReflect, ha1, hb0]
    rw [hr] at this
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at this
    have := hs b0 a1
    linarith
  have g11 : H a1 b1 = 2 * cf := by
    have := hqt (a0 + b0)
    have hr : pairQuarter (a0 + b0) = a1 + b1 := by
      refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [pairQuarter, ha0, ha1, hb0, hb1]
    rw [hr] at this
    simp only [map_add, add_apply] at this
    have := hs b1 a1
    have := hs b0 a0
    linarith
  have hw : w = w.1 0 • a0 + w.1 1 • a1 + w.2 0 • b0 + w.2 1 • b1 := by
    refine Prod.ext ?_ ?_ <;> ext k <;> fin_cases k <;> simp [ha0, ha1, hb0, hb1]
  rw [hA]
  conv_lhs => rw [hw]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hps]
  have s01 := hs a1 a0
  have s02 := hs b0 a0
  have s03 := hs b1 a0
  have s12 := hs b0 a1
  have s13 := hs b1 a1
  have s23 := hs b1 b0
  rw [s01, s02, s03, s12, s13, s23, e00, e11, e01, f00, f11, f01, g00, g01, g10, g11]
  simp [planeDot, Fin.sum_univ_two]
  ring

end Generic

end SecularForm
end KAM.Planetary
end
