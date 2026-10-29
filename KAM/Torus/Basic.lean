/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Defs.DotC
public import KAM.Frozen.Defs.TorsionAverage
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Matrix.Norms
public import KAM.Strip.Averages
public import KAM.Strip.Bridges
public import KAM.Strip.Periodic
public import KAM.Strip.Limits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Carriers for Parts 2 and 3: the isometry `ℂⁿ × ℂⁿ ≃ ℂ^{n ⊕ n}`, predicates, averages

The frozen definitions use pairs `(Fin n → ℂ) × (Fin n → ℂ)` as phase points, while the matrix
layer of Part 1 indexes `2n × 2n` matrices by `Fin n ⊕ Fin n`. This file fixes the dictionary.

* `KAM.Torus.sumVec`: the linear equivalence `(a, b) ↦ Sum.elim a b`, isometric for the max
  norms (`KAM.Torus.norm_sumVec`).
* `KAM.Torus.colMat`, `KAM.Torus.sqMat`: the matrices of a linear map `ℂ^q → ℂⁿ × ℂⁿ` and of an
  endomorphism of `ℂⁿ × ℂⁿ`, with `norm_colMat`, `norm_sqMat` (operator norm = row-sum norm) and
  `colMat_mulVec`, `sqMat_mulVec`.
* `KAM.Torus.fderiv_sumVec_apply`, `KAM.Torus.dotℂ_eq_dotProduct_sumVec`: `sumVec` commutes with
  `fderiv`, and the frozen bilinear dot product is the dot product of the `sumVec`-images.
* `KAM.Torus.IsPeriodicOn`, `IsRealVec`, `IsRealMat`, `avg`: the shared hypothesis forms of
  periodicity, realness and averaging.
* `KAM.Torus.cauchy_transpose_fintype`: the Cauchy estimate for the transposed Jacobian of a
  map into `ι → ℂ`, for any finite index type `ι`.
* `KAM.Torus.primary_coordinatewise` and `KAM.Torus.isRealVec_sumVec_iff`: conversions from the
  frozen `IsPrimaryOnStrip` and `IsRealOnReals`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology


namespace KAM.Torus

variable {n : ℕ}

/-- `ℂⁿ × ℂⁿ ≃ ℂ^{n ⊕ n}`, `(a, b) ↦ Sum.elim a b`; isometric for the max norms. -/
def sumVec (n : ℕ) : ((Fin n → ℂ) × (Fin n → ℂ)) ≃ₗ[ℂ] (Fin n ⊕ Fin n → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℂ ℂ).symm

theorem sumVec_apply (u : (Fin n → ℂ) × (Fin n → ℂ)) : sumVec n u = Sum.elim u.1 u.2 := rfl

theorem norm_sumVec (u : (Fin n → ℂ) × (Fin n → ℂ)) : ‖sumVec n u‖ = ‖u‖ := by
  rw [sumVec_apply, Prod.norm_def]
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 ?_)
    (max_le ?_ ?_)
  · rintro (i | i)
    · exact (norm_le_pi_norm u.1 i).trans (le_max_left _ _)
    · exact (norm_le_pi_norm u.2 i).trans (le_max_right _ _)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
      norm_le_pi_norm (Sum.elim u.1 u.2) (Sum.inl i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
      norm_le_pi_norm (Sum.elim u.1 u.2) (Sum.inr i)

/-- `sumVec` as a linear isometry equivalence, used to transport operator norms. -/
def sumVecIso (n : ℕ) : ((Fin n → ℂ) × (Fin n → ℂ)) ≃ₗᵢ[ℂ] (Fin n ⊕ Fin n → ℂ) :=
  { sumVec n with norm_map' := norm_sumVec }

@[simp] theorem sumVecIso_apply (u : (Fin n → ℂ) × (Fin n → ℂ)) : sumVecIso n u = sumVec n u :=
  rfl

@[simp] theorem sumVec_symm_apply_sumVec (u : (Fin n → ℂ) × (Fin n → ℂ)) :
    (sumVec n).symm (sumVec n u) = u := (sumVec n).symm_apply_apply u

/-- The `2n × q` matrix (rows `Fin n ⊕ Fin n`) of a linear map `ℂ^q → ℂⁿ × ℂⁿ`. -/
def colMat {q : ℕ} (U : (Fin q → ℂ) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin q) ℂ :=
  LinearMap.toMatrix' ((sumVec n).toLinearMap ∘ₗ (U : (Fin q → ℂ) →ₗ[ℂ] _))

/-- The `2n × 2n` matrix of a linear map `ℂⁿ × ℂⁿ → ℂⁿ × ℂⁿ`. -/
def sqMat (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  LinearMap.toMatrix' ((sumVec n).toLinearMap ∘ₗ
    (U : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] _) ∘ₗ (sumVec n).symm.toLinearMap)

theorem norm_colMat {q : ℕ} (U : (Fin q → ℂ) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖colMat U‖ = ‖U‖ := by
  set L : (Fin q → ℂ) →L[ℂ] (Fin n ⊕ Fin n → ℂ) :=
    (sumVecIso n).toLinearIsometry.toContinuousLinearMap.comp U with hL
  have hmat : colMat U = LinearMap.toMatrix' (L : (Fin q → ℂ) →ₗ[ℂ] _) := rfl
  rw [hmat, ← norm_continuousLinearMap_eq_norm_toMatrix', hL,
    LinearIsometry.norm_toContinuousLinearMap_comp]

theorem colMat_mulVec {q : ℕ} (U : (Fin q → ℂ) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ))
    (v : Fin q → ℂ) : colMat U *ᵥ v = sumVec n (U v) := by
  rw [colMat, LinearMap.toMatrix'_mulVec]
  rfl

theorem norm_sqMat (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) :
    ‖sqMat U‖ = ‖U‖ := by
  set L : (Fin n ⊕ Fin n → ℂ) →L[ℂ] (Fin n ⊕ Fin n → ℂ) :=
    (sumVecIso n).toLinearIsometry.toContinuousLinearMap.comp
      (U.comp (sumVecIso n).symm.toLinearIsometry.toContinuousLinearMap) with hL
  have hmat : sqMat U = LinearMap.toMatrix' (L : (Fin n ⊕ Fin n → ℂ) →ₗ[ℂ] _) := rfl
  rw [hmat, ← norm_continuousLinearMap_eq_norm_toMatrix', hL,
    LinearIsometry.norm_toContinuousLinearMap_comp]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv U (sumVecIso n).symm

theorem sqMat_mulVec (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ))
    (u : (Fin n → ℂ) × (Fin n → ℂ)) : sqMat U *ᵥ sumVec n u = sumVec n (U u) := by
  rw [sqMat, LinearMap.toMatrix'_mulVec]
  simp

/-- Coordinatewise `1`-periodicity on `T_r`: the hypothesis form of `KAM.averages`,
`KAM.periodic_bounded`, `KAM.periodic_int_shift` (Part 1). -/
def IsPeriodicOn {F : Type*} (u : (Fin n → ℂ) → F) (r : ℝ) : Prop :=
  ∀ (i : Fin n) z, z ∈ complexStrip n r → u (z + Pi.single i 1) = u z

/-- A vector-valued function is real at real points. -/
def IsRealVec {ι : Type*} (u : (Fin n → ℂ) → ι → ℂ) : Prop :=
  ∀ (x : Fin n → ℝ) (i : ι), (u (fun j => (x j : ℂ)) i).im = 0

/-- A matrix-valued function is real at real points. -/
def IsRealMat {ι κ : Type*} (u : (Fin n → ℂ) → Matrix ι κ ℂ) : Prop :=
  ∀ (x : Fin n → ℝ) (i : ι) (j : κ), (u (fun l => (x l : ℂ)) i j).im = 0

/-- The average `⟨u⟩ = ∫_{[0,1]ⁿ} u` over the real torus of a function on a strip. -/
abbrev avg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (u : (Fin n → ℂ) → F) : F :=
  torusAverage (fun x : Fin n → ℝ => u (fun i => (x i : ℂ)))

/-- Index-type bridge for `KAM.cauchy_corollaries_transpose` (stated there for `Fin p → ℂ`):
the transposed Jacobian of a `ι → ℂ`-valued map, `ι` any finite type (here `Fin n ⊕ Fin n`). -/
theorem cauchy_transpose_fintype {ι : Type*} [Fintype ι] {ρ δ A : ℝ}
    {f : (Fin n → ℂ) → ι → ℂ} (hf : DifferentiableOn ℂ f (complexStrip n ρ))
    (hA : ∀ θ ∈ complexStrip n ρ, ‖f θ‖ ≤ A) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖(Matrix.of fun (i : ι) (ℓ : Fin n) => fderiv ℂ f θ (Pi.single ℓ 1) i)ᵀ‖ ≤
        Fintype.card ι * δ⁻¹ * A := by
  intro θ hθ
  have hsub : complexStrip n (ρ - δ) ⊆ complexStrip n ρ := fun θ hθ i =>
    (hθ i).trans (by linarith)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA θ (hsub hθ))
  refine (norm_le_iff_forall_rowSum (by positivity)).2 fun ℓ => ?_
  have hcoord : ‖fderiv ℂ f θ (Pi.single ℓ 1)‖ ≤ δ⁻¹ * A :=
    (cauchy_strip hf hA hδ).1 ℓ θ hθ
  calc ∑ i : ι, ‖(Matrix.of fun (i : ι) (ℓ : Fin n) =>
          fderiv ℂ f θ (Pi.single ℓ 1) i)ᵀ ℓ i‖
      = ∑ i : ι, ‖fderiv ℂ f θ (Pi.single ℓ 1) i‖ := rfl
    _ ≤ ∑ _i : ι, ‖fderiv ℂ f θ (Pi.single ℓ 1)‖ :=
        Finset.sum_le_sum fun i _ => norm_le_pi_norm _ i
    _ = Fintype.card ι * ‖fderiv ℂ f θ (Pi.single ℓ 1)‖ := by simp
    _ ≤ Fintype.card ι * (δ⁻¹ * A) := by gcongr
    _ = Fintype.card ι * δ⁻¹ * A := by ring

/-- A primary torus is coordinatewise quasi-periodic: shifting an angle by `e_i` shifts the
phase point by `(e_i, 0)`. This is `IsPrimaryOnStrip` for the generators of `ℤⁿ`. -/
theorem primary_coordinatewise {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}
    (hK : IsPrimaryOnStrip K r) (i : Fin n) {z : Fin n → ℂ} (hz : z ∈ complexStrip n r) :
    K (z + Pi.single i 1) = K z + (Pi.single i 1, 0) := by
  have hcast : (fun j => ((Pi.single i (1 : ℤ) : Fin n → ℤ) j : ℂ)) = Pi.single i 1 := by
    ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  simpa only [hcast] using hK z hz (Pi.single i 1)

/-- Realness of `IsRealOnReals` (frozen) in the form `IsRealVec` for the `sumVec`-image. -/
theorem isRealVec_sumVec_iff {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} :
    IsRealVec (fun θ => sumVec n (K θ)) ↔ IsRealOnReals K := by
  rw [isRealOnReals_iff_im]
  constructor
  · intro h θ i
    exact ⟨h θ (Sum.inl i), h θ (Sum.inr i)⟩
  · rintro h θ (i | i)
    · exact (h θ i).1
    · exact (h θ i).2

/-! ### `sumVec` and the frozen operations -/

section FrozenOps

/-- The frozen bilinear dot product on `ℂⁿ × ℂⁿ` is the dot product of the `sumVec`-images. -/
theorem dotℂ_eq_dotProduct_sumVec (u v : (Fin n → ℂ) × (Fin n → ℂ)) :
    dotℂ u v = sumVec n u ⬝ᵥ sumVec n v := by
  simp [dotℂ, dotProduct, Fintype.sum_sum_type, sumVec_apply, Finset.sum_add_distrib]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableAt_sumVec_iff {f : E → (Fin n → ℂ) × (Fin n → ℂ)} {x : E} :
    DifferentiableAt ℂ (fun y => sumVec n (f y)) x ↔ DifferentiableAt ℂ f x :=
  (sumVecIso n).comp_differentiableAt_iff

/-- `sumVec` is a linear isometry equivalence, so it commutes with the derivative:
`D (sumVec ∘ f) v = sumVec (D f v)`, with no differentiability hypothesis. -/
theorem fderiv_sumVec_apply (f : E → (Fin n → ℂ) × (Fin n → ℂ)) (x v : E) :
    fderiv ℂ (fun y => sumVec n (f y)) x v = sumVec n (fderiv ℂ f x v) :=
  congrArg (fun L => L v) ((sumVecIso n).comp_fderiv (f := f) (x := x))

end FrozenOps

end KAM.Torus

end
