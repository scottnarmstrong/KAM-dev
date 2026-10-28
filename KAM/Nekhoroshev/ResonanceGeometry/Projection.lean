/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import KAM.Nekhoroshev.ResonanceGeometry.Lattice

/-!
# Canonical orthogonal projection (`bpN:p8:projection`, `stepN:p8:pr-alg`, `stepN:p8:pr-dist`)

The unique dot-product orthogonal projector `proj V` with range `V`, its characterization, the zero
and nested laws, the real-column matrix formula `A (AᵀA)⁻¹ Aᵀ` for arbitrary independent real
columns, the distance to the orthogonal complement of an arbitrary real subspace, and the lattice
specializations `projection_matrix_lattice` and `projection_distance`.
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
open KAM.Stability
variable {n : ℕ}

theorem euclid_sq_eq_dot (x : Fin n → ℝ) : euclid x ^ 2 = x ⬝ᵥ x := by
  rw [euclid, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [dotProduct, sq]

theorem euclid_nonneg' (x : Fin n → ℝ) : 0 ≤ euclid x := Real.sqrt_nonneg _

theorem euclid_le_of_sq_le {x : Fin n → ℝ} {b : ℝ} (hb : 0 ≤ b) (h : euclid x ^ 2 ≤ b ^ 2) :
    euclid x ≤ b :=
  (pow_le_pow_iff_left₀ (euclid_nonneg' x) hb two_ne_zero).1 h

/-- The complement of an orthogonal projector with range fixed is orthogonal to the range. -/
theorem orthProj_perp {V : Submodule ℝ (Fin n → ℝ)} {P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hP : IsOrthProj P) (hid : ∀ v ∈ V, P v = v) (v : Fin n → ℝ) {w : Fin n → ℝ} (hw : w ∈ V) :
    (v - P v) ⬝ᵥ w = 0 := by
  rw [sub_dotProduct, hP.symm, hid w hw, sub_self]

/-- A vector of `V` orthogonal to `V` is zero. -/
theorem eq_zero_of_mem_of_perp {V : Submodule ℝ (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ V)
    (h : ∀ w ∈ V, x ⬝ᵥ w = 0) : x = 0 :=
  dotProduct_self_eq_zero.1 (h x hx)

/-- Well-defined canonical projection: unique orthogonal projector with prescribed range. -/
theorem projection_exists_unique (V : Submodule ℝ (Fin n → ℝ)) :
    ∃! P : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      IsOrthProj P ∧ (∀ v, P v ∈ V) ∧ (∀ v ∈ V, P v = v) := by
  obtain ⟨P, hP, hPV, hPid⟩ := exists_orthProj V
  refine ⟨P, ⟨hP, hPV, hPid⟩, ?_⟩
  rintro Q ⟨hQ, hQV, hQid⟩
  refine LinearMap.ext fun v => ?_
  have hz : Q v - P v = 0 := by
    refine eq_zero_of_mem_of_perp (V.sub_mem (hQV v) (hPV v)) fun w hw => ?_
    have : (Q v - P v) = (v - P v) - (v - Q v) := by abel
    rw [this, sub_dotProduct, orthProj_perp hP hPid v hw, orthProj_perp hQ hQid v hw, sub_zero]
  exact sub_eq_zero.1 hz

def proj (V : Submodule ℝ (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Classical.choose (ExistsUnique.exists (projection_exists_unique V))

def compProj (V : Submodule ℝ (Fin n → ℝ)) (v : Fin n → ℝ) : Fin n → ℝ := v - proj V v

theorem proj_spec (V : Submodule ℝ (Fin n → ℝ)) :
    IsOrthProj (proj V) ∧ (∀ v, proj V v ∈ V) ∧ (∀ v ∈ V, proj V v = v) :=
  Classical.choose_spec (ExistsUnique.exists (projection_exists_unique V))

theorem proj_eq_of_perp (V : Submodule ℝ (Fin n → ℝ)) (v w : Fin n → ℝ) (hw : w ∈ V)
    (h : ∀ u ∈ V, (v - w) ⬝ᵥ u = 0) : w = proj V v := by
  obtain ⟨hP, hPV, hPid⟩ := proj_spec V
  have hz : w - proj V v = 0 := by
    refine eq_zero_of_mem_of_perp (V.sub_mem hw (hPV v)) fun u hu => ?_
    have : w - proj V v = (v - proj V v) - (v - w) := by abel
    rw [this, sub_dotProduct, orthProj_perp hP hPid v hu, h u hu, sub_zero]
  exact sub_eq_zero.1 hz

theorem projection (V : Submodule ℝ (Fin n → ℝ)) :
    IsOrthProj (proj V) ∧
    (∀ v, proj V v ∈ V) ∧ (∀ v ∈ V, proj V v = v) ∧
    (∀ v w, w ∈ V → compProj V v ⬝ᵥ w = 0) ∧
    (∀ v, euclid v ^ 2 = euclid (proj V v) ^ 2 + euclid (compProj V v) ^ 2) ∧
    (∀ v, euclid (proj V v) ≤ euclid v ∧ euclid (compProj V v) ≤ euclid v) ∧
    (∀ v w, w ∈ V → (∀ u ∈ V, (v - w) ⬝ᵥ u = 0) → w = proj V v) ∧
    (∀ V' : Submodule ℝ (Fin n → ℝ), V ≤ V' → ∀ v,
      proj V' (proj V v) = proj V v ∧ proj V (proj V' v) = proj V v) := by
  obtain ⟨hP, hPV, hPid⟩ := proj_spec V
  have hperp : ∀ v w, w ∈ V → compProj V v ⬝ᵥ w = 0 := fun v w hw =>
    orthProj_perp hP hPid v hw
  have hpyth : ∀ v, euclid v ^ 2 = euclid (proj V v) ^ 2 + euclid (compProj V v) ^ 2 := by
    intro v
    have h0 : proj V v ⬝ᵥ compProj V v = 0 := by
      rw [dotProduct_comm]; exact hperp v _ (hPV v)
    have hv : v = proj V v + compProj V v := by simp [compProj]
    rw [euclid_sq_eq_dot, euclid_sq_eq_dot, euclid_sq_eq_dot]
    conv_lhs => rw [hv]
    rw [add_dotProduct, dotProduct_add, dotProduct_add, h0, dotProduct_comm (compProj V v), h0]
    ring
  refine ⟨hP, hPV, hPid, hperp, hpyth, fun v => ⟨?_, ?_⟩, proj_eq_of_perp V, ?_⟩
  · refine euclid_le_of_sq_le (euclid_nonneg' v) ?_
    rw [hpyth v]; nlinarith [sq_nonneg (euclid (compProj V v))]
  · refine euclid_le_of_sq_le (euclid_nonneg' v) ?_
    rw [hpyth v]; nlinarith [sq_nonneg (euclid (proj V v))]
  · intro V' hV v
    obtain ⟨-, -, hP'id⟩ := proj_spec V'
    refine ⟨hP'id _ (hV (hPV v)), ?_⟩
    symm
    refine proj_eq_of_perp V _ _ (hPV v) fun u hu => ?_
    obtain ⟨hP', -, hP'id⟩ := proj_spec V'
    have : proj V' v - proj V v = (v - proj V v) - (v - proj V' v) := by abel
    rw [this, sub_dotProduct, orthProj_perp hP hPid v hu, orthProj_perp hP' hP'id v (hV hu),
      sub_zero]

theorem projection_zero : proj (⊥ : Submodule ℝ (Fin n → ℝ)) = 0 := by
  refine LinearMap.ext fun v => ?_
  simpa using (proj_spec (⊥ : Submodule ℝ (Fin n → ℝ))).2.1 v

def resonanceDistance (Λ : Lattice n) (w : Fin n → ℝ) : ℝ :=
  euclid (proj (lattice Λ) w)

/-- Distance to the dot-orthogonal complement of an arbitrary real subspace. -/
theorem projection_distance_subspace (V : Submodule ℝ (Fin n → ℝ)) (w : Fin n → ℝ) :
    (∀ v ∈ V, v ⬝ᵥ compProj V w = 0) ∧
    euclid (w - compProj V w) = euclid (proj V w) ∧
    (∀ u : Fin n → ℝ, (∀ v ∈ V, v ⬝ᵥ u = 0) →
      euclid (proj V w) ≤ euclid (w - u)) := by
  obtain ⟨hP, hPV, hPid, hperp, -⟩ := projection V
  have h1 : ∀ v ∈ V, v ⬝ᵥ compProj V w = 0 := fun v hv => by
    rw [dotProduct_comm]; exact hperp w v hv
  refine ⟨h1, by simp [compProj], fun u hu => ?_⟩
  refine euclid_le_of_sq_le (euclid_nonneg' _) ?_
  have h0 : proj V w ⬝ᵥ (compProj V w - u) = 0 := by
    rw [dotProduct_sub, h1 _ (hPV w), hu _ (hPV w), sub_zero]
  have hw : w - u = proj V w + (compProj V w - u) := by simp only [compProj]; abel
  have hpy : euclid (w - u) ^ 2 = euclid (proj V w) ^ 2 + euclid (compProj V w - u) ^ 2 := by
    rw [euclid_sq_eq_dot, euclid_sq_eq_dot, euclid_sq_eq_dot]
    conv_lhs => rw [hw]
    rw [add_dotProduct, dotProduct_add, dotProduct_add, h0, dotProduct_comm (compProj V w - u), h0]
    ring
  rw [hpy]
  nlinarith [sq_nonneg (euclid (compProj V w - u))]

theorem projection_distance (Λ : Lattice n) (w : Fin n → ℝ) :
    compProj (lattice Λ) w ∈ resonance Λ ∧
    euclid (w - compProj (lattice Λ) w) = resonanceDistance Λ w ∧
    (∀ u ∈ resonance Λ, resonanceDistance Λ w ≤ euclid (w - u)) ∧
    Module.finrank ℝ (lattice Λ) +
      Module.finrank ℝ (LinearMap.ker (proj (lattice Λ))) = n := by
  obtain ⟨h1, h2, h3⟩ := projection_distance_subspace (lattice Λ) w
  have hres := (lattice_resonance Λ).1
  refine ⟨?_, h2, fun u hu => h3 u ?_, ?_⟩
  · rw [hres]; exact fun v hv => h1 v hv
  · rw [hres] at hu; exact hu
  · have hr : LinearMap.range (proj (lattice Λ)) = lattice Λ := by
      refine le_antisymm ?_ fun v hv => ⟨v, (proj_spec _).2.2 v hv⟩
      rintro _ ⟨v, rfl⟩
      exact (proj_spec _).2.1 v
    have := LinearMap.finrank_range_add_finrank_ker (proj (lattice Λ))
    rwa [hr, Module.finrank_fin_fun] at this

/-- Real-column formula for every real span, including the empty-column case. -/
theorem projection_matrix {d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : LinearIndependent ℝ (fun j => fun i => A i j)) :
    ∀ v : Fin n → ℝ,
      proj (Submodule.span ℝ (Set.range (fun j => fun i => A i j))) v =
        (A * (A.transpose * A)⁻¹ * A.transpose).mulVec v := by
  intro v
  set V := Submodule.span ℝ (Set.range (fun j => fun i => A i j)) with hV
  have hmvEq : ∀ x : Fin d → ℝ, A.mulVec x = ∑ j, x j • (fun i => A i j) := fun x => by
    ext i; simp [Matrix.mulVec, dotProduct, mul_comm]
  have hmv : ∀ x : Fin d → ℝ, A.mulVec x ∈ V := fun x => by
    rw [hmvEq]
    exact V.sum_mem fun j _ => V.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have hmem : ∀ w ∈ V, ∃ x, A.mulVec x = w := fun w hw => by
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec_single]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, rfl⟩ := hy; obtain ⟨b, rfl⟩ := hz; exact ⟨a + b, by simp [Matrix.mulVec_add]⟩
    | smul c y _ hy =>
      obtain ⟨a, rfl⟩ := hy; exact ⟨c • a, by simp [Matrix.mulVec_smul]⟩
  have hdot : ∀ (x : Fin d → ℝ) (y : Fin n → ℝ), x ⬝ᵥ (A.transpose *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hker : ∀ x, (A.transpose * A) *ᵥ x = 0 → x = 0 := by
    intro x hx
    have h0 : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = 0 := by
      have hx' : A.transpose *ᵥ (A *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec]; exact hx
      rw [← hdot x (A *ᵥ x), hx', dotProduct_zero]
    have hAx : A *ᵥ x = 0 := dotProduct_self_eq_zero.1 h0
    rw [hmvEq] at hAx
    funext j
    exact Fintype.linearIndependent_iff.1 hA x hAx j
  have hinj : Function.Injective (A.transpose * A).mulVec := by
    intro x y h
    have : (A.transpose * A) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
    exact sub_eq_zero.1 (hker _ this)
  have hG : IsUnit (A.transpose * A).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)
  set G := A.transpose * A with hGdef
  have hGG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hG
  have hform : (A * G⁻¹ * A.transpose).mulVec v = A *ᵥ (G⁻¹ *ᵥ (A.transpose *ᵥ v)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hform]
  symm
  refine proj_eq_of_perp V v _ (hmv _) fun u hu => ?_
  obtain ⟨x, rfl⟩ := hmem u hu
  rw [dotProduct_comm, ← hdot, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  have : A.transpose * A * G⁻¹ = 1 := by
    rw [← hGdef]; exact hGG
  have hGG' : A.transpose * A * G⁻¹ = 1 := hGG
  rw [Matrix.mulVec_mulVec, hGG', Matrix.one_mulVec, sub_self, dotProduct_zero]

/-- Lattice specialization of the real-column formula. -/
theorem projection_matrix_lattice {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    let A := (basisMatrix b).map (Int.castRingHom ℝ)
    ∀ v, proj (lattice Λ) v = (A * (A.transpose * A)⁻¹ * A.transpose).mulVec v := by
  intro A v
  have hcol : (fun j => fun i => A i j) = fun j => integerReal (b j).val := by
    funext j i; simp [A, basisMatrix, integerReal]
  have h := projection_matrix A (by rw [hcol]; exact basis_real_linearIndependent b) v
  rw [hcol, basis_span_eq] at h
  exact h

end KAM.Nekhoroshev
