/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Block
public import KAM.Nekhoroshev.ResonanceGeometry.Lattice
public import KAM.Nekhoroshev.ResonanceGeometry.Projection

/-!
# Lattice volume (`bpN:p8:volume-def`, `bpN:p8:lattice-volume`)

The covolume `volume_def Λ = √(det Gram)` of an integer lattice, its independence of the basis,
integrality of its square, monotonicity along equal-rank sublattices, the index formula, the
Schur-complement formula for adding a vector, and the cyclic and Hadamard companions.
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
open KAM.Stability
variable {n : ℕ}

def gram {d : ℕ} (A : Matrix (Fin n) (Fin d) ℤ) : Matrix (Fin d) (Fin d) ℝ :=
  (A.map (Int.castRingHom ℝ)).transpose * A.map (Int.castRingHom ℝ)

def volume_def (Λ : Lattice n) : ℝ :=
  Real.sqrt (gram (basisMatrix (latticeBasis Λ))).det

section Gram
variable {d : ℕ}

theorem gram_eq_map (A : Matrix (Fin n) (Fin d) ℤ) :
    gram A = (A.transpose * A).map (Int.castRingHom ℝ) := by
  ext i j
  simp [gram, Matrix.mul_apply]

theorem gram_det_eq (A : Matrix (Fin n) (Fin d) ℤ) :
    (gram A).det = (((A.transpose * A).det : ℤ) : ℝ) := by
  rw [gram_eq_map]
  exact (RingHom.map_det (Int.castRingHom ℝ) _).symm

theorem gramZ_det_mul (A : Matrix (Fin n) (Fin d) ℤ) (N : Matrix (Fin d) (Fin d) ℤ) :
    ((A * N).transpose * (A * N)).det = N.det ^ 2 * (A.transpose * A).det := by
  have : (A * N).transpose * (A * N) = N.transpose * (A.transpose * A) * N := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

theorem gramZ_det_pos {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    0 < ((basisMatrix b).transpose * basisMatrix b).det := by
  have h : 0 < (gram (basisMatrix b)).det := by
    set A := (basisMatrix b).map (Int.castRingHom ℝ) with hA
    have hinj : Function.Injective A.mulVec := by
      intro x y hxy
      have h0 : A.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
      have h2 := Fintype.linearIndependent_iff.1 (basis_real_linearIndependent b) (x - y) (by
        ext i
        have := congrFun h0 i
        simpa [Matrix.mulVec, dotProduct, hA, basisMatrix, integerReal, mul_comm,
          Finset.sum_apply] using this)
      funext j
      exact sub_eq_zero.1 (h2 j)
    have := (Matrix.PosDef.conjTranspose_mul_self A hinj).det_pos
    simpa [gram, hA, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  rw [gram_det_eq] at h
  exact_mod_cast h

theorem gramZ_det_basis_change {Λ : Lattice n} (b c : Basis (Fin d) ℤ Λ) :
    ((basisMatrix c).transpose * basisMatrix c).det =
      ((basisMatrix b).transpose * basisMatrix b).det := by
  obtain ⟨U, hU, hdet⟩ := (lattice_basis_change b c).1
  rw [hU, gramZ_det_mul]
  rcases hdet with h | h <;> simp [h]

theorem volume_sq_eq {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    volume_def Λ ^ 2 = (gram (basisMatrix b)).det := by
  obtain rfl := basis_card_eq_latticeDim b
  have hpos := gramZ_det_pos b
  unfold volume_def
  rw [Real.sq_sqrt, gram_det_eq, gram_det_eq, gramZ_det_basis_change b (latticeBasis Λ)]
  rw [gram_det_eq]
  exact_mod_cast (gramZ_det_pos (latticeBasis Λ)).le

theorem volume_nonneg (Λ : Lattice n) : 0 ≤ volume_def Λ := Real.sqrt_nonneg _

theorem volume_sq_int (Λ : Lattice n) : ∃ q : ℤ, 0 < q ∧ volume_def Λ ^ 2 = (q : ℝ) := by
  refine ⟨_, gramZ_det_pos (latticeBasis Λ), ?_⟩
  rw [volume_sq_eq (latticeBasis Λ), gram_det_eq]

theorem one_le_volume (Λ : Lattice n) : 1 ≤ volume_def Λ := by
  obtain ⟨q, hq, h⟩ := volume_sq_int Λ
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  by_contra hlt
  push Not at hlt
  nlinarith [volume_nonneg Λ]

theorem volume_bot : volume_def (⊥ : Lattice n) = 1 := by
  have h0 : latticeDim (⊥ : Lattice n) = 0 := (lattice_resonance (⊥ : Lattice n)).2.mpr rfl
  have : IsEmpty (Fin (latticeDim (⊥ : Lattice n))) := by rw [h0]; infer_instance
  have h := volume_sq_eq (latticeBasis (⊥ : Lattice n))
  rw [Matrix.det_isEmpty] at h
  have := volume_nonneg (⊥ : Lattice n)
  nlinarith

/-- The standard basis of `ℤⁿ`, as a basis of the top lattice. -/
def topBasis (n : ℕ) : Basis (Fin n) ℤ (⊤ : Lattice n) :=
  (Pi.basisFun ℤ (Fin n)).map AddSubgroup.topEquiv.symm.toIntLinearEquiv

theorem basisMatrix_topBasis : basisMatrix (topBasis n) = 1 := by
  ext i j
  simp [basisMatrix, topBasis, Pi.single_apply, Matrix.one_apply]

theorem volume_top : volume_def (⊤ : Lattice n) = 1 := by
  have h := volume_sq_eq (topBasis n)
  rw [basisMatrix_topBasis, gram_det_eq] at h
  simp at h
  have := volume_nonneg (⊤ : Lattice n)
  rcases h with h | h
  · exact h
  · linarith

theorem lattice_volume_index {d : ℕ} {Γ Λ : Lattice n}
    (b : Basis (Fin d) ℤ Λ) (c : Basis (Fin d) ℤ Γ)
    (N : Matrix (Fin d) (Fin d) ℤ) (hN : basisMatrix c = basisMatrix b * N) :
    volume_def Γ = |(N.det : ℝ)| * volume_def Λ := by
  have h1 := volume_sq_eq c
  have h2 := volume_sq_eq b
  rw [hN, gram_det_eq, gramZ_det_mul] at h1
  rw [gram_det_eq] at h2
  have h3 : volume_def Γ ^ 2 = (|(N.det : ℝ)| * volume_def Λ) ^ 2 := by
    rw [h1, mul_pow, sq_abs, h2]
    push_cast
    ring
  exact (sq_eq_sq₀ (volume_nonneg Γ) (mul_nonneg (abs_nonneg _) (volume_nonneg Λ))).1 h3

theorem volume_mono {Γ Λ : Lattice n} (hΓ : Γ ≤ Λ) (hd : latticeDim Γ = latticeDim Λ) :
    volume_def Λ ≤ volume_def Γ := by
  set c : Basis (Fin (latticeDim Λ)) ℤ Γ := (latticeBasis Γ).reindex (finCongr hd) with hc
  obtain ⟨N, hN, hdet⟩ := lattice_basis_sub hΓ (latticeBasis Λ) c
  rw [lattice_volume_index (latticeBasis Λ) c N hN]
  have h1 : (1 : ℝ) ≤ |(N.det : ℝ)| := by
    have : (1 : ℤ) ≤ |N.det| := Int.one_le_abs hdet
    exact_mod_cast this
  nlinarith [volume_nonneg Λ]

end Gram

section Schur
variable {d : ℕ}

/-- The matrix `A` with the column `c` appended on the right. -/
def snocCol (A : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ) : Matrix (Fin n) (Fin (d + 1)) ℝ :=
  Matrix.of fun i j => Fin.snoc (α := fun _ => ℝ) (fun j' => A i j') (c i) j

/-- Block-diagonal Gram determinant after replacing the last column by a vector orthogonal to the
others. -/
theorem det_gram_snoc_orth (A : Matrix (Fin n) (Fin d) ℝ) (c : Fin n → ℝ)
    (hperp : ∀ j, (fun i => A i j) ⬝ᵥ c = 0) :
    ((snocCol A c).transpose * snocCol A c).det = (A.transpose * A).det * (c ⬝ᵥ c) := by
  set M := (snocCol A c).transpose * snocCol A c with hM
  have hcc : ∀ a b : Fin d, M a.castSucc b.castSucc = (A.transpose * A) a b := by
    intro a b
    simp [hM, snocCol, Matrix.mul_apply]
  have hcl : ∀ a : Fin d, M (Fin.last d) a.castSucc = 0 := by
    intro a
    have := hperp a
    simp only [hM, snocCol, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Fin.snoc_last,
      Fin.snoc_castSucc]
    rw [← this]
    simp [dotProduct, mul_comm]
  have hll : M (Fin.last d) (Fin.last d) = c ⬝ᵥ c := by
    simp [hM, snocCol, Matrix.mul_apply, dotProduct]
  rw [Matrix.det_succ_row M (Fin.last d), Finset.sum_eq_single (Fin.last d)]
  · rw [hll, Fin.succAbove_last]
    have : M.submatrix Fin.castSucc Fin.castSucc = A.transpose * A := by
      ext a b
      exact hcc a b
    rw [this]
    simp [← two_mul, pow_mul]
    ring
  · intro j _ hj
    obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hj
    rw [hcl]
    simp
  · simp

/-- The unitriangular column operation subtracting `A x` from the last column. -/
def shearMat (x : Fin d → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun l j => (if l = j then 1 else 0) -
    (if j = Fin.last d then Fin.snoc (α := fun _ => ℝ) x 0 l else 0)

theorem det_shearMat (x : Fin d → ℝ) : (shearMat x).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    refine Fin.lastCases ?_ (fun a => ?_) i
    · simp [shearMat]
    · simp [shearMat, (Fin.castSucc_lt_last a).ne]
  · intro i j hij
    have hj : j ≠ Fin.last d := (lt_of_lt_of_le hij (Fin.le_last i)).ne
    have hne : i ≠ j := by
      intro h
      subst h
      exact lt_irrefl _ hij
    simp [shearMat, hne, hj]

theorem snocCol_mul_shear (A : Matrix (Fin n) (Fin d) ℝ) (kv : Fin n → ℝ) (x : Fin d → ℝ) :
    snocCol A kv * shearMat x = snocCol A (kv - A.mulVec x) := by
  ext i j
  refine Fin.lastCases ?_ (fun b => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, snocCol, shearMat, Matrix.mulVec, dotProduct,
      (Fin.castSucc_lt_last _).ne, sub_eq_add_neg, Finset.sum_neg_distrib]
    ring
  · have hb : (b : ℕ) ≠ d := b.2.ne
    simp [Matrix.mul_apply, snocCol, shearMat, hb.symm, mul_ite]

theorem det_gram_snoc_shear (A : Matrix (Fin n) (Fin d) ℝ) (kv : Fin n → ℝ) (x : Fin d → ℝ) :
    ((snocCol A (kv - A.mulVec x)).transpose * snocCol A (kv - A.mulVec x)).det =
      ((snocCol A kv).transpose * snocCol A kv).det := by
  rw [← snocCol_mul_shear, Matrix.transpose_mul]
  have : (shearMat x).transpose * (snocCol A kv).transpose * (snocCol A kv * shearMat x) =
      (shearMat x).transpose * ((snocCol A kv).transpose * snocCol A kv) * shearMat x := by
    simp [Matrix.mul_assoc]
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_shearMat]
  ring

end Schur
end KAM.Nekhoroshev
