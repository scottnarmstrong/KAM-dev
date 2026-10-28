/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Nekhoroshev.Stability.Gradient
public import KAM.Nekhoroshev.Stability.Energy

/-!
# Lattice geometry (`bpN:p8:lattice`, `bpN:p8:lattice-basis`, `bpN:p8:ext-indep`)

Integer lattices `Λ ≤ ℤⁿ` (`AddSubgroup (Fin n → ℤ)`), their real span `lattice Λ`, the rank
`latticeDim Λ`, the resonance space, integer bases (`Basis (Fin d) ℤ Λ`), integer–real independence
(`integer_independent_real`), unimodular basis changes and the index matrix of a sublattice.
-/

@[expose] public noncomputable section
open Set Matrix Module Classical

namespace KAM.Nekhoroshev
open KAM.Stability
variable {n : ℕ}

abbrev Lattice (n : ℕ) := AddSubgroup (Fin n → ℤ)
def lattice (Λ : Lattice n) : Submodule ℝ (Fin n → ℝ) := resSpan (Λ : Set _)
def latticeDim (Λ : Lattice n) : ℕ := Module.finrank ℝ (lattice Λ)
def integerReal (k : Fin n → ℤ) : Fin n → ℝ := fun i => (k i : ℝ)
def eBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | euclid (integerReal k) ≤ K}
def resonance (Λ : Lattice n) : Set (Fin n → ℝ) := resSpace (Λ : Set _)
def basisMatrix {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    Matrix (Fin n) (Fin d) ℤ := fun i j => (b j).val i

/-- Field-extension step of ext-indep; not supplied merely by a rank API name. -/
theorem integer_independent_real {d : ℕ} (v : Fin d → (Fin n → ℤ))
    (hv : LinearIndependent ℤ v) : LinearIndependent ℝ (fun j => integerReal (v j)) := by
  have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := v)).2 hv
  convert h using 2 with j
  ext i
  simp [integerReal]

theorem integerReal_injective : Function.Injective (integerReal (n := n)) := by
  intro a b h
  funext i
  have := congrFun h i
  simpa [integerReal] using this

theorem integerReal_mem_lattice {Λ : Lattice n} {k : Fin n → ℤ} (hk : k ∈ Λ) :
    integerReal k ∈ lattice Λ :=
  Submodule.subset_span ⟨k, hk, rfl⟩

/-- The integer vectors of a `ℤ`-basis are `ℤ`-independent in `ℤⁿ`. -/
theorem basis_val_linearIndependent {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    LinearIndependent ℤ (fun j => (b j).val) :=
  b.linearIndependent.map' Λ.subtype.toIntLinearMap
    (LinearMap.ker_eq_bot.2 Subtype.val_injective)

theorem basis_real_linearIndependent {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    LinearIndependent ℝ (fun j => integerReal (b j).val) :=
  integer_independent_real _ (basis_val_linearIndependent b)

/-- Coordinates of an element of `Λ` in a basis, written on integer vectors. -/
theorem basisMatrix_apply_repr {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) (x : Λ)
    (i : Fin n) : (x : Fin n → ℤ) i = ∑ k, (basisMatrix b) i k * b.repr x k := by
  have h : (x : Fin n → ℤ) = ∑ k, b.repr x k • (b k : Fin n → ℤ) := by
    have h := congrArg Λ.subtype (b.sum_repr x)
    rw [map_sum] at h
    simpa [map_zsmul] using h.symm
  rw [h]
  simp [basisMatrix, mul_comm]

theorem basis_span_eq {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    Submodule.span ℝ (Set.range fun j => integerReal (b j).val) = lattice Λ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact integerReal_mem_lattice (b j).2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have : integerReal k = ∑ j, (b.repr ⟨k, hk⟩ j : ℝ) • integerReal (b j).val := by
      ext i
      have h := basisMatrix_apply_repr b ⟨k, hk⟩ i
      simp only [integerReal, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [show (k i : ℝ) = ((∑ j, basisMatrix b i j * b.repr ⟨k, hk⟩ j : ℤ) : ℝ) from
        by exact_mod_cast h]
      push_cast
      simp [basisMatrix, mul_comm]
    show integerReal k ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem basis_card_eq_latticeDim {d : ℕ} {Λ : Lattice n} (b : Basis (Fin d) ℤ Λ) :
    d = latticeDim Λ := by
  have h := finrank_span_eq_card (basis_real_linearIndependent b)
  rw [basis_span_eq b] at h
  simpa [latticeDim] using h.symm

theorem exists_basis (Λ : Lattice n) : ∃ d : ℕ, Nonempty (Basis (Fin d) ℤ Λ) := by
  obtain ⟨d, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin n)) Λ.toIntSubmodule
  exact ⟨d, ⟨b.map (AddEquiv.refl Λ).toIntLinearEquiv⟩⟩

theorem lattice_basis (Λ : Lattice n) :
    latticeDim Λ ≤ n ∧ Nonempty (Basis (Fin (latticeDim Λ)) ℤ Λ) ∧
    Module.finrank ℤ Λ = latticeDim Λ ∧
    ∀ d : ℕ, ∀ b : Basis (Fin d) ℤ Λ,
      LinearIndependent ℝ (fun j => integerReal (b j).val) ∧ d = latticeDim Λ := by
  obtain ⟨d, ⟨b⟩⟩ := exists_basis Λ
  have hd := basis_card_eq_latticeDim b
  refine ⟨?_, ⟨b.reindex (finCongr hd)⟩, ?_, fun d' b' =>
    ⟨basis_real_linearIndependent b', basis_card_eq_latticeDim b'⟩⟩
  · have := Submodule.finrank_le (lattice Λ)
    simpa [latticeDim] using this
  · rw [Module.finrank_eq_card_basis b]
    simpa using hd

theorem lattice_resonance (Λ : Lattice n) :
    resonance Λ = {w | ∀ v ∈ lattice Λ, v ⬝ᵥ w = 0} ∧
    (latticeDim Λ = 0 ↔ Λ = ⊥) := by
  constructor
  · ext w
    constructor
    · intro hw v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, rfl⟩ := hx
        exact hw k hk
      | zero => simp
      | add x y _ _ hx hy => simp [add_dotProduct, hx, hy]
      | smul a x _ hx => simp [smul_dotProduct, hx]
    · intro hw k hk
      exact hw _ (integerReal_mem_lattice hk)
  · have h1 : latticeDim Λ = 0 ↔ lattice Λ = ⊥ := by
      unfold latticeDim
      exact Submodule.finrank_eq_zero
    rw [h1, AddSubgroup.eq_bot_iff_forall]
    constructor
    · intro h k hk
      have := h ▸ integerReal_mem_lattice hk
      have h0 : integerReal k = 0 := (Submodule.mem_bot ℝ).1 this
      exact integerReal_injective (h0.trans (by ext; simp [integerReal]))
    · intro h
      rw [lattice, resSpan, Submodule.span_eq_bot]
      rintro _ ⟨k, hk, rfl⟩
      have := h k hk
      subst this
      ext i
      simp

def latticeBasis (Λ : Lattice n) : Basis (Fin (latticeDim Λ)) ℤ Λ :=
  Classical.choice (lattice_basis Λ).2.1

theorem basisMatrix_eq_mul {d : ℕ} {Λ : Lattice n} (b c : Basis (Fin d) ℤ Λ) :
    basisMatrix c = basisMatrix b * b.toMatrix c := by
  ext i j
  rw [Matrix.mul_apply]
  exact basisMatrix_apply_repr b (c j) i

theorem lattice_basis_change {d : ℕ} {Λ : Lattice n}
    (b c : Basis (Fin d) ℤ Λ) :
    (∃ U : Matrix (Fin d) (Fin d) ℤ,
      basisMatrix c = basisMatrix b * U ∧ (U.det = 1 ∨ U.det = -1)) ∧
    (∀ U : Matrix (Fin d) (Fin d) ℤ, U.det = 1 ∨ U.det = -1 →
      ∃ c' : Basis (Fin d) ℤ Λ, basisMatrix c' = basisMatrix b * U) := by
  refine ⟨⟨b.toMatrix c, basisMatrix_eq_mul b c, ?_⟩, ?_⟩
  · have h : IsUnit (b.toMatrix c).det := by
      rw [← Basis.det_apply]
      exact b.isUnit_det c
    exact Int.isUnit_iff.1 h
  · intro U hU
    have hu : IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b U)).det := by
      rw [LinearMap.toMatrix_toLin]
      exact Int.isUnit_iff.2 hU
    refine ⟨b.map (LinearEquiv.ofIsUnitDet hu), ?_⟩
    have := basisMatrix_eq_mul b (b.map (LinearEquiv.ofIsUnitDet hu))
    rw [this]
    congr 1
    ext k j
    simp [Basis.toMatrix_apply, Matrix.toLin_self, Finsupp.single_apply]

theorem lattice_basis_sub {d : ℕ} {Γ Λ : Lattice n} (hΓ : Γ ≤ Λ)
    (b : Basis (Fin d) ℤ Λ) (c : Basis (Fin d) ℤ Γ) :
    ∃ N : Matrix (Fin d) (Fin d) ℤ,
      basisMatrix c = basisMatrix b * N ∧ N.det ≠ 0 := by
  set N : Matrix (Fin d) (Fin d) ℤ := fun k j => b.repr ⟨(c j).val, hΓ (c j).2⟩ k with hN
  have hmul : basisMatrix c = basisMatrix b * N := by
    ext i j
    rw [Matrix.mul_apply]
    exact basisMatrix_apply_repr b ⟨(c j).val, hΓ (c j).2⟩ i
  refine ⟨N, hmul, fun hdet => ?_⟩
  have hR : (N.map (Int.castRingHom ℝ)).det = 0 := by
    have := RingHom.map_det (Int.castRingHom ℝ) N
    rw [hdet, map_zero] at this
    exact this.symm
  obtain ⟨x, hx, hNx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hR
  have hind := basis_real_linearIndependent c
  rw [Fintype.linearIndependent_iff] at hind
  apply hx
  funext j
  refine hind x ?_ j
  have hC : (basisMatrix c).map (Int.castRingHom ℝ) =
      (basisMatrix b).map (Int.castRingHom ℝ) * N.map (Int.castRingHom ℝ) := by
    rw [hmul, Matrix.map_mul]
  have h0 : ((basisMatrix c).map (Int.castRingHom ℝ)).mulVec x = 0 := by
    rw [hC, ← Matrix.mulVec_mulVec, hNx, Matrix.mulVec_zero]
  ext i
  have := congrFun h0 i
  simpa [Matrix.mulVec, dotProduct, basisMatrix, integerReal, mul_comm] using this

end KAM.Nekhoroshev
