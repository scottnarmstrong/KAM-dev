/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Gram
public import KAM.Certificate.NormBridge
public import KAM.Torus.FrozenAgreement
public import KAM.Frozen.Iso.Defs.ExtendedTorsionAverage

/-!
# The bordered torsion of a certified embedding: frame calculus

The analytic identities behind the torsion models (SO design §1.9), for an embedding `K`
holomorphic on `ℂⁿ` whose Gram matrix is invertible on the open strip `T_ρ`:

* `fderiv_tangentMat_apply`: `(D L[v])_{sj} = Σ_l v_l ∂_l L_{sj}` (`L = DK`);
* `fderiv_normalMat_apply`: `D N[v] = Ω₀ (D L[v] G⁻¹ + L D(G⁻¹)[v])` with
  `D(G⁻¹)[v] = -G⁻¹ (D L[v]ᵀ L + Lᵀ D L[v]) G⁻¹`;
* `linMat_apply_eq`: `(DX_H ∘ K)_{ab} = ± ∂_{a'} ∂_b H (K)` (`a' = a.swap`, sign `hamSign a`);
* `fderiv_apply_normalFrame`: the last row `DH(K) N_b = Σ_a ∂_a H(K) N_{ab}`;
* `continuousOn_extendedTorsion`: every entry of the frozen `extendedTorsion` is continuous
  on `T_ρ` when `H` is holomorphic on an open set containing `K(T_ρ)`;
* the second derivatives of a certified embedding (`CertModel.ofDeriv2` and its contract
  `CertModel.Encloses.ofDeriv2`, `fderiv_tangentMat_eval_inl`, `fderiv_tangentMat_eval_inr`).

`torsionIdx n` is the list index of the bordered rows and columns: `inl i ↦ i`, `inr () ↦ n`.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

/-- Row/column index of the bordered torsion: `inl i ↦ i`, `inr () ↦ n`. -/
def torsionIdx (n : ℕ) : Fin n ⊕ Unit → ℕ := Sum.elim (fun i => i.val) (fun _ => n)

/-! ### Generic frame calculus -/

section Generic

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

/-- The directional derivative of `L = DK` as the sum of its partials. -/
theorem fderiv_tangentMat_apply {θ : Fin n → ℂ} (hL : DifferentiableAt ℂ (tangentMat K) θ)
    (v : Fin n → ℂ) (s : Fin n ⊕ Fin n) (j : Fin n) :
    fderiv ℂ (tangentMat K) θ v s j =
      ∑ l, v l * fderiv ℂ (fun y => tangentMat K y s j) θ (Pi.single l 1) := by
  have hv : v = ∑ l, v l • (Pi.single l (1 : ℂ) : Fin n → ℂ) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    fderiv_matrix_apply hL]

/-- The derivative of the normal frame `N = Ω₀ L G⁻¹` on the strip where `G` is invertible:
`D N[v] = Ω₀ (D L[v] G⁻¹ + L D(G⁻¹)[v])`, `D(G⁻¹)[v] = -G⁻¹ (D L[v]ᵀ L + Lᵀ D L[v]) G⁻¹`. -/
theorem fderiv_normalMat_apply (hK : Differentiable ℂ K)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) (v : Fin n → ℂ) :
    fderiv ℂ (normalMat K) θ v = omegaZeroMatrix n *
      (fderiv ℂ (tangentMat K) θ v * (gramMatrix K θ)⁻¹ + tangentMat K θ *
        -((gramMatrix K θ)⁻¹ * ((fderiv ℂ (tangentMat K) θ v)ᵀ * tangentMat K θ +
          (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ v) * (gramMatrix K θ)⁻¹)) := by
  have hS := isOpen_complexStrip n ρ
  have hL := differentiableOn_tangentMat (r := ρ) hK.differentiableOn
  have hLa : DifferentiableAt ℂ (tangentMat K) θ := hL.differentiableAt (hS.mem_nhds hθ)
  have hinv := holomorphic_inverse hS (differentiableOn_gramMatrix (r := ρ) hK.differentiableOn)
    fun z hz => (hG z hz).ne_zero
  have hIa : DifferentiableAt ℂ (fun z => (gramMatrix K z)⁻¹) θ :=
    hinv.1.differentiableAt (hS.mem_nhds hθ)
  have hDG : fderiv ℂ (gramMatrix K) θ v = (fderiv ℂ (tangentMat K) θ v)ᵀ * tangentMat K θ +
      (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ v := by
    have hGf : gramMatrix K = fun y => (tangentMat K y)ᵀ * tangentMat K y :=
      funext (gramMatrix_eq_tangentMat_transpose_mul K)
    rw [hGf, fderiv_matrix_mul_apply hLa.matrix_transpose hLa, fderiv_matrix_transpose_apply]
  have hN : normalMat K = fun y => (omegaZeroMatrix n * tangentMat K y) * (gramMatrix K y)⁻¹ :=
    rfl
  rw [hN, fderiv_matrix_mul_apply ((differentiableAt_const _).matrix_mul hLa) hIa,
    fderiv_matrix_const_mul_apply _ hLa, hinv.2 θ hθ v, hDG]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

/-- The torsion is holomorphic on the strip when `N` and `X_N` are. -/
theorem differentiableOn_torsion_of {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
    (hN : DifferentiableOn ℂ (normalMat K) (complexStrip n ρ))
    (hX : DifferentiableOn ℂ (normalFieldMat H K ω) (complexStrip n ρ)) :
    DifferentiableOn ℂ (torsion H K ω) (complexStrip n ρ) :=
  ((hN.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mul hX).congr fun _ hθ =>
    torsion_eq_mat H K ω (hN.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ))

/-- The last row: `DH(z) N_b = Σ_a ∂_a H(z) N_{ab}`. -/
theorem fderiv_apply_normalFrame (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) (b : Fin n) :
    fderiv ℂ H z (normalFrame K θ b) =
      ∑ a, fderiv ℂ H z (phaseBasis a) * normalMat K θ a b := by
  conv_lhs => rw [← sum_sumVec_smul_phaseBasis (normalFrame K θ b)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, sumVec_normalFrame]

/-- Entries of `sqMat`: column `b` is the image of the phase basis vector `b`. -/
theorem sqMat_apply_eq_phaseBasis
    (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) (a b : Fin n ⊕ Fin n) :
    sqMat U a b = sumVec n (U (phaseBasis b)) a := by
  have h := congrFun (sqMat_mulVec U (phaseBasis b)) a
  simpa [phaseBasis, Matrix.mulVec_single_one] using h

/-- `(DX_H ∘ K)_{ab} = hamSign a · ∂_{a.swap} ∂_b H (K)` for `C²` `H`. -/
theorem linMat_apply_eq {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {θ : Fin n → ℂ}
    (hH : ContDiffAt ℂ 2 H (K θ)) (a b : Fin n ⊕ Fin n) :
    linMat H K θ a b =
      hamSign a * iteratedFDeriv ℂ 2 H (K θ) ![phaseBasis a.swap, phaseBasis b] := by
  have hsym := hH.isSymmSndFDerivAt (by simp)
  rw [linMat, sqMat_apply_eq_phaseBasis, sumVec_fderiv_hamiltonianVectorFieldℂ hH,
    iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hsym]

end Generic

end KAM.Certificate

end
