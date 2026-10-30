/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.PerturbationParts
public import KAM.Sharp.TorsionPoly
public import KAM.Sharp.Tools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The torsion against the initial torus (`bp:p2s2:sec-tor`, audit F8)

By the torsion polynomial (`KAM.Sharp.torsion_identity`, `bp:p2s:torsion-identity`),
`T = 𝒯_ab + 𝒯_F + 𝒯_c` with the frame part `𝒯_ab = B Lᵀ (A Ω₀ - Ω₀ A) L B`, `A = DX_h ∘ K`.

* `hamComm`, `torsionAB`, `torsionABAverage`: the commutator `A Ω₀ - Ω₀ A` (refined data (R1):
  `c_Th`, `c_DTh`), the frame part and its average over the real torus.
* `norm_torsionAB_le` (`bp:p2s2:torsion-local`, frame part): `|𝒯_ab| ≤ |Nᵀ| c_Th |N|`, since
  `B Lᵀ = Nᵀ Ω₀` and `L B = -Ω₀ N`.
* `norm_torsion_sub_torsionAB_le` (`bp:p2s2:torsion-local`, local part):
  `|T - 𝒯_ab| = |𝒯_F + 𝒯_c| ≤ σ_{Nᵀ} σ_B |DE| + σ_B³ w |Ω_K|`.
* `inv_le_of_ref` (`bp:p2s2:torsion-ref`, step `step:p2s2:tr-n`): Neumann against the initial
  average, `|A - A₀| ≤ (σ - m)/(σ m)` and `|A₀⁻¹| ≤ m < σ` give `|A⁻¹| ≤ σ`.
* `norm_lagrangeMat_comp_le` (option L10, `step:p2s2:selfcons`): the pullback
  `Ω_{K̃∘φ} = Dφᵀ (Ω_{K̃}∘φ) Dφ`, `φ = id + ξ`, with `|Dφ|, |Dφᵀ| ≤ 1 + b`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

/-- The commutator `A Ω₀ - Ω₀ A`, `A = DX_h(z)` (refined data (R1): `c_Th`, `c_DTh`). -/
def hamComm (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z) * omegaZeroMatrix n -
    omegaZeroMatrix n * sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z)

/-- The frame part `𝒯_ab = B Lᵀ (A Ω₀ - Ω₀ A) L B` of the torsion polynomial
(`bp:p2s:torsion-identity`). -/
def torsionAB (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (θ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ * hamComm h (K θ) * tangentMat K θ * (gramMatrix K θ)⁻¹

/-- `⟨𝒯_ab⟩` over the real torus (as `torsionAverage`). -/
def torsionABAverage (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∫ θ in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
    torsionAB h K (fun l => (θ l : ℂ)) i j

namespace TorsionRef

/-- `B Lᵀ = Nᵀ Ω₀`, so `|B Lᵀ| = |Nᵀ|`. -/
theorem norm_B_Lt (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ = ‖(normalMat K θ)ᵀ‖ := by
  rw [← TorsionPoly.normalMat_transpose_mul_omega, norm_mul_omegaZeroMatrix]

/-- `L B = -Ω₀ N`, so `|L B| = |N|`. -/
theorem norm_L_B (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    ‖tangentMat K θ * (gramMatrix K θ)⁻¹‖ = ‖normalMat K θ‖ := by
  rw [← norm_omegaZeroMatrix_mul, normalMat, Matrix.mul_assoc]

/-- `𝒯_ab` is the `tAB` part of the torsion polynomial at `A = DX_h ∘ K`. -/
theorem torsionAB_eq_tAB (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    torsionAB h K θ = tAB (linMat h K θ) (tangentMat K θ) (gramMatrix K θ)⁻¹ := by
  simp only [torsionAB, hamComm, tAB, linMat, Matrix.mul_sub, Matrix.sub_mul]

/-- `𝒯_ab = (B Lᵀ) (A Ω₀ - Ω₀ A) (L B)`. -/
theorem torsionAB_eq_triple (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    torsionAB h K θ = ((gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ) * hamComm h (K θ) *
      (tangentMat K θ * (gramMatrix K θ)⁻¹) := by
  simp only [torsionAB, Matrix.mul_assoc]

/-- `colMat (U ∘ V) = colMat U · [V]`. -/
theorem colMat_comp {q : ℕ} (U : (Fin q → ℂ) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ))
    (V : (Fin q → ℂ) →L[ℂ] (Fin q → ℂ)) :
    colMat (U.comp V) = colMat U * LinearMap.toMatrix' (V : (Fin q → ℂ) →ₗ[ℂ] (Fin q → ℂ)) := by
  rw [colMat, colMat, ← LinearMap.toMatrix'_comp]
  rfl

/-- The row sums of `1 + D` are at most `1 + b` when those of `D` are at most `b`. -/
theorem norm_one_add_le {D : Matrix (Fin n) (Fin n) ℂ} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ i, ∑ j, ‖D i j‖ ≤ b) : ‖1 + D‖ ≤ 1 + b := by
  refine (norm_le_iff_forall_rowSum (by linarith)).2 fun i => ?_
  calc ∑ j, ‖(1 + D) i j‖ ≤ ∑ j, (‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ + ‖D i j‖) :=
        Finset.sum_le_sum fun j _ => by rw [Matrix.add_apply]; exact norm_add_le _ _
    _ = ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ + ∑ j, ‖D i j‖ := Finset.sum_add_distrib
    _ ≤ 1 + b := by
        refine add_le_add (le_of_eq ?_) (hb i)
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Matrix.one_apply_ne' hji, norm_zero]
        · simp

end TorsionRef

/-- `bp:p2s2:torsion-local`, the frame part: `|𝒯_ab| ≤ c_Th |Nᵀ| |N|`. -/
theorem norm_torsionAB_le {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {sN sNt cTh : ℝ}
    (hG : IsUnit (gramMatrix K θ).det) (hN : ‖normalMat K θ‖ ≤ sN)
    (hNt : ‖(normalMat K θ)ᵀ‖ ≤ sNt) (hc : ‖hamComm h (K θ)‖ ≤ cTh) :
    ‖torsionAB h K θ‖ ≤ sNt * cTh * sN := by
  have _hG := hG
  rw [TorsionRef.torsionAB_eq_triple]
  have nm := @FrameSharp.norm_mul_le_of_le
  exact nm (nm (by rw [TorsionRef.norm_B_Lt]; exact hNt) hc) (by rw [TorsionRef.norm_L_B]; exact hN)

/-- `bp:p2s2:torsion-local`, the local part:
`|T - 𝒯_ab| = |𝒯_F + 𝒯_c| ≤ σ_{Nᵀ} σ_B |DE| + σ_B³ w |Ω_K|`. -/
theorem norm_torsion_sub_torsionAB_le {τ M σK σB σT γ : ℝ}
    {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {ω : Fin n → ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n r) {sB sNt w dE oK : ℝ}
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ sB) (hNt : ‖(normalMat K θ)ᵀ‖ ≤ sNt)
    (hDE : ‖errDerivMat h K ω θ‖ ≤ dE)
    (hW : ‖(tangentMat K θ)ᵀ * ((linMat h K θ)ᵀ + linMat h K θ) * tangentMat K θ -
      (errDerivMat h K ω θ)ᵀ * tangentMat K θ - (tangentMat K θ)ᵀ * errDerivMat h K ω θ‖ ≤ w)
    (hΩ : ‖lagrangeMat K θ‖ ≤ oK) :
    ‖torsion h K ω θ - torsionAB h K θ‖ ≤ sNt * sB * dE + sB ^ 3 * w * oK := by
  have hT := ((torsion_identity hS hr hK hK𝔅 hG ω) θ hθ).2.2
  rw [hT, torsionPoly_split, TorsionRef.torsionAB_eq_tAB, add_assoc, add_sub_cancel_left]
  have nm := @FrameSharp.norm_mul_le_of_le
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have e : tF (tangentMat K θ) (errDerivMat h K ω θ) (gramMatrix K θ)⁻¹ =
        ((gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ) *
          (omegaZeroMatrix n * errDerivMat h K ω θ * (gramMatrix K θ)⁻¹) := rfl
    have hOF : ‖omegaZeroMatrix n * errDerivMat h K ω θ‖ ≤ dE := by
      rw [norm_omegaZeroMatrix_mul]; exact hDE
    rw [e]
    calc _ ≤ sNt * (dE * sB) := nm (by rw [TorsionRef.norm_B_Lt]; exact hNt) (nm hOF hB)
      _ = sNt * sB * dE := by ring
  · calc _ ≤ sB * oK * sB * w * sB := norm_tC_le hB hΩ hW
      _ = sB ^ 3 * w * oK := by ring

/-- `bp:p2s2:torsion-ref`: Neumann against the initial average. -/
theorem inv_le_of_ref {A A0 : Matrix (Fin n) (Fin n) ℂ} {m σ : ℝ} (hA0 : IsUnit A0.det)
    (hm : ‖A0⁻¹‖ ≤ m) (hm0 : 0 < m) (hmσ : m < σ) (hd : ‖A - A0‖ ≤ (σ - m) / (σ * m)) :
    IsUnit A.det ∧ ‖A⁻¹‖ ≤ σ := by
  have hσ : 0 < σ := hm0.trans hmσ
  have hq : (σ - m) / σ < 1 := by rw [div_lt_one hσ]; linarith
  have hsmall : ‖A0⁻¹‖ * ‖A - A0‖ ≤ (σ - m) / σ := by
    calc ‖A0⁻¹‖ * ‖A - A0‖ ≤ m * ((σ - m) / (σ * m)) :=
          mul_le_mul hm hd (norm_nonneg _) hm0.le
      _ = (σ - m) / σ := by field_simp
  obtain ⟨hu, hb, -⟩ := neumann_ratio ((Matrix.isUnit_iff_isUnit_det A0).2 hA0) hq hsmall
  rw [add_sub_cancel] at hu hb
  refine ⟨(Matrix.isUnit_iff_isUnit_det A).1 hu, hb.trans ?_⟩
  have h1 : 1 - (σ - m) / σ = m / σ := by field_simp; ring
  rw [h1, div_le_iff₀ (div_pos hm0 hσ)]
  calc ‖A0⁻¹‖ ≤ m := hm
    _ = σ * (m / σ) := by field_simp

/-- The pullback of the Lagrangian defect (option L10, `step:p2s2:selfcons`):
`Ω_{K̃∘φ} = Dφᵀ (Ω_{K̃}∘φ) Dφ`. -/
theorem norm_lagrangeMat_comp_le {Kt : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ξ : (Fin n → ℂ) → (Fin n → ℂ)} {θ : Fin n → ℂ} {b oK : ℝ}
    (hKt : DifferentiableAt ℂ Kt (θ + ξ θ)) (hξ : DifferentiableAt ℂ ξ θ)
    (hb : ∀ i, ∑ j, ‖fderiv ℂ ξ θ (Pi.single j 1) i‖ ≤ b)
    (hbT : ∀ j, ∑ i, ‖fderiv ℂ ξ θ (Pi.single j 1) i‖ ≤ b)
    (hΩ : ‖lagrangeMat Kt (θ + ξ θ)‖ ≤ oK) :
    ‖lagrangeMat (fun θ' => Kt (θ' + ξ θ')) θ‖ ≤ (1 + b) ^ 2 * oK := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : lagrangeMat (fun θ' => Kt (θ' + ξ θ')) θ = 0 := Subsingleton.elim _ _
    rw [h0, norm_zero]
    exact mul_nonneg (sq_nonneg _) ((norm_nonneg _).trans hΩ)
  have hb0 : 0 ≤ b := (Finset.sum_nonneg fun j _ => norm_nonneg _).trans (hb ⟨0, hn⟩)
  set V : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.id ℂ _ + fderiv ℂ ξ θ with hV
  have hφ : HasFDerivAt (fun θ' => θ' + ξ θ') V θ := (hasFDerivAt_id θ).add hξ.hasFDerivAt
  have hcomp : HasFDerivAt (fun θ' => Kt (θ' + ξ θ')) ((fderiv ℂ Kt (θ + ξ θ)).comp V) θ :=
    hKt.hasFDerivAt.comp θ hφ
  set D := LinearMap.toMatrix' (V : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) with hD
  have hL : tangentMat (fun θ' => Kt (θ' + ξ θ')) θ = tangentMat Kt (θ + ξ θ) * D := by
    rw [tangentMat, hcomp.fderiv, TorsionRef.colMat_comp]
    rfl
  set Dξ : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => fderiv ℂ ξ θ (Pi.single j 1) i
  have hDe : D = 1 + Dξ := by
    ext i j
    rw [hD, LinearMap.toMatrix'_apply, Matrix.add_apply]
    simp only [Dξ, Matrix.of_apply, hV, ContinuousLinearMap.coe_coe,
      _root_.add_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.single_apply,
      Matrix.one_apply]
  have hDn : ‖D‖ ≤ 1 + b := by
    rw [hDe]
    exact TorsionRef.norm_one_add_le hb0 fun i => hb i
  have hDTn : ‖Dᵀ‖ ≤ 1 + b := by
    rw [hDe, Matrix.transpose_add, Matrix.transpose_one]
    exact TorsionRef.norm_one_add_le hb0 fun j => by
      simpa [Dξ, Matrix.transpose_apply] using hbT j
  have hΩe : lagrangeMat (fun θ' => Kt (θ' + ξ θ')) θ = Dᵀ * lagrangeMat Kt (θ + ξ θ) * D := by
    rw [lagrangeMat, lagrangeMat, hL, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [hΩe]
  have nm := @FrameSharp.norm_mul_le_of_le
  calc _ ≤ (1 + b) * oK * (1 + b) := nm (nm hDTn hΩ) hDn
    _ = (1 + b) ^ 2 * oK := by ring

end KAM.Sharp2

end
