/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp.TorsionBound
public import KAM.Sharp.Tools
public import KAM.Apost.PerturbationTorsion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pieces of the perturbation lemma `bp:p2s:perturbation`

Helpers for `KAM.Sharp.perturbation_poly` (`KAM.Sharp.Perturbation`):

* `prod5_sub_le`: Lemma `bp:p2s:telescope` for five factors
  (`|∏ X̃ - ∏ X| ≤ ϑ̂⁴ ∑_i Δ_i ∏_{j≠i} x_j`,
  through the control predicate `PertSharp.Ctrl`);
* `diffOn_invarianceError_any`, `geo_de_any`: the Cauchy bounds of `DE` and `(DE)ᵀ` for the error
  `E_{ω'}` at any frequency `ω'` (`KAM.Apost.Geometry.geo_de` is tied to the standing frequency);
* `norm_linMat_sub_le_M`: `|Ã - A| ≤ M d` (step `step:p2s:pt-domain`);
* `norm_transpose_tangentMat_le_vthh`: `|L̃ᵀ| ≤ 2n ϑ̂ σ_K` (step `step:p2s:pt-l`);
* `tAB`, `tF`, `tC` and `torsionPoly_split`: `𝒯 = 𝒯_ab + 𝒯_F + 𝒯_c` (`bp:p2s:sec-torsion`), with
  the norm bounds `norm_tF_le`, `norm_tC_le`, `norm_W_le`;
* `norm_torsionAverage_sub_le_any`: the bound of `⟨T̃_{ω'}⟩ - ⟨T_ω⟩` by a bound at real points
  (step `step:p2s:pt-avg`; the existing `PerturbationAux.norm_torsionAverage_sub_le` has one
  frequency).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Sharp

open KAM KAM.Torus KAM.Apost

namespace PertSharp

/-! ### Products of perturbed factors -/

section Products

variable {c : ℝ}

/-- `X, X'` are controlled: `‖X‖ ≤ x`, `‖X'‖ ≤ c^{m+1} x`, `‖X' - X‖ ≤ c^m e`. -/
def Ctrl {a b : Type*} [Fintype a] [Fintype b] (c : ℝ) (m : ℕ) (X X' : Matrix a b ℂ)
    (x e : ℝ) : Prop :=
  ‖X‖ ≤ x ∧ ‖X'‖ ≤ c ^ (m + 1) * x ∧ ‖X' - X‖ ≤ c ^ m * e

theorem Ctrl.base {a b : Type*} [Fintype a] [Fintype b] {X X' : Matrix a b ℂ} {x e : ℝ}
    (h1 : ‖X‖ ≤ x) (h2 : ‖X'‖ ≤ c * x) (h3 : ‖X' - X‖ ≤ e) : Ctrl c 0 X X' x e :=
  ⟨h1, by simpa using h2, by simpa using h3⟩

theorem Ctrl.mul {a b d : Type*} [Fintype a] [Fintype b] [Fintype d] (hc : 1 ≤ c) {m l : ℕ}
    {X X' : Matrix a b ℂ} {Y Y' : Matrix b d ℂ} {x e y f : ℝ}
    (hX : Ctrl c m X X' x e) (hY : Ctrl c l Y Y' y f) :
    Ctrl c (m + l + 1) (X * Y) (X' * Y') (x * y) (x * f + e * y) := by
  obtain ⟨hX1, hX2, hX3⟩ := hX
  obtain ⟨hY1, hY2, hY3⟩ := hY
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hx : 0 ≤ x := (norm_nonneg _).trans hX1
  have hy : 0 ≤ y := (norm_nonneg _).trans hY1
  have hcm : 0 < c ^ m := pow_pos (zero_lt_one.trans_le hc) m
  have hcl : 0 < c ^ l := pow_pos (zero_lt_one.trans_le hc) l
  have he : 0 ≤ e := by
    have h0 := (norm_nonneg _).trans hX3
    by_contra hne
    linarith [mul_neg_of_pos_of_neg hcm (not_le.mp hne)]
  have hf : 0 ≤ f := by
    have h0 := (norm_nonneg _).trans hY3
    by_contra hne
    linarith [mul_neg_of_pos_of_neg hcl (not_le.mp hne)]
  have hpow : c ^ m ≤ c ^ (m + l + 1) := pow_le_pow_right₀ hc (by omega)
  refine ⟨(Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hX1 hY1 (norm_nonneg _) hx), ?_, ?_⟩
  · calc ‖X' * Y'‖ ≤ ‖X'‖ * ‖Y'‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ (c ^ (m + 1) * x) * (c ^ (l + 1) * y) :=
          mul_le_mul hX2 hY2 (norm_nonneg _) (by positivity)
      _ = c ^ (m + l + 1 + 1) * (x * y) := by ring
  · calc ‖X' * Y' - X * Y‖ ≤ ‖X'‖ * ‖Y' - Y‖ + ‖X' - X‖ * ‖Y‖ := norm_mul_sub_mul_le _ _ _ _
      _ ≤ (c ^ (m + 1) * x) * (c ^ l * f) + (c ^ m * e) * y :=
          add_le_add (mul_le_mul hX2 hY3 (norm_nonneg _) (by positivity))
            (mul_le_mul hX3 hY1 (norm_nonneg _) (by positivity))
      _ = c ^ (m + l + 1) * (x * f) + c ^ m * (e * y) := by ring
      _ ≤ c ^ (m + l + 1) * (x * f) + c ^ (m + l + 1) * (e * y) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hpow (mul_nonneg he hy))
      _ = c ^ (m + l + 1) * (x * f + e * y) := by ring

end Products

end PertSharp

/-- Lemma `bp:p2s:telescope` for five factors (constant factors of norm `≤ 1` may be absorbed in
the factors): `|X̃₁⋯X̃₅ - X₁⋯X₅| ≤ c⁴ ∑_i Δ_i ∏_{j≠i} x_j` when `|X_i| ≤ x_i`, `|X̃_i| ≤ c x_i`,
`|X̃_i - X_i| ≤ Δ_i`, `c ≥ 1`. -/
theorem prod5_sub_le {a₀ a₁ a₂ a₃ a₄ a₅ : Type*} [Fintype a₀] [Fintype a₁] [Fintype a₂]
    [Fintype a₃] [Fintype a₄] [Fintype a₅] {c : ℝ} (hc : 1 ≤ c)
    {X₁ X₁' : Matrix a₀ a₁ ℂ} {X₂ X₂' : Matrix a₁ a₂ ℂ} {X₃ X₃' : Matrix a₂ a₃ ℂ}
    {X₄ X₄' : Matrix a₃ a₄ ℂ} {X₅ X₅' : Matrix a₄ a₅ ℂ}
    {x₁ x₂ x₃ x₄ x₅ e₁ e₂ e₃ e₄ e₅ : ℝ}
    (h₁ : ‖X₁‖ ≤ x₁) (h₁' : ‖X₁'‖ ≤ c * x₁) (d₁ : ‖X₁' - X₁‖ ≤ e₁)
    (h₂ : ‖X₂‖ ≤ x₂) (h₂' : ‖X₂'‖ ≤ c * x₂) (d₂ : ‖X₂' - X₂‖ ≤ e₂)
    (h₃ : ‖X₃‖ ≤ x₃) (h₃' : ‖X₃'‖ ≤ c * x₃) (d₃ : ‖X₃' - X₃‖ ≤ e₃)
    (h₄ : ‖X₄‖ ≤ x₄) (h₄' : ‖X₄'‖ ≤ c * x₄) (d₄ : ‖X₄' - X₄‖ ≤ e₄)
    (h₅ : ‖X₅‖ ≤ x₅) (h₅' : ‖X₅'‖ ≤ c * x₅) (d₅ : ‖X₅' - X₅‖ ≤ e₅) :
    ‖X₁' * X₂' * X₃' * X₄' * X₅' - X₁ * X₂ * X₃ * X₄ * X₅‖ ≤
      c ^ 4 * (e₁ * x₂ * x₃ * x₄ * x₅ + x₁ * e₂ * x₃ * x₄ * x₅ + x₁ * x₂ * e₃ * x₄ * x₅ +
        x₁ * x₂ * x₃ * e₄ * x₅ + x₁ * x₂ * x₃ * x₄ * e₅) := by
  have C := ((((PertSharp.Ctrl.base h₁ h₁' d₁).mul hc (PertSharp.Ctrl.base h₂ h₂' d₂)).mul hc
    (PertSharp.Ctrl.base h₃ h₃' d₃)).mul hc (PertSharp.Ctrl.base h₄ h₄' d₄)).mul hc
    (PertSharp.Ctrl.base h₅ h₅' d₅)
  refine C.2.2.trans (le_of_eq ?_)
  ring

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-! ### The error at another frequency -/

/-- The invariance error `E_{ω'} = X_h ∘ K - DK ω'` is holomorphic on the strip, for any `ω'`. -/
theorem diffOn_invarianceError_any (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) (ω' : Fin n → ℝ) :
    DifferentiableOn ℂ (invarianceError h K ω') (complexStrip n r) := by
  have h1 : DifferentiableOn ℂ (fun θ => hamiltonianVectorFieldℂ h (K θ)) (complexStrip n r) :=
    (differentiableOn_ham hS).comp hK hK𝔅
  have h2 : DifferentiableOn ℂ (fun θ => fderiv ℂ K θ (fun i => (ω' i : ℂ))) (complexStrip n r) :=
    (holomorphic_regularity (isOpen_complexStrip n r) hK).1.clm_apply (differentiableOn_const _)
  exact h1.sub h2

/-- `|DE_{ω'}| ≤ n ε'/δ` and `|(DE_{ω'})ᵀ| ≤ 2n ε'/δ` on `T_{r-δ}` (the Cauchy estimates of
`KAM.Apost.Geometry.geo_de`, at any frequency `ω'`). -/
theorem geo_de_any (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {r ε δ : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅) {ω' : Fin n → ℝ}
    (hA6 : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω' θ‖ ≤ ε) (hδ : 0 < δ) :
    ∀ θ ∈ complexStrip n (r - δ),
      ‖errDerivMat h K ω' θ‖ ≤ n * ε / δ ∧ ‖(errDerivMat h K ω' θ)ᵀ‖ ≤ 2 * n * ε / δ := by
  intro θ hθ
  have hE := diffOn_invarianceError_any hS hK hK𝔅 ω'
  have hf : DifferentiableOn ℂ (fun y => sumVec n (invarianceError h K ω' y))
      (complexStrip n r) := (sumVecIso n).differentiable.comp_differentiableOn hE
  have hA : ∀ y ∈ complexStrip n r, ‖sumVec n (invarianceError h K ω' y)‖ ≤ ε := fun y hy => by
    rw [norm_sumVec]
    exact hA6 y hy
  refine ⟨?_, ?_⟩
  · rw [errDerivMat, norm_colMat]
    calc ‖fderiv ℂ (invarianceError h K ω') θ‖ ≤ n * δ⁻¹ * ε :=
          (cauchy_strip hE hA6 hδ).2 θ hθ
      _ = n * ε / δ := by ring
  · have := cauchy_transpose_fintype hf hA hδ θ hθ
    rw [Geometry.errDerivMat_eq_of]
    calc _ ≤ (Fintype.card (Fin n ⊕ Fin n) : ℝ) * δ⁻¹ * ε := this
      _ = 2 * n * ε / δ := by
        rw [Fintype.card_sum, Fintype.card_fin]
        push_cast
        ring

/-! ### The frame of the perturbed torus -/

/-- Step `step:p2s:pt-domain`: `|Ã - A| ≤ M d` (the segment `[Kθ, K̃θ]` lies in
`𝔹_β(Kθ) ⊆ 𝔅`). -/
theorem norm_linMat_sub_le_M (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {β d : ℝ}
    (hball : Metric.ball (K θ) β ⊆ 𝔅) (hd : ‖K' θ - K θ‖ ≤ d) (hdβ : d < β) :
    ‖linMat h K' θ - linMat h K θ‖ ≤ M * d := by
  have h1 := (ham_mvt hS (K θ) (K' θ - K θ) β hball (lt_of_le_of_lt hd hdβ)).1
  rw [add_sub_cancel] at h1
  have heq : linMat h K' θ - linMat h K θ = sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) (K' θ) -
      fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)) := (PerturbationAux.sqMat_sub _ _).symm
  rw [heq, norm_sqMat]
  exact h1.trans (mul_le_mul_of_nonneg_left hd hS.M_pos.le)

/-- Step `step:p2s:pt-l`: `|L̃ᵀ| ≤ |Lᵀ| + |(L̃ - L)ᵀ| ≤ 2n ϑ̂ σ_K` when `|Lᵀ| ≤ 2n σ_K`,
`|(L̃ - L)ᵀ| ≤ 2n d/δ` and `n d/δ ≤ ϑ σ_K`. -/
theorem norm_transpose_tangentMat_le_vthh {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} {d δ : ℝ} (hn : 1 ≤ n) (hσK : 0 ≤ σK)
    (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * σK)
    (hdLt : ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ 2 * n * d / δ)
    (hs1 : n * d / δ ≤ vth * σK) :
    ‖(tangentMat K' θ)ᵀ‖ ≤ 2 * n * (vthh * σK) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv : vth = 1 / 8 := rfl
  have hvv : vthh = 8 / 7 := rfl
  have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
    rw [Matrix.transpose_sub]
    abel
  have hv0 : 0 ≤ vth * σK := by rw [hv]; positivity
  have h2 : 2 * (n : ℝ) * d / δ ≤ 2 * n * (vth * σK) := by
    calc 2 * (n : ℝ) * d / δ = 2 * (n * d / δ) := by ring
      _ ≤ 2 * (vth * σK) := by linarith
      _ ≤ 2 * n * (vth * σK) := by
          have : (2 : ℝ) ≤ 2 * n := by linarith
          exact mul_le_mul_of_nonneg_right this hv0
  rw [e]
  calc ‖(tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ‖
      ≤ 2 * n * σK + 2 * n * (vth * σK) := (norm_add_le _ _).trans (add_le_add hLt (hdLt.trans h2))
    _ = 2 * n * ((1 + vth) * σK) := by ring
    _ ≤ 2 * n * (vthh * σK) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hσK) (by positivity)
        rw [hv, hvv]
        norm_num

/-! ### The three parts of the torsion polynomial -/

/-- `𝒯_ab = B Lᵀ (A Ω₀) L B - B Lᵀ (Ω₀ A) L B`. -/
def tAB (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (L : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  B * Lᵀ * (A * omegaZeroMatrix n) * L * B - B * Lᵀ * (omegaZeroMatrix n * A) * L * B

/-- `𝒯_F = B Lᵀ (Ω₀ F B)`. -/
def tF (L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  B * Lᵀ * (omegaZeroMatrix n * F * B)

/-- `𝒯_c = B Ω B W B`, `Ω = Lᵀ Ω₀ L`, `W = Lᵀ (Aᵀ + A) L - Fᵀ L - Lᵀ F`. -/
def tC (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  B * (Lᵀ * omegaZeroMatrix n * L) * B * (Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F) * B

/-- `𝒯 = 𝒯_ab + 𝒯_F + 𝒯_c`. -/
theorem torsionPoly_split (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    torsionPoly A L F B = tAB A L B + tF L F B + tC A L F B := by
  simp only [torsionPoly, tAB, tF, tC, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_assoc]

/-- `|𝒯_F| ≤ b ℓ f b`. -/
theorem norm_tF_le {L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    {lt f b : ℝ} (hLt : ‖Lᵀ‖ ≤ lt) (hF : ‖F‖ ≤ f) (hB : ‖B‖ ≤ b) :
    ‖tF L F B‖ ≤ b * lt * (f * b) := by
  have nm := @FrameSharp.norm_mul_le_of_le
  have hOF : ‖omegaZeroMatrix n * F‖ ≤ f := by rw [norm_omegaZeroMatrix_mul]; exact hF
  exact nm (nm hB hLt) (nm hOF hB)

/-- `|W| ≤ ℓᵀ (2M) ℓ + fᵀ ℓ + ℓᵀ f`. -/
theorem norm_W_le {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    {L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ} {M l lt f ft : ℝ} (hA : ‖A‖ ≤ M) (hAt : ‖Aᵀ‖ ≤ M)
    (hL : ‖L‖ ≤ l) (hLt : ‖Lᵀ‖ ≤ lt) (hF : ‖F‖ ≤ f) (hFt : ‖Fᵀ‖ ≤ ft) :
    ‖Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F‖ ≤ lt * (2 * M) * l + ft * l + lt * f := by
  have nm := @FrameSharp.norm_mul_le_of_le
  have hAA : ‖Aᵀ + A‖ ≤ 2 * M := (norm_add_le _ _).trans (by linarith)
  exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add (nm (nm hLt hAA) hL) (nm hFt hL))) (nm hLt hF))

/-- `|𝒯_c| ≤ b w b v b`. -/
theorem norm_tC_le {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ}
    {L F : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ} {B : Matrix (Fin n) (Fin n) ℂ} {b w v : ℝ}
    (hB : ‖B‖ ≤ b) (hΩ : ‖Lᵀ * omegaZeroMatrix n * L‖ ≤ w)
    (hW : ‖Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F‖ ≤ v) :
    ‖tC A L F B‖ ≤ b * w * b * v * b := by
  have nm := @FrameSharp.norm_mul_le_of_le
  exact nm (nm (nm (nm hB hΩ) hB) hW) hB

/-! ### Averages at two frequencies -/

/-- Step `step:p2s:pt-avg`: if the continuous tori `T̃_{ω'}` and `T_ω` differ by at most `D` on
`ℝⁿ`, then `|⟨T̃_{ω'}⟩ - ⟨T_ω⟩| ≤ D` (no periodicity used). -/
theorem norm_torsionAverage_sub_le_any {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω' : Fin n → ℝ} {D : ℝ}
    (hc : Continuous (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))))
    (hc' : Continuous (fun x : Fin n → ℝ => torsion h K' ω' (fun i => (x i : ℂ))))
    (hb : ∀ x : Fin n → ℝ, ‖torsion h K' ω' (fun i => (x i : ℂ)) -
      torsion h K ω (fun i => (x i : ℂ))‖ ≤ D) :
    ‖torsionAverage h K' ω' - torsionAverage h K ω‖ ≤ D := by
  rw [torsionAverage_eq_avg h K ω hc, torsionAverage_eq_avg h K' ω' hc']
  have heq : avg (torsion h K' ω') - avg (torsion h K ω) = torusAverage (fun x : Fin n → ℝ =>
      torsion h K' ω' (fun i => (x i : ℂ)) - torsion h K ω (fun i => (x i : ℂ))) := by
    unfold avg torusAverage
    rw [integral_sub (integrableOn_unitCube_of_continuous hc')
      (integrableOn_unitCube_of_continuous hc)]
  rw [heq]
  exact norm_torusAverage_le fun x _ => hb x

end KAM.Sharp

end
