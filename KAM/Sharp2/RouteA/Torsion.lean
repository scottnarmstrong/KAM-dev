/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Frames
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

/-!
# The change of the torsion, route A

`torsion_sub_le` (lever L8 of `bp:p2s2:constantsA`): at a point of `T_{r-3δ}`, with `D = d/δ`,

`|T̄_{ω₂} - T_{ω₁}| ≤ (C_Δab + C_Δc) D + 2n σ_{Nᵀ} σ_B ε/δ + 2σ_B³ w W`,

where `W` bounds `|Ω_K|`, for any two frequencies. Both torsions are torsion polynomials
(`KAM.Sharp.torsion_identity`). `𝒯_ab = Y (A Ω₀ - Ω₀ A) Z` with `Y = B Lᵀ = Nᵀ Ω₀` and `Ω₀ Z = N` is
telescoped; `𝒯_F`, `𝒯_c` are bounded for each torus (`|Ω̄_K| ≤ |Ω_K| + (2nσ_K + nσ_{Lᵀ}) D`). No
small-divisor constant at a later bite enters: the Lagrangian defect of the new torus is bounded from
that of `K` (audit finding F8 concerns route B only).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ} {τ M σK σB σT : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {γ : ℝ}

/-- `|Ā - A| ≤ M₂ d`. -/
theorem norm_linMat_sub_le_M2 (hS : Standing n τ M σK σB σT 𝔅 h ω γ) {M2 : ℝ}
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M2) (hM2 : 0 ≤ M2)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {β d : ℝ}
    (hball : Metric.ball (K θ) β ⊆ 𝔅) (hd : ‖K' θ - K θ‖ ≤ d) (hdβ : d < β) :
    ‖linMat h K' θ - linMat h K θ‖ ≤ M2 * d := by
  have hw : ‖K' θ - K θ‖ < β := lt_of_le_of_lt hd hdβ
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg _) hw
  have hzw : K θ + (K' θ - K θ) ∈ Metric.ball (K θ) β := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ (K θ) (K θ + (K' θ - K θ)) ⊆ Metric.ball (K θ) β :=
    (convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hzw
  have h1 := increments_open (Metric.isOpen_ball (x := K θ) (ε := β))
    ((differentiableOn_fderiv_ham hS).mono hball) (A := M2) (fun x hx => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℂ), norm_iteratedFDeriv_fderiv]
      exact hd2 x (hball hx)) hseg
  rw [add_sub_cancel] at h1
  have heq : linMat h K' θ - linMat h K θ = sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) (K' θ) -
      fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ)) := (PerturbationAux.sqMat_sub _ _).symm
  rw [heq, norm_sqMat]
  exact h1.trans (mul_le_mul_of_nonneg_left hd hM2)

/-- `‖P Q R‖ ≤ ‖P‖ ‖Q‖ ‖R‖`. -/
theorem norm_triple_le {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (P : Matrix a b ℂ) (Q : Matrix b c ℂ) (R : Matrix c e ℂ) :
    ‖P * Q * R‖ ≤ ‖P‖ * ‖Q‖ * ‖R‖ :=
  (Matrix.linfty_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))

/-- The three-factor telescoping. -/
theorem triple_sub_le {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (X X' : Matrix a b ℂ) (Y Y' : Matrix b c ℂ) (Z Z' : Matrix c e ℂ) :
    ‖X' * Y' * Z' - X * Y * Z‖ ≤
      ‖X' - X‖ * ‖Y'‖ * ‖Z'‖ + ‖X‖ * ‖Y' - Y‖ * ‖Z'‖ + ‖X‖ * ‖Y‖ * ‖Z' - Z‖ := by
  have hid : X' * Y' * Z' - X * Y * Z =
      (X' - X) * Y' * Z' + X * (Y' - Y) * Z' + X * Y * (Z' - Z) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (norm_triple_le _ _ _) (norm_triple_le _ _ _))) (norm_triple_le _ _ _))

/-- `𝒯_ab = Y (A Ω₀ - Ω₀ A) Z`. -/
theorem tAB_eq (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (L : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    tAB A L B = (B * Lᵀ) * (A * omegaZeroMatrix n - omegaZeroMatrix n * A) * (L * B) := by
  simp only [tAB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- `|B Lᵀ| = |Nᵀ|`. -/
theorem norm_B_Lt (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ = ‖(normalMat K θ)ᵀ‖ := by
  rw [← TorsionPoly.normalMat_transpose_mul_omega, norm_mul_omegaZeroMatrix]

/-- `|L B| = |N|`. -/
theorem norm_L_B (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    ‖tangentMat K θ * (gramMatrix K θ)⁻¹‖ = ‖normalMat K θ‖ := by
  rw [← norm_omegaZeroMatrix_mul, normalMat, Matrix.mul_assoc]

/-- `|Ā Ω₀ - Ω₀ Ā| ≤ 2 M₁` for `|Ā| ≤ M₁`. -/
theorem norm_comm_le {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ} {m : ℝ} (hA : ‖A‖ ≤ m) :
    ‖A * omegaZeroMatrix n - omegaZeroMatrix n * A‖ ≤ 2 * m := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul]
  linarith

/-- Blueprint step `step:p2s:pt-tt` with lever L8: the change of the torsion at a point of
`T_{r-3δ}`, in terms of the frame increments `BarBd`, for two arbitrary frequencies. -/
theorem torsion_sub_le {p : StepInA} (hp : p.Pos) (hpn : p.n = n)
    (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    (hd1 : ∀ z ∈ 𝔅, ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ p.M1)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ p.M2)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω₁ ω₂ : Fin n → ℝ}
    {r β d δ ε ε' Wb : ℝ} {θ : Fin n → ℂ} (hr : 0 < r) (hδ : 0 < δ) (hδD : δ ≤ p.δ)
    (h3δ : 3 * δ < r) (hθ : θ ∈ complexStrip n (r - 3 * δ))
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ 𝔅)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det)
    (hE : ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω₁ θ‖ ≤ ε)
    (hK' : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)))
    (hK'𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), K' θ ∈ 𝔅)
    (hG' : ∀ θ ∈ complexStrip n (r - 3 * δ), IsUnit (gramMatrix K' θ).det)
    (hE' : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖invarianceError h K' ω₂ θ‖ ≤ ε')
    (hball : Metric.ball (K θ) β ⊆ 𝔅) (hd : ‖K' θ - K θ‖ ≤ d) (hdβ : d < β)
    (hε : 0 ≤ ε) (hεε : ε' ≤ ε) (hεδ : ε ≤ δ)
    (hL : ‖tangentMat K θ‖ ≤ p.sK) (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ p.sLt)
    (hNt : ‖(normalMat K θ)ᵀ‖ ≤ p.sNt) (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ p.sB)
    (hL' : ‖tangentMat K' θ‖ ≤ p.sK) (hLt' : ‖(tangentMat K' θ)ᵀ‖ ≤ p.sLt)
    (hN' : ‖normalMat K' θ‖ ≤ p.sN) (hNt' : ‖(normalMat K' θ)ᵀ‖ ≤ p.sNt)
    (hB' : ‖(gramMatrix K' θ)⁻¹‖ ≤ p.sB) (hW : ‖lagrangeMat K θ‖ ≤ Wb)
    (hbar : BarBd p K K' θ (d / δ)) :
    ‖torsion h K' ω₂ θ - torsion h K ω₁ θ‖ ≤
      (p.CDab + p.CDc) * (d / δ) + 2 * n * p.sNt * p.sB * (ε / δ) + 2 * p.sB ^ 3 * p.w * Wb := by
  subst hpn
  have hsub32 : complexStrip p.n (r - 3 * δ) ⊆ complexStrip p.n (r - 2 * δ) :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hθ2 := hsub32 hθ
  have hr3 : 0 < r - 3 * δ := by linarith
  have hθr : θ ∈ complexStrip p.n r := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hθ1 : θ ∈ complexStrip p.n (r - δ) := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hθ2' : θ ∈ complexStrip p.n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  set D := d / δ with hDdef
  have hD0 : 0 ≤ D := div_nonneg hd0 hδ.le
  have hdeq : d = δ * D := by rw [hDdef]; field_simp
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hK'θ := hK'𝔅 θ hθ2
  -- the linearisations
  have hA : ‖linMat h K θ‖ ≤ p.M1 := by
    rw [FrameAux.norm_linMat]; exact hd1 _ (hK𝔅 θ hθr)
  have hA' : ‖linMat h K' θ‖ ≤ p.M1 := by
    rw [FrameAux.norm_linMat]; exact hd1 _ hK'θ
  have hAt : ‖(linMat h K θ)ᵀ‖ ≤ p.M1 := by
    rw [FrameSharp.linMat_transpose hS (hK𝔅 θ hθr), norm_mul_omegaZeroMatrix,
      norm_omegaZeroMatrix_mul]
    exact hA
  have hAt' : ‖(linMat h K' θ)ᵀ‖ ≤ p.M1 := by
    rw [FrameSharp.linMat_transpose hS hK'θ, norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul]
    exact hA'
  have hdA := norm_linMat_sub_le_M2 hS hd2 hp.M2 hball hd hdβ
  -- the derivatives of the errors
  obtain ⟨hF, hFt⟩ := geo_de_any hS hK hK𝔅 hE hδ θ hθ1
  obtain ⟨hF', hF't⟩ := geo_de_any hS hK' hK'𝔅 hE' hδ θ hθ2'
  have hε'0 : 0 ≤ ε' := (norm_nonneg _).trans (hE' θ hθ2)
  have hεδ1 : ε / δ ≤ 1 := (div_le_one hδ).2 hεδ
  have hε'δ1 : ε' / δ ≤ 1 := (div_le_one hδ).2 (hεε.trans hεδ)
  have hεδ0 : 0 ≤ ε / δ := div_nonneg hε hδ.le
  have hε'δ0 : 0 ≤ ε' / δ := div_nonneg hε'0 hδ.le
  have hsK := hp.sK
  have hsB := hp.sB
  have hsLt := hp.sLt
  have hsN := hp.sN
  have hsNt := hp.sNt
  have hM1 := hp.M1
  have hM2 := hp.M2
  -- both torsions as torsion polynomials
  rw [(torsion_identity hS hr3 (hK'.mono hsub32) (fun θ hθ => hK'𝔅 θ (hsub32 hθ)) hG' ω₂ θ
      hθ).2.2, (torsion_identity hS hr hK hK𝔅 hG ω₁ θ hθr).2.2, torsionPoly_split,
    torsionPoly_split]
  set A := linMat h K θ
  set A' := linMat h K' θ
  set L := tangentMat K θ
  set L' := tangentMat K' θ
  set F := errDerivMat h K ω₁ θ
  set F' := errDerivMat h K' ω₂ θ
  set B := (gramMatrix K θ)⁻¹
  set B' := (gramMatrix K' θ)⁻¹
  -- the part `𝒯_ab`
  have hY : ‖B * Lᵀ‖ ≤ p.sNt := by rw [norm_B_Lt]; exact hNt
  have hdY : ‖B' * L'ᵀ - B * Lᵀ‖ ≤ p.CNtd * D := by
    have := hbar.dNt
    rwa [← norm_mul_omegaZeroMatrix, Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
      TorsionPoly.normalMat_transpose_mul_omega] at this
  have hZ' : ‖L' * B'‖ ≤ p.sN := by rw [norm_L_B]; exact hN'
  have hdZ : ‖L' * B' - L * B‖ ≤ p.CNd * D := by
    have := hbar.dN
    rw [← norm_omegaZeroMatrix_mul, Matrix.mul_sub]
    simpa only [normalMat, Matrix.mul_assoc] using this
  have hX : ‖A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A‖ ≤ 2 * p.M1 := norm_comm_le hA
  have hX' : ‖A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A'‖ ≤ 2 * p.M1 := norm_comm_le hA'
  have hdX : ‖(A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A') -
      (A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A)‖ ≤ 2 * (p.M2 * d) := by
    have e : (A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A') -
        (A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A) =
        (A' - A) * omegaZeroMatrix p.n - omegaZeroMatrix p.n * (A' - A) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub]
      abel
    rw [e]
    exact norm_comm_le hdA
  have hab : ‖tAB A' L' B' - tAB A L B‖ ≤ p.CDab * D := by
    rw [tAB_eq, tAB_eq]
    refine (triple_sub_le _ _ _ _ _ _).trans ?_
    have h1 : ‖B' * L'ᵀ - B * Lᵀ‖ * ‖A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A'‖ *
        ‖L' * B'‖ ≤ p.CNtd * D * (2 * p.M1) * p.sN :=
      mul_le_mul (mul_le_mul hdY hX' (norm_nonneg _) (mul_nonneg hp.CNtd hD0)) hZ' (norm_nonneg _)
        (mul_nonneg (mul_nonneg hp.CNtd hD0) (by positivity))
    have h2 : ‖B * Lᵀ‖ * ‖(A' * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A') -
        (A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A)‖ * ‖L' * B'‖ ≤
        p.sNt * (2 * (p.M2 * d)) * p.sN :=
      mul_le_mul (mul_le_mul hY hdX (norm_nonneg _) hsNt) hZ' (norm_nonneg _)
        (mul_nonneg hsNt (by positivity))
    have h3 : ‖B * Lᵀ‖ * ‖A * omegaZeroMatrix p.n - omegaZeroMatrix p.n * A‖ *
        ‖L' * B' - L * B‖ ≤ p.sNt * (2 * p.M1) * (p.CNd * D) :=
      mul_le_mul (mul_le_mul hY hX (norm_nonneg _) hsNt) hdZ (norm_nonneg _)
        (mul_nonneg hsNt (by positivity))
    have h4 : p.sNt * (2 * (p.M2 * d)) * p.sN ≤ 2 * p.M2 * p.sNt * p.sN * p.δ * D := by
      rw [hdeq]
      have : p.sNt * (2 * (p.M2 * (δ * D))) * p.sN = 2 * p.M2 * p.sNt * p.sN * D * δ := by ring
      rw [this]
      have h5 := mul_le_mul_of_nonneg_left hδD
        (show 0 ≤ 2 * p.M2 * p.sNt * p.sN * D by positivity)
      linarith
    calc _ ≤ p.CNtd * D * (2 * p.M1) * p.sN + 2 * p.M2 * p.sNt * p.sN * p.δ * D +
          p.sNt * (2 * p.M1) * (p.CNd * D) := add_le_add (add_le_add h1 (h2.trans h4)) h3
      _ = p.CDab * D := by unfold StepInA.CDab; ring
  -- the part `𝒯_F`
  have hfF : ∀ {X : Matrix (Fin p.n ⊕ Fin p.n) (Fin p.n) ℂ} {f : ℝ}, ‖X‖ ≤ f → (hb : ‖B'‖ ≤ p.sB) →
      ‖tF L' X B'‖ ≤ p.sNt * (f * p.sB) := fun {X f} hXf hb => by
    have hOF : ‖omegaZeroMatrix p.n * X‖ ≤ f := by rw [norm_omegaZeroMatrix_mul]; exact hXf
    have hY' : ‖B' * L'ᵀ‖ ≤ p.sNt := by rw [norm_B_Lt]; exact hNt'
    exact FrameSharp.norm_mul_le_of_le hY' (FrameSharp.norm_mul_le_of_le hOF hb)
  have hfF0 : ‖tF L F B‖ ≤ p.sNt * (p.n * ε / δ * p.sB) := by
    have hOF : ‖omegaZeroMatrix p.n * F‖ ≤ p.n * ε / δ := by
      rw [norm_omegaZeroMatrix_mul]; exact hF
    exact FrameSharp.norm_mul_le_of_le hY (FrameSharp.norm_mul_le_of_le hOF hB)
  have hF2 : ‖tF L' F' B' - tF L F B‖ ≤ 2 * p.n * p.sNt * p.sB * (ε / δ) := by
    have h1 := hfF hF' hB'
    have hle : (p.n : ℝ) * ε' / δ ≤ p.n * ε / δ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hεε hn0) hδ.le
    have h2 : p.sNt * (p.n * ε' / δ * p.sB) ≤ p.sNt * (p.n * ε / δ * p.sB) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hsB) hsNt
    calc ‖tF L' F' B' - tF L F B‖ ≤ ‖tF L' F' B'‖ + ‖tF L F B‖ := norm_sub_le _ _
      _ ≤ p.sNt * (p.n * ε / δ * p.sB) + p.sNt * (p.n * ε / δ * p.sB) :=
          add_le_add (h1.trans h2) hfF0
      _ = 2 * p.n * p.sNt * p.sB * (ε / δ) := by ring
  -- the part `𝒯_c`
  have hWw : ‖Lᵀ * (Aᵀ + A) * L - Fᵀ * L - Lᵀ * F‖ ≤ p.w := by
    refine (norm_W_le hA hAt hL hLt hF hFt).trans ?_
    have e : p.sLt * (2 * p.M1) * p.sK + 2 * p.n * ε / δ * p.sK + p.sLt * (p.n * ε / δ) =
        2 * p.M1 * p.sLt * p.sK + (2 * p.n * p.sK + p.n * p.sLt) * (ε / δ) := by ring
    rw [e]
    unfold StepInA.w
    have : (2 * (p.n : ℝ) * p.sK + p.n * p.sLt) * (ε / δ) ≤ 2 * p.n * p.sK + p.n * p.sLt :=
      mul_le_of_le_one_right (by positivity) hεδ1
    linarith
  have hWw' : ‖L'ᵀ * (A'ᵀ + A') * L' - F'ᵀ * L' - L'ᵀ * F'‖ ≤ p.w := by
    refine (norm_W_le hA' hAt' hL' hLt' hF' hF't).trans ?_
    have e : p.sLt * (2 * p.M1) * p.sK + 2 * p.n * ε' / δ * p.sK + p.sLt * (p.n * ε' / δ) =
        2 * p.M1 * p.sLt * p.sK + (2 * p.n * p.sK + p.n * p.sLt) * (ε' / δ) := by ring
    rw [e]
    unfold StepInA.w
    have : (2 * (p.n : ℝ) * p.sK + p.n * p.sLt) * (ε' / δ) ≤ 2 * p.n * p.sK + p.n * p.sLt :=
      mul_le_of_le_one_right (by positivity) hε'δ1
    linarith
  have hdΩ : ‖L'ᵀ * omegaZeroMatrix p.n * L' - Lᵀ * omegaZeroMatrix p.n * L‖ ≤
      (2 * p.n * p.sK + p.n * p.sLt) * D := by
    have e : L'ᵀ * omegaZeroMatrix p.n * L' - Lᵀ * omegaZeroMatrix p.n * L =
        (L' - L)ᵀ * omegaZeroMatrix p.n * L' + Lᵀ * omegaZeroMatrix p.n * (L' - L) := by
      simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    have hdL' : ‖L' - L‖ ≤ p.n * D := by
      rw [PerturbationAux.norm_tangentMat_sub]; exact hbar.dDK
    rw [e]
    have nm := @FrameSharp.norm_mul_le_of_le
    have a1 : ‖(L' - L)ᵀ * omegaZeroMatrix p.n * L'‖ ≤ 2 * p.n * D * p.sK := by
      refine nm ?_ hL'
      rw [norm_mul_omegaZeroMatrix]; exact hbar.dLt
    have a2 : ‖Lᵀ * omegaZeroMatrix p.n * (L' - L)‖ ≤ p.sLt * (p.n * D) := by
      refine nm ?_ hdL'
      rw [norm_mul_omegaZeroMatrix]; exact hLt
    calc _ ≤ 2 * p.n * D * p.sK + p.sLt * (p.n * D) := (norm_add_le _ _).trans (add_le_add a1 a2)
      _ = (2 * p.n * p.sK + p.n * p.sLt) * D := by ring
  have hΩ : ‖Lᵀ * omegaZeroMatrix p.n * L‖ ≤ Wb := hW
  have hΩ' : ‖L'ᵀ * omegaZeroMatrix p.n * L'‖ ≤ Wb + (2 * p.n * p.sK + p.n * p.sLt) * D :=
    norm_le_add_sub hΩ hdΩ
  have hc1 := norm_tC_le (A := A') (F := F') hB' hΩ' hWw'
  have hc0 := norm_tC_le (A := A) (F := F) hB hΩ hWw
  have hC2 : ‖tC A' L' F' B' - tC A L F B‖ ≤ p.CDc * D + 2 * p.sB ^ 3 * p.w * Wb := by
    refine (norm_sub_le _ _).trans ((add_le_add hc1 hc0).trans (le_of_eq ?_))
    unfold StepInA.CDc
    ring
  have e : tAB A' L' B' + tF L' F' B' + tC A' L' F' B' - (tAB A L B + tF L F B + tC A L F B) =
      (tAB A' L' B' - tAB A L B) + (tF L' F' B' - tF L F B) + (tC A' L' F' B' - tC A L F B) := by
    abel
  rw [e]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hab hF2))
    hC2)).trans (le_of_eq ?_)
  ring

end KAM.Sharp2.RouteA

end
