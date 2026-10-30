/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteA.Correction
public import KAM.Sharp.Perturbation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The frames of the new torus, route A

Lever L8 of `bp:p2s2:constantsA`: the barred factors are bounded by the caps, not by `ϑ̂^k`.
`frames_bar`: for `K̄` holomorphic on `T_{r-2δ}` with `|K̄ - K| ≤ d`, on `T_{r-3δ}` and with `D = d/δ`,

`|L̄ - L| ≤ n D`, `|(L̄ - L)ᵀ| ≤ 2n D`, `|B̄ - B| ≤ C_B D`, `|N̄ - N| ≤ C_N̄ D`, `|N̄ᵀ - Nᵀ| ≤ C_N̄ᵀ D`,

using the caps `|L̄ᵀ| ≤ σ_{Lᵀ}` and `|B̄| ≤ σ_B` (given by the budgets of the engine) and the Neumann
condition `σ_B C_G D ≤ ϑ`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteA

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

/-- The frame increments of `K'` over `K` at `θ`, with `D = d/δ`. -/
structure BarBd (p : StepInA) (K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (D : ℝ) : Prop where
  dDK : ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ n * D
  dLt : ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ 2 * n * D
  unit : IsUnit (gramMatrix K' θ).det
  dB : ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ p.CB * D
  dN : ‖normalMat K' θ - normalMat K θ‖ ≤ p.CNd * D
  dNt : ‖(normalMat K' θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ p.CNtd * D

theorem norm_le_add_sub {E : Type*} [NormedAddCommGroup E] {a b : E} {x y : ℝ} (h1 : ‖b‖ ≤ x)
    (h2 : ‖a - b‖ ≤ y) : ‖a‖ ≤ x + y :=
  (norm_le_norm_add_norm_sub' a b).trans (add_le_add h1 h2)

/-- Lever L8: the frame of the new torus with caps for the barred factors. -/
theorem frames_bar {p : StepInA} (hp : p.Pos) (hpn : p.n = n)
    {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r δ d mLt mB : ℝ}
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hL : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ p.sK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ mB)
    (hLt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ mLt)
    (hmLt : mLt ≤ p.sLt) (hmB : mB ≤ p.sB)
    (hδ : 0 < δ) (hK' : DifferentiableOn ℂ K' (complexStrip n (r - 2 * δ)))
    (hd : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖K' θ - K θ‖ ≤ d)
    (hgr : p.sB * (p.CGr * (d / δ)) ≤ p.th)
    (hcLt : mLt + 2 * n * (d / δ) ≤ p.sLt) (hcB : mB + p.CB * (d / δ) ≤ p.sB) :
    ∀ θ ∈ complexStrip n (r - 3 * δ), BarBd p K K' θ (d / δ) := by
  subst hpn
  intro θ hθ
  have hsub2r : complexStrip p.n (r - 2 * δ) ⊆ complexStrip p.n r :=
    PerturbationAux.complexStrip_mono (by linarith)
  have hθr : θ ∈ complexStrip p.n r := PerturbationAux.complexStrip_mono (by linarith) hθ
  have hθ' : θ ∈ complexStrip p.n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  have hKd := hK.mono hsub2r
  have hD : 0 ≤ d / δ := by
    have h0 := (norm_nonneg _).trans (hd θ (PerturbationAux.complexStrip_mono (by linarith) hθ))
    exact div_nonneg h0 hδ.le
  have hn0 : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  have hdL : ‖fderiv ℂ K' θ - fderiv ℂ K θ‖ ≤ p.n * (d / δ) := by
    have := PerturbationAux.norm_fderiv_sub_le hKd hK' hd hδ θ hθ'
    rwa [mul_div_assoc] at this
  have hdLt : ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ ≤ 2 * p.n * (d / δ) := by
    have := PerturbationAux.norm_transpose_tangentMat_sub_le hKd hK' hd hδ θ hθ'
    rwa [mul_div_assoc] at this
  have hdL' : ‖tangentMat K' θ - tangentMat K θ‖ ≤ p.n * (d / δ) := by
    rw [PerturbationAux.norm_tangentMat_sub]; exact hdL
  have hLtθ := hLt θ hθr
  have hLθ := hL θ hθr
  have hLt' : ‖(tangentMat K' θ)ᵀ‖ ≤ p.sLt := by
    have e : (tangentMat K' θ)ᵀ = (tangentMat K θ)ᵀ + (tangentMat K' θ - tangentMat K θ)ᵀ := by
      rw [Matrix.transpose_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans ((add_le_add hLtθ hdLt).trans hcLt)
  have hGd : ‖gramMatrix K' θ - gramMatrix K θ‖ ≤ p.CGr * (d / δ) := by
    rw [PerturbationAux.gramMatrix_sub]
    calc _ ≤ ‖(tangentMat K' θ)ᵀ‖ * ‖tangentMat K' θ - tangentMat K θ‖ +
          ‖(tangentMat K' θ - tangentMat K θ)ᵀ‖ * ‖tangentMat K θ‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.linfty_opNorm_mul _ _)
            (Matrix.linfty_opNorm_mul _ _))
      _ ≤ p.sLt * (p.n * (d / δ)) + 2 * p.n * (d / δ) * p.sK :=
          add_le_add (mul_le_mul hLt' hdL' (norm_nonneg _) hp.sLt)
            (mul_le_mul hdLt hLθ (norm_nonneg _) (by positivity))
      _ = p.CGr * (d / δ) := by unfold StepInA.CGr; ring
  obtain ⟨hGu, hBθ⟩ := hG θ hθr
  have hBθ' : ‖(gramMatrix K θ)⁻¹‖ ≤ p.sB := hBθ.trans hmB
  have hA : IsUnit (gramMatrix K θ) := (Matrix.isUnit_iff_isUnit_det _).2 hGu
  have hsmall : ‖(gramMatrix K θ)⁻¹‖ * ‖gramMatrix K' θ - gramMatrix K θ‖ ≤ p.th :=
    (mul_le_mul hBθ' hGd (norm_nonneg _) hp.sB).trans hgr
  obtain ⟨hU, -, hBdiff⟩ := neumann_ratio hA hp.th1 hsmall
  rw [add_sub_cancel] at hU hBdiff
  have hth := hp.one_sub_th
  have hdB : ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ p.CB * (d / δ) := by
    have hBB : ‖(gramMatrix K θ)⁻¹‖ ^ 2 ≤ p.sB ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hBθ' 2
    calc _ ≤ ‖(gramMatrix K θ)⁻¹‖ ^ 2 * ‖gramMatrix K' θ - gramMatrix K θ‖ / (1 - p.th) := hBdiff
      _ ≤ p.sB ^ 2 * (p.CGr * (d / δ)) / (1 - p.th) :=
          div_le_div_of_nonneg_right (mul_le_mul hBB hGd (norm_nonneg _) (by positivity)) hth.le
      _ = p.CB * (d / δ) := by unfold StepInA.CB; ring
  have hB' : ‖(gramMatrix K' θ)⁻¹‖ ≤ p.sB :=
    (norm_le_add_sub hBθ hdB).trans hcB
  have hdN : ‖normalMat K' θ - normalMat K θ‖ ≤ p.CNd * (d / δ) := by
    rw [PerturbationAux.normalMat_sub]
    have a1 : ‖omegaZeroMatrix p.n * (tangentMat K' θ - tangentMat K θ) *
        (gramMatrix K' θ)⁻¹‖ ≤ p.n * (d / δ) * p.sB := by
      refine FrameSharp.norm_mul_le_of_le ?_ hB'
      rw [norm_omegaZeroMatrix_mul]
      exact hdL'
    have a2 : ‖omegaZeroMatrix p.n * tangentMat K θ *
        ((gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹)‖ ≤ p.sK * (p.CB * (d / δ)) := by
      refine FrameSharp.norm_mul_le_of_le ?_ hdB
      rw [norm_omegaZeroMatrix_mul]
      exact hLθ
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ p.n * (d / δ) * p.sB + p.sK * (p.CB * (d / δ)) := add_le_add a1 a2
      _ = p.CNd * (d / δ) := by unfold StepInA.CNd; ring
  have hdNt : ‖(normalMat K' θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ p.CNtd * (d / δ) := by
    rw [← norm_mul_omegaZeroMatrix, Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
      TorsionPoly.normalMat_transpose_mul_omega]
    have hdLt'' : ‖(tangentMat K' θ)ᵀ - (tangentMat K θ)ᵀ‖ ≤ 2 * p.n * (d / δ) := by
      rw [← Matrix.transpose_sub]; exact hdLt
    calc _ ≤ ‖(gramMatrix K' θ)⁻¹‖ * ‖(tangentMat K' θ)ᵀ - (tangentMat K θ)ᵀ‖ +
          ‖(gramMatrix K' θ)⁻¹ - (gramMatrix K θ)⁻¹‖ * ‖(tangentMat K θ)ᵀ‖ :=
          norm_mul_sub_mul_le _ _ _ _
      _ ≤ p.sB * (2 * p.n * (d / δ)) + p.CB * (d / δ) * p.sLt :=
          add_le_add (mul_le_mul hB' hdLt'' (norm_nonneg _) hp.sB)
            (mul_le_mul hdB (hLtθ.trans hmLt) (norm_nonneg _) (mul_nonneg hp.CB hD))
      _ = p.CNtd * (d / δ) := by unfold StepInA.CNtd; ring
  exact ⟨hdL, hdLt, (Matrix.isUnit_iff_isUnit_det _).1 hU, hdB, hdN, hdNt⟩

end KAM.Sharp2.RouteA

end
