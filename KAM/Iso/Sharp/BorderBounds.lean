/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.BorderSolve
public import KAM.Sharp.CohData
import Mathlib.Tactic.Linarith

/-!
# Bounds for the bordered triangular system with general small-divisor data

`KAM.Iso.Sharp.border_bounds` (blueprint `bpI:p2s:border`) is clause (c) of
`KAM.Iso.Linear.border_solve` with the factor `Γ_δ = c_R γ⁻¹ δ^{-κ}` of an arbitrary
`KAM.Sharp.CohData`. Clauses (a), (b), (d), (e) do not depend on the constants and are
`border_solve` itself. The proof is that of `border_solve` (c): the helpers
`KAM.Iso.Linear.BorderSolve.norm_bordSol_le` and `norm_bordXiN_bordGL_le` are generic in the bound
`Z` of `uᴺ`, and `CohData.sol` supplies `Z` and the bound of `𝓡 gᴸ`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Sharp KAM.Iso.Linear.BorderSolve

variable {n : ℕ} {κ cR : ℝ}

/-- Blueprint `bpI:p2s:border`: clause (c) of `KAM.Iso.Linear.border_solve` with
`Γ_δ = c_R γ⁻¹ δ^{-κ}` (clauses (a), (b), (d), (e) are `border_solve` itself). -/
theorem border_bounds {τ γ : ℝ} {ω : Fin n → ℝ} (hC : CohData n τ κ cR) (hγ : 0 < γ)
    (hdio : IsDiophantine γ τ ω) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) (d : BordData n) {HL HN HT HY σ : ℝ}
    (hηL : DifferentiableOn ℂ d.ηL (complexStrip n r)) (hηLp : IsPeriodicOn d.ηL r)
    (hηN : DifferentiableOn ℂ d.ηN (complexStrip n r)) (hηNp : IsPeriodicOn d.ηN r)
    (hHL : ∀ θ ∈ complexStrip n r, ‖d.ηL θ‖ ≤ HL) (hHN : ∀ θ ∈ complexStrip n r, ‖d.ηN θ‖ ≤ HN)
    (hηN0 : avg d.ηN = 0) (hT : DifferentiableOn ℂ d.T (complexStrip n r))
    (hTp : IsPeriodicOn d.T r)
    (hY : DifferentiableOn ℂ d.Y (complexStrip n r)) (hYp : IsPeriodicOn d.Y r)
    (hHT : ∀ θ ∈ complexStrip n (r - δ), ‖d.T θ‖ ≤ HT)
    (hHY : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖d.Y θ b‖ ≤ HY)
    (hinv : IsUnit (bordAvg ω d).det) (hσ : ‖(bordAvg ω d)⁻¹‖ ≤ σ) (ξL0 : Fin n → ℂ) :
    ‖bordSol ω d‖ ≤ σ * max (HL + HT * (cR * γ⁻¹ * δ ^ (-κ)) * HN)
        (‖d.ηω‖ + HY * (cR * γ⁻¹ * δ ^ (-κ)) * HN) ∧
    ∀ S, ‖bordSol ω d‖ ≤ S →
      (∀ θ ∈ complexStrip n (r - δ),
        ‖bordXiN ω d θ‖ ≤ S + cR * γ⁻¹ * δ ^ (-κ) * HN ∧
        ‖bordGL ω d θ‖ ≤ HT * (S + cR * γ⁻¹ * δ ^ (-κ) * HN) + ‖ω‖ * S + HL) ∧
      ∀ G, (∀ θ ∈ complexStrip n (r - δ), ‖bordGL ω d θ‖ ≤ G) →
        ∀ θ ∈ complexStrip n (r - 2 * δ),
          ‖bordXiL ω d ξL0 θ - ξL0‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * G := by
  have hδr : δ < r := by linarith
  have hr1 : 0 < r - δ := by linarith
  have hsub : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hrr : r - δ - δ = r - 2 * δ := by ring
  have hHN0 : 0 ≤ HN := (norm_nonneg _).trans (hHN _ (ofReal_mem_complexStrip hr 0))
  obtain ⟨⟨-, -, hgd, hgp, hg0, -, -⟩, -⟩ := border_solve hγ hC.tau_nonneg hdio hr hδ h2δ d hηL
    hηLp hηN hηNp hHL hHN hηN0 hT hTp hY hYp hHT hHY hinv hσ ξL0
  have hU : ∀ θ ∈ complexStrip n (r - δ), ‖triU ω d.ηN θ‖ ≤ cR * γ⁻¹ * δ ^ (-κ) * HN :=
    hC.sol hγ hdio hδ hδ1 hδr d.ηN HN hηN hηNp hHN hηN0
  have e1 : HT * (cR * γ⁻¹ * δ ^ (-κ)) * HN = HT * (cR * γ⁻¹ * δ ^ (-κ) * HN) := mul_assoc _ _ _
  have e2 : ‖d.ηω‖ + HY * (cR * γ⁻¹ * δ ^ (-κ)) * HN =
      ‖d.ηω‖ + HY * (cR * γ⁻¹ * δ ^ (-κ) * HN) := by rw [mul_assoc]
  have hS := norm_bordSol_le (ω := ω) d hr hr1 hHL hHT hHY hU hσ
  refine ⟨by rw [e1, e2]; exact hS, fun S hS' => ⟨fun θ hθ =>
    norm_bordXiN_bordGL_le ω d hS' hU (fun θ hθ => hHL θ (hsub hθ)) hHT hθ, fun G hG θ hθ => ?_⟩⟩
  have hb := hC.sol hγ hdio hδ hδ1 (by linarith : δ < r - δ) (bordGL ω d) G hgd hgp hG hg0
  rw [hrr] at hb
  simpa [bordXiL] using hb θ hθ

end KAM.Iso.Sharp

end
