/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.TorsionRef
public import KAM.Apost.Triangular

/-!
# The objects of the repaired modified step (`bp:p2s2:step`)

The definitions of `APOST-SHARP-V2-SIGNATURES.lean.txt` (module `KAM/Sharp2/ModStepB.lean`),
verbatim:

* `ξᴺ₀ = ⟨T⟩⁻¹ ⟨ηᴸ + T 𝓡ηᴺ⟩` (`modXiN0`), `ξᴺ = ξᴺ₀ - 𝓡ηᴺ` (`modXiN`), `K̃ = K + N ξᴺ`
  (`modKtilde`), `ξᴸ = -𝓡(ηᴸ - T ξᴺ)` (`modXiL`), `K̄ = K̃ ∘ (id + ξᴸ)` on `T_w` (`modNewton`).

and their agreement with the triangular objects of v1 (`KAM.Apost.triXi0`, `triXiN`, `triXiL`,
`bp:p2:triangular`), whose regularity, periodicity, cohomological equations and reality are
proved there: `modXiN0_eq`, `modXiN_eq`, `modXiL_eq` (`cohR_neg`: `𝓡(-g) = -𝓡g`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost

variable {n : ℕ}

/-- `ξᴺ₀ = ⟨T⟩⁻¹ ⟨ηᴸ + T 𝓡ηᴺ⟩`. -/
def modXiN0 (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) : Fin n → ℂ :=
  (torsionAverage h K ω)⁻¹ *ᵥ
    avg (fun θ => etaL h K ω θ + torsion h K ω θ *ᵥ cohR ω (etaN h K ω) θ)

/-- `ξᴺ = ξᴺ₀ - 𝓡ηᴺ`. -/
def modXiN (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) : Fin n → ℂ :=
  modXiN0 h K ω - cohR ω (etaN h K ω) θ

/-- `K̃ = K + N ξᴺ`. -/
def modKtilde (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  K θ + (sumVec n).symm (normalMat K θ *ᵥ modXiN h K ω θ)

/-- `ξᴸ = -𝓡(ηᴸ - T ξᴺ)`. -/
def modXiL (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) : Fin n → ℂ :=
  -cohR ω (fun θ' => etaL h K ω θ' - torsion h K ω θ' *ᵥ modXiN h K ω θ') θ

open Classical in
/-- `K̄ = K̃ ∘ (id + ξᴸ)` on `T_w`, `K` elsewhere (`w = r - 2δ`). -/
def modNewton (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (w : ℝ) : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => if θ ∈ complexStrip n w then modKtilde h K ω (θ + modXiL h K ω θ) else K θ

namespace ModStepB

variable {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  {ω : Fin n → ℝ}

/-- `𝓡(-g) = -𝓡 g` (no hypothesis: every step of `cohSolution` is odd). -/
theorem cohR_neg {p : ℕ} (ω : Fin n → ℝ) (g : (Fin n → ℂ) → Fin p → ℂ) :
    cohR ω (fun θ => -g θ) = fun θ => -cohR ω g θ := by
  funext θ i
  have hc : torusCoeff (fun x => -g (fun j => (x j : ℂ)) i) =
      fun k => -torusCoeff (fun x => g (fun j => (x j : ℂ)) i) k := by
    funext k
    simp only [torusCoeff, torusAverage, mul_neg, integral_neg]
  have hs : Diophantine.solve ω (fun k => -torusCoeff (fun x => g (fun j => (x j : ℂ)) i) k) =
      fun k => -Diophantine.solve ω (torusCoeff (fun x => g (fun j => (x j : ℂ)) i)) k := by
    funext k
    simp only [Diophantine.solve]
    split_ifs <;> ring
  simp only [cohR, Pi.neg_apply, cohSolution]
  rw [hc, hs]
  simp only [neg_mul, tsum_neg]

/-- `⟨f + g⟩ = ⟨f⟩ + ⟨g⟩` for functions continuous on the real torus. -/
theorem avg_add {f g : (Fin n → ℂ) → Fin n → ℂ}
    (hf : Continuous fun x : Fin n → ℝ => f (fun i => (x i : ℂ)))
    (hg : Continuous fun x : Fin n → ℝ => g (fun i => (x i : ℂ))) :
    avg (fun θ => f θ + g θ) = avg f + avg g :=
  integral_add (integrableOn_unitCube_of_continuous hf) (integrableOn_unitCube_of_continuous hg)

/-- `ξᴺ₀` is the triangular `ξᴺ₀` of v1. -/
theorem modXiN0_eq
    (hcL : Continuous fun x : Fin n → ℝ => etaL h K ω (fun i => (x i : ℂ)))
    (hcTU : Continuous fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ)) *ᵥ
      cohR ω (etaN h K ω) (fun i => (x i : ℂ)))
    (hTa : torsionAverage h K ω = avg (torsion h K ω)) :
    modXiN0 h K ω = triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω) := by
  rw [modXiN0, triXi0, hTa, avg_add hcL hcTU]
  rfl

/-- `ξᴺ` is the triangular `ξᴺ` of v1. -/
theorem modXiN_eq (h0 : modXiN0 h K ω = triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) :
    modXiN h K ω = triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) := by
  funext θ
  rw [modXiN, h0]
  rfl

/-- `ξᴸ` is the triangular `ξᴸ = 𝓡(T ξᴺ - ηᴸ)` of v1. -/
theorem modXiL_eq (h0 : modXiN0 h K ω = triXi0 ω (etaL h K ω) (etaN h K ω) (torsion h K ω)) :
    modXiL h K ω = triXiL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) := by
  have hN := modXiN_eq h0
  have e : (fun θ' => etaL h K ω θ' - torsion h K ω θ' *ᵥ modXiN h K ω θ') =
      fun θ' => -triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ' := by
    funext θ'
    rw [hN, triGL, neg_sub]
  funext θ
  rw [modXiL, e, cohR_neg]
  simp only [neg_neg]
  rfl

/-- On `T_w`, `K̄ = K̃ ∘ (id + ξᴸ)`. -/
theorem modNewton_of_mem {w : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n w) :
    modNewton h K ω w θ = modKtilde h K ω (θ + modXiL h K ω θ) := by
  simp [modNewton, hθ]

/-- Near a point of `T_w`, `K̄ = K̃ ∘ (id + ξᴸ)`. -/
theorem modNewton_eventuallyEq {w : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n w) :
    modNewton h K ω w =ᶠ[𝓝 θ] fun y => modKtilde h K ω (y + modXiL h K ω y) :=
  Filter.mem_of_superset ((isOpen_complexStrip n w).mem_nhds hθ) fun _ hy =>
    modNewton_of_mem hy

/-- `sumVec (K̃ - K) = N ξᴺ`. -/
theorem sumVec_modKtilde_sub (θ : Fin n → ℂ) :
    sumVec n (modKtilde h K ω θ - K θ) = normalMat K θ *ᵥ modXiN h K ω θ := by
  rw [modKtilde, add_sub_cancel_left, LinearEquiv.apply_symm_apply]

end ModStepB

end KAM.Sharp2

end
