/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB
public import KAM.Iso.Sharp2.RouteA.Correction

/-!
# The objects of the bordered modified step (`bpI:p2s2:step`)

The bordered system is the one of v1 (`KAM.Iso.Linear.bordSol`, at `KAM.Iso.Apost.isoBordData`):

* `ξᴺ = ξᴺ₀ - 𝓡ηᴺ` (`xiNI`), `K̃ = K + N ξᴺ` (`tilK`);
* `gᴸ = T ξᴺ + ω ξ^ω - ηᴸ` (`gLI`), `ξᴸ = 𝓡 gᴸ` (`xiLI`), `K̄ = K̃ ∘ (id + ξᴸ)` on `T_w` (`newK`);
* `ω̄ = (1 - ξ^ω) ω` (`newOmega`), with `ξ^ω` real (`xw`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2.ModStepB

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost

variable {n : ℕ}

/-- `ξᴺ = ξᴺ₀ - 𝓡ηᴺ`. -/
def xiNI (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : (Fin n → ℂ) → Fin n → ℂ :=
  bordXiN ω (isoBordData h K ω E₀)

/-- `K̃ = K + N ξᴺ`. -/
def tilK (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  K θ + (sumVec n).symm (normalMat K θ *ᵥ xiNI h K ω E₀ θ)

/-- `gᴸ = T ξᴺ + ω ξ^ω - ηᴸ`. -/
def gLI (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : (Fin n → ℂ) → Fin n → ℂ :=
  bordGL ω (isoBordData h K ω E₀)

/-- `ξᴸ = 𝓡 gᴸ`. -/
def xiLI (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : (Fin n → ℂ) → Fin n → ℂ :=
  bordXiL ω (isoBordData h K ω E₀) 0

open Classical in
/-- `K̄ = K̃ ∘ (id + ξᴸ)` on `T_w`, `K` elsewhere (`w = r - 2δ`). -/
def newK (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ w : ℝ) : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => if θ ∈ complexStrip n w then tilK h K ω E₀ (θ + xiLI h K ω E₀ θ) else K θ

/-- The real part of `ξ^ω`. -/
def xw (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : ℝ :=
  (isoXiOmega h K ω E₀).re

/-- `ω̄ = (1 - ξ^ω) ω`. -/
def newOmega (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : Fin n → ℝ :=
  (1 - xw h K ω E₀) • ω

variable {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  {ω : Fin n → ℝ} {E₀ : ℝ}

/-- `ω̄` is on the ray, at the scalar of the additive step. -/
theorem newOmega_smul (ωstar : Fin n → ℝ) (s : ℝ) :
    newOmega h K (s • ωstar) E₀ = isoNewS h K ωstar E₀ s • ωstar := by
  rw [newOmega, xw, isoNewS, smul_smul, mul_comm]

/-- On `T_w`, `K̄ = K̃ ∘ (id + ξᴸ)`. -/
theorem newK_of_mem {w : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n w) :
    newK h K ω E₀ w θ = tilK h K ω E₀ (θ + xiLI h K ω E₀ θ) := by
  simp [newK, hθ]

/-- Near a point of `T_w`, `K̄ = K̃ ∘ (id + ξᴸ)`. -/
theorem newK_eventuallyEq {w : ℝ} {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n w) :
    newK h K ω E₀ w =ᶠ[𝓝 θ] fun y => tilK h K ω E₀ (y + xiLI h K ω E₀ y) :=
  Filter.mem_of_superset ((isOpen_complexStrip n w).mem_nhds hθ) fun _ hy => newK_of_mem hy

/-- `sumVec (K̃ - K) = N ξᴺ`. -/
theorem sumVec_tilK_sub (θ : Fin n → ℂ) :
    sumVec n (tilK h K ω E₀ θ - K θ) = normalMat K θ *ᵥ xiNI h K ω E₀ θ := by
  rw [tilK, add_sub_cancel_left, LinearEquiv.apply_symm_apply]

end KAM.Iso.Sharp2.ModStepB

end
