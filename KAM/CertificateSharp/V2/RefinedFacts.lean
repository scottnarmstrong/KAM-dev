/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Engine
public import KAM.Iso.Sharp2.RouteA.G1

/-!
# The refined bounds of stage 2

`RefClaim` holds the rational bounds a refined certificate claims, and `RefinedFacts c R ω` their
meaning on the objects of `c`. The two parts are checked separately:

* `HamFacts`, on `H` and the domain `D` (`V2/HamClaim.lean` by the disc pass,
  `V2/HamTrig.lean` by the cosh pass);
* `FrameFacts`, on `K` and the strip `T_ρ` (`V2/RouteARefinedEngine.lean`, by the majorants of C4).

These are statements on explicit objects, in the row and column sums the checks compute;
`RefinedFacts.refHyp` turns them into `KAM.Iso.Sharp2.RouteA.RefHypIA`.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate KAM.Sharp2.RouteA KAM.Iso.Sharp2.RouteA

/-- The claimed rational bounds: `‖DH‖ ≤ dh`, `‖DX_H‖ ≤ dx`, `‖D²X_H‖ ≤ d2x`, `‖D²H‖ ≤ d2h` on `D`;
`|Lᵀ| ≤ bL`, `|N| ≤ bN`, `|Nᵀ| ≤ bNt`, `|T| ≤ bT` on `T_ρ`. -/
structure RefClaim where
  dh : ℚ
  dx : ℚ
  d2x : ℚ
  d2h : ℚ
  bL : ℚ
  bN : ℚ
  bNt : ℚ
  bT : ℚ

variable {n : ℕ} {α : Type} [CertArith α]

/-- The bounds on `H`. -/
structure HamFacts (c : TorusCertificate n α) (R : RefClaim) : Prop where
  dh : ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ R.dh
  dx : ∀ z ∈ c.D, ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ R.dx
  d2x : ∀ z ∈ c.D, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ R.d2x
  d2h : ∀ z ∈ c.D, ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ R.d2h

/-- The bounds on the frame of `K` and the torsion, at `ωstar`. -/
structure FrameFacts (c : TorusCertificate n α) (R : RefClaim) (ωstar : Fin n → ℝ) : Prop where
  bL : ∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
    ∑ r : Fin n ⊕ Fin n, ‖tangentMat c.K θ r j‖ ≤ R.bL
  bN : ∀ θ ∈ complexStrip n c.params.rho, ∀ r : Fin n ⊕ Fin n,
    ∑ j : Fin n, ‖normalMat c.K θ r j‖ ≤ R.bN
  bNt : ∀ θ ∈ complexStrip n c.params.rho, ∀ j : Fin n,
    ∑ r : Fin n ⊕ Fin n, ‖normalMat c.K θ r j‖ ≤ R.bNt
  bT : ∀ θ ∈ complexStrip n c.params.rho, ∀ i : Fin n, ∑ j : Fin n,
    ‖KAM.Iso.extendedTorsion c.H c.K ((c.params.s : ℝ) • ωstar) θ (Sum.inl i) (Sum.inl j)‖ ≤ R.bT

/-- The initial values of the refined run. -/
noncomputable def RefClaim.init (R : RefClaim) : InitA := ⟨R.bL, R.bN, R.bNt, R.bT⟩

/-- `RefHypIA` from the two parts, for numbers `N` with the claimed bounds. -/
theorem refHyp_of {N : NumA} {c : TorusCertificate N.n α} {R : RefClaim} {ωstar : Fin N.n → ℝ}
    (hn : 1 ≤ N.n) (hρ : N.ρ = c.params.rho) (hδ : 0 ≤ N.δ 0) (hρ0 : (0 : ℝ) < c.params.rho)
    (hM1 : N.M1 = R.dx) (hM2 : N.M2 = R.d2x) (hMh2 : N.Mh2 = R.d2h)
    (hH : HamFacts c R) (hF : FrameFacts c R ωstar) :
    RefHypIA N R.init R.dh c.D c.H c.K ((c.params.s : ℝ) • ωstar) := by
  have h00 : (0 : Fin N.n → ℂ) ∈ complexStrip N.n c.params.rho := fun i => by simpa using hρ0
  have j0 : Fin N.n := ⟨0, hn⟩
  have hbL : (0 : ℝ) ≤ R.bL :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bL 0 h00 j0)
  have hbN : (0 : ℝ) ≤ R.bN :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bN 0 h00 (Sum.inl j0))
  have hbNt : (0 : ℝ) ≤ R.bNt :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bNt 0 h00 j0)
  have hbT : (0 : ℝ) ≤ R.bT :=
    (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hF.bT 0 h00 j0)
  have hs : ∀ θ ∈ complexStrip N.n N.ρ, θ ∈ complexStrip N.n c.params.rho := fun θ hθ => hρ ▸ hθ
  refine
    { dX := fun z hz => hM1 ▸ hH.dx z hz
      d2X := fun z hz => hM2 ▸ hH.d2x z hz
      dH := hH.dh
      d2H := fun z hz => hMh2 ▸ hH.d2h z hz
      tangentT := fun θ hθ => (norm_le_iff_forall_rowSum hbL).2 fun j => hF.bL θ (hs θ hθ) j
      normal := fun θ hθ => (norm_le_iff_forall_rowSum hbN).2 fun r => hF.bN θ (hs θ hθ) r
      normalT := fun θ hθ => (norm_le_iff_forall_rowSum hbNt).2 fun j => hF.bNt θ (hs θ hθ) j
      tors := fun θ hθ => (norm_le_iff_forall_rowSum hbT).2 fun i => ?_ }
  have hθ' : θ ∈ complexStrip N.n c.params.rho :=
    hs θ (fun i => (hθ i).trans_le (by linarith))
  exact hF.bT θ hθ' i

end KAM.CertificateSharp.V2

end
