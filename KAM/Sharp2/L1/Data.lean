/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.L1.Norms
public import KAM.Torus.Objects
public import KAM.Frozen.Defs.Torsion

/-!
# The ℓ¹ entry data (package B10b)

Blueprint `bp:p2s2l1:data` of `blueprint/parts/p2s2-l1hybrid.tex`: the numbers of (L1)–(L4) (`L1Data`), their
well-formedness (`L1Data.WF`), and the hypotheses on the explicit objects of `(h, K, ω)` that a certificate checks
(`L1Hyp`): the ℓ¹ bounds of `ηᴺ`, `ηᴸ` on `T_ρ` relative to the frozen sup bound `e` and the caps `s_Lt`, `s_Nt`; the
ℓ¹ row sums of the frozen torsion on `T_{ρ-δ₀}`; its sup on `ℝⁿ`; the three `Γ_∞` bounds at the actual frequency
and the actual bites `δ₀`, `δ₀/2`, `ρ`; and the optional ℓ¹ frame bounds.

The design audit AUDIT-B10D-1 (F1) found that the optional frame option of these signatures can be bypassed with
zero caps; its repair is recorded with the B10c signatures (`docs/campaign/design/APOST-SHARP-V2-L1.md`, dispositions).
These declarations are the B10D signatures, verbatim.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Sharp2.L1

open KAM KAM.Torus

/-- The numbers of (L1)–(L4): ℓ¹/sup ratios of `ηᴺ, ηᴸ`, the ℓ¹ and real torsion caps, the three `Γ_∞` bounds, and the
optional ℓ¹ frame caps (`0` = not used). -/
structure L1Data where
  aN : ℝ
  aL : ℝ
  t1 : ℝ
  tR : ℝ
  G0 : ℝ
  G0h : ℝ
  Gρ : ℝ
  nuK : ℝ := 0
  nuN : ℝ := 0

/-- Well-formedness of the numerical package (audit AUDIT-SHARP-V2-fixed-1, F1). -/
structure L1Data.WF (d : L1Data) : Prop where
  aN_pos : 0 < d.aN
  aL_pos : 0 < d.aL
  t1_pos : 0 < d.t1
  tR_nonneg : 0 ≤ d.tR
  tR_le : d.tR ≤ d.t1
  G0_pos : 0 < d.G0
  G0h_pos : 0 < d.G0h
  Gρ_pos : 0 < d.Gρ
  nuK_nonneg : 0 ≤ d.nuK
  nuN_nonneg : 0 ≤ d.nuN

/-- The hypotheses (L1)–(L4) on the explicit objects of `(h, K, ω)` (a certificate checks them); `e` is the frozen
sup bound of the invariance error, `sLt`, `sNt` the caps of (R2), `δ₀` the stage-0 bite. -/
structure L1Hyp {n : ℕ} (d : L1Data) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (ρ δ₀ e sLt sNt : ℝ) : Prop where
  l1EtaN : L1Vec ρ (etaN h K ω) (d.aN * sLt * e)
  l1EtaL : L1Vec ρ (etaL h K ω) (d.aL * sNt * e)
  l1Torsion : L1Mat (ρ - δ₀) (torsion h K ω) d.t1
  realTorsion : ∀ x : Fin n → ℝ, ‖torsion h K ω (fun i => (x i : ℂ))‖ ≤ d.tR
  gam0 : smallDivisorSup ω δ₀ ≤ d.G0
  gam0h : smallDivisorSup ω (δ₀ / 2) ≤ d.G0h
  gamρ : smallDivisorSup ω ρ ≤ d.Gρ
  frame : 0 < d.nuK → L1Mat ρ (tangentMat K) d.nuK ∧ L1Mat ρ (normalMat K) d.nuN

end KAM.Sharp2.L1

end
