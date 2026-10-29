/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Apost.Constants
public import KAM.Apost.Schedule

/-!
# Part 2 (isoenergetic iteration): standing data, constants and constructions

Definitions only (there is no theorem in this module).

* `IsoStanding` (`bpI:p2:standing`), the ray margin `rayMargin` (`ν(s)`), `IsoAdmissible`
  (`bpI:p2:admissible`) and `IterHyp` (hypotheses (I5)-(I12) of `bpI:p2:iteration`).
* The constants of `bpI:p2:constants`: `hatCS`, `hatCxiN`, `hatCg`, `hatCxi`, `hatCDK`,
  `hatCDelta`, `CP`, `hatCpartial`, `hatClin`, `hatCE1`, `hatCE2`, `hatCE`, `CY`, `CDTbord`,
  `hatcStep`, `hatcSum`, `hatcStar` and the step size `dStep`; the I-G1 constants `isoC1`, `isoC2`.
* The explicit correction of `bpI:p2:correction`: `isoBordData`, `isoXi`, `isoXiOmega`,
  `isoCorrection`, `isoNewS`; the Newton map and its quadratic remainders of
  `bpI:p2:newton-error`: `isoNewtonMap`, `isoQuadX`, `isoQuadH`.
* The schedule `isoEpsSeq`, `isoDSeq` and the iteration `isoSeq`. `δ_s`, `r_s` are
  `KAM.Apost.deltaSeq`, `KAM.Apost.rSeq`. The limits `isoLimit`, `isoSLimit` are in `Apost/Limit`.

Rule 6: the iteration and the correction are total definitions, so that `iteration` assumes exactly
the hypotheses `IterHyp`. The frequency is always the term `s • ωstar`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

variable {n : ℕ}

/-- `bpI:p2:standing`: `n ≥ 2, τ ≥ n-1, M, σ > 0` (`Params`), `σ_ω > 1`, `ν > 0`, `ω* ≠ 0`,
(I1)–(I4) verbatim (five bounds), `γ > 0`, `ω* ∈ Dio_{γ,τ}`. `E₀ ∈ ℝ` is typing data. -/
structure IsoStanding (n : ℕ) (τ M σK σB σT σω ν : ℝ) (ωstar : Fin n → ℝ)
    (D : Set ((Fin n → ℂ) × (Fin n → ℂ))) (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (γ : ℝ) : Prop
    extends KAM.Apost.Params n τ M σK σB σT where
  σω_gt : 1 < σω
  ν_pos : 0 < ν
  ωstar_ne : ωstar ≠ 0
  isOpen : IsOpen D
  transl_mem : ∀ z ∈ D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ D
  holo : DifferentiableOn ℂ H D
  periodic : ∀ z ∈ D, ∀ k : Fin n → ℤ, H (z.1 + (fun i => (k i : ℂ)), z.2) = H z
  real : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ D →
    (H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  bounds : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ H z‖ ≤ M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ H) z‖ ≤ M ∧ ‖iteratedFDeriv ℂ 2 H z‖ ≤ M
  gamma_pos : 0 < γ
  dio : IsDiophantine γ τ ωstar

/-- `ν(s) = min {s - 1, σ_ω - s} |ω*|`, the endpoint margin of `sω*` on the ray. -/
def rayMargin (σω : ℝ) (ωstar : Fin n → ℝ) (s : ℝ) : ℝ := min (s - 1) (σω - s) * ‖ωstar‖

/-- `bpI:p2:admissible` (B1)–(B7): K's (A1)–(A4), (A6) at `ω = sω*`, `s > 1`, the bordered twist
(B5) and the energy error (B7). -/
structure IsoAdmissible (σK σB σT : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ r β ε s : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop
    extends AdmissibleNoTwist σK σB D H (s • ωstar) r β ε K where
  s_gt : 1 < s
  twist : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det ∧
    ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ σT
  energy_le : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ ε

section Constants

variable (n : ℕ) (τ M σK σB σT : ℝ)

def hatCS : ℝ := max (C_xi0 n τ M σK σB σT)
  (mSize M σK σB σT * Theta n M σK σB σT + 2 * n * cR n τ * mSize M σK σB σT ^ 5)
def hatCxiN : ℝ := hatCS n τ M σK σB σT + 2 * n * cR n τ * mSize M σK σB σT
def hatCg : ℝ := C_T n M σK σB σT * hatCxiN n τ M σK σB σT +
  Theta n M σK σB σT * hatCS n τ M σK σB σT + 2 * n * mSize M σK σB σT ^ 2 * Theta n M σK σB σT
def hatCxi : ℝ := max (cR n τ * hatCg n τ M σK σB σT) (Theta n M σK σB σT * hatCxiN n τ M σK σB σT)
def hatCDK : ℝ := 2 * mSize M σK σB σT ^ 2 * hatCxi n τ M σK σB σT
def hatCDelta : ℝ := max (hatCDK n τ M σK σB σT) (Theta n M σK σB σT ^ 2 * hatCS n τ M σK σB σT)
/-- `C_P = 𝔪² + n + 𝔪³ + C_X` (bound `|∂_ω P| ≤ C_P/δ`). -/
def CP : ℝ := mSize M σK σB σT ^ 2 + n + mSize M σK σB σT ^ 3 + C_X n M σK σB σT
def hatCpartial : ℝ := CP n M σK σB σT * hatCxi n τ M σK σB σT +
  2 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT * hatCg n τ M σK σB σT
def hatClin : ℝ := C_red n M σK σB σT * hatCxi n τ M σK σB σT +
  C_sym n τ M σK σB σT * hatCg n τ M σK σB σT +
  Theta n M σK σB σT * C_Omega n τ M σK σB σT * hatCS n τ M σK σB σT
def hatCE1 : ℝ := 4 * mSize M σK σB σT ^ 2 * Theta n M σK σB σT ^ 2 * hatClin n τ M σK σB σT +
  mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2 +
  Theta n M σK σB σT * hatCS n τ M σK σB σT * hatCpartial n τ M σK σB σT
def hatCE2 : ℝ := n * Theta n M σK σB σT ^ 2 *
  (2 * n * mSize M σK σB σT + C_Omega n τ M σK σB σT) * cR n τ * hatCg n τ M σK σB σT +
  mSize M σK σB σT * hatCDK n τ M σK σB σT ^ 2
def hatCE : ℝ := max (hatCE1 n τ M σK σB σT) (hatCE2 n τ M σK σB σT)
def CY : ℝ := n * mSize M σK σB σT * (2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT)
/-- `C_{Δ𝖳} = C_ΔT + 8n²𝔪⁴ + 1 + C_Y`. -/
def CDTbord : ℝ := C_DT n M σK σB σT + 8 * n ^ 2 * mSize M σK σB σT ^ 4 + 1 + CY n M σK σB σT
def hatcStep : ℝ := 2 * Theta n M σK σB σT ^ 3 * max (C_sym n τ M σK σB σT)
  (mSize M σK σB σT * CDTbord n M σK σB σT * hatCDelta n τ M σK σB σT)
def hatcSum : ℝ := 4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT *
  max (n : ℝ) (max (C_B n M σK σB σT) (mSize M σK σB σT ^ 2 * CDTbord n M σK σB σT))
def hatcStar (μ ν : ℝ) : ℝ := max ((2 : ℝ) ^ (2 * aExp n τ) * hatCE n τ M σK σB σT)
  (max (hatcStep n τ M σK σB σT * max 1 (2 / μ))
    (max (2 * hatcSum n τ M σK σB σT / μ)
      (4 * Theta n M σK σB σT ^ 2 * hatCDelta n τ M σK σB σT / ν)))
/-- `d = Ĉ_Δ ε / (γ² δ^a)`, the step size of `bpI:p2:correction`. -/
def dStep (γ ε δ : ℝ) : ℝ := hatCDelta n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)

end Constants

/-- The data of the correction: `ηᴸ, ηᴺ` of `K`, `T`, `Y = DH(K)N`, `η^ω = -(Ē_H(K) - E₀)`. -/
def isoBordData (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : BordData n :=
  ⟨etaL H K ω, etaN H K ω, torsion H K ω, energyRow H K,
    -(KAM.Iso.energyAverage H K - (E₀ : ℂ))⟩

/-- `ξ = (ξᴸ, ξᴺ)` with `ξᴸ₀ = 0`. -/
def isoXi (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) : Fin n ⊕ Fin n → ℂ :=
  Sum.elim (bordXiL ω (isoBordData H K ω E₀) 0 θ) (bordXiN ω (isoBordData H K ω E₀) θ)

def isoXiOmega (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) : ℂ :=
  bordXiOmega ω (isoBordData H K ω E₀)

/-- `ΔK = Pξ`. -/
def isoCorrection (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) :
    (Fin n → ℂ) × (Fin n → ℂ) :=
  (sumVec n).symm (frameMat K θ *ᵥ isoXi H K ω E₀ θ)

/-- `s̄ = s (1 - ξ^ω)` (`ξ^ω` is real, `correction`), so `ω̄ = s̄ω* = ω + Δω`, `Δω = -ωξ^ω`. -/
def isoNewS (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ωstar : Fin n → ℝ) (E₀ s : ℝ) : ℝ :=
  s * (1 - (isoXiOmega H K (s • ωstar) E₀).re)

open Classical in
/-- `K̄ = K + ΔK` on `T_w`, `K` elsewhere (`w = r - 2δ`). -/
def isoNewtonMap (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ωstar : Fin n → ℝ) (E₀ s w : ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  fun θ => if θ ∈ complexStrip n w then K θ + isoCorrection H K (s • ωstar) E₀ θ else K θ

/-- `Δ²X = X_H(K + ΔK) - X_H(K) - AΔK`. -/
def isoQuadX (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  hamiltonianVectorFieldℂ H (K θ + isoCorrection H K ω E₀ θ) - hamiltonianVectorFieldℂ H (K θ) -
    fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ) (isoCorrection H K ω E₀ θ)

/-- `Δ²H = H(K + ΔK) - H(K) - DH(K)ΔK`. -/
def isoQuadH (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) : ℂ :=
  H (K θ + isoCorrection H K ω E₀ θ) - H (K θ) - fderiv ℂ H (K θ) (isoCorrection H K ω E₀ θ)

variable (n τ M σK σB σT) in
/-- `ε₀ = e`, `ε_{s+1} = Ĉ_E ε_s² / (γ⁴ δ_s^{2a})`. -/
def isoEpsSeq (ρ ρinf γ e : ℝ) : ℕ → ℝ
  | 0 => e
  | s + 1 => hatCE n τ M σK σB σT * isoEpsSeq ρ ρinf γ e s ^ 2 /
      (γ ^ 4 * deltaSeq ρ ρinf s ^ (2 * aExp n τ))

variable (n τ M σK σB σT) in
/-- `d_s = Ĉ_Δ ε_s / (γ² δ_s^a)`. -/
def isoDSeq (ρ ρinf γ e : ℝ) (s : ℕ) : ℝ :=
  dStep n τ M σK σB σT γ (isoEpsSeq n τ M σK σB σT ρ ρinf γ e s) (deltaSeq ρ ρinf s)

/-- `(K_{j+1}, s_{j+1}) = (K̄_j, s̄_j)` with `w_j = r_j - 2δ_j`. -/
def isoSeq (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ωstar : Fin n → ℝ) (E₀ s₀ ρ ρinf : ℝ) :
    ℕ → ((Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) × ℝ
  | 0 => (K, s₀)
  | j + 1 => (isoNewtonMap H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 ωstar E₀
      (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2 (rSeq ρ ρinf j - 2 * deltaSeq ρ ρinf j),
    isoNewS H (isoSeq H K ωstar E₀ s₀ ρ ρinf j).1 ωstar E₀ (isoSeq H K ωstar E₀ s₀ ρ ρinf j).2)

/-- (I5)–(I12) of I-G1 on `T_ρ` with margin `μ`, and `ν(s₀) ≥ ν` (hypotheses of `iteration`). -/
structure IterHyp (σK σB σT σω ν : ℝ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ωstar : Fin n → ℝ) (E₀ ρ μ e s₀ : ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  holo : DifferentiableOn ℂ K (complexStrip n ρ)
  primary : IsPrimaryOnStrip K ρ
  real : IsRealOnReals K
  ball_sub : ∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ D
  deriv_le : ∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ
  gram : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB - μ
  twist : IsUnit (KAM.Iso.extendedTorsionAverage H K (s₀ • ωstar)).det ∧
    ‖(KAM.Iso.extendedTorsionAverage H K (s₀ • ωstar))⁻¹‖ ≤ σT - μ
  s_gt : 1 < s₀
  margin : ν ≤ rayMargin σω ωstar s₀
  error_le : ∀ θ ∈ complexStrip n ρ, ‖invarianceError H K (s₀ • ωstar) θ‖ ≤ e
  energy_le : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ e

-- `isoLimit` (`K_∞ = lim K_j` on `T_{ρ∞}`) and `isoSLimit` (`s_∞ = lim s_j`) are not defined here:
-- they are `limUnder` selectors, admitted only together with the theorems that prove convergence
-- and characterize them. They are defined in `Apost/Limit` with `limit` and
-- `energy_limit`, as `kamLimit` is defined with `limit` in `KAM/Apost/Limit.lean`.

/-- `C₁ = ρ^{4τ} max {γ̄⁴, ĉ_* δ₀^{-2a}}`. -/
def isoC1 (n : ℕ) (τ ρ ρinf M σK σB σT μ ν γbar : ℝ) : ℝ :=
  ρ ^ (4 * τ) * max (γbar ^ 4)
    (hatcStar n τ M σK σB σT μ ν * delta0 ρ ρinf ^ (-(2 * aExp n τ)))

/-- `C₂ = C₃ = 2 Ĉ_Δ ρ^{2τ} δ₀^{-a}`. -/
def isoC2 (n : ℕ) (τ ρ ρinf M σK σB σT : ℝ) : ℝ :=
  2 * hatCDelta n τ M σK σB σT * ρ ^ (2 * τ) * delta0 ρ ρinf ^ (-aExp n τ)

end KAM.Iso.Apost

end
