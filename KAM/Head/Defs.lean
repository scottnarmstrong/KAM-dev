/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Head.Standing
public import KAM.Head.HBounded
public import KAM.Head.PhaseAverage
public import KAM.Strip.RealRestriction
public import KAM.Frozen.Defs.GramMatrix
public import KAM.Frozen.Defs.HamiltonianVectorFieldC
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Defs.TorsionAverage

/-!
# The definitions of Part 4

Definitions only. Theorems about them live in the later `KAM/Head/*` modules; the adapters to
`KAM.Head.derivative_bounds` and its companions are in `KAM/Head/Adapters.lean`.

* `Hconst`, `Fconst`, `Mconst` are the constants `H_j`, `F_j`, `M` of `bp:p4:derivative-bounds`, in
  the division-by-power form. They equal `derivConstH`, `derivConstF` and
  `derivConstM` (`KAM.Head.Hconst_eq_derivConstH`, ...).
* `realDomain`, `gradC`, `hessian`, `actionHessian`, `LambdaG`, `Winf` and `invFreq` are the objects
  of `bp:p4:freq-map`, `bp:p4:inverse-freq` and `bp:p4:unperturbed`.
* `GConsts`, `GConsts.Pos`, `G1Body`, `G2Body` and `GValid` carry the constants of the frozen G1,
  G2 and G3 as plain data plus their defining property. `G1Body` and
  `G2Body` are the bodies of the frozen `KAM.aposteriori_kam` and `KAM.local_uniqueness_flow` after
  their leading `∃` over the constants.
* `sigmaK`, `sigmaB`, `sigmaT`, `A0`-`A4`, `lamStar`, `cT`, `etaStar`, `cStar`, `SA`, `eta0` and
  `OmegaGamma` are Definition `bp:p4:parameters` and the display `bp:p4:SA`.
* `IsApplyTorus`, `applyTorus`, `normTorus`, `normDisp` and `shiftedTorus` are the tori of
  `bp:p4:apply`, `bp:p4:normalized-torus` and `bp:p4:lip-error`.
* `layerSet`, `goodActions`, `disp` and `Cmeas` are the objects of `bp:p4:good-actions` and
  `bp:p4:main-measure`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace KAM.Head

/-! ### The constants of `bp:p4:derivative-bounds` -/

/-- `H_j = c̄ M_h δ_*^{-j}` of `bp:p4:derivative-bounds`. -/
def Hconst {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (j : ℕ) : ℝ :=
  cbar n * hBound h B r₀ / deltaStar s₀ r₀ ^ j

/-- `F_j = c̄ δ_*^{-j}` of `bp:p4:derivative-bounds`. -/
def Fconst (n : ℕ) (s₀ r₀ : ℝ) (j : ℕ) : ℝ := cbar n / deltaStar s₀ r₀ ^ j

/-- `M = c̄ (M_h + 1) δ_*^{-3}` of `bp:p4:derivative-bounds`. -/
def Mconst {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) : ℝ :=
  cbar n * (hBound h B r₀ + 1) / deltaStar s₀ r₀ ^ 3

/-! ### The remaining definitions -/

/-- `U = {I ∈ ℝⁿ : ι I ∈ B_{r₀}}`. -/
def realDomain {n : ℕ} (B : Set (Fin n → ℝ)) (r₀ : ℝ) : Set (Fin n → ℝ) :=
  {I | (fun i => (I i : ℂ)) ∈ actionNbhd B r₀}

/-- The complex gradient `∇h(z) = (∂_i h(z))_i`. -/
def gradC {n : ℕ} (h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => fderiv ℂ h z (Pi.single i 1)

/-- The complex Hessian `∇²h(z) = (∂_j ∂_i h(z))_{ij}`. -/
def hessian {n : ℕ} (h : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun w => fderiv ℂ h w (Pi.single i 1)) z (Pi.single j 1)

/-- `Λ_g = max (H₂, 2 H₁ / δ_*)`. -/
def LambdaG {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) : ℝ :=
  max (Hconst s₀ r₀ B h 2) (2 * Hconst s₀ r₀ B h 1 / deltaStar s₀ r₀)

/-- `W_∞ = H₁`. -/
def Winf {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) : ℝ :=
  Hconst s₀ r₀ B h 1

/-- `I_ω`: the action in `B` with frequency `ω` (`bp:p4:inverse-freq`); junk off `∇h(B)`. -/
def invFreq {n : ℕ} (h : (Fin n → ℂ) → ℂ) (B : Set (Fin n → ℝ)) (ω : Fin n → ℝ) : Fin n → ℝ :=
  Function.invFunOn (frequencyMap h) B ω

/-- The action Hessian `∂²_I φ(z) = (∂_{I_j} ∂_{I_i} φ(z))_{ij}` of `φ` on `ℂⁿ × ℂⁿ`. -/
def actionHessian {n : ℕ} (φ : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun w => fderiv ℂ φ w (0, Pi.single i 1)) z (0, Pi.single j 1)

/-- The constants supplied by the frozen G1 (two tuples), G2 and G3 (Definition
`bp:p4:parameters`; `C3` is the constant of `bp:p4:preimage-measure`). Plain data; their defining
properties are `GConsts.Pos` and `GValid`. -/
structure GConsts where
  /-- `C₁⁽¹⁾` -/
  C11 : ℝ
  /-- `C₂⁽¹⁾` -/
  C21 : ℝ
  /-- `C₁⁽²⁾` -/
  C12 : ℝ
  /-- `C₂⁽²⁾` -/
  C22 : ℝ
  /-- `c_G` -/
  cG : ℝ
  /-- `C₃` (any sign) -/
  C3 : ℝ

/-- The positivity the frozen G1 and G2 give their constants. -/
structure GConsts.Pos (gc : GConsts) : Prop where
  C11_pos : 0 < gc.C11
  C21_pos : 0 < gc.C21
  C12_pos : 0 < gc.C12
  C22_pos : 0 < gc.C22
  cG_pos : 0 < gc.cG

/-- `σ_K = 2 + μ`. -/
def sigmaK (s₀ r₀ : ℝ) : ℝ := 2 + muParam s₀ r₀

/-- `σ_B = 2 + μ`. -/
def sigmaB (s₀ r₀ : ℝ) : ℝ := 2 + muParam s₀ r₀

/-- `σ_T = 4 L₊ + μ`. -/
def sigmaT (Lh s₀ r₀ : ℝ) : ℝ := 4 * Lplus Lh + muParam s₀ r₀

/-- The body of the frozen G1 (`KAM.aposteriori_kam`) after `∃ C₁ C₂, 0 < C₁ ∧ 0 < C₂ ∧`,
verbatim (checked by `exact` against the frozen statement). -/
def G1Body (n : ℕ) (τ ρ ρinf M σK σB σT μ γbar C₁ C₂ : ℝ) : Prop :=
  ∀ (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ e : ℝ),
    -- H1: the Hamiltonian
    IsOpen 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) →
    DifferentiableOn ℂ h 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) →
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M) →
    -- H2: the parameterization
    DifferentiableOn ℂ K (complexStrip n ρ) → IsPrimaryOnStrip K ρ → IsRealOnReals K →
    (∀ θ ∈ complexStrip n ρ, Metric.ball (K θ) μ ⊆ 𝔅) →
    (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K θ‖ ≤ σK - μ) →
    -- H3: the tangent frame has maximal rank, with `|B(θ)| ≤ σB - μ`
    (∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K θ)⁻¹ i j‖ ≤ σB - μ) →
    -- H4: twist condition
    IsUnit (torsionAverage h K ω).det →
    (∀ i, ∑ j, ‖(torsionAverage h K ω)⁻¹ i j‖ ≤ σT - μ) →
    -- H5: Diophantine frequency, with `γ ≤ γbar`
    0 < γ → γ ≤ γbar → IsDiophantine γ τ ω →
    -- smallness of the invariance error
    (∀ θ ∈ complexStrip n ρ, ‖invarianceError h K ω θ‖ ≤ e) →
    C₁ * e / (γ ^ 4 * ρ ^ (4 * τ)) < 1 →
    ∃ Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip n ρinf) ∧ IsPrimaryOnStrip Kinf ρinf ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip n ρinf, invarianceError h Kinf ω θ = 0) ∧
      (∀ θ ∈ complexStrip n ρinf, Metric.ball (Kinf θ) (μ / 2) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip n ρinf, ‖fderiv ℂ Kinf θ‖ ≤ σK - μ / 2) ∧
      ∀ θ ∈ complexStrip n ρinf, ‖Kinf θ - K θ‖ ≤ C₂ * e / (γ ^ 2 * ρ ^ (2 * τ))

/-- The body of the frozen G2 (`KAM.local_uniqueness_flow`) after `∃ c, 0 < c ∧`, verbatim
(checked by `exact` against the frozen statement). -/
def G2Body (n : ℕ) (τ ρ M σK σB σT μ c : ℝ) : Prop :=
  ∀ (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))) (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K₁ K₂ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) (γ : ℝ),
    -- H1: the Hamiltonian
    IsOpen 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ 𝔅) →
    DifferentiableOn ℂ h 𝔅 →
    (∀ z ∈ 𝔅, ∀ k : Fin n → ℤ, h (z.1 + (fun i => (k i : ℂ)), z.2) = h z) →
    (∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ 𝔅 →
      (h ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0) →
    (∀ z ∈ 𝔅, ‖fderiv ℂ h z‖ ≤ M ∧ ‖hamiltonianVectorFieldℂ h z‖ ≤ M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M) →
    -- the reference torus `K₁`: H2–H4 and invariance
    DifferentiableOn ℂ K₁ (complexStrip n ρ) → IsPrimaryOnStrip K₁ ρ → IsRealOnReals K₁ →
    (∀ θ ∈ complexStrip n ρ, Metric.ball (K₁ θ) μ ⊆ 𝔅) →
    (∀ θ ∈ complexStrip n ρ, ‖fderiv ℂ K₁ θ‖ ≤ σK - μ) →
    (∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K₁ θ).det ∧
      ∀ i, ∑ j, ‖(gramMatrix K₁ θ)⁻¹ i j‖ ≤ σB - μ) →
    IsUnit (torsionAverage h K₁ ω).det →
    (∀ i, ∑ j, ‖(torsionAverage h K₁ ω)⁻¹ i j‖ ≤ σT - μ) →
    0 < γ → IsDiophantine γ τ ω →
    (∀ θ ∈ complexStrip n ρ, invarianceError h K₁ ω θ = 0) →
    -- the second torus `K₂`
    DifferentiableOn ℂ K₂ (complexStrip n ρ) → IsPrimaryOnStrip K₂ ρ → IsRealOnReals K₂ →
    (∀ θ ∈ complexStrip n ρ, K₂ θ ∈ 𝔅) →
    (∀ θ ∈ complexStrip n ρ, invarianceError h K₂ ω θ = 0) →
    -- closeness
    (∀ θ ∈ complexStrip n ρ, ‖K₁ θ - K₂ θ‖ ≤ c * γ ^ 2 * ρ ^ (2 * τ)) →
    ∃ φ : Fin n → ℝ, ∀ θ ∈ complexStrip n (ρ / 2), K₂ θ = K₁ (θ + (fun i => (φ i : ℂ)))

/-- Definition `bp:p4:parameters`: `gc` are constants of the frozen G1 at the two tuples
`(ρ, ρ_∞) = (s/4, s/8)` and `(3s/32, s/16)`, of the frozen G2 at `ρ = s/16`, all with
`(n, τ, M, σ_K, σ_B, σ_T, μ, γ̄ = 1)`, and of the frozen G3 for `Ω = ∇h(B)`. -/
structure GValid {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ)
    (gc : GConsts) : Prop extends GConsts.Pos gc where
  g1a : G1Body n τ (stripWidth s₀ / 4) (stripWidth s₀ / 8) (Mconst s₀ r₀ B h) (sigmaK s₀ r₀)
    (sigmaB s₀ r₀) (sigmaT Lh s₀ r₀) (muParam s₀ r₀) 1 gc.C11 gc.C21
  g1b : G1Body n τ (3 * stripWidth s₀ / 32) (stripWidth s₀ / 16) (Mconst s₀ r₀ B h)
    (sigmaK s₀ r₀) (sigmaB s₀ r₀) (sigmaT Lh s₀ r₀) (muParam s₀ r₀) 1 gc.C12 gc.C22
  g2 : G2Body n τ (stripWidth s₀ / 16) (Mconst s₀ r₀ B h) (sigmaK s₀ r₀) (sigmaB s₀ r₀)
    (sigmaT Lh s₀ r₀) (muParam s₀ r₀) gc.cG
  g3 : ∀ α : ℝ, 0 < α →
    volume {ω ∈ frequencyMap h '' B | ¬ IsDiophantine α τ ω} ≤ ENNReal.ofReal (gc.C3 * α)

/-- `A₀ = 2 C₂⁽¹⁾ F₁ / (s/4)^{2τ}`. -/
def A0 (n : ℕ) (τ s₀ r₀ : ℝ) (gc : GConsts) : ℝ :=
  2 * gc.C21 * Fconst n s₀ r₀ 1 / (stripWidth s₀ / 4) ^ (2 * τ)

/-- `λ_* = δ_* / (4 L₊)`. -/
def lamStar (Lh s₀ r₀ : ℝ) : ℝ := deltaStar s₀ r₀ / (4 * Lplus Lh)

/-- `A₁ = L₊ (H₃ A₀ + F₂) + 32 n A₀ / s`. -/
def A1 {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ)
    (gc : GConsts) : ℝ :=
  Lplus Lh * (Hconst s₀ r₀ B h 3 * A0 n τ s₀ r₀ gc + Fconst n s₀ r₀ 2) +
    32 * n * A0 n τ s₀ r₀ gc / stripWidth s₀

/-- `A₂ = (σ_K + 1) C₂⁽²⁾ A₁ / (3s/32)^{2τ}`. -/
def A2 {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ)
    (gc : GConsts) : ℝ :=
  (sigmaK s₀ r₀ + 1) * gc.C22 * A1 τ s₀ r₀ B h Lh gc / (3 * stripWidth s₀ / 32) ^ (2 * τ)

/-- `A₃ = max (A₂, 2 A₀ / λ_*)`. -/
def A3 {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ)
    (gc : GConsts) : ℝ :=
  max (A2 τ s₀ r₀ B h Lh gc) (2 * A0 n τ s₀ r₀ gc / lamStar Lh s₀ r₀)

/-- `A₄ = 16 n A₀ / s`. -/
def A4 (n : ℕ) (τ s₀ r₀ : ℝ) (gc : GConsts) : ℝ := 16 * n * A0 n τ s₀ r₀ gc / stripWidth s₀

/-- `c_T = 304 n³ (M + W_∞ + 1)`. -/
def cT {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) : ℝ :=
  304 * (n : ℝ) ^ 3 * (Mconst s₀ r₀ B h + Winf s₀ r₀ B h + 1)

/-- `η_*(δ) = min (μ, δ² / (16 c_T L₊))`. -/
def etaStar {n : ℕ} (s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh δ : ℝ) : ℝ :=
  min (muParam s₀ r₀) (δ ^ 2 / (16 * cT s₀ r₀ B h * Lplus Lh))

/-- `c_*`, the minimum of the eight numbers of Definition `bp:p4:parameters`. -/
def cStar {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ)
    (gc : GConsts) : ℝ :=
  min 1 <| min (deltaStar s₀ r₀ ^ 2 / (2 * Lplus Lh * cbar n)) <|
    min ((stripWidth s₀ / 4) ^ (4 * τ) / (2 * gc.C11 * Fconst n s₀ r₀ 1)) <|
    min (etaStar s₀ r₀ B h Lh (stripWidth s₀ / 32) / A0 n τ s₀ r₀ gc) <|
    min ((3 * stripWidth s₀ / 32) ^ (4 * τ) /
      (2 * gc.C12 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀)) <|
    min (gc.cG * (stripWidth s₀ / 16) ^ (2 * τ) /
      (2 * A0 n τ s₀ r₀ gc +
        gc.C22 * A1 τ s₀ r₀ B h Lh gc * lamStar Lh s₀ r₀ / (3 * stripWidth s₀ / 32) ^ (2 * τ))) <|
    min (1 / (4 * (A3 τ s₀ r₀ B h Lh gc * LambdaG s₀ r₀ B h + A4 n τ s₀ r₀ gc)))
      (1 / (2 * A0 n τ s₀ r₀ gc))

/-- Display `bp:p4:SA`: the standing assumption `0 < γ ≤ 1`, `0 ≤ ε ≤ c_* γ⁴`. -/
structure SA {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ) (Lh : ℝ)
    (gc : GConsts) (ε γ : ℝ) : Prop where
  gamma_pos : 0 < γ
  gamma_le : γ ≤ 1
  eps_nonneg : 0 ≤ ε
  eps_le : ε ≤ cStar τ s₀ r₀ B h Lh gc * γ ^ 4

/-- Display `bp:p4:SA`: `η₀ = A₀ ε γ⁻²`. -/
def eta0 (n : ℕ) (τ s₀ r₀ : ℝ) (gc : GConsts) (ε γ : ℝ) : ℝ := A0 n τ s₀ r₀ gc * ε / γ ^ 2

/-- Display `bp:p4:SA`: `Ω_γ = ∇h(B) ∩ Dio_{γ,τ}`. -/
def OmegaGamma {n : ℕ} (h : (Fin n → ℂ) → ℂ) (B : Set (Fin n → ℝ)) (τ γ : ℝ) :
    Set (Fin n → ℝ) :=
  frequencyMap h '' B ∩ {ω | IsDiophantine γ τ ω}

/-- The conclusion clauses of `bp:p4:apply` for a candidate `K`. -/
def IsApplyTorus {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (gc : GConsts) (ε γ : ℝ) (ω : Fin n → ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop :=
  DifferentiableOn ℂ K (complexStrip n (stripWidth s₀ / 8)) ∧
  IsPrimaryOnStrip K (stripWidth s₀ / 8) ∧ IsRealOnReals K ∧
  (∀ θ ∈ complexStrip n (stripWidth s₀ / 8), invarianceError (hbold h f) K ω θ = 0) ∧
  (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
    Metric.ball (K θ) (muParam s₀ r₀ / 2) ⊆ domainD n s₀ r₀ B) ∧
  (∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
    ‖fderiv ℂ K θ‖ ≤ sigmaK s₀ r₀ - muParam s₀ r₀ / 2) ∧
  ∀ θ ∈ complexStrip n (stripWidth s₀ / 8),
    ‖K θ - unperturbedTorus (invFreq h B ω) θ‖ ≤ eta0 n τ s₀ r₀ gc ε γ / 2

/-- `K^∞_ω`: a torus given by APPLY, fixed by choice (Definition `bp:p4:normalized-torus`). -/
def applyTorus {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (gc : GConsts) (ε γ : ℝ) (ω : Fin n → ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  Classical.epsilon (IsApplyTorus τ s₀ r₀ B h f gc ε γ ω)

/-- `K_ω = (K^∞_ω)^{[-ph(K^∞_ω)]}` (Definition `bp:p4:normalized-torus`). -/
def normTorus {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (gc : GConsts) (ε γ : ℝ) (ω : Fin n → ℝ) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) :=
  phaseShift (applyTorus τ s₀ r₀ B h f gc ε γ ω)
    (-phaseAverage (applyTorus τ s₀ r₀ B h f gc ε γ ω))

/-- `W_ω = K_ω - K⁰_ω = (u_ω, v_ω)` (Definition `bp:p4:normalized-torus`). -/
def normDisp {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (gc : GConsts) (ε γ : ℝ) (ω : Fin n → ℝ)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  normTorus τ s₀ r₀ B h f gc ε γ ω θ - unperturbedTorus (invFreq h B ω) θ

/-- `K' = K_ω + (0, ι ΔI)`, `ΔI = I_{ω'} - I_ω` (Lemma `bp:p4:lip-error`). -/
def shiftedTorus {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (gc : GConsts) (ε γ : ℝ) (ω ω' : Fin n → ℝ)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  normTorus τ s₀ r₀ B h f gc ε γ ω θ +
    (0, fun i => ((invFreq h B ω' i - invFreq h B ω i : ℝ) : ℂ))

/-- `Z = {I : infDist(I, Bᶜ) ≤ γ}`. -/
def layerSet {n : ℕ} (B : Set (Fin n → ℝ)) (γ : ℝ) : Set (Fin n → ℝ) :=
  {I | Metric.infDist I Bᶜ ≤ γ}

/-- `A_γ = {I ∈ B : infDist(I, Bᶜ) ≥ 2γ, ∇h(I) ∈ Dio_{γ,τ}}`. -/
def goodActions {n : ℕ} (h : (Fin n → ℂ) → ℂ) (B : Set (Fin n → ℝ)) (τ γ : ℝ) :
    Set (Fin n → ℝ) :=
  {I ∈ B | 2 * γ ≤ Metric.infDist I Bᶜ ∧ IsDiophantine γ τ (frequencyMap h I)}

/-- `G₀(θ, I) = k_{∇h(I)}(θ) - (θ, I)` on `ℝⁿ × A_γ`, and `0` elsewhere (in particular on
`ℝⁿ × Z`). -/
def disp {n : ℕ} (τ s₀ r₀ : ℝ) (B : Set (Fin n → ℝ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (gc : GConsts) (ε γ : ℝ) :
    (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  Set.indicator (Set.univ ×ˢ goodActions h B τ γ) fun z =>
    realRestriction (normTorus τ s₀ r₀ B h f gc ε γ (frequencyMap h z.2)) z.1 - z

/-- `C_meas = 2 C_B⁺ + (9/2)ⁿ (2 C_B⁺ + L₊ⁿ C₃⁺)`. -/
def Cmeas (n : ℕ) (Lh CB C3 : ℝ) : ℝ :=
  2 * CBplus CB + (9 / 2) ^ n * (2 * CBplus CB + Lplus Lh ^ n * max C3 0)

end KAM.Head

end
