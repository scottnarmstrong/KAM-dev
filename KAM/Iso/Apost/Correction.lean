/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Standing
public import KAM.Iso.Apost.ConstantsArith
public import KAM.Iso.Linear.Extended
public import KAM.Iso.Linear.Energy
public import KAM.Iso.Linear.BorderSolve
public import KAM.Iso.Linear.NoTwist
public import KAM.Apost.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Part 2 (isoenergetic iteration): the Newton correction

Blueprint node `bpI:p2:correction`
(`KAM.Iso.Apost.correction`). For an `IsoAdmissible` torus `K` at the frequency `ω = s ω*` the data
`ηᴸ, ηᴺ, T, Y` of `K` and `η^ω = -(Ē_H(K) - E₀)` feed the bordered triangular system of
`bpI:p1:border-solve` (`KAM.Iso.Linear.border_solve`); the explicit solution is `isoXi`,
`isoXiOmega`, the correction is `ΔK = P ξ` (`isoCorrection`) and the new frequency parameter is
`s̄ = s (1 - Re ξ^ω)` (`isoNewS`, all in `KAM.Iso.Apost.Defs`).

The proof follows the steps of the blueprint, with `KAM.Apost.correction_spec` as model.

* `correction_core` (`co-data`, `co-xi0`, `co-xi`, `co-omega`'s first half, `co-dk`): everything
  that only involves the frequency `ω` as a Diophantine vector: the Part 1 data (`geometry_noA5`,
  `extended_basic`, `energy_approx`, `KAM.Apost.exactness`, `periodicity`, `frame_basic`), the
  application of `border_solve` (its uniqueness clause is not needed), the arithmetic of
  `KAM.Iso.Apost.Arith` and the bound `|∂_ω P| ≤ C_P/δ` (`norm_fderiv_frameMat_le`).
* `correction`: the claims of `bpI:p2:correction`, adding the frequency update `s̄`.

The helper lemmas are in `KAM.Iso.Apost.CorrectionAux`. `isoNewS_smul_eq` records
`s̄ ω* = (1 - ξ^ω) s ω*` (as complex vectors) once and for all (used by `newton_error`).
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory Filter Topology

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

variable {n : ℕ}

namespace CorrectionAux

/-! ### The correction `ΔK = P ξ` -/

section Transport

variable {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  {ω : Fin n → ℝ} {E₀ r : ℝ}

theorem sumVec_isoCorrection (θ : Fin n → ℂ) :
    sumVec n (isoCorrection H K ω E₀ θ) = frameMat K θ *ᵥ isoXi H K ω E₀ θ :=
  (sumVec n).apply_symm_apply _

theorem diffOn_isoCorrection {S : Set (Fin n → ℂ)} (hP : DifferentiableOn ℂ (frameMat K) S)
    (hξ : DifferentiableOn ℂ (isoXi H K ω E₀) S) :
    DifferentiableOn ℂ (isoCorrection H K ω E₀) S :=
  (sumVecIso n).symm.differentiable.comp_differentiableOn (hP.matrix_mulVec hξ)

theorem periodic_isoCorrection (hP : IsPeriodicOn (frameMat K) r)
    (hξ : IsPeriodicOn (isoXi H K ω E₀) r) : IsPeriodicOn (isoCorrection H K ω E₀) r :=
  fun i z hz => by simp only [isoCorrection, hP i z hz, hξ i z hz]

theorem isRealOnReals_isoCorrection (hP : IsRealMat (frameMat K))
    (hξ : IsRealVec (isoXi H K ω E₀)) : IsRealOnReals (isoCorrection H K ω E₀) := by
  rw [← isRealVec_sumVec_iff]
  intro x s
  simp only [sumVec_isoCorrection]
  exact Triangular.mulVec_im_eq_zero (hP x) (hξ x) s

theorem norm_isoCorrection_le {θ : Fin n → ℂ} {B X : ℝ} (hB : ‖frameMat K θ‖ ≤ B)
    (hX : ‖isoXi H K ω E₀ θ‖ ≤ X) : ‖isoCorrection H K ω E₀ θ‖ ≤ B * X := by
  rw [← norm_sumVec, sumVec_isoCorrection]
  calc _ ≤ ‖frameMat K θ‖ * ‖isoXi H K ω E₀ θ‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ B * X := mul_le_mul hB hX (norm_nonneg _) ((norm_nonneg _).trans hB)

/-- The `sumVec`-image of `∂ ΔK`, by the product rule for `ΔK = P ξ`. -/
theorem sumVec_fderiv_isoCorrection {θ : Fin n → ℂ} (hP : DifferentiableAt ℂ (frameMat K) θ)
    (hξ : DifferentiableAt ℂ (isoXi H K ω E₀) θ) (v : Fin n → ℂ) :
    sumVec n (fderiv ℂ (isoCorrection H K ω E₀) θ v) =
      fderiv ℂ (frameMat K) θ v *ᵥ isoXi H K ω E₀ θ +
        frameMat K θ *ᵥ fderiv ℂ (isoXi H K ω E₀) θ v := by
  rw [← fderiv_sumVec_apply]
  have hfun : (fun y => sumVec n (isoCorrection H K ω E₀ y)) =
      fun y => frameMat K y *ᵥ isoXi H K ω E₀ y := funext sumVec_isoCorrection
  rw [hfun, fderiv_matrix_mulVec_apply hP hξ]

end Transport

/-! ### The bound `|∂_ω P| ≤ C_P/δ` (step `co-dk`) -/

section DerivFrame

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}

/-- `∂_ω P = (∂_ω L  ∂_ω N)`, `∂_ω L = A L - DE` (`fi_dL`), `∂_ω N = A N - X_N`:
`|∂_ω P| ≤ (𝔪² + nε/δ) + (𝔪³ + C_X/δ) ≤ C_P/δ`. -/
theorem norm_fderiv_frameMat_le (hS : Standing n τ M σK σB σT D H ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) {ε δ : ℝ} (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : ‖tangentMat K θ‖ ≤ mSize M σK σB σT) (hN : ‖normalMat K θ‖ ≤ mSize M σK σB σT ^ 2)
    (hA : ‖linMat H K θ‖ ≤ mSize M σK σB σT) (hDE : ‖errDerivMat H K ω θ‖ ≤ n * ε / δ)
    (hX : ‖normalFieldMat H K ω θ‖ ≤ C_X n M σK σB σT / δ) :
    ‖fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))‖ ≤ CP n M σK σB σT / δ := by
  have hm : (0 : ℝ) ≤ mSize M σK σB σT := zero_le_one.trans one_le_mSize
  rw [Identities.fderiv_frameMat hK hG hθ]
  refine (Tools.norm_fromCols_le_add _ _).trans ?_
  have h1 : ‖fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ))‖ ≤
      mSize M σK σB σT ^ 2 + n * ε / δ := by
    rw [Identities.fi_dL hS hK hK𝔅 hθ]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hDE)
    calc ‖linMat H K θ * tangentMat K θ‖ ≤ ‖linMat H K θ‖ * ‖tangentMat K θ‖ :=
          Matrix.linfty_opNorm_mul _ _
      _ ≤ mSize M σK σB σT * mSize M σK σB σT := mul_le_mul hA hL (norm_nonneg _) hm
      _ = mSize M σK σB σT ^ 2 := (sq _).symm
  have h2 : ‖fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ))‖ ≤
      mSize M σK σB σT ^ 3 + C_X n M σK σB σT / δ := by
    have e : fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ)) =
        linMat H K θ * normalMat K θ - normalFieldMat H K ω θ := by
      rw [normalFieldMat]
      abel
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hX)
    calc ‖linMat H K θ * normalMat K θ‖ ≤ ‖linMat H K θ‖ * ‖normalMat K θ‖ :=
          Matrix.linfty_opNorm_mul _ _
      _ ≤ mSize M σK σB σT * mSize M σK σB σT ^ 2 :=
          mul_le_mul hA hN (norm_nonneg _) hm
      _ = mSize M σK σB σT ^ 3 := by ring
  have h3 := Arith.dP_arith (n := n) (M := M) (σK := σK) (σB := σB) (σT := σT) hε1 hδ hδ1
  linarith

end DerivFrame

/-- `‖Y‖₁ ≤ M σ_K σ_B ≤ 𝔪³`. -/
theorem Msigma_le_mSize {τ M σK σB σT : ℝ} (hP : Params n τ M σK σB σT) :
    M * σK * σB ≤ mSize M σK σB σT ^ 3 := by
  have hM := M_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hK := σK_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hB := σB_le_mSize (M := M) (σK := σK) (σB := σB) (σT := σT)
  have hm : (0 : ℝ) ≤ mSize M σK σB σT := zero_le_one.trans one_le_mSize
  calc M * σK * σB ≤ mSize M σK σB σT * mSize M σK σB σT * mSize M σK σB σT :=
        mul_le_mul (mul_le_mul hM hK hP.σK_pos.le hm) hB hP.σB_pos.le (mul_nonneg hm hm)
    _ = mSize M σK σB σT ^ 3 := by ring

/-! ### The core: the correction at a general Diophantine frequency -/

section Core

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} {E₀ r β ε δ : ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- Steps `co-data` to `co-dk` of `bpI:p2:correction` at a general frequency `ω`; the frequency
update is added in `correction`. -/
theorem correction_core (hS : Setting n τ M σK σB σT D H ω γ)
    (hK : AdmissibleNoTwist σK σB D H ω r β ε K)
    (htw : IsUnit (KAM.Iso.extendedTorsionAverage H K ω).det ∧
      ‖(KAM.Iso.extendedTorsionAverage H K ω)⁻¹‖ ≤ σT)
    (hE : ‖KAM.Iso.energyAverage H K - (E₀ : ℂ)‖ ≤ ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) :
    (DifferentiableOn ℂ (isoXi H K ω E₀) (complexStrip n (r - 2 * δ)) ∧
      IsPeriodicOn (isoXi H K ω E₀) (r - 2 * δ) ∧ IsRealVec (isoXi H K ω E₀) ∧
      DifferentiableOn ℂ (isoCorrection H K ω E₀) (complexStrip n (r - 2 * δ)) ∧
      IsPeriodicOn (isoCorrection H K ω E₀) (r - 2 * δ) ∧
      IsRealOnReals (isoCorrection H K ω E₀) ∧ (isoXiOmega H K ω E₀).im = 0) ∧
    (‖bordXi0 ω (isoBordData H K ω E₀)‖ ≤
        hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
      ‖isoXiOmega H K ω E₀‖ ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
      ∀ θ ∈ complexStrip n (r - δ),
        ‖bordXiN ω (isoBordData H K ω E₀) θ‖ ≤
          hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
        ‖bordGL ω (isoBordData H K ω E₀) θ‖ ≤
          hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoXi H K ω E₀ θ‖ ≤ hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ∧
      ‖isoCorrection H K ω E₀ θ‖ ≤ hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ∧
      ‖fderiv ℂ (isoXi H K ω E₀) θ (fun l => (ω l : ℂ))‖ ≤
        hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) ∧
      ‖fderiv ℂ (isoCorrection H K ω E₀) θ (fun l => (ω l : ℂ))‖ ≤
        hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1))) := by
  have hSt := hS.toStanding
  have hP := hSt.toParams
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hSt.gamma_pos
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hsubr : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  -- step `co-data`: frequency, holomorphy, periodicity, realness, bounds, `⟨ηᴺ⟩ = 0`
  obtain ⟨hγω, hω1, hω2⟩ := frequency hSt hr hK.ε_le_one hK𝔅 hK.deriv_le hK.gram hK.error_le
  have hω : ‖ω‖ ≤ Theta n M σK σB σT := hω1.trans hω2
  have hγΘ : γ ≤ Theta n M σK σB σT := hγω.trans hω
  obtain ⟨hgeoDE, -, hgeoN, hgeoXT⟩ := geometry_noA5 hS hK hδ hδ1 h2δ
  obtain ⟨⟨-, -, -, -, -, -, -, hPd, -, hTd, -, -, hηd, -, hTc⟩, -, -, -⟩ :=
    frame_basic hSt hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨-, hperiod, hreal⟩ := periodicity hSt hr hK.holo hK.primary hK𝔅
  obtain ⟨-, -, hPp, -, hTp, -, hηp⟩ := hperiod hGu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hPr, -, hTr, -, hηr, -⟩ := hreal hGu hK.real
  obtain ⟨⟨hYd, hYp, hYr, -, -, -, -, havg, -⟩, hYbd⟩ :=
    extended_basic hS hr hK.holo hK.primary hK.real hK𝔅 hGu
  obtain ⟨⟨-, -, -, -, -, hEim⟩, -, -, -, -⟩ :=
    energy_approx hS hr hK.holo hK.primary hK.real hK𝔅
  have hηN0 : avg (etaN H K ω) = 0 := (exactness hSt hr hK.holo hK.primary hK𝔅).2
  have hbord : bordAvg ω (isoBordData H K ω E₀) = KAM.Iso.extendedTorsionAverage H K ω := by
    rw [havg, torsionAverage_eq_avg H K ω hTc]
    rfl
  have hinv : IsUnit (bordAvg ω (isoBordData H K ω E₀)).det := by
    rw [hbord]
    exact htw.1
  have hσ : ‖(bordAvg ω (isoBordData H K ω E₀))⁻¹‖ ≤ σT := by
    rw [hbord]
    exact htw.2
  have hHL : ∀ θ ∈ complexStrip n r,
      ‖etaL H K ω θ‖ ≤ 2 * n * mSize M σK σB σT ^ 2 * ε := fun θ hθ => (hgeoN θ hθ).1
  have hHN : ∀ θ ∈ complexStrip n r,
      ‖etaN H K ω θ‖ ≤ 2 * n * mSize M σK σB σT * ε := fun θ hθ => (hgeoN θ hθ).2.1
  have hHT : ∀ θ ∈ complexStrip n (r - δ),
      ‖torsion H K ω θ‖ ≤ C_T n M σK σB σT / δ := fun θ hθ => (hgeoXT hω θ hθ).2
  have hHY : ∀ θ ∈ complexStrip n (r - δ),
      ∑ b, ‖energyRow H K θ b‖ ≤ mSize M σK σB σT ^ 3 := fun θ hθ =>
    ((hYbd σK σB (fun θ hθ => ⟨hK.deriv_le θ hθ, (hK.gram θ hθ).2⟩) θ (hsubr hθ)).1).trans
      (Msigma_le_mSize hP)
  have hηω0 : (isoBordData H K ω E₀).ηω.im = 0 := by
    show (-(KAM.Iso.energyAverage H K - (E₀ : ℂ))).im = 0
    simp [hEim]
  have hηωe : ‖(isoBordData H K ω E₀).ηω‖ ≤ ε := by
    show ‖-(KAM.Iso.energyAverage H K - (E₀ : ℂ))‖ ≤ ε
    rw [norm_neg]
    exact hE
  -- the bordered triangular system (Lemma `bpI:p1:border-solve`)
  obtain ⟨⟨hXNd, hXNp, hGd, hGp, hg0, hXLd, hXLp⟩, ⟨hb1, hb2, hb3⟩, ⟨hcs, hcS⟩, -, hre⟩ :=
    border_solve hγ (cohomological_tau_nonneg hSt) hSt.dio hr hδ h2δ (isoBordData H K ω E₀)
      (HL := 2 * n * mSize M σK σB σT ^ 2 * ε) (HN := 2 * n * mSize M σK σB σT * ε)
      (HT := C_T n M σK σB σT / δ) (HY := mSize M σK σB σT ^ 3) (σ := σT)
      (Correction.diffOn_etaL hηd) (Correction.periodic_etaL hηp)
      (Correction.diffOn_etaN hηd) (Correction.periodic_etaN hηp) hHL hHN hηN0 hTd hTp hYd hYp
      hHT hHY hinv hσ 0
  obtain ⟨-, hωr, hXNr, -, hXLr⟩ := hre (Correction.isRealVec_etaL hηr)
    (Correction.isRealVec_etaN hηr) hTr hYr hηω0 (fun i => by simp)
  -- steps `co-xi0`, `co-xi`: the sizes of `(ξ₀, ξ^ω)`, `ξᴺ`, `gᴸ`, `ξᴸ`, `ξ`
  have hS0 : ‖bordSol ω (isoBordData H K ω E₀)‖ ≤
      hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) :=
    hcs.trans (Arith.sStar_arith hP hγ hγΘ hδ hδ1 hε0 (norm_nonneg _) hηωe)
  have hXG := (hcS _ hS0).1
  have hXN : ∀ θ ∈ complexStrip n (r - δ), ‖bordXiN ω (isoBordData H K ω E₀) θ‖ ≤
      hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) := fun θ hθ =>
    ((hXG θ hθ).1).trans (Arith.xiN_arith hγ hδ hδ1 hε0 le_rfl)
  have hGL : ∀ θ ∈ complexStrip n (r - δ), ‖bordGL ω (isoBordData H K ω E₀) θ‖ ≤
      hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := fun θ hθ =>
    ((hXG θ hθ).2).trans (Arith.gL_arith hP hγ hγΘ hδ hδ1 hε0 hω)
  have hXL : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiL ω (isoBordData H K ω E₀) 0 θ‖ ≤
        hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
    intro θ hθ
    have h := (hcS _ hS0).2 _ hGL θ hθ
    rw [sub_zero] at h
    exact h.trans (Arith.xiL_le_hatCxi hγ hδ hε0)
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoXi H K ω E₀ θ‖ ≤
      hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := fun θ hθ =>
    Correction.norm_sumElim_le (hXL θ hθ)
      ((hXN θ (hsub hθ)).trans (Arith.xiN_le_hatCxi hP hγ hγΘ hδ hδ1 hε0))
  -- regularity of `ξ` and `ΔK`
  have hξd : DifferentiableOn ℂ (isoXi H K ω E₀) (complexStrip n (r - 2 * δ)) :=
    Correction.diffOn_sumElim hXLd (hXNd.mono hsub)
  have hξp : IsPeriodicOn (isoXi H K ω E₀) (r - 2 * δ) :=
    Correction.periodic_sumElim hXLp (Triangular.isPeriodicOn_mono (by linarith) hXNp)
  have hξr : IsRealVec (isoXi H K ω E₀) := Correction.isRealVec_sumElim hXLr hXNr
  have hPd' : DifferentiableOn ℂ (frameMat K) (complexStrip n (r - 2 * δ)) :=
    hPd.mono (Triangular.strip_mono (by linarith))
  -- step `co-dk`: `ΔK`, `∂_ω ξ`, `∂_ω ΔK`
  have hΔ : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖isoCorrection H K ω E₀ θ‖ ≤
      hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
    intro θ hθ
    have hθr : θ ∈ complexStrip n r := hsubr (hsub hθ)
    rw [← Arith.hatCDK_arith]
    exact norm_isoCorrection_le (hgeoN θ hθr).2.2.2.2.2 (hXi θ hθ)
  have hdξ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖fderiv ℂ (isoXi H K ω E₀) θ (fun l => (ω l : ℂ))‖ ≤
        hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) := by
    intro θ hθ
    have hopen : complexStrip n (r - 2 * δ) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    have hdL : fderiv ℂ (bordXiL ω (isoBordData H K ω E₀) 0) θ (fun l => (ω l : ℂ)) =
        bordGL ω (isoBordData H K ω E₀) θ := by
      have h1 := hb1 θ hθ
      simp only [bordGL]
      rw [← h1]
      abel
    have hdN : fderiv ℂ (bordXiN ω (isoBordData H K ω E₀)) θ (fun l => (ω l : ℂ)) =
        -(etaN H K ω θ) := neg_eq_iff_eq_neg.mp (hb2 θ (hsub hθ))
    rw [show isoXi H K ω E₀ = fun θ => (Sum.elim (bordXiL ω (isoBordData H K ω E₀) 0 θ)
      (bordXiN ω (isoBordData H K ω E₀) θ) : Fin n ⊕ Fin n → ℂ) from rfl,
      Correction.fderiv_sumElim_apply (hXLd.differentiableAt hopen)
        ((hXNd.mono hsub).differentiableAt hopen), hdL, hdN]
    refine Correction.norm_sumElim_le (hGL θ (hsub hθ)) ?_
    rw [norm_neg]
    exact (hHN θ (hsubr (hsub hθ))).trans (Arith.etaN_arith hP hγ hγΘ hδ hδ1 hε0)
  have hdΔ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖fderiv ℂ (isoCorrection H K ω E₀) θ (fun l => (ω l : ℂ))‖ ≤
        hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1)) := by
    intro θ hθ
    have hθ1 : θ ∈ complexStrip n (r - δ) := hsub hθ
    have hθr : θ ∈ complexStrip n r := hsubr hθ1
    have hopen : complexStrip n (r - 2 * δ) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    obtain ⟨-, -, hL, -, hN, -⟩ := hgeoN θ hθr
    have hA : ‖linMat H K θ‖ ≤ mSize M σK σB σT :=
      FrameAux.norm_linMat_le hSt (hK𝔅 θ hθr)
    have hP' := norm_fderiv_frameMat_le hSt hK.holo hK𝔅 hGu hθr hK.ε_le_one hδ hδ1 hL hN hA
      (hgeoDE θ hθ1).1 (hgeoXT hω θ hθ1).1
    have hPdiff : DifferentiableAt ℂ (frameMat K) θ :=
      hPd.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
    rw [← norm_sumVec, sumVec_fderiv_isoCorrection hPdiff (hξd.differentiableAt hopen)]
    calc _ ≤ ‖fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ)) *ᵥ isoXi H K ω E₀ θ‖ +
          ‖frameMat K θ *ᵥ fderiv ℂ (isoXi H K ω E₀) θ (fun l => (ω l : ℂ))‖ := norm_add_le _ _
      _ ≤ CP n M σK σB σT / δ * (hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) +
          2 * mSize M σK σB σT ^ 2 *
            (hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) := by
        refine add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans ?_)
          ((Matrix.linfty_opNorm_mulVec _ _).trans ?_)
        · exact mul_le_mul hP' (hXi θ hθ) (norm_nonneg _) ((norm_nonneg _).trans hP')
        · exact mul_le_mul (hgeoN θ hθr).2.2.2.2.2 (hdξ θ hθ) (norm_nonneg _)
            (by positivity)
      _ ≤ _ := Arith.dPxi_arith hP hγ hγΘ hδ hδ1 hε0
  exact ⟨⟨hξd, hξp, hξr, diffOn_isoCorrection hPd' hξd,
    periodic_isoCorrection (Triangular.isPeriodicOn_mono (by linarith) hPp) hξp,
    isRealOnReals_isoCorrection hPr hξr, hωr⟩,
    ⟨(BorderSolve.norm_bordXi0_le ω _).trans hS0, (BorderSolve.norm_bordXiOmega_le ω _).trans hS0,
      fun θ hθ => ⟨hXN θ hθ, hGL θ hθ⟩⟩,
    fun θ hθ => ⟨hXi θ hθ, hΔ θ hθ, hdξ θ hθ, hdΔ θ hθ⟩⟩

end Core

end CorrectionAux

/-! ### The frequency update `s̄ = s (1 - Re ξ^ω)` -/

section NewS

variable {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  {ωstar : Fin n → ℝ} {E₀ s : ℝ}

/-- `s̄ ω* - s ω* = -(Re ξ^ω) (s ω*)`. -/
theorem isoNewS_smul_sub :
    isoNewS H K ωstar E₀ s • ωstar - s • ωstar =
      -(isoXiOmega H K (s • ωstar) E₀).re • (s • ωstar) := by
  rw [isoNewS, ← sub_smul, smul_smul]
  congr 1
  ring

/-- `s̄ ω* = (1 - ξ^ω) (s ω*)` as complex vectors, for real `ξ^ω` (`Δω = -ω ξ^ω`). -/
theorem isoNewS_smul_eq (hre : (isoXiOmega H K (s • ωstar) E₀).im = 0) :
    (fun l => ((isoNewS H K ωstar E₀ s • ωstar) l : ℂ)) =
      (1 - isoXiOmega H K (s • ωstar) E₀) • (fun l => ((s • ωstar) l : ℂ)) := by
  have hz : isoXiOmega H K (s • ωstar) E₀ = ((isoXiOmega H K (s • ωstar) E₀).re : ℂ) :=
    Complex.ext (by simp) (by simp [hre])
  funext l
  conv_rhs => rw [hz]
  simp only [isoNewS, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one]
  ring

end NewS

section Step

variable {τ M σK σB σT σω ν γ : ℝ} {ωstar : Fin n → ℝ}
  {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}

/-- `bpI:p2:correction`. -/
theorem correction (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) {E₀ r β ε δ s : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) :
    (DifferentiableOn ℂ (isoXi H K (s • ωstar) E₀) (complexStrip n (r - 2 * δ)) ∧
      IsPeriodicOn (isoXi H K (s • ωstar) E₀) (r - 2 * δ) ∧ IsRealVec (isoXi H K (s • ωstar) E₀) ∧
      DifferentiableOn ℂ (isoCorrection H K (s • ωstar) E₀) (complexStrip n (r - 2 * δ)) ∧
      IsPeriodicOn (isoCorrection H K (s • ωstar) E₀) (r - 2 * δ) ∧
      IsRealOnReals (isoCorrection H K (s • ωstar) E₀) ∧
      (isoXiOmega H K (s • ωstar) E₀).im = 0) ∧
    (‖bordXi0 (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ ≤
        hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
      ‖isoXiOmega H K (s • ωstar) E₀‖ ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
      ∀ θ ∈ complexStrip n (r - δ),
        ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
          hatCxiN n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) ∧
        ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
          hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2))) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ hatCxi n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ∧
      ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤ hatCDK n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) ∧
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        hatCg n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 2)) ∧
      ‖fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        hatCpartial n τ M σK σB σT * ε / (γ ^ 2 * δ ^ (aExp n τ + 1))) ∧
    (‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ =
        |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ ∧
      ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤
        Theta n M σK σB σT ^ 2 * hatCS n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ)) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤ dStep n τ M σK σB σT γ ε δ) ∧
    ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤ dStep n τ M σK σB σT γ ε δ := by
  have hSet := hS.setting hK.s_gt.le
  obtain ⟨hreg, hb1, hb2⟩ := CorrectionAux.correction_core hSet hK.toAdmissibleNoTwist hK.twist
    hK.energy_le hδ hδ1 h2δ
  have hP := hS.toParams
  have hγ := hS.gamma_pos
  obtain ⟨hγω, hω⟩ := hK.freq hS
  have hγΘ : γ ≤ Theta n M σK σB σT := hγω.trans hω
  have hnorm : ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤
      Theta n M σK σB σT ^ 2 * hatCS n τ M σK σB σT * ε / (γ ^ 2 * δ ^ aExp n τ) := by
    rw [isoNewS_smul_sub, norm_smul, norm_neg, Real.norm_eq_abs]
    calc |(isoXiOmega H K (s • ωstar) E₀).re| * ‖s • ωstar‖
        ≤ ‖isoXiOmega H K (s • ωstar) E₀‖ * ‖s • ωstar‖ :=
          mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)
      _ ≤ hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1)) * ‖s • ωstar‖ :=
          mul_le_mul_of_nonneg_right hb1.2.1 (norm_nonneg _)
      _ = ‖s • ωstar‖ * (hatCS n τ M σK σB σT * ε / (γ * δ ^ (kappa n τ + 1))) := mul_comm _ _
      _ ≤ _ := Arith.dOmega_arith hP hγ hγΘ hδ hδ1 hK.ε_nonneg hω
  have heq : ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ =
      |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ := by
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  exact ⟨hreg, hb1, hb2, ⟨heq, hnorm⟩,
    fun θ hθ => (hb2 θ hθ).2.1.trans (Arith.hatCDK_le_dStep hγ hδ hK.ε_nonneg),
    hnorm.trans (Arith.Theta_sq_hatCS_le_dStep hγ hδ hK.ε_nonneg)⟩

end Step

end KAM.Iso.Apost
