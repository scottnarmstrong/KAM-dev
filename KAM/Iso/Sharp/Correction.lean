/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp.BorderBounds
public import KAM.Iso.Sharp.ConstantsArith
public import KAM.Iso.Apost.Correction
public import KAM.Sharp.Correction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The size of the isoenergetic correction, with general small-divisor data

Blueprint `bpI:p2s:correction` (`KAM.Iso.Sharp.iso_correction_bounds`): for an `IsoAdmissible`
torus `K` at `ω = s ω*`, the bounds of `ξ₀, ξ^ω, ξᴺ, gᴸ` on `T_{r-δ}` and of `ξ, ΔK, ∂_ω ξ, ∂_ω ΔK`
on `T_{r-2δ}` in the separate sizes, and of `Δω = s̄ ω* - s ω*`. The qualitative clauses are those
of `KAM.Iso.Apost.correction`.

The proof follows the blueprint:

* `stepI:p2s:co-data`: `H_L = 2nσ_Kσ_Bε`, `H_N = 2nσ_Kε` (`KAM.Sharp.frame_bounds`),
  `H_Y = Mσ_Kσ_B` (`KAM.Iso.Linear.extended_basic`), `|η^ω| ≤ ε`, `σ = σ_T`, `|ω| ≤ Θ`
  (`KAM.Apost.frequency`) and `H_T = C_T0 + 1` on `T_{r-δ}` (`KAM.Sharp.torsion_bound`);
  `KAM.Iso.Sharp.border_bounds` applies;
* `stepI:p2s:co-s`, `co-xi`, `co-om`: the arithmetic, in `u = ε/(γδ^κ)` and
  `E = ε/(γ²δ^{2κ})`, with `KAM.Sharp.absorb`;
* `stepI:p2s:co-dk`: `|∂_ω P| ≤ C_P` (`IsoCorrectionSharp.norm_fderiv_frameMat_le_iCP`, through
  `∂_ω L = AL - DE` and `∂_ω N` of `KAM.Sharp.torsion_identity`, no factor `1/δ`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear KAM.Iso.Apost KAM.Sharp

variable {n : ℕ} {κ cR M σK σB σT γb : ℝ}

namespace IsoCorrectionSharp

/-- Nonnegativity of the constants of `bpI:p2s:correction`. -/
theorem iso_nonneg (hcR : 0 < cR) (hM : 0 < M) (hσK : 0 < σK) (hσB : 0 < σB) (hσT : 0 < σT)
    (hγb : 0 < γb) :
    0 ≤ hT n M σK σB ∧ 0 ≤ thetaS n M σK σB ∧ 0 ≤ iCS n cR M σK σB σT γb ∧
      0 ≤ iCXiN n cR M σK σB σT γb ∧ 0 ≤ iCG n cR M σK σB σT γb ∧
      0 ≤ iCDXi n cR M σK σB σT γb ∧ 0 ≤ iCXi n cR M σK σB σT γb ∧ 0 ≤ iCP n M σK σB := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have p1 : 0 ≤ hT n M σK σB := by unfold hT cT0; positivity
  have p2 : 0 ≤ thetaS n M σK σB := by unfold thetaS; positivity
  have p3 : 0 ≤ iCS n cR M σK σB σT γb := by unfold iCS; positivity
  have p4 : 0 ≤ iCXiN n cR M σK σB σT γb := by unfold iCXiN; positivity
  have p5 : 0 ≤ iCG n cR M σK σB σT γb := by unfold iCG; positivity
  have p6 : 0 ≤ iCDXi n cR M σK σB σT γb := by unfold iCDXi; positivity
  have p7 : 0 ≤ iCXi n cR M σK σB σT γb := by unfold iCXi; positivity
  have p8 : 0 ≤ iCP n M σK σB := by unfold iCP; positivity
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩

variable {τ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {ω : Fin n → ℝ} {γ : ℝ}

/-- Step `stepI:p2s:co-dk`: `|∂_ω P| ≤ |∂_ω L| + |∂_ω N| ≤ C_P` from `|L| ≤ σ_K`, `|Lᵀ| ≤ 2nσ_K`,
`|N| ≤ σ_Kσ_B`, `|B| ≤ σ_B`, `|A|, |Aᵀ| ≤ M`, `|DE| ≤ n`, `|(DE)ᵀ| ≤ 2n`. -/
theorem norm_fderiv_frameMat_le_iCP (hS : Standing n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n r) (hL : ‖tangentMat K θ‖ ≤ σK)
    (hLt : ‖(tangentMat K θ)ᵀ‖ ≤ 2 * n * σK) (hN : ‖normalMat K θ‖ ≤ σK * σB)
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB) (hA : ‖linMat H K θ‖ ≤ M) (hAt : ‖(linMat H K θ)ᵀ‖ ≤ M)
    (hF : ‖errDerivMat H K ω θ‖ ≤ n) (hFt : ‖(errDerivMat H K ω θ)ᵀ‖ ≤ 2 * n) :
    ‖fderiv ℂ (frameMat K) θ (fun l => (ω l : ℂ))‖ ≤ iCP n M σK σB := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hσK : 0 ≤ σK := (norm_nonneg _).trans hL
  have hσB : 0 ≤ σB := (norm_nonneg _).trans hB
  have hM : 0 ≤ M := (norm_nonneg _).trans hA
  set X := linMat H K θ * tangentMat K θ - errDerivMat H K ω θ with hXdef
  have hX : ‖X‖ ≤ M * σK + n :=
    (norm_sub_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul hA hL (norm_nonneg _) hM)) hF)
  have hXt : ‖Xᵀ‖ ≤ 2 * n * σK * M + 2 * n := by
    rw [hXdef, Matrix.transpose_sub, Matrix.transpose_mul]
    exact (norm_sub_le _ _).trans (add_le_add ((Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul hLt hAt (norm_nonneg _) (by positivity))) hFt)
  have hdL : fderiv ℂ (tangentMat K) θ (fun l => (ω l : ℂ)) = X :=
    TorsionPoly.fderiv_tangentMat_eq hS hK hKD hθ ω
  have hdN := (torsion_identity hS hr hK hKD hG ω θ hθ).2.1
  rw [← hXdef] at hdN
  rw [Identities.fderiv_frameMat hK hG hθ]
  refine (Tools.norm_fromCols_le_add _ _).trans ?_
  rw [hdL, hdN]
  have hW : ‖Xᵀ * tangentMat K θ + (tangentMat K θ)ᵀ * X‖ ≤
      (2 * n * σK * M + 2 * n) * σK + 2 * n * σK * (M * σK + n) :=
    (norm_add_le _ _).trans (add_le_add
      ((Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hXt hL (norm_nonneg _) (by positivity)))
      ((Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hLt hX (norm_nonneg _) (by positivity))))
  have h1 : ‖omegaZeroMatrix n * X * (gramMatrix K θ)⁻¹‖ ≤ (M * σK + n) * σB := by
    refine (Matrix.linfty_opNorm_mul _ _).trans ?_
    rw [norm_omegaZeroMatrix_mul]
    exact mul_le_mul hX hB (norm_nonneg _) (by positivity)
  have h2 : ‖normalMat K θ * (Xᵀ * tangentMat K θ + (tangentMat K θ)ᵀ * X) *
      (gramMatrix K θ)⁻¹‖ ≤
      σK * σB * ((2 * n * σK * M + 2 * n) * σK + 2 * n * σK * (M * σK + n)) * σB := by
    refine (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul ?_ hB (norm_nonneg _) (by positivity))
    exact (Matrix.linfty_opNorm_mul _ _).trans (mul_le_mul hN hW (norm_nonneg _) (by positivity))
  calc ‖X‖ + ‖omegaZeroMatrix n * X * (gramMatrix K θ)⁻¹ - normalMat K θ *
        (Xᵀ * tangentMat K θ + (tangentMat K θ)ᵀ * X) * (gramMatrix K θ)⁻¹‖
      ≤ (M * σK + n) + ((M * σK + n) * σB +
          σK * σB * ((2 * n * σK * M + 2 * n) * σK + 2 * n * σK * (M * σK + n)) * σB) :=
        add_le_add hX ((norm_sub_le _ _).trans (add_le_add h1 h2))
    _ = iCP n M σK σB := by unfold iCP; ring

end IsoCorrectionSharp

variable {τ σω ν : ℝ} {ωstar : Fin n → ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {γ : ℝ}

/-- Blueprint `bpI:p2s:correction` (qualitative clauses: the first conjunct of
`KAM.Iso.Apost.correction`). -/
theorem iso_correction_bounds (hC : CohData n τ κ cR)
    (hS : IsoStanding n τ M σK σB σT σω ν ωstar D H γ) (hγb : γ ≤ γb) {E₀ r β ε δ s : ℝ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : IsoAdmissible σK σB σT D H ωstar E₀ r β ε s K) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (h2δ : 2 * δ < r) (hεδ : ε ≤ δ)
    (hTS : cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) ≤ 1) :
    (‖bordXi0 (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ ≤
        iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ) ∧
      ‖isoXiOmega H K (s • ωstar) E₀‖ ≤ iCS n cR M σK σB σT γb * ε / (γ * δ ^ κ) ∧
      ∀ θ ∈ complexStrip n (r - δ),
        ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
          iCXiN n cR M σK σB σT γb * ε / (γ * δ ^ κ) ∧
        ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
          iCG n cR M σK σB σT γb * ε / (γ * δ ^ κ)) ∧
    (∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ iCXi n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ∧
      ‖isoCorrection H K (s • ωstar) E₀ θ‖ ≤ iCDK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) ∧
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        iCDXi n cR M σK σB σT γb * ε / (γ * δ ^ κ) ∧
      ‖fderiv ℂ (isoCorrection H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        iCdK n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ))) ∧
    ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ = |isoNewS H K ωstar E₀ s - s| * ‖ωstar‖ ∧
    ‖isoNewS H K ωstar E₀ s • ωstar - s • ωstar‖ ≤
      iCDw n cR M σK σB σT γb * ε / (γ ^ 2 * δ ^ (2 * κ)) := by
  have hSet := hS.setting hK.s_gt.le
  have hSt := hSet.toStanding
  have hKN := hK.toAdmissibleNoTwist
  have hr := hK.r_pos
  have hε0 := hK.ε_nonneg
  have hγ := hS.gamma_pos
  have hγb0 : 0 < γb := hγ.trans_le hγb
  have hcR := hC.cR_pos
  have hσK := hS.σK_pos
  have hσB := hS.σB_pos
  have hσT := hS.σT_pos
  have hM := hS.M_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨hhT0, hΘ0, hCS0, hCXN0, hCG0, hCDX0, hCX0, hCP0⟩ :=
    IsoCorrectionSharp.iso_nonneg (n := n) hcR hM hσK hσB hσT hγb0
  have hsub : complexStrip n (r - 2 * δ) ⊆ complexStrip n (r - δ) :=
    Triangular.strip_mono (by linarith)
  have hsubr : complexStrip n (r - δ) ⊆ complexStrip n r := Triangular.strip_mono (by linarith)
  have hK𝔅 : ∀ θ ∈ complexStrip n r, K θ ∈ D := fun θ hθ =>
    hK.ball_sub θ hθ (Metric.mem_ball_self hK.β_pos)
  have hGu : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det := fun θ hθ => (hK.gram θ hθ).1
  -- step `co-data`
  obtain ⟨-, hω1, -⟩ := frequency hSt hr hK.ε_le_one hK𝔅 hK.deriv_le hK.gram hK.error_le
  have hω : ‖s • ωstar‖ ≤ thetaS n M σK σB := by
    refine hω1.trans ?_
    unfold thetaS
    exact mul_le_mul_of_nonneg_left (by linarith [hK.ε_le_one]) (by positivity)
  obtain ⟨⟨-, -, -, -, -, -, -, hPd, -, hTd, -, -, hηd, -, hTc⟩, -, -, -⟩ :=
    frame_basic hSt hr hK.β_pos hK.holo hK.ball_sub hK.deriv_le hK.gram
  obtain ⟨-, hperiod, -⟩ := periodicity hSt hr hK.holo hK.primary hK𝔅
  obtain ⟨-, -, -, -, hTp, -, hηp⟩ := hperiod hGu
  obtain ⟨⟨hYd, hYp, -, -, -, -, -, havg, -⟩, hYbd⟩ :=
    extended_basic hSet hr hK.holo hK.primary hK.real hK𝔅 hGu
  have hηN0 : avg (etaN H K (s • ωstar)) = 0 := (exactness hSt hr hK.holo hK.primary hK𝔅).2
  have hbord : bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀) =
      KAM.Iso.extendedTorsionAverage H K (s • ωstar) := by
    rw [havg, torsionAverage_eq_avg H K (s • ωstar) hTc]
    rfl
  have hinv : IsUnit (bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀)).det := by
    rw [hbord]
    exact hK.twist.1
  have hσ : ‖(bordAvg (s • ωstar) (isoBordData H K (s • ωstar) E₀))⁻¹‖ ≤ σT := by
    rw [hbord]
    exact hK.twist.2
  have hfb : ∀ θ ∈ complexStrip n r, _ := fun θ hθ =>
    frame_bounds hSt (hK𝔅 θ hθ) (hK.deriv_le θ hθ) (hGu θ hθ) (hK.gram θ hθ).2 (s • ωstar)
  have hHL : ∀ θ ∈ complexStrip n r, ‖etaL H K (s • ωstar) θ‖ ≤ 2 * n * σK * σB * ε :=
    fun θ hθ => ((hfb θ hθ).2.2.2.2.2.2.2.2.2.2.1 ε (hK.error_le θ hθ)).2.1
  have hHN : ∀ θ ∈ complexStrip n r, ‖etaN H K (s • ωstar) θ‖ ≤ 2 * n * σK * ε :=
    fun θ hθ => ((hfb θ hθ).2.2.2.2.2.2.2.2.2.2.1 ε (hK.error_le θ hθ)).2.2
  have hHT : ∀ θ ∈ complexStrip n (r - δ), ‖torsion H K (s • ωstar) θ‖ ≤ hT n M σK σB := by
    intro θ hθ
    have := torsion_bound hC hSt hKN hδ hδ1 (by linarith) hεδ θ hθ
    unfold hT
    have e : cT0 n M σK σB + cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1)) =
        cT0 n M σK σB + (cT1 n σK σB * ε / δ + cT2 n κ cR M σK σB * ε / (γ * δ ^ (κ + 1))) := by
      ring
    linarith
  have hHY : ∀ θ ∈ complexStrip n (r - δ), ∑ b, ‖energyRow H K θ b‖ ≤ M * σK * σB :=
    fun θ hθ => (hYbd σK σB (fun θ hθ => ⟨hK.deriv_le θ hθ, (hK.gram θ hθ).2⟩) θ (hsubr hθ)).1
  have hηωe : ‖(isoBordData H K (s • ωstar) E₀).ηω‖ ≤ ε := by
    show ‖-(KAM.Iso.energyAverage H K - (E₀ : ℂ))‖ ≤ ε
    rw [norm_neg]
    exact hK.energy_le
  -- the bordered system (Corollary `bpI:p2s:border` and Lemma `bpI:p1:border-solve`)
  obtain ⟨hb0, hbS⟩ := border_bounds hC hγ hSt.dio hr hδ hδ1 h2δ (isoBordData H K (s • ωstar) E₀)
    (HL := 2 * n * σK * σB * ε) (HN := 2 * n * σK * ε) (HT := hT n M σK σB)
    (HY := M * σK * σB) (σ := σT)
    (KAM.Apost.Correction.diffOn_etaL hηd) (KAM.Apost.Correction.periodic_etaL hηp)
    (KAM.Apost.Correction.diffOn_etaN hηd) (KAM.Apost.Correction.periodic_etaN hηp) hHL hHN hηN0
    hTd hTp hYd hYp hHT hHY hinv hσ 0
  obtain ⟨⟨hXNd, -, -, -, -, hXLd, -⟩, ⟨hb1, hb2, -⟩, -, -, -⟩ :=
    border_solve hγ hC.tau_nonneg hSt.dio hr hδ h2δ (isoBordData H K (s • ωstar) E₀)
      (HL := 2 * n * σK * σB * ε) (HN := 2 * n * σK * ε) (HT := hT n M σK σB)
      (HY := M * σK * σB) (σ := σT)
      (KAM.Apost.Correction.diffOn_etaL hηd) (KAM.Apost.Correction.periodic_etaL hηp)
      (KAM.Apost.Correction.diffOn_etaN hηd) (KAM.Apost.Correction.periodic_etaN hηp) hHL hHN
      hηN0 hTd hTp hYd hYp hHT hHY hinv hσ 0
  -- steps `co-s`, `co-xi`: in terms of `u = ε/(γ δ^κ)` and `E = ε/(γ² δ^{2κ})`
  obtain ⟨⟨hεu, huE⟩, -, -, -⟩ := absorb hC.one_le_kappa hγ hγb hδ hδ1 hε0
  set u := ε / (γ * δ ^ κ) with hu
  set E := ε / (γ ^ 2 * δ ^ (2 * κ)) with hE
  have hu0 : 0 ≤ u := div_nonneg hε0 (mul_pos hγ (Real.rpow_pos_of_pos hδ κ)).le
  have hE0 : 0 ≤ E := div_nonneg hε0 (by positivity)
  have hΓN : cR * γ⁻¹ * δ ^ (-κ) * (2 * n * σK * ε) = 2 * n * σK * cR * u :=
    CorrectionSharp.gamma_mul_eq hγ hδ
  have hS0 : ‖bordSol (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ ≤
      iCS n cR M σK σB σT γb * u := by
    refine hb0.trans ?_
    rw [mul_assoc (hT n M σK σB), mul_assoc (M * σK * σB), hΓN]
    have h1 : 2 * n * σK * σB * ε + hT n M σK σB * (2 * n * σK * cR * u) ≤
        (2 * n * σK * σB * γb + 2 * n * cR * σK * hT n M σK σB) * u := by
      have : 2 * (n : ℝ) * σK * σB * ε ≤ 2 * n * σK * σB * (γb * u) :=
        mul_le_mul_of_nonneg_left hεu (by positivity)
      calc _ ≤ 2 * n * σK * σB * (γb * u) + hT n M σK σB * (2 * n * σK * cR * u) :=
            add_le_add this le_rfl
        _ = _ := by ring
    have h2 : ‖(isoBordData H K (s • ωstar) E₀).ηω‖ + M * σK * σB * (2 * n * σK * cR * u) ≤
        (γb + 2 * n * cR * M * σK ^ 2 * σB) * u :=
      calc _ ≤ γb * u + M * σK * σB * (2 * n * σK * cR * u) :=
            add_le_add (hηωe.trans hεu) le_rfl
        _ = _ := by ring
    calc _ ≤ σT * (max (2 * n * σK * σB * γb + 2 * n * cR * σK * hT n M σK σB)
          (γb + 2 * n * cR * M * σK ^ 2 * σB) * u) := by
          refine mul_le_mul_of_nonneg_left (max_le ?_ ?_) hσT.le
          · exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0)
          · exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hu0)
      _ = iCS n cR M σK σB σT γb * u := by unfold iCS; ring
  have hX0 : ‖bordXi0 (s • ωstar) (isoBordData H K (s • ωstar) E₀)‖ ≤
      iCS n cR M σK σB σT γb * u := (BorderSolve.norm_bordXi0_le _ _).trans hS0
  have hXω : ‖isoXiOmega H K (s • ωstar) E₀‖ ≤ iCS n cR M σK σB σT γb * u :=
    (BorderSolve.norm_bordXiOmega_le _ _).trans hS0
  obtain ⟨hbNG, hbL⟩ := hbS _ hS0
  have e1 : iCS n cR M σK σB σT γb * u + cR * γ⁻¹ * δ ^ (-κ) * (2 * n * σK * ε) =
      iCXiN n cR M σK σB σT γb * u := by
    rw [hΓN]
    unfold iCXiN
    ring
  have hXN : ∀ θ ∈ complexStrip n (r - δ),
      ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
        iCXiN n cR M σK σB σT γb * u := fun θ hθ => by
    have h := (hbNG θ hθ).1
    rwa [e1] at h
  have hGL : ∀ θ ∈ complexStrip n (r - δ),
      ‖bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
        iCG n cR M σK σB σT γb * u := by
    intro θ hθ
    have h := (hbNG θ hθ).2
    rw [e1] at h
    have h3 : 2 * (n : ℝ) * σK * σB * ε ≤ 2 * n * σK * σB * (γb * u) :=
      mul_le_mul_of_nonneg_left hεu (by positivity)
    calc _ ≤ hT n M σK σB * (iCXiN n cR M σK σB σT γb * u) +
          ‖s • ωstar‖ * (iCS n cR M σK σB σT γb * u) + 2 * n * σK * σB * ε := h
      _ ≤ hT n M σK σB * (iCXiN n cR M σK σB σT γb * u) +
          thetaS n M σK σB * (iCS n cR M σK σB σT γb * u) + 2 * n * σK * σB * (γb * u) :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hω (by positivity))) h3
      _ = iCG n cR M σK σB σT γb * u := by unfold iCG; ring
  -- step `co-xi`: `ξᴸ`, `ξ`, `ΔK`
  have hXL : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ ≤
        cR * iCG n cR M σK σB σT γb * E := by
    intro θ hθ
    have h := hbL _ hGL θ hθ
    rw [sub_zero, CorrectionSharp.gamma_mul_u_eq hγ hδ] at h
    rw [hE, ← mul_div_assoc]
    exact h
  have hXNE : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ ≤
        γb * iCXiN n cR M σK σB σT γb * E := by
    intro θ hθ
    calc _ ≤ iCXiN n cR M σK σB σT γb * u := hXN θ (hsub hθ)
      _ ≤ iCXiN n cR M σK σB σT γb * (γb * E) := mul_le_mul_of_nonneg_left huE hCXN0
      _ = γb * iCXiN n cR M σK σB σT γb * E := by ring
  have hXi : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖isoXi H K (s • ωstar) E₀ θ‖ ≤ iCXi n cR M σK σB σT γb * E := fun θ hθ =>
    KAM.Apost.Correction.norm_sumElim_le
      ((hXL θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE0))
      ((hXNE θ hθ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hE0))
  -- regularity of `ξ`
  have hξd : DifferentiableOn ℂ (isoXi H K (s • ωstar) E₀) (complexStrip n (r - 2 * δ)) :=
    KAM.Apost.Correction.diffOn_sumElim hXLd (hXNd.mono hsub)
  -- step `co-xi`, the derivative: `∂_ω ξ = (gᴸ, -ηᴺ)`
  have hdξ : ∀ θ ∈ complexStrip n (r - 2 * δ),
      ‖fderiv ℂ (isoXi H K (s • ωstar) E₀) θ (fun l => ((s • ωstar) l : ℂ))‖ ≤
        iCDXi n cR M σK σB σT γb * u := by
    intro θ hθ
    have hopen : complexStrip n (r - 2 * δ) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    have hdL : fderiv ℂ (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0) θ
        (fun l => ((s • ωstar) l : ℂ)) = bordGL (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ := by
      have h1 := hb1 θ hθ
      simp only [bordGL]
      rw [← h1]
      abel
    have hdN : fderiv ℂ (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀)) θ
        (fun l => ((s • ωstar) l : ℂ)) = -(etaN H K (s • ωstar) θ) :=
      neg_eq_iff_eq_neg.mp (hb2 θ (hsub hθ))
    rw [show isoXi H K (s • ωstar) E₀ = fun θ =>
      (Sum.elim (bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ)
        (bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ) : Fin n ⊕ Fin n → ℂ) from rfl,
      KAM.Apost.Correction.fderiv_sumElim_apply (hXLd.differentiableAt hopen)
        ((hXNd.mono hsub).differentiableAt hopen), hdL, hdN]
    refine KAM.Apost.Correction.norm_sumElim_le
      ((hGL θ (hsub hθ)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0)) ?_
    rw [norm_neg]
    calc ‖etaN H K (s • ωstar) θ‖ ≤ 2 * n * σK * ε := hHN θ (hsubr (hsub hθ))
      _ ≤ 2 * n * σK * (γb * u) := mul_le_mul_of_nonneg_left hεu (by positivity)
      _ = 2 * n * σK * γb * u := by ring
      _ ≤ iCDXi n cR M σK σB σT γb * u := mul_le_mul_of_nonneg_right (le_max_right _ _) hu0
  refine ⟨⟨by rw [mul_div_assoc]; exact hX0, by rw [mul_div_assoc]; exact hXω,
      fun θ hθ => ⟨by rw [mul_div_assoc]; exact hXN θ hθ, by rw [mul_div_assoc]; exact hGL θ hθ⟩⟩,
    fun θ hθ => ⟨by rw [mul_div_assoc]; exact hXi θ hθ, ?_, by rw [mul_div_assoc]; exact hdξ θ hθ,
      ?_⟩, ?_, ?_⟩
  · -- `ΔK = L ξᴸ + N ξᴺ`
    have hθr : θ ∈ complexStrip n r := hsubr (hsub hθ)
    have hP := (hfb θ hθr).2.2.2.2.2.2.2.2.2.2.2
    rw [← norm_sumVec, CorrectionAux.sumVec_isoCorrection, mul_div_assoc]
    calc ‖frameMat K θ *ᵥ isoXi H K (s • ωstar) E₀ θ‖ ≤
          σK * ‖bordXiL (s • ωstar) (isoBordData H K (s • ωstar) E₀) 0 θ‖ +
            σK * σB * ‖bordXiN (s • ωstar) (isoBordData H K (s • ωstar) E₀) θ‖ := hP _ _
      _ ≤ σK * (cR * iCG n cR M σK σB σT γb * E) +
            σK * σB * (γb * iCXiN n cR M σK σB σT γb * E) :=
          add_le_add (mul_le_mul_of_nonneg_left (hXL θ hθ) hσK.le)
            (mul_le_mul_of_nonneg_left (hXNE θ hθ) (by positivity))
      _ = iCDK n cR M σK σB σT γb * E := by unfold iCDK; ring
  · -- step `co-dk`: `∂_ω ΔK = (∂_ω P) ξ + P ∂_ω ξ`
    have hθ1 : θ ∈ complexStrip n (r - δ) := hsub hθ
    have hθr : θ ∈ complexStrip n r := hsubr hθ1
    have hopen : complexStrip n (r - 2 * δ) ∈ 𝓝 θ := (isOpen_complexStrip n _).mem_nhds hθ
    obtain ⟨hL, hLt, hN, -, -, -, hPn, hA, -, hAt, -, -⟩ := hfb θ hθr
    obtain ⟨hF, hFt⟩ := Geometry.geo_de hSt hK.holo hK𝔅 hK.error_le hδ θ hθ1
    have hεδ1 : ε / δ ≤ 1 := (div_le_one hδ).2 hεδ
    have hF' : ‖errDerivMat H K (s • ωstar) θ‖ ≤ n := by
      refine hF.trans (le_of_eq_of_le (mul_div_assoc _ _ _) ?_)
      exact mul_le_of_le_one_right hn hεδ1
    have hFt' : ‖(errDerivMat H K (s • ωstar) θ)ᵀ‖ ≤ 2 * n := by
      refine hFt.trans (le_of_eq_of_le (mul_div_assoc _ _ _) ?_)
      exact mul_le_of_le_one_right (by positivity) hεδ1
    have hdP := IsoCorrectionSharp.norm_fderiv_frameMat_le_iCP hSt hr hK.holo hK𝔅 hGu hθr hL hLt
      hN (hK.gram θ hθr).2 hA hAt hF' hFt'
    have hPdiff : DifferentiableAt ℂ (frameMat K) θ :=
      hPd.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
    rw [← norm_sumVec, CorrectionAux.sumVec_fderiv_isoCorrection hPdiff
      (hξd.differentiableAt hopen), mul_div_assoc]
    calc _ ≤ ‖fderiv ℂ (frameMat K) θ (fun l => ((s • ωstar) l : ℂ)) *ᵥ
            isoXi H K (s • ωstar) E₀ θ‖ +
          ‖frameMat K θ *ᵥ fderiv ℂ (isoXi H K (s • ωstar) E₀) θ
            (fun l => ((s • ωstar) l : ℂ))‖ := norm_add_le _ _
      _ ≤ iCP n M σK σB * (iCXi n cR M σK σB σT γb * E) +
          σK * (1 + σB) * (iCDXi n cR M σK σB σT γb * u) :=
          add_le_add ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul hdP (hXi θ hθ) (norm_nonneg _) hCP0))
            ((Matrix.linfty_opNorm_mulVec _ _).trans
              (mul_le_mul hPn (hdξ θ hθ) (norm_nonneg _) (by positivity)))
      _ ≤ iCP n M σK σB * (iCXi n cR M σK σB σT γb * E) +
          σK * (1 + σB) * (iCDXi n cR M σK σB σT γb * (γb * E)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left huE hCDX0) (by positivity))
      _ = iCdK n cR M σK σB σT γb * E := by unfold iCdK; ring
  · -- `|Δω| = |s̄ - s| |ω*|`
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  · -- step `co-om`
    rw [isoNewS_smul_sub, norm_smul, norm_neg, Real.norm_eq_abs, mul_div_assoc]
    calc |(isoXiOmega H K (s • ωstar) E₀).re| * ‖s • ωstar‖
        ≤ ‖isoXiOmega H K (s • ωstar) E₀‖ * ‖s • ωstar‖ :=
          mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (norm_nonneg _)
      _ ≤ iCS n cR M σK σB σT γb * u * thetaS n M σK σB :=
          mul_le_mul hXω hω (norm_nonneg _) (by positivity)
      _ ≤ iCS n cR M σK σB σT γb * (γb * E) * thetaS n M σK σB :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huE hCS0) hΘ0
      _ = iCDw n cR M σK σB σT γb * E := by unfold iCDw; ring

end KAM.Iso.Sharp

end
