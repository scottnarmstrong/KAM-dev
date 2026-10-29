/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.Constants
public import KAM.Iso.Linear.Extended
public import KAM.Apost.PerturbationTorsion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Part 2 (isoenergetic iteration): differences of the bordered torsion

Helper lemmas for `bpI:p2:torsion` (`KAM.Iso.Apost.torsion_step`), none of
which involves the correction: they compare
the bordered torsion `𝖳 = (T ω; Y 0)` of two tori `K`, `K'` at two frequencies `ω`, `ω'`.

* `torsion_sub_freq`, `norm_torsion_sub_freq_le` (step `to-omega`): the torsion is affine in the
  frequency, `T_{ω'}(K) - T_ω(K) = -Nᵀ Ω₀ ∂_{ω'-ω} N`, bounded by the Cauchy estimate.
* `energyRow_sub`, `sum_norm_energyRow_sub_le`, `norm_fderiv_sub_le_mvt` (step `to-row`):
  `Y' - Y = (DH(K') - DH(K)) N' + DH(K) (N' - N)` and the mean value estimate for `DH`.
* `norm_extendedTorsion_sub_le` (the block estimate of step `to-avg`) and
  `norm_extendedTorsionAverage_sub_le` (the integral bound over `[0,1]ⁿ`).
* `torsion_diff_arith`: the constants `C_{Δ𝖳} = C_ΔT + 8n²𝔪⁴ + 1 + C_Y` dominate the pieces.
-/

@[expose] public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Apost

open KAM KAM.Torus KAM.Apost KAM.Iso.Linear

namespace TorsionDiff

variable {n : ℕ}

/-! ### The bordered matrix: differences and norms -/

theorem bordMat_sub (A A' : Matrix (Fin n) (Fin n) ℂ) (c c' y y' : Fin n → ℂ) :
    bordMat A' c' y' - bordMat A c y = bordMat (A' - A) (c' - c) (y' - y) := by
  ext (a | u) (b | v)
  · rfl
  · rfl
  · rfl
  · simp [bordMat, Matrix.fromBlocks]

/-- A bound for the bordered matrix `(A c; yᵀ 0)`: row sums. -/
theorem norm_bordMat_le (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) {a d e : ℝ}
    (hA : ‖A‖ ≤ a) (hc : ‖c‖ ≤ d) (hy : ∑ b, ‖y b‖ ≤ e) (he : 0 ≤ e) :
    ‖bordMat A c y‖ ≤ max (a + d) e := by
  refine (norm_le_iff_forall_rowSum (le_max_of_le_right he)).2 ?_
  rintro (i | u)
  · rw [Fintype.sum_sum_type]
    simp only [ExtendedAux.bordMat_inl_inl, ExtendedAux.bordMat_inl_inr, Finset.univ_unique,
      Finset.sum_singleton]
    exact ((add_le_add ((rowSum_le_norm A i).trans hA) ((norm_le_pi_norm c i).trans hc)).trans
      (le_max_left _ _))
  · rw [Fintype.sum_sum_type]
    simp only [ExtendedAux.bordMat_inr_inl, ExtendedAux.bordMat_inr_inr, Finset.univ_unique,
      Finset.sum_singleton, norm_zero, add_zero]
    exact hy.trans (le_max_right _ _)

/-! ### The effect of the frequency on the torsion block (step `to-omega`) -/

section Frequency

variable {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- `T_{ω'}(K) - T_ω(K) = -Nᵀ Ω₀ ∂_{ω'-ω} N`: the torsion is affine in the frequency. -/
theorem torsion_sub_freq (ω ω' : Fin n → ℝ) {θ : Fin n → ℂ}
    (hN : DifferentiableAt ℂ (normalMat K) θ) :
    torsion H K ω' θ - torsion H K ω θ =
      -((normalMat K θ)ᵀ * omegaZeroMatrix n *
        fderiv ℂ (normalMat K) θ (fun l => ((ω' - ω) l : ℂ))) := by
  rw [torsion_eq_mat H K ω' hN, torsion_eq_mat H K ω hN, ← Matrix.mul_sub, ← neg_sub,
    ← Matrix.mul_neg]
  congr 2
  have hv : (fun l => (((ω' - ω) l : ℝ) : ℂ)) =
      (fun l => (ω' l : ℂ)) - (fun l => (ω l : ℂ)) := by
    funext l
    simp
  simp only [normalFieldMat, hv, map_sub]
  abel

/-- The Cauchy estimate for `T_{ω'}(K) - T_ω(K)` on `T_{ρ-δ}`, from `‖N‖ ≤ B` on `T_ρ` and
`‖ω' - ω‖ ≤ d`: `‖Nᵀ‖ ≤ 2nB` and `‖∂_{Δω} N‖ ≤ n d δ⁻¹ B`. -/
theorem norm_torsion_sub_freq_le {ρ δ B d : ℝ} (ω ω' : Fin n → ℝ) (hδ : 0 < δ)
    (hNd : DifferentiableOn ℂ (normalMat K) (complexStrip n ρ))
    (hNb : ∀ θ ∈ complexStrip n ρ, ‖normalMat K θ‖ ≤ B) (hω : ‖ω' - ω‖ ≤ d) :
    ∀ θ ∈ complexStrip n (ρ - δ),
      ‖torsion H K ω' θ - torsion H K ω θ‖ ≤ 2 * n * B * (n * d * δ⁻¹ * B) := by
  intro θ hθ
  have hθρ : θ ∈ complexStrip n ρ := Triangular.strip_mono (by linarith) hθ
  have hB : 0 ≤ B := (norm_nonneg _).trans (hNb θ hθρ)
  have hdir := cauchy_corollaries_directional_real hNd hNb hδ (ω' - ω) θ hθ
  have hsum := PerturbationAux.sum_abs_le_of_norm_le (ω := ω' - ω) hω
  have hDN : ‖fderiv ℂ (normalMat K) θ (fun l => ((ω' - ω) l : ℂ))‖ ≤ n * d * δ⁻¹ * B := by
    refine hdir.trans ?_
    have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
    calc (∑ ℓ, |(ω' - ω) ℓ|) * δ⁻¹ * B ≤ (n * d) * δ⁻¹ * B := by gcongr
      _ = n * d * δ⁻¹ * B := rfl
  have hN : DifferentiableAt ℂ (normalMat K) θ :=
    hNd.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθρ)
  rw [torsion_sub_freq ω ω' hN, norm_neg]
  calc ‖(normalMat K θ)ᵀ * omegaZeroMatrix n *
        fderiv ℂ (normalMat K) θ (fun l => ((ω' - ω) l : ℂ))‖
      ≤ ‖(normalMat K θ)ᵀ * omegaZeroMatrix n‖ *
        ‖fderiv ℂ (normalMat K) θ (fun l => ((ω' - ω) l : ℂ))‖ := Matrix.linfty_opNorm_mul _ _
    _ = ‖(normalMat K θ)ᵀ‖ * ‖fderiv ℂ (normalMat K) θ (fun l => ((ω' - ω) l : ℂ))‖ := by
        rw [norm_mul_omegaZeroMatrix]
    _ ≤ (2 * n * B) * (n * d * δ⁻¹ * B) := by
        refine mul_le_mul ((FrameAux.norm_transpose_le_two_mul _).trans ?_) hDN (norm_nonneg _)
          (by positivity)
        gcongr
        exact hNb θ hθρ

end Frequency

/-! ### The energy row (step `to-row`) -/

section EnergyRow

variable {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}

/-- `∑_b |∑_s N_{sb} c_s| ≤ ‖N‖ ∑_s |c_s|`. -/
theorem sum_norm_mul_le {ι : Type*} [Fintype ι] (N : Matrix ι (Fin n) ℂ) (c : ι → ℂ) :
    ∑ b, ‖∑ s, N s b * c s‖ ≤ ‖N‖ * ∑ s, ‖c s‖ := by
  calc ∑ b, ‖∑ s, N s b * c s‖ ≤ ∑ b, ∑ s, ‖N s b‖ * ‖c s‖ :=
        Finset.sum_le_sum fun b _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => (norm_mul _ _).le)
    _ = ∑ s, (∑ b, ‖N s b‖) * ‖c s‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
    _ ≤ ∑ s, ‖N‖ * ‖c s‖ :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (rowSum_le_norm N s) (norm_nonneg _)
    _ = ‖N‖ * ∑ s, ‖c s‖ := (Finset.mul_sum _ _ _).symm

/-- `Y'_b - Y_b = ∑_s (N'_{sb} (∂_sH(K') - ∂_sH(K)) + (N'_{sb} - N_{sb}) ∂_sH(K))`. -/
theorem energyRow_sub (θ : Fin n → ℂ) (b : Fin n) :
    energyRow H K' θ b - energyRow H K θ b =
      ∑ s, (normalMat K' θ s b *
          (fderiv ℂ H (K' θ) - fderiv ℂ H (K θ)) ((sumVec n).symm (Pi.single s 1)) +
        (normalMat K' θ - normalMat K θ) s b *
          fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))) := by
  rw [ExtendedAux.energyRow_apply, ExtendedAux.energyRow_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [_root_.sub_apply, Matrix.sub_apply]
  ring

/-- The row-sum norm of `Y' - Y` from the norms of `N'`, `N' - N`, `DH(K') - DH(K)`, `DH(K)`. -/
theorem sum_norm_energyRow_sub_le (θ : Fin n → ℂ) {B₁ B₂ a b : ℝ}
    (hN' : ‖normalMat K' θ‖ ≤ B₁) (hNN : ‖normalMat K' θ - normalMat K θ‖ ≤ B₂)
    (hφ : ‖fderiv ℂ H (K' θ) - fderiv ℂ H (K θ)‖ ≤ a) (hψ : ‖fderiv ℂ H (K θ)‖ ≤ b) :
    ∑ j, ‖energyRow H K' θ j - energyRow H K θ j‖ ≤ B₁ * a + B₂ * b := by
  have hφs := (ExtendedAux.sum_norm_apply_le_opNorm
    (fderiv ℂ H (K' θ) - fderiv ℂ H (K θ))).trans hφ
  have hψs := (ExtendedAux.sum_norm_apply_le_opNorm (fderiv ℂ H (K θ))).trans hψ
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans hN'
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans hNN
  calc ∑ j, ‖energyRow H K' θ j - energyRow H K θ j‖
      = ∑ j, ‖∑ s, normalMat K' θ s j *
            (fderiv ℂ H (K' θ) - fderiv ℂ H (K θ)) ((sumVec n).symm (Pi.single s 1)) +
          ∑ s, (normalMat K' θ - normalMat K θ) s j *
            fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [energyRow_sub, Finset.sum_add_distrib]
    _ ≤ ∑ j, (‖∑ s, normalMat K' θ s j *
            (fderiv ℂ H (K' θ) - fderiv ℂ H (K θ)) ((sumVec n).symm (Pi.single s 1))‖ +
          ‖∑ s, (normalMat K' θ - normalMat K θ) s j *
            fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖) :=
        Finset.sum_le_sum fun j _ => norm_add_le _ _
    _ = ∑ j, ‖∑ s, normalMat K' θ s j *
            (fderiv ℂ H (K' θ) - fderiv ℂ H (K θ)) ((sumVec n).symm (Pi.single s 1))‖ +
        ∑ j, ‖∑ s, (normalMat K' θ - normalMat K θ) s j *
            fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ := Finset.sum_add_distrib
    _ ≤ ‖normalMat K' θ‖ * ∑ s, ‖(fderiv ℂ H (K' θ) - fderiv ℂ H (K θ))
              ((sumVec n).symm (Pi.single s 1))‖ +
        ‖normalMat K' θ - normalMat K θ‖ * ∑ s, ‖fderiv ℂ H (K θ)
              ((sumVec n).symm (Pi.single s 1))‖ :=
        add_le_add (sum_norm_mul_le _ _) (sum_norm_mul_le _ _)
    _ ≤ B₁ * a + B₂ * b :=
        add_le_add (mul_le_mul hN' hφs (Finset.sum_nonneg fun _ _ => norm_nonneg _) hB₁)
          (mul_le_mul hNN hψs (Finset.sum_nonneg fun _ _ => norm_nonneg _) hB₂)

/-- The mean value estimate `‖DH(z + w) - DH(z)‖ ≤ M ‖w‖` (segment in a ball inside the open
domain `D`, where `‖D²H‖ ≤ M`). -/
theorem norm_fderiv_sub_le_mvt {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hH : DifferentiableOn ℂ H D) {M : ℝ}
    (hM : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ M) {z w : (Fin n → ℂ) × (Fin n → ℂ)} {β : ℝ}
    (hball : Metric.ball z β ⊆ D) (hw : ‖w‖ < β) :
    ‖fderiv ℂ H (z + w) - fderiv ℂ H z‖ ≤ M * ‖w‖ := by
  have hβ : 0 < β := lt_of_le_of_lt (norm_nonneg w) hw
  have hzw : z + w ∈ Metric.ball z β := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hseg : segment ℝ z (z + w) ⊆ Metric.ball z β :=
    (convex_ball z β).segment_subset (Metric.mem_ball_self hβ) hzw
  exact increments_open (Metric.isOpen_ball (x := z) (ε := β))
    ((differentiableOn_fderiv_of_isOpen hD hH).mono hball) (A := M)
    (fun x hx => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℂ), norm_iteratedFDeriv_fderiv]
      exact hM x (hball hx)) hseg

end EnergyRow

/-! ### The bordered torsion and its average -/

section Average

variable {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K K' : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
  {ω ω' : Fin n → ℝ}

/-- The block estimate of step `to-avg`, pointwise: if `‖T' - T‖ ≤ a`, `‖ω' - ω‖ ≤ d` and
`∑ |Y' - Y| ≤ e` at `θ`, then `‖𝖳' - 𝖳‖ ≤ max {a + d, e}`. -/
theorem norm_extendedTorsion_sub_le (θ : Fin n → ℂ) {a d e : ℝ}
    (hT : ‖torsion H K' ω' θ - torsion H K ω θ‖ ≤ a) (hω : ‖ω' - ω‖ ≤ d)
    (hY : ∑ j, ‖energyRow H K' θ j - energyRow H K θ j‖ ≤ e) :
    ‖KAM.Iso.extendedTorsion H K' ω' θ - KAM.Iso.extendedTorsion H K ω θ‖ ≤ max (a + d) e := by
  rw [extendedTorsion_eq_bordMat, extendedTorsion_eq_bordMat, bordMat_sub]
  refine norm_bordMat_le _ _ _ hT ?_ hY ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hY)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hω)).2 fun i => ?_
  have h1 : ‖(((ω' i : ℝ) : ℂ)) - ((ω i : ℝ) : ℂ)‖ = |ω' i - ω i| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  show ‖(((ω' i : ℝ) : ℂ)) - ((ω i : ℝ) : ℂ)‖ ≤ d
  rw [h1]
  exact (norm_le_pi_norm (ω' - ω) i).trans hω

/-- A matrix-valued continuous function on `ℝⁿ` has the entrywise average as its (Bochner) average,
for any finite index types. -/
theorem torusAverage_matrix_apply_fintype {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [DecidableEq κ] {M : (Fin n → ℝ) → Matrix ι κ ℂ} (hM : Continuous M) (i : ι) (j : κ) :
    torusAverage M i j =
      ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), M x i j := by
  let L : Matrix ι κ ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact (L.integral_comp_comm (μ := volume.restrict (Set.pi Set.univ
    fun _ : Fin n => Set.Icc (0 : ℝ) 1)) (φ := M) (integrableOn_unitCube_of_continuous hM)).symm

/-- The integral bound for the averages of the bordered torsion (`bp:p1:ext-integral`): if the
continuous tori `𝖳'`, `𝖳` differ by at most `A` on `ℝⁿ`, then `‖⟨𝖳'⟩ - ⟨𝖳⟩‖ ≤ A`. -/
theorem norm_extendedTorsionAverage_sub_le {A : ℝ}
    (hc : Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))))
    (hc' : Continuous (fun x : Fin n → ℝ =>
      KAM.Iso.extendedTorsion H K' ω' (fun i => (x i : ℂ))))
    (hb : ∀ x : Fin n → ℝ, ‖KAM.Iso.extendedTorsion H K' ω' (fun i => (x i : ℂ)) -
      KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))‖ ≤ A) :
    ‖KAM.Iso.extendedTorsionAverage H K' ω' - KAM.Iso.extendedTorsionAverage H K ω‖ ≤ A := by
  have heq : KAM.Iso.extendedTorsionAverage H K' ω' - KAM.Iso.extendedTorsionAverage H K ω =
      torusAverage (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K' ω' (fun i => (x i : ℂ)) -
        KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) := by
    ext i j
    have hF : Continuous (fun x : Fin n → ℝ =>
        KAM.Iso.extendedTorsion H K' ω' (fun i => (x i : ℂ)) -
          KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) := hc'.sub hc
    rw [torusAverage_matrix_apply_fintype hF i j, Matrix.sub_apply]
    simp only [Matrix.sub_apply]
    exact (integral_sub (integrableOn_unitCube_of_continuous (hc'.matrix_elem i j))
      (integrableOn_unitCube_of_continuous (hc.matrix_elem i j))).symm
  rw [heq]
  exact norm_torusAverage_le fun x _ => hb x

end Average

/-! ### The constants -/

section Arith

variable {τ M σK σB σT : ℝ}

/-- The pieces of step `to-avg` are dominated by `C_{Δ𝖳} d/δ²` (`δ ≤ 1`). -/
theorem torsion_diff_arith (hP : Params n τ M σK σB σT) {δ d : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 ≤ d) :
    max (C_DT n M σK σB σT * d / δ ^ 2 + 8 * n ^ 2 * mSize M σK σB σT ^ 4 * d / δ + d)
        (CY n M σK σB σT * d / δ) ≤ CDTbord n M σK σB σT * d / δ ^ 2 := by
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ 2
  have hδδ : δ ^ 2 ≤ δ := by nlinarith
  have h1 : d / δ ≤ d / δ ^ 2 := div_le_div_of_nonneg_left hd hδ2 hδδ
  have h2 : d ≤ d / δ ^ 2 := by
    rw [le_div_iff₀ hδ2]
    nlinarith
  have hCY : 0 ≤ CY n M σK σB σT := zero_le_one.trans (one_le_CY hP)
  have hDT : 0 ≤ C_DT n M σK σB σT := zero_le_one.trans (one_le_C_DT hP)
  have h8 : 0 ≤ 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 := by positivity
  have hq : 0 ≤ d / δ ^ 2 := div_nonneg hd hδ2.le
  have e1 : CDTbord n M σK σB σT * d / δ ^ 2 =
      (C_DT n M σK σB σT + 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 + 1 + CY n M σK σB σT) *
        (d / δ ^ 2) := by
    unfold CDTbord
    ring
  have e2 : C_DT n M σK σB σT * d / δ ^ 2 = C_DT n M σK σB σT * (d / δ ^ 2) := by ring
  have e3 : 8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * d / δ =
      8 * (n : ℝ) ^ 2 * mSize M σK σB σT ^ 4 * (d / δ) := by ring
  have e4 : CY n M σK σB σT * d / δ = CY n M σK σB σT * (d / δ) := by ring
  rw [e1, e2, e3, e4]
  refine max_le ?_ ?_
  · nlinarith [mul_le_mul_of_nonneg_left h1 h8, mul_nonneg hCY hq]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hCY, mul_nonneg hDT hq, mul_nonneg h8 hq]

/-- The energy-row estimate of step `to-row`: `2𝔪² (M d) + (C_ΔN d/δ) M ≤ C_Y d/δ`
(`M ≤ 𝔪`, `n ≥ 1`, `δ ≤ 1`). -/
theorem energy_row_arith (hP : Params n τ M σK σB σT) {δ d : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hd : 0 ≤ d) :
    2 * mSize M σK σB σT ^ 2 * (M * d) + C_DN n M σK σB σT * d / δ * M ≤
      CY n M σK σB σT * d / δ := by
  have hM : M ≤ mSize M σK σB σT := M_le_mSize
  have hM0 : 0 ≤ M := hP.M_pos.le
  have hm : 1 ≤ mSize M σK σB σT := one_le_mSize
  have hn := hP.one_le_cast
  have hDN : 0 ≤ C_DN n M σK σB σT := zero_le_one.trans (one_le_C_DN hP)
  have hp : 0 ≤ d / δ := div_nonneg hd hδ.le
  have h1 : d ≤ d / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have e1 : C_DN n M σK σB σT * d / δ * M = C_DN n M σK σB σT * M * (d / δ) := by ring
  have e2 : CY n M σK σB σT * d / δ =
      n * mSize M σK σB σT * (2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT) * (d / δ) := by
    unfold CY
    ring
  rw [e1, e2]
  have hm0 : 0 ≤ mSize M σK σB σT := zero_le_one.trans hm
  have h2 : 2 * mSize M σK σB σT ^ 2 * (M * d) ≤ 2 * mSize M σK σB σT ^ 2 * M * (d / δ) := by
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * mSize M σK σB σT ^ 2 * M)
    nlinarith
  have h3 : 2 * mSize M σK σB σT ^ 2 * M * (d / δ) + C_DN n M σK σB σT * M * (d / δ) ≤
      n * mSize M σK σB σT * (2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT) * (d / δ) := by
    have hnm : mSize M σK σB σT ≤ n * mSize M σK σB σT := by nlinarith
    have hc : 0 ≤ 2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT := by positivity
    calc 2 * mSize M σK σB σT ^ 2 * M * (d / δ) + C_DN n M σK σB σT * M * (d / δ)
        = (2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT) * M * (d / δ) := by ring
      _ ≤ (2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT) * mSize M σK σB σT * (d / δ) := by
          gcongr
      _ ≤ (2 * mSize M σK σB σT ^ 2 + C_DN n M σK σB σT) * (n * mSize M σK σB σT) * (d / δ) := by
          gcongr
      _ = _ := by ring
  linarith

end Arith

end TorsionDiff

end KAM.Iso.Apost
