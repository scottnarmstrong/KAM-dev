/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.Hybrid.Frames
public import KAM.Sharp2.RouteA.Torsion
public import KAM.Frozen.Iso.Defs.ExtendedTorsionAverage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The torsion of the new torus (`bp:p2s2hc:torsion`, `bpI:p2s2hc:torsion`)

The torsion is compared through the torsion polynomial `T = 𝒯_ab + local part`, so no derivative of
a frame enters.

* `dAB`, `torsionAB_step_sub_le`: the frame part, by a triple telescoping;
* `norm_hamComm_sub_le_M2`: `|Δ(A Ω₀ - Ω₀ A)| ≤ 2 M₂ |Δz|` with `M₂` in place of the frozen `M`
  (`KAM.Sharp2.norm_hamComm_sub_le` is stated with `Standing`'s `M`);
* `torsion_step_le`: the two sup forms and the increment;
* `torsionAverage_step`: Neumann against the initial average. The proof takes `neumann_ratio`
  directly, so `t_A = 0` is not a separate case (`KAM.Sharp2.inv_le_of_ref` needs `m < σ`);
* `extTorsionAverage_step`: the bordered torsion, by the same Neumann step;
* `sum_norm_lastRow_step_le`: the last row of the bordered increment, through the transposes.

The averages are entrywise integrals; `norm_sub_of_rows` bounds their difference row by row, from a
pointwise bound of the row sums. The integrability hypotheses are discharged by
`KAM/Sharp2/Hybrid/Integrable.lean`, from holomorphy.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Sharp2.Hybrid

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

variable {n : ℕ}

/-- `Δ_ab` of Lemma `bp:p2s2hc:torsion`(a). -/
def dAB (F : FrameNum) (cTh cDTh d : ℝ) : ℝ :=
  F.nΔt * cTh * (F.ν + F.nΔ) + F.νt * (cDTh * d) * (F.ν + F.nΔ) + F.νt * cTh * F.nΔ

/-- `|Δ(A Ω₀ - Ω₀ A)| ≤ 2 M₂ |Δz|` on a segment in `𝔅`, from `|D²X_h| ≤ M₂` on `𝔅`. -/
theorem norm_hamComm_sub_le_M2 {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {M₂ : ℝ} (hopen : IsOpen 𝔅)
    (hdiff : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) 𝔅)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M₂)
    {z z' : (Fin n → ℂ) × (Fin n → ℂ)} (hseg : segment ℝ z z' ⊆ 𝔅) :
    ‖hamComm h z - hamComm h z'‖ ≤ 2 * M₂ * ‖z - z'‖ := by
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (f := fderiv ℂ (hamiltonianVectorFieldℂ h)) (s := segment ℝ z' z)
    (fun x hx => hdiff.differentiableAt (hopen.mem_nhds (hseg (segment_symm ℝ z z' ▸ hx))))
    (fun x hx => by
      rw [norm_fderiv_fderiv_eq]
      exact hd2 x (hseg (segment_symm ℝ z z' ▸ hx)))
    (convex_segment z' z) (left_mem_segment ℝ z' z) (right_mem_segment ℝ z' z)
  have e : hamComm h z - hamComm h z' =
      sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z - fderiv ℂ (hamiltonianVectorFieldℂ h) z') *
          omegaZeroMatrix n -
        omegaZeroMatrix n *
          sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z -
            fderiv ℂ (hamiltonianVectorFieldℂ h) z') := by
    rw [PerturbationAux.sqMat_sub]
    unfold hamComm
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul, norm_sqMat]
  linarith

/-- `norm_hamComm_sub_le_M2` along the step: `|ΔK| ≤ d`, `|ΔK| < μ` and `𝔹_μ(K θ) ⊆ 𝔅`. -/
theorem norm_hamComm_step_le {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} {M₂ μ d : ℝ} (hopen : IsOpen 𝔅)
    (hdiff : DifferentiableOn ℂ (fderiv ℂ (hamiltonianVectorFieldℂ h)) 𝔅)
    (hd2 : ∀ z ∈ 𝔅, ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ h) z‖ ≤ M₂)
    (hball : Metric.ball (K θ) μ ⊆ 𝔅) (hd : ‖ΔK θ‖ ≤ d) (hdμ : ‖ΔK θ‖ < μ) (hM : 0 ≤ M₂) :
    ‖hamComm h ((K + ΔK) θ) - hamComm h (K θ)‖ ≤ 2 * M₂ * d := by
  have hseg := segment_add_subset hball hdμ
  rw [segment_symm] at hseg
  refine (norm_hamComm_sub_le_M2 hopen hdiff hd2 hseg).trans ?_
  simp only [add_sub_cancel_left]
  exact mul_le_mul_of_nonneg_left hd (by positivity)

/-- Lemma `bp:p2s2hc:torsion`(a), the frame part (pointwise; `KAM.Sharp2.torsionAB`). -/
theorem torsionAB_step_sub_le {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ} {F : FrameNum}
    {cTh cDTh d : ℝ} (hG : IsUnit (gramMatrix K θ).det)
    (hG₁ : IsUnit (gramMatrix (K + ΔK) θ).det) (hN : ‖normalMat K θ‖ ≤ F.ν)
    (hNt : ‖(normalMat K θ)ᵀ‖ ≤ F.νt) (hdN : ‖normalMat (K + ΔK) θ - normalMat K θ‖ ≤ F.nΔ)
    (hdNt : ‖(normalMat (K + ΔK) θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ F.nΔt)
    (hc : ‖hamComm h (K θ)‖ ≤ cTh) (hc₁ : ‖hamComm h ((K + ΔK) θ)‖ ≤ cTh)
    (hcd : ‖hamComm h ((K + ΔK) θ) - hamComm h (K θ)‖ ≤ cDTh * d) :
    ‖torsionAB h (K + ΔK) θ - torsionAB h K θ‖ ≤ dAB F cTh cDTh d := by
  have _hG := hG
  have _hG₁ := hG₁
  rw [TorsionRef.torsionAB_eq_triple, TorsionRef.torsionAB_eq_triple]
  refine (RouteA.triple_sub_le _ _ _ _ _ _).trans ?_
  set K₁ := K + ΔK
  have hdX : ‖(gramMatrix K₁ θ)⁻¹ * (tangentMat K₁ θ)ᵀ - (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ ≤
      F.nΔt := by
    have := hdNt
    rwa [← norm_mul_omegaZeroMatrix, Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
      TorsionPoly.normalMat_transpose_mul_omega] at this
  have hdZ : ‖tangentMat K₁ θ * (gramMatrix K₁ θ)⁻¹ - tangentMat K θ * (gramMatrix K θ)⁻¹‖ ≤
      F.nΔ := by
    have := hdN
    rw [← norm_omegaZeroMatrix_mul, Matrix.mul_sub]
    simpa only [normalMat, Matrix.mul_assoc] using this
  have hX : ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ ≤ F.νt := by
    rw [TorsionRef.norm_B_Lt]; exact hNt
  have hZ : ‖tangentMat K₁ θ * (gramMatrix K₁ θ)⁻¹‖ ≤ F.ν + F.nΔ := by
    rw [TorsionRef.norm_L_B]; exact norm_le_add_of_sub hN hdN
  have h0X := (norm_nonneg _).trans hX
  have h0dX := (norm_nonneg _).trans hdX
  have h0c := (norm_nonneg _).trans hc
  have h0cd := (norm_nonneg _).trans hcd
  have t1 := mul_le_mul (mul_le_mul hdX hc₁ (norm_nonneg _) h0dX) hZ (norm_nonneg _)
    (mul_nonneg h0dX h0c)
  have t2 := mul_le_mul (mul_le_mul hX hcd (norm_nonneg _) h0X) hZ (norm_nonneg _)
    (mul_nonneg h0X h0cd)
  have t3 := mul_le_mul (mul_le_mul hX hc (norm_nonneg _) h0X) hdZ (norm_nonneg _)
    (mul_nonneg h0X h0c)
  exact add_le_add (add_le_add t1 t2) t3

/-- Lemma `bp:p2s2hc:torsion`(c) (pointwise): the two sup forms and the increment. The local parts
`l₀`, `l₁` come from `KAM.Sharp2.norm_torsion_sub_torsionAB_le` at `K` (frequency `ω`) and at `K₁`
(frequency `ω₁`; `ω₁ = ω` at fixed frequency, `s₁ ω*` against `s ω*` in the iso form: the frame
part `𝒯_ab` does not depend on the frequency). -/
theorem torsion_step_le {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω ω₁ : Fin n → ℝ} {θ : Fin n → ℂ}
    {t dab l₀ l₁ a₁ : ℝ} (hT : ‖torsion h K ω θ‖ ≤ t)
    (hab : ‖torsionAB h (K + ΔK) θ - torsionAB h K θ‖ ≤ dab)
    (hab₁ : ‖torsionAB h (K + ΔK) θ‖ ≤ a₁)
    (hl₀ : ‖torsion h K ω θ - torsionAB h K θ‖ ≤ l₀)
    (hl₁ : ‖torsion h (K + ΔK) ω₁ θ - torsionAB h (K + ΔK) θ‖ ≤ l₁) :
    ‖torsion h (K + ΔK) ω₁ θ‖ ≤ min (t + dab + l₀) a₁ + l₁ ∧
      ‖torsion h (K + ΔK) ω₁ θ - torsion h K ω θ‖ ≤ dab + l₀ + l₁ := by
  set T := torsion h K ω θ
  set T₁ := torsion h (K + ΔK) ω₁ θ
  set A := torsionAB h K θ
  set A₁ := torsionAB h (K + ΔK) θ
  have hA : ‖A‖ ≤ t + l₀ := by
    have e : A = T - (T - A) := by abel
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add hT hl₀)
  have hA₁ : ‖A₁‖ ≤ t + dab + l₀ := by
    have := norm_le_add_of_sub (X := A) (Y := A₁) hA hab
    linarith
  constructor
  · have e : T₁ = A₁ + (T₁ - A₁) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add (le_min hA₁ hab₁) hl₁)
  · have e : T₁ - T = (A₁ - A) - (T - A) + (T₁ - A₁) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hab hl₀)) hl₁)

/-- `∑ⱼ |∫ fⱼ| ≤ S` on the unit cube when `∑ⱼ |fⱼ| ≤ S` pointwise. -/
theorem sum_norm_integral_le {ι : Type*} [Fintype ι] {f : (Fin n → ℝ) → ι → ℂ} {S : ℝ}
    (hf : ∀ j, IntegrableOn (fun x => f x j) (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hS : ∀ x, ∑ j, ‖f x j‖ ≤ S) :
    ∑ j, ‖∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), f x j‖ ≤ S :=
  calc ∑ j, ‖∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), f x j‖
      ≤ ∑ j, ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), ‖f x j‖ :=
        Finset.sum_le_sum fun _ _ => norm_integral_le_integral_norm _
    _ = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), ∑ j, ‖f x j‖ :=
        (integral_finsetSum _ fun j _ => (hf j).norm).symm
    _ ≤ S := (Real.le_norm_self _).trans (norm_torusAverage_le fun x _ => by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact hS x)

/-- The row sums are at most the norm. -/
theorem sum_norm_row_le {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) (i : ι) :
    ∑ j, ‖M i j‖ ≤ ‖M‖ :=
  (norm_le_iff_forall_rowSum (norm_nonneg _)).1 le_rfl i

/-- The difference of two entrywise averages, from a pointwise bound of the row sums
(`step:p2s2hc:to-avg`, and the blocks of `stepI:p2s2hc:bl`). -/
theorem norm_sub_of_rows {ι κ : Type*} [Fintype ι] [Fintype κ] {A B : Matrix ι κ ℂ}
    {a b : (Fin n → ℝ) → Matrix ι κ ℂ} {S : ℝ} (hS0 : 0 ≤ S)
    (hA : ∀ i j, A i j = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), a x i j)
    (hB : ∀ i j, B i j = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), b x i j)
    (ha : ∀ i j, IntegrableOn (fun x => a x i j) (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hb : ∀ i j, IntegrableOn (fun x => b x i j) (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hS : ∀ x i, ∑ j, ‖a x i j - b x i j‖ ≤ S) : ‖A - B‖ ≤ S := by
  refine (norm_le_iff_forall_rowSum hS0).2 fun i => ?_
  have e : ∀ j, (A - B) i j =
      ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), (a x i j - b x i j) :=
    fun j => by rw [Matrix.sub_apply, hA, hB, integral_sub (ha i j) (hb i j)]
  simp only [e]
  exact sum_norm_integral_le (f := fun x j => a x i j - b x i j)
    (fun j => (ha i j).sub (hb i j)) fun x => hS x i

/-- The Neumann step of the averages: `|A₀⁻¹| ≤ m`, `|A - A₀| ≤ t`, `m t < 1`. -/
theorem neumann_step {ι : Type*} [Fintype ι] [DecidableEq ι] {A A0 : Matrix ι ι ℂ} {m t : ℝ}
    (hu : IsUnit A0.det) (hm : ‖A0⁻¹‖ ≤ m) (hm0 : 0 < m) (ht : ‖A - A0‖ ≤ t) (hmt : m * t < 1) :
    IsUnit A.det ∧ ‖A⁻¹‖ ≤ m / (1 - m * t) := by
  have hsmall : ‖A0⁻¹‖ * ‖A - A0‖ ≤ m * t := mul_le_mul hm ht (norm_nonneg _) hm0.le
  obtain ⟨hU, hBn, -⟩ := neumann_ratio ((Matrix.isUnit_iff_isUnit_det _).2 hu) hmt hsmall
  rw [add_sub_cancel] at hU hBn
  exact ⟨(Matrix.isUnit_iff_isUnit_det _).1 hU,
    hBn.trans (div_le_div_of_nonneg_right hm (by linarith))⟩

/-- Lemma `bp:p2s2hc:torsion`(d): Neumann against the initial average (`inv_le_of_ref`). -/
theorem torsionAverage_step {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {m tA : ℝ}
    (hint : ∀ i j, IntegrableOn (fun θ : Fin n → ℝ => torsion h K ω (fun l => (θ l : ℂ)) i j)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hint₁ : ∀ i j, IntegrableOn (fun θ : Fin n → ℝ => torsion h K₁ ω (fun l => (θ l : ℂ)) i j)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hd : ∀ θ : Fin n → ℝ,
      ‖torsion h K₁ ω (fun l => (θ l : ℂ)) - torsion h K ω (fun l => (θ l : ℂ))‖ ≤ tA)
    (hu : IsUnit (torsionAverage h K ω).det) (hm : ‖(torsionAverage h K ω)⁻¹‖ ≤ m)
    (hm0 : 0 < m) (htA : 0 ≤ tA) (hmt : m * tA < 1) :
    IsUnit (torsionAverage h K₁ ω).det ∧ ‖(torsionAverage h K₁ ω)⁻¹‖ ≤ m / (1 - m * tA) :=
  neumann_step hu hm hm0 (norm_sub_of_rows htA (fun _ _ => rfl) (fun _ _ => rfl) hint₁ hint
    fun x i => (sum_norm_row_le _ i).trans (hd x)) hmt

/-- Lemma `bpI:p2s2hc:torsion`: the bordered torsion of the new torus at `s₁ ω*`, by Neumann
against `⟨T^ext⟩` of `K` at `s ω*`; `tA` bounds the torsion increment, `y` the last-row increment
`DH(K₁)N₁ - DH(K)N` at real points, `dω` the change of the frequency. -/
theorem extTorsionAverage_step {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ωstar : Fin n → ℝ} {s s₁ m tA y dω : ℝ}
    (hint : ∀ i j, IntegrableOn
      (fun θ : Fin n → ℝ => torsion H K (s • ωstar) (fun l => (θ l : ℂ)) i j)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hint₁ : ∀ i j, IntegrableOn
      (fun θ : Fin n → ℝ => torsion H K₁ (s₁ • ωstar) (fun l => (θ l : ℂ)) i j)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hintY : ∀ j, IntegrableOn (fun θ : Fin n → ℝ =>
      fderiv ℂ H (K fun l => (θ l : ℂ)) (normalFrame K (fun l => (θ l : ℂ)) j))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hintY₁ : ∀ j, IntegrableOn (fun θ : Fin n → ℝ =>
      fderiv ℂ H (K₁ fun l => (θ l : ℂ)) (normalFrame K₁ (fun l => (θ l : ℂ)) j))
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1))
    (hd : ∀ θ : Fin n → ℝ, ‖torsion H K₁ (s₁ • ωstar) (fun l => (θ l : ℂ)) -
      torsion H K (s • ωstar) (fun l => (θ l : ℂ))‖ ≤ tA)
    (hy : ∀ θ : Fin n → ℝ, ∑ j, ‖fderiv ℂ H (K₁ fun l => (θ l : ℂ))
      (normalFrame K₁ (fun l => (θ l : ℂ)) j) -
        fderiv ℂ H (K fun l => (θ l : ℂ)) (normalFrame K (fun l => (θ l : ℂ)) j)‖ ≤ y)
    (hdω : ‖s₁ • ωstar - s • ωstar‖ ≤ dω)
    (hu : IsUnit (KAM.Iso.extendedTorsionAverage H K (s • ωstar)).det)
    (hm : ‖(KAM.Iso.extendedTorsionAverage H K (s • ωstar))⁻¹‖ ≤ m) (hm0 : 0 < m)
    (hmt : m * max (tA + dω) y < 1) (htA : 0 ≤ tA) :
    IsUnit (KAM.Iso.extendedTorsionAverage H K₁ (s₁ • ωstar)).det ∧
      ‖(KAM.Iso.extendedTorsionAverage H K₁ (s₁ • ωstar))⁻¹‖ ≤
        m / (1 - m * max (tA + dω) y) := by
  have hdω0 : 0 ≤ dω := (norm_nonneg _).trans hdω
  have hc : ∀ c : ℂ, IntegrableOn (fun _ : Fin n → ℝ => c)
      (Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1) := fun c =>
    integrableOn_unitCube_of_continuous continuous_const
  refine neumann_step hu hm hm0 ?_ hmt
  refine norm_sub_of_rows (le_max_of_le_left (add_nonneg htA hdω0)) (fun _ _ => rfl)
    (fun _ _ => rfl) ?_ ?_ ?_
  · rintro (a | u) (b | v)
    · exact hint₁ a b
    · exact hc _
    · exact hintY₁ b
    · exact hc 0
  · rintro (a | u) (b | v)
    · exact hint a b
    · exact hc _
    · exact hintY b
    · exact hc 0
  · intro x i
    rw [Fintype.sum_sum_type]
    rcases i with a | u
    · refine le_max_of_le_left (add_le_add ((sum_norm_row_le _ a).trans (hd x)) ?_)
      simp only [Finset.univ_unique, Finset.sum_singleton]
      show ‖((s₁ • ωstar) a : ℂ) - ((s • ωstar) a : ℂ)‖ ≤ dω
      rw [← Complex.ofReal_sub, Complex.norm_real]
      exact (norm_le_pi_norm (s₁ • ωstar - s • ωstar) a).trans hdω
    · refine le_max_of_le_right ?_
      have h0 : ∑ _b : Unit, ‖(0 : ℂ) - 0‖ = 0 := by simp
      rw [show (∑ b : Unit, ‖KAM.Iso.extendedTorsion H K₁ (s₁ • ωstar) (fun l => (x l : ℂ))
          (Sum.inr u) (Sum.inr b) - KAM.Iso.extendedTorsion H K (s • ωstar)
          (fun l => (x l : ℂ)) (Sum.inr u) (Sum.inr b)‖) = ∑ _b : Unit, ‖(0 : ℂ) - 0‖ from rfl,
        h0, add_zero]
      exact hy x

/-- A column of `M` is at most `‖Mᵀ‖` in the max norm. -/
theorem norm_col_le {κ : Type*} [Fintype κ] (M : Matrix (Fin n ⊕ Fin n) κ ℂ) (j : κ) :
    ‖fun s => M s j‖ ≤ ‖Mᵀ‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun s => ?_
  calc ‖M s j‖ ≤ ∑ s', ‖Mᵀ j s'‖ :=
        Finset.single_le_sum (f := fun s' => ‖Mᵀ j s'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ s)
    _ ≤ ‖Mᵀ‖ := sum_norm_row_le _ j

/-- The `j`-th column of `N`, as the frozen normal frame: `|Ne_j| ≤ |Nᵀ|`. -/
theorem norm_normalFrame_le (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (j : Fin n) : ‖normalFrame K θ j‖ ≤ ‖(normalMat K θ)ᵀ‖ := by
  rw [← norm_sumVec, sumVec_normalFrame]
  exact norm_col_le _ j

/-- `|N₁e_j - Ne_j| ≤ |N₁ᵀ - Nᵀ|`. -/
theorem norm_normalFrame_sub_le (K K₁ : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ)
    (j : Fin n) :
    ‖normalFrame K₁ θ j - normalFrame K θ j‖ ≤ ‖(normalMat K₁ θ)ᵀ - (normalMat K θ)ᵀ‖ := by
  rw [← norm_sumVec, map_sub, sumVec_normalFrame, sumVec_normalFrame, ← Matrix.transpose_sub]
  exact norm_col_le (normalMat K₁ θ - normalMat K θ) j

/-- The last row of the bordered increment (`stepI:p2s2hc:bl`), through the transposes: a sum over
the columns `v_j` of a linear form applied to them is at most `n |ℓ| |Xᵀ|`. -/
theorem sum_norm_lastRow_step_le {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K ΔK : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {θ : Fin n → ℂ} {μ Mh1 Mh2 d nt νt : ℝ} (hopen : IsOpen D) (hH : DifferentiableOn ℂ H D)
    (hd1 : ∀ z ∈ D, ‖fderiv ℂ H z‖ ≤ Mh1) (hd2 : ∀ z ∈ D, ‖iteratedFDeriv ℂ 2 H z‖ ≤ Mh2)
    (hball : Metric.ball (K θ) μ ⊆ D) (hd : ‖ΔK θ‖ ≤ d) (hdμ : ‖ΔK θ‖ < μ)
    (hdNt : ‖(normalMat (K + ΔK) θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ nt)
    (hNt₁ : ‖(normalMat (K + ΔK) θ)ᵀ‖ ≤ νt + nt) :
    ∑ j, ‖fderiv ℂ H ((K + ΔK) θ) (normalFrame (K + ΔK) θ j) -
      fderiv ℂ H (K θ) (normalFrame K θ j)‖ ≤ n * (Mh1 * nt + Mh2 * d * (νt + nt)) := by
  have hμ : 0 < μ := (norm_nonneg _).trans_lt hdμ
  have hKD : K θ ∈ D := hball (Metric.mem_ball_self hμ)
  have hM1 : 0 ≤ Mh1 := (norm_nonneg _).trans (hd1 _ hKD)
  have hM2 : 0 ≤ Mh2 := (norm_nonneg _).trans (hd2 _ hKD)
  have hseg := segment_add_subset hball hdμ
  have hA : ∀ x ∈ D, ‖fderiv ℂ (fderiv ℂ H) x‖ ≤ Mh2 := fun x hx => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℂ), norm_iteratedFDeriv_fderiv]
    exact hd2 x hx
  have hlip := taylor_lipschitz hopen hH hA hseg (t := 1) ⟨zero_le_one, le_rfl⟩
  rw [one_smul, mul_one] at hlip
  have hrow : ∀ j, ‖fderiv ℂ H ((K + ΔK) θ) (normalFrame (K + ΔK) θ j) -
      fderiv ℂ H (K θ) (normalFrame K θ j)‖ ≤ Mh1 * nt + Mh2 * d * (νt + nt) := fun j => by
    set v := normalFrame K θ j
    set v₁ := normalFrame (K + ΔK) θ j
    set A := fderiv ℂ H (K θ)
    set A₁ := fderiv ℂ H ((K + ΔK) θ)
    have e : A₁ v₁ - A v = A (v₁ - v) + (A₁ - A) v₁ := by
      rw [map_sub, _root_.sub_apply]
      ring
    have hv : ‖v₁ - v‖ ≤ nt := (norm_normalFrame_sub_le K (K + ΔK) θ j).trans hdNt
    have hv₁ : ‖v₁‖ ≤ νt + nt := (norm_normalFrame_le (K + ΔK) θ j).trans hNt₁
    have hdA : ‖A₁ - A‖ ≤ Mh2 * d :=
      hlip.trans (mul_le_mul_of_nonneg_left hd hM2)
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (A.le_opNorm _).trans (mul_le_mul (hd1 _ hKD) hv (norm_nonneg _) hM1)
    · exact ((A₁ - A).le_opNorm _).trans
        (mul_le_mul hdA hv₁ (norm_nonneg _) ((norm_nonneg _).trans hdA))
  calc _ ≤ ∑ _j : Fin n, (Mh1 * nt + Mh2 * d * (νt + nt)) :=
        Finset.sum_le_sum fun j _ => hrow j
    _ = n * (Mh1 * nt + Mh2 * d * (νt + nt)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end KAM.Sharp2.Hybrid

end
