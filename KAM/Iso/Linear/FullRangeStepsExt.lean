/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.FullRange

/-!
# Part 1 step exports: the extended torsion and the last row (graph gap GAP-I1b)

Literal exports of the proof-step nodes of `bpI:p1:extended-basic` (`eb-*`) and `bpI:p1:last-row`
(`lr-gradient`, `lr-average`), each under the source setting `SettingSrc` (`τ ≥ 0`) and built
from landed declarations; nothing is re-proved. Hypotheses beyond the setting are those of the
step; a step that only reads holomorphy of `K` does not assume `K` primary or real.

* `step_eb_holo`, `step_eb_holo_inverse`, `step_eb_holo_field`, `step_eb_holo_torsion`,
  `step_eb_holo_conclude`, `step_eb_period`, `step_eb_average`, `step_eb_bounds`;
* `step_lr_gradient`, `step_lr_average`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost ExtendedAux

variable {n : ℕ} {τ M γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}

/-- `bpI:p1:extended-basic`, step `eb-holo`: `N`, `T`, `Y` and every entry of `𝖳_H` are
holomorphic on `T_r`, in particular continuous on `ℝⁿ`. Only holomorphy of `K`, `K(T_r) ⊆ D` and
`det G ≠ 0` are used. -/
theorem step_eb_holo (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (normalMat K) (complexStrip n r) ∧
    DifferentiableOn ℂ (torsion H K ω) (complexStrip n r) ∧
    DifferentiableOn ℂ (energyRow H K) (complexStrip n r) ∧
    (∀ i j, DifferentiableOn ℂ (fun θ => KAM.Iso.extendedTorsion H K ω θ i j)
      (complexStrip n r)) ∧
    Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) := by
  have hSt := (hS.setting one_pos one_pos one_pos).toStanding
  obtain ⟨hY, hE, hc⟩ := extended_regular hSt hr hK hKD hG ω
  have hN := differentiableOn_normalMat hK hG
  have hA := FrameAux.differentiableOn_linMat hSt hK hKD
  exact ⟨hN, FrameAux.differentiableOn_torsion hN
    (FrameAux.differentiableOn_normalFieldMat hA hN), hY, differentiableOn_matrix_iff_entries.1 hE,
    hc⟩

/-- `bpI:p1:extended-basic`, step `eb-holo-inverse`: `B = G⁻¹`, `N = Ω₀ L B` and `P = (L N)` are
holomorphic on `T_r`. -/
theorem step_eb_holo_inverse (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (fun θ => (gramMatrix K θ)⁻¹) (complexStrip n r) ∧
    DifferentiableOn ℂ (normalMat K) (complexStrip n r) ∧
    DifferentiableOn ℂ (frameMat K) (complexStrip n r) := by
  have hN := differentiableOn_normalMat hK hG
  exact ⟨(holomorphic_inverse (isOpen_complexStrip n r) (differentiableOn_gramMatrix hK)
    fun θ hθ => (hG θ hθ).ne_zero).1, hN,
    FrameAux.differentiableOn_frameMat (differentiableOn_tangentMat hK) hN⟩

/-- `bpI:p1:extended-basic`, step `eb-holo-field`: `A = DX_H ∘ K` and `DH ∘ K` are holomorphic
on `T_r`. -/
theorem step_eb_holo_field (hS : SettingSrc n τ M D H ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) :
    DifferentiableOn ℂ (linMat H K) (complexStrip n r) ∧
    DifferentiableOn ℂ (fun θ => fderiv ℂ H (K θ)) (complexStrip n r) := by
  have hSt := (hS.setting one_pos one_pos one_pos).toStanding
  exact ⟨FrameAux.differentiableOn_linMat hSt hK hKD,
    (differentiableOn_fderiv_h hSt).comp hK hKD⟩

/-- `bpI:p1:extended-basic`, step `eb-holo-torsion`: `X_N`, `T`, `E_sym`, `Q`, `η`, `Y` are
holomorphic on `T_r`, and `𝖳_H` has the entries `T`, the constant block `ω`, the entries of `Y`
and `0`. -/
theorem step_eb_holo_torsion (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (normalFieldMat H K ω) (complexStrip n r) ∧
    DifferentiableOn ℂ (torsion H K ω) (complexStrip n r) ∧
    DifferentiableOn ℂ (symDefect K) (complexStrip n r) ∧
    DifferentiableOn ℂ (reducer K) (complexStrip n r) ∧
    DifferentiableOn ℂ (eta H K ω) (complexStrip n r) ∧
    DifferentiableOn ℂ (energyRow H K) (complexStrip n r) ∧
    ∀ θ, KAM.Iso.extendedTorsion H K ω θ =
      bordMat (torsion H K ω θ) (fun a => (ω a : ℂ)) (energyRow H K θ) := by
  have hSt := (hS.setting one_pos one_pos one_pos).toStanding
  obtain ⟨hN, hT, hY, -, -⟩ := step_eb_holo hS hr hK hKD hG
  have hP := FrameAux.differentiableOn_frameMat (differentiableOn_tangentMat hK) hN
  exact ⟨FrameAux.differentiableOn_normalFieldMat
    (FrameAux.differentiableOn_linMat hSt hK hKD) hN, hT,
    FrameAux.differentiableOn_symDefect hP, FrameAux.differentiableOn_reducer hP,
    FrameAux.differentiableOn_eta hP (FrameAux.differentiableOn_invarianceError hSt hK hKD), hY,
    extendedTorsion_eq_bordMat H K ω⟩

/-- `bpI:p1:extended-basic`, step `eb-holo-conclude`: `N`, `T`, `Y`, hence every entry of `𝖳_H`,
are holomorphic on `T_r`, in particular continuous on `ℝⁿ ⊆ T_r`. -/
theorem step_eb_holo_conclude (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (normalMat K) (complexStrip n r) ∧
    DifferentiableOn ℂ (torsion H K ω) (complexStrip n r) ∧
    DifferentiableOn ℂ (energyRow H K) (complexStrip n r) ∧
    (∀ i j, DifferentiableOn ℂ (fun θ => KAM.Iso.extendedTorsion H K ω θ i j)
      (complexStrip n r)) ∧
    Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) :=
  step_eb_holo hS hr hK hKD hG

/-- `bpI:p1:extended-basic`, step `eb-period`: `Y` is `1`-periodic on `T_r` and real at real `θ`
(`N`, `T` periodic and real; `DH` periodic along `K` and real at real phase points). -/
theorem step_eb_period (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    IsPeriodicOn (energyRow H K) r ∧ IsRealVec (energyRow H K) ∧
    IsPeriodicOn (normalMat K) r ∧ IsPeriodicOn (torsion H K ω) r ∧
    IsPeriodicOn (fun θ => fderiv ℂ H (K θ)) r ∧
    (∀ x : Fin n → ℝ, ∀ s, (fderiv ℂ H (K fun i => (x i : ℂ))
      ((sumVec n).symm (Pi.single s 1))).im = 0) ∧
    (∀ x : Fin n → ℝ, HasRealEntries (normalMat K fun i => (x i : ℂ))) ∧
    (∀ x : Fin n → ℝ, HasRealEntries (torsion H K ω fun i => (x i : ℂ))) := by
  have hSt := (hS.setting one_pos one_pos one_pos).toStanding
  refine ⟨isPeriodicOn_energyRow hSt hKD hKp, isRealVec_energyRow hSt hr hK hKD hKr hG,
    periodic_normalMat hKp, periodic_torsion hSt hKD hKp hK hG, fun i z hz => ?_, fun x s => ?_,
    hasRealEntries_normalMat hr hK hKr hG, hasRealEntries_torsion hSt hr hK hKD hKr hG⟩
  · have h := fderiv_h_translate hSt (hKD z hz) (Pi.single i 1)
    rw [cast_single_int] at h
    show fderiv ℂ H (K (z + Pi.single i 1)) = fderiv ℂ H (K z)
    rw [primary_coordinatewise hKp i hz]
    exact h
  · obtain ⟨z, hz⟩ := hKr x
    have hmem := hKD _ (realPoint_mem_complexStrip hr x)
    rw [hz] at hmem ⊢
    obtain ⟨h1, h2⟩ := sumVec_symm_single_im s
    exact im_fderiv_real_direction hS.isOpen hS.holo hS.real hmem h1 h2

/-- `bpI:p1:extended-basic`, step `eb-average`: each entry of `𝖳_H` is integrable on `[0,1]ⁿ`;
the frozen `⟨𝖳_H⟩` is the entrywise integral, real; the border entries are `ω` and `0`. -/
theorem step_eb_average (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKp : IsPrimaryOnStrip K r)
    (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    (∀ i j, IntegrableOn
      (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun l => (x l : ℂ)) i j)
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1)) ∧
    (∀ i j, KAM.Iso.extendedTorsionAverage H K ω i j =
      ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        KAM.Iso.extendedTorsion H K ω (fun l => (x l : ℂ)) i j) ∧
    (∀ i j, (KAM.Iso.extendedTorsionAverage H K ω i j).im = 0) ∧
    (∀ a, KAM.Iso.extendedTorsionAverage H K ω (Sum.inl a) (Sum.inr ()) = (ω a : ℂ)) ∧
    KAM.Iso.extendedTorsionAverage H K ω (Sum.inr ()) (Sum.inr ()) = 0 := by
  obtain ⟨⟨-, -, -, -, -, -, hc, havg, him⟩, -⟩ := extended_basic_src hS hr hK hKp hKr hKD hG
  refine ⟨fun i j => integrableOn_unitCube_of_continuous
    ((continuous_apply j).comp ((continuous_apply i).comp hc)), fun i j => rfl, him, fun a => ?_,
    ?_⟩
  · rw [havg]
    simp [bordMat_inl_inr]
  · rw [havg]
    simp [bordMat_inr_inr]

/-- `bpI:p1:extended-basic`, step `eb-bounds`: `|Y| ≤ |DH(K)| |N| ≤ M σ_K' σ_B'` and
`|𝖳_H| ≤ max {C_T + |ω|, |Y|}` in the row-sum norm, where `|DH(K)| = ∑ₛ |DH(K) eₛ|` is the
row-sum norm of the `1 × 2n` matrix `DH(K)`. -/
theorem step_eb_bounds (hS : SettingSrc n τ M D H ω γ) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    {σK' σB' : ℝ} (hL : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK')
    (hB : ∀ θ ∈ complexStrip n r, ‖(gramMatrix K θ)⁻¹‖ ≤ σB') :
    ∀ θ ∈ complexStrip n r,
      ∑ b, ‖energyRow H K θ b‖ ≤
        (∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖) * ‖normalMat K θ‖ ∧
      (∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖) * ‖normalMat K θ‖ ≤
        M * σK' * σB' ∧
      ∀ CT : ℝ, ‖torsion H K ω θ‖ ≤ CT →
        ‖KAM.Iso.extendedTorsion H K ω θ‖ ≤ max (CT + ‖ω‖) (∑ b, ‖energyRow H K θ b‖) := by
  intro θ hθ
  have hN := norm_normalMat_le_of_le (hL θ hθ) (hB θ hθ)
  have hg : ∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ ≤ M :=
    (sum_norm_apply_le_opNorm (fderiv ℂ H (K θ))).trans (hS.dH_le _ (hKD θ hθ))
  have hg0 : 0 ≤ ∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hY : ∑ b, ‖energyRow H K θ b‖ ≤
      (∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖) * ‖normalMat K θ‖ := by
    calc ∑ b, ‖energyRow H K θ b‖
        = ∑ b, ‖∑ s, normalMat K θ s b *
            fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ := by
          simp only [energyRow_apply]
      _ ≤ ∑ b, ∑ s, ‖normalMat K θ s b‖ *
            ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
          Finset.sum_le_sum fun b _ =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => (norm_mul _ _).le)
      _ = ∑ s, (∑ b, ‖normalMat K θ s b‖) *
            ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
      _ ≤ ∑ s, ‖normalMat K θ‖ *
            ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
          Finset.sum_le_sum fun s _ =>
            mul_le_mul_of_nonneg_right (rowSum_le_norm _ s) (norm_nonneg _)
      _ = (∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖) * ‖normalMat K θ‖ := by
          rw [← Finset.mul_sum, mul_comm]
  have hMσ : 0 ≤ ∑ b, ‖energyRow H K θ b‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨hY, ?_, fun CT hCT => ?_⟩
  · calc (∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖) * ‖normalMat K θ‖
        ≤ M * (σK' * σB') := mul_le_mul hg hN (norm_nonneg _) hS.M_pos.le
      _ = M * σK' * σB' := by ring
  · rw [extendedTorsion_eq_bordMat]
    refine (norm_le_iff_forall_rowSum (le_max_of_le_right hMσ)).2 ?_
    rintro (a | u)
    · rw [Fintype.sum_sum_type]
      simp only [bordMat_inl_inl, bordMat_inl_inr, Finset.univ_unique, Finset.sum_singleton]
      have h1 : ∑ b, ‖torsion H K ω θ a b‖ ≤ ‖torsion H K ω θ‖ := rowSum_le_norm _ a
      have h2 : ‖(ω a : ℂ)‖ ≤ ‖ω‖ := by
        rw [Complex.norm_real]
        exact norm_le_pi_norm ω a
      exact (add_le_add (h1.trans hCT) h2).trans (le_max_left _ _)
    · rw [Fintype.sum_sum_type]
      simp only [bordMat_inr_inl, bordMat_inr_inr, Finset.univ_unique, Finset.sum_singleton,
        norm_zero, add_zero]
      exact le_max_right _ _

/-- `bpI:p1:last-row`, step `lr-gradient`: `DH(z) = (Ω₀ X_H(z))ᵀ = -X_H(z)ᵀ Ω₀`, as rows
indexed by the coordinates `Fin n ⊕ Fin n` (`ᵥ*` is the row-vector product). -/
theorem step_lr_gradient (z : (Fin n → ℂ) × (Fin n → ℂ)) :
    (fun s => fderiv ℂ H z ((sumVec n).symm (Pi.single s 1))) =
      omegaZeroMatrix n *ᵥ sumVec n (hamiltonianVectorFieldℂ H z) ∧
    (fun s => fderiv ℂ H z ((sumVec n).symm (Pi.single s 1))) =
      -(sumVec n (hamiltonianVectorFieldℂ H z) ᵥ* omegaZeroMatrix n) := by
  have h : (fun s => fderiv ℂ H z ((sumVec n).symm (Pi.single s 1))) =
      omegaZeroMatrix n *ᵥ sumVec n (hamiltonianVectorFieldℂ H z) := by
    rw [← sumVec_omegaZero, sumVec_omegaZero_ham]
  refine ⟨h, ?_⟩
  rw [h, ← Matrix.mulVec_transpose, omegaZeroMatrix_transpose, Matrix.neg_mulVec]
  simp

/-- `bpI:p1:last-row`, step `lr-average`: (b) `Y = ωᵀ` and `𝖳_H`, `⟨𝖳_H⟩` take the stated form
when `E = 0`; (c) in general `⟨𝖳_H⟩ = 𝖳^inv - (0 0; ⟨ηᴸ⟩ᵀ 0)` and, if `|E| ≤ e`, `|DK| ≤ σ_K'`,
`|B| ≤ σ_B'` on `T_r`, `|⟨𝖳_H⟩ - 𝖳^inv| ≤ 2 n² σ_K' σ_B' e`. -/
theorem step_lr_average (hS : SettingSrc n τ M D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    ((∀ θ ∈ complexStrip n r, invarianceError H K ω θ = 0) →
      (∀ θ ∈ complexStrip n r, energyRow H K θ = fun b => (ω b : ℂ)) ∧
      (∀ θ ∈ complexStrip n r, KAM.Iso.extendedTorsion H K ω θ =
        bordMat (torsion H K ω θ) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ))) ∧
      KAM.Iso.extendedTorsionAverage H K ω =
        bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ))) ∧
    KAM.Iso.extendedTorsionAverage H K ω =
      bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ)) -
        bordMat 0 0 (avg (etaL H K ω)) ∧
    ∀ e σK' σB' : ℝ, (∀ θ ∈ complexStrip n r, ‖invarianceError H K ω θ‖ ≤ e ∧
        ‖fderiv ℂ K θ‖ ≤ σK' ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB') →
      ‖KAM.Iso.extendedTorsionAverage H K ω -
          bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (fun a => (ω a : ℂ))‖ ≤
        2 * n ^ 2 * σK' * σB' * e := by
  obtain ⟨ha, hb, hc, hd⟩ := last_row_src hS hr hK hKD hG
  refine ⟨fun hE => ⟨fun θ hθ => ?_, (hb hE).1, (hb hE).2⟩, ?_, hd⟩
  · rw [(ha θ hθ).1]
    ext b
    simp [etaL, hE θ hθ]
  · rw [hc]
    ext (a | u) (b | v) <;> simp [bordMat]

end KAM.Iso.Linear
