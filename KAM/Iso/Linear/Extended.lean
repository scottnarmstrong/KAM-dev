/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Linear.Defs
public import KAM.Apost.Frame
public import KAM.Apost.Periodicity
public import KAM.Torus.FrozenAgreement
import KAM.Matrix.Inverse

/-!
# Part 1: regularity, periodicity, realness and size of the extended torsion

Blueprint node `bpI:p1:extended-basic` (`KAM.Iso.Linear.extended_basic`) and the helper
`KAM.Iso.Linear.extended_regular` (regularity at any real frequency, blueprint issue B1).

The last row `Y = DH(K) N` (`energyRow`) is first rewritten as a matrix expression,
`Y = Nᵀ (Ω₀ (X_H ∘ K))` in the `sumVec`-coordinates (`ExtendedAux.energyRow_eq_mulVec`); this
reduces holomorphy, periodicity and realness of `Y` to the corresponding facts about `N` and
`X_H ∘ K` proved in `KAM.Apost` (`KAM.Apost.periodicity`, `KAM.Apost.ham_real_of_K`,
`KAM.Apost.FrameAux.differentiableOn_*`). The bordered matrix is `bordMat T ω Y`
(`extendedTorsion_eq_bordMat`), so every statement about `𝖳_H` is entrywise over
`Fin n ⊕ Unit`. The size bound `‖Y‖ ≤ M σ_K' σ_B'` uses the hypothesis `‖DH‖ ≤ M` of `Setting`
through the `ℓ¹` bound `∑ₛ |DH e_s| ≤ ‖DH‖` (`ExtendedAux.sum_norm_apply_le_opNorm`).

Helper lemmas live in `KAM.Iso.Linear.ExtendedAux`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix MeasureTheory

namespace KAM.Iso.Linear

open KAM KAM.Torus KAM.Apost

namespace ExtendedAux

variable {n : ℕ}

/-! ### The bordered matrix, entrywise -/

theorem bordMat_inl_inl (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) (a b : Fin n) :
    bordMat A c y (Sum.inl a) (Sum.inl b) = A a b := rfl

theorem bordMat_inl_inr (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) (a : Fin n) (u : Unit) :
    bordMat A c y (Sum.inl a) (Sum.inr u) = c a := rfl

theorem bordMat_inr_inl (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) (u : Unit) (b : Fin n) :
    bordMat A c y (Sum.inr u) (Sum.inl b) = y b := rfl

theorem bordMat_inr_inr (A : Matrix (Fin n) (Fin n) ℂ) (c y : Fin n → ℂ) (u v : Unit) :
    bordMat A c y (Sum.inr u) (Sum.inr v) = 0 := rfl

/-- `𝖳_H` as a function of the angle: `bordMat T ω Y`. -/
theorem extendedTorsion_eq_fun (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (ω : Fin n → ℝ) :
    KAM.Iso.extendedTorsion H K ω =
      fun θ => bordMat (torsion H K ω θ) (fun a => (ω a : ℂ)) (energyRow H K θ) :=
  funext (extendedTorsion_eq_bordMat H K ω)

theorem differentiableOn_bordMat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {V : Set E} {A : E → Matrix (Fin n) (Fin n) ℂ} {y : E → Fin n → ℂ} (c : Fin n → ℂ)
    (hA : DifferentiableOn ℂ A V) (hy : DifferentiableOn ℂ y V) :
    DifferentiableOn ℂ (fun θ => bordMat (A θ) c (y θ)) V := by
  rw [differentiableOn_matrix_iff_entries]
  rintro (a | u) (b | v)
  · exact differentiableOn_matrix_iff_entries.1 hA a b
  · exact differentiableOn_const _
  · exact differentiableOn_pi.1 hy b
  · exact differentiableOn_const _

/-- A function holomorphic on the strip `T_r` is continuous on the real points. -/
theorem continuous_real_restrict {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {u : (Fin n → ℂ) → F} {r : ℝ} (hr : 0 < r) (hu : DifferentiableOn ℂ u (complexStrip n r)) :
    Continuous (fun x : Fin n → ℝ => u (fun i => (x i : ℂ))) :=
  hu.continuousOn.comp_continuous
    (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
    (ofReal_mem_complexStrip hr)

/-! ### The last row `Y = DH(K) N` as a matrix expression -/

/-- A linear functional on `ℂⁿ × ℂⁿ` in the coordinates of `sumVec`. -/
theorem apply_eq_sum_sumVec (φ : (Fin n → ℂ) × (Fin n → ℂ) →L[ℂ] ℂ)
    (v : (Fin n → ℂ) × (Fin n → ℂ)) :
    φ v = ∑ s, sumVec n v s * φ ((sumVec n).symm (Pi.single s 1)) := by
  have hv : v = ∑ s, sumVec n v s • (sumVec n).symm (Pi.single s 1) := by
    apply (sumVec n).injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    ext t
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

/-- `Y_b = ∑ₛ N_{sb} ∂ₛH(K θ)`, for every `θ`. -/
theorem energyRow_apply (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) (b : Fin n) :
    energyRow H K θ b = ∑ s, normalMat K θ s b *
      fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1)) := by
  rw [energyRow, apply_eq_sum_sumVec (fderiv ℂ H (K θ)), sumVec_normalFrame]

/-- `Y = Nᵀ (Ω₀ (X_H ∘ K))` in the `sumVec`-coordinates, for every `θ`. -/
theorem energyRow_eq_mulVec (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) :
    energyRow H K θ =
      (normalMat K θ)ᵀ *ᵥ (omegaZeroMatrix n *ᵥ sumVec n (hamiltonianVectorFieldℂ H (K θ))) := by
  ext b
  rw [← sumVec_omegaZero, sumVec_omegaZero_ham, energyRow_apply, Matrix.mulVec, dotProduct]
  rfl

/-- The `ℓ¹` norm of the coordinates of a linear functional is at most its operator norm. -/
theorem sum_norm_apply_le_opNorm (φ : (Fin n → ℂ) × (Fin n → ℂ) →L[ℂ] ℂ) :
    ∑ s, ‖φ ((sumVec n).symm (Pi.single s 1))‖ ≤ ‖φ‖ := by
  obtain ⟨w, hw, hwM⟩ := exists_mulVec_apply_eq_rowSum
    (Matrix.of fun (_ : Unit) (s : Fin n ⊕ Fin n) => φ ((sumVec n).symm (Pi.single s 1))) ()
  have hv : ‖(sumVec n).symm w‖ ≤ 1 := by
    rw [← norm_sumVec, LinearEquiv.apply_symm_apply]
    exact hw
  have hφ : φ ((sumVec n).symm w) = ((∑ s, ‖φ ((sumVec n).symm (Pi.single s 1))‖ : ℝ) : ℂ) := by
    rw [apply_eq_sum_sumVec φ]
    simp only [LinearEquiv.apply_symm_apply]
    have hwM' : ∑ s, φ ((sumVec n).symm (Pi.single s 1)) * w s =
        ((∑ s, ‖φ ((sumVec n).symm (Pi.single s 1))‖ : ℝ) : ℂ) := hwM
    rw [← hwM']
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have h0 : 0 ≤ ∑ s, ‖φ ((sumVec n).symm (Pi.single s 1))‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc ∑ s, ‖φ ((sumVec n).symm (Pi.single s 1))‖
      = ‖φ ((sumVec n).symm w)‖ := by
        rw [hφ, Complex.norm_real, Real.norm_of_nonneg h0]
    _ ≤ ‖φ‖ * ‖(sumVec n).symm w‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ := mul_le_of_le_one_right (norm_nonneg _) hv

/-! ### Holomorphy, periodicity, realness of `Y` -/

section Analytic

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {r : ℝ}

/-- `Y = DH(K) N` is holomorphic on `T_r`. -/
theorem differentiableOn_energyRow (hS : Standing n τ M σK σB σT D H ω γ)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    DifferentiableOn ℂ (energyRow H K) (complexStrip n r) := by
  have hN := differentiableOn_normalMat hK hG
  have hX : DifferentiableOn ℂ (fun θ => sumVec n (hamiltonianVectorFieldℂ H (K θ)))
      (complexStrip n r) :=
    (sumVecIso n).differentiable.comp_differentiableOn ((differentiableOn_ham hS).comp hK hKD)
  have h := hN.matrix_transpose.matrix_mulVec
    ((differentiableOn_const (omegaZeroMatrix n)).matrix_mulVec hX)
  exact h.congr fun θ _ => energyRow_eq_mulVec H K θ

/-- `Y` is `1`-periodic on `T_r`. -/
theorem isPeriodicOn_energyRow (hS : Standing n τ M σK σB σT D H ω γ)
    (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D) (hKp : IsPrimaryOnStrip K r) :
    IsPeriodicOn (energyRow H K) r := fun i z hz => by
  rw [energyRow_eq_mulVec, energyRow_eq_mulVec, periodic_normalMat hKp i z hz,
    primary_coordinatewise hKp i hz, ham_translate_single hS (hKD z hz) i |>.1]

/-- `Y` is real at real points. -/
theorem isRealVec_energyRow (hS : Standing n τ M σK σB σT D H ω γ) (hr : 0 < r)
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hKr : IsRealOnReals K) (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    IsRealVec (energyRow H K) := fun x b => by
  rw [energyRow_eq_mulVec]
  exact ((hasRealEntries_normalMat hr hK hKr hG x).transpose.mulVec
    ((hasRealEntries_omegaZeroMatrix n).mulVec
      (ham_real_of_K hS hr hKD hKr x).1)) b

/-- The average of `𝖳_H`: the border carries `ω` and `⟨Y⟩`. Only continuity of `Y` on the real
points is used. -/
theorem extendedTorsionAverage_eq_bordMat
    (hY : Continuous (fun x : Fin n → ℝ => energyRow H K (fun i => (x i : ℂ)))) :
    KAM.Iso.extendedTorsionAverage H K ω = bordMat (torsionAverage H K ω)
      (fun a => (ω a : ℂ)) (avg (energyRow H K)) := by
  ext (a | u) (b | v)
  · rfl
  · show ∫ θ in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), ((ω a : ℝ) : ℂ) = (ω a : ℂ)
    rw [setIntegral_const, measureReal_def, volume_unitCube, ENNReal.toReal_one, one_smul]
  · show ∫ θ in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        energyRow H K (fun l => (θ l : ℂ)) b = avg (energyRow H K) b
    exact (Tools.torusAverage_vector_apply hY b).symm
  · show ∫ θ in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), (0 : ℂ) = 0
    simp

end Analytic

/-! ### The size of `Y` -/

section Size

variable {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {θ : Fin n → ℂ}

/-- `‖N‖ ≤ ‖L‖ ‖B‖` for bounds `σK', σB'` of `‖DK‖`, `‖B‖`. -/
theorem norm_normalMat_le_of_le {σK' σB' : ℝ} (hL : ‖fderiv ℂ K θ‖ ≤ σK')
    (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB') : ‖normalMat K θ‖ ≤ σK' * σB' := by
  calc ‖normalMat K θ‖
      ≤ ‖omegaZeroMatrix n * tangentMat K θ‖ * ‖(gramMatrix K θ)⁻¹‖ :=
        Matrix.linfty_opNorm_mul _ _
    _ = ‖tangentMat K θ‖ * ‖(gramMatrix K θ)⁻¹‖ := by rw [norm_omegaZeroMatrix_mul]
    _ ≤ σK' * σB' := by
        rw [FrameAux.norm_tangentMat]
        exact mul_le_mul hL hB (norm_nonneg _) ((norm_nonneg _).trans hL)

/-- `∑_b |Y_b| ≤ M σ_K' σ_B'` at a point where `K θ ∈ D`, `‖DK‖ ≤ σ_K'`, `‖B‖ ≤ σ_B'`. -/
theorem sum_norm_energyRow_le (hS : Setting n τ M σK σB σT D H ω γ) (hθD : K θ ∈ D)
    {σK' σB' : ℝ} (hL : ‖fderiv ℂ K θ‖ ≤ σK') (hB : ‖(gramMatrix K θ)⁻¹‖ ≤ σB') :
    ∑ b, ‖energyRow H K θ b‖ ≤ M * σK' * σB' := by
  have hN := norm_normalMat_le_of_le hL hB
  have hg : ∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ ≤ M :=
    (sum_norm_apply_le_opNorm (fderiv ℂ H (K θ))).trans (hS.dH_le _ hθD)
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
    _ ≤ ∑ s, (σK' * σB') *
          ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
        Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_right ((rowSum_le_norm _ s).trans hN) (norm_nonneg _)
    _ = (σK' * σB') * ∑ s, ‖fderiv ℂ H (K θ) ((sumVec n).symm (Pi.single s 1))‖ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (σK' * σB') * M :=
        mul_le_mul_of_nonneg_left hg ((norm_nonneg _).trans hN)
    _ = M * σK' * σB' := by ring

end Size

end ExtendedAux

open ExtendedAux

section Torus

variable {n : ℕ} {τ M σK σB σT γ : ℝ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))}
  {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}

/-- Regularity of `𝖳_H` at ANY real frequency `ω'` (blueprint issue B1: `bpI:p2:torsion` uses
`extended-basic` at the non-certified frequency `ω̄`). Only the Hamiltonian fields of `hS` enter. -/
theorem extended_regular {ω₀ : Fin n → ℝ} (hS : KAM.Apost.Standing n τ M σK σB σT D H ω₀ γ)
    {r : ℝ} (hr : 0 < r) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n r)) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) (ω' : Fin n → ℝ) :
    DifferentiableOn ℂ (energyRow H K) (complexStrip n r) ∧
      DifferentiableOn ℂ (KAM.Iso.extendedTorsion H K ω') (complexStrip n r) ∧
      Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω' (fun i => (x i : ℂ))) := by
  have hN := differentiableOn_normalMat hK hG
  have hY := differentiableOn_energyRow hS hK hKD hG
  have hAd := FrameAux.differentiableOn_linMat hS hK hKD
  have hXd := FrameAux.differentiableOn_normalFieldMat (ω := ω') hAd hN
  have hTd := FrameAux.differentiableOn_torsion hN hXd
  have hE : DifferentiableOn ℂ (KAM.Iso.extendedTorsion H K ω') (complexStrip n r) := by
    rw [extendedTorsion_eq_fun]
    exact differentiableOn_bordMat _ hTd hY
  exact ⟨hY, hE, continuous_real_restrict hr hE⟩

/-- `bpI:p1:extended-basic`. (a) regularity, periodicity, realness, the block form of `⟨𝖳_H⟩`;
(b) `|Y| ≤ Mσ'_Kσ'_B` (row sums) and `|𝖳_H| ≤ max {C_T + |ω|, Mσ'_Kσ'_B}`. -/
theorem extended_basic (hS : Setting n τ M σK σB σT D H ω γ) {r : ℝ} (hr : 0 < r)
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hKp : IsPrimaryOnStrip K r) (hKr : IsRealOnReals K) (hKD : ∀ θ ∈ complexStrip n r, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det) :
    (DifferentiableOn ℂ (energyRow H K) (complexStrip n r) ∧ IsPeriodicOn (energyRow H K) r ∧
      IsRealVec (energyRow H K) ∧
      DifferentiableOn ℂ (KAM.Iso.extendedTorsion H K ω) (complexStrip n r) ∧
      IsPeriodicOn (KAM.Iso.extendedTorsion H K ω) r ∧ IsRealMat (KAM.Iso.extendedTorsion H K ω) ∧
      Continuous (fun x : Fin n → ℝ => KAM.Iso.extendedTorsion H K ω (fun i => (x i : ℂ))) ∧
      KAM.Iso.extendedTorsionAverage H K ω =
        bordMat (torsionAverage H K ω) (fun a => (ω a : ℂ)) (avg (energyRow H K)) ∧
      ∀ i j, (KAM.Iso.extendedTorsionAverage H K ω i j).im = 0) ∧
    ∀ σK' σB' : ℝ,
      (∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK' ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB') →
      ∀ θ ∈ complexStrip n r, ∑ b, ‖energyRow H K θ b‖ ≤ M * σK' * σB' ∧
        ∀ CT : ℝ, ‖torsion H K ω θ‖ ≤ CT →
          ‖KAM.Iso.extendedTorsion H K ω θ‖ ≤ max (CT + ‖ω‖) (M * σK' * σB') := by
  have hSt := hS.toStanding
  obtain ⟨hYd, hEd, hEc⟩ := extended_regular hSt hr hK hKD hG ω
  have hYr := isRealVec_energyRow hSt hr hK hKD hKr hG
  have hTr : ∀ x : Fin n → ℝ, HasRealEntries (torsion H K ω fun i => (x i : ℂ)) :=
    fun x => hasRealEntries_torsion hSt hr hK hKD hKr hG x
  have hYc := continuous_real_restrict hr hYd
  have havg := extendedTorsionAverage_eq_bordMat (ω := ω) hYc
  refine ⟨⟨hYd, isPeriodicOn_energyRow hSt hKD hKp, hYr, hEd, ?_, ?_, hEc, havg, ?_⟩, ?_⟩
  · intro i z hz
    rw [extendedTorsion_eq_fun]
    show bordMat (torsion H K ω (z + Pi.single i 1)) _ (energyRow H K (z + Pi.single i 1)) =
      bordMat (torsion H K ω z) _ (energyRow H K z)
    rw [periodic_torsion hSt hKD hKp hK hG i z hz, isPeriodicOn_energyRow hSt hKD hKp i z hz]
  · intro x i j
    rw [extendedTorsion_eq_bordMat]
    rcases i with a | u <;> rcases j with b | v
    · exact hTr x a b
    · simp [bordMat_inl_inr]
    · exact hYr x b
    · simp [bordMat_inr_inr]
  · intro i j
    rw [havg]
    rcases i with a | u <;> rcases j with b | v
    · exact im_torsionAverage hTr a b
    · simp [bordMat_inl_inr]
    · show (avg (energyRow H K) b).im = 0
      rw [show avg (energyRow H K) b = ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
        energyRow H K (fun i => (x i : ℂ)) b from Tools.torusAverage_vector_apply hYc b]
      exact Tools.im_integral_eq_zero fun x => hYr x b
    · simp [bordMat_inr_inr]
  · intro σK' σB' hbd θ hθ
    obtain ⟨hL, hB⟩ := hbd θ hθ
    have hY := sum_norm_energyRow_le hS (hKD θ hθ) hL hB
    refine ⟨hY, fun CT hCT => ?_⟩
    have hMσ : 0 ≤ M * σK' * σB' := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hY
    rw [extendedTorsion_eq_bordMat]
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
      exact hY.trans (le_max_right _ _)

end Torus

end KAM.Iso.Linear

end
