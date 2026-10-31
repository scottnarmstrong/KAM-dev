/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.Normal
public import KAM.Strip.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The intermediate error (step `step:p2s2:st-int`)

For `K̃ = K + N ξᴺ` on `T_{r-δ}`, with `Δ²X = X_h(K + N ξᴺ) - X_h(K) - A N ξᴺ`
(`ModStepB.taylorRem`):

* `Et_eq`: `Ẽ = E + X_N ξᴺ + Δ²X + N ηᴺ` (`∂_ω ξᴺ = -ηᴺ`);
* `Et_add_le`, `Et_le`: `|Ẽ| + σ̃_K Θ C_0 μ ≤ C_Ẽ μ` (the frequency term of `C_Ẽ` is the room for
  `|Ẽ_ω̄ - Ẽ_ω|`);
* `etaNt_eq`, `etaNt_le`: `η̃ᴺ = (L̃ - L)ᵀ Ω₀ Ẽ - (DE)ᵀ Ω₀ N ξᴺ + Lᵀ Ω₀ Δ²X` (`Lᵀ Ω₀ N = -I`,
  `Lᵀ Ω₀ X_N = -(DE)ᵀ Ω₀ N`) and `|η̃ᴺ| ≤ Q̃_N μ²/δ` (FH24 (3.58)–(3.59));
* `omegaKt`: `|Ω_K̃| ≤ C_Ω Q̃_N X μ/δ` on `T_{r-2δ}` (`bp:p2s2:omega` for `K̃` on `T_{r-δ}`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Iso.Linear KAM.Iso.Apost
  KAM.Sharp2.ModStepB

variable {n : ℕ}

namespace ModStepB

/-- `Δ²X = X_h(K + N ξᴺ) - X_h(K) - DX_h(K) N ξᴺ`. -/
def taylorRem (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  hamiltonianVectorFieldℂ h (tilK h K ω E₀ θ) - hamiltonianVectorFieldℂ h (K θ) -
    fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (tilK h K ω E₀ θ - K θ)

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {E₀ γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω E₀ Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `Ẽ = E + X_N ξᴺ + Δ²X + N ηᴺ` on `T_{r-δ}`. -/
theorem Et_eq : ∀ θ ∈ complexStrip n (r - δ),
    sumVec n (invarianceError h (tilK h K ω E₀) ω θ) =
      sumVec n (invarianceError h K ω θ) + normalFieldMat h K ω θ *ᵥ xiNI h K ω E₀ θ +
        sumVec n (taylorRem h K ω E₀ θ) + normalMat K θ *ᵥ etaN h K ω θ := by
  intro θ hθ
  have hθr := H.sub1 hθ
  have hnhds := (isOpen_complexStrip n (r - δ)).mem_nhds hθ
  have hNd : DifferentiableAt ℂ (normalMat K) θ :=
    (H.N_props hS).1.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
  have hξd : DifferentiableAt ℂ (xiNI h K ω E₀) θ := (H.xiN_props hS).1.differentiableAt hnhds
  set v : (Fin n → ℂ) → Fin n ⊕ Fin n → ℂ := fun y => normalMat K y *ᵥ xiNI h K ω E₀ y with hv
  have hvd : DifferentiableAt ℂ v θ := hNd.matrix_mulVec hξd
  set w : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := fun y => (sumVec n).symm (v y) with hw
  have hwd : DifferentiableAt ℂ w θ := (sumVecIso n).symm.differentiable.differentiableAt.comp θ hvd
  have hKt : tilK h K ω E₀ = fun y => K y + w y := rfl
  have hKd := H.K_diffAt θ hθr
  have hdKt : fderiv ℂ (tilK h K ω E₀) θ (fun l => (ω l : ℂ)) =
      fderiv ℂ K θ (fun l => (ω l : ℂ)) + fderiv ℂ w θ (fun l => (ω l : ℂ)) := by
    rw [hKt, fderiv_fun_add hKd hwd, _root_.add_apply]
  have hsw : sumVec n (fderiv ℂ w θ (fun l => (ω l : ℂ))) =
      fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ)) *ᵥ xiNI h K ω E₀ θ -
        normalMat K θ *ᵥ etaN h K ω θ := by
    rw [← fderiv_sumVec_apply]
    have e : (fun y => sumVec n (w y)) = v := funext fun y => by simp [hw]
    rw [e, hv, fderiv_matrix_mulVec_apply hNd hξd, (H.xiN_props hS).2.2.2 θ hθ,
      Matrix.mulVec_neg, sub_eq_add_neg]
  have hKw : tilK h K ω E₀ θ - K θ = w θ := by
    show K θ + w θ - K θ = w θ
    abel
  have hA : sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ h) (K θ) (w θ)) =
      linMat h K θ *ᵥ v θ := by
    have hvw : v θ = sumVec n (w θ) := by simp [hw]
    rw [linMat, hvw, sqMat_mulVec]
  have hT : sumVec n (taylorRem h K ω E₀ θ) =
      sumVec n (hamiltonianVectorFieldℂ h (tilK h K ω E₀ θ)) -
        sumVec n (hamiltonianVectorFieldℂ h (K θ)) - linMat h K θ *ᵥ v θ := by
    rw [taylorRem, hKw, map_sub, map_sub, hA]
  rw [invarianceError, invarianceError, map_sub, map_sub, hdKt, map_add, hsw, normalFieldMat,
    Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  have : sumVec n (hamiltonianVectorFieldℂ h (tilK h K ω E₀ θ)) =
      sumVec n (taylorRem h K ω E₀ θ) + sumVec n (hamiltonianVectorFieldℂ h (K θ)) +
        linMat h K θ *ᵥ v θ := by rw [hT]; abel
  rw [this]
  simp only [hv]
  abel

/-- `|Δ²X| ≤ (M₂/2) |N ξᴺ|²` on `T_{r-δ}`. -/
theorem taylor_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖taylorRem h K ω E₀ θ‖ ≤ p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2 := fun θ hθ => by
  have hθr := H.sub1 hθ
  have hb := H.Kt_mem hS θ hθ
  have hβ := H.β_pos
  have hseg : segment ℝ (K θ) (K θ + (tilK h K ω E₀ θ - K θ)) ⊆ 𝔅 := by
    rw [add_sub_cancel]
    exact ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hb).trans
      (H.ball θ hθr)
  have h1 := taylor_iteratedFDeriv hS.isOpen (differentiableOn_ham hS) (A := p.M2) H.d2X hseg
  rw [add_sub_cancel] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
    (H.Kt_sub_le hS θ hθ) 2) (by have := H.ok.nonneg.2.1; positivity))

omit hS in
/-- `C_K̃ μ ≤ 1` (fifth step condition). -/
theorem Kt_mu_le_one : sCKt p * mu p γ εL εN δ ≤ 1 :=
  (mul_le_mul_of_nonneg_left H.mu_le (nn_sCKt H.ok)).trans (by
    rw [← mul_assoc]; exact H.c_Kt)

/-- `|Ẽ| + σ̃_K Θ C_0 μ ≤ C_Ẽ μ` on `T_{r-δ}`. -/
theorem Et_add_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖invarianceError h (tilK h K ω E₀) ω θ‖ + sKt p * p.Θ * sC0 p * mu p γ εL εN δ ≤
      sCEt p * mu p γ εL εN δ := fun θ hθ => by
  have hθr := H.sub1 hθ
  have hμ := H.mu_nonneg
  have hM2 := H.ok.nonneg.2.1
  rw [← norm_sumVec, H.Et_eq hS θ hθ]
  have h1 := H.E_le hS θ hθ
  have h2 : ‖normalFieldMat h K ω θ *ᵥ xiNI h K ω E₀ θ‖ ≤ sCXN p * (sCxiN p * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.XN_le hS θ hθ) (H.xiN_le hS θ hθ)
      (norm_nonneg _) (nn_sCXN H.ok))
  have h3 : ‖sumVec n (taylorRem h K ω E₀ θ)‖ ≤ p.M2 / 2 * (sCKt p * mu p γ εL εN δ) := by
    rw [norm_sumVec]
    refine (H.taylor_le hS θ hθ).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have h0 : 0 ≤ sCKt p * mu p γ εL εN δ := mul_nonneg (nn_sCKt H.ok) hμ
    nlinarith [H.Kt_mu_le_one]
  have h4 : ‖normalMat K θ *ᵥ etaN h K ω θ‖ ≤ p.sN * (sg p * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.N' θ hθr) ((H.ηN θ hθr).trans
      (H.εN_le.trans (mul_le_mul_of_nonneg_right H.gd_le hμ))) (norm_nonneg _)
      H.ok.caps.2.2.2.1.le)
  have h1' : ‖sumVec n (invarianceError h K ω θ)‖ ≤ sCE p * mu p γ εL εN δ := by
    rw [norm_sumVec]; exact h1
  have hsum := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add h1' h2)) h3)) h4)
  have e : sCEt p * mu p γ εL εN δ = sCE p * mu p γ εL εN δ +
      sCXN p * (sCxiN p * mu p γ εL εN δ) + p.M2 / 2 * (sCKt p * mu p γ εL εN δ) +
      p.sN * (sg p * mu p γ εL εN δ) + sKt p * p.Θ * sC0 p * mu p γ εL εN δ := by
    rw [sCEt]
    simp only [H.iso, ↓reduceIte]
    ring
  rw [e]
  linarith

/-- `|Ẽ| ≤ C_Ẽ μ` on `T_{r-δ}`. -/
theorem Et_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖invarianceError h (tilK h K ω E₀) ω θ‖ ≤ sCEt p * mu p γ εL εN δ := fun θ hθ => by
  have h1 := H.Et_add_le hS θ hθ
  have h0 : 0 ≤ sKt p * p.Θ * sC0 p * mu p γ εL εN δ :=
    mul_nonneg (mul_nonneg (mul_nonneg (nn_sKt H.ok) H.ok.nonneg.2.2.2.2.1) (nn_sC0 H.ok))
      H.mu_nonneg
  linarith

/-- `η̃ᴺ = (L̃ - L)ᵀ Ω₀ Ẽ - (DE)ᵀ Ω₀ N ξᴺ + Lᵀ Ω₀ Δ²X` on `T_{r-δ}`. -/
theorem etaNt_eq : ∀ θ ∈ complexStrip n (r - δ),
    etaN h (tilK h K ω E₀) ω θ =
      ((tangentMat (tilK h K ω E₀) θ - tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          sumVec n (invarianceError h (tilK h K ω E₀) ω θ) -
        ((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ xiNI h K ω E₀ θ +
        ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ) := by
  intro θ hθ
  have hθr := H.sub1 hθ
  have hLON := Identities.fi_LtON K (H.gram θ hθr)
  have hLOX := Identities.fi_LtOXN hS H.holo H.K_mem H.gram hθr
  have hsplit : etaN h (tilK h K ω E₀) ω θ =
      ((tangentMat (tilK h K ω E₀) θ - tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          sumVec n (invarianceError h (tilK h K ω E₀) ω θ) +
        ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          sumVec n (invarianceError h (tilK h K ω E₀) ω θ) := by
    rw [etaN, ← Matrix.add_mulVec, Matrix.transpose_sub, Matrix.sub_mul, sub_add_cancel]
  have hmain : ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h (tilK h K ω E₀) ω θ) =
      -((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ xiNI h K ω E₀ θ +
        ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ) := by
    rw [H.Et_eq hS θ hθ, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hLOX, hLON]
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec]
    have : ((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h K ω θ) =
        etaN h K ω θ := rfl
    rw [this]
    abel
  rw [hsplit, hmain, Matrix.neg_mulVec]
  abel

/-- `|η̃ᴺ| ≤ Q̃_N μ²/δ` on `T_{r-δ}`. -/
theorem etaNt_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖etaN h (tilK h K ω E₀) ω θ‖ ≤ sQtN p * mu p γ εL εN δ ^ 2 / δ := fun θ hθ => by
  have hθr := H.sub1 hθ
  have hμ := H.mu_nonneg
  have hδ := H.δ_pos
  have hM2 := H.ok.nonneg.2.1
  rw [H.etaNt_eq hS θ hθ]
  have h1 : ‖((tangentMat (tilK h K ω E₀) θ - tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h (tilK h K ω E₀) ω θ)‖ ≤
      sCDLtT p * (mu p γ εL εN δ / δ) * (sCEt p * mu p γ εL εN δ) := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
      (by have := nn_sCDLtT H.ok; positivity))
    · rw [norm_mul_omegaZeroMatrix]; exact (H.Lt_sub_le hS θ hθ).2
    · rw [norm_sumVec]; exact H.Et_le hS θ hθ
  have h2 : ‖((errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ xiNI h K ω E₀ θ‖ ≤
      sCNN p * (mu p γ εL εN δ / δ) * (sCxiN p * mu p γ εL εN δ) := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ (H.xiN_le hS θ hθ)
      (norm_nonneg _) (by have := nn_sCNN H.ok; positivity))
    have e : (errDerivMat h K ω θ)ᵀ * omegaZeroMatrix n * normalMat K θ =
        -((normalMat K θ)ᵀ * omegaZeroMatrix n * errDerivMat h K ω θ)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        omegaZeroMatrix_transpose]
      simp [Matrix.mul_assoc]
    rw [e, norm_neg]; exact H.NtODE_le hS θ hθ
  have h3 : ‖((tangentMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ)‖ ≤
      p.sLt * (p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2) := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
      H.ok.caps.2.1.le)
    · rw [norm_mul_omegaZeroMatrix]; exact H.Lt' θ hθr
    · rw [norm_sumVec]; exact H.taylor_le hS θ hθ
  refine (norm_add_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans (add_le_add h1 h2))
    h3).trans ?_)
  have hC : 0 ≤ p.sLt * (p.M2 / 2) * sCKt p ^ 2 := by have := H.ok.caps.2.1; positivity
  have hpd : δ * (p.sLt * (p.M2 / 2) * sCKt p ^ 2) ≤ p.δ * (p.sLt * (p.M2 / 2) * sCKt p ^ 2) :=
    mul_le_mul_of_nonneg_right H.δ_le hC
  have hμ2 : 0 ≤ mu p γ εL εN δ ^ 2 / δ := by positivity
  have key : sCDLtT p * (mu p γ εL εN δ / δ) * (sCEt p * mu p γ εL εN δ) +
      sCNN p * (mu p γ εL εN δ / δ) * (sCxiN p * mu p γ εL εN δ) +
      p.sLt * (p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2) =
      (sCDLtT p * sCEt p + sCNN p * sCxiN p + δ * (p.sLt * (p.M2 / 2) * sCKt p ^ 2)) *
        (mu p γ εL εN δ ^ 2 / δ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    field_simp
  rw [key]
  calc _ ≤ (sCDLtT p * sCEt p + sCNN p * sCxiN p + p.δ * (p.sLt * (p.M2 / 2) * sCKt p ^ 2)) *
        (mu p γ εL εN δ ^ 2 / δ) := mul_le_mul_of_nonneg_right (by linarith) hμ2
    _ = _ := by rw [sQtN]; ring

omit hS in
/-- `2(n-1) c' / (s^κ (1-s)) γ⁻¹ δ^{-(κ+1)} E ≤ C_Ω X E/μ`, in the form used for `Ω_K̃`. -/
theorem omega_conv {E : ℝ} (hE : 0 ≤ E) :
    2 * ((n : ℝ) - 1) * (c' / (s ^ p.κ * (1 - s))) * γ⁻¹ * δ ^ (-(p.κ + 1)) * E ≤
      sCΩ p * (E / (γ * δ ^ (p.κ + 1))) := by
  have hn1 : (0 : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith [H.one_le_n]
  have e : γ⁻¹ * δ ^ (-(p.κ + 1)) * E = E / (γ * δ ^ (p.κ + 1)) := by
    rw [Real.rpow_neg H.δ_pos.le]; field_simp
  have hY : 0 ≤ E / (γ * δ ^ (p.κ + 1)) := div_nonneg hE H.gd1_pos.le
  calc _ = 2 * ((n : ℝ) - 1) * (c' / (s ^ p.κ * (1 - s))) * (γ⁻¹ * δ ^ (-(p.κ + 1)) * E) := by
        ring
    _ ≤ 2 * ((n : ℝ) - 1) * p.c1 * (E / (γ * δ ^ (p.κ + 1))) := by
        rw [e]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H.c1_le hn1) hY
    _ = _ := by rw [sCΩ, H.pn_real]

/-- `bp:p2s2:omega` for `K̃` on `T_{r-δ}`: `|Ω_K̃| ≤ C_Ω Q̃_N X μ/δ` on `T_{r-2δ}`. -/
theorem omegaKt : ∀ θ ∈ complexStrip n (r - 2 * δ),
    ‖lagrangeMat (tilK h K ω E₀) θ‖ ≤
      sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ) := by
  intro θ hθ
  have hn : 1 ≤ n := H.n_pos
  have hθ' : θ ∈ complexStrip n (r - δ - δ) := by
    rw [show r - δ - δ = r - 2 * δ by ring]; exact hθ
  have h1 := norm_lagrangeMat_le_etaN_of_standing hn H.cert' H.mem H.s_pos H.s_lt H.δ_lt_r1 hS
    (H.Kt_holo hS) (H.Kt_primary hS) (H.Kt_mem𝔅 hS) (H.etaNt_le hS) θ hθ'
  have hE : 0 ≤ sQtN p * mu p γ εL εN δ ^ 2 / δ := by
    have := nn_sQtN H.ok
    have := H.δ_pos
    positivity
  refine h1.trans ((H.omega_conv hE).trans (le_of_eq ?_))
  rw [xX]
  field_simp

end Hyp

end ModStepB

end KAM.Iso.Sharp2

end
