/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.Frames
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new errors (steps `stepI:p2s2:st-w`, `stepI:p2s2:st-l`)

With `φ = id + ξᴸ`, `g = gᴸ = ∂_ω ξᴸ`, `x = ξ^ω`, `a = 1 - x`, `ω̄ = a ω`, at `θ ∈ T_{r-2δ}`:

* `Lb_eq`: `L̄ = (L̃ ∘ φ)(I + Dξᴸ)` (chain rule);
* `EW_eq`: `Ẽ_ω̄ = Ẽ_ω + x L̃ ω`; `Eb_eq`: `Ē_ω̄ = Ẽ_ω̄ ∘ φ - a (L̃ ∘ φ) g`;
* `etaNb_eq`: `η̄ᴺ = (I + Dξᴸ)ᵀ (η̃ᴺ ∘ φ + (Ω_K̃ ∘ φ)(x ω - a g))`;

and on `T_{r-3δ}`:

* `etaNb_le`: `|η̄ᴺ| ≤ Q̄_N μ²/δ` (`|x ω - a g| ≤ (1 + a_ω) C_gL μ`, as `Θ C_0 ≤ C_gL`);
* `NtO_Et_eq`, `NtOEb_key`, `NtOEb_le`: `|Nᵀ Ω₀ Ē| ≤ Q'_L μ X`, from
  `Nᵀ Ω₀ Ē = Nᵀ Ω₀ (Ẽ_ω̄∘φ - Ẽ_ω̄) - a Nᵀ Ω₀ (L̃∘φ - L̃) g - a Nᵀ Ω₀ (L̃ - L) g + x g +
  (Nᵀ Ω₀ Δ²X + Ω_N ηᴺ) + x Nᵀ Ω₀ (L̃ - L) ω`: the terms `ηᴸ - T ξᴺ - ω ξ^ω` cancel against `a g`
  up to `x g`;
* `Eb_le`: `|Ē| ≤ C_Ē μ`; `etaLb_crude`: `|η̄ᴸ| ≤ (Q'_L + C_N̄ᵀ C_Ē) μ X`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Iso.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Iso.Linear KAM.Iso.Apost
  KAM.Sharp2.ModStepB

variable {n : ℕ}

namespace ModStepB

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {E₀ γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω E₀ Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `Dξᴸ` as a matrix. -/
abbrev dXiL (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (E₀ : ℝ) (θ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ (xiLI h K ω E₀) θ (Pi.single j 1) i

theorem phi2 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    θ + xiLI h K ω E₀ θ ∈ complexStrip n (r - δ) := by
  have := H.phi_mem hS le_rfl hθ
  rwa [show r - 2 * δ + δ = r - δ by ring] at this

theorem phi3 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    θ + xiLI h K ω E₀ θ ∈ complexStrip n (r - 2 * δ) := by
  have := H.phi_mem hS (by linarith [H.δ_pos]) hθ
  rwa [show r - 3 * δ + δ = r - 2 * δ by ring] at this

theorem xiL_diffAt {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    DifferentiableAt ℂ (xiLI h K ω E₀) θ :=
  (H.xiL_props hS).1.differentiableAt ((isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ)

/-- The derivative of `K̄` near `θ ∈ T_{r-2δ}` is that of `K̃ ∘ φ`. -/
theorem fderiv_Kb {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    fderiv ℂ (newK h K ω E₀ (r - 2 * δ)) θ =
      (fderiv ℂ (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ)).comp
        (ContinuousLinearMap.id ℂ _ + fderiv ℂ (xiLI h K ω E₀) θ) := by
  rw [(newK_eventuallyEq hθ).fderiv_eq]
  exact ((H.Kt_diffAt hS _ (H.phi2 hS hθ)).hasFDerivAt.comp θ
    ((hasFDerivAt_id θ).add (H.xiL_diffAt hS hθ).hasFDerivAt)).fderiv

/-- `L̄ = (L̃ ∘ φ)(I + Dξᴸ)`. -/
theorem Lb_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    tangentMat (newK h K ω E₀ (r - 2 * δ)) θ =
      tangentMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) * (1 + dXiL h K ω E₀ θ) := by
  have e : tangentMat (newK h K ω E₀ (r - 2 * δ)) θ =
      tangentMat (fun y => tilK h K ω E₀ (y + xiLI h K ω E₀ y)) θ := by
    rw [tangentMat, tangentMat, (newK_eventuallyEq hθ).fderiv_eq]
  rw [e, tangentMat_comp_eq (H.Kt_diffAt hS _ (H.phi2 hS hθ)) (H.xiL_diffAt hS hθ)]

/-- `ξ^ω` is real. -/
theorem xw_eq : isoXiOmega h K ω E₀ = (xw h K ω E₀ : ℂ) := by
  obtain ⟨-, -, -, -, him, -⟩ := H.bord hS
  exact Complex.ext (by simp [xw]) (by simpa using him)

/-- `|ξ^ω| ≤ C_0 μ`. -/
theorem abs_xw_le : |xw h K ω E₀| ≤ sC0 p * mu p γ εL εN δ := by
  refine (Complex.abs_re_le_norm _).trans (H.xw_le hS)

/-- `|ξ^ω| ≤ ϑ_ω` (step `st-av`). -/
theorem abs_xw_small : |xw h K ω E₀| ≤ p.θω := by
  refine (H.abs_xw_le hS).trans ?_
  refine (mul_le_mul_of_nonneg_left H.mu_le (nn_sC0 H.ok)).trans ?_
  have := H.c_ω
  rw [sg1, ← mul_assoc]
  exact this

/-- `|1 - ξ^ω| ≤ a_ω`. -/
theorem abs_a_le : ‖(1 : ℂ) - (xw h K ω E₀ : ℂ)‖ ≤ saw p := by
  have e : (1 : ℂ) - (xw h K ω E₀ : ℂ) = ((1 - xw h K ω E₀ : ℝ) : ℂ) := by push_cast; rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, saw]
  simp only [H.iso, ↓reduceIte]
  have h1 := abs_sub (1 : ℝ) (xw h K ω E₀)
  rw [abs_one] at h1
  linarith [H.abs_xw_small hS]

omit H hS in
/-- `ω̄ = (1 - x) ω`, as a complex vector. -/
theorem newOmega_c : (fun l => (newOmega h K ω E₀ l : ℂ)) =
    ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • fun l => (ω l : ℂ) := by
  funext l
  simp [newOmega]

omit H hS in
/-- `Ẽ_ω̄ = Ẽ_ω + x L̃ ω`. -/
theorem EW_eq (y : Fin n → ℂ) :
    sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) y) =
      sumVec n (invarianceError h (tilK h K ω E₀) ω y) +
        (xw h K ω E₀ : ℂ) • (tangentMat (tilK h K ω E₀) y *ᵥ fun l => (ω l : ℂ)) := by
  rw [invarianceError, invarianceError, newOmega_c, map_smul, map_sub, map_sub, tangentMat,
    colMat_mulVec, map_smul]
  module

/-- `|Ẽ_ω̄| ≤ C_Ẽ μ` on `T_{r-δ}`. -/
theorem EW_le : ∀ y ∈ complexStrip n (r - δ),
    ‖sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) y)‖ ≤
      sCEt p * mu p γ εL εN δ := fun y hy => by
  rw [EW_eq]
  have h1 := H.Et_add_le hS y hy
  have h2 : ‖(xw h K ω E₀ : ℂ) • (tangentMat (tilK h K ω E₀) y *ᵥ fun l => (ω l : ℂ))‖ ≤
      sC0 p * mu p γ εL εN δ * (sKt p * p.Θ) := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (H.abs_xw_le hS) ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (H.Lt_le hS y hy).1 ((BorderSolve.norm_omega_le ω).trans H.Θ) (norm_nonneg _)
        (nn_sKt H.ok))) (norm_nonneg _) (mul_nonneg (nn_sC0 H.ok) H.mu_nonneg)
  refine (norm_add_le _ _).trans ?_
  rw [norm_sumVec]
  nlinarith [h1, h2]

/-- `Ē_ω̄ = Ẽ_ω̄ ∘ φ - a (L̃ ∘ φ) g`. -/
theorem Eb_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ) =
      sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀)
          (θ + xiLI h K ω E₀ θ)) -
        ((1 : ℂ) - (xw h K ω E₀ : ℂ)) •
          (tangentMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) *ᵥ gLI h K ω E₀ θ) := by
  have hg := (H.xiL_props hS).2.2.2 θ hθ
  rw [invarianceError, invarianceError, H.fderiv_Kb hS hθ, newK_of_mem hθ,
    ContinuousLinearMap.comp_apply, _root_.add_apply, ContinuousLinearMap.id_apply,
    newOmega_c, map_smul (fderiv ℂ (xiLI h K ω E₀) θ), hg, tangentMat, colMat_mulVec]
  simp only [map_add, map_sub, map_smul]
  module

/-- `η̄ᴺ = (I + Dξᴸ)ᵀ (η̃ᴺ ∘ φ + (Ω_K̃ ∘ φ)(x ω - a g))`. -/
theorem etaNb_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    etaN h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ =
      (1 + dXiL h K ω E₀ θ)ᵀ *ᵥ (etaN h (tilK h K ω E₀) ω (θ + xiLI h K ω E₀ θ) +
        lagrangeMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) *ᵥ
          ((xw h K ω E₀ : ℂ) • (fun l => (ω l : ℂ)) -
            ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • gLI h K ω E₀ θ)) := by
  simp only [etaN, lagrangeMat]
  rw [H.Lb_eq hS hθ, H.Eb_eq hS hθ, EW_eq]
  simp only [Matrix.transpose_mul, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mulVec_smul]
  module

/-- The columns of `Dξᴸ` on `T_{r-3δ}`: `|∂_j ξᴸ| ≤ C_ξL X`. -/
theorem dXiL_entry {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) (i j : Fin n) :
    ‖fderiv ℂ (xiLI h K ω E₀) θ (Pi.single j 1) i‖ ≤ sCxiL p * xX p γ εL εN δ := by
  have hθ' : θ ∈ complexStrip n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  have hc := (cauchy_strip (H.xiL_props hS).1 (H.xiL_le hS) H.δ_pos).1 j θ hθ'
  refine (norm_le_pi_norm _ i).trans (hc.trans (le_of_eq ?_))
  rw [H.mu_div_gd]; field_simp [H.δ_pos.ne']

theorem dXiL_b {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    (∀ i, ∑ j, ‖fderiv ℂ (xiLI h K ω E₀) θ (Pi.single j 1) i‖ ≤ p.n * p.θξ) ∧
      ∀ j, ∑ i, ‖fderiv ℂ (xiLI h K ω E₀) θ (Pi.single j 1) i‖ ≤ p.n * p.θξ := by
  have he : ∀ i j, ‖fderiv ℂ (xiLI h K ω E₀) θ (Pi.single j 1) i‖ ≤ p.θξ := fun i j =>
    (H.dXiL_entry hS hθ i j).trans H.c_xiL
  constructor
  · intro i
    calc _ ≤ ∑ _j : Fin n, p.θξ := Finset.sum_le_sum fun j _ => he i j
      _ = p.n * p.θξ := by simp [H.pn]
  · intro j
    calc _ ≤ ∑ _i : Fin n, p.θξ := Finset.sum_le_sum fun i _ => he i j
      _ = p.n * p.θξ := by simp [H.pn]

theorem one_add_dXiL_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖1 + dXiL h K ω E₀ θ‖ ≤ 1 + p.n * p.θξ ∧ ‖(1 + dXiL h K ω E₀ θ)ᵀ‖ ≤ 1 + p.n * p.θξ := by
  have hb0 : 0 ≤ (p.n : ℝ) * p.θξ := mul_nonneg (Nat.cast_nonneg _) H.ok.ratios.2.2.1.le
  obtain ⟨hr, hc⟩ := H.dXiL_b hS hθ
  constructor
  · exact TorsionRef.norm_one_add_le hb0 fun i => by simpa [dXiL] using hr i
  · rw [Matrix.transpose_add, Matrix.transpose_one]
    exact TorsionRef.norm_one_add_le hb0 fun j => by
      simpa [dXiL, Matrix.transpose_apply] using hc j

/-- `|x ω - a g| ≤ (1 + a_ω) C_gL μ` on `T_{r-δ}`. -/
theorem v_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖(xw h K ω E₀ : ℂ) • (fun l => (ω l : ℂ)) -
      ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • gLI h K ω E₀ θ‖ ≤
      (1 + saw p) * (sCgL p * mu p γ εL εN δ) := fun θ hθ => by
  have hμ := H.mu_nonneg
  have h1 : ‖(xw h K ω E₀ : ℂ) • (fun l => (ω l : ℂ))‖ ≤ sCgL p * mu p γ εL εN δ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h0 : p.Θ * sC0 p ≤ sCgL p := by
      rw [sCgL]
      simp only [H.iso, ↓reduceIte]
      have := mul_nonneg (nn_st H.ok) (nn_sCxiN H.ok)
      have := H.ok.lam.1
      linarith
    calc _ ≤ sC0 p * mu p γ εL εN δ * p.Θ :=
          mul_le_mul (H.abs_xw_le hS) ((BorderSolve.norm_omega_le ω).trans H.Θ) (norm_nonneg _)
            (mul_nonneg (nn_sC0 H.ok) hμ)
      _ = (p.Θ * sC0 p) * mu p γ εL εN δ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h0 hμ
  have h2 : ‖((1 : ℂ) - (xw h K ω E₀ : ℂ)) • gLI h K ω E₀ θ‖ ≤
      saw p * (sCgL p * mu p γ εL εN δ) := by
    rw [norm_smul]
    exact mul_le_mul (H.abs_a_le hS) (H.gL_le hS θ hθ) (norm_nonneg _) (nn_saw H.ok)
  refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq (by ring)))

/-- Step `st-w`: `|η̄ᴺ| ≤ Q̄_N μ²/δ` on `T_{r-3δ}`. -/
theorem etaNb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖etaN h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ‖ ≤
      sQbN p * mu p γ εL εN δ ^ 2 / δ := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hφ := H.phi3 hS hθ
  have hφ1 : θ + xiLI h K ω E₀ θ ∈ complexStrip n (r - δ) :=
    strip_sub (by linarith [H.δ_pos]) hφ
  rw [H.etaNb_eq hS hθ2]
  have hD := (H.one_add_dXiL_le hS hθ).2
  have h1 := H.etaNt_le hS _ hφ1
  have hQ := nn_sQtN H.ok
  have hμ := H.mu_nonneg
  have hδ := H.δ_pos
  have ha0 := nn_saw H.ok
  have h2 : ‖lagrangeMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) *ᵥ
      ((xw h K ω E₀ : ℂ) • (fun l => (ω l : ℂ)) -
        ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • gLI h K ω E₀ θ)‖ ≤
      sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ) *
        ((1 + saw p) * (sCgL p * mu p γ εL εN δ)) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.omegaKt hS _ hφ) (H.v_le hS θ hθ1)
      (norm_nonneg _) (by
        have := nn_sCΩ H.ok; have := H.X_nonneg
        positivity))
  have hΩ : sCΩ p * sCgL p * xX p γ εL εN δ ≤ p.θΩ := H.c_Ω
  have e2 : sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ) *
      ((1 + saw p) * (sCgL p * mu p γ εL εN δ)) =
      (1 + saw p) * (sCΩ p * sCgL p * xX p γ εL εN δ) * (sQtN p * mu p γ εL εN δ ^ 2 / δ) := by
    ring
  rw [e2] at h2
  have hA : 0 ≤ sQtN p * mu p γ εL εN δ ^ 2 / δ := by positivity
  have h2' := h2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hΩ (by linarith)) hA)
  have h3 : ‖etaN h (tilK h K ω E₀) ω (θ + xiLI h K ω E₀ θ) +
      lagrangeMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) *ᵥ
        ((xw h K ω E₀ : ℂ) • (fun l => (ω l : ℂ)) -
          ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • gLI h K ω E₀ θ)‖ ≤
      (1 + (1 + saw p) * p.θΩ) * (sQtN p * mu p γ εL εN δ ^ 2 / δ) :=
    (norm_add_le _ _).trans ((add_le_add h1 h2').trans (le_of_eq (by ring)))
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ((mul_le_mul hD h3 (norm_nonneg _)
    (by have := H.ok.ratios.2.2.1; positivity)).trans (le_of_eq ?_))
  rw [sQbN]
  simp only [H.iso, ↓reduceIte]
  ring

/-! ### The new tangential error -/

/-- Step `st-l`: `Nᵀ Ω₀ Ẽ_ω = (T ξᴺ - ηᴸ) + Nᵀ Ω₀ Δ²X + Ω_N ηᴺ`. -/
theorem NtO_Et_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - δ)) :
    ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (tilK h K ω E₀) ω θ) =
      (torsion h K ω θ *ᵥ xiNI h K ω E₀ θ - etaL h K ω θ) +
        (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ) +
          ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ) := by
  have hθr := H.sub1 hθ
  have hNd : DifferentiableAt ℂ (normalMat K) θ :=
    (H.N_props hS).1.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
  have hT := torsion_eq_mat h K ω hNd
  have hL : etaL h K ω θ = -(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h K ω θ)) := rfl
  rw [H.Et_eq hS θ hθ]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← hT]
  rw [show ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h K ω θ) =
    -etaL h K ω θ by rw [hL, neg_neg]]
  abel

/-- The decomposition of step `st-l`: everything first order cancels, up to `x g`. -/
theorem NtOEb_key {θ : Fin n → ℂ} (hθ2 : θ ∈ complexStrip n (r - 2 * δ))
    (hθ1 : θ ∈ complexStrip n (r - δ)) :
    ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ) =
      ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          (sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀)
            (θ + xiLI h K ω E₀ θ)) -
            sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) θ)) -
        ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          ((tangentMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) - tangentMat (tilK h K ω E₀) θ) *ᵥ
            gLI h K ω E₀ θ)) -
        ((1 : ℂ) - (xw h K ω E₀ : ℂ)) • (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          ((tangentMat (tilK h K ω E₀) θ - tangentMat K θ) *ᵥ gLI h K ω E₀ θ)) +
        (xw h K ω E₀ : ℂ) • gLI h K ω E₀ θ +
        (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ) +
          ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ) +
        (xw h K ω E₀ : ℂ) • (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
          ((tangentMat (tilK h K ω E₀) θ - tangentMat K θ) *ᵥ fun l => (ω l : ℂ))) := by
  have hθr := H.sub1 hθ1
  have hNOL := Identities.fi_NtOL K (H.gram θ hθr)
  set Y := (normalMat K θ)ᵀ * omegaZeroMatrix n with hY
  set g := gLI h K ω E₀ θ with hg
  set c : ℂ := (xw h K ω E₀ : ℂ) with hc
  set w : Fin n → ℂ := fun l => (ω l : ℂ) with hw
  have hYL : ∀ u : Fin n → ℂ, Y *ᵥ (tangentMat K θ *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, hNOL, Matrix.one_mulVec]
  have hg0 : g = (torsion h K ω θ *ᵥ xiNI h K ω E₀ θ - etaL h K ω θ) + c • w := by
    have e : g = torsion h K ω θ *ᵥ xiNI h K ω E₀ θ + isoXiOmega h K ω E₀ • w -
        etaL h K ω θ := rfl
    rw [e, H.xw_eq hS]
    abel
  have hA2 := H.NtO_Et_eq hS hθ1
  rw [H.Eb_eq hS hθ2, EW_eq θ]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_smul]
  rw [hYL g, hYL w]
  linear_combination (norm := module) hA2 - hg0

omit hS in
theorem Y_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖(normalMat K θ)ᵀ * omegaZeroMatrix n‖ ≤ p.sNt := by
  rw [norm_mul_omegaZeroMatrix]; exact H.Nt' θ (H.sub3 hθ)

theorem xiL_step {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖θ + xiLI h K ω E₀ θ - θ‖ ≤ sCxiL p * (δ * xX p γ εL εN δ) := by
  rw [add_sub_cancel_left, ← H.mu_div_gd]; exact H.xiL_le hS θ (H.sub32 hθ)

theorem c_le : ‖(xw h K ω E₀ : ℂ)‖ ≤ sC0 p * mu p γ εL εN δ := by
  rw [Complex.norm_real, Real.norm_eq_abs]; exact H.abs_xw_le hS

/-- `Ẽ_ω̄` is holomorphic on `T_{r-δ}`. -/
theorem EW_diff : DifferentiableOn ℂ
    (fun y => sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) y))
    (complexStrip n (r - δ)) := by
  have hEtd : DifferentiableOn ℂ (fun y => sumVec n (invarianceError h (tilK h K ω E₀) ω y))
      (complexStrip n (r - δ)) :=
    (sumVecIso n).differentiable.comp_differentiableOn
      (FrameAux.differentiableOn_invarianceError hS (H.Kt_holo hS) (H.Kt_mem𝔅 hS))
  have e : (fun y => sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) y)) =
      fun y => sumVec n (invarianceError h (tilK h K ω E₀) ω y) +
        (xw h K ω E₀ : ℂ) • (tangentMat (tilK h K ω E₀) y *ᵥ fun l => (ω l : ℂ)) :=
    funext fun y => EW_eq y
  rw [e]
  have hv : DifferentiableOn ℂ
      (fun y => tangentMat (tilK h K ω E₀) y *ᵥ fun l => (ω l : ℂ))
      (complexStrip n (r - δ)) :=
    (differentiableOn_tangentMat (H.Kt_holo hS)).matrix_mulVec (differentiableOn_const _)
  exact hEtd.fun_add ((differentiableOn_const _).fun_smul hv)

/-- The term `Nᵀ Ω₀ (Ẽ_ω̄ ∘ φ - Ẽ_ω̄)`. -/
theorem term_E {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
        (sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀)
          (θ + xiLI h K ω E₀ θ)) -
          sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) θ))‖ ≤
      n * p.sNt * sCEt p * sCxiL p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hδ := H.δ_pos
  have hθ2 := H.sub32 hθ
  have hs2 : r - δ - δ = r - 2 * δ := by ring
  have hC := mul_nonneg (nn_sCEt H.ok) H.mu_nonneg
  have hEW' : ∀ y ∈ complexStrip n (r - 2 * δ), ‖fderiv ℂ (fun y =>
      sumVec n (invarianceError h (tilK h K ω E₀) (newOmega h K ω E₀) y)) y‖ ≤
      n * δ⁻¹ * (sCEt p * mu p γ εL εN δ) := fun y hy =>
    (cauchy_strip (H.EW_diff hS) (H.EW_le hS) hδ).2 y (by rw [hs2]; exact hy)
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun y hy => (H.EW_diff hS).differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds
      (strip_sub (by linarith) hy))) hEW' (convex_complexStrip n (r - 2 * δ)) hθ2 (H.phi3 hS hθ)
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ((mul_le_mul (H.Y_le hθ) (hmvt.trans
    (mul_le_mul_of_nonneg_left (H.xiL_step hS hθ) (by positivity))) (norm_nonneg _)
    H.ok.caps.2.2.2.2.1.le).trans (le_of_eq ?_))
  have hδi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  calc _ = n * p.sNt * sCEt p * sCxiL p * (mu p γ εL εN δ * xX p γ εL εN δ) * (δ⁻¹ * δ) := by
        ring
    _ = _ := by rw [hδi, mul_one]

/-- The term `a Nᵀ Ω₀ (L̃ ∘ φ - L̃) g`. -/
theorem term_L1 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖((1 : ℂ) - (xw h K ω E₀ : ℂ)) • (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      ((tangentMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) - tangentMat (tilK h K ω E₀) θ) *ᵥ
        gLI h K ω E₀ θ))‖ ≤
      saw p * p.sNt * sCgL p * (n * sKt p * sCxiL p) * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hδ := H.δ_pos
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hs2 : r - δ - δ = r - 2 * δ := by ring
  have hLtd : DifferentiableOn ℂ (tangentMat (tilK h K ω E₀)) (complexStrip n (r - δ)) :=
    differentiableOn_tangentMat (H.Kt_holo hS)
  have hLt' : ∀ y ∈ complexStrip n (r - 2 * δ), ‖fderiv ℂ (tangentMat (tilK h K ω E₀)) y‖ ≤
      n * δ⁻¹ * sKt p :=
    fun y hy => (cauchy_strip hLtd (fun z hz => (H.Lt_le hS z hz).1) hδ).2 y
      (by rw [hs2]; exact hy)
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun y hy => hLtd.differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds
      (strip_sub (by linarith) hy))) hLt' (convex_complexStrip n (r - 2 * δ)) hθ2 (H.phi3 hS hθ)
  have hK0 := nn_sKt H.ok
  have hξ0 := nn_sCxiL H.ok
  have hX := H.X_nonneg
  rw [norm_smul]
  refine (mul_le_mul (H.abs_a_le hS) ((Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul (H.Y_le hθ) ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (hmvt.trans (mul_le_mul_of_nonneg_left (H.xiL_step hS hθ)
        (by positivity))) (H.gL_le hS θ hθ1) (norm_nonneg _) (by positivity))) (norm_nonneg _)
      H.ok.caps.2.2.2.2.1.le)) (norm_nonneg _) (nn_saw H.ok)).trans (le_of_eq ?_)
  have hδi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  calc _ = saw p * p.sNt * sCgL p * (n * sKt p * sCxiL p) *
        (mu p γ εL εN δ * xX p γ εL εN δ) * (δ⁻¹ * δ) := by ring
    _ = _ := by rw [hδi, mul_one]

/-- The term `a Nᵀ Ω₀ (L̃ - L) g`. -/
theorem term_L2 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖((1 : ℂ) - (xw h K ω E₀ : ℂ)) • (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      ((tangentMat (tilK h K ω E₀) θ - tangentMat K θ) *ᵥ gLI h K ω E₀ θ))‖ ≤
      saw p * p.sNt * sCgL p * (sg p * sCDLt p) * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hμ := H.mu_nonneg
  have hX := H.X_nonneg
  have hD := nn_sCDLt H.ok
  have hg := nn_sCgL H.ok
  have hsNt := H.ok.caps.2.2.2.2.1.le
  have ha := nn_saw H.ok
  have hL : sCDLt p * (mu p γ εL εN δ / δ) ≤ sCDLt p * (sg p * xX p γ εL εN δ) :=
    mul_le_mul_of_nonneg_left H.mu_div_δ_le hD
  rw [norm_smul]
  refine (mul_le_mul (H.abs_a_le hS) ((Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul (H.Y_le hθ) ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul ((H.Lt_sub_le hS θ hθ1).1.trans hL) (H.gL_le hS θ hθ1) (norm_nonneg _)
        (mul_nonneg hD (mul_nonneg (nn_sg H.ok) hX)))) (norm_nonneg _) hsNt)) (norm_nonneg _)
    ha).trans (le_of_eq (by ring))

/-- The term `x g`. -/
theorem term_x1 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖(xw h K ω E₀ : ℂ) • gLI h K ω E₀ θ‖ ≤
      sC0 p * sCgL p * sg1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hμ := H.mu_nonneg
  have hC := mul_nonneg (nn_sC0 H.ok) (nn_sCgL H.ok)
  rw [norm_smul]
  calc _ ≤ sC0 p * mu p γ εL εN δ * (sCgL p * mu p γ εL εN δ) :=
        mul_le_mul (H.c_le hS) (H.gL_le hS θ hθ1) (norm_nonneg _) (mul_nonneg (nn_sC0 H.ok) hμ)
    _ = sC0 p * sCgL p * mu p γ εL εN δ * mu p γ εL εN δ := by ring
    _ ≤ sC0 p * sCgL p * (sg1 p * xX p γ εL εN δ) * mu p γ εL εN δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H.mu_le hC) hμ
    _ = _ := by ring

/-- The term `x Nᵀ Ω₀ (L̃ - L) ω`. -/
theorem term_x2 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖(xw h K ω E₀ : ℂ) • (((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      ((tangentMat (tilK h K ω E₀) θ - tangentMat K θ) *ᵥ fun l => (ω l : ℂ)))‖ ≤
      sC0 p * p.sNt * sCDLt p * p.Θ * sg p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hμ := H.mu_nonneg
  have hX := H.X_nonneg
  have hD := nn_sCDLt H.ok
  have hsNt := H.ok.caps.2.2.2.2.1.le
  have hL : sCDLt p * (mu p γ εL εN δ / δ) ≤ sCDLt p * (sg p * xX p γ εL εN δ) :=
    mul_le_mul_of_nonneg_left H.mu_div_δ_le hD
  rw [norm_smul]
  refine (mul_le_mul (H.c_le hS) ((Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul (H.Y_le hθ) ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul ((H.Lt_sub_le hS θ hθ1).1.trans hL)
        ((BorderSolve.norm_omega_le ω).trans H.Θ) (norm_nonneg _)
        (mul_nonneg hD (mul_nonneg (nn_sg H.ok) hX)))) (norm_nonneg _) hsNt)) (norm_nonneg _)
    (mul_nonneg (nn_sC0 H.ok) hμ)).trans (le_of_eq (by ring))

/-- The term `Nᵀ Ω₀ Δ²X + Ω_N ηᴺ`. -/
theorem term_R {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ) +
        ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ‖ ≤
      (p.sNt * (p.M2 / 2) * sCKt p ^ 2 * sg1 p + p.sB ^ 2 * sCΩ p * sg p ^ 2) *
        (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hθr := H.sub3 hθ
  have hμ := H.mu_nonneg
  have hX := H.X_nonneg
  have hsNt := H.ok.caps.2.2.2.2.1.le
  have hgd := H.gd_le
  have hg0 := H.gd_pos.le
  have t1a : ‖((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω E₀ θ)‖ ≤
      p.sNt * (p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.Y_le hθ) (by
      rw [norm_sumVec]; exact H.taylor_le hS θ hθ1) (norm_nonneg _) hsNt)
  have t1b : ‖((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ‖ ≤
      p.sB ^ 2 * (sCΩ p * (mu p γ εL εN δ / δ)) * (γ * δ ^ p.κ * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.omegaN hS θ hθ1)
      ((H.ηN θ hθr).trans H.εN_le) (norm_nonneg _)
      (by have := nn_sCΩ H.ok; have := H.δ_pos; positivity))
  have B1 : p.sNt * (p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2) ≤
      p.sNt * (p.M2 / 2) * sCKt p ^ 2 * sg1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have hc0 : 0 ≤ p.sNt * (p.M2 / 2) * sCKt p ^ 2 := by
      have := H.ok.nonneg.2.1; positivity
    calc _ = p.sNt * (p.M2 / 2) * sCKt p ^ 2 * mu p γ εL εN δ * mu p γ εL εN δ := by ring
      _ ≤ p.sNt * (p.M2 / 2) * sCKt p ^ 2 * (sg1 p * xX p γ εL εN δ) * mu p γ εL εN δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H.mu_le hc0) hμ
      _ = _ := by ring
  have B2 : p.sB ^ 2 * (sCΩ p * (mu p γ εL εN δ / δ)) * (γ * δ ^ p.κ * mu p γ εL εN δ) ≤
      p.sB ^ 2 * sCΩ p * sg p ^ 2 * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have hc0 : 0 ≤ p.sB ^ 2 * sCΩ p := by have := nn_sCΩ H.ok; positivity
    have hsq : (γ * δ ^ p.κ) ^ 2 ≤ sg p ^ 2 := pow_le_pow_left₀ hg0 hgd 2
    rw [H.mu_div_δ]
    calc _ = p.sB ^ 2 * sCΩ p * (γ * δ ^ p.κ) ^ 2 * (mu p γ εL εN δ * xX p γ εL εN δ) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc0)
          (mul_nonneg hμ hX)
  refine (norm_add_le _ _).trans ((add_le_add (t1a.trans B1) (t1b.trans B2)).trans
    (le_of_eq (by ring)))

/-- `|Nᵀ Ω₀ Ē| ≤ Q'_L μ X` on `T_{r-3δ}`. -/
theorem NtOEb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ)‖ ≤
      sQL1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  rw [H.NtOEb_key hS hθ2 hθ1]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (H.term_E hS hθ) (H.term_L1 hS hθ)))
      (H.term_L2 hS hθ))) (H.term_x1 hS hθ))) (H.term_R hS hθ))) (H.term_x2 hS hθ))).trans
    (le_of_eq ?_)
  rw [sQL1]
  simp only [H.iso, ↓reduceIte, H.pn_real]
  ring

/-- `|Ē| ≤ C_Ē μ` on `T_{r-3δ}`. -/
theorem Eb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ‖ ≤
      sCEb p * mu p γ εL εN δ := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hφ1 : θ + xiLI h K ω E₀ θ ∈ complexStrip n (r - δ) :=
    strip_sub (by linarith [H.δ_pos]) (H.phi3 hS hθ)
  rw [← norm_sumVec, H.Eb_eq hS hθ2]
  have h2 : ‖((1 : ℂ) - (xw h K ω E₀ : ℂ)) •
      (tangentMat (tilK h K ω E₀) (θ + xiLI h K ω E₀ θ) *ᵥ gLI h K ω E₀ θ)‖ ≤
      saw p * (sKt p * (sCgL p * mu p γ εL εN δ)) := by
    rw [norm_smul]
    exact mul_le_mul (H.abs_a_le hS) ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (H.Lt_le hS _ hφ1).1 (H.gL_le hS θ hθ1) (norm_nonneg _) (nn_sKt H.ok)))
      (norm_nonneg _) (nn_saw H.ok)
  refine (norm_sub_le _ _).trans ((add_le_add (H.EW_le hS _ hφ1) h2).trans (le_of_eq ?_))
  rw [sCEb]
  ring

omit H hS in
/-- `η̄ᴸ = -Nᵀ Ω₀ Ē - (N̄ - N)ᵀ Ω₀ Ē`. -/
theorem etaLb_split (θ : Fin n → ℂ) :
    etaL h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ =
      -(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ)) -
      (((normalMat (newK h K ω E₀ (r - 2 * δ)) θ)ᵀ - (normalMat K θ)ᵀ) *
        omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ) := by
  rw [etaL, Matrix.sub_mul, Matrix.sub_mulVec]
  abel

/-- The crude bound of step `st-l`: `|η̄ᴸ| ≤ (Q'_L + C_N̄ᵀ C_Ē) μ X` on `T_{r-3δ}`. -/
theorem etaLb_crude : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖etaL h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ‖ ≤
      sQLc p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  intro θ hθ
  rw [etaLb_split θ]
  obtain ⟨⟨-, hN2⟩, -⟩ := H.Nb_sub_le hS θ hθ
  have h2 : ‖(((normalMat (newK h K ω E₀ (r - 2 * δ)) θ)ᵀ - (normalMat K θ)ᵀ) *
      omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ)‖ ≤
      sCNbT p * xX p γ εL εN δ * (sCEb p * mu p γ εL εN δ) := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
      (mul_nonneg (nn_sCNbT H.ok) H.X_nonneg))
    · rw [norm_mul_omegaZeroMatrix]; exact hN2
    · rw [norm_sumVec]; exact H.Eb_le hS θ hθ
  have h1 : ‖-(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h (newK h K ω E₀ (r - 2 * δ)) (newOmega h K ω E₀) θ))‖ ≤
      sQL1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    rw [norm_neg]; exact H.NtOEb_le hS θ hθ
  refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  rw [sQLc]; ring

end Hyp

end ModStepB

end KAM.Iso.Sharp2

end
