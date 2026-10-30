/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB.Frames
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The new errors (steps `step:p2s2:st-e`, `step:p2s2:st-etal`)

With `φ = id + ξᴸ`, `g = T ξᴺ - ηᴸ = ∂_ω ξᴸ` (`triGL`), at `θ ∈ T_{r-2δ}`:

* `Lb_eq`: `L̄ = (L̃ ∘ φ)(I + Dξᴸ)` (chain rule);
* `Eb_eq`: `Ē = Ẽ ∘ φ - (L̃ ∘ φ) g`;
* `etaNb_eq`: `η̄ᴺ = (I + Dξᴸ)ᵀ (η̃ᴺ ∘ φ - (Ω_K̃ ∘ φ) g)`;

and on `T_{r-3δ}`:

* `etaNb_le`: `|η̄ᴺ| ≤ Q̄_N μ²/δ` (FH24 (3.80); `|(Dξᴸ)ᵀ| ≤ n C_ξL X ≤ n ϑ_ξ`,
  `C_Ω C_gL X ≤ ϑ_Ω`);
* `NtOEb_le`: `|Nᵀ Ω₀ Ē| ≤ Q'_L μ X`, from
  `Nᵀ Ω₀ Ē = Nᵀ Ω₀ (Ẽ∘φ - Ẽ) + (Nᵀ Ω₀ Δ²X + Ω_N ηᴺ) - Nᵀ Ω₀ (L̃∘φ - L̃) g - Nᵀ Ω₀ (L̃ - L) g`
  (the terms `ηᴸ - T ξᴺ` cancel against `g`; FH24 (3.81));
* `Eb_le`: `|Ē| ≤ C_Ē μ`; `etaLb_crude`: `|η̄ᴸ| ≤ (Q'_L + C_N̄ᵀ C_Ē) μ X`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

namespace ModStepB

/-- `L_{F∘φ} = (L_F ∘ φ)(I + Dξ)` for `φ = id + ξ`. -/
theorem tangentMat_comp_eq {F : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ξ : (Fin n → ℂ) → (Fin n → ℂ)} {θ : Fin n → ℂ} (hF : DifferentiableAt ℂ F (θ + ξ θ))
    (hξ : DifferentiableAt ℂ ξ θ) :
    tangentMat (fun y => F (y + ξ y)) θ =
      tangentMat F (θ + ξ θ) * (1 + Matrix.of fun i j => fderiv ℂ ξ θ (Pi.single j 1) i) := by
  set V : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := ContinuousLinearMap.id ℂ _ + fderiv ℂ ξ θ with hV
  have hφ : HasFDerivAt (fun y => y + ξ y) V θ := (hasFDerivAt_id θ).add hξ.hasFDerivAt
  have hcomp : HasFDerivAt (fun y => F (y + ξ y)) ((fderiv ℂ F (θ + ξ θ)).comp V) θ :=
    hF.hasFDerivAt.comp θ hφ
  rw [tangentMat, hcomp.fderiv, TorsionRef.colMat_comp]
  congr 1
  ext i j
  rw [LinearMap.toMatrix'_apply, Matrix.add_apply]
  simp only [Matrix.of_apply, hV, ContinuousLinearMap.coe_coe, _root_.add_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.single_apply, Matrix.one_apply]

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `Dξᴸ` as a matrix. -/
abbrev dXiL (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => fderiv ℂ (modXiL h K ω) θ (Pi.single j 1) i

theorem phi2 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    θ + modXiL h K ω θ ∈ complexStrip n (r - δ) := by
  have := H.phi_mem hS le_rfl hθ
  rwa [show r - 2 * δ + δ = r - δ by ring] at this

theorem phi3 {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    θ + modXiL h K ω θ ∈ complexStrip n (r - 2 * δ) := by
  have := H.phi_mem hS (by linarith [H.δ_pos]) hθ
  rwa [show r - 3 * δ + δ = r - 2 * δ by ring] at this

theorem xiL_diffAt {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    DifferentiableAt ℂ (modXiL h K ω) θ :=
  (H.xiL_props hS).1.differentiableAt ((isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ)

/-- The derivative of `K̄` near `θ ∈ T_{r-2δ}` is that of `K̃ ∘ φ`. -/
theorem fderiv_Kb {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    fderiv ℂ (modNewton h K ω (r - 2 * δ)) θ =
      (fderiv ℂ (modKtilde h K ω) (θ + modXiL h K ω θ)).comp
        (ContinuousLinearMap.id ℂ _ + fderiv ℂ (modXiL h K ω) θ) := by
  rw [(modNewton_eventuallyEq hθ).fderiv_eq]
  exact ((H.Kt_diffAt hS _ (H.phi2 hS hθ)).hasFDerivAt.comp θ
    ((hasFDerivAt_id θ).add (H.xiL_diffAt hS hθ).hasFDerivAt)).fderiv

/-- `L̄ = (L̃ ∘ φ)(I + Dξᴸ)`. -/
theorem Lb_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    tangentMat (modNewton h K ω (r - 2 * δ)) θ =
      tangentMat (modKtilde h K ω) (θ + modXiL h K ω θ) * (1 + dXiL h K ω θ) := by
  have e : tangentMat (modNewton h K ω (r - 2 * δ)) θ =
      tangentMat (fun y => modKtilde h K ω (y + modXiL h K ω y)) θ := by
    rw [tangentMat, tangentMat, (modNewton_eventuallyEq hθ).fderiv_eq]
  rw [e, tangentMat_comp_eq (H.Kt_diffAt hS _ (H.phi2 hS hθ)) (H.xiL_diffAt hS hθ)]

/-- `Ē = Ẽ ∘ φ - (L̃ ∘ φ) g`. -/
theorem Eb_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ) =
      sumVec n (invarianceError h (modKtilde h K ω) ω (θ + modXiL h K ω θ)) -
        tangentMat (modKtilde h K ω) (θ + modXiL h K ω θ) *ᵥ
          triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ := by
  rw [invarianceError, invarianceError, H.fderiv_Kb hS hθ, modNewton_of_mem hθ,
    ContinuousLinearMap.comp_apply, _root_.add_apply, ContinuousLinearMap.id_apply,
    (H.xiL_props hS).2.2.2 θ hθ, map_add, tangentMat, colMat_mulVec, map_sub, map_sub,
    map_add]
  abel

/-- `η̄ᴺ = (I + Dξᴸ)ᵀ (η̃ᴺ ∘ φ - (Ω_K̃ ∘ φ) g)`. -/
theorem etaNb_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    etaN h (modNewton h K ω (r - 2 * δ)) ω θ =
      (1 + dXiL h K ω θ)ᵀ *ᵥ (etaN h (modKtilde h K ω) ω (θ + modXiL h K ω θ) -
        lagrangeMat (modKtilde h K ω) (θ + modXiL h K ω θ) *ᵥ
          triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) := by
  simp only [etaN, lagrangeMat]
  rw [H.Lb_eq hS hθ, H.Eb_eq hS hθ]
  simp only [Matrix.transpose_mul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The columns of `Dξᴸ` on `T_{r-3δ}`: `|∂_j ξᴸ| ≤ C_ξL X`. -/
theorem dXiL_entry {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) (i j : Fin n) :
    ‖fderiv ℂ (modXiL h K ω) θ (Pi.single j 1) i‖ ≤ sCxiL p * xX p γ εL εN δ := by
  have hθ' : θ ∈ complexStrip n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  have hc := (cauchy_strip (H.xiL_props hS).1 (H.xiL_le hS) H.δ_pos).1 j θ hθ'
  refine (norm_le_pi_norm _ i).trans (hc.trans (le_of_eq ?_))
  rw [H.mu_div_gd]; field_simp [H.δ_pos.ne']

theorem dXiL_b {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    (∀ i, ∑ j, ‖fderiv ℂ (modXiL h K ω) θ (Pi.single j 1) i‖ ≤ p.n * p.θξ) ∧
      ∀ j, ∑ i, ‖fderiv ℂ (modXiL h K ω) θ (Pi.single j 1) i‖ ≤ p.n * p.θξ := by
  have he : ∀ i j, ‖fderiv ℂ (modXiL h K ω) θ (Pi.single j 1) i‖ ≤ p.θξ := fun i j =>
    (H.dXiL_entry hS hθ i j).trans H.c_xiL
  constructor
  · intro i
    calc _ ≤ ∑ _j : Fin n, p.θξ := Finset.sum_le_sum fun j _ => he i j
      _ = p.n * p.θξ := by simp [H.pn]
  · intro j
    calc _ ≤ ∑ _i : Fin n, p.θξ := Finset.sum_le_sum fun i _ => he i j
      _ = p.n * p.θξ := by simp [H.pn]

theorem one_add_dXiL_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖1 + dXiL h K ω θ‖ ≤ 1 + p.n * p.θξ ∧ ‖(1 + dXiL h K ω θ)ᵀ‖ ≤ 1 + p.n * p.θξ := by
  have hb0 : 0 ≤ (p.n : ℝ) * p.θξ := mul_nonneg (Nat.cast_nonneg _) H.ok.ratios.2.2.1.le
  obtain ⟨hr, hc⟩ := H.dXiL_b hS hθ
  constructor
  · exact TorsionRef.norm_one_add_le hb0 fun i => by simpa [dXiL] using hr i
  · rw [Matrix.transpose_add, Matrix.transpose_one]
    exact TorsionRef.norm_one_add_le hb0 fun j => by
      simpa [dXiL, Matrix.transpose_apply] using hc j

/-- `bp:p2s2:step`, step `st-e`: `|η̄ᴺ| ≤ Q̄_N μ²/δ` on `T_{r-3δ}`. -/
theorem etaNb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖etaN h (modNewton h K ω (r - 2 * δ)) ω θ‖ ≤ sQbN p * mu p γ εL εN δ ^ 2 / δ := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hφ := H.phi3 hS hθ
  have hφ1 : θ + modXiL h K ω θ ∈ complexStrip n (r - δ) :=
    strip_sub (by linarith [H.δ_pos]) hφ
  rw [H.etaNb_eq hS hθ2]
  have hD := (H.one_add_dXiL_le hS hθ).2
  have h1 := H.etaNt_le hS _ hφ1
  have h2 : ‖lagrangeMat (modKtilde h K ω) (θ + modXiL h K ω θ) *ᵥ
      triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
      sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ) * (sCgL p * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.omegaKt hS _ hφ) (H.gL_le hS θ hθ1)
      (norm_nonneg _) (by
        have := nn_sCΩ H.ok; have := nn_sQtN H.ok; have := H.X_nonneg; have := H.mu_nonneg
        have := H.δ_pos; positivity))
  have hQ := nn_sQtN H.ok
  have hμ := H.mu_nonneg
  have hδ := H.δ_pos
  have hΩ : sCΩ p * sCgL p * xX p γ εL εN δ ≤ p.θΩ := H.c_Ω
  have e2 : sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ) * (sCgL p * mu p γ εL εN δ) =
      (sCΩ p * sCgL p * xX p γ εL εN δ) * (sQtN p * mu p γ εL εN δ ^ 2 / δ) := by ring
  rw [e2] at h2
  have hA : 0 ≤ sQtN p * mu p γ εL εN δ ^ 2 / δ := by positivity
  have h3 : ‖etaN h (modKtilde h K ω) ω (θ + modXiL h K ω θ) -
      lagrangeMat (modKtilde h K ω) (θ + modXiL h K ω θ) *ᵥ
        triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
      (1 + p.θΩ) * (sQtN p * mu p γ εL εN δ ^ 2 / δ) :=
    (norm_sub_le _ _).trans ((add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_right hΩ hA))).trans
      (le_of_eq (by ring)))
  refine (Matrix.linfty_opNorm_mulVec _ _).trans ((mul_le_mul hD h3 (norm_nonneg _)
    (by have := H.ok.ratios.2.2.1; positivity)).trans (le_of_eq ?_))
  rw [sQbN]
  simp only [H.fix, Bool.false_eq_true, ↓reduceIte]
  ring

/-! ### The new tangential error -/

/-- The identity of step `st-etal` (i): `Nᵀ Ω₀ Ẽ - Nᵀ Ω₀ L g = Nᵀ Ω₀ Δ²X + Ω_N ηᴺ`. -/
theorem NtO_Et_eq {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - δ)) :
    ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (modKtilde h K ω) ω θ) -
      ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ (tangentMat K θ *ᵥ
        triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ) =
      ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (taylorRem h K ω θ) +
        ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ := by
  have hθr := H.sub1 hθ
  have hNd : DifferentiableAt ℂ (normalMat K) θ :=
    (H.N_props hS).1.differentiableAt ((isOpen_complexStrip n r).mem_nhds hθr)
  have hT := torsion_eq_mat h K ω hNd
  have hNOL := Identities.fi_NtOL K (H.gram θ hθr)
  have hL : etaL h K ω θ = -(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h K ω θ)) := rfl
  rw [H.Et_eq hS θ hθ, Matrix.mulVec_mulVec, hNOL, Matrix.one_mulVec]
  simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← hT]
  rw [triGL, ← H.xiN_eq hS]
  rw [show ((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h K ω θ) =
    -etaL h K ω θ by rw [hL, neg_neg]]
  abel

/-- `|Nᵀ Ω₀ Ē| ≤ Q'_L μ X` on `T_{r-3δ}` (FH24 (3.81), without the frame increment). -/
theorem NtOEb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ)‖ ≤
      sQL1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hθr := H.sub3 hθ
  have hφ := H.phi3 hS hθ
  set Y := (normalMat K θ)ᵀ * omegaZeroMatrix n with hY
  set g := triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ with hg
  set φθ := θ + modXiL h K ω θ with hφθ
  set Et := fun y => sumVec n (invarianceError h (modKtilde h K ω) ω y) with hEt
  set Lt := tangentMat (modKtilde h K ω) with hLt
  have key : Y *ᵥ sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ) =
      Y *ᵥ (Et φθ - Et θ) + (Y *ᵥ sumVec n (taylorRem h K ω θ) +
        ((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ) -
        Y *ᵥ ((Lt φθ - Lt θ) *ᵥ g) - Y *ᵥ ((Lt θ - tangentMat K θ) *ᵥ g) := by
    rw [H.Eb_eq hS hθ2, ← H.NtO_Et_eq hS hθ1]
    simp only [Matrix.mulVec_sub, Matrix.sub_mulVec, hEt, hLt]
    abel
  rw [key]
  -- the five terms
  have hYn : ‖Y‖ ≤ p.sNt := by rw [hY, norm_mul_omegaZeroMatrix]; exact H.Nt' θ hθr
  have hsNt := H.ok.caps.2.2.2.2.1.le
  have hμ := H.mu_nonneg
  have hX := H.X_nonneg
  have hδ := H.δ_pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hξ : ‖φθ - θ‖ ≤ sCxiL p * (δ * xX p γ εL εN δ) := by
    rw [hφθ, add_sub_cancel_left, ← H.mu_div_gd]; exact H.xiL_le hS θ hθ2
  -- (ii) `Ẽ ∘ φ - Ẽ`: mean value inequality with Cauchy on `Ẽ`
  have hEtd : DifferentiableOn ℂ Et (complexStrip n (r - δ)) :=
    (sumVecIso n).differentiable.comp_differentiableOn
      (FrameAux.differentiableOn_invarianceError hS (H.Kt_holo hS) (H.Kt_mem𝔅 hS))
  have hEtb : ∀ y ∈ complexStrip n (r - δ), ‖Et y‖ ≤ sCEt p * mu p γ εL εN δ := fun y hy => by
    rw [hEt, norm_sumVec]; exact H.Et_le hS y hy
  have hs2 : r - δ - δ = r - 2 * δ := by ring
  have hEt' : ∀ y ∈ complexStrip n (r - 2 * δ), ‖fderiv ℂ Et y‖ ≤
      n * δ⁻¹ * (sCEt p * mu p γ εL εN δ) := fun y hy =>
    (cauchy_strip hEtd hEtb H.δ_pos).2 y (by rw [hs2]; exact hy)
  have hmvt1 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun y hy => hEtd.differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds
      (strip_sub (by linarith) hy))) hEt' (convex_complexStrip n (r - 2 * δ)) hθ2 hφ
  have t2 : ‖Y *ᵥ (Et φθ - Et θ)‖ ≤ p.sNt * (n * δ⁻¹ * (sCEt p * mu p γ εL εN δ) *
      (sCxiL p * (δ * xX p γ εL εN δ))) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hYn (hmvt1.trans
      (mul_le_mul_of_nonneg_left hξ (by have := nn_sCEt H.ok; positivity))) (norm_nonneg _)
      hsNt)
  -- (i) `Nᵀ Ω₀ Δ²X + Ω_N ηᴺ`
  have t1a : ‖Y *ᵥ sumVec n (taylorRem h K ω θ)‖ ≤
      p.sNt * (p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hYn (by
      rw [norm_sumVec]; exact H.taylor_le hS θ hθ1) (norm_nonneg _) hsNt)
  have t1b : ‖((normalMat K θ)ᵀ * omegaZeroMatrix n * normalMat K θ) *ᵥ etaN h K ω θ‖ ≤
      p.sB ^ 2 * (sCΩ p * (mu p γ εL εN δ / δ)) * (γ * δ ^ p.κ * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.omegaN hS θ hθ1)
      ((H.ηN θ hθr).trans H.εN_le) (norm_nonneg _)
      (by have := nn_sCΩ H.ok; positivity))
  -- (iii) `(L̃ ∘ φ - L̃) g` and `(L̃ - L) g`
  have hLtd : DifferentiableOn ℂ Lt (complexStrip n (r - δ)) :=
    differentiableOn_tangentMat (H.Kt_holo hS)
  have hLt' : ∀ y ∈ complexStrip n (r - 2 * δ), ‖fderiv ℂ Lt y‖ ≤ n * δ⁻¹ * sKt p :=
    fun y hy => (cauchy_strip hLtd (fun z hz => (H.Lt_le hS z hz).1) H.δ_pos).2 y
      (by rw [hs2]; exact hy)
  have hmvt2 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun y hy => hLtd.differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds
      (strip_sub (by linarith) hy))) hLt' (convex_complexStrip n (r - 2 * δ)) hθ2 hφ
  have hgb := H.gL_le hS θ hθ1
  have hgL0 := nn_sCgL H.ok
  have t3 : ‖Y *ᵥ ((Lt φθ - Lt θ) *ᵥ g)‖ ≤ p.sNt * (n * δ⁻¹ * sKt p *
      (sCxiL p * (δ * xX p γ εL εN δ)) * (sCgL p * mu p γ εL εN δ)) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hYn ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (hmvt2.trans (mul_le_mul_of_nonneg_left hξ
        (by have := nn_sKt H.ok; positivity))) hgb (norm_nonneg _)
        (by have := nn_sKt H.ok; have := nn_sCxiL H.ok; positivity))) (norm_nonneg _) hsNt)
  have t4 : ‖Y *ᵥ ((Lt θ - tangentMat K θ) *ᵥ g)‖ ≤
      p.sNt * (sCDLt p * (mu p γ εL εN δ / δ) * (sCgL p * mu p γ εL εN δ)) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul hYn ((Matrix.linfty_opNorm_mulVec _ _).trans
      (mul_le_mul (H.Lt_sub_le hS θ hθ1).1 hgb (norm_nonneg _)
        (by have := nn_sCDLt H.ok; positivity))) (norm_nonneg _) hsNt)
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add t2 ((norm_add_le _ _).trans (add_le_add t1a t1b))))
    t3)) t4) |>.trans ?_
  -- arithmetic: everything in units of `μ X`
  have eμ : mu p γ εL εN δ = γ * δ ^ (p.κ + 1) * xX p γ εL εN δ := H.mu_eq
  have eμδ : mu p γ εL εN δ / δ = γ * δ ^ p.κ * xX p γ εL εN δ := H.mu_div_δ
  have hgd := H.gd_le
  have hgd1 := H.gd1_le
  have hg0 := H.gd_pos.le
  have hδi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ H.δ_pos.ne'
  rw [eμδ]
  have A1 : p.sNt * (n * δ⁻¹ * (sCEt p * mu p γ εL εN δ) * (sCxiL p * (δ * xX p γ εL εN δ))) =
      n * p.sNt * sCEt p * sCxiL p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have : n * δ⁻¹ * (sCEt p * mu p γ εL εN δ) * (sCxiL p * (δ * xX p γ εL εN δ)) =
        n * sCEt p * sCxiL p * (mu p γ εL εN δ * xX p γ εL εN δ) * (δ⁻¹ * δ) := by ring
    rw [this, hδi]; ring
  have A3 : p.sNt * (n * δ⁻¹ * sKt p * (sCxiL p * (δ * xX p γ εL εN δ)) *
      (sCgL p * mu p γ εL εN δ)) =
      p.sNt * sCgL p * (n * sKt p * sCxiL p) * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have : n * δ⁻¹ * sKt p * (sCxiL p * (δ * xX p γ εL εN δ)) * (sCgL p * mu p γ εL εN δ) =
        sCgL p * (n * sKt p * sCxiL p) * (mu p γ εL εN δ * xX p γ εL εN δ) * (δ⁻¹ * δ) := by ring
    rw [this, hδi]; ring
  have B1 : p.sNt * (p.M2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2) ≤
      p.sNt * (p.M2 / 2) * sCKt p ^ 2 * sg1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have hc : 0 ≤ p.sNt * (p.M2 / 2) * sCKt p ^ 2 := by
      have := H.ok.nonneg.2.1; positivity
    calc _ = p.sNt * (p.M2 / 2) * sCKt p ^ 2 * mu p γ εL εN δ * mu p γ εL εN δ := by ring
      _ ≤ p.sNt * (p.M2 / 2) * sCKt p ^ 2 * (sg1 p * xX p γ εL εN δ) * mu p γ εL εN δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H.mu_le hc) hμ
      _ = _ := by ring
  have B2 : p.sB ^ 2 * (sCΩ p * (γ * δ ^ p.κ * xX p γ εL εN δ)) *
      (γ * δ ^ p.κ * mu p γ εL εN δ) ≤
      p.sB ^ 2 * sCΩ p * sg p ^ 2 * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have hc : 0 ≤ p.sB ^ 2 * sCΩ p := by have := nn_sCΩ H.ok; positivity
    have hsq : (γ * δ ^ p.κ) ^ 2 ≤ sg p ^ 2 := pow_le_pow_left₀ hg0 hgd 2
    calc _ = p.sB ^ 2 * sCΩ p * (γ * δ ^ p.κ) ^ 2 * (mu p γ εL εN δ * xX p γ εL εN δ) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc)
          (mul_nonneg hμ hX)
  have B4 : p.sNt * (sCDLt p * (γ * δ ^ p.κ * xX p γ εL εN δ) * (sCgL p * mu p γ εL εN δ)) ≤
      p.sNt * sCgL p * (sg p * sCDLt p) * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have hc : 0 ≤ p.sNt * sCgL p * sCDLt p := by have := nn_sCDLt H.ok; positivity
    calc _ = p.sNt * sCgL p * sCDLt p * (γ * δ ^ p.κ) * (mu p γ εL εN δ * xX p γ εL εN δ) := by
          ring
      _ ≤ p.sNt * sCgL p * sCDLt p * sg p * (mu p γ εL εN δ * xX p γ εL εN δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgd hc) (mul_nonneg hμ hX)
      _ = _ := by ring
  rw [A1, A3]
  have hfin : sQL1 p = p.sNt * (p.M2 / 2) * sCKt p ^ 2 * sg1 p + p.sB ^ 2 * sCΩ p * sg p ^ 2 +
      n * p.sNt * sCEt p * sCxiL p +
      p.sNt * sCgL p * (n * sKt p * sCxiL p + sg p * sCDLt p) := by
    rw [sQL1, saw]
    simp only [H.fix, Bool.false_eq_true, ↓reduceIte, H.pn_real]
    ring
  rw [hfin]
  nlinarith [B1, B2, B4]

/-- `|Ē| ≤ C_Ē μ` on `T_{r-3δ}`. -/
theorem Eb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ‖ ≤ sCEb p * mu p γ εL εN δ := by
  intro θ hθ
  have hθ2 := H.sub32 hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hφ1 : θ + modXiL h K ω θ ∈ complexStrip n (r - δ) :=
    strip_sub (by linarith [H.δ_pos]) (H.phi3 hS hθ)
  rw [← norm_sumVec, H.Eb_eq hS hθ2]
  have h1 : ‖sumVec n (invarianceError h (modKtilde h K ω) ω (θ + modXiL h K ω θ))‖ ≤
      sCEt p * mu p γ εL εN δ := by
    rw [norm_sumVec]; exact H.Et_le hS _ hφ1
  refine (norm_sub_le _ _).trans ((add_le_add h1
    ((Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.Lt_le hS _ hφ1).1 (H.gL_le hS θ hθ1)
      (norm_nonneg _) (nn_sKt H.ok)))).trans (le_of_eq ?_))
  rw [sCEb, saw]
  simp only [H.fix, Bool.false_eq_true, ↓reduceIte]
  ring

omit H hS in
/-- `η̄ᴸ = -Nᵀ Ω₀ Ē - (N̄ - N)ᵀ Ω₀ Ē`. -/
theorem etaLb_split (θ : Fin n → ℂ) :
    etaL h (modNewton h K ω (r - 2 * δ)) ω θ =
      -(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ)) -
      (((normalMat (modNewton h K ω (r - 2 * δ)) θ)ᵀ - (normalMat K θ)ᵀ) *
        omegaZeroMatrix n) *ᵥ
        sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ) := by
  rw [etaL, Matrix.sub_mul, Matrix.sub_mulVec]
  abel

/-- The crude bound of step `st-etal`: `|η̄ᴸ| ≤ (Q'_L + C_N̄ᵀ C_Ē) μ X` on `T_{r-3δ}`. -/
theorem etaLb_crude : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖etaL h (modNewton h K ω (r - 2 * δ)) ω θ‖ ≤
      sQLc p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
  intro θ hθ
  rw [etaLb_split θ]
  obtain ⟨⟨-, hN2⟩, -⟩ := H.Nb_sub_le hS θ hθ
  have h2 : ‖(((normalMat (modNewton h K ω (r - 2 * δ)) θ)ᵀ - (normalMat K θ)ᵀ) *
      omegaZeroMatrix n) *ᵥ sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ)‖ ≤
      sCNbT p * xX p γ εL εN δ * (sCEb p * mu p γ εL εN δ) := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
      (mul_nonneg (nn_sCNbT H.ok) H.X_nonneg))
    · rw [norm_mul_omegaZeroMatrix]; exact hN2
    · rw [norm_sumVec]; exact H.Eb_le hS θ hθ
  have h1 : ‖-(((normalMat K θ)ᵀ * omegaZeroMatrix n) *ᵥ
      sumVec n (invarianceError h (modNewton h K ω (r - 2 * δ)) ω θ))‖ ≤
      sQL1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    rw [norm_neg]; exact H.NtOEb_le hS θ hθ
  refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
  rw [sQLc]; ring

end Hyp

end ModStepB

end KAM.Sharp2

end
