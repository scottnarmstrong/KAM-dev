/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.Inter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The tangential correction by composition (step `stepI:p2s2:st-w`)

With `gᴸ = T ξᴺ + ω ξ^ω - ηᴸ` (`gLI`) and `ξᴸ = 𝓡 gᴸ` (`xiLI`):

* `gL_le`: `|gᴸ| ≤ C_gL μ` on `T_{r-δ}` (`⟨gᴸ⟩ = 0` by the bordered system);
* `xiL_le`, `xiL_small`: `|ξᴸ| ≤ C_ξL μ/(γ δ^κ) ≤ ϑ_ξ δ` on `T_{r-2δ}`; `xiL_props`;
* `phi_mem`: `θ + ξᴸ(θ) ∈ T_{a+δ}` for `θ ∈ T_a`, `a ≤ r - 2δ`;
* `Kb_holo`, `Kb_primary`, `Kb_real`: `K̄ = K̃ ∘ (id + ξᴸ)` is holomorphic, primary and real on
  `T_{r-2δ}`;
* `Kb_sub_le`, `Kb_mem`: `|K̄ - K| ≤ |L̃| |ξᴸ| + |K̃ - K| ≤ C_ΔK μ/(γ δ^κ) < β` (mean value
  inequality on the convex strip `T_{r-δ}`).
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

/-- `|gᴸ| ≤ C_gL μ` on `T_{r-δ}`. -/
theorem gL_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖gLI h K ω E₀ θ‖ ≤ sCgL p * mu p γ εL εN δ := by
  intro θ hθ
  have hξ := H.xiN_le hS θ hθ
  have h1 : ‖torsion h K ω θ *ᵥ xiNI h K ω E₀ θ‖ ≤ st p * (sCxiN p * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.T θ hθ) hξ (norm_nonneg _)
      (nn_st H.ok))
  have h2 : ‖isoXiOmega h K ω E₀ • (fun a => (ω a : ℂ))‖ ≤
      sC0 p * mu p γ εL εN δ * p.Θ := by
    rw [norm_smul]
    exact mul_le_mul (H.xw_le hS) ((BorderSolve.norm_omega_le ω).trans H.Θ) (norm_nonneg _)
      (mul_nonneg (nn_sC0 H.ok) H.mu_nonneg)
  have h3 : ‖etaL h K ω θ‖ ≤ p.lam * mu p γ εL εN δ := (H.ηL θ (H.sub1 hθ)).trans H.εL_le
  have e : gLI h K ω E₀ θ = torsion h K ω θ *ᵥ xiNI h K ω E₀ θ +
      isoXiOmega h K ω E₀ • (fun a => (ω a : ℂ)) - etaL h K ω θ := rfl
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3).trans
    (le_of_eq ?_))
  rw [sCgL]
  simp only [H.iso, ↓reduceIte]
  ring

/-- `ξᴸ` is holomorphic, periodic and real on `T_{r-2δ}`, and `∂_ω ξᴸ = gᴸ`. -/
theorem xiL_props : DifferentiableOn ℂ (xiLI h K ω E₀) (complexStrip n (r - 2 * δ)) ∧
    IsPeriodicOn (xiLI h K ω E₀) (r - 2 * δ) ∧ IsRealVec (xiLI h K ω E₀) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ), fderiv ℂ (xiLI h K ω E₀) θ (fun l => (ω l : ℂ)) =
      gLI h K ω E₀ θ := by
  obtain ⟨⟨-, -, -, -, -, hd, hp⟩, hdω, -, -, -, -, -, hr⟩ := H.bord hS
  exact ⟨hd, hp, hr, hdω⟩

/-- `|ξᴸ| ≤ C_ξL μ/(γ δ^κ)` on `T_{r-2δ}`. -/
theorem xiL_le : ∀ θ ∈ complexStrip n (r - 2 * δ),
    ‖xiLI h K ω E₀ θ‖ ≤ sCxiL p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
  intro θ hθ
  obtain ⟨⟨-, -, hgd, hgp, hg0, -, -⟩, -⟩ := H.bord hS
  have hθ' : θ ∈ complexStrip n (r - δ - δ) := by
    rw [show r - δ - δ = r - 2 * δ by ring]; exact hθ
  have h1 := H.cert.sol ω H.mem H.δ_lt_r1 _ (sCgL p * mu p γ εL εN δ) hgd hgp (H.gL_le hS) hg0
    θ hθ'
  have e : xiLI h K ω E₀ θ = cohR ω (gLI h K ω E₀) θ := by
    show (0 : Fin n → ℂ) + cohR ω (bordGL ω (isoBordData h K ω E₀)) θ = _
    rw [zero_add]
    rfl
  rw [e]
  refine h1.trans (le_of_eq ?_)
  rw [sCxiL, Real.rpow_neg H.δ_pos.le]
  field_simp

theorem xiL_small : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖xiLI h K ω E₀ θ‖ ≤ p.θξ * δ :=
  fun θ hθ => by
  refine (H.xiL_le hS θ hθ).trans ?_
  rw [H.mu_div_gd]
  calc sCxiL p * (δ * xX p γ εL εN δ) = (sCxiL p * xX p γ εL εN δ) * δ := by ring
    _ ≤ p.θξ * δ := mul_le_mul_of_nonneg_right H.c_xiL H.δ_pos.le

/-- `θ + ξᴸ(θ) ∈ T_{a+δ}` for `θ ∈ T_a`, `a ≤ r - 2δ` (`|ξᴸ| ≤ ϑ_ξ δ < δ`). -/
theorem phi_mem {a : ℝ} (ha : a ≤ r - 2 * δ) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n a) :
    θ + xiLI h K ω E₀ θ ∈ complexStrip n (a + δ) := by
  have hθ2 : θ ∈ complexStrip n (r - 2 * δ) := strip_sub ha hθ
  have hξ := H.xiL_small hS θ hθ2
  have hθξ := H.ok.ratios.2.2.2.1
  intro i
  have h1 : |(xiLI h K ω E₀ θ i).im| ≤ p.θξ * δ :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm _ i).trans hξ)
  have h2 : p.θξ * δ ≤ δ := by nlinarith [H.δ_pos]
  calc |((θ + xiLI h K ω E₀ θ) i).im| = |(θ i).im + (xiLI h K ω E₀ θ i).im| := by
        simp [Complex.add_im]
    _ ≤ |(θ i).im| + |(xiLI h K ω E₀ θ i).im| := abs_add_le _ _
    _ < a + δ := by linarith [hθ i]

/-! ### The new torus `K̄ = K̃ ∘ (id + ξᴸ)` -/

theorem phi_diffOn : DifferentiableOn ℂ (fun y => y + xiLI h K ω E₀ y)
    (complexStrip n (r - 2 * δ)) := differentiableOn_id.add (H.xiL_props hS).1

theorem Kb_holo : DifferentiableOn ℂ (newK h K ω E₀ (r - 2 * δ))
    (complexStrip n (r - 2 * δ)) := by
  have hmaps : Set.MapsTo (fun y => y + xiLI h K ω E₀ y) (complexStrip n (r - 2 * δ))
      (complexStrip n (r - δ)) := fun y hy => by
    have := H.phi_mem hS le_rfl hy
    rwa [show r - 2 * δ + δ = r - δ by ring] at this
  exact ((H.Kt_holo hS).comp (H.phi_diffOn hS) hmaps).congr fun y hy => newK_of_mem hy

theorem Kb_primary : IsPrimaryOnStrip (newK h K ω E₀ (r - 2 * δ)) (r - 2 * δ) := by
  intro θ hθ k
  have hθk : θ + (fun i => (k i : ℂ)) ∈ complexStrip n (r - 2 * δ) :=
    add_mem_complexStrip_of_im_eq_zero hθ fun j => by simp
  have hφ := H.phi_mem hS le_rfl hθ
  rw [show r - 2 * δ + δ = r - δ by ring] at hφ
  rw [newK_of_mem hθk, newK_of_mem hθ, periodic_int_shift (H.xiL_props hS).2.1 k hθ]
  have e : θ + (fun i => (k i : ℂ)) + xiLI h K ω E₀ θ =
      (θ + xiLI h K ω E₀ θ) + (fun i => (k i : ℂ)) := by abel
  rw [e, H.Kt_primary hS _ hφ k]

theorem Kb_real : IsRealOnReals (newK h K ω E₀ (r - 2 * δ)) := by
  intro x
  have hx : (fun i => (x i : ℂ)) ∈ complexStrip n (r - 2 * δ) :=
    ofReal_mem_complexStrip H.r2_pos x
  rw [newK_of_mem hx]
  set y : Fin n → ℝ := fun i => x i + (xiLI h K ω E₀ (fun i => (x i : ℂ)) i).re
  have hy : (fun i => (x i : ℂ)) + xiLI h K ω E₀ (fun i => (x i : ℂ)) = fun i => (y i : ℂ) := by
    funext i
    have him := (H.xiL_props hS).2.2.1 x i
    apply Complex.ext <;> simp [y, him]
  rw [hy]
  exact H.Kt_real hS y

/-- `|K̄ - K| ≤ C_ΔK μ/(γ δ^κ)` on `T_{r-2δ}`. -/
theorem Kb_sub_le : ∀ θ ∈ complexStrip n (r - 2 * δ),
    ‖newK h K ω E₀ (r - 2 * δ) θ - K θ‖ ≤ sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
  intro θ hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hφ := H.phi_mem hS le_rfl hθ
  rw [show r - 2 * δ + δ = r - δ by ring] at hφ
  rw [newK_of_mem hθ]
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun x hx => H.Kt_diffAt hS x hx) (fun x hx => by
      rw [← norm_colMat]; exact (H.Lt_le hS x hx).1) (convex_complexStrip n (r - δ)) hθ1 hφ
  rw [add_sub_cancel_left] at hmvt
  have h1 : ‖tilK h K ω E₀ (θ + xiLI h K ω E₀ θ) - tilK h K ω E₀ θ‖ ≤
      sKt p * (sCxiL p * (mu p γ εL εN δ / (γ * δ ^ p.κ))) :=
    hmvt.trans (mul_le_mul_of_nonneg_left (H.xiL_le hS θ hθ) (nn_sKt H.ok))
  have h2 : ‖tilK h K ω E₀ θ - K θ‖ ≤ sg p * sCKt p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
    refine (H.Kt_sub_le hS θ hθ1).trans ?_
    calc sCKt p * mu p γ εL εN δ ≤ sCKt p * (sg p * (mu p γ εL εN δ / (γ * δ ^ p.κ))) :=
          mul_le_mul_of_nonneg_left H.mu_le_g_mu_div (nn_sCKt H.ok)
      _ = _ := by ring
  calc _ = ‖(tilK h K ω E₀ (θ + xiLI h K ω E₀ θ) - tilK h K ω E₀ θ) +
        (tilK h K ω E₀ θ - K θ)‖ := by abel_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by rw [sCDK]; ring

theorem Kb_mem : ∀ θ ∈ complexStrip n (r - 2 * δ),
    newK h K ω E₀ (r - 2 * δ) θ ∈ Metric.ball (K θ) β := fun θ hθ => by
  rw [Metric.mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (H.Kb_sub_le hS θ hθ) ?_
  have := H.β_gt
  rw [mul_div_assoc']
  exact this

theorem Kb_mem𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), newK h K ω E₀ (r - 2 * δ) θ ∈ 𝔅 :=
  fun θ hθ => H.ball θ (strip_sub (by linarith [H.δ_pos]) hθ) (H.Kb_mem hS θ hθ)

end Hyp

end ModStepB

end KAM.Iso.Sharp2

end
