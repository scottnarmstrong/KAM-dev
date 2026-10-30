/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB.Inter
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The tangential correction by composition (step `step:p2s2:st-l`)

With `gᴸ = ηᴸ - T ξᴺ` (`= -triGL`) and `ξᴸ = -𝓡 gᴸ` (`modXiL = triXiL`):

* `gL_le`: `|gᴸ| ≤ C_gL μ` on `T_{r-δ}` (`⟨gᴸ⟩ = 0` by the choice of `ξᴺ₀`);
* `xiL_le`, `xiL_small`: `|ξᴸ| ≤ C_ξL μ/(γ δ^κ) ≤ ϑ_ξ δ` on `T_{r-2δ}`; `xiL_props`;
* `phi_mem`: `θ + ξᴸ(θ) ∈ T_{a+δ}` for `θ ∈ T_a`, `a ≤ r - 2δ`;
* `Kb_holo`, `Kb_primary`, `Kb_real`: `K̄ = K̃ ∘ (id + ξᴸ)` is holomorphic, primary and real on
  `T_{r-2δ}`;
* `Kb_sub_le`, `Kb_mem`: `K̄ - K = (K ∘ φ - K) + (N ξᴺ) ∘ φ`, so
  `|K̄ - K| ≤ σ_K |ξᴸ| + |K̃ - K| ≤ C_ΔK μ/(γ δ^κ) < β` (mean value inequality for `K` on the convex
  strip `T_{r-δ}`, where `|DK| ≤ σ_K`; SHARP2-DOMPLUS).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

namespace ModStepB

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

/-- `|gᴸ| ≤ C_gL μ` on `T_{r-δ}`. -/
theorem gL_le : ∀ θ ∈ complexStrip n (r - δ),
    ‖triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤ sCgL p * mu p γ εL εN δ := by
  intro θ hθ
  have hξ := H.xiN_le hS θ hθ
  rw [H.xiN_eq hS] at hξ
  have h1 : ‖torsion h K ω θ *ᵥ triXiN ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ‖ ≤
      st p * (sCxiN p * mu p γ εL εN δ) :=
    (Matrix.linfty_opNorm_mulVec _ _).trans (mul_le_mul (H.T θ hθ) hξ (norm_nonneg _)
      (nn_st H.ok))
  refine (norm_sub_le _ _).trans ((add_le_add h1 ((H.ηL θ (H.sub1 hθ)).trans H.εL_le)).trans
    (le_of_eq ?_))
  rw [sCgL]
  simp only [H.fix, Bool.false_eq_true, ↓reduceIte]
  ring

/-- `ξᴸ` is holomorphic, periodic and real on `T_{r-2δ}`, and `∂_ω ξᴸ = T ξᴺ - ηᴸ`. -/
theorem xiL_props : DifferentiableOn ℂ (modXiL h K ω) (complexStrip n (r - 2 * δ)) ∧
    IsPeriodicOn (modXiL h K ω) (r - 2 * δ) ∧ IsRealVec (modXiL h K ω) ∧
    ∀ θ ∈ complexStrip n (r - 2 * δ), fderiv ℂ (modXiL h K ω) θ (fun l => (ω l : ℂ)) =
      triGL ω (etaL h K ω) (etaN h K ω) (torsion h K ω) θ := by
  obtain ⟨-, -, -, -, -, hd, hp, -, hdω, hr, -, -⟩ := H.tri hS
  rw [H.xiL_eq hS]
  exact ⟨hd, hp, hr, hdω⟩

/-- `|ξᴸ| ≤ C_ξL μ/(γ δ^κ)` on `T_{r-2δ}`. -/
theorem xiL_le : ∀ θ ∈ complexStrip n (r - 2 * δ),
    ‖modXiL h K ω θ‖ ≤ sCxiL p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
  intro θ hθ
  obtain ⟨hg0, -, -, hgd, hgp, -⟩ := H.tri hS
  have hθ' : θ ∈ complexStrip n (r - δ - δ) := by
    rw [show r - δ - δ = r - 2 * δ by ring]; exact hθ
  have h1 := H.cert.sol ω H.mem H.δ_lt_r1 _ (sCgL p * mu p γ εL εN δ) hgd hgp (H.gL_le hS) hg0
    θ hθ'
  rw [H.xiL_eq hS]
  refine h1.trans (le_of_eq ?_)
  rw [sCxiL, Real.rpow_neg H.δ_pos.le]
  field_simp

theorem xiL_small : ∀ θ ∈ complexStrip n (r - 2 * δ), ‖modXiL h K ω θ‖ ≤ p.θξ * δ :=
  fun θ hθ => by
  refine (H.xiL_le hS θ hθ).trans ?_
  rw [H.mu_div_gd]
  calc sCxiL p * (δ * xX p γ εL εN δ) = (sCxiL p * xX p γ εL εN δ) * δ := by ring
    _ ≤ p.θξ * δ := mul_le_mul_of_nonneg_right H.c_xiL H.δ_pos.le

/-- `θ + ξᴸ(θ) ∈ T_{a+δ}` for `θ ∈ T_a`, `a ≤ r - 2δ` (`|ξᴸ| ≤ ϑ_ξ δ < δ`). -/
theorem phi_mem {a : ℝ} (ha : a ≤ r - 2 * δ) {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n a) :
    θ + modXiL h K ω θ ∈ complexStrip n (a + δ) := by
  have hθ2 : θ ∈ complexStrip n (r - 2 * δ) := strip_sub ha hθ
  have hξ := H.xiL_small hS θ hθ2
  have hθξ := H.ok.ratios.2.2.2.1
  intro i
  have h1 : |(modXiL h K ω θ i).im| ≤ p.θξ * δ :=
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm _ i).trans hξ)
  have h2 : p.θξ * δ ≤ δ := by nlinarith [H.δ_pos]
  calc |((θ + modXiL h K ω θ) i).im| = |(θ i).im + (modXiL h K ω θ i).im| := by
        simp [Complex.add_im]
    _ ≤ |(θ i).im| + |(modXiL h K ω θ i).im| := abs_add_le _ _
    _ < a + δ := by linarith [hθ i]

/-! ### The new torus `K̄ = K̃ ∘ (id + ξᴸ)` -/

theorem phi_diffOn : DifferentiableOn ℂ (fun y => y + modXiL h K ω y)
    (complexStrip n (r - 2 * δ)) := differentiableOn_id.add (H.xiL_props hS).1

theorem Kb_holo : DifferentiableOn ℂ (modNewton h K ω (r - 2 * δ))
    (complexStrip n (r - 2 * δ)) := by
  have hmaps : Set.MapsTo (fun y => y + modXiL h K ω y) (complexStrip n (r - 2 * δ))
      (complexStrip n (r - δ)) := fun y hy => by
    have := H.phi_mem hS le_rfl hy
    rwa [show r - 2 * δ + δ = r - δ by ring] at this
  exact ((H.Kt_holo hS).comp (H.phi_diffOn hS) hmaps).congr fun y hy => modNewton_of_mem hy

theorem Kb_primary : IsPrimaryOnStrip (modNewton h K ω (r - 2 * δ)) (r - 2 * δ) := by
  intro θ hθ k
  have hθk : θ + (fun i => (k i : ℂ)) ∈ complexStrip n (r - 2 * δ) :=
    add_mem_complexStrip_of_im_eq_zero hθ fun j => by simp
  have hφ := H.phi_mem hS le_rfl hθ
  rw [show r - 2 * δ + δ = r - δ by ring] at hφ
  rw [modNewton_of_mem hθk, modNewton_of_mem hθ, periodic_int_shift (H.xiL_props hS).2.1 k hθ]
  have e : θ + (fun i => (k i : ℂ)) + modXiL h K ω θ =
      (θ + modXiL h K ω θ) + (fun i => (k i : ℂ)) := by abel
  rw [e, H.Kt_primary hS _ hφ k]

theorem Kb_real : IsRealOnReals (modNewton h K ω (r - 2 * δ)) := by
  intro x
  have hx : (fun i => (x i : ℂ)) ∈ complexStrip n (r - 2 * δ) :=
    ofReal_mem_complexStrip H.r2_pos x
  rw [modNewton_of_mem hx]
  set y : Fin n → ℝ := fun i => x i + (modXiL h K ω (fun i => (x i : ℂ)) i).re
  have hy : (fun i => (x i : ℂ)) + modXiL h K ω (fun i => (x i : ℂ)) = fun i => (y i : ℂ) := by
    funext i
    have him := (H.xiL_props hS).2.2.1 x i
    apply Complex.ext <;> simp [y, him]
  rw [hy]
  exact H.Kt_real hS y

/-- `|K̄ - K| ≤ C_ΔK μ/(γ δ^κ)` on `T_{r-2δ}`. -/
theorem Kb_sub_le : ∀ θ ∈ complexStrip n (r - 2 * δ),
    ‖modNewton h K ω (r - 2 * δ) θ - K θ‖ ≤ sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
  intro θ hθ
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  have hφ := H.phi_mem hS le_rfl hθ
  rw [show r - 2 * δ + δ = r - δ by ring] at hφ
  rw [modNewton_of_mem hθ]
  -- `K̄ - K = (K ∘ φ - K) + (N ξᴺ) ∘ φ`; the segment `[θ, φ(θ)]` lies in `T_{r-δ}`, `|DK| ≤ σ_K`
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun x hx => H.K_diffAt x (H.sub1 hx)) (fun x hx => H.fderiv_le x (H.sub1 hx))
    (convex_complexStrip n (r - δ)) hθ1 hφ
  rw [add_sub_cancel_left] at hmvt
  have h1 : ‖K (θ + modXiL h K ω θ) - K θ‖ ≤
      p.sK * (sCxiL p * (mu p γ εL εN δ / (γ * δ ^ p.κ))) :=
    hmvt.trans (mul_le_mul_of_nonneg_left (H.xiL_le hS θ hθ) H.ok.caps.1.le)
  have h2 : ‖modKtilde h K ω (θ + modXiL h K ω θ) - K (θ + modXiL h K ω θ)‖ ≤
      sg p * sCKt p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by
    refine (H.Kt_sub_le hS _ hφ).trans ?_
    calc sCKt p * mu p γ εL εN δ ≤ sCKt p * (sg p * (mu p γ εL εN δ / (γ * δ ^ p.κ))) :=
          mul_le_mul_of_nonneg_left H.mu_le_g_mu_div (nn_sCKt H.ok)
      _ = _ := by ring
  calc _ = ‖(K (θ + modXiL h K ω θ) - K θ) +
        (modKtilde h K ω (θ + modXiL h K ω θ) - K (θ + modXiL h K ω θ))‖ := by abel_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := by rw [sCDK]; ring

theorem Kb_mem : ∀ θ ∈ complexStrip n (r - 2 * δ),
    modNewton h K ω (r - 2 * δ) θ ∈ Metric.ball (K θ) β := fun θ hθ => by
  rw [Metric.mem_ball, dist_eq_norm]
  refine lt_of_le_of_lt (H.Kb_sub_le hS θ hθ) ?_
  have := H.β_gt
  rw [mul_div_assoc']
  exact this

theorem Kb_mem𝔅 : ∀ θ ∈ complexStrip n (r - 2 * δ), modNewton h K ω (r - 2 * δ) θ ∈ 𝔅 :=
  fun θ hθ => H.ball θ (strip_sub (by linarith [H.δ_pos]) hθ) (H.Kb_mem hS θ hθ)

end Hyp

end ModStepB

end KAM.Sharp2

end
