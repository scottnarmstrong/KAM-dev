/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Sharp2.ModStepB.SelfCons
public import KAM.Iso.Linear.EnergyDefect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The new energy error (step `stepI:p2s2:st-e`)

With `K̃ = K + N ξᴺ` and `K̄ = K̃ ∘ φ`, `φ = id + ξᴸ`:

* `quadH_le`, `energyAverage_Kt_sub_eq`, `energyAverage_Kt_sub_le`: the last row of the bordered
  system, `⟨Y ξᴺ⟩ = -(⟨H ∘ K⟩ - E₀)`, cancels the first-order term, so
  `|⟨H ∘ K̃⟩ - E₀| ≤ (M_h2/2) C_K̃² μ²`;
* `fderiv_HKt_le`, `HKb_sub_le`: `|D(H ∘ K̃)| ≤ n (|η̃ᴺ| + Θ |Ω_K̃|)` on `T_{r-2δ}`, so
  `|H ∘ K̄ - H ∘ K̃| ≤ n Q̃_N ϑ_ξ (Θ C_Ω + g₁) μ X` on `T_{r-3δ}`;
* `energyAverage_Kb_sub_le`: `|⟨H ∘ K̄⟩ - E₀| ≤ Q_ω μ²/(γ δ^{κ+1})`.
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

/-- `DH(K)(N ξᴺ) = Y ξᴺ`. -/
theorem fderiv_h_normal {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - δ)) :
    fderiv ℂ h (K θ) ((sumVec n).symm (normalMat K θ *ᵥ xiNI h K ω E₀ θ)) =
      energyRow h K θ ⬝ᵥ xiNI h K ω E₀ θ := by
  have hθr := H.sub1 hθ
  have hd : DifferentiableAt ℂ h (K θ) :=
    hS.holo.differentiableAt (hS.isOpen.mem_nhds (H.K_mem θ hθr))
  have e := Energy.fderiv_frame_apply hd (H.K_diffAt θ hθr) 0 (xiNI h K ω E₀ θ)
  rw [frameMat, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, zero_add, map_zero,
    add_zero] at e
  exact e

/-- `|H ∘ K̃ - H ∘ K - Y ξᴺ| ≤ (M_h2/2) (C_K̃ μ)²` on `T_{r-δ}` (Taylor). -/
theorem quadH_le {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - δ)) :
    ‖h (tilK h K ω E₀ θ) - h (K θ) - energyRow h K θ ⬝ᵥ xiNI h K ω E₀ θ‖ ≤
      p.Mh2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2 := by
  have hθr := H.sub1 hθ
  have hm := H.Kt_mem hS θ hθ
  have hβ : 0 < β := H.β_pos
  have hseg : segment ℝ (K θ) (tilK h K ω E₀ θ) ⊆ 𝔅 :=
    ((convex_ball (K θ) β).segment_subset (Metric.mem_ball_self hβ) hm).trans (H.ball θ hθr)
  set w := (sumVec n).symm (normalMat K θ *ᵥ xiNI h K ω E₀ θ) with hw
  have ew : tilK h K ω E₀ θ = K θ + w := rfl
  have h1 := taylor_iteratedFDeriv hS.isOpen hS.holo (A := p.Mh2) H.d2H (z := K θ) (w := w)
    (by rw [← ew]; exact hseg)
  rw [H.fderiv_h_normal hS hθ] at h1
  rw [ew]
  refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    (by have := H.ok.nonneg.2.2.2.2.2.2.1; positivity))
  have := H.Kt_sub_le hS θ hθ
  rwa [ew, add_sub_cancel_left] at this

/-- `⟨H ∘ K̃⟩ - E₀ = ⟨H ∘ K̃ - H ∘ K - Y ξᴺ⟩`. -/
theorem energyAverage_Kt_sub_eq {M' : ℝ} (hS' : Setting n τ M' p.sK p.sB p.sT 𝔅 h ω γ₀) :
    avg (fun θ => h (tilK h K ω E₀ θ)) - (E₀ : ℂ) =
      avg (fun θ => h (tilK h K ω E₀ θ) - h (K θ) - energyRow h K θ ⬝ᵥ xiNI h K ω E₀ θ) := by
  have hr1 : 0 < r - δ := by linarith [H.three, H.δ_pos]
  have cKt : Continuous fun x : Fin n → ℝ => h (tilK h K ω E₀ fun i => (x i : ℂ)) :=
    Exactness.continuous_real_of_differentiableOn hr1
      (hS.holo.comp (H.Kt_holo hS) (H.Kt_mem𝔅 hS))
  have cK : Continuous fun x : Fin n → ℝ => h (K fun i => (x i : ℂ)) :=
    Exactness.continuous_real_of_differentiableOn H.r_pos (hS.holo.comp H.holo H.K_mem)
  have hYd : DifferentiableOn ℂ (fun θ => energyRow h K θ) (complexStrip n (r - δ)) :=
    (H.Y_props hS).1.mono H.sub1
  have cY : Continuous fun x : Fin n → ℝ =>
      energyRow h K (fun i => (x i : ℂ)) ⬝ᵥ xiNI h K ω E₀ fun i => (x i : ℂ) :=
    (Exactness.continuous_real_of_differentiableOn hr1 hYd).dotProduct
      (Exactness.continuous_real_of_differentiableOn hr1 (H.xiN_props hS).1)
  have e1 := avg_sub_of_continuous (f := fun θ => h (tilK h K ω E₀ θ) - h (K θ))
    (g := fun θ => energyRow h K θ ⬝ᵥ xiNI h K ω E₀ θ) (cKt.sub cK) cY
  have e2 := avg_sub_of_continuous (f := fun θ => h (tilK h K ω E₀ θ)) (g := fun θ => h (K θ))
    cKt cK
  have e3 := (energy_approx hS' H.r_pos H.holo H.primary H.real H.K_mem).1.2.2.2.2.1
  obtain ⟨-, -, -, hbY, -⟩ := H.bord hS
  rw [e1, e2, hbY, e3]
  ring

theorem energyAverage_Kt_sub_le {M' : ℝ} (hS' : Setting n τ M' p.sK p.sB p.sT 𝔅 h ω γ₀) :
    ‖avg (fun θ => h (tilK h K ω E₀ θ)) - (E₀ : ℂ)‖ ≤
      p.Mh2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2 := by
  rw [H.energyAverage_Kt_sub_eq hS hS']
  exact norm_torusAverage_le_of_strip_bound (by linarith [H.three, H.δ_pos])
    fun θ hθ => H.quadH_le hS hθ

/-- `|D(H ∘ K̃)| ≤ n (Q̃_N μ²/δ + Θ C_Ω Q̃_N X μ/δ)` on `T_{r-2δ}`. -/
theorem fderiv_HKt_le {M' : ℝ} (hS' : Setting n τ M' p.sK p.sB p.sT 𝔅 h ω γ₀)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 2 * δ)) :
    ‖fderiv ℂ (fun y => h (tilK h K ω E₀ y)) θ‖ ≤
      n * (sQtN p * mu p γ εL εN δ ^ 2 / δ +
        p.Θ * (sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ))) := by
  have hθ1 : θ ∈ complexStrip n (r - δ) := strip_sub (by linarith [H.δ_pos]) hθ
  refine (Energy.norm_fderiv_comp_le hS' (H.Kt_holo hS) (H.Kt_mem𝔅 hS) hθ1).trans
    (mul_le_mul_of_nonneg_left (add_le_add (H.etaNt_le hS θ hθ1)
      (mul_le_mul H.Θ (H.omegaKt hS θ hθ) (norm_nonneg _) H.ok.nonneg.2.2.2.2.1))
      (Nat.cast_nonneg _))

/-- `|H ∘ K̄ - H ∘ K̃| ≤ n Q̃_N ϑ_ξ (Θ C_Ω + g₁) μ X` on `T_{r-3δ}`. -/
theorem HKb_sub_le {M' : ℝ} (hS' : Setting n τ M' p.sK p.sB p.sT 𝔅 h ω γ₀)
    {θ : Fin n → ℂ} (hθ : θ ∈ complexStrip n (r - 3 * δ)) :
    ‖h (newK h K ω E₀ (r - 2 * δ) θ) - h (tilK h K ω E₀ θ)‖ ≤
      n * sQtN p * p.θξ * (p.Θ * sCΩ p + sg1 p) *
        (mu p γ εL εN δ * xX p γ εL εN δ) := by
  have hδ := H.δ_pos
  have hθ2 := H.sub32 hθ
  have hμ := H.mu_nonneg
  have hX := H.X_nonneg
  have hQ := nn_sQtN H.ok
  have hξ : 0 ≤ p.θξ := (norm_nonneg _).trans (H.xiL_small hS θ hθ2) |> fun h1 =>
    nonneg_of_mul_nonneg_left h1 hδ
  have hHKt : DifferentiableOn ℂ (fun y => h (tilK h K ω E₀ y)) (complexStrip n (r - δ)) :=
    hS.holo.comp (H.Kt_holo hS) (H.Kt_mem𝔅 hS)
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (fun y hy => hHKt.differentiableAt ((isOpen_complexStrip n (r - δ)).mem_nhds
      (strip_sub (by linarith) hy))) (fun y hy => H.fderiv_HKt_le hS hS' hy)
    (convex_complexStrip n (r - 2 * δ)) hθ2 (H.phi3 hS hθ)
  rw [newK_of_mem hθ2]
  rw [add_sub_cancel_left] at hmvt
  have hC0 : 0 ≤ (n : ℝ) * (sQtN p * mu p γ εL εN δ ^ 2 / δ +
      p.Θ * (sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ))) := by
    have := H.ok.nonneg.2.2.2.2.1
    have := nn_sCΩ H.ok
    positivity
  refine (hmvt.trans (mul_le_mul_of_nonneg_left (H.xiL_small hS θ hθ2) hC0)).trans ?_
  have hδi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have e : (n : ℝ) * (sQtN p * mu p γ εL εN δ ^ 2 / δ +
      p.Θ * (sCΩ p * sQtN p * xX p γ εL εN δ * (mu p γ εL εN δ / δ))) * (p.θξ * δ) =
      n * sQtN p * p.θξ * (mu p γ εL εN δ * (mu p γ εL εN δ +
        p.Θ * sCΩ p * xX p γ εL εN δ)) * (δ⁻¹ * δ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  rw [e, hδi, mul_one]
  have hc : 0 ≤ (n : ℝ) * sQtN p * p.θξ := by positivity
  calc _ ≤ (n : ℝ) * sQtN p * p.θξ * (mu p γ εL εN δ * (sg1 p * xX p γ εL εN δ +
        p.Θ * sCΩ p * xX p γ εL εN δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (add_le_add_left H.mu_le _) hμ) hc
    _ = _ := by ring

/-- `|⟨H ∘ K̄⟩ - E₀| ≤ Q_ω μ²/(γ δ^{κ+1})`. -/
theorem energyAverage_Kb_sub_le :
    ‖KAM.Iso.energyAverage h (newK h K ω E₀ (r - 2 * δ)) - (E₀ : ℂ)‖ ≤
      sQw p * mu p γ εL εN δ ^ 2 / (γ * δ ^ (p.κ + 1)) := by
  obtain ⟨M', hS'⟩ := H.setting hS
  have hδ := H.δ_pos
  have hr2 : 0 < r - 2 * δ := by linarith [H.three]
  have hr1 : 0 < r - δ := by linarith [H.three]
  have hr3 : 0 < r - 3 * δ := by linarith [H.three]
  have hμ := H.mu_nonneg
  have hX := H.X_nonneg
  have eKb := (energy_approx hS' hr2 (H.Kb_holo hS) (H.Kb_primary hS) (H.Kb_real hS)
    (H.Kb_mem𝔅 hS)).1.2.2.2.2.1
  have cKb : Continuous fun x : Fin n → ℝ => h (newK h K ω E₀ (r - 2 * δ) fun i => (x i : ℂ)) :=
    Exactness.continuous_real_of_differentiableOn hr2
      (hS.holo.comp (H.Kb_holo hS) (H.Kb_mem𝔅 hS))
  have cKt : Continuous fun x : Fin n → ℝ => h (tilK h K ω E₀ fun i => (x i : ℂ)) :=
    Exactness.continuous_real_of_differentiableOn hr1
      (hS.holo.comp (H.Kt_holo hS) (H.Kt_mem𝔅 hS))
  have h1 : ‖avg (fun θ => h (newK h K ω E₀ (r - 2 * δ) θ)) -
      avg (fun θ => h (tilK h K ω E₀ θ))‖ ≤
      n * sQtN p * p.θξ * (p.Θ * sCΩ p + sg1 p) * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    rw [← avg_sub_of_continuous (f := fun θ => h (newK h K ω E₀ (r - 2 * δ) θ))
      (g := fun θ => h (tilK h K ω E₀ θ)) cKb cKt]
    exact norm_torusAverage_le_of_strip_bound hr3 fun θ hθ => H.HKb_sub_le hS hS' hθ
  have h2 := H.energyAverage_Kt_sub_le hS hS'
  have h3 : p.Mh2 / 2 * (sCKt p * mu p γ εL εN δ) ^ 2 ≤
      p.Mh2 / 2 * sCKt p ^ 2 * sg1 p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    have hc : 0 ≤ p.Mh2 / 2 * sCKt p ^ 2 := by
      have := H.ok.nonneg.2.2.2.2.2.2.1; positivity
    calc _ = p.Mh2 / 2 * sCKt p ^ 2 * mu p γ εL εN δ * mu p γ εL εN δ := by ring
      _ ≤ p.Mh2 / 2 * sCKt p ^ 2 * (sg1 p * xX p γ εL εN δ) * mu p γ εL εN δ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left H.mu_le hc) hμ
      _ = _ := by ring
  have e : sQw p * mu p γ εL εN δ ^ 2 / (γ * δ ^ (p.κ + 1)) =
      sQw p * (mu p γ εL εN δ * xX p γ εL εN δ) := by
    rw [xX]; ring
  have hpn' : (p.n : ℝ) = n := by rw [H.pn]
  rw [e, ← eKb, sQw, hpn']
  calc _ = ‖(avg (fun θ => h (newK h K ω E₀ (r - 2 * δ) θ)) -
        avg (fun θ => h (tilK h K ω E₀ θ))) +
        (avg (fun θ => h (tilK h K ω E₀ θ)) - (E₀ : ℂ))‖ := by abel_nf
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 (h2.trans h3))
    _ = _ := by ring

end Hyp

end ModStepB

end KAM.Iso.Sharp2

end
