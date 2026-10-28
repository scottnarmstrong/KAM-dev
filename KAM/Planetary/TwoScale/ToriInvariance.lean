/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.ToriInvConj
public import KAM.Planetary.TwoScale.ToriInvLimit
public import KAM.Planetary.TwoScale.ToriLagr

/-!
# Two-scale KAM: invariance (`bpP:p3:invariance`)

The private conditional helper `tori_invariance_of_limit` for the local obligation `invariance`:
for `I₀ ∈ D₀`, `ω = ω(I₀)` and `φ(θ) = Φ(θ, ǐ(I₀))`, `d/dt φ(θ + tω) = X_H(φ(θ + tω))`. The finite
stage curves `γ_j(t) = ψ_j(θ + tω, I_*)` satisfy `γ_j' − X_H(γ_j) = Dψ_j ((ω, 0) − X_{H_j})`
(`conj_field`), with `‖Dψ_j‖ ≤ κ` uniformly (`psiR_fderiv_bound`) and `‖(ω, 0) − X_{H_j}‖ ≤ C Ê_j`
(`field_err`, with `ω = ω_j(ǐ_j(I₀))` the proved frequency identity and the three error terms of
P3b L137–141), so `‖γ_j' − X_H(γ_j)‖ ≤ κ C Ê_j → 0` uniformly (`stage_err_le`); the passage to the
limit is `curve_limit_field`. Design package P23-20.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}
  {is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)}
  {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φinf : Phase (a + b) → Phase (a + b)}

/-- `M R̂ ≤ γ₁/3` and `E ≤ Ê R̂ γ₁/3` (from `R̂ ≤ γ₁/(3 M K^{τ+1})`, `K ≥ 1`, `E ≤ Ê R̂² M`). -/
theorem stage_bound (H : KamHyp D sbar p h f) :
    p.M * rhoHat p ≤ p.γ₁ / 3 ∧ p.E ≤ eHat p * rhoHat p * (p.γ₁ / 3) := by
  have hK : 1 ≤ cutoff p := by
    have h6 := H.K_mul_s
    have hs0 := H.positive.2.1
    have hw := H.widths
    have hs1 : p.s < 1 := by linarith
    by_contra hlt
    push_neg at hlt
    nlinarith [H.K_pos]
  have hKp : 1 ≤ cutoff p ^ (p.τ + 1) := Real.one_le_rpow hK (by have := H.τ_pos; linarith)
  have hR := H.R_pos
  have hM := H.positive.2.2.2.2.1
  have h1 := H.R_le_γ₁
  have h2 : p.M * rhoHat p ≤ p.γ₁ / 3 := by
    have : p.M * rhoHat p ≤ p.M * cutoff p ^ (p.τ + 1) * rhoHat p := by
      have := mul_le_mul_of_nonneg_left hKp hM.le
      nlinarith
    linarith
  refine ⟨h2, ?_⟩
  have := H.E_le_M
  have he := H.eHat_nonneg
  calc p.E ≤ eHat p * rhoHat p ^ 2 * p.M := this
    _ = eHat p * rhoHat p * (p.M * rhoHat p) := by ring
    _ ≤ eHat p * rhoHat p * (p.γ₁ / 3) := by gcongr

/-- The scalar bound of the three error terms: `M ‖I − c‖ + E/δ ≤ C Ê`. -/
theorem stage_err_le (H : KamHyp D sbar p h f) {Rmax : ℝ} (hR : rhoHat p ≤ Rmax)
    {d : ℝ} (hd : d ≤ 20 * rhoHat p * eHat p) (hd0 : 0 ≤ d) :
    p.M * d + p.E / min (p.ρ / 2) (sbar / (4 * π)) ≤
      eHat p * (20 * p.γ₁ / 3 + p.γ₁ / 3 * (2 + 4 * π * Rmax / sbar)) := by
  obtain ⟨hMR, hER⟩ := stage_bound H
  have hρ := H.positive.2.2.1
  have hs0 := H.positive.2.1
  have hsb : 0 < sbar := by have := H.widths.1; linarith
  have hM := H.positive.2.2.2.2.1
  have hE := H.positive.2.2.2.1
  have hRh := H.R_pos
  have he := eHat_pos H
  have hRρ := H.R_le_ρ
  have hγ := H.γ₁_pos
  have h1 : p.M * d ≤ 20 * eHat p * (p.γ₁ / 3) := by
    calc p.M * d ≤ p.M * (20 * rhoHat p * eHat p) := by gcongr
      _ = 20 * eHat p * (p.M * rhoHat p) := by ring
      _ ≤ _ := by gcongr
  have hmin : p.E / min (p.ρ / 2) (sbar / (4 * π)) ≤
      p.E / (p.ρ / 2) + p.E / (sbar / (4 * π)) := by
    have hp1 : 0 ≤ p.E / (p.ρ / 2) := by positivity
    have hp2 : 0 ≤ p.E / (sbar / (4 * π)) := by positivity
    rcases min_choice (p.ρ / 2) (sbar / (4 * π)) with e | e <;> rw [e] <;> linarith
  have h2 : p.E / (p.ρ / 2) ≤ eHat p * (p.γ₁ / 3) * 2 := by
    rw [div_le_iff₀ (by positivity)]
    calc p.E ≤ eHat p * rhoHat p * (p.γ₁ / 3) := hER
      _ ≤ eHat p * p.ρ * (p.γ₁ / 3) := by gcongr
      _ = _ := by ring
  have h3 : p.E / (sbar / (4 * π)) ≤ eHat p * (p.γ₁ / 3) * (4 * π * Rmax / sbar) := by
    rw [div_le_iff₀ (by positivity)]
    calc p.E ≤ eHat p * rhoHat p * (p.γ₁ / 3) := hER
      _ ≤ eHat p * Rmax * (p.γ₁ / 3) := by gcongr
      _ = _ := by field_simp
  nlinarith

end KAM.Planetary

end
