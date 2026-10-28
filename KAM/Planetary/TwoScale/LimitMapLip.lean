/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMapPsi

/-!
# Two-scale KAM: rescaled Lipschitz bound for `Ψ_k − id` (`bpP:p3:psi-lip`, `stepP:p3:pl-lip`)

`lip_sup` is applied in the scaled coordinates `sc`/`unsc` (`N = 2n`) to the scaled displacement
`Δ = S (Ψ_{j+1} − id) S⁻¹` on the complex `ε_j`-neighbourhood of the real set `S(𝒟_{j+1} × ℝⁿ)`,
`ε_j = min {ρ_{j+1}/(2ρ̂₀), s_{j+1}/s₀}`. Design package P23-18.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Scalars

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

theorem seq_s (p : ScaleData) (j : ℕ) : (seq p j).s = p.s / 12 ^ j := by
  induction j with
  | zero => simp [seq]
  | succ j ih => rw [pow_succ]; change (seq p j).s / 12 = _; rw [ih]; field_simp

theorem seq_ρ_succ (p : ScaleData) (j : ℕ) : (seq p (j + 1)).ρ = rhoHat (seq p j) / 16 := rfl

theorem two_pow_ge_twelve (p : ScaleData) (hτ : 0 ≤ p.τ) : 12 ≤ 2 * (24 : ℝ) ^ (p.τ + 1) := by
  have : (24 : ℝ) ^ (1 : ℝ) ≤ 24 ^ (p.τ + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_one] at this
  linarith

namespace PsiSteps

theorem rho_pos (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) : 0 < rhoHat (seq p j) :=
  (P.hyp j).R_pos

theorem rho_upper (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    rhoHat (seq p j) ≤ rhoHat p / 16 ^ j := by
  induction j with
  | zero => simp [seq]
  | succ j ih =>
    calc rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16 := P.rho_hi j
      _ ≤ rhoHat p / 16 ^ j / 16 := by gcongr
      _ = rhoHat p / 16 ^ (j + 1) := by rw [pow_succ]; field_simp

theorem rho_lower (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    rhoHat p / (2 * (24 : ℝ) ^ (p.τ + 1)) ^ j ≤ rhoHat (seq p j) := by
  have hq : 0 < 2 * (24 : ℝ) ^ (p.τ + 1) := by positivity
  induction j with
  | zero => simp [seq]
  | succ j ih =>
    have := P.rho_lo j
    calc rhoHat p / (2 * (24 : ℝ) ^ (p.τ + 1)) ^ (j + 1)
        = (rhoHat p / (2 * (24 : ℝ) ^ (p.τ + 1)) ^ j) / (2 * (24 : ℝ) ^ (p.τ + 1)) := by
          rw [pow_succ]; field_simp
      _ ≤ rhoHat (seq p j) / (2 * (24 : ℝ) ^ (p.τ + 1)) := by gcongr
      _ ≤ _ := this

end PsiSteps

end Scalars

end KAM.Planetary

end
