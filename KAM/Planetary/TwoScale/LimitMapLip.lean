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

section Lip

variable {a b : ℕ} {sbar : ℝ} {p : ScaleData}
  {Ds : ℕ → Set (Fin (a + b) → ℝ)} {hs : ℕ → (Fin (a + b) → ℂ) → ℂ}
  {fs : ℕ → CHam (a + b)} {Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b)}

theorem differentiable_unsc {n : ℕ} (R s : ℝ) : Differentiable ℂ (unsc (n := n) (𝕜 := ℂ) R s) := by
  unfold unsc
  refine Differentiable.prodMk ?_ ?_ <;> refine differentiable_pi.2 fun i => ?_ <;> fun_prop

theorem differentiable_sc {n : ℕ} (R s : ℝ) : Differentiable ℂ (sc (n := n) (𝕜 := ℂ) R s) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [sc, Fin.append_left]; fun_prop
  · simp only [sc, Fin.append_right]; fun_prop

/-- The scaling radius of `stepP:p3:pl-lip`: `ε_j = min {ρ_{j+1}/(2ρ̂₀), s_{j+1}/s₀}`. -/
def stageEps (p : ScaleData) (j : ℕ) : ℝ :=
  min (rhoHat (seq p j) / 16 / 2 / rhoHat p) (1 / 12 ^ (j + 1))

namespace PsiSteps

theorem stageEps_pos (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) : 0 < stageEps p j := by
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have := P.rho_pos j
  unfold stageEps
  exact lt_min (by positivity) (by positivity)

theorem stageEps_lower (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) :
    1 / (32 * (2 * (24 : ℝ) ^ (p.τ + 1)) ^ j) ≤ stageEps p j := by
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hτ : 0 ≤ p.τ := by
    have : ((a + b : ℕ) : ℝ) < p.τ := (P.hyp 0).τ_gt
    have h2 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hq := two_pow_ge_twelve p hτ
  have hqj : (12 : ℝ) ^ j ≤ (2 * (24 : ℝ) ^ (p.τ + 1)) ^ j := pow_le_pow_left₀ (by norm_num) hq j
  have hqp : 0 < (2 * (24 : ℝ) ^ (p.τ + 1)) ^ j := by positivity
  have hlow := P.rho_lower j
  unfold stageEps
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ (by positivity) h0]
    have := (div_le_iff₀ hqp).1 hlow
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 12) j]

/-- On the complex `ε_j`-neighbourhood of the scaled real domain, `unsc` lands in the complex
domain of `Ψ_{j+1}`. -/
theorem unsc_mem (P : PsiSteps sbar p Ds hs fs Ψ Φ) (j : ℕ) {z : Fin ((a + b) + (a + b)) → ℂ}
    {w : Fin ((a + b) + (a + b)) → ℝ}
    (hw : (unsc (rhoHat p) p.s w).2 ∈ realTube (Ds (j + 1)) ((seq p (j + 1)).ρ / 2))
    (hz : ‖z - KAM.realInclusion _ w‖ < stageEps p j) :
    unsc (rhoHat p) p.s z ∈
      coefficientDom (Ds (j + 1)) (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12) := by
  have h0 : 0 < rhoHat p := (P.hyp 0).R_pos
  have hs0 : 0 < p.s := (P.hyp 0).positive.2.1
  have hs1 : 4 * (seq p j).s ≤ sbar := (P.hyp j).widths.1
  have hsj : 0 < (seq p j).s := (P.hyp j).positive.2.1
  rw [(conv_data _ _ _).2]
  have hε1 : stageEps p j ≤ rhoHat (seq p j) / 16 / 2 / rhoHat p := min_le_left _ _
  have hε2 : stageEps p j ≤ 1 / 12 ^ (j + 1) := min_le_right _ _
  have hd : unsc (rhoHat p) p.s z - KAM.realInclusion₂ _ (unsc (rhoHat p) p.s w) =
      unsc (rhoHat p) p.s (z - KAM.realInclusion _ w) := by
    rw [unsc_sub, unsc_incl]
  have hs2 : (seq p j).s / 12 = p.s / 12 ^ (j + 1) := by
    rw [seq_s, pow_succ]; field_simp
  refine ⟨fun i => ?_, ?_⟩
  · have h1 := norm_unsc_fst_le (R := rhoHat p) hs0.le (z - KAM.realInclusion _ w)
    have h2 := norm_le_pi_norm (unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).1 i
    have h3 : (unsc (rhoHat p) p.s z).1 i - ((((unsc (rhoHat p) p.s w).1 i : ℝ)) : ℂ) =
        (unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).1 i := by
      rw [← hd]; rfl
    have h4 : |((unsc (rhoHat p) p.s z).1 i).im| ≤ ‖(unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).1 i‖ := by
      rw [← h3]
      have := Complex.abs_im_le_norm ((unsc (rhoHat p) p.s z).1 i - ((((unsc (rhoHat p) p.s w).1 i : ℝ)) : ℂ))
      simpa using this
    have hc : 0 < p.s / (2 * π) := by positivity
    have h5 : ‖(unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).1‖ <
        p.s / (2 * π) * stageEps p j :=
      h1.trans_lt (mul_lt_mul_of_pos_left hz hc)
    have h6 : p.s / (2 * π) * stageEps p j ≤ p.s / (2 * π) * (1 / 12 ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left hε2 hc.le
    have h7 : p.s / (2 * π) * (1 / 12 ^ (j + 1)) = ((seq p j).s / 12) / (2 * π) := by
      rw [hs2]; field_simp
    have h8 : ((seq p j).s / 12) / (2 * π) ≤ (sbar + (seq p j).s / 12) / (2 * π) := by
      gcongr; linarith
    show |((unsc (rhoHat p) p.s z).1 i).im| < (sbar + (seq p j).s / 12) / (2 * π)
    exact lt_of_le_of_lt (h4.trans h2) (h5.trans_le (h6.trans (h7.le.trans h8)))
  · obtain ⟨J, hJ, hwJ⟩ := mem_realTube_iff.1 hw
    refine ⟨J, hJ, ?_⟩
    have h1 := norm_unsc_snd_le (s := p.s) h0.le (z - KAM.realInclusion _ w)
    have h2 : (unsc (rhoHat p) p.s z).2 - (KAM.realInclusion _ ((unsc (rhoHat p) p.s w).2)) =
        (unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).2 := by
      rw [← hd]; rfl
    have h3 : rhoHat p * stageEps p j ≤ rhoHat (seq p j) / 16 / 2 := by
      calc rhoHat p * stageEps p j ≤ rhoHat p * (rhoHat (seq p j) / 16 / 2 / rhoHat p) :=
            mul_le_mul_of_nonneg_left hε1 h0.le
        _ = _ := by field_simp
    have h4 : ‖(unsc (rhoHat p) p.s z).2 - (fun i => ((J i : ℝ) : ℂ))‖ <
        rhoHat (seq p j) / 16 := by
      have e : (unsc (rhoHat p) p.s z).2 - (fun i => ((J i : ℝ) : ℂ)) =
          (unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).2 +
            KAM.realInclusion _ ((unsc (rhoHat p) p.s w).2 - J) := by
        rw [← h2, map_sub]; ext i; simp
      rw [e]
      have h5 : ‖KAM.realInclusion _ ((unsc (rhoHat p) p.s w).2 - J)‖ < rhoHat (seq p j) / 16 / 2 := by
        rw [KAM.norm_realInclusion]; rwa [seq_ρ_succ] at hwJ
      have h6 : ‖(unsc (rhoHat p) p.s (z - KAM.realInclusion _ w)).2‖ < rhoHat (seq p j) / 16 / 2 :=
        h1.trans_lt ((mul_lt_mul_of_pos_left hz h0).trans_le h3)
      calc _ ≤ _ := norm_add_le _ _
        _ < _ := add_lt_add h6 h5
        _ = _ := by ring
    exact h4

end PsiSteps

end Lip

end KAM.Planetary

end
