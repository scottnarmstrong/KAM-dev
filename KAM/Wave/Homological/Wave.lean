/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Melnikov
public import KAM.Wave.Seq.Tails
public import KAM.Wave.Normal.ActionCoeff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The wave frequencies satisfy the frequency hypotheses (blueprint-W `bpW:w4:wave` (i))

`waveFreqTan m hm ξ = (λ₁, λ₂) + Aξ` (`A = actionA`, Theorem `bpW:w0n:AB`) and
`waveFreqNor m hm ξ j = Ω_j(ξ) = waveOmega (j+2)` (P96-K index `j`, wave index `J = j+2`).
`homFreqHyp1_wave` proves `HomFreqHyp1` (and `homFreqHyp_wave` the weaker `HomFreqHyp`) with the
    explicit constants
`M_ω = 9/(8πλ₁²) + 3/(2πλ₁λ₂)`, `M_Ω = 3/(2π)(λ₁⁻¹ + λ₂⁻¹)`, `M₀ = m/2 + 3/(2π) B` where
`B` bounds `|⟨b,ξ⟩|` on the parameter set.
-/

@[expose] public section

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- The tangential frequencies `ω(ξ) = (λ₁, λ₂) + Aξ` (blueprint `bpW:w4:wave`). -/
noncomputable def waveFreqTan (ξ : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => lamTan m hm i + ∑ i', actionA m hm i i' * ξ i'

/-- The normal frequencies `Ω_j(ξ) = Ω^{wave}_{j+2}(ξ)` in the P96-K index `j ≥ 1`. -/
noncomputable def waveFreqNor (ξ : Fin 2 → ℝ) (j : ℕ+) : ℝ := waveOmega m hm ξ (j + 2)

theorem lam_one_lt_two : lam m hm 1 < lam m hm 2 := by
  unfold lam
  exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

theorem actionA_pos (i i' : Fin 2) : 0 < actionA m hm i i' := by
  have h0 := lamTan_pos m hm i
  have h1 := lamTan_pos m hm i'
  unfold actionA
  split_ifs <;> positivity

theorem waveFreqTan_sub (ξ ζ : Fin 2 → ℝ) (i : Fin 2) :
    waveFreqTan m hm ξ i - waveFreqTan m hm ζ i = ∑ i', actionA m hm i i' * (ξ - ζ) i' := by
  unfold waveFreqTan
  simp [mul_sub, Finset.sum_sub_distrib]

/-- The Lipschitz constant of `ω`: the first row sum of `A`. -/
noncomputable def waveMomega : ℝ :=
  9 / (8 * Real.pi * lam m hm 1 ^ 2) + 3 / (2 * Real.pi * lam m hm 1 * lam m hm 2)

/-- The Lipschitz constant of `Ω` (in `j |Ω_j(ξ) - Ω_j(ζ)|`). -/
noncomputable def waveMOmega : ℝ := 3 / (2 * Real.pi) * (1 / lam m hm 1 + 1 / lam m hm 2)

theorem abs_waveFreqTan_sub_le (ξ ζ : Fin 2 → ℝ) :
    ‖waveFreqTan m hm ξ - waveFreqTan m hm ζ‖ ≤ waveMomega m hm * ‖ξ - ζ‖ := by
  have hl1 := lam_pnat_pos hm 1
  have hl2 := lam_pnat_pos hm 2
  have hlt := lam_one_lt_two m hm
  have hM : 0 ≤ waveMomega m hm * ‖ξ - ζ‖ := by unfold waveMomega; positivity
  refine (pi_norm_le_iff_of_nonneg hM).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply, waveFreqTan_sub, Fin.sum_univ_two]
  have e0 : |(ξ - ζ) 0| ≤ ‖ξ - ζ‖ := by simpa using norm_le_pi_norm (ξ - ζ) 0
  have e1 : |(ξ - ζ) 1| ≤ ‖ξ - ζ‖ := by simpa using norm_le_pi_norm (ξ - ζ) 1
  have a00 : actionA m hm 0 0 = 9 / (8 * Real.pi * lam m hm 1 ^ 2) := by
    simp [actionA, lamTan]
  have a11 : actionA m hm 1 1 = 9 / (8 * Real.pi * lam m hm 2 ^ 2) := by
    simp [actionA, lamTan]
  have a01 : actionA m hm 0 1 = 3 / (2 * Real.pi * lam m hm 1 * lam m hm 2) := by
    simp [actionA, lamTan]
  have a10 : actionA m hm 1 0 = 3 / (2 * Real.pi * lam m hm 2 * lam m hm 1) := by
    simp [actionA, lamTan]
  have p00 := actionA_pos m hm 0 0
  have p01 := actionA_pos m hm 0 1
  have p10 := actionA_pos m hm 1 0
  have p11 := actionA_pos m hm 1 1
  have key : ∀ x y : Fin 2, 0 < actionA m hm x y → ∀ t : ℝ, |t| ≤ ‖ξ - ζ‖ →
      |actionA m hm x y * t| ≤ actionA m hm x y * ‖ξ - ζ‖ := fun x y hxy t ht => by
    rw [abs_mul, abs_of_pos hxy]; exact mul_le_mul_of_nonneg_left ht hxy.le
  have hs : ∀ x : Fin 2, actionA m hm x 0 + actionA m hm x 1 ≤ waveMomega m hm →
      |actionA m hm x 0 * (ξ - ζ) 0 + actionA m hm x 1 * (ξ - ζ) 1| ≤
        waveMomega m hm * ‖ξ - ζ‖ := fun x hx => by
    refine (abs_add_le _ _).trans ?_
    have := key x 0 (actionA_pos m hm x 0) _ e0
    have := key x 1 (actionA_pos m hm x 1) _ e1
    nlinarith [norm_nonneg (ξ - ζ)]
  fin_cases i
  · refine hs 0 ?_
    unfold waveMomega; rw [a00, a01]
  · refine hs 1 ?_
    unfold waveMomega
    rw [a10, a11]
    have h1 : 9 / (8 * Real.pi * lam m hm 2 ^ 2) ≤ 9 / (8 * Real.pi * lam m hm 1 ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      have := Real.pi_pos
      gcongr
    have h2 : 3 / (2 * Real.pi * lam m hm 2 * lam m hm 1) =
        3 / (2 * Real.pi * lam m hm 1 * lam m hm 2) := by ring
    linarith

/-- **The wave frequencies** (blueprint `bpW:w4:wave` (i)): `(bpW:w4:freq)` holds with
`M_ω = 9/(8πλ₁²) + 3/(2πλ₁λ₂)`, `M_Ω = 3/(2π)(λ₁⁻¹+λ₂⁻¹)`, `M₀ = m/2 + 3/(2π) B`, where
`|⟨b,ξ⟩| ≤ B` on the parameter set `Par`. -/
theorem homFreqHyp1_wave (Par : Set (Fin 2 → ℝ)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ξ ∈ Par, |waveB m hm ξ| ≤ B) :
    HomFreqHyp1 Par (waveFreqTan m hm) (waveFreqNor m hm)
      (m / 2 + 3 / (2 * Real.pi) * B) (waveMomega m hm) (waveMOmega m hm) := by
  have hl1 := lam_pnat_pos hm 1
  have hl2 := lam_pnat_pos hm 2
  refine ⟨⟨by positivity, ?_, ?_⟩, ?_, fun ξ _ ζ _ => abs_waveFreqTan_sub_le m hm ξ ζ, ?_⟩
  · unfold waveMomega; positivity
  · unfold waveMOmega; positivity
  · intro ξ hξ j
    have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
    have h := tail_bound hm ξ (j + 2)
    have hc : (((j + 2 : ℕ+) : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
    have hrw : waveFreqNor m hm ξ j - ((j : ℝ) + 2) = waveOmegaTilde m hm ξ (j + 2) := by
      unfold waveFreqNor waveOmegaTilde; rw [PNat.add_coe]; push_cast; ring
    rw [hrw]
    have hle : (j : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) := by rw [PNat.add_coe]; push_cast; linarith
    calc (j : ℝ) * |waveOmegaTilde m hm ξ (j + 2)|
        ≤ ((j + 2 : ℕ+) : ℝ) * |waveOmegaTilde m hm ξ (j + 2)| := by gcongr
      _ = |waveOmegaTilde m hm ξ (j + 2)| * ((j + 2 : ℕ+) : ℝ) := by ring
      _ ≤ m / 2 + 3 / (2 * Real.pi) * |waveB m hm ξ| := h
      _ ≤ _ := by gcongr; exact hB ξ hξ
  · intro ξ _ ζ _ j
    have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
    have h := tail_lipschitz hm ξ ζ (j + 2)
    have hrw : waveFreqNor m hm ξ j - waveFreqNor m hm ζ j =
        waveOmegaTilde m hm ξ (j + 2) - waveOmegaTilde m hm ζ (j + 2) := by
      unfold waveFreqNor waveOmegaTilde; rw [PNat.add_coe]; push_cast; ring
    rw [hrw]
    have hle : (j : ℝ) ≤ ((j + 2 : ℕ+) : ℝ) := by rw [PNat.add_coe]; push_cast; linarith
    calc (j : ℝ) * |waveOmegaTilde m hm ξ (j + 2) - waveOmegaTilde m hm ζ (j + 2)|
        ≤ ((j + 2 : ℕ+) : ℝ) * |waveOmegaTilde m hm ξ (j + 2) - waveOmegaTilde m hm ζ (j + 2)| := by
          gcongr
      _ = _ := by ring
      _ ≤ _ := h

/-- The wave frequencies satisfy the general hypothesis `bpW:w5:freq` (with the same constants). -/
theorem homFreqHyp_wave (Par : Set (Fin 2 → ℝ)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ξ ∈ Par, |waveB m hm ξ| ≤ B) :
    HomFreqHyp Par (waveFreqTan m hm) (waveFreqNor m hm)
      (m / 2 + 3 / (2 * Real.pi) * B) (waveMomega m hm) (waveMOmega m hm) :=
  (homFreqHyp1_wave m hm Par hB0 hB).toHyp

end KAM.Wave
