/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Linfty
public import KAM.Frozen.Wave.Defs.Lam
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Spectral asymptotics of the wave normal frequencies (blueprint-W `bpW:w1:tails`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

`waveOmega` is `Ω_j(ξ) = λ_j + 3/(2πλ_j) ⟨b, ξ⟩` with `b = (λ_1⁻¹, λ_2⁻¹)`, and
`waveOmegaTilde = Ω_j - j`. The statement of the blueprint is proved pointwise for `j ≥ 3`
(`tail_bound`, `tail_lipschitz`, `tail_gap`) and, through the `ℓ^1_∞` realization of
`KAM.Wave.Seq.Linfty` with the entries `j = 1, 2` set to zero (`tildeOmegaSeq`), as
`isLinfty_tildeOmegaSeq`, `norm_tildeOmegaSeq_le`, `isLinftyLipschitz_tildeOmegaSeq`.
-/

@[expose] public noncomputable section

namespace KAM.Wave

variable {m : ℝ} (hm : 0 < m)

/-- The pairing `⟨b, ξ⟩ = ξ₀/λ₁ + ξ₁/λ₂`. -/
def waveB (m : ℝ) (hm : 0 < m) (ξ : Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, ξ i / lam m hm (i : ℕ).succPNat

/-- The normal frequencies `Ω_j(ξ) = λ_j + 3/(2πλ_j) ⟨b, ξ⟩`. -/
def waveOmega (m : ℝ) (hm : 0 < m) (ξ : Fin 2 → ℝ) (j : ℕ+) : ℝ :=
  lam m hm j + 3 / (2 * Real.pi * lam m hm j) * waveB m hm ξ

/-- `Ω̃_j = Ω_j - j`. -/
def waveOmegaTilde (m : ℝ) (hm : 0 < m) (ξ : Fin 2 → ℝ) (j : ℕ+) : ℝ := waveOmega m hm ξ j - j

/-- The `ℓ^1_∞` sequence `Ω̃` with entries `j = 1, 2` set to zero (`PNat`-indexed). -/
def tildeOmegaSeq (m : ℝ) (hm : 0 < m) (ξ : Fin 2 → ℝ) (j : ℕ+) : ℝ :=
  if 3 ≤ (j : ℕ) then waveOmegaTilde m hm ξ j else 0

private theorem pnat_pos (j : ℕ+) : (0 : ℝ) < j := by exact_mod_cast j.pos

private theorem lam_gt (j : ℕ+) : (j : ℝ) < lam m hm j := by
  unfold lam
  exact Real.lt_sqrt (pnat_pos j).le |>.2 (by linarith)

theorem lam_pnat_pos (j : ℕ+) : 0 < lam m hm j := (pnat_pos j).trans (lam_gt hm j)

/-- `0 < λ_j - j ≤ m / (2j)`. -/
theorem lam_sub_pnat_le (j : ℕ+) : lam m hm j - j ≤ m / (2 * j) := by
  have hj := pnat_pos j
  have h1 := lam_gt hm j
  have h2 : (lam m hm j - j) * (lam m hm j + j) = m := by
    have : lam m hm j ^ 2 = (j : ℝ) ^ 2 + m := by unfold lam; exact Real.sq_sqrt (by positivity)
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem lam_sub_pnat_pos (j : ℕ+) : 0 < lam m hm j - j := sub_pos.2 (lam_gt hm j)

theorem waveB_sub (ξ ζ : Fin 2 → ℝ) : waveB m hm ξ - waveB m hm ζ = waveB m hm (ξ - ζ) := by
  simp [waveB, sub_div, Finset.sum_sub_distrib]

/-- `|⟨b, ξ⟩| ≤ (λ₁⁻¹ + λ₂⁻¹) |ξ|` (max norm). -/
theorem abs_waveB_le (ξ : Fin 2 → ℝ) :
    |waveB m hm ξ| ≤ (1 / lam m hm 1 + 1 / lam m hm 2) * ‖ξ‖ := by
  unfold waveB
  rw [Fin.sum_univ_two]
  have h0 := lam_pnat_pos hm (Nat.succPNat 0)
  have h1 := lam_pnat_pos hm (Nat.succPNat 1)
  have e0 : |ξ 0| ≤ ‖ξ‖ := by simpa using norm_le_pi_norm ξ 0
  have e1 : |ξ 1| ≤ ‖ξ‖ := by simpa using norm_le_pi_norm ξ 1
  calc |ξ 0 / lam m hm (Nat.succPNat 0) + ξ 1 / lam m hm (Nat.succPNat 1)|
      ≤ |ξ 0 / lam m hm (Nat.succPNat 0)| + |ξ 1 / lam m hm (Nat.succPNat 1)| := abs_add_le _ _
    _ = |ξ 0| / lam m hm (Nat.succPNat 0) + |ξ 1| / lam m hm (Nat.succPNat 1) := by
        rw [abs_div, abs_div, abs_of_pos h0, abs_of_pos h1]
    _ ≤ ‖ξ‖ / lam m hm (Nat.succPNat 0) + ‖ξ‖ / lam m hm (Nat.succPNat 1) := by gcongr
    _ = _ := by
        have : Nat.succPNat 0 = 1 := rfl
        have h' : Nat.succPNat 1 = 2 := rfl
        rw [this, h']; ring

/-- `bpW:w1:tails`, first bound: `j |Ω̃_j(ξ)| ≤ m/2 + 3/(2π) |⟨b, ξ⟩|` for `j ≥ 3` (in fact all
`j`). -/
theorem tail_bound (ξ : Fin 2 → ℝ) (j : ℕ+) :
    |waveOmegaTilde m hm ξ j| * j ≤ m / 2 + 3 / (2 * Real.pi) * |waveB m hm ξ| := by
  have hj := pnat_pos j
  have hl := lam_gt hm j
  have hlp : 0 < lam m hm j := hj.trans hl
  have heq : waveOmegaTilde m hm ξ j =
      (lam m hm j - j) + 3 / (2 * Real.pi * lam m hm j) * waveB m hm ξ := by
    unfold waveOmegaTilde waveOmega; ring
  have h1 : (lam m hm j - j) * j ≤ m / 2 := by
    have := lam_sub_pnat_le hm j
    calc (lam m hm j - j) * j ≤ m / (2 * j) * j := by gcongr
      _ = m / 2 := by field_simp
  have h2 : 3 / (2 * Real.pi * lam m hm j) * j ≤ 3 / (2 * Real.pi) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [mul_pos this hlp, mul_pos this hj]
  calc |waveOmegaTilde m hm ξ j| * j
      ≤ ((lam m hm j - j) + 3 / (2 * Real.pi * lam m hm j) * |waveB m hm ξ|) * j := by
        rw [heq]; gcongr
        calc _ ≤ |lam m hm j - j| + |3 / (2 * Real.pi * lam m hm j) * waveB m hm ξ| :=
              abs_add_le _ _
          _ = _ := by
            rw [abs_of_pos (sub_pos.2 hl), abs_mul, abs_of_pos (by positivity)]
    _ = (lam m hm j - j) * j + 3 / (2 * Real.pi * lam m hm j) * j * |waveB m hm ξ| := by ring
    _ ≤ m / 2 + 3 / (2 * Real.pi) * |waveB m hm ξ| := by gcongr

/-- `bpW:w1:tails`, Lipschitz bound. -/
theorem tail_lipschitz (ξ ζ : Fin 2 → ℝ) (j : ℕ+) :
    |waveOmegaTilde m hm ξ j - waveOmegaTilde m hm ζ j| * j ≤
      3 / (2 * Real.pi) * (1 / lam m hm 1 + 1 / lam m hm 2) * ‖ξ - ζ‖ := by
  have hj := pnat_pos j
  have hl := lam_gt hm j
  have hlp : 0 < lam m hm j := hj.trans hl
  have heq : waveOmegaTilde m hm ξ j - waveOmegaTilde m hm ζ j =
      3 / (2 * Real.pi * lam m hm j) * waveB m hm (ξ - ζ) := by
    unfold waveOmegaTilde waveOmega; rw [← waveB_sub]; ring
  have h2 : 3 / (2 * Real.pi * lam m hm j) * j ≤ 3 / (2 * Real.pi) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    nlinarith [mul_pos this hlp, mul_pos this hj]
  rw [heq, abs_mul, abs_of_pos (by positivity)]
  calc 3 / (2 * Real.pi * lam m hm j) * |waveB m hm (ξ - ζ)| * j
      = (3 / (2 * Real.pi * lam m hm j) * j) * |waveB m hm (ξ - ζ)| := by ring
    _ ≤ 3 / (2 * Real.pi) * ((1 / lam m hm 1 + 1 / lam m hm 2) * ‖ξ - ζ‖) := by
        gcongr; exact abs_waveB_le hm _
    _ = _ := by ring

/-- `bpW:w1:tails`, last bound: `|Ω_i - Ω_j - (i - j)| ≤ (m + 3/π |⟨b, ξ⟩|)/min(i, j)`. -/
theorem tail_gap (ξ : Fin 2 → ℝ) (i j : ℕ+) :
    |waveOmega m hm ξ i - waveOmega m hm ξ j - ((i : ℝ) - j)| ≤
      (m + 3 / Real.pi * |waveB m hm ξ|) / (min i j : ℕ+) := by
  set A := m / 2 + 3 / (2 * Real.pi) * |waveB m hm ξ| with hA
  have hA0 : 0 ≤ A := by positivity
  have hmin : (0 : ℝ) < ((min i j : ℕ+) : ℝ) := pnat_pos _
  have hi : |waveOmegaTilde m hm ξ i| ≤ A / ((min i j : ℕ+) : ℝ) := by
    have h := tail_bound hm ξ i
    have hle : ((min i j : ℕ+) : ℝ) ≤ i := by exact_mod_cast min_le_left i j
    rw [le_div_iff₀ hmin]
    calc _ ≤ |waveOmegaTilde m hm ξ i| * i := by gcongr
      _ ≤ A := h
  have hj : |waveOmegaTilde m hm ξ j| ≤ A / ((min i j : ℕ+) : ℝ) := by
    have h := tail_bound hm ξ j
    have hle : ((min i j : ℕ+) : ℝ) ≤ j := by exact_mod_cast min_le_right i j
    rw [le_div_iff₀ hmin]
    calc _ ≤ |waveOmegaTilde m hm ξ j| * j := by gcongr
      _ ≤ A := h
  have : waveOmega m hm ξ i - waveOmega m hm ξ j - ((i : ℝ) - j) =
      waveOmegaTilde m hm ξ i - waveOmegaTilde m hm ξ j := by unfold waveOmegaTilde; ring
  rw [this]
  calc _ ≤ |waveOmegaTilde m hm ξ i| + |waveOmegaTilde m hm ξ j| := abs_sub _ _
    _ ≤ A / ((min i j : ℕ+) : ℝ) + A / ((min i j : ℕ+) : ℝ) := add_le_add hi hj
    _ = _ := by rw [hA]; field_simp; ring

/-- `bpW:w1:tails` (`ℓ^1_∞` form): `Ω̃ ∈ ℓ^1_∞` with `|Ω̃(ξ)|_1 ≤ m/2 + 3/(2π) |⟨b, ξ⟩|`. -/
theorem isLinfty_tildeOmegaSeq (ξ : Fin 2 → ℝ) : IsLinfty 1 (tildeOmegaSeq m hm ξ) :=
  isLinfty_of_bound 1 _ (C := m / 2 + 3 / (2 * Real.pi) * |waveB m hm ξ|) fun j => by
    unfold tildeOmegaSeq
    split_ifs
    · simpa using tail_bound hm ξ j
    · simp only [abs_zero, zero_mul]; positivity

theorem norm_tildeOmegaSeq_le (ξ : Fin 2 → ℝ) :
    ‖tauInfty 1 _ (isLinfty_tildeOmegaSeq hm ξ)‖ ≤ m / 2 + 3 / (2 * Real.pi) * |waveB m hm ξ| := by
  refine (norm_tauInfty_le_iff _ _ _ (by positivity)).2 fun j => ?_
  unfold tildeOmegaSeq
  split_ifs
  · simpa using tail_bound hm ξ j
  · simp only [abs_zero, zero_mul]; positivity

/-- `bpW:w1:tails` (`ℓ^1_∞` form): `Ω̃` is `L`-Lipschitz into `ℓ^1_∞` with
`L = 3/(2π) (λ₁⁻¹ + λ₂⁻¹)`. -/
theorem isLinftyLipschitz_tildeOmegaSeq :
    IsLinftyLipschitz 1 (3 / (2 * Real.pi) * (1 / lam m hm 1 + 1 / lam m hm 2)) Set.univ
      (tildeOmegaSeq m hm) := by
  have hL : 0 ≤ 3 / (2 * Real.pi) * (1 / lam m hm 1 + 1 / lam m hm 2) := by
    have := lam_pnat_pos hm 1; have := lam_pnat_pos hm 2; positivity
  rw [isLinftyLipschitz_iff]
  refine ⟨hL, fun ξ _ => isLinfty_tildeOmegaSeq hm ξ, ?_⟩
  intro ξ _ ζ _ j
  simp only [Real.rpow_one]
  unfold tildeOmegaSeq
  split_ifs
  · exact tail_lipschitz hm ξ ζ j
  · simp only [sub_self, abs_zero, zero_mul]
    have := lam_pnat_pos hm 1; have := lam_pnat_pos hm 2; positivity

end KAM.Wave

end
