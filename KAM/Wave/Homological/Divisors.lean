/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Melnikov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Divisor bounds (blueprint-W `bpW:w4:divisors`)

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

For `(k,l) ∈ 𝒵` the divisor `⟨k,ω⟩ + ⟨l,Ω⟩` satisfies `|δ(ξ)| ≥ α ⟨l⟩ / A_k` (`(H_α)`) and
`|1/δ(ξ) - 1/δ(ζ)| ≤ 2 (1+|k|₁) A_k² M ⟨l⟩⁻¹ α⁻² |ξ-ζ|` (`homDivGen_bounds`). The six divisors of
Definition `bpW:w4:melnikov` are the cases `l = 0, ∓e_j, ∓(e_i+e_j), e_i - e_j`
(`homDelta0_bound`, `homDeltaPlus_bound`, `homDeltaMinus_bound`, `homDeltaP_bound`,
`homDeltaP'_bound`, `homDeltaQ_bound`), with their weights; also `homWeightQ_ge_abs`.
-/

@[expose] public section

namespace KAM.Wave

open Finset

/-- The momentum `∑_j j l_j` of `l`. -/
def homMom (l : ℕ+ →₀ ℤ) : ℤ := l.sum fun j n => (j : ℤ) * n

theorem homMom_add (l₁ l₂ : ℕ+ →₀ ℤ) : homMom (l₁ + l₂) = homMom l₁ + homMom l₂ :=
  Finsupp.sum_add_index' (by simp) (by intros; ring)

theorem homMom_neg (l : ℕ+ →₀ ℤ) : homMom (-l) = -homMom l := by
  have h := homMom_add l (-l)
  rw [add_neg_cancel] at h
  have h0 : homMom 0 = 0 := Finsupp.sum_zero_index
  linarith

theorem homMom_single (j : ℕ+) (n : ℤ) : homMom (Finsupp.single j n) = j * n :=
  Finsupp.sum_single_index (by simp)

theorem homPairL_add (l₁ l₂ : ℕ+ →₀ ℤ) (Ω : ℕ+ → ℝ) :
    homPairL (l₁ + l₂) Ω = homPairL l₁ Ω + homPairL l₂ Ω :=
  Finsupp.sum_add_index' (by simp) (by intros; push_cast; ring)

theorem homPairL_neg (l : ℕ+ →₀ ℤ) (Ω : ℕ+ → ℝ) : homPairL (-l) Ω = -homPairL l Ω := by
  have h := homPairL_add l (-l) Ω
  rw [add_neg_cancel] at h
  have h0 : homPairL 0 Ω = 0 := Finsupp.sum_zero_index
  linarith

theorem homPairL_single (j : ℕ+) (n : ℤ) (Ω : ℕ+ → ℝ) :
    homPairL (Finsupp.single j n) Ω = n * Ω j :=
  Finsupp.sum_single_index (by simp)

theorem homL1_add_le (l₁ l₂ : ℕ+ →₀ ℤ) : homL1 (l₁ + l₂) ≤ homL1 l₁ + homL1 l₂ := by
  classical
  unfold homL1
  have hsub : (l₁ + l₂).support ⊆ l₁.support ∪ l₂.support := Finsupp.support_add
  rw [Finsupp.sum_of_support_subset _ hsub _ (by simp)]
  rw [Finsupp.sum_of_support_subset l₁ (Finset.subset_union_left (s₂ := l₂.support)) _ (by simp),
    Finsupp.sum_of_support_subset l₂ (Finset.subset_union_right (s₁ := l₁.support)) _ (by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simpa using Int.natAbs_add_le (l₁ j) (l₂ j)

theorem homL1_neg (l : ℕ+ →₀ ℤ) : homL1 (-l) = homL1 l := by
  unfold homL1
  rw [Finsupp.sum_neg_index (by simp)]
  simp

theorem homL1_single (j : ℕ+) (n : ℤ) : homL1 (Finsupp.single j n) = n.natAbs :=
  Finsupp.sum_single_index (by simp)

theorem homJap_eq (l : ℕ+ →₀ ℤ) : homJap l = max 1 (homMom l).natAbs := rfl

theorem homL1_zero : homL1 0 = 0 := Finsupp.sum_zero_index

theorem homMom_zero : homMom 0 = 0 := Finsupp.sum_zero_index

theorem homPairL_zero (Ω : ℕ+ → ℝ) : homPairL 0 Ω = 0 := Finsupp.sum_zero_index

/-- The real number `|l|` is the sum of `|l_j|`. -/
theorem homL1_cast (l : ℕ+ →₀ ℤ) : (homL1 l : ℝ) = l.sum fun _ n => |(n : ℝ)| := by
  unfold homL1 Finsupp.sum
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem abs_homPairZ_le (k : Fin 2 → ℤ) (v : Fin 2 → ℝ) :
    |homPairZ k v| ≤ Fourier.modeSize k * ‖v‖ := by
  unfold homPairZ Fourier.modeSize
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm v i) (abs_nonneg _)

theorem homPairZ_sub (k : Fin 2 → ℤ) (v w : Fin 2 → ℝ) :
    homPairZ k v - homPairZ k w = homPairZ k (v - w) := by
  unfold homPairZ
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_sub]

/-- The divisor of `(k,l)` moves by at most `(|k|₁ M_ω + |l| M_Ω) |ξ - ζ|`. -/
theorem homDivGen_diff_le {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    {ξ ζ : Fin 2 → ℝ} (hξ : ξ ∈ Par) (hζ : ζ ∈ Par) (k : Fin 2 → ℤ) (l : ℕ+ →₀ ℤ) :
    |(homPairZ k (ω ξ) + homPairL l (Ω ξ)) - (homPairZ k (ω ζ) + homPairL l (Ω ζ))| ≤
      (Fourier.modeSize k * Mω + homL1 l * MΩ) * ‖ξ - ζ‖ := by
  have hk : |homPairZ k (ω ξ) - homPairZ k (ω ζ)| ≤ Fourier.modeSize k * (Mω * ‖ξ - ζ‖) := by
    rw [homPairZ_sub]
    exact (abs_homPairZ_le k _).trans
      (mul_le_mul_of_nonneg_left (h.lipOmega ξ hξ ζ hζ) (Fourier.modeSize_nonneg k))
  have hl : |homPairL l (Ω ξ) - homPairL l (Ω ζ)| ≤ homL1 l * (MΩ * ‖ξ - ζ‖) := by
    unfold homPairL Finsupp.sum
    rw [← Finset.sum_sub_distrib, homL1_cast]
    unfold Finsupp.sum
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hj := h.lipTail ξ hξ ζ hζ j
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast j.pos
    have := abs_nonneg (Ω ξ j - Ω ζ j)
    nlinarith
  calc _ = |(homPairZ k (ω ξ) - homPairZ k (ω ζ)) + (homPairL l (Ω ξ) - homPairL l (Ω ζ))| := by
        congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hk hl)
    _ = _ := by ring

/-- Divisor bounds for one `(k,l) ∈ 𝒵` (blueprint `bpW:w4:divisors`): the generic form. -/
theorem homDivGen_bounds {Par : Set (Fin 2 → ℝ)} {ω : (Fin 2 → ℝ) → Fin 2 → ℝ}
    {Ω : (Fin 2 → ℝ) → ℕ+ → ℝ} {M0 Mω MΩ τ α : ℝ} (h : HomFreqHyp Par ω Ω M0 Mω MΩ)
    (hα : 0 < α) (hH : HomMelnikov τ α Par ω Ω) {k : Fin 2 → ℤ} {l : ℕ+ →₀ ℤ}
    (hz : (k, l) ∈ homZ) :
    (∀ ξ ∈ Par, α * (homJap l : ℝ) / waveA τ k ≤
        |homPairZ k (ω ξ) + homPairL l (Ω ξ)|) ∧
    ∀ ξ ∈ Par, ∀ ζ ∈ Par,
      |1 / (homPairZ k (ω ξ) + homPairL l (Ω ξ)) - 1 / (homPairZ k (ω ζ) + homPairL l (Ω ζ))| ≤
        2 * (1 + Fourier.modeSize k) * waveA τ k ^ 2 * (Mω + MΩ) / (α ^ 2 * (homJap l : ℝ)) *
          ‖ξ - ζ‖ := by
  refine ⟨fun ξ hξ => hH ξ hξ (k, l) hz, fun ξ hξ ζ hζ => ?_⟩
  have hA : 1 ≤ waveA τ k := waveA_ge_one k
  have hw : (1 : ℝ) ≤ homJap l := by exact_mod_cast le_max_left 1 _
  set w : ℝ := (homJap l : ℝ) with hwdef
  set A := waveA τ k with hAdef
  set a := homPairZ k (ω ξ) + homPairL l (Ω ξ) with ha
  set b := homPairZ k (ω ζ) + homPairL l (Ω ζ) with hb
  have hc : 0 < α * w / A := by positivity
  have hla : α * w / A ≤ |a| := hH ξ hξ (k, l) hz
  have hlb : α * w / A ≤ |b| := hH ζ hζ (k, l) hz
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, abs_zero] at hla; linarith
  have hb0 : b ≠ 0 := fun h0 => by rw [h0, abs_zero] at hlb; linarith
  have hd := homDivGen_diff_le h hξ hζ k l
  have hl2 : (homL1 l : ℝ) ≤ 2 := by exact_mod_cast hz.2
  have hM : 0 ≤ Mω + MΩ := by have := h.nonneg; linarith
  have hnorm : 0 ≤ ‖ξ - ζ‖ := norm_nonneg _
  have hk0 := Fourier.modeSize_nonneg k
  have hD : |a - b| ≤ 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by
    refine hd.trans ?_
    have hMω := h.nonneg.2.1
    have hMΩ := h.nonneg.2.2
    have hl0 : (0 : ℝ) ≤ homL1 l := Nat.cast_nonneg _
    have e1 : Fourier.modeSize k * Mω + homL1 l * MΩ ≤
        2 * (1 + Fourier.modeSize k) * (Mω + MΩ) := by
      nlinarith [mul_nonneg hk0 hMω, mul_nonneg hk0 hMΩ, mul_nonneg hl0 hMΩ,
        mul_nonneg (sub_nonneg.2 hl2) hMΩ]
    exact mul_le_mul_of_nonneg_right e1 hnorm
  rw [div_sub_div _ _ ha0 hb0, abs_div, abs_mul]
  simp only [one_mul, mul_one]
  rw [div_le_iff₀ (by positivity)]
  have hab : (α * w / A) * (α * w / A) ≤ |a| * |b| := mul_le_mul hla hlb hc.le (abs_nonneg _)
  have hba : |b - a| = |a - b| := abs_sub_comm _ _
  rw [hba]
  have hpos : 0 < α ^ 2 * w := by positivity
  have key : 2 * (1 + Fourier.modeSize k) * A ^ 2 * (Mω + MΩ) / (α ^ 2 * w) * ‖ξ - ζ‖ *
        (α * w / A * (α * w / A)) = 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ * w := by
    field_simp
  have hnn : 0 ≤ 2 * (1 + Fourier.modeSize k) * A ^ 2 * (Mω + MΩ) / (α ^ 2 * w) * ‖ξ - ζ‖ := by
    positivity
  calc |a - b| ≤ 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := hD
    _ ≤ 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ * w := by
        have : 0 ≤ 2 * (1 + Fourier.modeSize k) * (Mω + MΩ) * ‖ξ - ζ‖ := by positivity
        nlinarith
    _ = 2 * (1 + Fourier.modeSize k) * A ^ 2 * (Mω + MΩ) / (α ^ 2 * w) * ‖ξ - ζ‖ *
        (α * w / A * (α * w / A)) := key.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hab hnn

end KAM.Wave
