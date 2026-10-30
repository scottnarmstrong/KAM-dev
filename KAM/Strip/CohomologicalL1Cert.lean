/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalL1Sup
public import KAM.Strip.CohomologicalSumFiber
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Certified upper bounds of `Γ_∞(ω, δ)`

`Γ_∞(ω, δ) = sup_{k≠0} e^{-b|k|₁}/(2π|k·ω|)` with `b = 2πδ` (`KAM.smallDivisorSup`) is a supremum,
so a certificate is a finite maximum plus a tail. The modes split as follows.

* **Tail `|k|₁ > N`.** Here the Diophantine bound `|k·ω| ≥ γ|k|₁^{-τ}` applies. Since
  `m ↦ m^τ e^{-bm}` decreases for `m ≥ τ/b`, these terms are at most
  `KAM.sdSupTail γ τ δ N = (N+1)^τ e^{-b(N+1)}/(2πγ)` once `τ ≤ b(N+1)`.
  * `KAM.smallDivisorSup_le_box_tail` keeps one term per mode of `0 < |k|₁ ≤ N` (`KAM.modeBox`).
* **Clock frequencies `ω = (ω', 1)`.** `KAM.smallDivisorSup_snoc_le` uses the fibers of SHARP-L2B.
  For each `k'` the only small divisor is the nearest integer `p(k')` of `-k'·ω'`. Every other
  `k_n` has `|k'·ω' + k_n| ≥ 1/2`, so its term is at most `e^{-b|k'|₁}/π`. The data are therefore
  one entry per `0 < |k'|₁ ≤ N` in `ℤ^{n-1}`:
  * the integer `p(k')`;
  * a lower bound `0 < L(k') ≤ |k'·ω' + p(k')|`;
  * an upper bound `E_j ≥ e^{-bj}` of the weights.
  The fiber `k' = 0` contributes at most `e^{-b}/(2π)`.
-/

public noncomputable section

namespace KAM

variable {n : ℕ}

/-- The tail bound `(N+1)^τ e^{-2πδ(N+1)} / (2πγ)` of `Γ_∞` beyond `|k|₁ = N`. -/
@[expose] def sdSupTail (γ τ δ : ℝ) (N : ℕ) : ℝ :=
  (N + 1 : ℝ) ^ τ * Real.exp (-(2 * Real.pi * δ) * (N + 1)) / (2 * Real.pi * γ)

theorem sdSupTail_nonneg {γ τ δ : ℝ} (hγ : 0 < γ) (N : ℕ) : 0 ≤ sdSupTail γ τ δ N := by
  unfold sdSupTail
  positivity

/-- `m^τ e^{-bm} ≤ (N+1)^τ e^{-b(N+1)}` for `m ≥ N + 1 ≥ τ/b`. -/
theorem rpow_mul_exp_le_tail {τ b : ℝ} (hτ : 0 ≤ τ) {N m : ℕ} (hm : N + 1 ≤ m)
    (hN : τ ≤ b * (N + 1)) :
    (m : ℝ) ^ τ * Real.exp (-b * m) ≤ (N + 1 : ℝ) ^ τ * Real.exp (-b * (N + 1)) := by
  have h := rpow_mul_exp_le_geom (τ := τ / 2) (b := b) (by positivity) hm
  rw [show 2 * (τ / 2) = τ by ring] at h
  refine h.trans (mul_le_of_le_one_right (by positivity)
    (pow_le_one₀ (Real.exp_nonneg _) (Real.exp_le_one_iff.mpr ?_)))
  have : τ / (N + 1) ≤ b := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- The Diophantine bound of a term of `Γ_∞`: `e^{-b|k|₁}/(2π|k·ω|) ≤ |k|₁^τ e^{-b|k|₁}/(2πγ)`. -/
theorem exp_div_le_of_condition {ω : Fin n → ℝ} {γ τ : ℝ} (hω : Diophantine.Condition ω γ τ)
    (hγ : 0 < γ) {k : Fin n → ℤ} (hk : k ≠ 0) (b : ℝ) :
    Real.exp (-b * Fourier.modeSize k) / (2 * Real.pi * |Diophantine.frequencyDot ω k|) ≤
      Fourier.modeSize k ^ τ * Real.exp (-b * Fourier.modeSize k) / (2 * Real.pi * γ) := by
  have hm : 0 < Fourier.modeSize k := by
    rw [modeSize_eq_modeNat]
    exact_mod_cast modeNat_pos hk
  have hmτ : 0 < Fourier.modeSize k ^ τ := Real.rpow_pos_of_pos hm τ
  have hd := hω k hk
  have hdpos : 0 < |Diophantine.frequencyDot ω k| := lt_of_lt_of_le (div_pos hγ hmτ) hd
  rw [div_le_iff₀ hmτ] at hd
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have he := Real.exp_pos (-b * Fourier.modeSize k)
  calc Real.exp (-b * Fourier.modeSize k) * (2 * Real.pi * γ)
      = (2 * Real.pi * Real.exp (-b * Fourier.modeSize k)) * γ := by ring
    _ ≤ (2 * Real.pi * Real.exp (-b * Fourier.modeSize k)) *
          (|Diophantine.frequencyDot ω k| * Fourier.modeSize k ^ τ) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = Fourier.modeSize k ^ τ * Real.exp (-b * Fourier.modeSize k) *
          (2 * Real.pi * |Diophantine.frequencyDot ω k|) := by ring

/-- Every term with `|k|₁ ≥ N + 1` is at most the tail bound, once `τ ≤ 2πδ(N+1)`. -/
theorem exp_div_le_sdSupTail {ω : Fin n → ℝ} {γ τ δ : ℝ} (hω : Diophantine.Condition ω γ τ)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) {N : ℕ} (hN : τ ≤ 2 * Real.pi * δ * (N + 1)) {k : Fin n → ℤ}
    (hk : k ≠ 0) (hkN : N + 1 ≤ modeNat k) :
    Real.exp (-(2 * Real.pi * δ) * Fourier.modeSize k) /
        (2 * Real.pi * |Diophantine.frequencyDot ω k|) ≤ sdSupTail γ τ δ N := by
  refine (exp_div_le_of_condition hω hγ hk _).trans ?_
  rw [modeSize_eq_modeNat]
  exact div_le_div_of_nonneg_right (rpow_mul_exp_le_tail hτ hkN hN) (by positivity)

/-- **Certificate of `Γ_∞`, general frequency.** For `(γ, τ)`-Diophantine `ω` and a cut-off `N`
with `τ ≤ 2πδ(N+1)`, given `0 < L k ≤ |k·ω|` on `modeBox n N`, weights `E j ≥ e^{-2πδj}` and
`E(|k|₁)/(2π L k) ≤ B` on the box: `Γ_∞(ω, δ) ≤ max B (sdSupTail γ τ δ N)`. -/
theorem smallDivisorSup_le_box_tail {ω : Fin n → ℝ} {γ τ δ : ℝ} (hω : IsDiophantine γ τ ω)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) {N : ℕ} (hN : τ ≤ 2 * Real.pi * δ * (N + 1))
    (L : (Fin n → ℤ) → ℝ)
    (hL : ∀ k ∈ modeBox n N, 0 < L k ∧ L k ≤ |Diophantine.frequencyDot ω k|)
    (E : ℕ → ℝ) (hE : ∀ j : ℕ, Real.exp (-(2 * Real.pi * δ) * j) ≤ E j) {B : ℝ}
    (hB : ∀ k ∈ modeBox n N, E (modeNat k) / (2 * Real.pi * L k) ≤ B) :
    smallDivisorSup ω δ ≤ max B (sdSupTail γ τ δ N) := by
  have hc : Diophantine.Condition ω γ τ := hω.condition
  refine smallDivisorSup_le_of_forall (le_max_of_le_right (sdSupTail_nonneg hγ N)) fun k hk => ?_
  by_cases hkN : modeNat k ≤ N
  · have hbox : k ∈ modeBox n N := mem_modeBox.mpr ⟨hk, hkN⟩
    obtain ⟨hL0, hLk⟩ := hL k hbox
    refine le_max_of_le_left ((div_le_div₀ ((Real.exp_nonneg _).trans (hE _)) ?_ (by positivity)
      (mul_le_mul_of_nonneg_left hLk (by positivity))).trans (hB k hbox))
    rw [modeSize_eq_modeNat]
    exact hE _
  · exact le_max_of_le_right (exp_div_le_sdSupTail hc hγ hτ hN hk (by omega))

/-- **Certificate of `Γ_∞`, clock frequencies `ω = (ω', 1)` (fibered).** For `(γ, τ)`-Diophantine
`ω = Fin.snoc ω' 1` and a cut-off `N` with `τ ≤ 2πδ(N+1)`, given for each `k'` of
`modeBox m N` (`0 < |k'|₁ ≤ N` in `ℤ^m`) an integer `p k'` with `|k'·ω' + p k'| ≤ 1/2` and
`0 < L k' ≤ |k'·ω' + p k'|`, weights `E j ≥ e^{-2πδj}`, and a bound `B` of every entry:
`Γ_∞(ω, δ) ≤ max B (sdSupTail γ τ δ N)`.

The entries are `E(|k'|₁ + |p k'|)/(2π L k')` (the nearest mode of the fiber) and `E(|k'|₁)/π`
(every other mode of the fiber), and `E 1/(2π)` covers the fiber `k' = 0`. -/
theorem smallDivisorSup_snoc_le {m : ℕ} {ω' : Fin m → ℝ} {γ τ δ : ℝ}
    (hω : IsDiophantine γ τ (Fin.snoc ω' 1 : Fin (m + 1) → ℝ)) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) {N : ℕ} (hN : τ ≤ 2 * Real.pi * δ * (N + 1))
    (p : (Fin m → ℤ) → ℤ) (L : (Fin m → ℤ) → ℝ)
    (hp : ∀ k ∈ modeBox m N, |Diophantine.frequencyDot ω' k + p k| ≤ 1 / 2)
    (hL : ∀ k ∈ modeBox m N, 0 < L k ∧ L k ≤ |Diophantine.frequencyDot ω' k + p k|)
    (E : ℕ → ℝ) (hE : ∀ j : ℕ, Real.exp (-(2 * Real.pi * δ) * j) ≤ E j) {B : ℝ}
    (hB1 : E 1 / (2 * Real.pi) ≤ B)
    (hB : ∀ k ∈ modeBox m N, E (modeNat k + (p k).natAbs) / (2 * Real.pi * L k) ≤ B ∧
      E (modeNat k) / Real.pi ≤ B) :
    smallDivisorSup (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) δ ≤ max B (sdSupTail γ τ δ N) := by
  have hc : Diophantine.Condition (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) γ τ := hω.condition
  have hb : 0 ≤ 2 * Real.pi * δ := by positivity
  refine smallDivisorSup_le_of_forall (le_max_of_le_right (sdSupTail_nonneg hγ N)) fun K hK => ?_
  obtain ⟨k, j, rfl⟩ : ∃ (k : Fin m → ℤ) (j : ℤ), K = Fin.snoc k j :=
    ⟨Fin.init K, K (Fin.last m), (Fin.snoc_init_self K).symm⟩
  have hdot : Diophantine.frequencyDot (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) (Fin.snoc k j) =
      Diophantine.frequencyDot ω' k + j := by
    rw [frequencyDot_snoc, Fin.init_snoc, Fin.snoc_last]
  have hmodeN : modeNat (Fin.snoc k j : Fin (m + 1) → ℤ) = modeNat k + j.natAbs := by
    rw [modeNat_eq_init_add, Fin.init_snoc, Fin.snoc_last]
  have hmode : Fourier.modeSize (Fin.snoc k j : Fin (m + 1) → ℤ) =
      ((modeNat k + j.natAbs : ℕ) : ℝ) := by
    rw [modeSize_eq_modeNat, hmodeN]
  rw [hdot, hmode]
  have hEk : ∀ i : ℕ, i ≤ modeNat k + j.natAbs →
      Real.exp (-(2 * Real.pi * δ) * ((modeNat k + j.natAbs : ℕ) : ℝ)) ≤ E i := fun i hi =>
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by exact_mod_cast hi) (by linarith))).trans
      (hE i)
  by_cases hk0 : k = 0
  · -- the fiber `k' = 0`: `|k·ω| = |j| ≥ 1`
    subst hk0
    have hj0 : j ≠ 0 := by
      rintro rfl
      refine hK (funext fun i => ?_)
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    have hx0 : Diophantine.frequencyDot ω' (0 : Fin m → ℤ) = 0 := by
      simp [Diophantine.frequencyDot]
    have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj0
    have h1 : 1 ≤ modeNat (0 : Fin m → ℤ) + j.natAbs := by
      have := Int.natAbs_pos.mpr hj0
      omega
    rw [hx0, zero_add]
    refine le_max_of_le_left ((div_le_div₀ ((Real.exp_nonneg _).trans (hE 1)) (hEk 1 h1)
      (by positivity) ?_).trans hB1)
    nlinarith [Real.pi_pos]
  by_cases hkN : modeNat k ≤ N
  · have hbox : k ∈ modeBox m N := mem_modeBox.mpr ⟨hk0, hkN⟩
    obtain ⟨hL0, hLk⟩ := hL k hbox
    by_cases hjp : j = p k
    · -- the nearest mode of the fiber
      subst hjp
      refine le_max_of_le_left ((div_le_div₀ ((Real.exp_nonneg _).trans (hE _)) (hEk _ le_rfl)
        (by positivity) (mul_le_mul_of_nonneg_left hLk (by positivity))).trans (hB k hbox).1)
    · -- every other mode: `|k'·ω' + j| ≥ 1/2`
      have hjp1 : (1 : ℝ) ≤ |(j : ℝ) - p k| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjp)
      have hfar : (1 : ℝ) / 2 ≤ |Diophantine.frequencyDot ω' k + j| := by
        have h := abs_sub_abs_le_abs_sub ((j : ℝ) - p k) (-(Diophantine.frequencyDot ω' k + p k))
        rw [abs_neg, show (j : ℝ) - p k - -(Diophantine.frequencyDot ω' k + p k) =
          Diophantine.frequencyDot ω' k + j by ring] at h
        linarith [hp k hbox]
      refine le_max_of_le_left ((div_le_div₀ ((Real.exp_nonneg _).trans (hE _))
        (hEk _ (Nat.le_add_right _ _)) Real.pi_pos ?_).trans (hB k hbox).2)
      nlinarith [Real.pi_pos]
  · -- the tail `|k'|₁ > N`
    have hK' := exp_div_le_sdSupTail hc hγ hτ hN hK (by rw [hmodeN]; omega)
    rw [hdot, hmode] at hK'
    exact le_max_of_le_right hK'

end KAM

end
