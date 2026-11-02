/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Iteration.Bridge
public import KAM.Wave.Homological.ModifiedDivisors
public import KAM.Wave.Homological.Wave
public import KAM.Wave.Measure.Family
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W6: the divisor hypotheses of the preparatory step (`bpW:w6:prep-step` (i))

Blueprint label `bpW:w6:prep-step` (milestone W6), clause (i) and step `p-div`.

For `ξ ∈ Π ∖ Ξ` (W7's preparatory set `prepSet`, Definition `bpW:w7:zones` (i)) and every
`(k, l) ∈ Z`, the defining inequality of `S_{kl}` fails:
`|⟨k, ω⁰⟩ + ⟨l, Ω⁰⟩| ≥ α̂ ŵ(l)/A_k` (`w6_prep_divisors`). This uses only the unperturbed
frequencies.
With W7's Dirichlet weights it gives W5's modified conditions `(bpW:w5:modified)` with `β = 1/4`
for the wave frequencies `(waveFreqTan, waveFreqNor)` (`w6_homMelnikovMod_of_prep`): for
`l = ±(e_I - e_J)` the weight is `|I - J| min(I, J)^{-1/4}` (W5's `min(i, j) + 2 = min(I, J)`), for
the
other `l` it is `⟨l⟩`, which dominates W4's weights.
-/

@[expose] public noncomputable section

open Real Finsupp

namespace KAM.Wave

theorem coeffSum_single (a : ℕ) (σ : ℤ) : (single a σ).sum (fun _ v => v) = σ :=
  Finsupp.sum_single_index rfl

theorem coeffSum_add (l l' : ℕ →₀ ℤ) :
    (l + l').sum (fun _ v => v) = l.sum (fun _ v => v) + l'.sum (fun _ v => v) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem coeffSum_neg (l : ℕ →₀ ℤ) : (-l).sum (fun _ v => v) = -l.sum (fun _ v => v) := by
  unfold Finsupp.sum
  rw [Finsupp.support_neg, ← Finset.sum_neg_distrib]
  rfl

theorem not_isLamMinus_of_coeffSum_ne {l : ℕ →₀ ℤ} (h : l.sum (fun _ v => v) ≠ 0) :
    ¬ IsLamMinus l := by
  rintro ⟨i, j, σ, -, -, rfl⟩
  apply h
  rw [coeffSum_add, coeffSum_single, coeffSum_single]
  ring

theorem hatW_eq_japL_of_coeffSum_ne {l : ℕ →₀ ℤ} (h : l.sum (fun _ v => v) ≠ 0) :
    hatW l = japL l := by
  unfold hatW
  rw [ite_eq_right (not_isLamMinus_of_coeffSum_ne h)]

theorem l1Norm_single (a : ℕ) (σ : ℤ) : l1Norm (single a σ) = σ.natAbs := by
  unfold l1Norm
  exact Finsupp.sum_single_index rfl

theorem l1Norm_pair {a b : ℕ} (hab : a ≠ b) (σ τ : ℤ) :
    l1Norm (single a σ + single b τ) = σ.natAbs + τ.natAbs := by
  have h := sum_single_pair hab σ τ (fun _ v => ((v.natAbs : ℕ) : ℝ)) (by simp)
  have e : ((l1Norm (single a σ + single b τ) : ℕ) : ℝ) =
      (single a σ + single b τ).sum (fun _ v => ((v.natAbs : ℕ) : ℝ)) := by
    unfold l1Norm Finsupp.sum; push_cast; rfl
  have : ((l1Norm (single a σ + single b τ) : ℕ) : ℝ) = ((σ.natAbs + τ.natAbs : ℕ) : ℝ) := by
    rw [e, h]; push_cast; rfl
  exact_mod_cast this

/-- `normLab (j - 1) = j + 2` for W5's index `j : ℕ+`. -/
theorem normLab_natPred (j : ℕ+) : normLab j.natPred = (j : ℝ) + 2 := by
  have h := PNat.natPred_add_one j
  have : ((j.natPred : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) := by exact_mod_cast h
  unfold normLab
  rw [show ((j : ℕ+) : ℝ) = ((j : ℕ) : ℝ) from rfl]
  linarith

section

variable (m : ℝ) (hm : 0 < m)

/-- W4's normal wave frequencies are W7's: `Ω_j = Ω⁰_{j-1}` (W5 index `j`, W7 index `j - 1`). -/
theorem waveFreqNor_eq_omegaNor (ξ : Fin 2 → ℝ) (j : ℕ+) :
    waveFreqNor m hm ξ j = omegaNor m hm ξ j.natPred := by
  have hj : ((j + 2 : ℕ+) : ℕ) = j.natPred + 3 := by
    have := PNat.natPred_add_one j
    rw [PNat.add_coe]
    simp only [PNat.val_ofNat]
    omega
  have hL : lam m hm (j + 2) = lamN m hm j.natPred := by
    unfold lamN
    congr 1
    exact PNat.eq hj
  unfold waveFreqNor waveOmega omegaNor waveB actionBN
  rw [hL, Fin.sum_univ_two, Fin.sum_univ_two]
  have h1 : lam m hm ((0 : Fin 2) : ℕ).succPNat = lamTan m hm 0 := rfl
  have h2 : lam m hm ((1 : Fin 2) : ℕ).succPNat = lamTan m hm 1 := rfl
  rw [h1, h2]
  have := lamTan_pos m hm 0
  have := lamTan_pos m hm 1
  have : 0 < lamN m hm j.natPred := by
    unfold lamN; exact lam_pnat_pos hm _
  have := Real.pi_pos
  field_simp

/-- W4's tangential wave frequencies are W7's. -/
theorem waveFreqTan_eq_omegaTan (ξ : Fin 2 → ℝ) : waveFreqTan m hm ξ = omegaTan m hm ξ := rfl

/-- **Divisors** (`bpW:w6:prep-step` (i), step `p-div`): for `ξ ∈ Π ∖ Ξ` and `(k, l) ∈ Z`,
`|⟨k, ω⁰⟩ + ⟨l, Ω⁰⟩| ≥ α̂ ŵ(l)/A_k`. -/
theorem w6_prep_divisors {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) {k : Fin 2 → ℤ} {l : ℕ →₀ ℤ} (hkl : InZ k l) :
    alphaHat α * hatW l / kAk k ≤
      |∑ i, (k i : ℝ) * omegaTan m hm ξ i + linF l (omegaNor m hm ξ)| := by
  have hn := hξ.2
  simp only [prepSet, Set.mem_iUnion, not_exists] at hn
  by_contra hlt
  push Not at hlt
  exact hn k l hkl ⟨hξ.1, hlt⟩

/-- The divisor bound for `l = σ e_a` (`σ = ±1`), with weight `ŵ = ⟨l⟩ = a + 3`. -/
theorem w6_prep_single {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) (k : Fin 2 → ℤ) (a : ℕ) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    alphaHat α * normLab a / kAk k ≤
      |∑ i, (k i : ℝ) * omegaTan m hm ξ i + σ * omegaNor m hm ξ a| := by
  have hl : IsLam (single a σ) := by
    unfold IsLam; rw [l1Norm_single]; rcases hσ with rfl | rfl <;> simp
  have hne : single a σ ≠ 0 := by
    rw [Ne, Finsupp.single_eq_zero]; rcases hσ with rfl | rfl <;> simp
  have h := w6_prep_divisors m hm hξ (k := k) ⟨Or.inr hl, Or.inr hne⟩
  rwa [hatW_eq_japL_of_coeffSum_ne (by rw [coeffSum_single]; rcases hσ with rfl | rfl <;> simp),
    japL_single a (by rcases hσ with rfl | rfl <;> simp), linF_single,
    show |(σ : ℝ)| = 1 by rcases hσ with rfl | rfl <;> simp, one_mul] at h

/-- The divisor bound for `l = σ(e_a + e_b)` (`σ = ±1`), with weight `ŵ = ⟨l⟩ = a + b + 6`. -/
theorem w6_prep_sum {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) (k : Fin 2 → ℤ) (a b : ℕ) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    alphaHat α * (normLab a + normLab b) / kAk k ≤
      |∑ i, (k i : ℝ) * omegaTan m hm ξ i +
        σ * (omegaNor m hm ξ a + omegaNor m hm ξ b)| := by
  set l : ℕ →₀ ℤ := single a σ + single b σ
  have hσ1 : |(σ : ℝ)| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hl : IsLam l := by
    by_cases hab : a = b
    · subst hab
      have e : l = single a (σ + σ) := by simp [l, Finsupp.single_add]
      unfold IsLam; rw [e, l1Norm_single]; rcases hσ with rfl | rfl <;> simp
    · unfold IsLam; rw [l1Norm_pair hab]; rcases hσ with rfl | rfl <;> simp
  have hsum : l.sum (fun _ v => v) ≠ 0 := by
    rw [coeffSum_add, coeffSum_single, coeffSum_single]; rcases hσ with rfl | rfl <;> simp
  have hne : l ≠ 0 := fun h => hsum (by rw [h]; rfl)
  have h := w6_prep_divisors m hm hξ (k := k) ⟨Or.inr hl, Or.inr hne⟩
  have hlin : ∀ f : ℕ → ℝ, linF l f = σ * (f a + f b) := fun f => by
    rw [linF_add_single]; ring
  have hj : japL l = normLab a + normLab b := by
    unfold japL
    rw [hlin, abs_mul, hσ1, one_mul]
    have := normLab_ge a; have := normLab_ge b
    rw [abs_of_pos (by linarith)]
    exact max_eq_right (by linarith)
  rwa [hatW_eq_japL_of_coeffSum_ne hsum, hj, hlin] at h

/-- The divisor bound for `l = e_a - e_b` (`a ≠ b`), with weight
`ŵ = |a - b| (min(a, b) + 3)^{-1/4}`. -/
theorem w6_prep_diff {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) (k : Fin 2 → ℤ) {a b : ℕ} (hab : a ≠ b) :
    alphaHat α * (|(a : ℝ) - b| * normLab (min a b) ^ (-(1 / 4 : ℝ))) / kAk k ≤
      |∑ i, (k i : ℝ) * omegaTan m hm ξ i + (omegaNor m hm ξ a - omegaNor m hm ξ b)| := by
  have key : ∀ {i j : ℕ}, j < i → ∀ σ : ℤ, (σ = 1 ∨ σ = -1) →
      alphaHat α * (((i : ℝ) - j) * normLab j ^ (-(1 / 4 : ℝ))) / kAk k ≤
        |∑ i', (k i' : ℝ) * omegaTan m hm ξ i' +
          σ * (omegaNor m hm ξ i - omegaNor m hm ξ j)| := by
    intro i j hji σ hσ
    have hm' : IsLamMinus (single i σ + single j (-σ)) := ⟨i, j, σ, hji, hσ, rfl⟩
    have hne : single i σ + single j (-σ) ≠ 0 := fun h => by
      have := congrArg (fun f => f i) h
      simp [hji.ne] at this
      rcases hσ with rfl | rfl <;> simp at this
    have h := w6_prep_divisors m hm hξ (k := k) ⟨Or.inr (IsLam_of_minus hm'), Or.inr hne⟩
    rwa [hatW_minus hji hσ, linF_minus hji] at h
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · have h := key hlt (-1) (Or.inr rfl)
    have hab' : (a : ℝ) < b := by exact_mod_cast hlt
    have e1 : |(a : ℝ) - b| = (b : ℝ) - a := by
      rw [abs_sub_comm, abs_of_pos (by linarith)]
    rw [e1, min_eq_left hlt.le]
    refine le_of_le_of_eq h ?_
    congr 2
    push_cast; ring
  · have h := key hlt 1 (Or.inl rfl)
    have hab' : (b : ℝ) < a := by exact_mod_cast hlt
    have e1 : |(a : ℝ) - b| = (a : ℝ) - b := by
      rw [abs_of_pos (by linarith)]
    rw [e1, min_eq_right hlt.le]
    refine le_of_le_of_eq h ?_
    congr 2
    push_cast; ring

/-- The divisor bound for `l = 0`, `k ≠ 0`. -/
theorem w6_prep_zero {Pi : Set (Fin 2 → ℝ)} {α : ℝ} {ξ : Fin 2 → ℝ}
    (hξ : ξ ∈ Pi \ prepSet m hm Pi α) {k : Fin 2 → ℤ} (hk : k ≠ 0) :
    alphaHat α / kAk k ≤ |∑ i, (k i : ℝ) * omegaTan m hm ξ i| := by
  have h := w6_prep_divisors m hm hξ (k := k) (l := 0) ⟨Or.inl rfl, Or.inl hk⟩
  have hnot : ¬ IsLamMinus (0 : ℕ →₀ ℤ) := by
    rintro ⟨i, j, σ, hji, hσ, h⟩
    have := congrArg (fun f => f i) h
    simp [hji.ne] at this
    rcases hσ with rfl | rfl <;> simp at this
  have hw : hatW 0 = 1 := by
    unfold hatW; rw [ite_eq_right hnot]; unfold japL linF; simp
  have hl0 : linF 0 (omegaNor m hm ξ) = 0 := by unfold linF; simp
  rwa [hw, mul_one, hl0, add_zero] at h

theorem natPred_cast (j : ℕ+) : ((j.natPred : ℕ) : ℝ) = (j : ℝ) - 1 := by
  have h := PNat.natPred_add_one j
  have : ((j.natPred : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) := by exact_mod_cast h
  rw [show ((j : ℕ+) : ℝ) = ((j : ℕ) : ℝ) from rfl]
  linarith

/-- **Divisor hypotheses of the preparatory step** (`bpW:w6:prep-step` (i), step `p-div`): on
`Π ∖ Ξ` the wave frequencies satisfy W5's modified conditions `(bpW:w5:modified)` at level
`α̂ = α^{44/47}` with `β = 1/4` and `τ = 24`. -/
theorem w6_homMelnikovMod_of_prep {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (hα : 0 < α) :
    HomMelnikovMod 24 (alphaHat α) (1 / 4) (Pi \ prepSet m hm Pi α) (waveFreqTan m hm)
      (waveFreqNor m hm) := by
  have hαh : 0 < alphaHat α := Real.rpow_pos_of_pos hα _
  have hA : ∀ k, 0 < kAk k := fun k => lt_of_lt_of_le one_pos (kAk_pos k)
  have hj0 : ∀ j : ℕ+, (0 : ℝ) < j := fun j => by exact_mod_cast j.pos
  -- the weight comparison `α̂ w/A ≤ α̂ w'/A` for `w ≤ w'`
  have hw : ∀ (k : Fin 2 → ℤ) {w w' : ℝ}, w ≤ w' →
      alphaHat α * w / kAk k ≤ alphaHat α * w' / kAk k := fun k _ _ h =>
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hαh.le) (hA k).le
  refine ⟨fun ξ hξ k hk => ?_, fun ξ hξ k j => ?_, fun ξ hξ k j => ?_, fun ξ hξ k i j => ?_,
    fun ξ hξ k i j => ?_, fun ξ hξ k hk j => ?_, fun ξ hξ k i j hij => ?_⟩
  · have h := w6_prep_zero m hm hξ hk
    rw [mul_one, ← kAk_eq_waveA]
    exact h
  · have h := w6_prep_single m hm hξ k j.natPred (σ := -1) (Or.inr rfl)
    rw [normLab_natPred, ← waveFreqNor_eq_omegaNor] at h
    rw [← kAk_eq_waveA]
    refine (hw k (by linarith)).trans (h.trans_eq ?_)
    unfold homDeltaPlus; rw [homPairZ_eq_sum, waveFreqTan_eq_omegaTan]; congr 1; push_cast; ring
  · have h := w6_prep_single m hm hξ k j.natPred (σ := 1) (Or.inl rfl)
    rw [normLab_natPred, ← waveFreqNor_eq_omegaNor] at h
    rw [← kAk_eq_waveA]
    refine (hw k (by linarith)).trans (h.trans_eq ?_)
    unfold homDeltaMinus; rw [homPairZ_eq_sum, waveFreqTan_eq_omegaTan]; congr 1; push_cast; ring
  · have h := w6_prep_sum m hm hξ k i.natPred j.natPred (σ := -1) (Or.inr rfl)
    rw [normLab_natPred, normLab_natPred, ← waveFreqNor_eq_omegaNor,
      ← waveFreqNor_eq_omegaNor] at h
    rw [← kAk_eq_waveA]
    refine (hw k (by linarith)).trans (h.trans_eq ?_)
    unfold homDeltaP; rw [homPairZ_eq_sum, waveFreqTan_eq_omegaTan]; congr 1; push_cast; ring
  · have h := w6_prep_sum m hm hξ k i.natPred j.natPred (σ := 1) (Or.inl rfl)
    rw [normLab_natPred, normLab_natPred, ← waveFreqNor_eq_omegaNor,
      ← waveFreqNor_eq_omegaNor] at h
    rw [← kAk_eq_waveA]
    refine (hw k (by linarith)).trans (h.trans_eq ?_)
    unfold homDeltaP'; rw [homPairZ_eq_sum, waveFreqTan_eq_omegaTan]; congr 1; push_cast; ring
  · have h := w6_prep_zero m hm hξ hk
    rw [mul_one, ← kAk_eq_waveA]
    refine h.trans_eq ?_
    unfold homDeltaQ; rw [homPairZ_eq_sum, waveFreqTan_eq_omegaTan]; congr 1; ring
  · have hab : i.natPred ≠ j.natPred := fun h => hij (by
      have := congrArg Nat.succPNat h
      rwa [PNat.succPNat_natPred, PNat.succPNat_natPred] at this)
    have h := w6_prep_diff m hm hξ k hab
    rw [← waveFreqNor_eq_omegaNor, ← waveFreqNor_eq_omegaNor, natPred_cast, natPred_cast] at h
    have hmin : normLab (min i.natPred j.natPred) = min (i : ℝ) j + 2 := by
      unfold normLab
      rw [Nat.cast_min, natPred_cast, natPred_cast, min_sub_sub_right]
      ring
    rw [hmin] at h
    have hM : 0 < min (i : ℝ) j + 2 := by have := hj0 i; have := hj0 j; positivity
    rw [← kAk_eq_waveA]
    refine le_of_eq_of_le ?_ (h.trans_eq ?_)
    · rw [Real.rpow_neg hM.le, sub_sub_sub_cancel_right]
      field_simp
    · unfold homDeltaQ; rw [homPairZ_eq_sum, waveFreqTan_eq_omegaTan]; congr 1; ring

end

end KAM.Wave
