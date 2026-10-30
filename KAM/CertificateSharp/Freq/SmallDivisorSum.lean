/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalSumCert
public import KAM.Certificate.Freq
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# A rational upper bound of the small-divisor sum from a frequency box

For a frequency box (`KAM.Certificate.FreqBox`, the certificate's own datum), `sdsCheck`
verifies over `ℚ` that the modes `0 < |k|₁ ≤ N` have a positive box lower bound
`L_k = |k·c| - ∑ |k_i| r_i` of `|k·ω|`, and `sdsBound` is the rational
`∑_{k ∈ modeBox n N} L_k⁻² E₁^{|k|₁} + T̂` (the real-analysis theorem
`KAM.smallDivisorSum_le_box_add_tail`). The exponential is bounded by the Taylor polynomial of
degree `J` of `e^{6.28 δ}` (`E₁ ≥ e^{-2πδ}`) and the tail `T_N` by `KAM.sdTail_le` at `τ = 1`,
`π ∈ (3.14, 3.15)`.

`sdsBound_sound`: for every `ω` in the box that is `(γ, 1)`-Diophantine,
`S(ω, δ) ≤ sdsBound`. `sdsStagesOk_sound` is the stage list `δ_s` (one claimed bound per stage).
The cost of `sdsBound` is the number of modes of the box, `≈ 4N²` for `n = 2`
(design `CERTIFIER-SHARPNESS` §2.6 sketches a row-wise `O(N)` evaluation, not implemented).
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Certificate

variable {n : ℕ}

/-- `∑ k_i c_i` for the box centre `c`. -/
def boxDot (box : FreqBox) (k : Fin n → ℤ) : ℚ := ∑ j : Fin n, (k j : ℚ) * (box.getD j.val (0, 0)).1

/-- `∑ |k_i| r_i` for the box radius `r`. -/
def boxRad (box : FreqBox) (k : Fin n → ℤ) : ℚ :=
  ∑ j : Fin n, |(k j : ℚ)| * (box.getD j.val (0, 0)).2

/-- The lower bound `|k·c| - ∑ |k_i| r_i` of `|k·ω|` on the box. -/
def boxLb (box : FreqBox) (k : Fin n → ℤ) : ℚ := |boxDot box k| - boxRad box k

theorem dot_sub_boxDot_le {box : FreqBox} {ω : Fin n → ℝ} (h : FreqEncloses n box ω)
    (k : Fin n → ℤ) :
    |Diophantine.frequencyDot ω k - (boxDot box k : ℝ)| ≤ (boxRad box k : ℝ) := by
  have e : Diophantine.frequencyDot ω k - (boxDot box k : ℝ) =
      ∑ j : Fin n, (k j : ℝ) * (ω j - ((box.getD j.val (0, 0)).1 : ℝ)) := by
    unfold Diophantine.frequencyDot boxDot
    push_cast
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  unfold boxRad
  push_cast
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (h j) (abs_nonneg _)

theorem boxLb_le {box : FreqBox} {ω : Fin n → ℝ} (h : FreqEncloses n box ω) (k : Fin n → ℤ) :
    (boxLb box k : ℝ) ≤ |Diophantine.frequencyDot ω k| := by
  unfold boxLb
  have h1 := dot_sub_boxDot_le h k
  push_cast
  have := abs_sub_abs_le_abs_sub (boxDot box k : ℝ) (Diophantine.frequencyDot ω k)
  rw [abs_sub_comm] at this
  linarith

/-- The data of one bound: a frequency box, the Diophantine constant `γ` (with `τ = 1`), `δ`,
the cut-off `N` and the degree `J` of the exponential Taylor polynomial. -/
structure SdsData where
  /-- The frequency box. -/
  box : FreqBox
  /-- The Diophantine constant (`τ = 1`). -/
  γ : ℚ
  /-- The strip parameter of `S(ω, δ)`. -/
  δ : ℚ
  /-- The mode cut-off. -/
  N : ℕ
  /-- The degree of the exponential lower polynomial. -/
  J : ℕ
  /-- A (short) rational upper bound of `e^{-2πδ}`, checked against the Taylor polynomial. -/
  E1 : ℚ

namespace SdsData

variable (d : SdsData)

/-- The Taylor polynomial of `e^{6.28 δ}`, a lower bound of `e^{2πδ}`. -/
def expLow : ℚ := ∑ i ∈ Finset.range (d.J + 1), (628 / 100 * d.δ) ^ i / (i.factorial : ℚ)

/-- The lower bound `c ≤ 2πδ - 2/(N+1)` entering the tail. -/
def cLo : ℚ := 628 / 100 * d.δ - 2 / (d.N + 1)

/-- The finite part `∑_{0<|k|₁≤N} L_k⁻² E₁^{|k|₁}`. -/
def boxSum : ℚ := ∑ k ∈ modeBox n d.N, ((boxLb d.box k) ^ 2)⁻¹ * d.E1 ^ modeNat k

/-- The rational bound of the tail `T_N`. -/
def tailBound : ℚ :=
  2 * (1 + 2) * (d.γ ^ 2)⁻¹ * (63 / 10 * d.δ) * (((d.N : ℚ) + 1) ^ 2 * d.E1 ^ (d.N + 1)) *
    (1 + (d.cLo)⁻¹)

/-- The certified bound of `S(ω, δ)`. -/
def bound : ℚ := (d.boxSum (n := n)) + d.tailBound

/-- The side conditions, over `ℚ`. -/
def check : Bool :=
  decide (0 < d.γ) && decide (0 < d.δ) && decide (0 < d.cLo) && decide (1 ≤ d.E1 * d.expLow) &&
    decide (∀ k ∈ modeBox n d.N, 0 < boxLb d.box k)

end SdsData

lemma exp_neg_le_E1 (d : SdsData) (hδ : 0 < (d.δ : ℝ)) (hE1 : 1 ≤ d.E1 * d.expLow) :
    Real.exp (-(2 * Real.pi * d.δ)) ≤ (d.E1 : ℝ) := by
  have hpi := Real.pi_gt_d2
  have hx : (0 : ℝ) ≤ 628 / 100 * d.δ := by positivity
  have h1 : ((d.expLow : ℚ) : ℝ) ≤ Real.exp (628 / 100 * d.δ) := by
    unfold SdsData.expLow
    push_cast
    exact Real.sum_le_exp_of_nonneg hx _
  have h2 : Real.exp (628 / 100 * d.δ) ≤ Real.exp (2 * Real.pi * d.δ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hlow : 0 < ((d.expLow : ℚ) : ℝ) := by
    unfold SdsData.expLow
    push_cast
    have : (0 : ℝ) <
        ∑ i ∈ Finset.range (d.J + 1), (628 / 100 * (d.δ : ℝ)) ^ i / (i.factorial : ℝ) :=
      Finset.sum_pos (fun i _ => by positivity) ⟨0, by simp⟩
    exact this
  rw [Real.exp_neg]
  refine (inv_anti₀ hlow (h1.trans h2)).trans ?_
  have : (1 : ℝ) ≤ (d.E1 : ℝ) * d.expLow := by exact_mod_cast hE1
  rw [inv_le_iff_one_le_mul₀' hlow]
  linarith

/-- The exponential and tail hypotheses of the side conditions. -/
theorem sds_tail_le (d : SdsData) (hγ : 0 < d.γ) (hδ : 0 < d.δ) (hc : 0 < d.cLo)
    (hE1 : 1 ≤ d.E1 * d.expLow) :
    2 * (1 : ℝ) < 2 * Real.pi * d.δ * (d.N + 1) ∧ Real.exp (-(2 * Real.pi * d.δ)) ≤ d.E1 ∧
      sdTail (d.γ : ℝ) 1 d.δ d.N ≤ (d.tailBound : ℝ) := by
  have hγ' : (0 : ℝ) < d.γ := by exact_mod_cast hγ
  have hδ' : (0 : ℝ) < d.δ := by exact_mod_cast hδ
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  have hN1 : (0 : ℝ) < (d.N : ℝ) + 1 := by positivity
  have hcLo : (0 : ℝ) < (628 / 100 * d.δ - 2 / ((d.N : ℝ) + 1)) := by
    have : (0 : ℝ) < ((d.cLo : ℚ) : ℝ) := by exact_mod_cast hc
    unfold SdsData.cLo at this
    push_cast at this
    exact this
  have hN : 2 * (1 : ℝ) < 2 * Real.pi * d.δ * (d.N + 1) := by
    have h1 : 2 / ((d.N : ℝ) + 1) < 628 / 100 * d.δ := by linarith
    rw [div_lt_iff₀ hN1] at h1
    nlinarith
  have hE := exp_neg_le_E1 d hδ' hE1
  have hE0 : (0 : ℝ) ≤ (d.E1 : ℝ) := (Real.exp_pos _).le.trans hE
  refine ⟨hN, hE, ?_⟩
  · -- the tail
    have hE' : Real.exp (-(2 * Real.pi * d.δ) * (d.N + 1)) ≤ (d.E1 : ℝ) ^ (d.N + 1) := by
      calc Real.exp (-(2 * Real.pi * d.δ) * (d.N + 1))
          = Real.exp (-(2 * Real.pi * d.δ)) ^ (d.N + 1) := by
            rw [← Real.exp_nat_mul]; push_cast; ring_nf
        _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hE _
    refine (sdTail_le (γ := d.γ) (τ := 1) hδ' hN hE').trans ?_
    unfold SdsData.tailBound SdsData.cLo
    push_cast
    set E' : ℝ := (d.E1 : ℝ) ^ (d.N + 1) with hE'def
    have hE'0 : 0 ≤ E' := pow_nonneg hE0 _
    have hcge : (628 / 100 * (d.δ : ℝ) - 2 / ((d.N : ℝ) + 1)) ≤
        2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1) := by
      rw [mul_one]; nlinarith
    have hfrac : (1 + (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1))) /
        (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1)) ≤
        1 + (628 / 100 * (d.δ : ℝ) - 2 / ((d.N : ℝ) + 1))⁻¹ := by
      set c : ℝ := 2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1) with hc
      have hc0 : 0 < c := lt_of_lt_of_le hcLo hcge
      rw [add_div, div_self hc0.ne', ← one_div, add_comm]
      gcongr
    have hc0 : 0 < 2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1) := lt_of_lt_of_le hcLo hcge
    have hfr0 : 0 ≤ (1 + (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1))) /
        (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1)) := div_nonneg (by linarith) hc0.le
    have hpow : ((d.N : ℝ) + 1) ^ (2 * (1 : ℝ)) = ((d.N : ℝ) + 1) ^ 2 := by
      rw [show (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hpow]
    have hb : 2 * Real.pi * d.δ ≤ 63 / 10 * d.δ := by nlinarith
    have hC : 0 ≤ 2 * (1 + 2 ^ (1 : ℝ)) * ((d.γ : ℝ) ^ 2)⁻¹ := by positivity
    have hP : 0 ≤ ((d.N : ℝ) + 1) ^ 2 * E' := by positivity
    have h1 : 0 ≤ (1 : ℝ) + (628 / 100 * (d.δ : ℝ) - 2 / ((d.N : ℝ) + 1))⁻¹ := by
      have := inv_pos.mpr hcLo; linarith
    rw [Real.rpow_one]
    calc 2 * (1 + 2) * ((d.γ : ℝ) ^ 2)⁻¹ * (2 * Real.pi * d.δ) * (((d.N : ℝ) + 1) ^ 2 * E') *
          ((1 + (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1))) /
            (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1)))
        ≤ 2 * (1 + 2) * ((d.γ : ℝ) ^ 2)⁻¹ * (63 / 10 * d.δ) * (((d.N : ℝ) + 1) ^ 2 * E') *
          ((1 + (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1))) /
            (2 * Real.pi * d.δ - 2 * 1 / ((d.N : ℝ) + 1))) := by
          refine mul_le_mul_of_nonneg_right ?_ hfr0
          have : (0 : ℝ) ≤ 2 * (1 + 2) * ((d.γ : ℝ) ^ 2)⁻¹ := by positivity
          refine mul_le_mul_of_nonneg_right ?_ hP
          exact mul_le_mul_of_nonneg_left hb this
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left hfrac ?_
          have : (0 : ℝ) ≤ 63 / 10 * d.δ := by positivity
          positivity

/-- **Soundness of the rational small-divisor bound.** -/
theorem sdsBound_sound (d : SdsData) (h : d.check (n := n) = true) {ω : Fin n → ℝ}
    (hω : FreqEncloses n d.box ω) (hdio : IsDiophantine (d.γ : ℝ) 1 ω) :
    smallDivisorSum ω (d.δ : ℝ) ≤ (d.bound (n := n) : ℝ) := by
  simp only [SdsData.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hγ, hδ⟩, hc⟩, hE1⟩, hL⟩ := h
  obtain ⟨hN, hE, htail⟩ := sds_tail_le d hγ hδ hc hE1
  have hγ' : (0 : ℝ) < d.γ := by exact_mod_cast hγ
  have hδ' : (0 : ℝ) < d.δ := by exact_mod_cast hδ
  have hE0 : (0 : ℝ) ≤ (d.E1 : ℝ) := (Real.exp_pos _).le.trans hE
  -- the box part and the tail
  have key := smallDivisorSum_le_box_add_tail hdio hγ' (by norm_num : (0 : ℝ) ≤ 1) hδ' hN
    (fun k => (boxLb d.box k : ℝ)) (fun k hk => ⟨by exact_mod_cast hL k hk, boxLb_le hω k⟩)
    (fun m => (d.E1 : ℝ) ^ m) (fun m hm _ => by
      calc Real.exp (-(2 * Real.pi * d.δ) * m) = Real.exp (-(2 * Real.pi * d.δ)) ^ m := by
            rw [← Real.exp_nat_mul]; ring_nf
        _ ≤ (d.E1 : ℝ) ^ m := pow_le_pow_left₀ (Real.exp_pos _).le hE m)
  refine key.trans ?_
  unfold SdsData.bound
  push_cast
  refine add_le_add (le_of_eq ?_) ?_
  · unfold SdsData.boxSum
    push_cast
    rfl
  · exact htail

/-- One stage of a list: the strip parameter, cut-off, degree, exponential bound and the claimed
bound of `S(ω, δ)`. -/
structure SdsStage where
  /-- The strip parameter of the sum. -/
  δ : ℚ
  /-- The mode cut-off. -/
  N : ℕ
  /-- The degree of the exponential polynomial. -/
  J : ℕ
  /-- The rational upper bound of `e^{-2πδ}`. -/
  E1 : ℚ
  /-- The claimed bound of `S(ω, δ)`. -/
  claim : ℚ

/-- The data of a stage over a common box and constant. -/
def SdsStage.data (box : FreqBox) (γ : ℚ) (st : SdsStage) : SdsData :=
  { box := box, γ := γ, δ := st.δ, N := st.N, J := st.J, E1 := st.E1 }

/-- All stages of a list pass and are bounded by their claim. -/
def sdsStagesOk (n : ℕ) (box : FreqBox) (γ : ℚ) (stages : List SdsStage) : Bool :=
  stages.all fun st =>
    (st.data box γ).check (n := n) && decide ((st.data box γ).bound (n := n) ≤ st.claim)

/-- The halving ladder `δ_s = δ₀ / 2^s`. -/
def stageDelta (δ0 : ℚ) (s : ℕ) : ℚ := δ0 / 2 ^ s

/-- **Soundness of the stage list**: for `ω` in the box and `(γ, 1)`-Diophantine, every stage's
claim bounds `S(ω, δ_s)`. -/
theorem sdsStagesOk_sound {box : FreqBox} {γ : ℚ} {stages : List SdsStage}
    (h : sdsStagesOk n box γ stages = true) {ω : Fin n → ℝ} (hω : FreqEncloses n box ω)
    (hdio : IsDiophantine (γ : ℝ) 1 ω) :
    ∀ st ∈ stages, smallDivisorSum ω (st.δ : ℝ) ≤ (st.claim : ℝ) := by
  intro st hst
  unfold sdsStagesOk at h
  rw [List.all_eq_true] at h
  have := h st hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  have hb := sdsBound_sound (st.data box γ) this.1 hω hdio
  refine hb.trans ?_
  exact_mod_cast this.2

end KAM.CertificateSharp
