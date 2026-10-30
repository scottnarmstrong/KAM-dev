/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalSumSeries
public import KAM.Diophantine.Frozen
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Certified upper bounds of the small-divisor series

For a given `(γ, τ)`-Diophantine `ω` and `δ > 0`, `KAM.smallDivisorSum_le_box_add_tail`:
`S(ω, δ) ≤ F_N + T_N`, where

* `F_N = ∑_{0<|k|₁≤N} L_k⁻² E_{|k|₁}` is a finite sum over `KAM.modeBox n N`, from data: lower
  bounds `0 < L_k ≤ |k·ω|` and upper bounds `E_m ≥ e^{-2πδm}` (for instance from rational
  enclosures of `ω` and of the exponential, supplied and checked by a certificate);
* `T_N = KAM.sdTail γ τ δ N = C (1 - e^{-b}) (N+1)^{2τ} e^{-b(N+1)} / (1 - e^{-(b - 2τ/(N+1))})`
  is an explicit tail bound for `|k|₁ > N`, with `b = 2πδ`, `C = 2(1 + 2^τ)γ⁻²` and `2τ < b(N+1)`.

The tail is the separation/shell argument of `KAM.Strip.CohomologicalRussmannSep`: the shell sums
`S_m = ∑_{0<|k|₁≤m} |k·ω|⁻² ≤ C m^{2τ}` (`KAM.sum_inv_sq_frequencyDot_le`) are combined with the
weights `e^{-bm}` by discrete Abel summation (`KAM.abel_finite`); the shells `m ≤ N` do not occur,
and for `m ≥ N + 1`, `m^{2τ} e^{-bm} ≤ (N+1)^{2τ} e^{-b(N+1)} r^{m-N-1}` with
`r = e^{-(b - 2τ/(N+1))}`
(`KAM.rpow_mul_exp_le_geom`, from `1 + x ≤ e^x`), a geometric series. The boundary term of the Abel
sum tends to `0` as the cut-off grows. `KAM.sdTail_le` replaces `T_N` by an expression with only
`b`, `(N+1)^{2τ}`, an upper bound of `e^{-b(N+1)}` and `c = b - 2τ/(N+1)`, for a rational checker.
-/

public noncomputable section

open Filter Topology

namespace KAM

variable {n : ℕ}

/-- The finite set of modes `0 < |k|₁ ≤ N`. -/
@[expose] def modeBox (n N : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) N).filter
    (fun k => k ≠ 0 ∧ modeNat k ≤ N)

theorem mem_modeBox {N : ℕ} {k : Fin n → ℤ} : k ∈ modeBox n N ↔ k ≠ 0 ∧ modeNat k ≤ N := by
  unfold modeBox
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
  have hj : (k j).natAbs ≤ modeNat k :=
    Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have habs : |k j| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hj.trans h.2
  rw [Finset.mem_Icc]
  exact abs_le.mp habs

/-- The tail bound `T_N = C (1 - e^{-b}) (N+1)^{2τ} e^{-b(N+1)} / (1 - e^{-(b - 2τ/(N+1))})`, with
`b = 2πδ` and `C = 2(1 + 2^τ)γ⁻²`. -/
@[expose] def sdTail (γ τ δ : ℝ) (N : ℕ) : ℝ :=
  2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (1 - Real.exp (-(2 * Real.pi * δ))) *
      ((N + 1 : ℝ) ^ (2 * τ) * Real.exp (-(2 * Real.pi * δ) * (N + 1))) /
    (1 - Real.exp (-(2 * Real.pi * δ - 2 * τ / (N + 1))))

/-- `m^{2τ} e^{-bm} ≤ (N+1)^{2τ} e^{-b(N+1)} e^{-(b - 2τ/(N+1))(m - N - 1)}` for `m ≥ N + 1`
(from `(1 + x)^{2τ} ≤ e^{2τx}`). -/
theorem rpow_mul_exp_le_geom {τ b : ℝ} (hτ : 0 ≤ τ) {N m : ℕ} (hm : N + 1 ≤ m) :
    (m : ℝ) ^ (2 * τ) * Real.exp (-b * m) ≤
      (N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1)) *
        Real.exp (-(b - 2 * τ / (N + 1))) ^ (m - (N + 1)) := by
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  set j : ℕ := m - (N + 1) with hj
  have hmj : (m : ℝ) = (N + 1 : ℝ) + j := by
    rw [hj, Nat.cast_sub hm]
    push_cast
    ring
  set x : ℝ := (j : ℝ) / (N + 1) with hx
  have hx0 : 0 ≤ x := by positivity
  have hm' : (m : ℝ) = (N + 1) * (1 + x) := by
    rw [hmj, hx]
    field_simp
  have h1 : (m : ℝ) ^ (2 * τ) ≤ (N + 1 : ℝ) ^ (2 * τ) * Real.exp (2 * τ * x) := by
    rw [hm', Real.mul_rpow hN1.le (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN1.le _)
    calc (1 + x) ^ (2 * τ) ≤ Real.exp x ^ (2 * τ) :=
          Real.rpow_le_rpow (by positivity) (by linarith [Real.add_one_le_exp x]) (by positivity)
      _ = Real.exp (2 * τ * x) := by rw [← Real.exp_mul, mul_comm]
  have h2 : Real.exp (-(b - 2 * τ / (N + 1))) ^ j = Real.exp (j * -(b - 2 * τ / (N + 1))) :=
    (Real.exp_nat_mul _ j).symm
  calc (m : ℝ) ^ (2 * τ) * Real.exp (-b * m)
      ≤ (N + 1 : ℝ) ^ (2 * τ) * Real.exp (2 * τ * x) * Real.exp (-b * m) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (N + 1 : ℝ) ^ (2 * τ) * Real.exp (2 * τ * x + -b * m) := by
        rw [Real.exp_add]
        ring
    _ = (N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1) + j * -(b - 2 * τ / (N + 1))) := by
        congr 2
        rw [hx, hmj]
        field_simp
        ring
    _ = _ := by
        rw [h2, Real.exp_add]
        ring

section Tail

variable {ω : Fin n → ℝ} {γ τ δ : ℝ}

/-- **The tail.** If every mode of `F` has `|k|₁ > N` and `2τ < 2πδ(N + 1)`, then
`∑_{k∈F} |k·ω|⁻² e^{-2πδ|k|₁} ≤ T_N`. -/
theorem sum_smallDivisorTerm_tail_le (hω : Diophantine.Condition ω γ τ) (hγ : 0 < γ)
    (hτ : 0 ≤ τ) (hδ : 0 < δ) {N : ℕ} (hN : 2 * τ < 2 * Real.pi * δ * (N + 1))
    (F : Finset (Fin n → ℤ)) (hF : ∀ k ∈ F, N < modeNat k) :
    ∑ k ∈ F, smallDivisorTerm ω δ k ≤ sdTail γ τ δ N := by
  classical
  set b : ℝ := 2 * Real.pi * δ with hb
  have hb0 : 0 < b := by positivity
  set C : ℝ := 2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ with hC
  have hC0 : 0 ≤ C := by positivity
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  set c : ℝ := b - 2 * τ / (N + 1) with hc
  have hc0 : 0 < c := by
    rw [hc, sub_pos, div_lt_iff₀ hN1]
    linarith
  set r : ℝ := Real.exp (-c) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set P : ℝ := (N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1)) with hP
  have hP0 : 0 ≤ P := by positivity
  have he1 : 0 ≤ 1 - Real.exp (-b) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  set K : ℝ := C * (1 - Real.exp (-b)) * P with hK
  have hK0 : 0 ≤ K := by positivity
  have hT : sdTail γ τ δ N = K / (1 - r) := by
    rw [sdTail, hK, hP, hC, hr, hc, hb]
  have hk0 : ∀ k ∈ F, k ≠ 0 := fun k hk h => by
    have := hF k hk
    rw [h] at this
    simp [modeNat] at this
  set a : (Fin n → ℤ) → ℝ := fun k => ((Diophantine.frequencyDot ω k) ^ 2)⁻¹ with ha
  set w : ℕ → ℝ := fun m => Real.exp (-b * m) with hw
  have hterm : ∀ k ∈ F, smallDivisorTerm ω δ k = a k * w (modeNat k) := fun k hk => by
    rw [smallDivisorTerm_of_ne (hk0 k hk), modeSize_eq_modeNat]
  -- the shells
  have hshell : ∀ m : ℕ, 1 ≤ m →
      ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k ≤ C * (m : ℝ) ^ (2 * τ) := fun m hm =>
    sum_inv_sq_frequencyDot_le hω hγ hτ hm _ fun k hk =>
      ⟨hk0 k (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  have hempty : ∀ m : ℕ, m ≤ N → ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k = 0 := by
    intro m hm
    rw [Finset.filter_false_of_mem fun k hk => by have := hF k hk; omega, Finset.sum_empty]
  -- the Abel sum up to a cut-off `M`
  have hmain : ∀ M : ℕ, N + 1 ≤ M → (∀ k ∈ F, modeNat k ≤ M) →
      ∑ k ∈ F, smallDivisorTerm ω δ k ≤ K / (1 - r) + C * P * r ^ (M - (N + 1)) := by
    intro M hM hFM
    have hm : ∀ k ∈ F, 1 ≤ modeNat k ∧ modeNat k ≤ M := fun k hk =>
      ⟨by have := hF k hk; omega, hFM k hk⟩
    rw [Finset.sum_congr rfl hterm, abel_finite F modeNat a w M hm]
    set h : ℕ → ℝ := fun m => if N + 1 ≤ m then K * r ^ (m - (N + 1)) else 0 with hh
    have hfirst : ∀ m ∈ Finset.Ico 1 M,
        (w m - w (m + 1)) * ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k ≤ h m := by
      intro m hm1
      have hm1' : 1 ≤ m := (Finset.mem_Ico.mp hm1).1
      have hd : w m - w (m + 1) = (1 - Real.exp (-b)) * Real.exp (-b * m) := by
        simp only [hw]
        rw [show -b * ((m + 1 : ℕ) : ℝ) = -b * m + -b by push_cast; ring, Real.exp_add]
        ring
      by_cases hNm : N + 1 ≤ m
      · have hhm : h m = K * r ^ (m - (N + 1)) := by simp only [hh, hNm, ↓reduceIte]
        rw [hhm, hd]
        calc (1 - Real.exp (-b)) * Real.exp (-b * m) *
              ∑ k ∈ F.filter (fun k => modeNat k ≤ m), a k
            ≤ (1 - Real.exp (-b)) * Real.exp (-b * m) * (C * (m : ℝ) ^ (2 * τ)) :=
              mul_le_mul_of_nonneg_left (hshell m hm1') (by positivity)
          _ = C * (1 - Real.exp (-b)) * ((m : ℝ) ^ (2 * τ) * Real.exp (-b * m)) := by ring
          _ ≤ C * (1 - Real.exp (-b)) * (P * r ^ (m - (N + 1))) :=
              mul_le_mul_of_nonneg_left (rpow_mul_exp_le_geom hτ hNm) (by positivity)
          _ = K * r ^ (m - (N + 1)) := by rw [hK]; ring
      · have hhm : h m = 0 := by simp only [hh, hNm, ↓reduceIte]
        rw [hhm, hempty m (by omega), mul_zero]
    have hgeo : ∑ m ∈ Finset.Ico 1 M, h m ≤ K / (1 - r) := by
      have hfilt : (Finset.Ico 1 M).filter (fun m => N + 1 ≤ m) = Finset.Ico (N + 1) M := by
        ext m
        simp only [Finset.mem_filter, Finset.mem_Ico]
        omega
      have hrN : r ^ (N + 1) ≠ 0 := pow_ne_zero _ hr0.ne'
      calc ∑ m ∈ Finset.Ico 1 M, h m
          = ∑ m ∈ Finset.Ico (N + 1) M, K * r ^ (m - (N + 1)) := by
            rw [← hfilt, Finset.sum_filter]
          _ = ∑ m ∈ Finset.Ico (N + 1) M, K / r ^ (N + 1) * r ^ m := by
            refine Finset.sum_congr rfl fun m hm => ?_
            rw [pow_sub₀ r hr0.ne' (Finset.mem_Ico.mp hm).1]
            field_simp
          _ = K / r ^ (N + 1) * ∑ m ∈ Finset.Ico (N + 1) M, r ^ m := by rw [Finset.mul_sum]
          _ ≤ K / r ^ (N + 1) * (r ^ (N + 1) / (1 - r)) :=
            mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0.le hr1) (by positivity)
          _ = K / (1 - r) := by field_simp
    have hsecond : w M * ∑ k ∈ F, a k ≤ C * P * r ^ (M - (N + 1)) := by
      have hFa : ∑ k ∈ F, a k ≤ C * (M : ℝ) ^ (2 * τ) :=
        sum_inv_sq_frequencyDot_le hω hγ hτ (by omega) F fun k hk => ⟨hk0 k hk, hFM k hk⟩
      calc w M * ∑ k ∈ F, a k ≤ Real.exp (-b * M) * (C * (M : ℝ) ^ (2 * τ)) :=
            mul_le_mul_of_nonneg_left hFa (Real.exp_pos _).le
        _ = C * ((M : ℝ) ^ (2 * τ) * Real.exp (-b * M)) := by ring
        _ ≤ C * (P * r ^ (M - (N + 1))) :=
            mul_le_mul_of_nonneg_left (rpow_mul_exp_le_geom hτ hM) hC0
        _ = C * P * r ^ (M - (N + 1)) := by ring
    exact add_le_add ((Finset.sum_le_sum hfirst).trans hgeo) hsecond
  -- the cut-off to infinity
  have hlim : Tendsto (fun M : ℕ => K / (1 - r) + C * P * r ^ (M - (N + 1))) atTop
      (𝓝 (K / (1 - r))) := by
    have h1 : Tendsto (fun M : ℕ => r ^ (M - (N + 1))) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp (tendsto_sub_atTop_nat (N + 1))
    simpa using (h1.const_mul (C * P)).const_add (K / (1 - r))
  rw [hT]
  refine ge_of_tendsto hlim (eventually_atTop.2 ⟨max (N + 1) (F.sup modeNat), fun M hM =>
    hmain M (le_of_max_le_left hM) fun k hk =>
      (Finset.le_sup (f := modeNat) hk).trans (le_of_max_le_right hM)⟩)

end Tail

/-- **Certified upper bound of `S(ω, δ)`.** For `(γ, τ)`-Diophantine `ω`, `δ > 0`, a cut-off `N`
with `2τ < 2πδ(N + 1)`, lower bounds `0 < L_k ≤ |k·ω|` on `0 < |k|₁ ≤ N` and upper bounds
`E_m ≥ e^{-2πδm}` for `1 ≤ m ≤ N`: `S(ω, δ) ≤ ∑_{0<|k|₁≤N} L_k⁻² E_{|k|₁} + T_N`. -/
theorem smallDivisorSum_le_box_add_tail {ω : Fin n → ℝ} {γ τ δ : ℝ} (hω : IsDiophantine γ τ ω)
    (hγ : 0 < γ) (hτ : 0 ≤ τ) (hδ : 0 < δ) {N : ℕ} (hN : 2 * τ < 2 * Real.pi * δ * (N + 1))
    (L : (Fin n → ℤ) → ℝ)
    (hL : ∀ k ∈ modeBox n N, 0 < L k ∧ L k ≤ |Diophantine.frequencyDot ω k|)
    (E : ℕ → ℝ) (hE : ∀ m : ℕ, 1 ≤ m → m ≤ N → Real.exp (-(2 * Real.pi * δ) * m) ≤ E m) :
    smallDivisorSum ω δ ≤
      ∑ k ∈ modeBox n N, (L k ^ 2)⁻¹ * E (modeNat k) + sdTail γ τ δ N := by
  classical
  have hsum := summable_smallDivisorTerm hω.condition hγ hτ hδ
  refine hsum.tsum_le_of_sum_le fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun k => modeNat k ≤ N)]
  refine add_le_add ?_ (sum_smallDivisorTerm_tail_le hω.condition hγ hτ hδ hN _ fun k hk => by
    have := (Finset.mem_filter.mp hk).2
    omega)
  -- the box part: drop `k = 0`, enlarge to the box, bound term by term
  have hne : ∑ k ∈ u.filter (fun k => modeNat k ≤ N), smallDivisorTerm ω δ k =
      ∑ k ∈ (u.filter (fun k => modeNat k ≤ N)).filter (fun k : Fin n → ℤ => k ≠ 0),
        smallDivisorTerm ω δ k := by
    refine (Finset.sum_filter_of_ne (p := fun k : Fin n → ℤ => k ≠ 0) ?_).symm
    intro k _ hk h
    exact hk (by simp [smallDivisorTerm, h])
  rw [hne]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_)
    fun k _ _ => smallDivisorTerm_nonneg ω δ k).trans (Finset.sum_le_sum fun k hk => ?_)
  · simp only [Finset.mem_filter] at hk
    exact mem_modeBox.mpr ⟨hk.2, hk.1.2⟩
  · obtain ⟨hk0, hkN⟩ := mem_modeBox.mp hk
    obtain ⟨hL0, hLk⟩ := hL k hk
    rw [smallDivisorTerm_of_ne hk0, modeSize_eq_modeNat]
    have hsq : L k ^ 2 ≤ (Diophantine.frequencyDot ω k) ^ 2 := by
      rw [← sq_abs (Diophantine.frequencyDot ω k)]
      exact pow_le_pow_left₀ hL0.le hLk 2
    refine mul_le_mul (inv_anti₀ (by positivity) hsq) (hE _ (modeNat_pos hk0) hkN)
      (Real.exp_pos _).le (by positivity)

/-- A checker-friendly bound of the tail: `T_N ≤ C b (N+1)^{2τ} E' (1 + c)/c` for every
`E' ≥ e^{-b(N+1)}`, with `b = 2πδ`, `c = b - 2τ/(N+1) > 0` and `C = 2(1 + 2^τ)γ⁻²` (from
`1 - e^{-b} ≤ b` and `1 - e^{-c} ≥ c/(1 + c)`). -/
theorem sdTail_le {γ τ δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    (hN : 2 * τ < 2 * Real.pi * δ * (N + 1)) {E' : ℝ}
    (hE' : Real.exp (-(2 * Real.pi * δ) * (N + 1)) ≤ E') :
    sdTail γ τ δ N ≤
      2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ * (2 * Real.pi * δ) * ((N + 1 : ℝ) ^ (2 * τ) * E') *
        ((1 + (2 * Real.pi * δ - 2 * τ / (N + 1))) / (2 * Real.pi * δ - 2 * τ / (N + 1))) := by
  set b : ℝ := 2 * Real.pi * δ with hb
  have hb0 : 0 < b := by positivity
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  set c : ℝ := b - 2 * τ / (N + 1) with hc
  have hc0 : 0 < c := by
    rw [hc, sub_pos, div_lt_iff₀ hN1]
    linarith
  set C : ℝ := 2 * (1 + 2 ^ τ) * (γ ^ 2)⁻¹ with hC
  have hC0 : 0 ≤ C := by positivity
  have hE0 : 0 ≤ E' := (Real.exp_pos _).le.trans hE'
  have h1 : 1 - Real.exp (-b) ≤ b := by linarith [Real.add_one_le_exp (-b)]
  have he1 : 0 ≤ 1 - Real.exp (-b) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have h2 : (N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1)) ≤ (N + 1 : ℝ) ^ (2 * τ) * E' :=
    mul_le_mul_of_nonneg_left hE' (Real.rpow_nonneg hN1.le _)
  have h3 : c / (1 + c) ≤ 1 - Real.exp (-c) := by
    have hexp : Real.exp (-c) * (1 + c) ≤ 1 := by
      have := Real.add_one_le_exp c
      have hpos := Real.exp_pos (-c)
      calc Real.exp (-c) * (1 + c) ≤ Real.exp (-c) * Real.exp c :=
            mul_le_mul_of_nonneg_left (by linarith) hpos.le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hden : 0 < c / (1 + c) := div_pos hc0 (by linarith)
  have hnum : 0 ≤ C * (1 - Real.exp (-b)) * ((N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1))) := by
    positivity
  calc sdTail γ τ δ N
      = C * (1 - Real.exp (-b)) * ((N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1))) /
          (1 - Real.exp (-c)) := by
        rw [sdTail, hC, hc, hb]
    _ ≤ C * (1 - Real.exp (-b)) * ((N + 1 : ℝ) ^ (2 * τ) * Real.exp (-b * (N + 1))) /
          (c / (1 + c)) := div_le_div_of_nonneg_left hnum hden h3
    _ ≤ C * b * ((N + 1 : ℝ) ^ (2 * τ) * E') / (c / (1 + c)) := by
        refine div_le_div_of_nonneg_right ?_ hden.le
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) h2 (by positivity)
          (mul_nonneg hC0 hb0.le)
    _ = C * b * ((N + 1 : ℝ) ^ (2 * τ) * E') * ((1 + c) / c) := by
        field_simp

end KAM

end
