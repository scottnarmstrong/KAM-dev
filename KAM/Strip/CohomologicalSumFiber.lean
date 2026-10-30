/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Strip.CohomologicalSumCert
public import KAM.Diophantine.FrequencyDependence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A fibered certified bound for the small-divisor series

For a frequency of the form `ω = (ω', 1)` (a clock or extended-phase-space frequency, after
scaling), `k·ω = k'·ω' + k_n` and `|k|₁ = |k'|₁ + |k_n|`, so the series `S(ω, δ)` fibers over
`k' ∈ ℤ^{n-1}` (`KAM.smallDivisorSum_snoc_le_fiber`):
`S(ω, δ) ≤ π²/3 + ∑_{0<|k'|₁≤N} (E_{|k'|₁+|p_{k'}|} L_{k'}⁻² + E_{|k'|₁} C₀) + T_N`.

* The fiber `k' = 0` contributes at most `∑_{j≠0} j⁻² = π²/3` (`KAM.sum_inv_sq_int_le`).
* In a fiber `k' ≠ 0`, with `x = k'·ω'` and an integer `p` with `|x + p| ≤ 1/2` (the data `p_{k'}`,
  the nearest integer to `-x`), the term `j = p` keeps its weight `e^{-2πδ(|k'|₁+|p|)}` and is
  bounded by the datum `0 < L_{k'} ≤ |x + p|`; the other terms lose `e^{-2πδ|j|} ≤ 1` and sum to at
  most `C₀ = 4 + π²/3` (`KAM.fiberConst`, `KAM.sum_fiber_le`: `|x + j| ≥ |j - p|` on one side and
  `≥ |j - p| - 1/2` on the other, with `ζ(2) = π²/6`).
* The fibers `|k'|₁ > N` consist of modes with `|k|₁ > N`: the tail `T_N = KAM.sdTail γ τ δ N` of
  `KAM.smallDivisorSum_le_box_add_tail` (separation/shell argument) applies.

The data form a box of `#{0<|k'|₁≤N}` entries in `ℤ^{n-1}` instead of `ℤ^n`. The weights are
supplied as `E j ≥ e^{-2πδj}`. `KAM.fiber_dist_ge` records the Diophantine lower bound
`|k'·ω' + p| ≥ γ ((3/2 + ‖ω'‖) |k'|₁)^{-τ}` for every integer `p` with `|k'·ω' + p| ≤ 1/2`.
-/

public noncomputable section

namespace KAM

/-! ### Inverse squares over the integers -/

/-- `∑_{i∈T} i⁻² ≤ π²/6` for a finite set of integers `i ≥ 1`. -/
theorem sum_inv_sq_pos_le (T : Finset ℤ) (hT : ∀ i ∈ T, 1 ≤ i) :
    ∑ i ∈ T, ((i : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
  have hcast : ∀ i ∈ T, ((i.toNat : ℕ) : ℝ) = (i : ℝ) := fun i hi => by
    have h := Int.toNat_of_nonneg (by linarith [hT i hi] : (0 : ℤ) ≤ i)
    exact_mod_cast h
  have hinj : Set.InjOn Int.toNat (T : Set ℤ) := fun i hi j hj h => by
    have h1 := Int.toNat_of_nonneg (by linarith [hT i hi] : (0 : ℤ) ≤ i)
    have h2 := Int.toNat_of_nonneg (by linarith [hT j hj] : (0 : ℤ) ≤ j)
    rw [← h1, ← h2, h]
  calc ∑ i ∈ T, ((i : ℝ) ^ 2)⁻¹ = ∑ i ∈ T, (((i.toNat : ℕ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_congr rfl fun i hi => by rw [hcast i hi]
    _ = ∑ n ∈ T.image Int.toNat, (((n : ℕ) : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) hinj).symm
    _ ≤ Real.pi ^ 2 / 6 := by
        refine (le_of_eq (Finset.sum_congr rfl fun n _ => (one_div _).symm)).trans ?_
        exact sum_le_hasSum _ (fun n _ => by positivity) hasSum_zeta_two

/-- `∑_{j∈J} j⁻² ≤ π²/3` for every finite set of integers (the term `j = 0` is `0⁻¹ = 0`). -/
theorem sum_inv_sq_int_le (J : Finset ℤ) : ∑ j ∈ J, ((j : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 3 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not J (fun j => 0 ≤ j)]
  have h1 : ∑ j ∈ J.filter (fun j => 0 ≤ j), ((j : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun j => j = 0)]
    have h0 : ∑ j ∈ (J.filter (fun j => 0 ≤ j)).filter (fun j => j = 0), ((j : ℝ) ^ 2)⁻¹ = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [(Finset.mem_filter.mp hj).2]
    rw [h0, zero_add]
    exact sum_inv_sq_pos_le _ fun j hj => by
      simp only [Finset.mem_filter] at hj
      omega
  have h2 : ∑ j ∈ J.filter (fun j => ¬ 0 ≤ j), ((j : ℝ) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    have hinj : Set.InjOn (fun j : ℤ => -j) (J.filter (fun j => ¬ 0 ≤ j) : Set ℤ) :=
      fun i _ j _ h => neg_inj.mp h
    calc ∑ j ∈ J.filter (fun j => ¬ 0 ≤ j), ((j : ℝ) ^ 2)⁻¹
        = ∑ j ∈ J.filter (fun j => ¬ 0 ≤ j), ((((-j : ℤ)) : ℝ) ^ 2)⁻¹ :=
          Finset.sum_congr rfl fun j _ => by push_cast; ring
      _ = ∑ i ∈ (J.filter (fun j => ¬ 0 ≤ j)).image (fun j : ℤ => -j), ((i : ℝ) ^ 2)⁻¹ :=
          (Finset.sum_image (f := fun i : ℤ => ((i : ℝ) ^ 2)⁻¹) hinj).symm
      _ ≤ Real.pi ^ 2 / 6 := sum_inv_sq_pos_le _ fun i hi => by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          simp only [Finset.mem_filter] at hj
          omega
  linarith

/-- The constant `C₀ = 4 + π²/3` of a fiber. -/
@[expose] def fiberConst : ℝ := 4 + Real.pi ^ 2 / 3

theorem fiberConst_nonneg : 0 ≤ fiberConst := by unfold fiberConst; positivity

/-- For `0 ≤ y ≤ 1/2` and a finite set `I` of nonzero integers: `∑_{i∈I} (y + i)⁻² ≤ 4 + π²/3`. -/
theorem sum_inv_sq_shift_le_of_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (I : Finset ℤ)
    (hI : ∀ i ∈ I, i ≠ 0) : ∑ i ∈ I, ((y + i) ^ 2)⁻¹ ≤ fiberConst := by
  classical
  -- `i ≥ 1`: `y + i ≥ i`
  have hpos : ∑ i ∈ I.filter (fun i => 1 ≤ i), ((y + i) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    refine le_trans (Finset.sum_le_sum fun i hi => ?_)
      (sum_inv_sq_pos_le _ fun i hi => (Finset.mem_filter.mp hi).2)
    have h1 : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_filter.mp hi).2
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  -- `i = -1`: `|y - 1| ≥ 1/2`
  have hm1 : ∑ i ∈ I.filter (fun i => i = -1), ((y + i) ^ 2)⁻¹ ≤ 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {-1}) (fun i hi => ?_)
      fun i _ _ => by positivity) ?_
    · rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hi).2
    · rw [Finset.sum_singleton]
      have h : (1 / 2 : ℝ) ^ 2 ≤ (y + ((-1 : ℤ) : ℝ)) ^ 2 := by
        push_cast
        nlinarith
      calc ((y + ((-1 : ℤ) : ℝ)) ^ 2)⁻¹ ≤ ((1 / 2 : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) h
        _ = 4 := by norm_num
  -- `i ≤ -2`: `|y + i| ≥ |i + 1|`
  have hneg : ∑ i ∈ I.filter (fun i => i ≤ -2), ((y + i) ^ 2)⁻¹ ≤ Real.pi ^ 2 / 6 := by
    have hinj : Set.InjOn (fun i : ℤ => -(i + 1)) (I.filter (fun i => i ≤ -2) : Set ℤ) :=
      fun i _ j _ h => by simpa using h
    calc ∑ i ∈ I.filter (fun i => i ≤ -2), ((y + i) ^ 2)⁻¹
        ≤ ∑ i ∈ I.filter (fun i => i ≤ -2), ((((-(i + 1) : ℤ)) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have h2 : (i : ℝ) ≤ -2 := by exact_mod_cast (Finset.mem_filter.mp hi).2
          refine inv_anti₀ (by push_cast; nlinarith) ?_
          push_cast
          nlinarith
      _ = ∑ j ∈ (I.filter (fun i => i ≤ -2)).image (fun i : ℤ => -(i + 1)), ((j : ℝ) ^ 2)⁻¹ :=
          (Finset.sum_image (f := fun j : ℤ => ((j : ℝ) ^ 2)⁻¹) hinj).symm
      _ ≤ Real.pi ^ 2 / 6 := sum_inv_sq_pos_le _ fun j hj => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
          simp only [Finset.mem_filter] at hi
          omega
  -- the three parts cover `I`
  have hsplit : ∑ i ∈ I, ((y + i) ^ 2)⁻¹ =
      ∑ i ∈ I.filter (fun i => 1 ≤ i), ((y + i) ^ 2)⁻¹ +
        (∑ i ∈ I.filter (fun i => i = -1), ((y + i) ^ 2)⁻¹ +
          ∑ i ∈ I.filter (fun i => i ≤ -2), ((y + i) ^ 2)⁻¹) := by
    have hA : (I.filter (fun i => ¬ 1 ≤ i)).filter (fun i => i = -1) =
        I.filter (fun i => i = -1) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by omega⟩, h2⟩
    have hB : (I.filter (fun i => ¬ 1 ≤ i)).filter (fun i => ¬ i = -1) =
        I.filter (fun i => i ≤ -2) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, by have := hI i h1; omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, by omega⟩, by omega⟩
    rw [← Finset.sum_filter_add_sum_filter_not I (fun i => 1 ≤ i),
      ← Finset.sum_filter_add_sum_filter_not (I.filter (fun i => ¬ 1 ≤ i)) (fun i => i = -1),
      hA, hB]
  rw [hsplit, fiberConst]
  linarith

/-- For `|y| ≤ 1/2` and a finite set `I` of nonzero integers: `∑_{i∈I} (y + i)⁻² ≤ 4 + π²/3`. -/
theorem sum_inv_sq_shift_le {y : ℝ} (hy : |y| ≤ 1 / 2) (I : Finset ℤ) (hI : ∀ i ∈ I, i ≠ 0) :
    ∑ i ∈ I, ((y + i) ^ 2)⁻¹ ≤ fiberConst := by
  classical
  rcases le_total 0 y with h0 | h0
  · exact sum_inv_sq_shift_le_of_nonneg h0 (le_of_abs_le hy) I hI
  · have hinj : Set.InjOn (fun i : ℤ => -i) (I : Set ℤ) := fun i _ j _ h => neg_inj.mp h
    calc ∑ i ∈ I, ((y + i) ^ 2)⁻¹ = ∑ i ∈ I, ((-y + ((-i : ℤ) : ℝ)) ^ 2)⁻¹ :=
          Finset.sum_congr rfl fun i _ => by push_cast; ring
      _ = ∑ i ∈ I.image (fun i : ℤ => -i), ((-y + i) ^ 2)⁻¹ :=
          (Finset.sum_image (f := fun i : ℤ => ((-y + (i : ℝ)) ^ 2)⁻¹) hinj).symm
      _ ≤ fiberConst := sum_inv_sq_shift_le_of_nonneg (by linarith)
          (by linarith [neg_abs_le y]) _ fun i hi => by
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
            exact neg_ne_zero.mpr (hI j hj)

/-- **One fiber.** For `x ∈ ℝ`, an integer `p` with `|x + p| ≤ 1/2`, `0 < L ≤ |x + p|`, `b ≥ 0` and
a finite set `J` of integers: `∑_{j∈J} (x + j)⁻² e^{-b|j|} ≤ e^{-b|p|} L⁻² + C₀`. -/
theorem sum_fiber_le {x L b : ℝ} {p : ℤ} (hb : 0 ≤ b) (hp : |x + p| ≤ 1 / 2) (hL0 : 0 < L)
    (hL : L ≤ |x + p|) (J : Finset ℤ) :
    ∑ j ∈ J, ((x + j) ^ 2)⁻¹ * Real.exp (-b * (j.natAbs : ℝ)) ≤
      Real.exp (-b * (p.natAbs : ℝ)) * (L ^ 2)⁻¹ + fiberConst := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not J (fun j => j = p)]
  refine add_le_add ?_ ?_
  · refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := {p}) (fun j hj => ?_)
      fun j _ _ => by positivity) ?_
    · rw [Finset.mem_singleton]
      exact (Finset.mem_filter.mp hj).2
    · rw [Finset.sum_singleton, mul_comm]
      have hsq : L ^ 2 ≤ (x + p) ^ 2 := by
        rw [← sq_abs (x + p)]
        exact pow_le_pow_left₀ hL0.le hL 2
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (Real.exp_pos _).le
  · have hinj : Set.InjOn (fun j : ℤ => j - p) (J.filter (fun j => ¬ j = p) : Set ℤ) :=
      fun i _ j _ h => by simpa using h
    calc ∑ j ∈ J.filter (fun j => ¬ j = p), ((x + j) ^ 2)⁻¹ * Real.exp (-b * (j.natAbs : ℝ))
        ≤ ∑ j ∈ J.filter (fun j => ¬ j = p), (((x + p) + ((j - p : ℤ) : ℝ)) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have he : Real.exp (-b * (j.natAbs : ℝ)) ≤ 1 :=
            Real.exp_le_one_iff.mpr (by have : (0 : ℝ) ≤ j.natAbs := Nat.cast_nonneg _; nlinarith)
          have hx : x + (p : ℝ) + ((j - p : ℤ) : ℝ) = x + j := by push_cast; ring
          rw [hx]
          exact mul_le_of_le_one_right (by positivity) he
      _ = ∑ i ∈ (J.filter (fun j => ¬ j = p)).image (fun j : ℤ => j - p),
            (((x + p) + (i : ℝ)) ^ 2)⁻¹ :=
          (Finset.sum_image (f := fun i : ℤ => (((x + p) + (i : ℝ)) ^ 2)⁻¹) hinj).symm
      _ ≤ fiberConst := sum_inv_sq_shift_le hp _ fun i hi => by
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          exact sub_ne_zero.mpr (Finset.mem_filter.mp hj).2

/-! ### The fibered bound -/

section Snoc

variable {m : ℕ}

theorem frequencyDot_snoc (ω' : Fin m → ℝ) (k : Fin (m + 1) → ℤ) :
    Diophantine.frequencyDot (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) k =
      Diophantine.frequencyDot ω' (Fin.init k) + k (Fin.last m) := by
  simp [Diophantine.frequencyDot, Fin.sum_univ_castSucc, Fin.init]

theorem modeNat_eq_init_add (k : Fin (m + 1) → ℤ) :
    modeNat k = modeNat (Fin.init k) + (k (Fin.last m)).natAbs := by
  simp [modeNat, Fin.sum_univ_castSucc, Fin.init]

theorem eq_of_init_eq_of_last_eq {k l : Fin (m + 1) → ℤ} (h1 : Fin.init k = Fin.init l)
    (h2 : k (Fin.last m) = l (Fin.last m)) : k = l := by
  rw [← Fin.snoc_init_self k, ← Fin.snoc_init_self l, h1, h2]

/-- The Diophantine lower bound in a fiber: for `(γ, τ)`-Diophantine `ω = (ω', 1)`, `k' ≠ 0` and
an integer `p` with `|k'·ω' + p| ≤ 1/2`: `|k'·ω' + p| ≥ γ ((3/2 + ‖ω'‖) |k'|₁)^{-τ}` (take
`k = (k', p)` and `|p| ≤ |k'·ω'| + 1/2`). -/
theorem fiber_dist_ge {ω' : Fin m → ℝ} {γ τ : ℝ}
    (hω : IsDiophantine γ τ (Fin.snoc ω' 1 : Fin (m + 1) → ℝ)) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    {k : Fin m → ℤ} (hk : k ≠ 0) (p : ℤ) (hp : |Diophantine.frequencyDot ω' k + p| ≤ 1 / 2) :
    γ / ((3 / 2 + ‖ω'‖) * modeNat k) ^ τ ≤ |Diophantine.frequencyDot ω' k + p| := by
  set K : Fin (m + 1) → ℤ := Fin.snoc k p with hK
  have hKinit : Fin.init K = k := Fin.init_snoc _ _
  have hKlast : K (Fin.last m) = p := Fin.snoc_last _ _
  have hK0 : K ≠ 0 := fun h => hk (by rw [← hKinit, h]; rfl)
  have hc : Diophantine.Condition (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) γ τ := hω.condition
  have hd := hc K hK0
  rw [frequencyDot_snoc, hKinit, hKlast] at hd
  have hm1 : (1 : ℝ) ≤ modeNat k := by exact_mod_cast modeNat_pos hk
  have hsize : Fourier.modeSize K = (modeNat k : ℝ) + (p.natAbs : ℝ) := by
    rw [modeSize_eq_modeNat, modeNat_eq_init_add, hKinit, hKlast]
    push_cast
    ring
  have hpabs : (p.natAbs : ℝ) ≤ ‖ω'‖ * modeNat k + 1 / 2 := by
    have h1 : (p.natAbs : ℝ) = |(p : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h2 := Diophantine.abs_frequencyDot_le ω' k
    rw [modeSize_eq_modeNat] at h2
    set d := Diophantine.frequencyDot ω' k with hd_def
    have h3 : |(p : ℝ)| ≤ |d + p| + |d| :=
      calc |(p : ℝ)| = |(d + p) - d| := by ring_nf
        _ ≤ |d + p| + |d| := abs_sub _ _
    rw [h1]
    linarith
  have hle : Fourier.modeSize K ≤ (3 / 2 + ‖ω'‖) * modeNat k := by
    rw [hsize]
    nlinarith
  have hpos : 0 < Fourier.modeSize K := by rw [hsize]; positivity
  exact le_trans (div_le_div_of_nonneg_left hγ.le (Real.rpow_pos_of_pos hpos τ)
    (Real.rpow_le_rpow hpos.le hle hτ)) hd

/-- **The fibered certified bound.** For `(γ, τ)`-Diophantine `ω = (ω', 1)`, `δ > 0`, a cut-off
`N` with `2τ < 2πδ(N + 1)`, and data on the box `0 < |k'|₁ ≤ N` of `ℤ^{n-1}`: integers `p_{k'}` with
`|k'·ω' + p_{k'}| ≤ 1/2`, lower bounds `0 < L_{k'} ≤ |k'·ω' + p_{k'}|`, and upper bounds
`E_j ≥ e^{-2πδj}`:
`S(ω, δ) ≤ π²/3 + ∑_{0<|k'|₁≤N} (E_{|k'|₁+|p_{k'}|} L_{k'}⁻² + E_{|k'|₁} C₀) + T_N`. -/
theorem smallDivisorSum_snoc_le_fiber {ω' : Fin m → ℝ} {γ τ δ : ℝ}
    (hω : IsDiophantine γ τ (Fin.snoc ω' 1 : Fin (m + 1) → ℝ)) (hγ : 0 < γ) (hτ : 0 ≤ τ)
    (hδ : 0 < δ) {N : ℕ} (hN : 2 * τ < 2 * Real.pi * δ * (N + 1))
    (p : (Fin m → ℤ) → ℤ) (L : (Fin m → ℤ) → ℝ)
    (hp : ∀ k ∈ modeBox m N, |Diophantine.frequencyDot ω' k + p k| ≤ 1 / 2)
    (hL : ∀ k ∈ modeBox m N, 0 < L k ∧ L k ≤ |Diophantine.frequencyDot ω' k + p k|)
    (E : ℕ → ℝ) (hE : ∀ j : ℕ, Real.exp (-(2 * Real.pi * δ) * j) ≤ E j) :
    smallDivisorSum (Fin.snoc ω' 1 : Fin (m + 1) → ℝ) δ ≤
      Real.pi ^ 2 / 3 +
        ∑ k ∈ modeBox m N, (E (modeNat k + (p k).natAbs) * (L k ^ 2)⁻¹ +
          E (modeNat k) * fiberConst) +
        sdTail γ τ δ N := by
  classical
  set ω : Fin (m + 1) → ℝ := Fin.snoc ω' 1 with hωdef
  set b : ℝ := 2 * Real.pi * δ with hb
  have hb0 : 0 ≤ b := by positivity
  have hsum := summable_smallDivisorTerm hω.condition hγ hτ hδ
  refine hsum.tsum_le_of_sum_le fun u => ?_
  rw [← Finset.sum_filter_add_sum_filter_not u (fun k => modeNat (Fin.init k) ≤ N)]
  refine add_le_add ?_ (sum_smallDivisorTerm_tail_le hω.condition hγ hτ hδ hN _ fun k hk => by
    have h := (Finset.mem_filter.mp hk).2
    rw [modeNat_eq_init_add]
    omega)
  set u₁ := u.filter (fun k => modeNat (Fin.init k) ≤ N) with hu₁
  have hmaps : ∀ k ∈ u₁, Fin.init k ∈ insert 0 (modeBox m N) := fun k hk => by
    by_cases h0 : Fin.init k = 0
    · rw [h0]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (mem_modeBox.mpr ⟨h0, (Finset.mem_filter.mp hk).2⟩)
  have h0box : (0 : Fin m → ℤ) ∉ modeBox m N := fun h => (mem_modeBox.mp h).1 rfl
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_insert h0box]
  -- the term of a mode through its fiber coordinates
  have hterm : ∀ k : Fin (m + 1) → ℤ, k ≠ 0 → smallDivisorTerm ω δ k =
      Real.exp (-b * modeNat (Fin.init k)) *
        (((Diophantine.frequencyDot ω' (Fin.init k) + k (Fin.last m)) ^ 2)⁻¹ *
          Real.exp (-b * ((k (Fin.last m)).natAbs : ℝ))) := fun k hk => by
    rw [smallDivisorTerm_of_ne hk, hωdef, frequencyDot_snoc, modeSize_eq_modeNat,
      modeNat_eq_init_add]
    push_cast
    rw [show -b * ((modeNat (Fin.init k) : ℝ) + ((k (Fin.last m)).natAbs : ℝ)) =
      -b * modeNat (Fin.init k) + -b * ((k (Fin.last m)).natAbs : ℝ) by ring, Real.exp_add]
    ring
  have hlast_inj : ∀ k' : Fin m → ℤ, Set.InjOn (fun k : Fin (m + 1) → ℤ => k (Fin.last m))
      (u₁.filter (fun k => Fin.init k = k') : Set (Fin (m + 1) → ℤ)) := fun k' k hk l hl h => by
    have h1 := (Finset.mem_filter.mp hk).2
    have h2 := (Finset.mem_filter.mp hl).2
    exact eq_of_init_eq_of_last_eq (h1.trans h2.symm) h
  refine add_le_add ?_ (Finset.sum_le_sum fun k' hk' => ?_)
  · -- the fiber `k' = 0`
    calc ∑ k ∈ u₁.filter (fun k => Fin.init k = 0), smallDivisorTerm ω δ k
        ≤ ∑ k ∈ u₁.filter (fun k => Fin.init k = 0), (((k (Fin.last m) : ℤ) : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hinit := (Finset.mem_filter.mp hk).2
          by_cases hk0 : k = 0
          · rw [hk0]
            simp [smallDivisorTerm]
          · rw [hterm k hk0, hinit, Diophantine.frequencyDot_zero, zero_add]
            have : (modeNat (0 : Fin m → ℤ) : ℝ) = 0 := by simp [modeNat]
            rw [this, mul_zero, Real.exp_zero, one_mul]
            exact mul_le_of_le_one_right (by positivity)
              (Real.exp_le_one_iff.mpr (by
                have : (0 : ℝ) ≤ (k (Fin.last m)).natAbs := Nat.cast_nonneg _
                nlinarith))
      _ = ∑ j ∈ (u₁.filter (fun k => Fin.init k = 0)).image
            (fun k : Fin (m + 1) → ℤ => k (Fin.last m)), (((j : ℤ) : ℝ) ^ 2)⁻¹ :=
          (Finset.sum_image (f := fun j : ℤ => ((j : ℝ) ^ 2)⁻¹) (hlast_inj 0)).symm
      _ ≤ Real.pi ^ 2 / 3 := sum_inv_sq_int_le _
  · -- a fiber `0 < |k'|₁ ≤ N`
    obtain ⟨hk'0, -⟩ := mem_modeBox.mp hk'
    obtain ⟨hL0, hLk⟩ := hL k' hk'
    set x := Diophantine.frequencyDot ω' k' with hx
    have hne : ∀ k ∈ u₁.filter (fun k => Fin.init k = k'), k ≠ 0 := fun k hk h => by
      have := (Finset.mem_filter.mp hk).2
      rw [h] at this
      exact hk'0 this.symm
    calc ∑ k ∈ u₁.filter (fun k => Fin.init k = k'), smallDivisorTerm ω δ k
        = Real.exp (-b * modeNat k') * ∑ k ∈ u₁.filter (fun k => Fin.init k = k'),
            ((x + k (Fin.last m)) ^ 2)⁻¹ * Real.exp (-b * ((k (Fin.last m)).natAbs : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hterm k (hne k hk), (Finset.mem_filter.mp hk).2]
      _ = Real.exp (-b * modeNat k') *
            ∑ j ∈ (u₁.filter (fun k => Fin.init k = k')).image
              (fun k : Fin (m + 1) → ℤ => k (Fin.last m)),
              ((x + ((j : ℤ) : ℝ)) ^ 2)⁻¹ * Real.exp (-b * (j.natAbs : ℝ)) := by
          rw [Finset.sum_image (f := fun j : ℤ => ((x + j) ^ 2)⁻¹ * Real.exp (-b * (j.natAbs : ℝ)))
            (hlast_inj k')]
      _ ≤ Real.exp (-b * modeNat k') *
            (Real.exp (-b * ((p k').natAbs : ℝ)) * (L k' ^ 2)⁻¹ + fiberConst) :=
          mul_le_mul_of_nonneg_left (sum_fiber_le hb0 (hp k' hk') hL0 hLk _) (Real.exp_pos _).le
      _ = Real.exp (-b * ((modeNat k' + (p k').natAbs : ℕ) : ℝ)) * (L k' ^ 2)⁻¹ +
            Real.exp (-b * modeNat k') * fiberConst := by
          push_cast
          rw [show -b * ((modeNat k' : ℝ) + ((p k').natAbs : ℝ)) =
            -b * modeNat k' + -b * ((p k').natAbs : ℝ) by ring, Real.exp_add]
          ring
      _ ≤ E (modeNat k' + (p k').natAbs) * (L k' ^ 2)⁻¹ + E (modeNat k') * fiberConst :=
          add_le_add (mul_le_mul_of_nonneg_right (hE _) (by positivity))
            (mul_le_mul_of_nonneg_right (hE _) fiberConst_nonneg)

end Snoc

end KAM

end
