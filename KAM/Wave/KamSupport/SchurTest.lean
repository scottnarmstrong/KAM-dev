/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Multiplier
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Schur test on `ℓ²` (support for blueprint-W `bpW:w1:schur`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

A matrix `F : ℕ+ → ℕ+ → K` whose finite row sums and finite column sums of moduli are bounded by `Λ`
defines a bounded operator on `ℓ²` of norm at most `Λ`: `kamSchurCLM`. Its coordinates are the
absolutely convergent sums `(T v)_i = ∑_j F_{ij} v_j` (`kamSchurCLM_hasSum`).
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- Row and column bounds of the Schur test: all finite partial sums of moduli are at most `Λ`. -/
structure KamSchurBound (F : ℕ+ → ℕ+ → K) (Λ : ℝ) : Prop where
  row : ∀ (i : ℕ+) (J : Finset ℕ+), ∑ j ∈ J, ‖F i j‖ ≤ Λ
  col : ∀ (j : ℕ+) (I : Finset ℕ+), ∑ i ∈ I, ‖F i j‖ ≤ Λ

namespace KamSchurBound

variable {F : ℕ+ → ℕ+ → K} {Λ : ℝ}

theorem bound_nonneg (h : KamSchurBound F Λ) : 0 ≤ Λ := by simpa using h.row 1 ∅

theorem bound_mono {Λ' : ℝ} (h : KamSchurBound F Λ) (hΛ : Λ ≤ Λ') : KamSchurBound F Λ' :=
  ⟨fun i J => (h.row i J).trans hΛ, fun j I => (h.col j I).trans hΛ⟩

/-- Cauchy–Schwarz for one row: `(∑_J |F_ij| |v_j|)² ≤ Λ ∑_J |F_ij| |v_j|²`. -/
theorem sq_row_le (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+)
    (J : Finset ℕ+) :
    (∑ j ∈ J, ‖F i j‖ * ‖v j‖) ^ 2 ≤ Λ * ∑ j ∈ J, ‖F i j‖ * ‖v j‖ ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq J (fun j => Real.sqrt ‖F i j‖)
    (fun j => Real.sqrt ‖F i j‖ * ‖v j‖)
  have e1 : ∀ j, Real.sqrt ‖F i j‖ * (Real.sqrt ‖F i j‖ * ‖v j‖) = ‖F i j‖ * ‖v j‖ := fun j => by
    rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have e2 : ∀ j, Real.sqrt ‖F i j‖ ^ 2 = ‖F i j‖ := fun j => Real.sq_sqrt (norm_nonneg _)
  have e3 : ∀ j, (Real.sqrt ‖F i j‖ * ‖v j‖) ^ 2 = ‖F i j‖ * ‖v j‖ ^ 2 := fun j => by
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_right (h.row i J) ?_)
  exact Finset.sum_nonneg fun j _ => by positivity

theorem sum_sq_le (v : lp (fun _ : ℕ+ => K) 2) (J : Finset ℕ+) :
    ∑ j ∈ J, ‖v j‖ ^ 2 ≤ ‖v‖ ^ 2 :=
  sum_le_hasSum J (fun _ _ => by positivity) (lp_two_hasSum_sq v)

/-- Finite Schur bound: `∑_{i∈I} (∑_{j∈J} |F_ij||v_j|)² ≤ Λ² ‖v‖²`. -/
theorem sum_sq_partial_le (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2)
    (I J : Finset ℕ+) :
    ∑ i ∈ I, (∑ j ∈ J, ‖F i j‖ * ‖v j‖) ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2 := by
  have h0 := h.bound_nonneg
  calc ∑ i ∈ I, (∑ j ∈ J, ‖F i j‖ * ‖v j‖) ^ 2
      ≤ ∑ i ∈ I, Λ * ∑ j ∈ J, ‖F i j‖ * ‖v j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h.sq_row_le v i J
    _ = Λ * ∑ j ∈ J, ‖v j‖ ^ 2 * ∑ i ∈ I, ‖F i j‖ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ Λ * ∑ j ∈ J, ‖v j‖ ^ 2 * Λ := by
        gcongr with j _
        exact h.col j I
    _ = Λ ^ 2 * ∑ j ∈ J, ‖v j‖ ^ 2 := by rw [← Finset.sum_mul]; ring
    _ ≤ Λ ^ 2 * ‖v‖ ^ 2 := by gcongr; exact sum_sq_le v J

/-- Absolute convergence of each row. -/
theorem summable_row (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+) :
    Summable fun j => ‖F i j‖ * ‖v j‖ := by
  have h0 := h.bound_nonneg
  refine summable_of_sum_le (c := Λ * ‖v‖) (fun j => by positivity) fun J => ?_
  have h1 := h.sq_row_le v i J
  have h2 : ∑ j ∈ J, ‖F i j‖ * ‖v j‖ ^ 2 ≤ Λ * ‖v‖ ^ 2 := by
    calc ∑ j ∈ J, ‖F i j‖ * ‖v j‖ ^ 2 ≤ ∑ j ∈ J, ‖F i j‖ * ‖v‖ ^ 2 := by
          gcongr with j _
          exact lp.norm_apply_le_norm (by norm_num) v j
      _ = (∑ j ∈ J, ‖F i j‖) * ‖v‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ Λ * ‖v‖ ^ 2 := by gcongr; exact h.row i J
  have h3 : (∑ j ∈ J, ‖F i j‖ * ‖v j‖) ^ 2 ≤ (Λ * ‖v‖) ^ 2 := by
    calc _ ≤ Λ * ∑ j ∈ J, ‖F i j‖ * ‖v j‖ ^ 2 := h1
      _ ≤ Λ * (Λ * ‖v‖ ^ 2) := by gcongr
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun j _ => by positivity)
    (by positivity) two_ne_zero).1 h3

/-- The `ℓ²` bound for the row moduli `w_i = ∑_j |F_ij||v_j|` over a finite set of rows. -/
theorem sum_sq_tsum_le (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (I : Finset ℕ+) :
    ∑ i ∈ I, (∑' j, ‖F i j‖ * ‖v j‖) ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2 := by
  have hlim : Tendsto (fun J : Finset ℕ+ => ∑ i ∈ I, (∑ j ∈ J, ‖F i j‖ * ‖v j‖) ^ 2) atTop
      (𝓝 (∑ i ∈ I, (∑' j, ‖F i j‖ * ‖v j‖) ^ 2)) :=
    tendsto_finsetSum I fun i _ => ((h.summable_row v i).hasSum).pow 2
  exact le_of_tendsto' hlim fun J => h.sum_sq_partial_le v I J

end KamSchurBound

variable {F : ℕ+ → ℕ+ → K} {Λ : ℝ}

/-- The coordinates `(T v)_i = ∑_j F_ij v_j` of the Schur operator. -/
def kamSchurFun (F : ℕ+ → ℕ+ → K) (v : ℕ+ → K) (i : ℕ+) : K := ∑' j, F i j * v j

theorem kamSchurFun_hasSum (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+) :
    HasSum (fun j => F i j * v j) (kamSchurFun F v i) := by
  have : Summable fun j => F i j * v j :=
    Summable.of_norm (by simpa [norm_mul] using h.summable_row v i)
  exact this.hasSum

theorem norm_kamSchurFun_le (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+) :
    ‖kamSchurFun F v i‖ ≤ ∑' j, ‖F i j‖ * ‖v j‖ := by
  unfold kamSchurFun
  refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
  · simpa [norm_mul] using h.summable_row v i
  · simp [norm_mul]

theorem memℓp_kamSchurFun (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) :
    Memℓp (kamSchurFun F v) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine summable_of_sum_le (c := Λ ^ 2 * ‖v‖ ^ 2) (fun i => by positivity) fun I => ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (h.sum_sq_tsum_le v I)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_kamSchurFun_le h v i) 2

theorem norm_kamSchurFun_sq_le (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) :
    ‖(⟨kamSchurFun F v, memℓp_kamSchurFun h v⟩ : lp (fun _ : ℕ+ => K) 2)‖ ^ 2 ≤
      (Λ * ‖v‖) ^ 2 := by
  have hs := lp_two_hasSum_sq (⟨kamSchurFun F v, memℓp_kamSchurFun h v⟩ : lp (fun _ : ℕ+ => K) 2)
  rw [← hs.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun i => by positivity) fun I => ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) ((h.sum_sq_tsum_le v I).trans_eq (by ring))
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_kamSchurFun_le h v i) 2

/-- **Schur operator**: a matrix with row and column sums bounded by `Λ` defines a bounded operator
on `ℓ²` of norm at most `Λ`. -/
def kamSchurCLM (F : ℕ+ → ℕ+ → K) (h : KamSchurBound F Λ) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨kamSchurFun F v, memℓp_kamSchurFun h v⟩
      map_add' := fun v v' => by
        ext i
        have h1 := (kamSchurFun_hasSum h v i).add (kamSchurFun_hasSum h v' i)
        have h2 := kamSchurFun_hasSum h (v + v') i
        simp only [lp.coeFn_add, Pi.add_apply, mul_add] at h2
        exact h2.unique h1
      map_smul' := fun c v => by
        ext i
        have h1 := (kamSchurFun_hasSum h v i).const_smul c
        have h2 := kamSchurFun_hasSum h (c • v) i
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] at h2 h1 ⊢
        exact h2.unique h1 }
    Λ
    (fun v => by
      have h0 := h.bound_nonneg
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
        (norm_kamSchurFun_sq_le h v))

@[simp] theorem kamSchurCLM_apply (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+) :
    kamSchurCLM F h v i = kamSchurFun F v i := rfl

/-- **Schur test**: `(T v)_i = ∑_j F_ij v_j`, absolutely convergent. -/
theorem kamSchurCLM_hasSum (h : KamSchurBound F Λ) (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+) :
    HasSum (fun j => F i j * v j) (kamSchurCLM F h v i) :=
  kamSchurFun_hasSum h v i

/-- **Schur test**: `‖T‖ ≤ Λ`. -/
theorem norm_kamSchurCLM_le (h : KamSchurBound F Λ) : ‖kamSchurCLM F h‖ ≤ Λ :=
  LinearMap.mkContinuous_norm_le _ h.bound_nonneg _

end KAM.Wave
