/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.SchurTest
public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Hilbert-matrix bound (blueprint-W `bpW:w1:schur`)

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

For a bounded operator `A` on `ℓ²_K` with matrix `A_ij = (A e_j)_i` (`kamEntry`):

* the rows and columns of `A` are square summable with sum at most `‖A‖²`
  (`kamEntry_sum_sq_row_le`, `kamEntry_sum_sq_col_le`);
* the Hilbert kernel `1/|i-j|` (`kamHilbertKernel`, zero on the diagonal) is square summable with
  sum at most `π²/3` (`kamHilbertKernel_sum_sq_le`);
* (i) `kamHilbertCLM`, `norm_kamHilbertCLM_le`: the matrix `B_ij = |A_ij|/|i-j|` is a bounded
  operator of norm at most `(π/√3) ‖A‖`;
* (ii) `norm_kamEntry_diag_le`, `kamEntryDiagCLM`: the diagonal multiplier has norm at most `‖A‖`;
* (iii) `kamSchurBound_of_dominated`, `exists_clm_of_dominated`: entrywise dominated matrices;
* (iv) `kamSchur_weights_dominated`: the domination hypothesis is invariant under the weights.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

variable {K : Type*} [RCLike K]

/-- The basis vector `e_j` of `ℓ²`. -/
def kamBasis (K : Type*) [RCLike K] (j : ℕ+) : lp (fun _ : ℕ+ => K) 2 := lp.single 2 j (1 : K)

/-- The matrix entry `A_ij = (A e_j)_i`. -/
def kamEntry (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i j : ℕ+) : K :=
  A (kamBasis K j) i

theorem norm_kamBasis (j : ℕ+) : ‖kamBasis K j‖ = 1 := by
  unfold kamBasis
  rw [lp.norm_single (by norm_num)]
  simp

theorem norm_kamEntry_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i j : ℕ+) :
    ‖kamEntry A i j‖ ≤ ‖A‖ := by
  unfold kamEntry
  refine (lp.norm_apply_le_norm (by norm_num) _ i).trans ?_
  refine (A.le_opNorm _).trans ?_
  rw [norm_kamBasis, mul_one]

/-- (ii) The diagonal of `A` is bounded by `‖A‖`. -/
theorem norm_kamEntry_diag_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    (i : ℕ+) : ‖kamEntry A i i‖ ≤ ‖A‖ := norm_kamEntry_le A i i

/-- Columns: `∑_{i∈I} |A_ij|² ≤ ‖A‖²`. -/
theorem kamEntry_sum_sq_col_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    (j : ℕ+) (I : Finset ℕ+) : ∑ i ∈ I, ‖kamEntry A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  have h1 := KamSchurBound.sum_sq_le (A (kamBasis K j)) I
  refine h1.trans ?_
  have : ‖A (kamBasis K j)‖ ≤ ‖A‖ := by
    refine (A.le_opNorm _).trans ?_
    rw [norm_kamBasis, mul_one]
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

/-- The finitely supported test vector `x_J = ∑_{j∈J} conj(A_ij) e_j`. -/
def kamRowTest (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i : ℕ+)
    (J : Finset ℕ+) : lp (fun _ : ℕ+ => K) 2 :=
  ∑ j ∈ J, lp.single 2 j (starRingEnd K (kamEntry A i j))

theorem kamRowTest_apply (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i : ℕ+)
    (J : Finset ℕ+) (j : ℕ+) :
    kamRowTest A i J j = if j ∈ J then starRingEnd K (kamEntry A i j) else 0 := by
  classical
  unfold kamRowTest
  rw [lp.coeFn_sum, Finset.sum_apply]
  by_cases hj : j ∈ J
  · rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro b _ hb; simp [lp.single_apply, hb.symm]
    · intro h; exact absurd hj h
  · simp only [hj, ite_false]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : j ≠ b := fun h => hj (h ▸ hb)
    simp [lp.single_apply, this]

theorem norm_kamRowTest_sq (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i : ℕ+)
    (J : Finset ℕ+) : ‖kamRowTest A i J‖ ^ 2 = ∑ j ∈ J, ‖kamEntry A i j‖ ^ 2 := by
  classical
  have hs := lp_two_hasSum_sq (kamRowTest A i J)
  rw [← hs.tsum_eq]
  rw [tsum_eq_sum (s := J)]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [kamRowTest_apply]; simp only [hj, ite_true]; rw [RCLike.norm_conj]
  · intro j hj
    rw [kamRowTest_apply]; simp [hj]

/-- Rows: `∑_{j∈J} |A_ij|² ≤ ‖A‖²`. -/
theorem kamEntry_sum_sq_row_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    (i : ℕ+) (J : Finset ℕ+) : ∑ j ∈ J, ‖kamEntry A i j‖ ^ 2 ≤ ‖A‖ ^ 2 := by
  classical
  set S := ∑ j ∈ J, ‖kamEntry A i j‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hx := norm_kamRowTest_sq A i J
  have hAx : (A (kamRowTest A i J)) i = (S : K) := by
    have : A (kamRowTest A i J) = ∑ j ∈ J, starRingEnd K (kamEntry A i j) • A (kamBasis K j) := by
      unfold kamRowTest
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : lp.single 2 j (starRingEnd K (kamEntry A i j)) =
          starRingEnd K (kamEntry A i j) • kamBasis K j := by
        unfold kamBasis
        ext k
        by_cases hk : k = j
        · subst hk; simp [lp.single_apply]
        · simp [lp.single_apply, hk]
      rw [this, map_smul]
    rw [this, lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [hS]; push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    have := RCLike.conj_mul (kamEntry A i j)
    simpa [kamEntry] using this
  have h1 : S ≤ ‖A‖ * ‖kamRowTest A i J‖ := by
    have := lp.norm_apply_le_norm (p := 2) (by norm_num) (A (kamRowTest A i J)) i
    rw [hAx, RCLike.norm_ofReal, abs_of_nonneg hS0] at this
    exact this.trans (A.le_opNorm _)
  by_cases hz : S = 0
  · rw [hz]; positivity
  · have hpos : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hz)
    have h2 : S ^ 2 ≤ ‖A‖ ^ 2 * S := by
      calc S ^ 2 ≤ (‖A‖ * ‖kamRowTest A i J‖) ^ 2 := pow_le_pow_left₀ hS0 h1 2
        _ = ‖A‖ ^ 2 * ‖kamRowTest A i J‖ ^ 2 := by ring
        _ = ‖A‖ ^ 2 * S := by rw [hx]
    nlinarith

/-! ### The Hilbert kernel -/

/-- The Hilbert kernel `1/|i-j|`, zero on the diagonal. -/
def kamHilbertKernel (i j : ℕ+) : ℝ := if i = j then 0 else 1 / |(i : ℝ) - (j : ℝ)|

theorem kamHilbertKernel_nonneg (i j : ℕ+) : 0 ≤ kamHilbertKernel i j := by
  unfold kamHilbertKernel; split_ifs <;> positivity

theorem kamHilbertKernel_comm (i j : ℕ+) : kamHilbertKernel i j = kamHilbertKernel j i := by
  unfold kamHilbertKernel
  rw [abs_sub_comm]
  simp only [eq_comm (a := i)]

theorem kamHilbertKernel_of_ne {i j : ℕ+} (h : i ≠ j) :
    kamHilbertKernel i j = 1 / |(i : ℝ) - (j : ℝ)| := by
  unfold kamHilbertKernel; simp [h]

theorem kamHilbertKernel_self (i : ℕ+) : kamHilbertKernel i i = 0 := by
  unfold kamHilbertKernel; simp

private theorem kamInvSq_sum_image_le (S : Finset ℕ+) (φ : ℕ+ → ℕ) (hφ : Set.InjOn φ S) :
    ∑ j ∈ S, 1 / ((φ j : ℕ) : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  classical
  rw [← Finset.sum_image (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) hφ]
  exact sum_le_hasSum _ (fun _ _ => by positivity) hasSum_zeta_two

/-- The Hilbert kernel is square summable: `∑_j 1/|i-j|² ≤ π²/3`. -/
theorem kamHilbertKernel_sum_sq_le (i : ℕ+) (J : Finset ℕ+) :
    ∑ j ∈ J, kamHilbertKernel i j ^ 2 ≤ Real.pi ^ 2 / 3 := by
  classical
  set L := J.filter (fun j => j < i) with hL
  set U := J.filter (fun j => i < j) with hU
  have hsplit : ∑ j ∈ J, kamHilbertKernel i j ^ 2 ≤
      ∑ j ∈ L, kamHilbertKernel i j ^ 2 + ∑ j ∈ U, kamHilbertKernel i j ^ 2 := by
    have hsub : J.filter (fun j => j ≠ i) ⊆ L ∪ U := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_union, hL, hU, Finset.mem_filter, Finset.mem_filter]
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inl ⟨hj.1, h⟩
      · exact absurd h hj.2
      · exact Or.inr ⟨hj.1, h⟩
    have h1 : ∑ j ∈ J, kamHilbertKernel i j ^ 2 =
        ∑ j ∈ J.filter (fun j => j ≠ i), kamHilbertKernel i j ^ 2 := by
      rw [Finset.sum_filter_of_ne]
      intro j _ hne hji
      apply hne
      rw [hji, kamHilbertKernel_self]; ring
    rw [h1]
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
    rw [← Finset.sum_union_inter (s₁ := L) (s₂ := U)]
    have : ∑ j ∈ L ∩ U, kamHilbertKernel i j ^ 2 ≥ 0 := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hLb : ∑ j ∈ L, kamHilbertKernel i j ^ 2 ≤ Real.pi ^ 2 / 6 := by
    have := kamInvSq_sum_image_le L (fun j => (i : ℕ) - (j : ℕ)) (by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have : (a : ℕ) < i := ha'
      have : (b : ℕ) < i := hb'
      apply PNat.coe_injective
      simp only at hab
      omega)
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j < i := (Finset.mem_filter.mp hj).2
    have hji' : (j : ℕ) < i := hji
    rw [kamHilbertKernel_of_ne hji.ne', Nat.cast_sub hji'.le, div_pow, one_pow, sq_abs]
  have hUb : ∑ j ∈ U, kamHilbertKernel i j ^ 2 ≤ Real.pi ^ 2 / 6 := by
    have := kamInvSq_sum_image_le U (fun j => (j : ℕ) - (i : ℕ)) (by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have : (i : ℕ) < a := ha'
      have : (i : ℕ) < b := hb'
      apply PNat.coe_injective
      simp only at hab
      omega)
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.mp hj).2
    have hij' : (i : ℕ) < j := hij
    rw [kamHilbertKernel_of_ne hij.ne, Nat.cast_sub hij'.le, div_pow, one_pow, sq_abs]
    ring_nf
  linarith

/-! ### Row and column sums of the Hilbert matrix -/

/-- The Hilbert constant `π/√3`. -/
def kamHilbertConst : ℝ := Real.pi / Real.sqrt 3

theorem kamHilbertConst_nonneg : 0 ≤ kamHilbertConst := by
  unfold kamHilbertConst; positivity

theorem kamHilbertConst_sq : kamHilbertConst ^ 2 = Real.pi ^ 2 / 3 := by
  unfold kamHilbertConst
  rw [div_pow, Real.sq_sqrt (by norm_num)]

theorem kamHilbertConst_lt_two : kamHilbertConst < 2 := by
  have h3 : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  unfold kamHilbertConst
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [Real.pi_lt_d2]

/-- Cauchy–Schwarz against the Hilbert kernel: if `∑_J a_j² ≤ R²` then
`∑_J a_j k(i,j) ≤ (π/√3) R`. -/
theorem kamHilbert_cs (i : ℕ+) (J : Finset ℕ+) (a : ℕ+ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (ha : ∑ j ∈ J, a j ^ 2 ≤ R ^ 2) :
    ∑ j ∈ J, a j * kamHilbertKernel i j ≤ kamHilbertConst * R := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq J a (fun j => kamHilbertKernel i j)
  have hk := kamHilbertKernel_sum_sq_le i J
  have h2 : (∑ j ∈ J, a j * kamHilbertKernel i j) ^ 2 ≤ (kamHilbertConst * R) ^ 2 := by
    calc _ ≤ (∑ j ∈ J, a j ^ 2) * ∑ j ∈ J, kamHilbertKernel i j ^ 2 := hcs
      _ ≤ R ^ 2 * (Real.pi ^ 2 / 3) := by
        exact mul_le_mul ha hk (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
      _ = (kamHilbertConst * R) ^ 2 := by rw [mul_pow, kamHilbertConst_sq]; ring
  have h3 : 0 ≤ kamHilbertConst * R := mul_nonneg kamHilbertConst_nonneg hR
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt h3 two_ne_zero
  linarith

/-- The matrix `B_ij = |A_ij| / |i-j|` (zero on the diagonal), with values in `K`. -/
def kamHilbertB (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i j : ℕ+) : K :=
  ((‖kamEntry A i j‖ * kamHilbertKernel i j : ℝ) : K)

theorem norm_kamHilbertB (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i j : ℕ+) :
    ‖kamHilbertB A i j‖ = ‖kamEntry A i j‖ * kamHilbertKernel i j := by
  unfold kamHilbertB
  rw [RCLike.norm_ofReal, abs_of_nonneg (mul_nonneg (norm_nonneg _) (kamHilbertKernel_nonneg _ _))]

theorem kamHilbert_row_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (i : ℕ+)
    (J : Finset ℕ+) : ∑ j ∈ J, ‖kamEntry A i j‖ * kamHilbertKernel i j ≤ kamHilbertConst * ‖A‖ :=
  kamHilbert_cs i J _ (norm_nonneg _) (kamEntry_sum_sq_row_le A i J)

theorem kamHilbert_col_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) (j : ℕ+)
    (I : Finset ℕ+) : ∑ i ∈ I, ‖kamEntry A i j‖ * kamHilbertKernel i j ≤ kamHilbertConst * ‖A‖ := by
  simp_rw [kamHilbertKernel_comm _ j]
  exact kamHilbert_cs j I _ (norm_nonneg _) (kamEntry_sum_sq_col_le A j I)

/-- **Hilbert-matrix bound** (blueprint `bpW:w1:schur` (i)): the Schur bound for `B`. -/
theorem kamHilbertB_bound (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) :
    KamSchurBound (kamHilbertB A) (kamHilbertConst * ‖A‖) :=
  ⟨fun i J => by simpa only [norm_kamHilbertB] using kamHilbert_row_le A i J,
    fun j I => by simpa only [norm_kamHilbertB] using kamHilbert_col_le A j I⟩

/-- **Hilbert-matrix operator** (blueprint `bpW:w1:schur` (i)): `B_ij = |A_ij|/|i-j|`, `B_ii = 0`,
is a bounded operator, `(Bv)_i = ∑_j B_ij v_j` absolutely convergent. -/
def kamHilbertCLM (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  kamSchurCLM (kamHilbertB A) (kamHilbertB_bound A)

theorem kamHilbertCLM_hasSum (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+) :
    HasSum (fun j => kamHilbertB A i j * v j) (kamHilbertCLM A v i) :=
  kamSchurCLM_hasSum _ v i

/-- `‖B‖ ≤ (π/√3) ‖A‖` (blueprint `bpW:w1:schur` (i)). -/
theorem norm_kamHilbertCLM_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) :
    ‖kamHilbertCLM A‖ ≤ Real.pi / Real.sqrt 3 * ‖A‖ :=
  norm_kamSchurCLM_le _

/-- **Diagonal multiplier** (blueprint `bpW:w1:schur` (ii)): `(A_ii)` is a multiplier of norm at
most `‖A‖`. -/
def kamEntryDiagCLM (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) :
    lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  weightedDiagCLM (fun i => kamEntry A i i) (norm_kamEntry_diag_le A)

theorem norm_kamEntryDiagCLM_le (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2) :
    ‖kamEntryDiagCLM A‖ ≤ ‖A‖ :=
  norm_diagCLM_le _ _

/-! ### Dominated matrices -/

/-- The domination hypothesis of `bpW:w1:schur` (iii): `|F_ij| ≤ c |M_ij| / |i-j|` for `i ≠ j` and
`|F_ii| ≤ c |M_ii|`. -/
structure KamDominated (F M : ℕ+ → ℕ+ → K) (c : ℝ) : Prop where
  off : ∀ i j : ℕ+, i ≠ j → ‖F i j‖ ≤ c * ‖M i j‖ / |(i : ℝ) - (j : ℝ)|
  diag : ∀ i : ℕ+, ‖F i i‖ ≤ c * ‖M i i‖

theorem KamDominated.entry_le {F M : ℕ+ → ℕ+ → K} {c : ℝ} (h : KamDominated F M c) (i j : ℕ+) :
    ‖F i j‖ ≤ c * ((if i = j then ‖M i i‖ else 0) + ‖M i j‖ * kamHilbertKernel i j) := by
  by_cases hij : i = j
  · subst hij
    simpa [kamHilbertKernel_self] using h.diag i
  · have := h.off i j hij
    rw [kamHilbertKernel_of_ne hij]
    simp only [hij, ite_false]
    calc ‖F i j‖ ≤ c * ‖M i j‖ / |(i : ℝ) - (j : ℝ)| := this
      _ = _ := by ring

/-- **Weights do not change the ratios** (blueprint `bpW:w1:schur` (iv)): if `F` is dominated by
`M`, then the weighted matrices `α_i F_ij / β_j`, `α_i M_ij / β_j` (`α, β > 0`: the matrices of the
representatives for the weights `ω_{a,p̄}`, `ω_{a,p}`) satisfy the same domination. -/
theorem KamDominated.weighted {F M : ℕ+ → ℕ+ → K} {c : ℝ} (h : KamDominated F M c)
    (α β : ℕ+ → ℝ) (hα : ∀ i, 0 < α i) (hβ : ∀ j, 0 < β j) :
    KamDominated (fun i j => ((α i / β j : ℝ) : K) * F i j)
      (fun i j => ((α i / β j : ℝ) : K) * M i j) c := by
  have hn : ∀ i j (x : K), ‖((α i / β j : ℝ) : K) * x‖ = α i / β j * ‖x‖ := fun i j x => by
    rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (div_pos (hα i) (hβ j))]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [hn, hn]
    have := h.off i j hij
    calc α i / β j * ‖F i j‖ ≤ α i / β j * (c * ‖M i j‖ / |(i : ℝ) - (j : ℝ)|) :=
          mul_le_mul_of_nonneg_left this (div_pos (hα i) (hβ j)).le
      _ = _ := by ring
  · rw [hn, hn]
    calc α i / β i * ‖F i i‖ ≤ α i / β i * (c * ‖M i i‖) :=
          mul_le_mul_of_nonneg_left (h.diag i) (div_pos (hα i) (hβ i)).le
      _ = _ := by ring

/-- **Dominated matrices** (blueprint `bpW:w1:schur` (iii)): Schur bound with
`Λ = c (1 + π/√3) ‖A‖`. -/
theorem kamSchurBound_of_dominated (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    {F : ℕ+ → ℕ+ → K} {c : ℝ} (hc : 0 ≤ c) (h : KamDominated F (kamEntry A) c) :
    KamSchurBound F (c * (1 + kamHilbertConst) * ‖A‖) := by
  classical
  have hAn := norm_nonneg A
  refine ⟨fun i J => ?_, fun j I => ?_⟩
  · calc ∑ j ∈ J, ‖F i j‖
        ≤ ∑ j ∈ J, c * ((if i = j then ‖kamEntry A i i‖ else 0) +
            ‖kamEntry A i j‖ * kamHilbertKernel i j) :=
          Finset.sum_le_sum fun j _ => h.entry_le i j
      _ = c * ((if i ∈ J then ‖kamEntry A i i‖ else 0) +
            ∑ j ∈ J, ‖kamEntry A i j‖ * kamHilbertKernel i j) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq]
      _ ≤ c * (‖A‖ + kamHilbertConst * ‖A‖) := by
          gcongr
          · split_ifs
            · exact norm_kamEntry_diag_le A i
            · exact hAn
          · exact kamHilbert_row_le A i J
      _ = _ := by ring
  · calc ∑ i ∈ I, ‖F i j‖
        ≤ ∑ i ∈ I, c * ((if i = j then ‖kamEntry A i i‖ else 0) +
            ‖kamEntry A i j‖ * kamHilbertKernel i j) :=
          Finset.sum_le_sum fun i _ => h.entry_le i j
      _ = c * ((if j ∈ I then ‖kamEntry A j j‖ else 0) +
            ∑ i ∈ I, ‖kamEntry A i j‖ * kamHilbertKernel i j) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_eq']
      _ ≤ c * (‖A‖ + kamHilbertConst * ‖A‖) := by
          gcongr
          · split_ifs
            · exact norm_kamEntry_diag_le A j
            · exact hAn
          · exact kamHilbert_col_le A j I
      _ = _ := by ring

/-- **Dominated matrices define bounded operators** (blueprint `bpW:w1:schur` (iii)): if
`|F_ij| ≤ c |A_ij|/|i-j|` (`i ≠ j`) and `|F_ii| ≤ c |A_ii|`, then `F` defines a bounded operator
`T` with `(T v)_i = ∑_j F_ij v_j` and `‖T‖ ≤ c (1 + π/√3) ‖A‖ ≤ 3 c ‖A‖`. -/
theorem exists_clm_of_dominated (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    {F : ℕ+ → ℕ+ → K} {c : ℝ} (hc : 0 ≤ c) (h : KamDominated F (kamEntry A) c) :
    ∃ T : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2,
      (∀ (v : lp (fun _ : ℕ+ => K) 2) (i : ℕ+), HasSum (fun j => F i j * v j) (T v i)) ∧
        ‖T‖ ≤ c * (1 + Real.pi / Real.sqrt 3) * ‖A‖ ∧ ‖T‖ ≤ 3 * c * ‖A‖ := by
  have hb := kamSchurBound_of_dominated A hc h
  refine ⟨kamSchurCLM F hb, fun v i => kamSchurCLM_hasSum hb v i, norm_kamSchurCLM_le hb, ?_⟩
  refine (norm_kamSchurCLM_le hb).trans ?_
  have h2 := kamHilbertConst_lt_two
  have hAn := norm_nonneg A
  unfold kamHilbertConst at h2 ⊢
  nlinarith [mul_nonneg (sub_nonneg.2 h2.le) (mul_nonneg hc hAn)]

end KAM.Wave
