/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Seq.Embed
public import KAM.Frozen.Wave.Defs.Lam

/-!
# Frequency multipliers and complex rotations (blueprint-W `bpW:w1:diag`, parts (i)-(iii))

Off-frontier, source-faithful infrastructure; the dependency graph is still being built.

* (i) `lamMul m hm r`: the representative `D_μ`, `μ_j = (λ_j/j)^r`, of `λ^r : ℓ^{a,p+r} → ℓ^{a,p}`;
  `lamMul_represents`, `norm_lamMul_le`, `norm_lamMul_eq` (`= (1+m)^{r/2}` for `r ≥ 0`),
  `lamMul_comp_neg` (inverse `λ^{-r}`).
* (ii) `not_exists_bounded_lam_pow`: `λ^r`, `r > 0`, is not bounded `ℓ^{a,p} → ℓ^{a,p}`.
* (iii) `rotCLM`: `R_t z = (e^{-iλ_j t} z_j)`, isometry, group law, strong continuity.

The real flow (iv) is in `KAM.Wave.Seq.Flow`.
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

variable {K : Type*} [RCLike K] {m : ℝ} (hm : 0 < m)

theorem pnat_le_lam (j : ℕ+) : (j : ℝ) ≤ lam m hm j := by
  unfold lam
  exact Real.le_sqrt_of_sq_le (by linarith)

theorem lam_le_sqrt_mul (j : ℕ+) : lam m hm j ≤ Real.sqrt (1 + m) * j := by
  have hj : (1 : ℝ) ≤ j := Nat.one_le_cast.2 j.pos
  unfold lam
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  have h1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_nonneg hm.le (sub_nonneg.2 h1)]

/-- `1 ≤ λ_j / j ≤ √(1+m)`. -/
theorem one_le_lam_div_pnat (j : ℕ+) : 1 ≤ lam m hm j / j := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  rw [le_div_iff₀ hj, one_mul]; exact pnat_le_lam hm j

theorem lam_div_pnat_le (j : ℕ+) : lam m hm j / j ≤ Real.sqrt (1 + m) := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  rw [div_le_iff₀ hj]; linarith [lam_le_sqrt_mul hm j, mul_comm (Real.sqrt (1 + m)) (j : ℝ)]

/-- The multiplier `μ_j = (λ_j/j)^r` of `bpW:w1:diag`. -/
def lamRatio (m : ℝ) (hm : 0 < m) (r : ℝ) (j : ℕ+) : ℝ := (lam m hm j / j) ^ r

theorem lamRatio_pos (r : ℝ) (j : ℕ+) : 0 < lamRatio m hm r j :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_lam_div_pnat hm j)) _

theorem lamRatio_le_of_nonneg {r : ℝ} (hr : 0 ≤ r) (j : ℕ+) :
    lamRatio m hm r j ≤ (1 + m) ^ (r / 2) := by
  unfold lamRatio
  calc (lam m hm j / j) ^ r ≤ Real.sqrt (1 + m) ^ r :=
        Real.rpow_le_rpow (by linarith [one_le_lam_div_pnat hm j]) (lam_div_pnat_le hm j) hr
    _ = (1 + m) ^ (r / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]; congr 1; ring

theorem lamRatio_le_one_of_neg {r : ℝ} (hr : r < 0) (j : ℕ+) : lamRatio m hm r j ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_lam_div_pnat hm j) hr.le

theorem norm_lamRatio_cast_le (r : ℝ) (j : ℕ+) :
    ‖((lamRatio m hm r j : ℝ) : K)‖ ≤ max 1 ((1 + m) ^ (r / 2)) := by
  rw [RCLike.norm_ofReal, abs_of_pos (lamRatio_pos hm r j)]
  rcases lt_or_ge r 0 with h | h
  · exact (lamRatio_le_one_of_neg hm h j).trans (le_max_left _ _)
  · exact (lamRatio_le_of_nonneg hm h j).trans (le_max_right _ _)

/-- **Frequency multiplier** (blueprint `bpW:w1:diag` (i)): the representative `D_μ`,
`μ_j = (λ_j/j)^r`, of `λ^r : ℓ^{a,p+r} → ℓ^{a,p}`. -/
def lamMul (m : ℝ) (hm : 0 < m) (r : ℝ) : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2 :=
  weightedDiagCLM (fun j => ((lamRatio m hm r j : ℝ) : K)) (norm_lamRatio_cast_le hm r)

@[simp] theorem lamMul_apply (r : ℝ) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    lamMul m hm r y j = ((lamRatio m hm r j : ℝ) : K) * y j := rfl

/-- `bpW:w1:diag` (i): `λ^r` maps `κ_{a,p+r} y` to `κ_{a,p}(lamMul y)`, i.e. the representative of
`λ^r : ℓ^{a,p+r} → ℓ^{a,p}` is `lamMul`: `τ_{a,p}(λ^r κ_{a,p+r} y) = D_μ y`. -/
theorem lamMul_represents (a p r : ℝ) (y : lp (fun _ : ℕ+ => K) 2) (j : ℕ+) :
    (ellWeight a p j : K) * (((lam m hm j ^ r : ℝ) : K) * coeffW a (p + r) y j) =
      lamMul m hm r y j := by
  rw [lamMul_apply]
  refine (diag_representative a (p + r) a p (fun j => ((lam m hm j ^ r : ℝ) : K)) y j).trans ?_
  congr 2
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  have h : ellWeight a p j / ellWeight a (p + r) j = (j : ℝ) ^ (-r) := by
    have := embedRatio_eq a (p + r) a p j
    simp only [embedRatio, sub_self, zero_mul, Real.exp_zero, mul_one] at this
    rw [this]; congr 1; ring
  rw [← RCLike.ofReal_div, h, ← RCLike.ofReal_mul]
  congr 1
  unfold lamRatio
  rw [Real.div_rpow (by linarith [pnat_le_lam hm j]) hj.le, Real.rpow_neg hj.le, div_eq_mul_inv]

/-- `bpW:w1:diag` (i): `‖λ^r‖ ≤ (1+m)^{r/2}` for `r ≥ 0`. -/
theorem norm_lamMul_le_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    ‖(lamMul m hm r : lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ ≤ (1 + m) ^ (r / 2) :=
  norm_diagCLM_le' _ _ (fun j => by
    rw [RCLike.norm_ofReal, abs_of_pos (lamRatio_pos hm r j)]
    exact lamRatio_le_of_nonneg hm hr j)

/-- `bpW:w1:diag` (i): `‖λ^r‖ ≤ 1` for `r < 0`. -/
theorem norm_lamMul_le_of_neg {r : ℝ} (hr : r < 0) :
    ‖(lamMul m hm r : lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ ≤ 1 :=
  norm_diagCLM_le' _ _ (fun j => by
    rw [RCLike.norm_ofReal, abs_of_pos (lamRatio_pos hm r j)]
    exact lamRatio_le_one_of_neg hm hr j)

/-- `bpW:w1:diag` (i): the norm of `λ^r` is exactly `(1+m)^{r/2}` for `r ≥ 0` (attained at
`j = 1`). -/
theorem norm_lamMul_eq {r : ℝ} (hr : 0 ≤ r) :
    ‖(lamMul m hm r : lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ = (1 + m) ^ (r / 2) := by
  refine le_antisymm (norm_lamMul_le_of_nonneg hm hr) ?_
  have h : ‖((lamRatio m hm r 1 : ℝ) : K)‖ ≤ ‖(lamMul m hm r : lp (fun _ : ℕ+ => K) 2 →L[K] _)‖ :=
    norm_le_norm_diagCLM (fun j => ((lamRatio m hm r j : ℝ) : K)) (norm_lamRatio_cast_le hm r) 1
  rw [RCLike.norm_ofReal, abs_of_pos (lamRatio_pos hm r 1)] at h
  convert h using 1
  have h1 : lam m hm 1 = Real.sqrt (1 + m) := by simp [lam]
  unfold lamRatio
  rw [h1, PNat.one_coe, Nat.cast_one, div_one, Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
  congr 1; ring

/-- `bpW:w1:diag` (i): `λ^{-r}` is the inverse of `λ^r` (on the representatives). -/
theorem lamMul_comp_neg (r : ℝ) (y : lp (fun _ : ℕ+ => K) 2) :
    lamMul m hm r (lamMul m hm (-r) y) = y := by
  ext j
  simp only [lamMul_apply, ← mul_assoc, ← RCLike.ofReal_mul]
  have : lamRatio m hm r j * lamRatio m hm (-r) j = 1 := by
    unfold lamRatio
    rw [Real.rpow_neg (lt_of_lt_of_le one_pos (one_le_lam_div_pnat hm j)).le]
    exact mul_inv_cancel₀
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_lam_div_pnat hm j)) _).ne'
  rw [this]; simp

/-- `bpW:w1:diag` (ii): for `r > 0`, `λ^r` is not a bounded operator `ℓ^{a,p} → ℓ^{a,p}` (its
representative would be the diagonal operator with multiplier `λ_j^r`, which is unbounded). -/
theorem not_exists_bounded_lam_pow {r : ℝ} (hr : 0 < r) :
    ¬ ∃ T : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2,
      ∀ y j, T y j = ((lam m hm j ^ r : ℝ) : K) * y j := by
  refine not_exists_diag_of_unbounded (fun B => ?_)
  obtain ⟨n, hn⟩ := ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop B
    |>.exists
  refine ⟨n.succPNat, ?_⟩
  rw [RCLike.norm_ofReal, abs_of_pos (Real.rpow_pos_of_pos
    (lt_of_lt_of_le (by exact_mod_cast (n.succPNat).pos) (pnat_le_lam hm _)) _)]
  refine lt_of_lt_of_le hn (Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hr.le)
  refine le_trans ?_ (pnat_le_lam hm _)
  simp

end KAM.Wave

end
