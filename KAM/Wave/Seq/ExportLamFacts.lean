/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Frozen.Wave.Defs.Lam
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Elementary facts about the linear frequencies `λ_j` (blueprint `bpW:w0:basis#lambda-facts`)

The paragraph after Definition `bpW:w0:basis` (`w0-conventions.tex:45-47`) records, for `m > 0`,
`λ_j = √(j² + m)` and `f(s) = √(s² + m)`:

* `j < λ_j < j + √m` (`lamBasis_bounds`) and `j/λ_j < 1` (`lamBasis_div_lt_one`);
* `j ↦ λ_j` is strictly increasing (`lamBasis_strictMono`);
* `f` is strictly convex on `ℝ` (`lamFun_strictConvexOn`), with `f'(s) = s/f(s)`
  (`lamFun_hasDerivAt`, `lamFun_deriv`), `0 < f'(s) < 1` for `s > 0` (`lamFun_deriv_pos_lt_one`)
  and `f'` strictly increasing (`lamFun_deriv_strictMono`);
* `λ_{j+1} - λ_j = (2j+1)/(λ_{j+1} + λ_j) < 1` (`lamBasis_succ_sub`).

`lamBasis_facts` bundles the paragraph. Here `f = lamFun m`, and `λ_j = f(j)` (`lam_eq_lamFun`).
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

/-- The function `f(s) = √(s² + m)` of `bpW:w0:basis#lambda-facts`. -/
def lamFun (m : ℝ) (s : ℝ) : ℝ := Real.sqrt (s ^ 2 + m)

variable {m : ℝ} (hm : 0 < m)
include hm

theorem lam_eq_lamFun (j : ℕ+) : lam m hm j = lamFun m (j : ℝ) := rfl

theorem lamFun_pos (s : ℝ) : 0 < lamFun m s :=
  Real.sqrt_pos.2 (by positivity)

theorem lamFun_sq (s : ℝ) : lamFun m s ^ 2 = s ^ 2 + m :=
  Real.sq_sqrt (by positivity)

/-- `j < λ_j < j + √m` (`bpW:w0:basis#lambda-facts`). -/
theorem lamBasis_bounds (j : ℕ+) :
    (j : ℝ) < lam m hm j ∧ lam m hm j < (j : ℝ) + Real.sqrt m := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.pos
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hsq : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  refine ⟨(Real.lt_sqrt hj.le).2 (by linarith), (Real.sqrt_lt' (by positivity)).2 ?_⟩
  nlinarith [mul_pos hj hsm]

/-- `j / λ_j < 1` (`bpW:w0:basis#lambda-facts`). -/
theorem lamBasis_div_lt_one (j : ℕ+) : (j : ℝ) / lam m hm j < 1 :=
  (div_lt_one (lamFun_pos hm _)).2 (lamBasis_bounds hm j).1

/-- `j ↦ λ_j` is strictly increasing (`bpW:w0:basis#lambda-facts`). -/
theorem lamBasis_strictMono : StrictMono (lam m hm) := fun i j hij => by
  have hi : (0 : ℝ) < i := by exact_mod_cast i.pos
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)

/-- `√((x²+m)(y²+m)) > xy + m` for `x ≠ y` (strict Cauchy-Schwarz). -/
theorem lamFun_mul_gt {x y : ℝ} (hxy : x ≠ y) : x * y + m < lamFun m x * lamFun m y := by
  have hP : lamFun m x * lamFun m y = Real.sqrt ((x ^ 2 + m) * (y ^ 2 + m)) := by
    unfold lamFun; rw [Real.sqrt_mul (by positivity)]
  rw [hP]
  rcases lt_or_ge (x * y + m) 0 with h | h
  · exact h.trans_le (Real.sqrt_nonneg _)
  · refine (Real.lt_sqrt h).2 ?_
    have hd : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hxy
      positivity
    nlinarith [mul_pos hm hd]

/-- **`f(s) = √(s² + m)` is strictly convex on `ℝ`** (`bpW:w0:basis#lambda-facts`). -/
theorem lamFun_strictConvexOn : StrictConvexOn ℝ univ (lamFun m) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hfx := lamFun_pos hm x
  have hfy := lamFun_pos hm y
  have hR : 0 < a • lamFun m x + b • lamFun m y := by
    simp only [smul_eq_mul]; positivity
  show Real.sqrt ((a • x + b • y) ^ 2 + m) < a • lamFun m x + b • lamFun m y
  refine (Real.sqrt_lt' hR).2 ?_
  have key := lamFun_mul_gt hm hxy
  have h1 := lamFun_sq hm x
  have h2 := lamFun_sq hm y
  have hb' : b = 1 - a := by linarith
  subst hb'
  simp only [smul_eq_mul]
  set fx := lamFun m x
  set fy := lamFun m y
  have e : (a * fx + (1 - a) * fy) ^ 2 - ((a * x + (1 - a) * y) ^ 2 + m) =
      2 * a * (1 - a) * (fx * fy - (x * y + m)) := by
    have e2 : (a * fx + (1 - a) * fy) ^ 2 =
        a ^ 2 * fx ^ 2 + (1 - a) ^ 2 * fy ^ 2 + 2 * a * (1 - a) * (fx * fy) := by ring
    rw [e2, h1, h2]; ring
  have : 0 < 2 * a * (1 - a) * (fx * fy - (x * y + m)) := by
    have : 0 < fx * fy - (x * y + m) := by linarith
    positivity
  linarith

/-- `f'(s) = s / f(s)` (`bpW:w0:basis#lambda-facts`). -/
theorem lamFun_hasDerivAt (s : ℝ) : HasDerivAt (lamFun m) (s / lamFun m s) s := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2 + m) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const m
  have h2 := h.sqrt (by positivity : s ^ 2 + m ≠ 0)
  convert h2 using 1
  · rfl
  · exact (mul_div_mul_left s _ two_ne_zero).symm

theorem lamFun_deriv (s : ℝ) : deriv (lamFun m) s = s / lamFun m s :=
  (lamFun_hasDerivAt hm s).deriv

/-- `0 < f'(s) = s/f(s) < 1` for `s > 0` (`bpW:w0:basis#lambda-facts`). -/
theorem lamFun_deriv_pos_lt_one {s : ℝ} (hs : 0 < s) :
    deriv (lamFun m) s = s / lamFun m s ∧ 0 < deriv (lamFun m) s ∧ deriv (lamFun m) s < 1 := by
  rw [lamFun_deriv hm]
  have hf := lamFun_pos hm s
  have hlt : s < lamFun m s := (Real.lt_sqrt hs.le).2 (by linarith)
  exact ⟨rfl, div_pos hs hf, (div_lt_one hf).2 hlt⟩

/-- `f'` is strictly increasing on `ℝ` (`bpW:w0:basis#lambda-facts`). -/
theorem lamFun_deriv_strictMono : StrictMono (deriv (lamFun m)) := by
  have h := (lamFun_strictConvexOn hm).strictMonoOn_deriv
    (fun x _ => (lamFun_hasDerivAt hm x).differentiableAt)
  exact fun x y hxy => h (mem_univ x) (mem_univ y) hxy

/-- `λ_{j+1} - λ_j = (2j+1)/(λ_{j+1} + λ_j) < 1` (`bpW:w0:basis#lambda-facts`). -/
theorem lamBasis_succ_sub (j : ℕ+) :
    lam m hm (j + 1) - lam m hm j = (2 * (j : ℝ) + 1) / (lam m hm (j + 1) + lam m hm j) ∧
      (2 * (j : ℝ) + 1) / (lam m hm (j + 1) + lam m hm j) < 1 := by
  have hc : ((j + 1 : ℕ+) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have h1 := lamBasis_bounds hm j
  have h2 := lamBasis_bounds hm (j + 1)
  rw [hc] at h2
  have hs1 : lam m hm (j + 1) ^ 2 = ((j : ℝ) + 1) ^ 2 + m := by
    rw [lam_eq_lamFun, lamFun_sq hm, hc]
  have hs0 : lam m hm j ^ 2 = (j : ℝ) ^ 2 + m := lamFun_sq hm _
  have hpos : 0 < lam m hm (j + 1) + lam m hm j := by
    have := lamFun_pos hm (j : ℝ)
    have := lamFun_pos hm ((j + 1 : ℕ+) : ℝ)
    rw [lam_eq_lamFun, lam_eq_lamFun]; positivity
  refine ⟨?_, (div_lt_one hpos).2 (by linarith)⟩
  rw [eq_div_iff hpos.ne']
  nlinarith [hs1, hs0]

/-- **The elementary facts about `λ`** (blueprint `bpW:w0:basis#lambda-facts`,
`w0-conventions.tex:45-47`): for `m > 0`, `λ_j = √(j²+m)`, `f(s) = √(s²+m)`:
`j < λ_j < j + √m`, `j/λ_j < 1`, `j ↦ λ_j` strictly increasing, `f` strictly convex on `ℝ` with
`0 < f'(s) = s/f(s) < 1` for `s > 0`, `f'` strictly increasing, and
`λ_{j+1} - λ_j = (2j+1)/(λ_{j+1}+λ_j) < 1`. -/
theorem lamBasis_facts :
    (∀ j : ℕ+, (j : ℝ) < lam m hm j ∧ lam m hm j < (j : ℝ) + Real.sqrt m) ∧
    (∀ j : ℕ+, (j : ℝ) / lam m hm j < 1) ∧
    StrictMono (lam m hm) ∧
    StrictConvexOn ℝ univ (fun s : ℝ => Real.sqrt (s ^ 2 + m)) ∧
    (∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + m)) (s / Real.sqrt (s ^ 2 + m)) s) ∧
    (∀ s : ℝ, 0 < s → 0 < deriv (fun s : ℝ => Real.sqrt (s ^ 2 + m)) s ∧
      deriv (fun s : ℝ => Real.sqrt (s ^ 2 + m)) s < 1) ∧
    StrictMono (deriv (fun s : ℝ => Real.sqrt (s ^ 2 + m))) ∧
    (∀ j : ℕ+, lam m hm (j + 1) - lam m hm j =
        (2 * (j : ℝ) + 1) / (lam m hm (j + 1) + lam m hm j) ∧
      (2 * (j : ℝ) + 1) / (lam m hm (j + 1) + lam m hm j) < 1) :=
  ⟨lamBasis_bounds hm, lamBasis_div_lt_one hm, lamBasis_strictMono hm, lamFun_strictConvexOn hm,
    lamFun_hasDerivAt hm, fun _ hs => (lamFun_deriv_pos_lt_one hm hs).2,
    lamFun_deriv_strictMono hm, lamBasis_succ_sub hm⟩

end KAM.Wave
