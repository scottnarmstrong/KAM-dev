/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Algebra.C1
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Finite trigonometric polynomials on the angle plane (T2-CONF, N3)

A trigonometric polynomial of parity `p` is a dense list `d : List ℤ` of integer mantissas read
through a key map `κ : ℕ → ℤ × ℤ` (slot `i` carries the mode `κ i`):
* even (`p = false`): `evalK κ false d φ = Σ_i d_i cos (κ i · φ)`;
* odd (`p = true`): `evalK κ true d φ = -Σ_i d_i sin (κ i · φ)`.

These are the phase-1 conventions (`scripts/sjsu/rigor/ballft.py`): `Σ a_k e^{ik·φ}` with `a`
symmetric, resp. `Σ i b_k e^{ik·φ}` with `b` antisymmetric. The symmetry matters only for products
(`Trig/Product.lean`); everything here holds for any list.

The concrete key map is the dense square layout `Layout.key C S i = (i % S - C, i / S - C)`
(half-width `C`, row stride `S`).

Main results:
* `hasFDerivAt_evalK`, `differentiable_evalK`;
* `pderiv_evalK`: `∂_a (evalK κ p d) = evalK κ (!p) (dlist κ a p d)`, a parity flip with the factor
  `± (κ i)_a` per slot;
* `abs_evalK_le`: `|evalK κ p d φ| ≤ l1 d`; `abs_pderiv_evalK_le`: `|∂_a evalK| ≤ wl1 κ a d`
  (`= Σ_i |(κ i)_a| |d_i|`);
* `lowB_le_evalK`: `evalK κ false d φ ≥ Σ_{κ i = 0} d_i - Σ_{κ i ≠ 0} |d_i|`.

The computable functions (`l1`, `wl1`, `lowB`, `dlist`) are structural recursions with an index
accumulator (no `Array`), so the kernel evaluates them in linear time.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset

/-! ### The basis functions -/

/-- The trigonometric basis function of parity `p`: `cos` (even) or `-sin` (odd). -/
noncomputable def trig (p : Bool) (x : ℝ) : ℝ := if p then -Real.sin x else Real.cos x

/-- The sign `+1` (even) or `-1` (odd) of the derivative of `trig p`
(`trig' p = psgn p · trig !p`). -/
def psgn (p : Bool) : ℤ := if p then -1 else 1

theorem abs_trig_le (p : Bool) (x : ℝ) : |trig p x| ≤ 1 := by
  unfold trig
  split_ifs
  · rw [abs_neg]; exact Real.abs_sin_le_one x
  · exact Real.abs_cos_le_one x

theorem hasDerivAt_trig (p : Bool) (x : ℝ) :
    HasDerivAt (trig p) ((psgn p : ℝ) * trig (!p) x) x := by
  cases p
  · simp only [trig, psgn, Bool.not_false, ite_true, Bool.false_eq_true, ite_false, Int.cast_one,
      one_mul]
    exact Real.hasDerivAt_cos x
  · simp only [trig, psgn, Bool.not_true, ite_true, Bool.false_eq_true, ite_false, Int.cast_neg,
      Int.cast_one, neg_one_mul]
    exact (Real.hasDerivAt_sin x).neg

theorem trig_false_zero : trig false 0 = 1 := by simp [trig]

/-! ### Modes and the dot product -/

/-- The component `a` of a mode. -/
def kc (k : ℤ × ℤ) (a : Fin 2) : ℤ := if a = 0 then k.1 else k.2

/-- `k · φ = k₁ φ₀ + k₂ φ₁`. -/
def kdot (k : ℤ × ℤ) (φ : Fin 2 → ℝ) : ℝ := (k.1 : ℝ) * φ 0 + (k.2 : ℝ) * φ 1

/-- `φ ↦ k · φ` as a continuous linear map. -/
noncomputable def kdotL (k : ℤ × ℤ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (k.1 : ℝ) • ContinuousLinearMap.proj 0 + (k.2 : ℝ) • ContinuousLinearMap.proj 1

theorem kdotL_apply (k : ℤ × ℤ) (φ : Fin 2 → ℝ) : kdotL k φ = kdot k φ := by
  simp [kdotL, kdot]

theorem kdotL_single (k : ℤ × ℤ) (a : Fin 2) : kdotL k (Pi.single a 1) = (kc k a : ℝ) := by
  rw [kdotL_apply, kdot, kc]
  fin_cases a <;> simp

theorem hasFDerivAt_kdot (k : ℤ × ℤ) (φ : Fin 2 → ℝ) : HasFDerivAt (kdot k) (kdotL k) φ := by
  have : kdot k = ⇑(kdotL k) := funext fun φ => (kdotL_apply k φ).symm
  rw [this]
  exact (kdotL k).hasFDerivAt

theorem kdot_zero (φ : Fin 2 → ℝ) : kdot (0, 0) φ = 0 := by simp [kdot]

/-! ### Evaluation -/

/-- `Σ_i d_i trig_p (κ i · φ)` over the slots of a dense list. -/
noncomputable def evalK (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) : ℝ :=
  ∑ i ∈ range d.length, (d.getD i 0 : ℝ) * trig p (kdot (κ i) φ)

theorem hasFDerivAt_evalK (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) :
    HasFDerivAt (evalK κ p d)
      (∑ i ∈ range d.length, ((d.getD i 0 : ℝ) * ((psgn p : ℝ) * trig (!p) (kdot (κ i) φ))) •
        kdotL (κ i)) φ := by
  have h : ∀ i ∈ range d.length, HasFDerivAt (fun φ => (d.getD i 0 : ℝ) * trig p (kdot (κ i) φ))
      (((d.getD i 0 : ℝ) * ((psgn p : ℝ) * trig (!p) (kdot (κ i) φ))) • kdotL (κ i)) φ := by
    intro i _
    have := ((hasDerivAt_trig p (kdot (κ i) φ)).comp_hasFDerivAt φ (hasFDerivAt_kdot (κ i) φ))
    have := this.const_mul (d.getD i 0 : ℝ)
    rw [smul_smul] at this
    exact this
  have := HasFDerivAt.sum h
  convert this using 1
  ext φ
  simp [evalK]

theorem differentiable_evalK (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) :
    Differentiable ℝ (evalK κ p d) := fun φ => (hasFDerivAt_evalK κ p d φ).differentiableAt

/-- The partial derivative as a raw sum. -/
theorem pderiv_evalK_sum (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) (a : Fin 2) :
    pderiv (evalK κ p d) φ a = ∑ i ∈ range d.length,
      ((psgn p * kc (κ i) a * d.getD i 0 : ℤ) : ℝ) * trig (!p) (kdot (κ i) φ) := by
  rw [pderiv, (hasFDerivAt_evalK κ p d φ).fderiv, _root_.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_apply, kdotL_single, smul_eq_mul]
  push_cast
  ring

/-! ### Index-accumulator recursions (kernel-linear) -/

/-- `[f i₀ d₀, f (i₀+1) d₁, …]`: an index-aware map by structural recursion. -/
def mapIx {α β : Type*} (f : ℕ → α → β) : ℕ → List α → List β
  | _, [] => []
  | i, a :: l => f i a :: mapIx f (i + 1) l

theorem length_mapIx {α β : Type*} (f : ℕ → α → β) : ∀ (i : ℕ) (l : List α),
    (mapIx f i l).length = l.length
  | _, [] => rfl
  | i, _ :: l => by simp [mapIx, length_mapIx f (i + 1) l]

theorem getD_mapIx {α β : Type*} (f : ℕ → α → β) {a₀ : α} {b₀ : β} (hf : ∀ i, f i a₀ = b₀) :
    ∀ (i₀ : ℕ) (l : List α) (i : ℕ), (mapIx f i₀ l).getD i b₀ = f (i₀ + i) (l.getD i a₀)
  | i₀, [], i => by simp [mapIx, hf]
  | i₀, a :: l, 0 => by simp [mapIx]
  | i₀, a :: l, i + 1 => by
    simp only [mapIx, List.getD_cons_succ]
    rw [getD_mapIx f hf (i₀ + 1) l i]
    congr 1
    omega

/-- One pass of pairwise sums: `[a, b, c, d, …] ↦ [a + b, c + d, …]` (lazy, constructor-producing:
the kernel walks it without nesting). -/
def pairSum : List ℤ → List ℤ
  | [] => []
  | [a] => [a]
  | a :: b :: l => (a + b) :: pairSum l

/-- **Balanced sum**: repeated pairwise passes (`fuel` levels; `64` is unreachable in practice).
The kernel's evaluation depth is `O(log n)`, where a linear `foldr`/accumulator sum nests `n` deep
and hits the kernel's recursion limit on lists of `10⁴` slots (design signal, N3 kernel test). -/
def treeSum : ℕ → List ℤ → ℤ
  | _, [] => 0
  | _, [a] => a
  | 0, a :: b :: l => (a :: b :: l).sum
  | f + 1, a :: b :: l => treeSum f (pairSum (a :: b :: l))

theorem sum_pairSum : ∀ l : List ℤ, (pairSum l).sum = l.sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    rw [pairSum, List.sum_cons, sum_pairSum l, List.sum_cons, List.sum_cons, add_assoc]

theorem treeSum_eq : ∀ (f : ℕ) (l : List ℤ), treeSum f l = l.sum
  | _, [] => by simp [treeSum]
  | _, [a] => by simp [treeSum]
  | 0, a :: b :: l => rfl
  | f + 1, a :: b :: l => by
    rw [treeSum, treeSum_eq f, sum_pairSum]

/-- `Σ_i f (i₀ + i) d_i` by direct structural recursion (proof form). -/
def sumIxR {α : Type*} (f : ℕ → α → ℤ) : ℕ → List α → ℤ
  | _, [] => 0
  | i, a :: l => f i a + sumIxR f (i + 1) l

/-- `Σ_i f (i₀ + i) d_i` as a balanced sum of `mapIx` (kernel form). -/
def sumIx {α : Type*} (f : ℕ → α → ℤ) (i₀ : ℕ) (l : List α) : ℤ := treeSum 64 (mapIx f i₀ l)

theorem sum_mapIx {α : Type*} (f : ℕ → α → ℤ) : ∀ (i₀ : ℕ) (l : List α),
    (mapIx f i₀ l).sum = sumIxR f i₀ l
  | _, [] => rfl
  | i, a :: l => by rw [mapIx, List.sum_cons, sum_mapIx f (i + 1) l, sumIxR]

theorem sumIxR_eq {α : Type*} (f : ℕ → α → ℤ) {a₀ : α} : ∀ (i₀ : ℕ) (l : List α),
    sumIxR f i₀ l = ∑ i ∈ range l.length, f (i₀ + i) (l.getD i a₀)
  | _, [] => by simp [sumIxR]
  | i₀, a :: l => by
    rw [sumIxR, sumIxR_eq f (i₀ + 1) l, List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 1
    omega

theorem sumIx_eq {α : Type*} (f : ℕ → α → ℤ) {a₀ : α} (i₀ : ℕ) (l : List α) :
    sumIx f i₀ l = ∑ i ∈ range l.length, f (i₀ + i) (l.getD i a₀) := by
  rw [sumIx, treeSum_eq, sum_mapIx, sumIxR_eq]

/-! ### Derivative lists and norms -/

/-- The mantissas of `∂_a`: slot `i` times `psgn p · (κ i)_a`, read with parity `!p`. -/
def dlist (κ : ℕ → ℤ × ℤ) (a : Fin 2) (p : Bool) (d : List ℤ) : List ℤ :=
  mapIx (fun i c => psgn p * kc (κ i) a * c) 0 d

theorem length_dlist (κ : ℕ → ℤ × ℤ) (a : Fin 2) (p : Bool) (d : List ℤ) :
    (dlist κ a p d).length = d.length := length_mapIx _ _ _

theorem getD_dlist (κ : ℕ → ℤ × ℤ) (a : Fin 2) (p : Bool) (d : List ℤ) (i : ℕ) :
    (dlist κ a p d).getD i 0 = psgn p * kc (κ i) a * d.getD i 0 := by
  rw [dlist, getD_mapIx (fun i c => psgn p * kc (κ i) a * c) (a₀ := 0) (b₀ := 0)
    (fun i => by simp) 0 d i, zero_add]

/-- **The partial derivative is a parity flip**:
`∂_a evalK κ p d = evalK κ (!p) (dlist κ a p d)`. -/
theorem pderiv_evalK (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) (a : Fin 2) :
    pderiv (evalK κ p d) φ a = evalK κ (!p) (dlist κ a p d) φ := by
  rw [pderiv_evalK_sum, evalK, length_dlist]
  refine sum_congr rfl fun i _ => ?_
  rw [getD_dlist]

/-- The `ℓ¹` norm `Σ |d_i|` of the mantissas. -/
def l1 (d : List ℤ) : ℤ := sumIx (fun _ c => |c|) 0 d

/-- The weighted norm `Σ_i |(κ i)_a| |d_i|`, a bound of `∂_a`. -/
def wl1 (κ : ℕ → ℤ × ℤ) (a : Fin 2) (d : List ℤ) : ℤ := sumIx (fun i c => |kc (κ i) a| * |c|) 0 d

theorem l1_eq (d : List ℤ) : l1 d = ∑ i ∈ range d.length, |d.getD i 0| := by
  rw [l1, sumIx_eq _ (a₀ := 0)]

theorem wl1_eq (κ : ℕ → ℤ × ℤ) (a : Fin 2) (d : List ℤ) :
    wl1 κ a d = ∑ i ∈ range d.length, |kc (κ i) a| * |d.getD i 0| := by
  rw [wl1, sumIx_eq _ (a₀ := 0)]
  simp

theorem l1_nonneg (d : List ℤ) : 0 ≤ l1 d := by
  rw [l1_eq]; exact sum_nonneg fun _ _ => abs_nonneg _

theorem l1_dlist (κ : ℕ → ℤ × ℤ) (a : Fin 2) (p : Bool) (d : List ℤ) :
    l1 (dlist κ a p d) = wl1 κ a d := by
  rw [l1_eq, wl1_eq, length_dlist]
  refine sum_congr rfl fun i _ => ?_
  rw [getD_dlist, abs_mul, abs_mul]
  cases p <;> simp [psgn]

/-- **The sup bound**: `|evalK κ p d φ| ≤ Σ |d_i|`. -/
theorem abs_evalK_le (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) :
    |evalK κ p d φ| ≤ (l1 d : ℝ) := by
  rw [evalK, l1_eq]
  push_cast
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  calc |(d.getD i 0 : ℝ)| * |trig p (kdot (κ i) φ)| ≤ |(d.getD i 0 : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left (abs_trig_le _ _) (abs_nonneg _)
    _ = _ := by rw [mul_one]

/-- **The derivative bound**: `|∂_a evalK κ p d φ| ≤ Σ_i |(κ i)_a| |d_i|`. -/
theorem abs_pderiv_evalK_le (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ)
    (a : Fin 2) : |pderiv (evalK κ p d) φ a| ≤ (wl1 κ a d : ℝ) := by
  rw [pderiv_evalK, ← l1_dlist κ a p d]
  exact abs_evalK_le _ _ _ _

/-- The lower-bound functional `Σ_{κ i = 0} d_i - Σ_{κ i ≠ 0} |d_i|`. -/
def lowB (κ : ℕ → ℤ × ℤ) (d : List ℤ) : ℤ :=
  sumIx (fun i c => if κ i = (0, 0) then c else -|c|) 0 d

/-- **Positivity bound** for an even polynomial: `evalK κ false d φ ≥ c₀ - Σ_{k ≠ 0} |c_k|`. -/
theorem lowB_le_evalK (κ : ℕ → ℤ × ℤ) (d : List ℤ) (φ : Fin 2 → ℝ) :
    (lowB κ d : ℝ) ≤ evalK κ false d φ := by
  rw [lowB, sumIx_eq _ (a₀ := 0), evalK]
  push_cast
  refine sum_le_sum fun i _ => ?_
  simp only [zero_add]
  split_ifs with h
  · rw [h, kdot_zero, trig_false_zero, mul_one]
  · have h1 := abs_trig_le false (kdot (κ i) φ)
    have h2 : |(d.getD i 0 : ℝ) * trig false (kdot (κ i) φ)| ≤ |(d.getD i 0 : ℝ)| := by
      rw [abs_mul]
      calc |(d.getD i 0 : ℝ)| * |trig false (kdot (κ i) φ)| ≤ |(d.getD i 0 : ℝ)| * 1 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = _ := mul_one _
    linarith [neg_abs_le ((d.getD i 0 : ℝ) * trig false (kdot (κ i) φ))]

/-! ### Linearity in the mantissas -/

/-- Slotwise difference of two lists, padded by zeros to the longer length. -/
def lsub : List ℤ → List ℤ → List ℤ
  | [], [] => []
  | a :: l, [] => a :: lsub l []
  | [], b :: m => -b :: lsub [] m
  | a :: l, b :: m => (a - b) :: lsub l m

theorem length_lsub : ∀ c d : List ℤ, (lsub c d).length = max c.length d.length
  | [], [] => by simp [lsub]
  | a :: l, [] => by simp [lsub, length_lsub l []]
  | [], b :: m => by simp [lsub, length_lsub [] m]
  | a :: l, b :: m => by simp [lsub, length_lsub l m, Nat.succ_max_succ]

theorem getD_lsub : ∀ (c d : List ℤ) (i : ℕ), (lsub c d).getD i 0 = c.getD i 0 - d.getD i 0
  | [], [], i => by simp [lsub]
  | a :: l, [], 0 => by simp [lsub]
  | a :: l, [], i + 1 => by
    simp only [lsub, List.getD_cons_succ, List.getD_nil, sub_zero]
    simpa using getD_lsub l [] i
  | [], b :: m, 0 => by simp [lsub]
  | [], b :: m, i + 1 => by
    simp only [lsub, List.getD_cons_succ, List.getD_nil, zero_sub]
    simpa using getD_lsub [] m i
  | a :: l, b :: m, 0 => by simp [lsub]
  | a :: l, b :: m, i + 1 => by
    simp only [lsub, List.getD_cons_succ]
    exact getD_lsub l m i

/-- The sum may run over any range covering the list. -/
theorem evalK_eq_sum_of_le (κ : ℕ → ℤ × ℤ) (p : Bool) (d : List ℤ) (φ : Fin 2 → ℝ) {n : ℕ}
    (hn : d.length ≤ n) :
    evalK κ p d φ = ∑ i ∈ range n, (d.getD i 0 : ℝ) * trig p (kdot (κ i) φ) := by
  rw [evalK]
  refine sum_subset (range_subset_range.mpr hn) fun i _ hi => ?_
  rw [mem_range, not_lt] at hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem evalK_lsub (κ : ℕ → ℤ × ℤ) (p : Bool) (c d : List ℤ) (φ : Fin 2 → ℝ) :
    evalK κ p (lsub c d) φ = evalK κ p c φ - evalK κ p d φ := by
  rw [evalK, length_lsub, evalK_eq_sum_of_le κ p c φ (le_max_left _ _),
    evalK_eq_sum_of_le κ p d φ (le_max_right _ _), ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [getD_lsub]
  push_cast
  ring

/-- **Two polynomials on the same key map are `C¹`-close** with the `ℓ¹` and weighted norms of their
difference. -/
theorem c1Close_evalK (κ : ℕ → ℤ × ℤ) (p : Bool) (c d : List ℤ) {e₁ : ℝ}
    (h₁ : ∀ a, (wl1 κ a (lsub c d) : ℝ) ≤ e₁) :
    C1Close (evalK κ p c) (evalK κ p d) (l1 (lsub c d)) e₁ := by
  refine ⟨differentiable_evalK κ p c, differentiable_evalK κ p d, fun φ => ?_, fun φ a => ?_⟩
  · rw [← evalK_lsub]; exact abs_evalK_le _ _ _ _
  · rw [← C1Close.pderiv_sub (differentiable_evalK κ p c) (differentiable_evalK κ p d)]
    have : evalK κ p c - evalK κ p d = evalK κ p (lsub c d) :=
      funext fun φ => (evalK_lsub κ p c d φ).symm
    rw [this]
    exact (abs_pderiv_evalK_le _ _ _ _ _).trans (h₁ a)

/-! ### The dense square layout -/

/-- The dense square layout of half-width `C` and row stride `S`: slot `i` carries the mode
`(i % S - C, i / S - C)`. A polynomial on it has `2 C S + 2 C + 1` slots (`Layout.len`), and its
columns `i % S > 2 C` are padding (zero). -/
def Layout.key (C S : ℕ) (i : ℕ) : ℤ × ℤ := (((i % S : ℕ) : ℤ) - C, ((i / S : ℕ) : ℤ) - C)

/-- The number of slots of the square layout. -/
def Layout.len (C S : ℕ) : ℕ := 2 * C * S + 2 * C + 1

/-- The padding columns are zero from index `i₀` on (structural recursion). -/
def colsOkAux (C S : ℕ) : ℕ → List ℤ → Bool
  | _, [] => true
  | i, c :: l => (c == 0 || decide (i % S ≤ 2 * C)) && colsOkAux C S (i + 1) l

/-- The padding columns are zero: every nonzero slot has column `i % S ≤ 2 C`. -/
def colsOk (C S : ℕ) (d : List ℤ) : Bool := colsOkAux C S 0 d

theorem colsOkAux_spec {C S : ℕ} : ∀ {i₀ : ℕ} {d : List ℤ}, colsOkAux C S i₀ d = true →
    ∀ i, d.getD i 0 ≠ 0 → (i₀ + i) % S ≤ 2 * C
  | _, [], _, i, hi => by simp at hi
  | i₀, c :: l, h, 0, hi => by
    simp only [colsOkAux, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    simp only [List.getD_cons_zero] at hi
    rcases h.1 with h0 | h0
    · exact absurd h0 hi
    · simpa using h0
  | i₀, c :: l, h, i + 1, hi => by
    simp only [colsOkAux, Bool.and_eq_true] at h
    simp only [List.getD_cons_succ] at hi
    have := colsOkAux_spec h.2 i hi
    rwa [show i₀ + 1 + i = i₀ + (i + 1) by omega] at this

theorem colsOk_spec {C S : ℕ} {d : List ℤ} (h : colsOk C S d = true) (i : ℕ)
    (hi : d.getD i 0 ≠ 0) : i % S ≤ 2 * C := by
  simpa using colsOkAux_spec h i hi

end KAM.EffectiveStability.Tube

end
