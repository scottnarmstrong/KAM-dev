/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.TailTau
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The fibres of a three-frequency vector, walked by the kernel in integer fixed point

For `ω = (ω', 1) ∈ ℝ³` the fibered bound `KAM.smallDivisorSum_snoc_le_fiber` (any `τ`) sums one
term per mode `k' = (a, b)` of `ω' ∈ ℝ²` with `0 < |a| + |b| ≤ N`: `2N(N + 1)` modes. This module
evaluates that sum with natural numbers only, so that its cost per mode is a few machine-size
operations:

* **the walk** (`walk2`): rows `a = i - N`, columns `b = j - (N - |a|)`, `i, j < 2^l`,
  `2N + 1 ≤ 2^l`, both by bisection (`balFold`, recursion depth `2l`); a cell outside the diamond,
  and `(0, 0)`, is `0`; a failed mode makes the walk `none`. `walk2_sound`: an injection of
  `modeBox 2 N` into the cells, so the modes' values sum to at most the walk's value;
* **the dyadic box** `DBox2`: `ω'_i ∈ [C_i - R_i, C_i + R_i] / 2^q`. The mode's data are integers:
  `X = a C₀ + b C₁`, `p = ⌊(2^q - 2X)/2^{q+1}⌋`, `Y = |X + p 2^q|`, `Rd = |a| R₀ + |b| R₁`; the
  test is `Rd < Y` and `2(Y + Rd) ≤ 2^q`, i.e. `|x + p| + rad ≤ 1/2` and `L = (Y - Rd)/2^q > 0`;
* **the weights** `E_j = powUp e P 64 j / 2^P ≥ (e/2^P)^j` (`powUp_ge`): binary powering of the
  fixed-point `e ≥ 2^P e^{-2πδ}`, each product rounded **up**;
* **the term** of a mode, `⌈2^P (E_{s+|p|} L⁻² + E_s ([p ≠ 0] (|p| - 1/2)⁻² + E₁ · 7.3075))⌉`
  (`mode3`), each of the three quotients rounded up (`ceilDiv`); `7.3075 ≥ 4 + π²/3`.

`smallDivisorSum_snoc2_le_walk`: `S((ω', 1), δ) ≤ E₁ · 3.3075 + s/2^P + tailQ` for a walk `some s`.
Nothing is assumed of `p` beyond the checked inequalities; the rounding is outward everywhere.
-/

@[expose] public section

namespace KAM.CertificateSharp.Fiber

open KAM KAM.Certificate KAM.CertificateSharp

/-- `2^P` as a shift: the kernel evaluates `Nat.shiftLeft` on literals directly, while `2 ^ P`
goes through Mathlib's `Monoid.npow` instance (about `0.2 ms` per occurrence in the kernel). -/
def pow2 (P : ℕ) : ℕ := Nat.shiftLeft 1 P

theorem pow2_eq (P : ℕ) : pow2 P = 2 ^ P := by
  show 1 <<< P = 2 ^ P
  rw [Nat.shiftLeft_eq, one_mul]

/-! ### The balanced walk -/

/-- `∑_{i < 2^l} f (a + i)` by bisection; `none` if a term is `none`. -/
def balFold (f : ℕ → Option ℕ) : ℕ → ℕ → Option ℕ
  | 0, a => f a
  | l + 1, a =>
    match balFold f l a with
    | none => none
    | some x =>
      match balFold f l (a + pow2 l) with
      | none => none
      | some y => some (x + y)

theorem balFold_eq_some {f : ℕ → Option ℕ} {l a s : ℕ} (h : balFold f l a = some s) :
    (∀ i < 2 ^ l, ∃ v, f (a + i) = some v) ∧
      s = ∑ i ∈ Finset.range (2 ^ l), (f (a + i)).getD 0 := by
  induction l generalizing a s with
  | zero =>
    simp only [balFold] at h
    refine ⟨fun i hi => ⟨s, ?_⟩, ?_⟩
    · rw [show i = 0 by simpa using hi, add_zero]; exact h
    · simp [h]
  | succ l ih =>
    simp only [balFold] at h
    rcases h1 : balFold f l a with _ | x
    · rw [h1] at h; simp at h
    rw [h1] at h
    rw [pow2_eq] at h
    rcases h2 : balFold f l (a + 2 ^ l) with _ | y
    · rw [h2] at h; simp at h
    rw [h2] at h
    simp only [Option.some.injEq] at h
    obtain ⟨hall1, hs1⟩ := ih h1
    obtain ⟨hall2, hs2⟩ := ih h2
    refine ⟨fun i hi => ?_, ?_⟩
    · by_cases his : i < 2 ^ l
      · exact hall1 i his
      · obtain ⟨v, hv⟩ := hall2 (i - 2 ^ l) (by rw [pow_succ] at hi; omega)
        exact ⟨v, by rwa [show a + 2 ^ l + (i - 2 ^ l) = a + i by omega] at hv⟩
    · rw [← h, hs1, hs2, pow_succ, mul_two, Finset.sum_range_add]
      simp only [add_assoc]

/-- The row coordinate `a = i - N`. -/
def rowA (N i : ℕ) : ℤ := (i : ℤ) - N

/-- The half-width `N - |a|` of the row. -/
def rowW (N i : ℕ) : ℕ := N - (rowA N i).natAbs

/-- The cell `(i, j)` for the mode function `M`: `b = j - (N - |a|)`; `0` outside the diamond and
at `(0, 0)`. -/
def cell2 (M : ℤ → ℤ → Option ℕ) (N i j : ℕ) : Option ℕ :=
  if 2 * rowW N i < j then some 0
  else if rowA N i = 0 ∧ (j : ℤ) - rowW N i = 0 then some 0
  else M (rowA N i) ((j : ℤ) - rowW N i)

/-- The row `i`. -/
def row2 (M : ℤ → ℤ → Option ℕ) (N l i : ℕ) : Option ℕ :=
  if 2 * N < i then some 0 else balFold (cell2 M N i) l 0

/-- **The walk** of `M` over `0 < |a| + |b| ≤ N`. -/
def walk2 (M : ℤ → ℤ → Option ℕ) (N l : ℕ) : Option ℕ := balFold (row2 M N l) l 0

theorem modeNat_two (k : Fin 2 → ℤ) : modeNat k = (k 0).natAbs + (k 1).natAbs := by
  simp [modeNat, Fin.sum_univ_two]

section Walk

variable {M : ℤ → ℤ → Option ℕ} {N l : ℕ}

/-- The row and column of a mode. -/
def cellOf (N : ℕ) (k : Fin 2 → ℤ) : ℕ × ℕ :=
  ((k 0 + N).toNat, (k 1 + (N - (k 0).natAbs : ℕ)).toNat)

theorem cellOf_spec {k : Fin 2 → ℤ} (hk : k ∈ modeBox 2 N) :
    (cellOf N k).1 ≤ 2 * N ∧ rowA N (cellOf N k).1 = k 0 ∧
      rowW N (cellOf N k).1 = N - (k 0).natAbs ∧
      (cellOf N k).2 ≤ 2 * rowW N (cellOf N k).1 ∧
      ((cellOf N k).2 : ℤ) - rowW N (cellOf N k).1 = k 1 ∧ ¬ (k 0 = 0 ∧ k 1 = 0) := by
  obtain ⟨hk0, hkN⟩ := mem_modeBox.mp hk
  rw [modeNat_two] at hkN
  have ha : rowA N (k 0 + N).toNat = k 0 := by
    unfold rowA; omega
  have hw : rowW N (k 0 + N).toNat = N - (k 0).natAbs := by
    unfold rowW; rw [ha]
  refine ⟨by simp only [cellOf]; omega, ha, hw, ?_, ?_, ?_⟩
  · simp only [cellOf]; rw [hw]; omega
  · simp only [cellOf]; rw [hw]; omega
  · rintro ⟨h0, h1⟩
    apply hk0
    funext i
    fin_cases i
    · exact h0
    · exact h1

theorem cellOf_injOn : Set.InjOn (cellOf N) (modeBox 2 N : Set (Fin 2 → ℤ)) := by
  intro k hk l hl h
  obtain ⟨-, ha, -, -, hb, -⟩ := cellOf_spec (N := N) hk
  obtain ⟨-, ha', -, -, hb', -⟩ := cellOf_spec (N := N) hl
  have h1 : (cellOf N k).1 = (cellOf N l).1 := by rw [h]
  have h2 : (cellOf N k).2 = (cellOf N l).2 := by rw [h]
  funext i
  fin_cases i
  · change k 0 = l 0
    rw [← ha, ← ha', h1]
  · change k 1 = l 1
    rw [← hb, ← hb', h1, h2]

theorem cell2_of_mem {k : Fin 2 → ℤ} (hk : k ∈ modeBox 2 N) :
    cell2 M N (cellOf N k).1 (cellOf N k).2 = M (k 0) (k 1) := by
  obtain ⟨-, ha, -, hj, hb, hne⟩ := cellOf_spec (N := N) hk
  unfold cell2
  rw [ite_eq_right (by omega), ha, hb, ite_eq_right hne]

/-- **Soundness of the walk**: every mode of `modeBox 2 N` passes, and their values sum to at
most the walk's value. -/
theorem walk2_sound (hl : 2 * N + 1 ≤ 2 ^ l) {s : ℕ} (h : walk2 M N l = some s) :
    ∃ U : (Fin 2 → ℤ) → ℕ, (∀ k ∈ modeBox 2 N, M (k 0) (k 1) = some (U k)) ∧
      ∑ k ∈ modeBox 2 N, U k ≤ s := by
  obtain ⟨hrows, hs⟩ := balFold_eq_some h
  simp only [zero_add] at hrows hs
  have hcell : ∀ i ≤ 2 * N, ∀ j < 2 ^ l, ∃ v, cell2 M N i j = some v := by
    intro i hi j hj
    obtain ⟨v, hv⟩ := hrows i (by omega)
    rw [row2, ite_eq_right (by omega)] at hv
    obtain ⟨hall, -⟩ := balFold_eq_some hv
    simpa using hall j hj
  set g : ℕ × ℕ → ℕ := fun x =>
    if 2 * N < x.1 then 0 else (cell2 M N x.1 x.2).getD 0 with hg
  have hsg : s = ∑ x ∈ Finset.range (2 ^ l) ×ˢ Finset.range (2 ^ l), g x := by
    rw [Finset.sum_product, hs]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hg]
    split_ifs with hi2
    · rw [row2, ite_eq_left hi2]; simp
    · obtain ⟨v, hv⟩ := hrows i (Finset.mem_range.mp hi)
      rw [hv]
      rw [row2, ite_eq_right hi2] at hv
      obtain ⟨-, hv'⟩ := balFold_eq_some hv
      simpa using hv'
  have hj' : ∀ k ∈ modeBox 2 N, (cellOf N k).2 < 2 ^ l := fun k hk => by
    obtain ⟨-, -, -, hj, -, -⟩ := cellOf_spec (N := N) hk
    have : rowW N (cellOf N k).1 ≤ N := Nat.sub_le _ _
    omega
  refine ⟨fun k => g (cellOf N k), fun k hk => ?_, ?_⟩
  · obtain ⟨hi, -, -, -, -, -⟩ := cellOf_spec (N := N) hk
    obtain ⟨v, hv⟩ := hcell _ hi _ (hj' k hk)
    rw [← cell2_of_mem (M := M) hk, hv]
    simp only [hg, ite_eq_right (by omega : ¬ 2 * N < (cellOf N k).1), hv, Option.getD_some]
  · rw [hsg, ← Finset.sum_image fun k hk l hl h => cellOf_injOn hk hl h]
    refine Finset.sum_le_sum_of_subset fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hi, -, -, -, -, -⟩ := cellOf_spec (N := N) hk
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, hj' k hk⟩

end Walk

/-! ### Fixed point -/

/-- `⌈A / B⌉` for naturals. -/
def ceilDiv (A B : ℕ) : ℕ := (A + B - 1) / B

theorem div_le_ceilDiv (A : ℕ) {B : ℕ} (hB : 0 < B) : (A : ℝ) / B ≤ (ceilDiv A B : ℝ) := by
  have h : A ≤ ceilDiv A B * B := by
    unfold ceilDiv
    have h1 := Nat.div_add_mod (A + B - 1) B
    have h2 := Nat.mod_lt (A + B - 1) hB
    rw [mul_comm]
    generalize (A + B - 1) / B = Q at h1 ⊢
    generalize (A + B - 1) % B = r at h1 h2
    generalize B * Q = BQ at h1 ⊢
    omega
  rw [div_le_iff₀ (by exact_mod_cast hB)]
  exact_mod_cast h

/-- `⌈a b / 2^P⌉`. -/
def mulUp (P a b : ℕ) : ℕ := ceilDiv (a * b) (pow2 P)

theorem mulUp_ge (P a b : ℕ) :
    ((a : ℝ) / 2 ^ P) * ((b : ℝ) / 2 ^ P) ≤ (mulUp P a b : ℝ) / 2 ^ P := by
  have h := div_le_ceilDiv (a * b) (by positivity : 0 < 2 ^ P)
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  rw [mulUp, pow2_eq]
  calc ((a : ℝ) / 2 ^ P) * ((b : ℝ) / 2 ^ P) = ((a * b : ℕ) : ℝ) / ((2 ^ P : ℕ) : ℝ) / 2 ^ P := by
        push_cast; field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h h2.le

/-- One step of binary powering: square, and multiply by `e` if `r ≠ 0`, rounding up. -/
def sqMulUp (e P r h : ℕ) : ℕ := if r = 0 then mulUp P h h else mulUp P (mulUp P h h) e

/-- `2^P (e/2^P)^j` rounded up, by binary powering (`f` bits of fuel; `2^P` when it runs out,
which is an upper bound once `e ≤ 2^P`). -/
def powUp (e P : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => pow2 P
  | f + 1, j => if j = 0 then pow2 P else sqMulUp e P (j % 2) (powUp e P f (j / 2))

theorem powUp_ge {e P : ℕ} (he : e ≤ 2 ^ P) (f j : ℕ) :
    ((e : ℝ) / 2 ^ P) ^ j ≤ (powUp e P f j : ℝ) / 2 ^ P := by
  have h2 : (0 : ℝ) < 2 ^ P := by positivity
  have hx0 : (0 : ℝ) ≤ (e : ℝ) / 2 ^ P := by positivity
  have hx1 : (e : ℝ) / 2 ^ P ≤ 1 := by
    rw [div_le_one h2]; exact_mod_cast he
  have hone : ((pow2 P : ℕ) : ℝ) / 2 ^ P = 1 := by rw [pow2_eq]; push_cast; exact div_self h2.ne'
  induction f generalizing j with
  | zero =>
    simp only [powUp]
    rw [hone]
    exact pow_le_one₀ hx0 hx1
  | succ f ih =>
    simp only [powUp]
    split_ifs with hj
    · subst hj; rw [hone, pow_zero]
    · have hsq : ((e : ℝ) / 2 ^ P) ^ (2 * (j / 2)) ≤
          (mulUp P (powUp e P f (j / 2)) (powUp e P f (j / 2)) : ℝ) / 2 ^ P := by
        rw [pow_mul', sq]
        refine le_trans ?_ (mulUp_ge P _ _)
        exact mul_le_mul (ih _) (ih _) (by positivity) (by positivity)
      unfold sqMulUp
      split_ifs with hr
      · have hj2 : j = 2 * (j / 2) := by omega
        calc ((e : ℝ) / 2 ^ P) ^ j = ((e : ℝ) / 2 ^ P) ^ (2 * (j / 2)) := by rw [← hj2]
          _ ≤ _ := hsq
      · have hj2 : j = 2 * (j / 2) + 1 := by omega
        calc ((e : ℝ) / 2 ^ P) ^ j = ((e : ℝ) / 2 ^ P) ^ (2 * (j / 2)) * ((e : ℝ) / 2 ^ P) := by
              rw [← pow_succ, ← hj2]
          _ ≤ _ := by
              refine le_trans ?_ (mulUp_ge P _ _)
              exact mul_le_mul_of_nonneg_right hsq hx0

/-! ### The dyadic box and the modes -/

/-- The dyadic box of `ω' ∈ ℝ²`: `|ω'_i - C_i/2^q| ≤ R_i/2^q`. -/
structure DBox2 where
  /-- The scale `2^q`. -/
  q : ℕ
  /-- The centre of `ω'₀`, times `2^q`. -/
  C0 : ℤ
  /-- The centre of `ω'₁`, times `2^q`. -/
  C1 : ℤ
  /-- The radius of `ω'₀`, times `2^q`. -/
  R0 : ℕ
  /-- The radius of `ω'₁`, times `2^q`. -/
  R1 : ℕ

/-- The dyadic box as a `FreqBox`. -/
def DBox2.toBox (D : DBox2) : FreqBox :=
  [((D.C0 : ℚ) / 2 ^ D.q, (D.R0 : ℚ) / 2 ^ D.q), ((D.C1 : ℚ) / 2 ^ D.q, (D.R1 : ℚ) / 2 ^ D.q)]

/-- `⌊(2^q - 2X)/2^{q+1}⌋`, the nearest integer to `-X/2^q`. -/
def nearP (q : ℕ) (X : ℤ) : ℤ := ((pow2 q : ℕ) - 2 * X) / ((pow2 (q + 1) : ℕ) : ℤ)

/-- The rounded term of the mode `(a, b)` (times `2^P`), or `none` if its test fails. -/
def mode3 (D : DBox2) (e P : ℕ) (a b : ℤ) : Option ℕ :=
  let X : ℤ := a * D.C0 + b * D.C1
  let p : ℤ := nearP D.q X
  let Y : ℕ := (X + p * ((pow2 D.q : ℕ) : ℤ)).natAbs
  let Rd : ℕ := a.natAbs * D.R0 + b.natAbs * D.R1
  if Rd < Y ∧ 2 * (Y + Rd) ≤ pow2 D.q then
    let Es : ℕ := powUp e P 64 (a.natAbs + b.natAbs)
    some (ceilDiv (powUp e P 64 (a.natAbs + b.natAbs + p.natAbs) * pow2 (2 * D.q))
        ((Y - Rd) * (Y - Rd)) +
      (if p = 0 then 0 else ceilDiv (Es * 4) ((2 * p.natAbs - 1) * (2 * p.natAbs - 1))) +
      ceilDiv (Es * powUp e P 64 1 * 14615) (pow2 P * 2000))
  else none

/-! ### The kernel's forms

`mode3K` and `powUpK` are `mode3` and `powUp` written with the core operations (`Nat.add`,
`Nat.mul`, `Nat.shiftRight`, `Int.mul`, …) and `Bool` tests (`Nat.blt`, `Nat.ble`, `cond`). The
kernel evaluates them about `2.5×` faster and with `1.5×` less cache than the `Decidable`/instance
forms (measured on 420 modes: `0.39 s` against `1.0 s`); `mode3K_eq` and `powUpK_eq` identify them. -/

/-- `mulUp`, with core operations. -/
def mulUpK (P a b : ℕ) : ℕ := Nat.shiftRight (Nat.sub (Nat.add (Nat.mul a b) (pow2 P)) 1) P

/-- `sqMulUp`, with core operations. -/
def sqMulUpK (e P r h : ℕ) : ℕ := cond (Nat.beq r 0) (mulUpK P h h) (mulUpK P (mulUpK P h h) e)

/-- `powUp`, with core operations. -/
def powUpK (e P : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => pow2 P
  | f + 1, j => cond (Nat.beq j 0) (pow2 P) (sqMulUpK e P (Nat.mod j 2) (powUpK e P f (Nat.div j 2)))

/-- `mode3`, with core operations. -/
def mode3K (D : DBox2) (e P : ℕ) (a b : ℤ) : Option ℕ :=
  let X : ℤ := Int.add (Int.mul a D.C0) (Int.mul b D.C1)
  let p : ℤ := nearP D.q X
  let pa : ℕ := Int.natAbs p
  let Y : ℕ := Int.natAbs (Int.add X (Int.mul p (Int.ofNat (pow2 D.q))))
  let Rd : ℕ := Nat.add (Nat.mul (Int.natAbs a) D.R0) (Nat.mul (Int.natAbs b) D.R1)
  let s : ℕ := Nat.add (Int.natAbs a) (Int.natAbs b)
  let Es : ℕ := powUpK e P 64 s
  cond (Nat.blt Rd Y && Nat.ble (Nat.mul 2 (Nat.add Y Rd)) (pow2 D.q))
    (some (Nat.add (Nat.add
      (ceilDiv (Nat.mul (powUpK e P 64 (Nat.add s pa)) (pow2 (Nat.mul 2 D.q)))
        (Nat.mul (Nat.sub Y Rd) (Nat.sub Y Rd)))
      (cond (Nat.beq pa 0) 0
        (ceilDiv (Nat.mul Es 4) (Nat.mul (Nat.sub (Nat.mul 2 pa) 1) (Nat.sub (Nat.mul 2 pa) 1)))))
      (ceilDiv (Nat.mul (Nat.mul Es (powUpK e P 64 1)) 14615) (Nat.mul (pow2 P) 2000))))
    none

theorem mulUpK_eq (P a b : ℕ) : mulUpK P a b = mulUp P a b := by
  show (a * b + pow2 P - 1) >>> P = (a * b + pow2 P - 1) / pow2 P
  rw [Nat.shiftRight_eq_div_pow, pow2_eq]

theorem powUpK_eq (e P : ℕ) : ∀ f j, powUpK e P f j = powUp e P f j
  | 0, _ => rfl
  | f + 1, j => by
    simp only [powUpK, powUp, sqMulUpK, sqMulUp, mulUpK_eq, powUpK_eq e P f, Bool.cond_eq_ite,
      Nat.beq_eq]
    rfl

theorem mode3K_eq (D : DBox2) (e P : ℕ) (a b : ℤ) : mode3K D e P a b = mode3 D e P a b := by
  simp only [mode3K, mode3, powUpK_eq, Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq,
    Nat.ble_eq, Nat.beq_eq, Int.natAbs_eq_zero]
  rfl

section Modes

variable (D : DBox2) (e P : ℕ)

/-- The nearest integer of the mode `k`. -/
def modeP (k : Fin 2 → ℤ) : ℤ := nearP D.q (k 0 * D.C0 + k 1 * D.C1)

/-- The lower bound `L = (Y - Rd)/2^q` of the mode `k`. -/
noncomputable def modeL (k : Fin 2 → ℤ) : ℝ :=
  (((k 0 * D.C0 + k 1 * D.C1 + modeP D k * ((pow2 D.q : ℕ) : ℤ)).natAbs -
    ((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1) : ℕ) : ℝ) / 2 ^ D.q

/-- The weights `E_j = powUp e P 64 j / 2^P`. -/
noncomputable def wE (j : ℕ) : ℝ := (powUp e P 64 j : ℝ) / 2 ^ P

/-- The summand of `KAM.smallDivisorSum_snoc_le_fiber` at the mode `k`. -/
noncomputable def modeTerm (k : Fin 2 → ℤ) : ℝ :=
  wE e P (modeNat k + (modeP D k).natAbs) * (modeL D k ^ 2)⁻¹ +
    wE e P (modeNat k) * ((if modeP D k = 0 then 0
      else ((((modeP D k).natAbs : ℝ) - 1 / 2) ^ 2)⁻¹) + wE e P 1 * fiberConst)

variable {D e P}

theorem dot_sub_le_dbox {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (k : Fin 2 → ℤ) :
    |Diophantine.frequencyDot ω' k - ((k 0 * D.C0 + k 1 * D.C1 : ℤ) : ℝ) / 2 ^ D.q| ≤
      (((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 : ℕ) : ℝ) / 2 ^ D.q := by
  have h := dot_sub_boxDot_le hω k
  have e1 : (boxDot D.toBox k : ℝ) = ((k 0 * D.C0 + k 1 * D.C1 : ℤ) : ℝ) / 2 ^ D.q := by
    simp only [boxDot, DBox2.toBox, Fin.sum_univ_two]
    simp
    ring
  have e2 : (boxRad D.toBox k : ℝ) =
      (((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 : ℕ) : ℝ) / 2 ^ D.q := by
    simp only [boxRad, DBox2.toBox, Fin.sum_univ_two]
    simp
    ring
  rwa [e1, e2] at h

/-- A passing mode: the facts of the fibered bound, and its term below its rounded value. -/
theorem mode3_spec {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') {k : Fin 2 → ℤ} {u : ℕ}
    (h : mode3 D e P (k 0) (k 1) = some u) :
    |Diophantine.frequencyDot ω' k + modeP D k| ≤ 1 / 2 ∧ 0 < modeL D k ∧
      modeL D k ≤ |Diophantine.frequencyDot ω' k + modeP D k| ∧
      modeTerm D e P k ≤ (u : ℝ) / 2 ^ P := by
  unfold mode3 at h
  simp only [pow2_eq, Nat.cast_pow, Nat.cast_ofNat, ← sq] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hc
  simp only [Option.some.injEq] at h
  subst h
  obtain ⟨hlt, hhalf⟩ := hc
  set X : ℤ := k 0 * D.C0 + k 1 * D.C1 with hX
  set p : ℤ := nearP D.q X with hp
  set Y : ℕ := (X + p * 2 ^ D.q).natAbs with hY
  set Rd : ℕ := (k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 with hRd
  have hpP : modeP D k = p := rfl
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  have hd := dot_sub_le_dbox hω k
  rw [← hX, ← hRd] at hd
  have hYr : (Y : ℝ) = |(X : ℝ) + p * 2 ^ D.q| := by
    rw [hY, Nat.cast_natAbs]; push_cast; rfl
  have hxp : |(X : ℝ) / 2 ^ D.q + p| = (Y : ℝ) / 2 ^ D.q := by
    rw [hYr, ← abs_of_pos hq, ← abs_div, abs_of_pos hq]
    congr 1
    field_simp
  -- the two distance facts
  have h1 := abs_sub_abs_le_abs_sub (Diophantine.frequencyDot ω' k + p) ((X : ℝ) / 2 ^ D.q + p)
  have h2 := abs_sub_abs_le_abs_sub ((X : ℝ) / 2 ^ D.q + p) (Diophantine.frequencyDot ω' k + p)
  have e3 : Diophantine.frequencyDot ω' k + p - ((X : ℝ) / 2 ^ D.q + p) =
      Diophantine.frequencyDot ω' k - (X : ℝ) / 2 ^ D.q := by ring
  rw [e3] at h1
  rw [abs_sub_comm, e3] at h2
  have hhalf' : 2 * ((Y : ℝ) + Rd) ≤ 2 ^ D.q := by exact_mod_cast hhalf
  have hlt' : (Rd : ℝ) < Y := by exact_mod_cast hlt
  have hL : modeL D k = ((Y : ℝ) - Rd) / 2 ^ D.q := by
    simp only [modeL, hpP, pow2_eq, Nat.cast_pow, Nat.cast_ofNat]
    rw [Nat.cast_sub hlt.le]
  have hdist : |Diophantine.frequencyDot ω' k + p| ≤ 1 / 2 := by
    have : (Y : ℝ) / 2 ^ D.q + (Rd : ℝ) / 2 ^ D.q ≤ 1 / 2 := by
      rw [← add_div, div_le_iff₀ hq]; linarith
    linarith
  have hLpos : 0 < modeL D k := by rw [hL]; exact div_pos (by linarith) hq
  have hLle : modeL D k ≤ |Diophantine.frequencyDot ω' k + p| := by
    rw [hL, sub_div]; linarith
  refine ⟨hpP ▸ hdist, hLpos, hpP ▸ hLle, ?_⟩
  -- the term
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hYR : 0 < Y - Rd := Nat.sub_pos_of_lt hlt
  have hM := modeNat_two k
  push_cast
  rw [add_div, add_div]
  unfold modeTerm
  rw [hM, hpP, mul_add, ← add_assoc]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the nearest term
    have hc := div_le_ceilDiv (powUp e P 64 ((k 0).natAbs + (k 1).natAbs + p.natAbs) *
      2 ^ (2 * D.q)) (pow_pos hYR 2)
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hc hP.le)
    rw [hL, wE, Nat.cast_pow, Nat.cast_sub hlt.le]
    push_cast
    field_simp
    ring
  · -- the term `j = 0`
    split_ifs with hp0
    · simp
    · have hp1 : 1 ≤ p.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp0)
      have hpos : 0 < (2 * p.natAbs - 1) ^ 2 := pow_pos (by omega) 2
      have hc := div_le_ceilDiv (powUp e P 64 ((k 0).natAbs + (k 1).natAbs) * 4) hpos
      refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hc hP.le)
      rw [wE, Nat.cast_pow, Nat.cast_sub (by omega)]
      push_cast
      have h2p : (2 * (p.natAbs : ℝ) - 1) ≠ 0 := by
        have : (1 : ℝ) ≤ p.natAbs := by exact_mod_cast hp1
        linarith
      field_simp
      ring
  · -- the background `E_s E₁ C₀`
    have hc := div_le_ceilDiv (powUp e P 64 ((k 0).natAbs + (k 1).natAbs) * powUp e P 64 1 * 14615)
      (by positivity : 0 < 2 ^ P * 2000)
    refine le_trans ?_ (div_le_div_of_nonneg_right hc hP.le)
    have hC : fiberConst ≤ 14615 / 2000 := by
      unfold fiberConst
      have := Real.pi_pos
      have := Real.pi_lt_d2
      nlinarith
    rw [wE, wE]
    push_cast
    have hE0 : (0 : ℝ) ≤ (powUp e P 64 ((k 0).natAbs + (k 1).natAbs) : ℝ) := by positivity
    have hE1 : (0 : ℝ) ≤ (powUp e P 64 1 : ℝ) := by positivity
    calc (powUp e P 64 ((k 0).natAbs + (k 1).natAbs) : ℝ) / 2 ^ P *
          ((powUp e P 64 1 : ℝ) / 2 ^ P * fiberConst)
        ≤ (powUp e P 64 ((k 0).natAbs + (k 1).natAbs) : ℝ) / 2 ^ P *
          ((powUp e P 64 1 : ℝ) / 2 ^ P * (14615 / 2000)) := by gcongr
      _ = _ := by field_simp

end Modes

/-- **The bound of `S((ω', 1), δ)` from a walk**, `ω' ∈ ℝ²`, at the exponent `τ`. -/
theorem smallDivisorSum_snoc2_le_walk {D : DBox2} {e P N l s J τ : ℕ} {γ δ : ℚ}
    (he : e ≤ 2 ^ P) (hE : (2 : ℚ) ^ P ≤ e * expLowQ δ J) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : 0 < cLoQ δ τ N) (hl : 2 * N + 1 ≤ 2 ^ l) (hs : walk2 (mode3 D e P) N l = some s)
    {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω')
    (hdio : IsDiophantine (γ : ℝ) τ (Fin.snoc ω' 1 : Fin 3 → ℝ)) :
    smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (δ : ℝ) ≤
      (((powUp e P 64 1 : ℚ) / 2 ^ P * (99225 / 30000) + (s : ℚ) / 2 ^ P +
        tailQ γ δ τ N ((powUp e P 64 (N + 1) : ℚ) / 2 ^ P) : ℚ) : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hPq : (0 : ℚ) < 2 ^ P := by positivity
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  -- the weights
  have hx : Real.exp (-(2 * Real.pi * δ)) ≤ (e : ℝ) / 2 ^ P := by
    have h1 : (1 : ℚ) ≤ ((e : ℚ) / 2 ^ P) * expLowQ δ J := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hPq, one_mul]; exact hE
    have := exp_neg_le_of_expLowQ hδ h1
    push_cast at this
    exact this
  have hwE : ∀ j : ℕ, Real.exp (-(2 * Real.pi * δ) * j) ≤ wE e P j := fun j => by
    calc Real.exp (-(2 * Real.pi * δ) * j) = Real.exp (-(2 * Real.pi * δ)) ^ j := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ ((e : ℝ) / 2 ^ P) ^ j := pow_le_pow_left₀ (Real.exp_pos _).le hx j
      _ ≤ wE e P j := powUp_ge he 64 j
  -- the tail
  have hEp : Real.exp (-(2 * Real.pi * δ) * (N + 1)) ≤
      (((powUp e P 64 (N + 1) : ℚ) / 2 ^ P : ℚ) : ℝ) := by
    have := hwE (N + 1)
    push_cast at this ⊢
    exact this
  obtain ⟨hN, htail⟩ := sdTail_le_tailQ (γ := γ) hδ hc hEp
  -- the modes
  obtain ⟨U, hU, hsum⟩ := walk2_sound hl hs
  have hspec := fun k (hk : k ∈ modeBox 2 N) => mode3_spec hω (hU k hk)
  have key := smallDivisorSum_snoc_le_fiber hdio hγ' (Nat.cast_nonneg τ) hδ' hN
    (modeP D) (modeL D) (fun k => (((modeP D k).natAbs : ℝ) - 1 / 2))
    (fun k hk => (hspec k hk).1)
    (fun k hk => ⟨(hspec k hk).2.1, (hspec k hk).2.2.1⟩)
    (fun k hk hp => by
      have hp1 : (1 : ℝ) ≤ ((modeP D k).natAbs : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp)
      refine ⟨by linarith, ?_⟩
      have h5 := (hspec k hk).1
      have h6 := abs_sub_abs_le_abs_sub ((modeP D k : ℤ) : ℝ) (-(Diophantine.frequencyDot ω' k))
      have e : ((modeP D k : ℤ) : ℝ) - -Diophantine.frequencyDot ω' k =
          Diophantine.frequencyDot ω' k + modeP D k := by ring
      rw [e, abs_neg] at h6
      have e2 : ((modeP D k).natAbs : ℝ) = |((modeP D k : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [e2]
      linarith)
    (wE e P) hwE
  refine key.trans ?_
  have hpi2 : Real.pi ^ 2 / 3 ≤ 99225 / 30000 := by
    have := Real.pi_pos
    have := Real.pi_lt_d2
    nlinarith
  have hE1 : wE e P 1 * (Real.pi ^ 2 / 3) ≤ (powUp e P 64 1 : ℝ) / 2 ^ P * (99225 / 30000) :=
    mul_le_mul_of_nonneg_left hpi2 (by unfold wE; positivity)
  have hmodes : ∑ k ∈ modeBox 2 N, modeTerm D e P k ≤ (s : ℝ) / 2 ^ P := by
    calc ∑ k ∈ modeBox 2 N, modeTerm D e P k ≤ ∑ k ∈ modeBox 2 N, (U k : ℝ) / 2 ^ P :=
          Finset.sum_le_sum fun k hk => (hspec k hk).2.2.2
      _ = (∑ k ∈ modeBox 2 N, (U k : ℝ)) / 2 ^ P := (Finset.sum_div _ _ _).symm
      _ ≤ (s : ℝ) / 2 ^ P := by
          refine div_le_div_of_nonneg_right ?_ hP.le
          exact_mod_cast hsum
  have hsum3 := add_le_add (add_le_add hE1 hmodes) htail
  refine le_trans (le_of_eq ?_) (hsum3.trans (le_of_eq ?_))
  · rfl
  · push_cast; ring
end KAM.CertificateSharp.Fiber

end
