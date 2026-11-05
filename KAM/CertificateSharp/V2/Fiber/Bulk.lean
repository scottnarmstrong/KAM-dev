/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.Enum2
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# A bulk bound for the fibres far from resonance

`walk2` (`Fiber/Enum2.lean`) evaluates the fibered bound of `S((ω', 1), δ)`, `ω' ∈ ℝ²`, one fibre
`k' = (a, b)` at a time: `2N(N + 1)` fibres. This module bounds whole **runs** of fibres at once.

* **Runs.** In a row `a` (fixed), `x_b = a ω'₀ + b ω'₁` is an arithmetic progression in `b`, and
  the weights `e^{-2πδ(|a| + |b|)}` are geometric in `|b|`. On a run `b = σ (lo + i)`,
  `i₀ ≤ i ≤ i₁` (`σ = ±1`), with `p = nearP(X(i₀))` and `Z(i) = X(i) + p 2^q`,
  `Rd(i) = |a| R₀ + (lo + i) R₁` in the integer fixed point of `DBox2`, the functions
  `F = s Z - Rd` and `G = s Z + Rd` (`s` the common sign of `Z(i₀)`, `Z(i₁)`) are affine in `i`.
  So the endpoint checks `Rd < |Z|`, `2(|Z| + Rd) ≤ 2^q` hold on the whole run, and every fibre
  of the run has `Λ/2^q ≤ |x + p| ≤ 1/2`, `Λ = min(F(i₀), F(i₁))` (`run_point`, `blkK_spec`).
* **The run's value** (`blkValK`): the fibre terms sum to at most
  `x^{j₀} (x^{|p|} Λ⁻² 2^{2q} + [p ≠ 0] (|p| - 1/2)⁻² + x C₀) Σ_{j<2^t} x^j`, `j₀ = |a| + lo + i₀`,
  `x = e/2^P`; the geometric sum is a checked table (`gTabOk0`: `G_{t+1} ≥ G_t (1 + x^{2^t})`).
  A single fibre is the run `i₀ = i₁` (`t = 0`): `mode3`.
* **The walk** (`walkB`): rows `a = i - N` by `balFold`; each row is two half-rows
  (`b = lo + i ≥ 0`, `lo = 1` at `a = 0`, and `b = -(1 + i)`), bisected (`hrow`): a node is taken
  as one run if its check passes and either `rd · max G ≤ rn · Λ` (the distance varies by at most
  `rn/rd`) or its value is at most `tol`; otherwise it splits, down to single fibres. The
  acceptance rule affects cost and tightness only.
* **Soundness** (`BCov`): a per-fibre choice of `(p_k, L_k)` on a finite set of modes with the
  hypotheses of `KAM.smallDivisorSum_snoc_le_fiber`, whose summands (weights `x^j`) sum to at most
  `v`; it glues over disjoint unions. `walkB_sound` gives `BCov (modeBox 2 N) (s/2^P)`, and
  `smallDivisorSum_snoc2_le_bulk` is `smallDivisorSum_snoc2_le_walk` for `walkB`.

All functions the kernel evaluates are written with core operations (`Nat.blt`, `cond`,
`Int.mul`, `pow2`, `powUpK`, `mulUpK`), as `mode3K`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Fiber

open KAM KAM.Certificate KAM.CertificateSharp

/-! ### Covers of a set of fibres -/

/-- The summand of `KAM.smallDivisorSum_snoc_le_fiber` at the mode `k`, with the integer `p`, the
lower bound `L`, `L₀ = |p| - 1/2` and the weights `E_j = x^j`. -/
noncomputable def termX (x : ℝ) (k : Fin 2 → ℤ) (p : ℤ) (L : ℝ) : ℝ :=
  x ^ (modeNat k + p.natAbs) * (L ^ 2)⁻¹ +
    x ^ modeNat k * ((if p = 0 then 0 else ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹)) +
      x ^ 1 * fiberConst)

theorem termX_nonneg {x : ℝ} (hx : 0 ≤ x) (k : Fin 2 → ℤ) (p : ℤ) (L : ℝ) :
    0 ≤ termX x k p L := by
  have hif : (0 : ℝ) ≤ (if p = 0 then 0 else ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹)) := by
    split_ifs <;> positivity
  exact add_nonneg (mul_nonneg (pow_nonneg hx _) (inv_nonneg.mpr (sq_nonneg _)))
    (mul_nonneg (pow_nonneg hx _) (add_nonneg hif (mul_nonneg (pow_nonneg hx _)
      fiberConst_nonneg)))

/-- **A cover** of the finite set `S` of modes at the value `v`: integers `p_k` and lower bounds
`L_k` with the hypotheses of the fibered bound on `S`, whose summands sum to at most `v`. -/
def BCov (ω' : Fin 2 → ℝ) (x : ℝ) (S : Finset (Fin 2 → ℤ)) (v : ℝ) : Prop :=
  ∃ (pf : (Fin 2 → ℤ) → ℤ) (Lf : (Fin 2 → ℤ) → ℝ),
    (∀ k ∈ S, |Diophantine.frequencyDot ω' k + pf k| ≤ 1 / 2 ∧ 0 < Lf k ∧
      Lf k ≤ |Diophantine.frequencyDot ω' k + pf k|) ∧
    ∑ k ∈ S, termX x k (pf k) (Lf k) ≤ v

section Cover

variable {ω' : Fin 2 → ℝ} {x : ℝ}

theorem BCov.mono {S : Finset (Fin 2 → ℤ)} {v w : ℝ} (h : BCov ω' x S v) (hvw : v ≤ w) :
    BCov ω' x S w := by
  obtain ⟨pf, Lf, h1, h2⟩ := h
  exact ⟨pf, Lf, h1, h2.trans hvw⟩

theorem BCov.empty {v : ℝ} (hv : 0 ≤ v) : BCov ω' x ∅ v :=
  ⟨fun _ => 0, fun _ => 1, by simp, by simpa using hv⟩

theorem BCov.union {S T : Finset (Fin 2 → ℤ)} {v w : ℝ} (hST : Disjoint S T)
    (hS : BCov ω' x S v) (hT : BCov ω' x T w) : BCov ω' x (S ∪ T) (v + w) := by
  classical
  obtain ⟨p1, L1, h1, s1⟩ := hS
  obtain ⟨p2, L2, h2, s2⟩ := hT
  refine ⟨fun k => if k ∈ S then p1 k else p2 k, fun k => if k ∈ S then L1 k else L2 k,
    fun k hk => ?_, ?_⟩
  · by_cases hkS : k ∈ S
    · simp only [hkS, ↓reduceIte]
      exact h1 k hkS
    · simp only [hkS, ↓reduceIte]
      exact h2 k ((Finset.mem_union.mp hk).resolve_left hkS)
  · rw [Finset.sum_union hST]
    refine add_le_add (le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) s1)
      (le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) s2)
    · simp only [hk, ↓reduceIte]
    · have : k ∉ S := Finset.disjoint_right.mp hST hk
      simp only [this, ↓reduceIte]

theorem BCov.subset (hx : 0 ≤ x) {S T : Finset (Fin 2 → ℤ)} {v : ℝ} (hST : S ⊆ T)
    (hT : BCov ω' x T v) : BCov ω' x S v := by
  obtain ⟨pf, Lf, h1, s1⟩ := hT
  exact ⟨pf, Lf, fun k hk => h1 k (hST hk),
    (Finset.sum_le_sum_of_subset_of_nonneg hST fun k _ _ => termX_nonneg hx _ _ _).trans s1⟩

theorem BCov.biUnion {I : Finset ℕ} {S : ℕ → Finset (Fin 2 → ℤ)} {v : ℕ → ℝ}
    (hd : (I : Set ℕ).PairwiseDisjoint S) (h : ∀ i ∈ I, BCov ω' x (S i) (v i)) :
    BCov ω' x (I.biUnion S) (∑ i ∈ I, v i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using BCov.empty (ω' := ω') (x := x) (le_refl (0 : ℝ))
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    refine BCov.union ?_ (h a (Finset.mem_insert_self a I))
      (ih (hd.subset fun i hi => Finset.mem_insert_of_mem hi)
        fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finset.disjoint_biUnion_right]
    intro i hi
    exact hd (Finset.mem_insert_self a I) (Finset.mem_insert_of_mem hi)
      (fun hai => ha (hai ▸ hi))

end Cover

/-! ### The geometric table -/

theorem geom_two_mul (x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), x ^ j = (1 + x ^ n) * ∑ j ∈ Finset.range n, x ^ j := by
  rw [two_mul, Finset.sum_range_add, add_mul, one_mul, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [pow_add]

/-- The rows `t ≥ 1` of the geometric table: `G_{t+1} ≥ ⌈G_t (2^P + 2^P x^{2^t})/2^P⌉`. -/
def gTabOk (e P : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | t, g, h :: rest =>
    decide (mulUp P g (pow2 P + powUp e P 64 (pow2 t)) ≤ h) && gTabOk e P (t + 1) h rest

/-- **The geometric table** `G_t ≥ 2^P Σ_{j<2^t} x^j`, `x = e/2^P`, `t < gs.length`. -/
def gTabOk0 (e P : ℕ) : List ℕ → Bool
  | [] => false
  | g :: rest => decide (pow2 P ≤ g) && gTabOk e P 0 g rest

theorem gTabOk_spec {e P : ℕ} (he : e ≤ 2 ^ P) :
    ∀ (rest : List ℕ) (t g : ℕ), gTabOk e P t g rest = true →
      ∑ j ∈ Finset.range (2 ^ t), ((e : ℝ) / 2 ^ P) ^ j ≤ (g : ℝ) / 2 ^ P →
      ∀ i < rest.length + 1,
        ∑ j ∈ Finset.range (2 ^ (t + i)), ((e : ℝ) / 2 ^ P) ^ j ≤
          ((g :: rest).getD i 0 : ℝ) / 2 ^ P
  | [], t, g, _, hg, i, hi => by
    obtain rfl : i = 0 := by simpa using hi
    simpa using hg
  | h :: rest, t, g, hok, hg, i, hi => by
    simp only [gTabOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hstep, hrest⟩ := hok
    set x : ℝ := (e : ℝ) / 2 ^ P with hx
    have hx0 : 0 ≤ x := by positivity
    have hP : (0 : ℝ) < 2 ^ P := by positivity
    have hnext : ∑ j ∈ Finset.range (2 ^ (t + 1)), x ^ j ≤ (h : ℝ) / 2 ^ P := by
      rw [pow_succ, mul_comm, geom_two_mul]
      have hpow : x ^ (2 ^ t) ≤ (powUp e P 64 (pow2 t) : ℝ) / 2 ^ P := by
        rw [pow2_eq]; exact powUp_ge he 64 _
      have h1 : 1 + x ^ (2 ^ t) ≤ ((pow2 P + powUp e P 64 (pow2 t) : ℕ) : ℝ) / 2 ^ P := by
        rw [Nat.cast_add, add_div, pow2_eq]
        push_cast
        rw [div_self hP.ne']
        linarith
      have hS0 : 0 ≤ ∑ j ∈ Finset.range (2 ^ t), x ^ j :=
        Finset.sum_nonneg fun j _ => pow_nonneg hx0 j
      calc (1 + x ^ (2 ^ t)) * ∑ j ∈ Finset.range (2 ^ t), x ^ j
          ≤ ((pow2 P + powUp e P 64 (pow2 t) : ℕ) : ℝ) / 2 ^ P * ((g : ℝ) / 2 ^ P) :=
            mul_le_mul h1 hg hS0 (by positivity)
        _ = ((g : ℝ) / 2 ^ P) * (((pow2 P + powUp e P 64 (pow2 t) : ℕ) : ℝ) / 2 ^ P) :=
            mul_comm _ _
        _ ≤ (mulUp P g (pow2 P + powUp e P 64 (pow2 t)) : ℝ) / 2 ^ P := mulUp_ge P _ _
        _ ≤ (h : ℝ) / 2 ^ P :=
            div_le_div_of_nonneg_right (by exact_mod_cast hstep) hP.le
    cases i with
    | zero => simpa using hg
    | succ i =>
      have := gTabOk_spec he rest (t + 1) h hrest hnext i (by simpa using hi)
      rw [show t + (i + 1) = t + 1 + i by omega]
      simpa using this

theorem gTabOk0_spec {e P : ℕ} (he : e ≤ 2 ^ P) {gs : List ℕ} (h : gTabOk0 e P gs = true)
    {t : ℕ} (ht : t < gs.length) :
    ∑ j ∈ Finset.range (2 ^ t), ((e : ℝ) / 2 ^ P) ^ j ≤ (gs.getD t 0 : ℝ) / 2 ^ P := by
  cases gs with
  | nil => simp [gTabOk0] at h
  | cons g rest =>
    simp only [gTabOk0, Bool.and_eq_true, decide_eq_true_eq] at h
    have hg : ∑ j ∈ Finset.range (2 ^ 0), ((e : ℝ) / 2 ^ P) ^ j ≤ (g : ℝ) / 2 ^ P := by
      have h1 : (1 : ℝ) ≤ (g : ℝ) / 2 ^ P := by
        rw [le_div_iff₀ (by positivity), one_mul]
        have := h.1
        rw [pow2_eq] at this
        exact_mod_cast this
      simpa using h1
    simpa using gTabOk_spec he rest 0 g h.2 hg t (by simpa using ht)

/-! ### One point of a run -/

/-- The facts of the fibered bound at a mode `k` from the signed fixed-point data of its run:
`Λ ≤ s Z - Rd` and `s Z + Rd ≤ U ≤ 2^{q-1}` with `Z = X + p 2^q`, `s = ±1`. -/
theorem run_point {D : DBox2} {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω')
    (k : Fin 2 → ℤ) {p s Λ U : ℤ} (hs : s = 1 ∨ s = -1) (hΛ : 0 < Λ)
    (hF : Λ ≤ s * (k 0 * D.C0 + k 1 * D.C1 + p * 2 ^ D.q) -
      (((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 : ℕ) : ℤ))
    (hG : s * (k 0 * D.C0 + k 1 * D.C1 + p * 2 ^ D.q) +
      (((k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 : ℕ) : ℤ) ≤ U)
    (hU : 2 * U ≤ 2 ^ D.q) :
    |Diophantine.frequencyDot ω' k + p| ≤ 1 / 2 ∧
      (Λ : ℝ) / 2 ^ D.q ≤ |Diophantine.frequencyDot ω' k + p| := by
  set X : ℤ := k 0 * D.C0 + k 1 * D.C1 with hX
  set R : ℕ := (k 0).natAbs * D.R0 + (k 1).natAbs * D.R1 with hR
  set Z : ℤ := X + p * 2 ^ D.q with hZ
  set y : ℝ := Diophantine.frequencyDot ω' k with hy
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  have hd : |y - (X : ℝ) / 2 ^ D.q| ≤ (R : ℝ) / 2 ^ D.q := dot_sub_le_dbox hω k
  have hR0 : (0 : ℤ) ≤ R := Nat.cast_nonneg R
  have hsZ : 0 < s * Z := by linarith
  have habs : ((s * Z : ℤ) : ℝ) = |(Z : ℝ)| := by
    rcases hs with rfl | rfl
    · have : 0 < Z := by linarith
      rw [abs_of_pos (by exact_mod_cast this)]
      push_cast; ring
    · have : Z < 0 := by linarith
      rw [abs_of_neg (by exact_mod_cast this)]
      push_cast; ring
  have e1 : y + p = (Z : ℝ) / 2 ^ D.q + (y - (X : ℝ) / 2 ^ D.q) := by
    rw [hZ]
    push_cast
    field_simp
    ring
  have hZq : |(Z : ℝ) / 2 ^ D.q| = ((s * Z : ℤ) : ℝ) / 2 ^ D.q := by
    rw [abs_div, abs_of_pos hq, habs]
  have hup : |y + p| ≤ ((s * Z : ℤ) : ℝ) / 2 ^ D.q + (R : ℝ) / 2 ^ D.q := by
    rw [e1, ← hZq]
    exact (abs_add_le _ _).trans (by linarith)
  have hlo : ((s * Z : ℤ) : ℝ) / 2 ^ D.q - (R : ℝ) / 2 ^ D.q ≤ |y + p| := by
    have h1 : |(Z : ℝ) / 2 ^ D.q| ≤ |y + p| + |y - (X : ℝ) / 2 ^ D.q| := by
      have := abs_add_le (y + p) (-(y - (X : ℝ) / 2 ^ D.q))
      rw [abs_neg] at this
      calc |(Z : ℝ) / 2 ^ D.q| = |y + p + -(y - (X : ℝ) / 2 ^ D.q)| := by rw [e1]; ring_nf
        _ ≤ _ := this
    rw [hZq] at h1
    linarith
  have hF' : (Λ : ℝ) ≤ ((s * Z : ℤ) : ℝ) - R := by exact_mod_cast hF
  have hG' : ((s * Z : ℤ) : ℝ) + R ≤ U := by exact_mod_cast hG
  have hU' : 2 * (U : ℝ) ≤ 2 ^ D.q := by exact_mod_cast hU
  constructor
  · refine hup.trans ?_
    rw [← add_div, div_le_iff₀ hq]
    linarith
  · refine le_trans ?_ hlo
    rw [← sub_div]
    exact div_le_div_of_nonneg_right hF' hq.le

/-! ### The run check and its value -/

/-- `min` with a `Bool` test. -/
def minN (a b : ℕ) : ℕ := cond (Nat.ble a b) a b

/-- `max` with a `Bool` test. -/
def maxN (a b : ℕ) : ℕ := cond (Nat.ble a b) b a

theorem minN_eq (a b : ℕ) : minN a b = min a b := by
  simp only [minN, Bool.cond_eq_ite, Nat.ble_eq, min_def]

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  simp only [maxN, Bool.cond_eq_ite, Nat.ble_eq, max_def]

/-- Both integers are `≥ 0`, or both are `< 0`. -/
def sameSign : ℤ → ℤ → Bool
  | Int.ofNat _, Int.ofNat _ => true
  | Int.negSucc _, Int.negSucc _ => true
  | _, _ => false

theorem sameSign_spec {u w : ℤ} (h : sameSign u w = true) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ s * u = u.natAbs ∧ s * w = w.natAbs := by
  cases u <;> cases w <;> simp only [sameSign, reduceCtorEq] at h
  · exact ⟨1, Or.inl rfl, by simp, by simp⟩
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩ <;>
    · rw [Int.natAbs_negSucc, Int.negSucc_eq]; push_cast; ring

/-- `X = a C₀ + b C₁` at the column `b = sg (lo + i)`. -/
def colX (D : DBox2) (a sg : ℤ) (lo i : ℕ) : ℤ :=
  Int.add (Int.mul a D.C0) (Int.mul (Int.mul sg (Int.ofNat (Nat.add lo i))) D.C1)

/-- `Z = X + p 2^q` at the column `b = sg (lo + i)`. -/
def colZ (D : DBox2) (a sg p : ℤ) (lo i : ℕ) : ℤ :=
  Int.add (colX D a sg lo i) (Int.mul p (Int.ofNat (pow2 D.q)))

/-- `Rd = |a| R₀ + (lo + i) R₁` at the column `b = sg (lo + i)`. -/
def colR (D : DBox2) (a : ℤ) (lo i : ℕ) : ℕ :=
  Nat.add (Nat.mul (Int.natAbs a) D.R0) (Nat.mul (Nat.add lo i) D.R1)

theorem colZ_eq (D : DBox2) (a sg p : ℤ) (lo i : ℕ) :
    colZ D a sg p lo i = a * D.C0 + sg * ((lo + i : ℕ) : ℤ) * D.C1 + p * 2 ^ D.q := by
  simp only [colZ, colX, pow2_eq]
  push_cast
  rfl

theorem colR_eq (D : DBox2) (a : ℤ) (lo i : ℕ) :
    colR D a lo i = a.natAbs * D.R0 + (lo + i) * D.R1 := rfl

/-- **The value of a run** (times `2^P`): the `mode3` term with the weights `x^{j₀} G/2^P` and
`x^{j₀ + |p|} G/2^P` (`G ≥ 2^P Σ_{j<2^t} x^j`) and the lower bound `Λ/2^q`. -/
def blkValK (D : DBox2) (e P j0 g Λ : ℕ) (p : ℤ) : ℕ :=
  let pa : ℕ := Int.natAbs p
  let Ws : ℕ := mulUpK P (powUpK e P 64 j0) g
  let Wp : ℕ := mulUpK P (powUpK e P 64 (Nat.add j0 pa)) g
  Nat.add (Nat.add
    (ceilDiv (Nat.mul Wp (pow2 (Nat.mul 2 D.q))) (Nat.mul Λ Λ))
    (cond (Nat.beq pa 0) 0
      (ceilDiv (Nat.mul Ws 4) (Nat.mul (Nat.sub (Nat.mul 2 pa) 1) (Nat.sub (Nat.mul 2 pa) 1)))))
    (ceilDiv (Nat.mul (Nat.mul Ws (powUpK e P 64 1)) 14615) (Nat.mul (pow2 P) 2000))

/-- **The run check** of `b = sg (lo + i)`, `i₀ ≤ i ≤ i₁`: `p = nearP(X(i₀))`; `Z(i₀)` and
`Z(i₁)` of one sign, `Rd < |Z|` and `2(|Z| + Rd) ≤ 2^q` at both ends; then the value of the run
with `Λ = min(|Z| - Rd)`, if the acceptance test `acc Λ (max(|Z| + Rd)) v` passes. -/
def blkK (D : DBox2) (e P g : ℕ) (acc : ℕ → ℕ → ℕ → Bool) (a sg : ℤ) (lo i0 i1 : ℕ) :
    Option ℕ :=
  let p : ℤ := nearP D.q (colX D a sg lo i0)
  let Z0 : ℤ := colZ D a sg p lo i0
  let Z1 : ℤ := colZ D a sg p lo i1
  let Y0 : ℕ := Int.natAbs Z0
  let Y1 : ℕ := Int.natAbs Z1
  let R0 : ℕ := colR D a lo i0
  let R1 : ℕ := colR D a lo i1
  cond (sameSign Z0 Z1 && Nat.blt R0 Y0 && Nat.blt R1 Y1 &&
      Nat.ble (Nat.mul 2 (Nat.add Y0 R0)) (pow2 D.q) &&
      Nat.ble (Nat.mul 2 (Nat.add Y1 R1)) (pow2 D.q))
    (let Λ : ℕ := minN (Nat.sub Y0 R0) (Nat.sub Y1 R1)
     let v : ℕ := blkValK D e P (Nat.add (Nat.add (Int.natAbs a) lo) i0) g Λ p
     cond (acc Λ (maxN (Nat.add Y0 R0) (Nat.add Y1 R1)) v) (some v) none)
    none

/-- The modes `(a, sg (lo + i₀ + j))`, `j < n`, of a run. -/
def runSet (a sg : ℤ) (lo i0 n : ℕ) : Finset (Fin 2 → ℤ) :=
  (Finset.range n).image fun j => ![a, sg * ((lo + i0 + j : ℕ) : ℤ)]

section Run

variable {D : DBox2} {e P : ℕ}

theorem blkValK_ge {x A B : ℝ} {j0 g Λ : ℕ} {p : ℤ} (hΛ : 0 < Λ)
    (hx1 : x ≤ (powUp e P 64 1 : ℝ) / 2 ^ P)
    (hA : A ≤ (powUp e P 64 (j0 + p.natAbs) : ℝ) / 2 ^ P * ((g : ℝ) / 2 ^ P))
    (hB0 : 0 ≤ B) (hB : B ≤ (powUp e P 64 j0 : ℝ) / 2 ^ P * ((g : ℝ) / 2 ^ P)) :
    A * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
      B * ((if p = 0 then 0 else ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹)) + x * fiberConst) ≤
      (blkValK D e P j0 g Λ p : ℝ) / 2 ^ P := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  set Wp : ℕ := mulUp P (powUp e P 64 (j0 + p.natAbs)) g with hWp
  set Ws : ℕ := mulUp P (powUp e P 64 j0) g with hWs
  have hA' : A ≤ (Wp : ℝ) / 2 ^ P := hA.trans (mulUp_ge P _ _)
  have hB' : B ≤ (Ws : ℝ) / 2 ^ P := hB.trans (mulUp_ge P _ _)
  have hval : (blkValK D e P j0 g Λ p : ℝ) / 2 ^ P =
      (ceilDiv (Wp * 2 ^ (2 * D.q)) (Λ * Λ) : ℝ) / 2 ^ P +
      ((if p = 0 then 0 else ceilDiv (Ws * 4) ((2 * p.natAbs - 1) * (2 * p.natAbs - 1)) : ℕ) :
        ℝ) / 2 ^ P +
      (ceilDiv (Ws * powUp e P 64 1 * 14615) (2 ^ P * 2000) : ℝ) / 2 ^ P := by
    rw [← add_div, ← add_div]
    congr 1
    simp only [blkValK, powUpK_eq, mulUpK_eq, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, pow2_eq,
      Bool.cond_eq_ite, Nat.beq_eq, Int.natAbs_eq_zero, ← hWp, ← hWs]
    push_cast
    rfl
  rw [hval, mul_add, ← add_assoc]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the nearest term
    have hc := div_le_ceilDiv (Wp * 2 ^ (2 * D.q)) (Nat.mul_pos hΛ hΛ)
    refine le_trans ?_ (div_le_div_of_nonneg_right hc hP.le)
    have hL : ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ = (2 : ℝ) ^ (2 * D.q) / ((Λ : ℝ) * Λ) := by
      rw [div_pow, inv_div, pow_mul']
      ring
    rw [hL]
    calc A * ((2 : ℝ) ^ (2 * D.q) / ((Λ : ℝ) * Λ))
        ≤ (Wp : ℝ) / 2 ^ P * ((2 : ℝ) ^ (2 * D.q) / ((Λ : ℝ) * Λ)) :=
          mul_le_mul_of_nonneg_right hA' (by positivity)
      _ = ((Wp * 2 ^ (2 * D.q) : ℕ) : ℝ) / ((Λ * Λ : ℕ) : ℝ) / 2 ^ P := by
          push_cast; ring
  · -- the term `j = 0`
    split_ifs with hp0
    · simp
    · have hp1 : 1 ≤ p.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp0)
      have hpos : 0 < (2 * p.natAbs - 1) * (2 * p.natAbs - 1) := Nat.mul_pos (by omega) (by omega)
      have hc := div_le_ceilDiv (Ws * 4) hpos
      refine le_trans ?_ (div_le_div_of_nonneg_right hc hP.le)
      have h2p : (2 * (p.natAbs : ℝ) - 1) ≠ 0 := by
        have : (1 : ℝ) ≤ p.natAbs := by exact_mod_cast hp1
        linarith
      have e1 : ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹) = 4 / ((2 * (p.natAbs : ℝ) - 1) ^ 2) := by
        field_simp
        ring
      rw [e1]
      calc B * (4 / ((2 * (p.natAbs : ℝ) - 1) ^ 2))
          ≤ (Ws : ℝ) / 2 ^ P * (4 / ((2 * (p.natAbs : ℝ) - 1) ^ 2)) :=
            mul_le_mul_of_nonneg_right hB' (by positivity)
        _ = (((Ws * 4 : ℕ) : ℝ) / (((2 * p.natAbs - 1) * (2 * p.natAbs - 1) : ℕ) : ℝ)) /
              2 ^ P := by
            have hc2 : (((2 * p.natAbs - 1) * (2 * p.natAbs - 1) : ℕ) : ℝ) =
                (2 * (p.natAbs : ℝ) - 1) ^ 2 := by
              rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
            rw [hc2]
            push_cast
            field_simp
  · -- the background `E₁ C₀`
    have hc := div_le_ceilDiv (Ws * powUp e P 64 1 * 14615) (by positivity : 0 < 2 ^ P * 2000)
    refine le_trans ?_ (div_le_div_of_nonneg_right hc hP.le)
    have hC : fiberConst ≤ 14615 / 2000 := by
      unfold fiberConst
      have := Real.pi_pos
      have := Real.pi_lt_d2
      nlinarith
    have hx0 : 0 ≤ x * fiberConst ∨ True := Or.inr trivial
    clear hx0
    calc B * (x * fiberConst)
        ≤ (Ws : ℝ) / 2 ^ P * ((powUp e P 64 1 : ℝ) / 2 ^ P * (14615 / 2000)) := by
          by_cases hxs : 0 ≤ x
          · exact mul_le_mul hB' (mul_le_mul hx1 hC fiberConst_nonneg (by positivity))
              (mul_nonneg hxs fiberConst_nonneg) (by positivity)
          · have : x * fiberConst ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (by linarith) fiberConst_nonneg
            calc B * (x * fiberConst) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB0 this
              _ ≤ _ := by positivity
      _ = ((Ws * powUp e P 64 1 * 14615 : ℕ) : ℝ) / ((2 ^ P * 2000 : ℕ) : ℝ) / 2 ^ P := by
          push_cast; field_simp

/-- An affine function on `[i₀, i₁]` lies above its smaller endpoint value. -/
theorem affine_ge_min {c d : ℤ} {i0 i1 i : ℕ} (h0 : i0 ≤ i) (h1 : i ≤ i1) :
    min (c + d * i0) (c + d * i1) ≤ c + d * i := by
  have h0' : (i0 : ℤ) ≤ i := by exact_mod_cast h0
  have h1' : (i : ℤ) ≤ i1 := by exact_mod_cast h1
  rcases le_total 0 d with hd | hd
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- An affine function on `[i₀, i₁]` lies below its larger endpoint value. -/
theorem affine_le_max {c d : ℤ} {i0 i1 i : ℕ} (h0 : i0 ≤ i) (h1 : i ≤ i1) :
    c + d * i ≤ max (c + d * i0) (c + d * i1) := by
  have h0' : (i0 : ℤ) ≤ i := by exact_mod_cast h0
  have h1' : (i : ℤ) ≤ i1 := by exact_mod_cast h1
  rcases le_total 0 d with hd | hd
  · exact (by nlinarith : c + d * i ≤ c + d * i1).trans (le_max_right _ _)
  · exact (by nlinarith : c + d * i ≤ c + d * i0).trans (le_max_left _ _)

theorem natAbs_sg_mul {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) (n : ℕ) : (sg * (n : ℤ)).natAbs = n := by
  rcases hsg with rfl | rfl <;> simp

/-- **Soundness of the run check**: the run's modes are covered at its value. -/
theorem blkK_spec {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P)
    {t g : ℕ} (hg : ∑ j ∈ Finset.range (2 ^ t), ((e : ℝ) / 2 ^ P) ^ j ≤ (g : ℝ) / 2 ^ P)
    {acc : ℕ → ℕ → ℕ → Bool} {a sg : ℤ} {lo i0 i1 v : ℕ} (hsg : sg = 1 ∨ sg = -1)
    (hi : i0 ≤ i1) (hlen : i1 < i0 + 2 ^ t) (h : blkK D e P g acc a sg lo i0 i1 = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 (i1 - i0 + 1)) ((v : ℝ) / 2 ^ P) := by
  unfold blkK at h
  set p : ℤ := nearP D.q (colX D a sg lo i0) with hp
  simp only [Bool.cond_eq_ite, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq,
    Nat.sub_eq, pow2_eq] at h
  split at h
  case isFalse => exact absurd h (by simp)
  rename_i hc
  obtain ⟨⟨⟨⟨hsame, hlt0⟩, hlt1⟩, hup0⟩, hup1⟩ := hc
  split at h
  case isFalse => exact absurd h (by simp)
  simp only [Option.some.injEq] at h
  subst h
  rw [minN_eq]
  obtain ⟨s, hs, hs0, hs1⟩ := sameSign_spec hsame
  -- the affine functions `F = s Z - Rd`, `G = s Z + Rd` along the run
  set cZ : ℤ := a * D.C0 + sg * (lo : ℤ) * D.C1 + p * 2 ^ D.q with hcZ
  set dZ : ℤ := sg * D.C1 with hdZ
  have hZi : ∀ i : ℕ, colZ D a sg p lo i = cZ + dZ * i := fun i => by
    rw [colZ_eq]; push_cast; ring
  have hRi : ∀ i : ℕ, (colR D a lo i : ℤ) = ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + D.R1 * i :=
    fun i => by rw [colR_eq]; push_cast; ring
  generalize hZ0 : colZ D a sg p lo i0 = Z0 at *
  generalize hZ1 : colZ D a sg p lo i1 = Z1 at *
  generalize hR0 : colR D a lo i0 = R0 at *
  generalize hR1 : colR D a lo i1 = R1 at *
  set Λ : ℕ := min (Z0.natAbs - R0) (Z1.natAbs - R1) with hΛ
  have hΛ0 : 0 < Λ := lt_min (by omega) (by omega)
  set x : ℝ := (e : ℝ) / 2 ^ P with hx
  have hx0 : 0 ≤ x := by positivity
  have hF : ∀ i, i0 ≤ i → i ≤ i1 →
      (Λ : ℤ) ≤ s * colZ D a sg p lo i - (colR D a lo i : ℤ) := fun i h0 h1 => by
    have key := affine_ge_min (c := s * cZ - ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ))
      (d := s * dZ - D.R1) h0 h1
    have e0 : s * cZ - ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ - D.R1) * i0 =
        (Z0.natAbs : ℤ) - R0 := by
      rw [← hs0, ← hZ0, ← hR0, hZi, hRi]; ring
    have e1 : s * cZ - ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ - D.R1) * i1 =
        (Z1.natAbs : ℤ) - R1 := by
      rw [← hs1, ← hZ1, ← hR1, hZi, hRi]; ring
    rw [e0, e1] at key
    have hm : (Λ : ℤ) = min ((Z0.natAbs : ℤ) - R0) ((Z1.natAbs : ℤ) - R1) := by
      rw [hΛ, Nat.cast_min, Nat.cast_sub hlt0.le, Nat.cast_sub hlt1.le]
    rw [hm, hZi, hRi]
    linarith
  set U : ℕ := max (Z0.natAbs + R0) (Z1.natAbs + R1) with hU
  have hG : ∀ i, i0 ≤ i → i ≤ i1 →
      s * colZ D a sg p lo i + (colR D a lo i : ℤ) ≤ (U : ℤ) := fun i h0 h1 => by
    have key := affine_le_max (c := s * cZ + ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ))
      (d := s * dZ + D.R1) h0 h1
    have e0 : s * cZ + ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ + D.R1) * i0 =
        (Z0.natAbs : ℤ) + R0 := by
      rw [← hs0, ← hZ0, ← hR0, hZi, hRi]; ring
    have e1 : s * cZ + ((a.natAbs * D.R0 + lo * D.R1 : ℕ) : ℤ) + (s * dZ + D.R1) * i1 =
        (Z1.natAbs : ℤ) + R1 := by
      rw [← hs1, ← hZ1, ← hR1, hZi, hRi]; ring
    rw [e0, e1] at key
    rw [hU, Nat.cast_max, hZi, hRi]
    push_cast at key ⊢
    linarith
  have hU2 : 2 * (U : ℤ) ≤ 2 ^ D.q := by
    have : 2 * U ≤ 2 ^ D.q := by
      rw [hU]
      rcases le_total (Z0.natAbs + R0) (Z1.natAbs + R1) with h | h
      · rw [max_eq_right h]; exact hup1
      · rw [max_eq_left h]; exact hup0
    exact_mod_cast this
  -- the facts at each mode of the run
  have hmode : ∀ j < i1 - i0 + 1,
      |Diophantine.frequencyDot ω' ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] + p| ≤ 1 / 2 ∧
      (Λ : ℝ) / 2 ^ D.q ≤
        |Diophantine.frequencyDot ω' ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] + p| := fun j hj => by
    have h0 : i0 ≤ i0 + j := Nat.le_add_right _ _
    have h1 : i0 + j ≤ i1 := by omega
    refine run_point hω _ hs (by exact_mod_cast hΛ0) ?_ ?_ hU2
    · have := hF (i0 + j) h0 h1
      rw [colZ_eq, colR_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      exact this
    · have := hG (i0 + j) h0 h1
      rw [colZ_eq, colR_eq] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        natAbs_sg_mul hsg]
      rw [show lo + i0 + j = lo + (i0 + j) by omega]
      exact this
  -- the cover
  have hq : (0 : ℝ) < 2 ^ D.q := by positivity
  have hinj : Set.InjOn (fun j : ℕ => (![a, sg * ((lo + i0 + j : ℕ) : ℤ)] : Fin 2 → ℤ))
      (Finset.range (i1 - i0 + 1) : Set ℕ) := fun j _ j' _ hjj => by
    have h1 := congrFun hjj 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
    have hsg0 : sg ≠ 0 := by rcases hsg with rfl | rfl <;> norm_num
    have := mul_left_cancel₀ hsg0 h1
    omega
  refine ⟨fun _ => p, fun _ => (Λ : ℝ) / 2 ^ D.q, fun k hk => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨h1, h2⟩ := hmode j (Finset.mem_range.mp hj)
    exact ⟨h1, by positivity, h2⟩
  · rw [runSet, Finset.sum_image hinj]
    set j0 : ℕ := a.natAbs + lo + i0 with hj0
    set cP : ℝ := (if p = 0 then 0 else ((((p.natAbs : ℝ) - 1 / 2) ^ 2)⁻¹)) with hcP
    set Gs : ℝ := ∑ j ∈ Finset.range (i1 - i0 + 1), x ^ j with hGs
    have hterm : ∀ j ∈ Finset.range (i1 - i0 + 1),
        termX x ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] p ((Λ : ℝ) / 2 ^ D.q) =
          x ^ j * (x ^ (j0 + p.natAbs) * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
            x ^ j0 * (cP + x * fiberConst)) := fun j _ => by
      have hm : modeNat (![a, sg * ((lo + i0 + j : ℕ) : ℤ)] : Fin 2 → ℤ) = j0 + j := by
        rw [modeNat_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          natAbs_sg_mul hsg]
        omega
      rw [termX, hm, pow_one]
      rw [show j0 + j + p.natAbs = j + (j0 + p.natAbs) by omega, pow_add, pow_add]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    have hGs : Gs ≤ (g : ℝ) / 2 ^ P := by
      refine le_trans ?_ hg
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr (by omega : i1 - i0 + 1 ≤ 2 ^ t))
        fun j _ _ => pow_nonneg hx0 j
    have hGs0 : 0 ≤ Gs := Finset.sum_nonneg fun j _ => pow_nonneg hx0 j
    have hpw : ∀ m : ℕ, x ^ m ≤ (powUp e P 64 m : ℝ) / 2 ^ P := fun m => powUp_ge he 64 m
    have hx1 : x ≤ (powUp e P 64 1 : ℝ) / 2 ^ P := by simpa using hpw 1
    have key := blkValK_ge (D := D) (x := x) (A := Gs * x ^ (j0 + p.natAbs))
      (B := Gs * x ^ j0) (j0 := j0) (g := g) (p := p) hΛ0 hx1
      (by rw [mul_comm]; exact mul_le_mul (hpw _) hGs hGs0 (by positivity))
      (by positivity)
      (by rw [mul_comm]; exact mul_le_mul (hpw _) hGs hGs0 (by positivity))
    have e1 : Gs * (x ^ (j0 + p.natAbs) * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
        x ^ j0 * (cP + x * fiberConst)) =
        Gs * x ^ (j0 + p.natAbs) * ((((Λ : ℝ) / 2 ^ D.q)) ^ 2)⁻¹ +
          Gs * x ^ j0 * (cP + x * fiberConst) := by ring
    rw [e1]
    exact key

end Run

/-! ### Half-rows, rows and the walk -/

/-- The acceptance test of a run: `rd · max G ≤ rn · Λ`, or a value at most `tol`. -/
def accOk (rn rd tol Λ Gm v : ℕ) : Bool :=
  Nat.ble (Nat.mul rd Gm) (Nat.mul rn Λ) || Nat.ble v tol

/-- **A half-row** `b = sg (lo + i)`, `i₀ ≤ i < i₀ + 2^t`, `lo + i ≤ M`, by bisection: a node is
one run if `blkK` accepts it, otherwise its two halves; a single fibre must pass. -/
def hrow (D : DBox2) (e P : ℕ) (G : ℕ → ℕ) (rn rd tol : ℕ) (a sg : ℤ) (lo M : ℕ) :
    ℕ → ℕ → Option ℕ
  | 0, i0 => cond (Nat.blt M (Nat.add lo i0)) (some 0)
      (blkK D e P (G 0) (fun _ _ _ => true) a sg lo i0 i0)
  | t + 1, i0 => cond (Nat.blt M (Nat.add lo i0)) (some 0)
      (match blkK D e P (G (t + 1)) (accOk rn rd tol) a sg lo i0
          (minN (Nat.add i0 (Nat.sub (pow2 (t + 1)) 1)) (Nat.sub M lo)) with
        | some v => some v
        | none =>
          match hrow D e P G rn rd tol a sg lo M t i0 with
          | none => none
          | some u =>
            match hrow D e P G rn rd tol a sg lo M t (Nat.add i0 (pow2 t)) with
            | none => none
            | some w => some (Nat.add u w))

/-- The first `|b|` of the half-row `b ≥ 0`: `1` at `a = 0` (the mode `0` is not a fibre). -/
def loP (a : ℤ) : ℕ := cond (Nat.beq (Int.natAbs a) 0) 1 0

/-- **A row** `a`: the half-rows `b ≥ loP a` and `b ≤ -1`; `0` if `|a| > N`. -/
def rowB (D : DBox2) (e P : ℕ) (G : ℕ → ℕ) (rn rd tol N l : ℕ) (a : ℤ) : Option ℕ :=
  cond (Nat.blt N (Int.natAbs a)) (some 0)
    (match hrow D e P G rn rd tol a 1 (loP a) (Nat.sub N (Int.natAbs a)) l 0 with
      | none => none
      | some u =>
        match hrow D e P G rn rd tol a (-1) 1 (Nat.sub N (Int.natAbs a)) l 0 with
        | none => none
        | some w => some (Nat.add u w))

/-- **The bulk walk** over the fibres `0 < |a| + |b| ≤ N`: rows `a = i - N`, `i < 2^l`. -/
def walkB (D : DBox2) (e P : ℕ) (G : ℕ → ℕ) (rn rd tol N l : ℕ) : Option ℕ :=
  balFold (fun i => rowB D e P G rn rd tol N l (rowA N i)) l 0

/-- The modes of a half-row node. -/
def hrSet (a sg : ℤ) (lo M i0 t : ℕ) : Finset (Fin 2 → ℤ) :=
  ((Finset.range (2 ^ t)).filter fun j => lo + i0 + j ≤ M).image
    fun j => ![a, sg * ((lo + i0 + j : ℕ) : ℤ)]

/-- The modes of a row. -/
def rowSet (N l : ℕ) (a : ℤ) : Finset (Fin 2 → ℤ) :=
  if N < a.natAbs then ∅ else
    hrSet a 1 (loP a) (N - a.natAbs) 0 l ∪ hrSet a (-1) 1 (N - a.natAbs) 0 l

theorem mem_hrSet {a sg : ℤ} {lo M i0 t : ℕ} {k : Fin 2 → ℤ} :
    k ∈ hrSet a sg lo M i0 t ↔
      ∃ j < 2 ^ t, lo + i0 + j ≤ M ∧ k = ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] := by
  simp only [hrSet, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨j, ⟨hj, hjM⟩, rfl⟩
    exact ⟨j, hj, hjM, rfl⟩
  · rintro ⟨j, hj, hjM, rfl⟩
    exact ⟨j, ⟨hj, hjM⟩, rfl⟩

theorem mem_runSet {a sg : ℤ} {lo i0 n : ℕ} {k : Fin 2 → ℤ} :
    k ∈ runSet a sg lo i0 n ↔ ∃ j < n, k = ![a, sg * ((lo + i0 + j : ℕ) : ℤ)] := by
  simp only [runSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem vec_one_inj {a a' sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {n n' : ℕ}
    (h : (![a, sg * (n : ℤ)] : Fin 2 → ℤ) = ![a', sg * (n' : ℤ)]) : a = a' ∧ n = n' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h0 h1
  refine ⟨h0, ?_⟩
  rcases hsg with rfl | rfl <;> omega

theorem hrSet_succ {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) (lo M i0 t : ℕ) :
    hrSet a sg lo M i0 (t + 1) = hrSet a sg lo M i0 t ∪ hrSet a sg lo M (i0 + 2 ^ t) t ∧
      Disjoint (hrSet a sg lo M i0 t) (hrSet a sg lo M (i0 + 2 ^ t) t) := by
  constructor
  · ext k
    simp only [Finset.mem_union, mem_hrSet]
    constructor
    · rintro ⟨j, hj, hjM, rfl⟩
      by_cases hjt : j < 2 ^ t
      · exact Or.inl ⟨j, hjt, hjM, rfl⟩
      · refine Or.inr ⟨j - 2 ^ t, by rw [pow_succ] at hj; omega, by omega, ?_⟩
        rw [show lo + (i0 + 2 ^ t) + (j - 2 ^ t) = lo + i0 + j by omega]
    · rintro (⟨j, hj, hjM, rfl⟩ | ⟨j, hj, hjM, rfl⟩)
      · exact ⟨j, by rw [pow_succ]; omega, hjM, rfl⟩
      · refine ⟨2 ^ t + j, by rw [pow_succ]; omega, by omega, ?_⟩
        rw [show lo + i0 + (2 ^ t + j) = lo + (i0 + 2 ^ t) + j by omega]
  · rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨j, hj, -, rfl⟩ := mem_hrSet.mp hk
    obtain ⟨j', -, -, h⟩ := mem_hrSet.mp hk'
    have := (vec_one_inj hsg h).2
    omega

section Walk

variable {D : DBox2} {e P : ℕ} {G : ℕ → ℕ} {rn rd tol : ℕ}

/-- **Soundness of a half-row.** -/
theorem hrow_spec {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P)
    {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {lo M : ℕ} :
    ∀ t : ℕ, (∀ t' ≤ t, ∑ j ∈ Finset.range (2 ^ t'), ((e : ℝ) / 2 ^ P) ^ j ≤
        (G t' : ℝ) / 2 ^ P) →
      ∀ i0 v : ℕ, hrow D e P G rn rd tol a sg lo M t i0 = some v →
        BCov ω' ((e : ℝ) / 2 ^ P) (hrSet a sg lo M i0 t) ((v : ℝ) / 2 ^ P) := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hempty : ∀ i0 t, M < lo + i0 → hrSet a sg lo M i0 t = ∅ := fun i0 t hM => by
    ext k
    simp only [mem_hrSet, Finset.notMem_empty, iff_false]
    rintro ⟨j, -, hjM, -⟩
    omega
  intro t
  induction t with
  | zero =>
    intro hG i0 v h
    simp only [hrow, Bool.cond_eq_ite, Nat.blt_eq, Nat.add_eq] at h
    split_ifs at h with hM
    · simp only [Option.some.injEq] at h
      subst h
      rw [hempty i0 0 hM]
      exact BCov.empty (by simp)
    · have hset : hrSet a sg lo M i0 0 = runSet a sg lo i0 (i0 - i0 + 1) := by
        ext k
        simp only [mem_hrSet, mem_runSet, pow_zero]
        constructor
        · rintro ⟨j, hj, -, rfl⟩
          exact ⟨j, by omega, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          exact ⟨j, by omega, by omega, rfl⟩
      rw [hset]
      exact blkK_spec hω he (hG 0 le_rfl) hsg le_rfl (by simp) h
  | succ t ih =>
    intro hG i0 v h
    simp only [hrow, Bool.cond_eq_ite, Nat.blt_eq, Nat.add_eq, Nat.sub_eq, pow2_eq,
      minN_eq] at h
    split_ifs at h with hM
    · simp only [Option.some.injEq] at h
      subst h
      rw [hempty i0 (t + 1) hM]
      exact BCov.empty (by simp)
    · have h2 : 1 ≤ 2 ^ (t + 1) := Nat.one_le_two_pow
      split at h
      · rename_i v' hv'
        simp only [Option.some.injEq] at h
        subst h
        set i1 := min (i0 + (2 ^ (t + 1) - 1)) (M - lo) with hi1
        have hset : hrSet a sg lo M i0 (t + 1) = runSet a sg lo i0 (i1 - i0 + 1) := by
          ext k
          simp only [mem_hrSet, mem_runSet]
          constructor
          · rintro ⟨j, hj, hjM, rfl⟩
            exact ⟨j, by omega, rfl⟩
          · rintro ⟨j, hj, rfl⟩
            exact ⟨j, by omega, by omega, rfl⟩
        rw [hset]
        exact blkK_spec hω he (hG (t + 1) le_rfl) hsg (by omega) (by omega) hv'
      · split at h
        · simp at h
        rename_i u hu
        split at h
        · simp at h
        rename_i w hw
        simp only [Option.some.injEq] at h
        subst h
        have hG' : ∀ t' ≤ t, ∑ j ∈ Finset.range (2 ^ t'), ((e : ℝ) / 2 ^ P) ^ j ≤
            (G t' : ℝ) / 2 ^ P := fun t' ht' => hG t' (by omega)
        obtain ⟨hU, hD⟩ := hrSet_succ hsg lo M i0 t
        rw [hU]
        have := BCov.union hD (ih hG' i0 u hu) (ih hG' (i0 + 2 ^ t) w hw)
        refine this.mono (le_of_eq ?_)
        push_cast
        rw [add_div]

theorem loP_eq (a : ℤ) : loP a = if a = 0 then 1 else 0 := by
  simp only [loP, Bool.cond_eq_ite, Nat.beq_eq, Int.natAbs_eq_zero]

/-- **Soundness of a row.** -/
theorem rowB_spec {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P)
    {N l : ℕ} (hG : ∀ t ≤ l, ∑ j ∈ Finset.range (2 ^ t), ((e : ℝ) / 2 ^ P) ^ j ≤
      (G t : ℝ) / 2 ^ P) {a : ℤ} {v : ℕ} (h : rowB D e P G rn rd tol N l a = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (rowSet N l a) ((v : ℝ) / 2 ^ P) := by
  simp only [rowB, Bool.cond_eq_ite, Nat.blt_eq, Nat.sub_eq, Nat.add_eq] at h
  unfold rowSet
  by_cases hN : N < a.natAbs
  · simp only [hN, ↓reduceIte, Option.some.injEq] at h ⊢
    subst h
    exact BCov.empty (by simp)
  · simp only [hN, ↓reduceIte] at h ⊢
    split at h
    · simp at h
    rename_i u hu
    split at h
    · simp at h
    rename_i w hw
    simp only [Option.some.injEq] at h
    subst h
    have hD : Disjoint (hrSet a 1 (loP a) (N - a.natAbs) 0 l)
        (hrSet a (-1) 1 (N - a.natAbs) 0 l) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      obtain ⟨j, -, -, rfl⟩ := mem_hrSet.mp hk
      obtain ⟨j', -, -, h⟩ := mem_hrSet.mp hk'
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
      omega
    have := BCov.union hD (hrow_spec hω he (Or.inl rfl) l hG 0 u hu)
      (hrow_spec hω he (Or.inr rfl) l hG 0 w hw)
    refine this.mono (le_of_eq ?_)
    push_cast
    rw [add_div]

theorem mem_rowSet {N l : ℕ} {a : ℤ} {k : Fin 2 → ℤ} (hk : k ∈ rowSet N l a) : k 0 = a := by
  unfold rowSet at hk
  split_ifs at hk
  · simp at hk
  rcases Finset.mem_union.mp hk with hk | hk <;>
  · obtain ⟨j, -, -, rfl⟩ := mem_hrSet.mp hk
    simp

theorem mem_rowSet_of_mem_modeBox {N l : ℕ} (hl : 2 * N + 1 ≤ 2 ^ l) {k : Fin 2 → ℤ}
    (hk : k ∈ modeBox 2 N) : k ∈ rowSet N l (k 0) := by
  obtain ⟨hk0, hkN⟩ := mem_modeBox.mp hk
  rw [modeNat_two] at hkN
  have hvec : k = ![k 0, k 1] := by
    funext i
    fin_cases i <;> rfl
  unfold rowSet
  have hN : ¬ N < (k 0).natAbs := by omega
  simp only [hN, ↓reduceIte]
  rw [Finset.mem_union, mem_hrSet, mem_hrSet]
  rcases le_or_gt 0 (k 1) with hb | hb
  · left
    rw [loP_eq]
    by_cases ha : k 0 = 0
    · have hb1 : k 1 ≠ 0 := fun hb0 => hk0 (by rw [hvec, ha, hb0]; funext i; fin_cases i <;> rfl)
      simp only [ha, ↓reduceIte]
      refine ⟨(k 1).toNat - 1, by omega, by omega, ?_⟩
      conv_lhs => rw [hvec]
      congr 2
      omega
    · simp only [ha, ↓reduceIte]
      refine ⟨(k 1).toNat, by omega, by omega, ?_⟩
      conv_lhs => rw [hvec]
      congr 2
      omega
  · right
    refine ⟨(-(k 1)).toNat - 1, by omega, by omega, ?_⟩
    conv_lhs => rw [hvec]
    congr 2
    omega

/-- **Soundness of the bulk walk**: a cover of `modeBox 2 N` at `s/2^P`. -/
theorem walkB_sound {ω' : Fin 2 → ℝ} (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P)
    {N l s : ℕ} (hl : 2 * N + 1 ≤ 2 ^ l)
    (hG : ∀ t ≤ l, ∑ j ∈ Finset.range (2 ^ t), ((e : ℝ) / 2 ^ P) ^ j ≤ (G t : ℝ) / 2 ^ P)
    (h : walkB D e P G rn rd tol N l = some s) :
    BCov ω' ((e : ℝ) / 2 ^ P) (modeBox 2 N) ((s : ℝ) / 2 ^ P) := by
  obtain ⟨hrows, hs⟩ := balFold_eq_some h
  simp only [zero_add] at hrows hs
  have hx0 : (0 : ℝ) ≤ (e : ℝ) / 2 ^ P := by positivity
  set S : ℕ → Finset (Fin 2 → ℤ) := fun i => rowSet N l (rowA N i) with hS
  set v : ℕ → ℝ := fun i =>
    (((rowB D e P G rn rd tol N l (rowA N i)).getD 0 : ℕ) : ℝ) / 2 ^ P with hv
  have hcov : BCov ω' ((e : ℝ) / 2 ^ P) ((Finset.range (2 ^ l)).biUnion S)
      (∑ i ∈ Finset.range (2 ^ l), v i) := by
    refine BCov.biUnion (fun i _ j _ hij => ?_) fun i hi => ?_
    · rw [Function.onFun, Finset.disjoint_left]
      intro k hki hkj
      have h1 := mem_rowSet hki
      have h2 := mem_rowSet hkj
      apply hij
      have : rowA N i = rowA N j := h1.symm.trans h2
      unfold rowA at this
      omega
    · obtain ⟨u, hu⟩ := hrows i (Finset.mem_range.mp hi)
      have := rowB_spec hω he hG hu
      simp only [hv, hu, Option.getD_some]
      exact this
  have hsum : ∑ i ∈ Finset.range (2 ^ l), v i = (s : ℝ) / 2 ^ P := by
    rw [hs, Nat.cast_sum, Finset.sum_div]
  rw [hsum] at hcov
  refine BCov.subset hx0 (fun k hk => ?_) hcov
  rw [Finset.mem_biUnion]
  have ha : rowA N (k 0 + N).toNat = k 0 := by
    have := (mem_modeBox.mp hk).2
    rw [modeNat_two] at this
    unfold rowA
    omega
  refine ⟨(k 0 + N).toNat, ?_, ?_⟩
  · have := (mem_modeBox.mp hk).2
    rw [modeNat_two] at this
    rw [Finset.mem_range]
    omega
  · simp only [hS, ha]
    exact mem_rowSet_of_mem_modeBox hl hk

end Walk

/-- **The bound of `S((ω', 1), δ)` from the bulk walk**, `ω' ∈ ℝ²`, at the exponent `τ`: the
same form as `smallDivisorSum_snoc2_le_walk`. -/
theorem smallDivisorSum_snoc2_le_bulk {D : DBox2} {e P N l s J τ rn rd tol : ℕ} {G : ℕ → ℕ}
    {γ δ : ℚ} (he : e ≤ 2 ^ P) (hE : (2 : ℚ) ^ P ≤ e * expLowQ δ J) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : 0 < cLoQ δ τ N) (hl : 2 * N + 1 ≤ 2 ^ l)
    (hG : ∀ t ≤ l, ∑ j ∈ Finset.range (2 ^ t), ((e : ℝ) / 2 ^ P) ^ j ≤ (G t : ℝ) / 2 ^ P)
    (hs : walkB D e P G rn rd tol N l = some s) {ω' : Fin 2 → ℝ}
    (hω : FreqEncloses 2 D.toBox ω')
    (hdio : IsDiophantine (γ : ℝ) τ (Fin.snoc ω' 1 : Fin 3 → ℝ)) :
    smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (δ : ℝ) ≤
      (((powUp e P 64 1 : ℚ) / 2 ^ P * (99225 / 30000) + (s : ℚ) / 2 ^ P +
        tailQ γ δ τ N ((powUp e P 64 (N + 1) : ℚ) / 2 ^ P) : ℚ) : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hPq : (0 : ℚ) < 2 ^ P := by positivity
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  set x : ℝ := (e : ℝ) / 2 ^ P with hxdef
  have hx0 : 0 ≤ x := by positivity
  -- the weights
  have hx : Real.exp (-(2 * Real.pi * δ)) ≤ x := by
    have h1 : (1 : ℚ) ≤ ((e : ℚ) / 2 ^ P) * expLowQ δ J := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hPq, one_mul]; exact hE
    have := exp_neg_le_of_expLowQ hδ h1
    push_cast at this
    exact this
  have hxE : ∀ j : ℕ, Real.exp (-(2 * Real.pi * δ) * j) ≤ x ^ j := fun j => by
    calc Real.exp (-(2 * Real.pi * δ) * j) = Real.exp (-(2 * Real.pi * δ)) ^ j := by
          rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ x ^ j := pow_le_pow_left₀ (Real.exp_pos _).le hx j
  -- the tail
  have hEp : Real.exp (-(2 * Real.pi * δ) * (N + 1)) ≤
      (((powUp e P 64 (N + 1) : ℚ) / 2 ^ P : ℚ) : ℝ) := by
    have h1 := (hxE (N + 1)).trans (powUp_ge he 64 (N + 1))
    push_cast at h1 ⊢
    exact h1
  obtain ⟨hN, htail⟩ := sdTail_le_tailQ (γ := γ) hδ hc hEp
  -- the modes
  obtain ⟨pf, Lf, hgood, hsum⟩ : BCov ω' x (modeBox 2 N) ((s : ℝ) / 2 ^ P) :=
    walkB_sound hω he hl hG hs
  have key := smallDivisorSum_snoc_le_fiber hdio hγ' (Nat.cast_nonneg τ) hδ' hN
    pf Lf (fun k => (((pf k).natAbs : ℝ) - 1 / 2))
    (fun k hk => (hgood k hk).1)
    (fun k hk => (hgood k hk).2)
    (fun k hk hp => by
      have hp1 : (1 : ℝ) ≤ ((pf k).natAbs : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hp)
      refine ⟨by linarith, ?_⟩
      have h5 := (hgood k hk).1
      have h6 := abs_sub_abs_le_abs_sub ((pf k : ℤ) : ℝ) (-(Diophantine.frequencyDot ω' k))
      have e : ((pf k : ℤ) : ℝ) - -Diophantine.frequencyDot ω' k =
          Diophantine.frequencyDot ω' k + pf k := by ring
      rw [e, abs_neg] at h6
      have e2 : ((pf k).natAbs : ℝ) = |((pf k : ℤ) : ℝ)| := by
        rw [Nat.cast_natAbs]; push_cast; rfl
      rw [e2]
      linarith)
    (fun j => x ^ j) hxE
  refine key.trans ?_
  have hpi2 : Real.pi ^ 2 / 3 ≤ 99225 / 30000 := by
    have := Real.pi_pos
    have := Real.pi_lt_d2
    nlinarith
  have hE1 : x ^ 1 * (Real.pi ^ 2 / 3) ≤ (powUp e P 64 1 : ℝ) / 2 ^ P * (99225 / 30000) :=
    mul_le_mul (by simpa using powUp_ge he 64 1) hpi2 (by positivity) (by positivity)
  have hsum3 := add_le_add (add_le_add hE1 hsum) htail
  refine le_trans (le_of_eq ?_) (hsum3.trans (le_of_eq ?_))
  · rfl
  · push_cast; ring

end KAM.CertificateSharp.Fiber

end
