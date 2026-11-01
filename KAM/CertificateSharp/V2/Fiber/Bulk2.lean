/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Fiber.BulkRuns
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# The extended bulk walk: tent runs, crossing runs and a computed crossing cut

`walkB2` covers the fibres `0 < |a| + |b| ≤ N` as `walkB` (`Fiber/Bulk.lean`) does, row by row and
half-row by half-row, with the run checks of `Fiber/BulkRuns.lean`. A node `[i₀, i₀ + n)` of a
half-row (`hnode`) is, in order:

1. a single fibre (`n = 1`, `blkK` with weight `1`);
2. a plain run (`blkK`), a tent run (`tentK`) or a crossing run (`apK`), each at the run's own
   geometric sum `gsumK n` (no dyadic table);
3. if the centre line crosses an integer in the node (`crossCut`: the crossing index `i_c`,
   computed by one division), either the crossing fibre alone with one crossing run on each side
   (light crossings), or the cut `[i₀, i_c - s₀)`, the single fibres `[i_c - s₀, i_c + s₀]` and
   `(i_c + s₀, i₀ + n)`, each recursed;
4. otherwise its two halves.

The recursion runs on a fuel argument; a node that needs more fuel fails (`none`), as does a fibre
whose check fails. **Soundness** needs nothing of the cut points or of the acceptance rules: every
branch is a partition of the node's index interval (`runSet_split`), and every leaf is a run check
with its own soundness theorem. `walkB2_sound` gives `BCov (modeBox 2 N) (s/2^P)`, and
`smallDivisorSum_snoc2_le_bulk2` has the output form of `smallDivisorSum_snoc2_le_walk`, through
`smallDivisorSum_snoc2_le_of_cover`.
-/

@[expose] public section

namespace KAM.CertificateSharp.Fiber

open KAM KAM.Certificate KAM.CertificateSharp

/-- The sum of two options, `none` if either is. -/
def oadd : Option ℕ → Option ℕ → Option ℕ
  | some u, some w => some (Nat.add u w)
  | _, _ => none

theorem oadd_eq_some {u w : Option ℕ} {v : ℕ} (h : oadd u w = some v) :
    ∃ a b : ℕ, u = some a ∧ w = some b ∧ v = a + b := by
  cases u <;> cases w <;> simp only [oadd, reduceCtorEq] at h
  simp only [Option.some.injEq] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

/-! ### Partitions of a run -/

theorem runSet_split {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {lo i0 n c : ℕ} (h0 : i0 ≤ c)
    (h1 : c ≤ i0 + n) :
    runSet a sg lo i0 n = runSet a sg lo i0 (c - i0) ∪ runSet a sg lo c (i0 + n - c) ∧
      Disjoint (runSet a sg lo i0 (c - i0)) (runSet a sg lo c (i0 + n - c)) := by
  constructor
  · ext k
    simp only [Finset.mem_union, mem_runSet]
    constructor
    · rintro ⟨j, hj, rfl⟩
      by_cases hjc : i0 + j < c
      · exact Or.inl ⟨j, by omega, rfl⟩
      · refine Or.inr ⟨i0 + j - c, by omega, ?_⟩
        rw [show lo + c + (i0 + j - c) = lo + i0 + j by omega]
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, by omega, rfl⟩
      · refine ⟨c - i0 + j, by omega, ?_⟩
        rw [show lo + i0 + (c - i0 + j) = lo + c + j by omega]
  · rw [Finset.disjoint_left]
    intro k hk hk'
    obtain ⟨j, hj, rfl⟩ := mem_runSet.mp hk
    obtain ⟨j', hj', h⟩ := mem_runSet.mp hk'
    have := (vec_one_inj hsg h).2
    omega

theorem runSet_zero (a sg : ℤ) (lo i0 : ℕ) : runSet a sg lo i0 0 = ∅ := by
  simp [runSet]

variable {ω' : Fin 2 → ℝ} {x : ℝ}

/-- A cover of a node from covers of the two sides of a cut point. -/
theorem BCov.split {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {lo i0 n c : ℕ} (h0 : i0 ≤ c)
    (h1 : c ≤ i0 + n) {u w : ℝ} (hu : BCov ω' x (runSet a sg lo i0 (c - i0)) u)
    (hw : BCov ω' x (runSet a sg lo c (i0 + n - c)) w) :
    BCov ω' x (runSet a sg lo i0 n) (u + w) := by
  obtain ⟨he, hd⟩ := runSet_split (a := a) (lo := lo) hsg h0 h1
  rw [he]
  exact BCov.union hd hu hw

/-- `BCov.split` with natural values over a common denominator. -/
theorem BCov.split' {a sg : ℤ} (hsg : sg = 1 ∨ sg = -1) {lo i0 n c : ℕ} (h0 : i0 ≤ c)
    (h1 : c ≤ i0 + n) {M : ℝ} {u w : ℕ} (hu : BCov ω' x (runSet a sg lo i0 (c - i0)) ((u : ℝ) / M))
    (hw : BCov ω' x (runSet a sg lo c (i0 + n - c)) ((w : ℝ) / M)) :
    BCov ω' x (runSet a sg lo i0 n) (((u + w : ℕ) : ℝ) / M) := by
  have := BCov.split hsg h0 h1 hu hw
  push_cast
  rwa [add_div]

/-! ### The walk -/

section Walk

variable (D : DBox2) (e P rn rd tol s0 : ℕ)

/-- `n` single fibres from `i₀`. -/
def singles (a sg : ℤ) (lo : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => some 0
  | i0, n + 1 => oadd (blkK D e P (pow2 P) (fun _ _ _ => true) a sg lo i0 i0)
      (singles a sg lo (Nat.add i0 1) n)

/-- One side of a crossing as one crossing run (`0` fibres: `0`; one fibre: single). -/
def sideAP (a sg : ℤ) (lo i0 : ℕ) : ℕ → Option ℕ
  | 0 => some 0
  | 1 => blkK D e P (pow2 P) (fun _ _ _ => true) a sg lo i0 i0
  | m + 2 => apK D e P (gsumK e P (m + 2)) s0 rn rd tol a sg lo i0 (Nat.add (Nat.add i0 m) 1)

/-- The cut around the integer crossed by the centre line of `[i₀, i₁]`: `(c₀, c₁, i_c)`, or
`none` if there is no crossing. -/
def crossCut (a sg : ℤ) (lo i0 i1 : ℕ) : Option (ℕ × ℕ × ℕ) :=
  let Q : ℤ := Int.ofNat (pow2 D.q)
  let X0 : ℤ := colX D a sg lo i0
  let X1 : ℤ := colX D a sg lo i1
  let f0 : ℤ := X0 / Q
  let f1 : ℤ := X1 / Q
  let dX : ℕ := Int.natAbs D.C1
  cond (decide (f0 = f1) || Nat.beq dX 0) none
    (let k : ℕ := Nat.div (Int.natAbs (max f0 f1 * Q - X0)) dX
     let ic : ℕ := Nat.add i0 (minN k (Nat.sub i1 i0))
     some (Nat.add i0 (Nat.sub (Nat.sub ic i0) s0), minN (Nat.add (Nat.add ic s0) 1) (Nat.add i1 1),
       ic))

/-- **A node** `[i₀, i₀ + n)` of a half-row, with `fuel` levels of recursion. -/
def hnode (a sg : ℤ) (lo : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | _, _, 0 => some 0
  | fuel, i0, n + 1 =>
    cond (Nat.beq n 0) (blkK D e P (pow2 P) (fun _ _ _ => true) a sg lo i0 i0)
      (match blkK D e P (gsumK e P (Nat.add n 1)) (accOk rn rd tol) a sg lo i0 (Nat.add i0 n) with
      | some v => some v
      | none =>
      match tentK D e P (gsumK e P (Nat.add n 1)) (accOk rn rd tol) a sg lo i0 (Nat.add i0 n) with
      | some v => some v
      | none =>
      match apK D e P (gsumK e P (Nat.add n 1)) s0 rn rd tol a sg lo i0 (Nat.add i0 n) with
      | some v => some v
      | none =>
      match fuel with
      | 0 => none
      | f + 1 =>
        match crossCut D s0 a sg lo i0 (Nat.add i0 n) with
        | some (c0, c1, ic) =>
          match oadd (oadd (sideAP D e P rn rd tol s0 a sg lo i0 (Nat.sub ic i0))
              (blkK D e P (pow2 P) (fun _ _ _ => true) a sg lo ic ic))
              (sideAP D e P rn rd tol s0 a sg lo (Nat.add ic 1) (Nat.sub (Nat.add i0 n) ic)) with
          | some v => some v
          | none => oadd (oadd (hnode a sg lo f i0 (Nat.sub c0 i0))
              (singles D e P a sg lo c0 (Nat.sub c1 c0)))
              (hnode a sg lo f c1 (Nat.sub (Nat.add (Nat.add i0 n) 1) c1))
        | none =>
          oadd (hnode a sg lo f i0 (Nat.div (Nat.add n 2) 2))
            (hnode a sg lo f (Nat.add i0 (Nat.div (Nat.add n 2) 2))
              (Nat.sub (Nat.add n 1) (Nat.div (Nat.add n 2) 2))))

/-- **A row** `a`: the half-rows `b ≥ loP a` and `b ≤ -1`; `0` if `|a| > N`. -/
def rowB2 (fuel N : ℕ) (a : ℤ) : Option ℕ :=
  cond (Nat.blt N (Int.natAbs a)) (some 0)
    (oadd (hnode D e P rn rd tol s0 a 1 (loP a) fuel 0
        (Nat.sub (Nat.add (Nat.sub N (Int.natAbs a)) 1) (loP a)))
      (hnode D e P rn rd tol s0 a (-1) 1 fuel 0 (Nat.sub N (Int.natAbs a))))

/-- **The extended bulk walk** over the fibres `0 < |a| + |b| ≤ N`. -/
def walkB2 (fuel N l : ℕ) : Option ℕ :=
  balFold (fun i => rowB2 D e P rn rd tol s0 fuel N (rowA N i)) l 0

end Walk

/-! ### Soundness -/

section Sound

variable {D : DBox2} {e P rn rd tol s0 : ℕ}

theorem single_spec (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P) {a sg : ℤ}
    (hsg : sg = 1 ∨ sg = -1) {lo i0 v : ℕ}
    (h : blkK D e P (pow2 P) (fun _ _ _ => true) a sg lo i0 i0 = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 1) ((v : ℝ) / 2 ^ P) := by
  have hg : ∑ j ∈ Finset.range (i0 - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤
      ((pow2 P : ℕ) : ℝ) / 2 ^ P := by
    rw [pow2_eq]; simp
  simpa using blkK_spec_gen hω he hg hsg le_rfl h

theorem singles_spec (hω : FreqEncloses 2 D.toBox ω') (he : e ≤ 2 ^ P) {a sg : ℤ}
    (hsg : sg = 1 ∨ sg = -1) {lo : ℕ} :
    ∀ (n i0 v : ℕ), singles D e P a sg lo i0 n = some v →
      BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 n) ((v : ℝ) / 2 ^ P) := by
  intro n
  induction n with
  | zero =>
    intro i0 v h
    simp only [singles, Option.some.injEq] at h
    subst h
    rw [runSet_zero]; exact BCov.empty (by simp)
  | succ n ih =>
    intro i0 v h
    simp only [singles, Nat.add_eq] at h
    obtain ⟨u, w, hu, hw, rfl⟩ := oadd_eq_some h
    have h1 := single_spec hω he hsg hu
    have h2 := ih (i0 + 1) w hw
    have := BCov.split (ω' := ω') (x := (e : ℝ) / 2 ^ P) (a := a) (lo := lo) (n := n + 1)
      hsg (show i0 ≤ i0 + 1 by omega) (show i0 + 1 ≤ i0 + (n + 1) by omega)
      (by simpa using h1) (by rw [show i0 + (n + 1) - (i0 + 1) = n by omega]; exact h2)
    push_cast
    rwa [add_div]

theorem sideAP_spec (hω : FreqEncloses 2 D.toBox ω') (he : e < 2 ^ P) {a sg : ℤ}
    (hsg : sg = 1 ∨ sg = -1) {lo i0 : ℕ} :
    ∀ {m v : ℕ}, sideAP D e P rn rd tol s0 a sg lo i0 m = some v →
      BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 m) ((v : ℝ) / 2 ^ P)
  | 0, v, h => by
    simp only [sideAP, Option.some.injEq] at h
    subst h
    rw [runSet_zero]; exact BCov.empty (by simp)
  | 1, v, h => by
    simp only [sideAP] at h
    exact single_spec hω he.le hsg h
  | m + 2, v, h => by
    simp only [sideAP, Nat.add_eq] at h
    have hg : ∑ j ∈ Finset.range (i0 + m + 1 - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤
        (gsumK e P (m + 2) : ℝ) / 2 ^ P := by
      rw [show i0 + m + 1 - i0 + 1 = m + 2 by omega]; exact gsumK_ge he _
    have := apK_spec hω he hg hsg h
    rwa [show i0 + m + 1 - i0 + 1 = m + 2 by omega] at this

theorem crossCut_spec {a sg : ℤ} {lo i0 i1 c0 c1 ic : ℕ} (hi : i0 ≤ i1)
    (h : crossCut D s0 a sg lo i0 i1 = some (c0, c1, ic)) :
    i0 ≤ c0 ∧ c0 ≤ ic ∧ ic < c1 ∧ c1 ≤ i1 + 1 ∧ ic ≤ i1 := by
  unfold crossCut at h
  simp only [Bool.cond_eq_ite, Bool.or_eq_true, decide_eq_true_eq, Nat.beq_eq] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq, Nat.add_eq, Nat.sub_eq, minN_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨by omega, by omega, ?_, ?_, ?_⟩
    · rw [lt_min_iff]; constructor <;> omega
    · exact min_le_right _ _
    · omega

/-- **Soundness of a node.** -/
theorem hnode_spec (hω : FreqEncloses 2 D.toBox ω') (he : e < 2 ^ P) {a sg : ℤ}
    (hsg : sg = 1 ∨ sg = -1) {lo : ℕ} :
    ∀ (fuel i0 n v : ℕ), hnode D e P rn rd tol s0 a sg lo fuel i0 n = some v →
      BCov ω' ((e : ℝ) / 2 ^ P) (runSet a sg lo i0 n) ((v : ℝ) / 2 ^ P) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i0 n v h
    cases n with
    | zero =>
      simp only [hnode, Option.some.injEq] at h
      subst h; rw [runSet_zero]; exact BCov.empty (by simp)
    | succ n =>
      simp only [hnode, Bool.cond_eq_ite, Nat.beq_eq, Nat.add_eq] at h
      split_ifs at h with hn0
      · subst hn0; exact single_spec hω he.le hsg h
      · have hg := gsumK_ge (P := P) he (n + 1)
        have hg' : ∑ j ∈ Finset.range (i0 + n - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤
            (gsumK e P (n + 1) : ℝ) / 2 ^ P := by rwa [show i0 + n - i0 + 1 = n + 1 by omega]
        have hlen : i0 + n - i0 + 1 = n + 1 := by omega
        split at h
        · rename_i v' hv'
          simp only [Option.some.injEq] at h; subst h
          have := blkK_spec_gen hω he.le hg' hsg (by omega) hv'
          rwa [hlen] at this
        · split at h
          · rename_i v' hv'
            simp only [Option.some.injEq] at h; subst h
            have := tentK_spec hω he.le hg' hsg (by omega) hv'
            rwa [hlen] at this
          · split at h
            · rename_i v' hv'
              simp only [Option.some.injEq] at h; subst h
              have := apK_spec hω he hg' hsg hv'
              rwa [hlen] at this
            · exact absurd h (by simp)
  | succ f ih =>
    intro i0 n v h
    cases n with
    | zero =>
      simp only [hnode, Option.some.injEq] at h
      subst h; rw [runSet_zero]; exact BCov.empty (by simp)
    | succ n =>
      simp only [hnode, Bool.cond_eq_ite, Nat.beq_eq, Nat.add_eq, Nat.sub_eq] at h
      split_ifs at h with hn0
      · subst hn0; exact single_spec hω he.le hsg h
      · have hg' : ∑ j ∈ Finset.range (i0 + n - i0 + 1), ((e : ℝ) / 2 ^ P) ^ j ≤
            (gsumK e P (n + 1) : ℝ) / 2 ^ P := by
          rw [show i0 + n - i0 + 1 = n + 1 by omega]; exact gsumK_ge he _
        have hlen : i0 + n - i0 + 1 = n + 1 := by omega
        split at h
        · rename_i v' hv'
          simp only [Option.some.injEq] at h; subst h
          have := blkK_spec_gen hω he.le hg' hsg (by omega) hv'
          rwa [hlen] at this
        split at h
        · rename_i v' hv'
          simp only [Option.some.injEq] at h; subst h
          have := tentK_spec hω he.le hg' hsg (by omega) hv'
          rwa [hlen] at this
        split at h
        · rename_i v' hv'
          simp only [Option.some.injEq] at h; subst h
          have := apK_spec hω he hg' hsg hv'
          rwa [hlen] at this
        split at h
        · -- a crossing cut
          rename_i c0 c1 ic hcut
          obtain ⟨hc0, hc0ic, hicc1, hc1, hic⟩ := crossCut_spec (s0 := s0) (by omega) hcut
          split at h
          · -- light: the crossing fibre and one crossing run on each side
            rename_i v' hv'
            simp only [Option.some.injEq] at h; subst h
            obtain ⟨u1, w1, hu1, hw1, rfl⟩ := oadd_eq_some hv'
            obtain ⟨u2, w2, hu2, hw2, rfl⟩ := oadd_eq_some hu1
            have hL := sideAP_spec hω he hsg hu2
            have hC := single_spec hω he.le hsg hw2
            have hR := sideAP_spec hω he hsg hw1
            have h12 := BCov.split' (ω' := ω') (x := (e : ℝ) / 2 ^ P) (a := a) (lo := lo)
              (i0 := i0) (n := ic + 1 - i0) (c := ic) hsg (by omega) (by omega)
              hL (by rw [show i0 + (ic + 1 - i0) - ic = 1 by omega]; exact hC)
            have := BCov.split' (ω' := ω') (x := (e : ℝ) / 2 ^ P) (a := a) (lo := lo)
              (i0 := i0) (n := n + 1) (c := ic + 1) hsg (by omega) (by omega)
              (by rw [show ic + 1 - i0 = ic + 1 - i0 by rfl]; exact h12)
              (by rw [show i0 + (n + 1) - (ic + 1) = i0 + n - ic by omega]; exact hR)
            exact this
          · -- the cut, recursed
            obtain ⟨u1, w1, hu1, hw1, rfl⟩ := oadd_eq_some h
            obtain ⟨u2, w2, hu2, hw2, rfl⟩ := oadd_eq_some hu1
            have hL := ih i0 (c0 - i0) u2 hu2
            have hC := singles_spec hω he.le hsg (c1 - c0) c0 w2 hw2
            have hR := ih c1 (i0 + n + 1 - c1) w1 hw1
            have h12 := BCov.split' (ω' := ω') (x := (e : ℝ) / 2 ^ P) (a := a) (lo := lo)
              (i0 := i0) (n := c1 - i0) (c := c0) hsg (by omega) (by omega)
              hL (by rw [show i0 + (c1 - i0) - c0 = c1 - c0 by omega]; exact hC)
            exact BCov.split' (ω' := ω') (x := (e : ℝ) / 2 ^ P) (a := a) (lo := lo)
              (i0 := i0) (n := n + 1) (c := c1) hsg (by omega) (by omega) h12
              (by rw [show i0 + (n + 1) - c1 = i0 + n + 1 - c1 by omega]; exact hR)
        · -- the two halves
          obtain ⟨u1, w1, hu1, hw1, rfl⟩ := oadd_eq_some h
          have hL := ih i0 ((n + 2) / 2) u1 hu1
          have hR := ih (i0 + (n + 2) / 2) (n + 1 - (n + 2) / 2) w1 hw1
          exact BCov.split' (ω' := ω') (x := (e : ℝ) / 2 ^ P) (a := a) (lo := lo)
            (i0 := i0) (n := n + 1) (c := i0 + (n + 2) / 2) hsg (by omega) (by omega)
            (by rw [show i0 + (n + 2) / 2 - i0 = (n + 2) / 2 by omega]; exact hL)
            (by rw [show i0 + (n + 1) - (i0 + (n + 2) / 2) = n + 1 - (n + 2) / 2 by omega]
                exact hR)

/-- The modes of a row of `walkB2`. -/
def rowSet2 (N : ℕ) (a : ℤ) : Finset (Fin 2 → ℤ) :=
  if N < a.natAbs then ∅ else
    runSet a 1 (loP a) 0 (N - a.natAbs + 1 - loP a) ∪ runSet a (-1) 1 0 (N - a.natAbs)

/-- **Soundness of a row.** -/
theorem rowB2_spec (hω : FreqEncloses 2 D.toBox ω') (he : e < 2 ^ P) {fuel N : ℕ} {a : ℤ}
    {v : ℕ} (h : rowB2 D e P rn rd tol s0 fuel N a = some v) :
    BCov ω' ((e : ℝ) / 2 ^ P) (rowSet2 N a) ((v : ℝ) / 2 ^ P) := by
  simp only [rowB2, Bool.cond_eq_ite, Nat.blt_eq, Nat.sub_eq, Nat.add_eq] at h
  unfold rowSet2
  by_cases hN : N < a.natAbs
  · simp only [hN, ↓reduceIte, Option.some.injEq] at h ⊢
    subst h
    exact BCov.empty (by simp)
  · simp only [hN, ↓reduceIte] at h ⊢
    obtain ⟨u, w, hu, hw, rfl⟩ := oadd_eq_some h
    have hD : Disjoint (runSet a 1 (loP a) 0 (N - a.natAbs + 1 - loP a))
        (runSet a (-1) 1 0 (N - a.natAbs)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      obtain ⟨j, -, rfl⟩ := mem_runSet.mp hk
      obtain ⟨j', -, h⟩ := mem_runSet.mp hk'
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
      omega
    have := BCov.union hD (hnode_spec hω he (Or.inl rfl) fuel 0 _ u hu)
      (hnode_spec hω he (Or.inr rfl) fuel 0 _ w hw)
    refine this.mono (le_of_eq ?_)
    push_cast
    rw [add_div]

theorem mem_rowSet2 {N : ℕ} {a : ℤ} {k : Fin 2 → ℤ} (hk : k ∈ rowSet2 N a) : k 0 = a := by
  unfold rowSet2 at hk
  split_ifs at hk
  · simp at hk
  rcases Finset.mem_union.mp hk with hk | hk <;>
  · obtain ⟨j, -, rfl⟩ := mem_runSet.mp hk
    simp

theorem mem_rowSet2_of_mem_modeBox {N : ℕ} {k : Fin 2 → ℤ} (hk : k ∈ modeBox 2 N) :
    k ∈ rowSet2 N (k 0) := by
  obtain ⟨hk0, hkN⟩ := mem_modeBox.mp hk
  rw [modeNat_two] at hkN
  have hvec : k = ![k 0, k 1] := by
    funext i
    fin_cases i <;> rfl
  unfold rowSet2
  have hN : ¬ N < (k 0).natAbs := by omega
  simp only [hN, ↓reduceIte]
  rw [Finset.mem_union, mem_runSet, mem_runSet]
  rcases le_or_gt 0 (k 1) with hb | hb
  · left
    rw [loP_eq]
    by_cases ha : k 0 = 0
    · have hb1 : k 1 ≠ 0 := fun hb0 => hk0 (by rw [hvec, ha, hb0]; funext i; fin_cases i <;> rfl)
      simp only [ha, ↓reduceIte]
      refine ⟨(k 1).toNat - 1, by omega, ?_⟩
      conv_lhs => rw [hvec]
      congr 2
      omega
    · simp only [ha, ↓reduceIte]
      refine ⟨(k 1).toNat, by omega, ?_⟩
      conv_lhs => rw [hvec]
      congr 2
      omega
  · right
    refine ⟨(-(k 1)).toNat - 1, by omega, ?_⟩
    conv_lhs => rw [hvec]
    congr 2
    omega

/-- **Soundness of the extended walk**: a cover of `modeBox 2 N` at `s/2^P`. -/
theorem walkB2_sound (hω : FreqEncloses 2 D.toBox ω') (he : e < 2 ^ P) {fuel N l s : ℕ}
    (hl : 2 * N + 1 ≤ 2 ^ l) (h : walkB2 D e P rn rd tol s0 fuel N l = some s) :
    BCov ω' ((e : ℝ) / 2 ^ P) (modeBox 2 N) ((s : ℝ) / 2 ^ P) := by
  obtain ⟨hrows, hs⟩ := balFold_eq_some h
  simp only [zero_add] at hrows hs
  have hx0 : (0 : ℝ) ≤ (e : ℝ) / 2 ^ P := by positivity
  set S : ℕ → Finset (Fin 2 → ℤ) := fun i => rowSet2 N (rowA N i) with hS
  set v : ℕ → ℝ := fun i =>
    (((rowB2 D e P rn rd tol s0 fuel N (rowA N i)).getD 0 : ℕ) : ℝ) / 2 ^ P with hv
  have hcov : BCov ω' ((e : ℝ) / 2 ^ P) ((Finset.range (2 ^ l)).biUnion S)
      (∑ i ∈ Finset.range (2 ^ l), v i) := by
    refine BCov.biUnion (fun i _ j _ hij => ?_) fun i hi => ?_
    · rw [Function.onFun, Finset.disjoint_left]
      intro k hki hkj
      have h1 := mem_rowSet2 hki
      have h2 := mem_rowSet2 hkj
      apply hij
      have : rowA N i = rowA N j := h1.symm.trans h2
      unfold rowA at this
      omega
    · obtain ⟨u, hu⟩ := hrows i (Finset.mem_range.mp hi)
      have := rowB2_spec hω he hu
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
    exact mem_rowSet2_of_mem_modeBox hk

end Sound

/-- **The bound of `S((ω', 1), δ)` from a cover** of `modeBox 2 N` at `s/2^P` with the weights
`(e/2^P)^j`: the output form of `smallDivisorSum_snoc2_le_walk`. -/
theorem smallDivisorSum_snoc2_le_of_cover {e P N s J τ : ℕ} {γ δ : ℚ} (he : e ≤ 2 ^ P)
    (hE : (2 : ℚ) ^ P ≤ e * expLowQ δ J) (hγ : 0 < γ) (hδ : 0 < δ) (hc : 0 < cLoQ δ τ N)
    {ω' : Fin 2 → ℝ} (hcov : BCov ω' ((e : ℝ) / 2 ^ P) (modeBox 2 N) ((s : ℝ) / 2 ^ P))
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
  have hEp : Real.exp (-(2 * Real.pi * δ) * (N + 1)) ≤
      (((powUp e P 64 (N + 1) : ℚ) / 2 ^ P : ℚ) : ℝ) := by
    have h1 := (hxE (N + 1)).trans (powUp_ge he 64 (N + 1))
    push_cast at h1 ⊢
    exact h1
  obtain ⟨hN, htail⟩ := sdTail_le_tailQ (γ := γ) hδ hc hEp
  obtain ⟨pf, Lf, hgood, hsum⟩ := hcov
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

/-- **The bound of `S((ω', 1), δ)` from the extended bulk walk** (`e < 2^P`). -/
theorem smallDivisorSum_snoc2_le_bulk2 {D : DBox2} {e P N l s J τ rn rd tol s0 fuel : ℕ}
    {γ δ : ℚ} (he : e < 2 ^ P) (hE : (2 : ℚ) ^ P ≤ e * expLowQ δ J) (hγ : 0 < γ) (hδ : 0 < δ)
    (hc : 0 < cLoQ δ τ N) (hl : 2 * N + 1 ≤ 2 ^ l)
    (hs : walkB2 D e P rn rd tol s0 fuel N l = some s) {ω' : Fin 2 → ℝ}
    (hω : FreqEncloses 2 D.toBox ω')
    (hdio : IsDiophantine (γ : ℝ) τ (Fin.snoc ω' 1 : Fin 3 → ℝ)) :
    smallDivisorSum (Fin.snoc ω' 1 : Fin 3 → ℝ) (δ : ℝ) ≤
      (((powUp e P 64 1 : ℚ) / 2 ^ P * (99225 / 30000) + (s : ℚ) / 2 ^ P +
        tailQ γ δ τ N ((powUp e P 64 (N + 1) : ℚ) / 2 ^ P) : ℚ) : ℝ) :=
  smallDivisorSum_snoc2_le_of_cover he.le hE hγ hδ hc (walkB2_sound hω he hl hs) hdio

end KAM.CertificateSharp.Fiber

end
