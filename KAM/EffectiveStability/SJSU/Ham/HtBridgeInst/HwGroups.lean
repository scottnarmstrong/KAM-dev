/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Groups

/-!
# Every row exponent of `H_w` is a group of N7's ledger (T2-CONF, N5a-2)

`sjsuHwAll_groups : ∀ e ∈ sjsuHwAll, tripleExp e ∈ sjsuNs`. Each triple `(n₁, n₂, n₃)` with
entries `< 32` has the key `(n₁·32 + n₂)·32 + n₃`. The groups give the bit mask `Σ 2^key`
(`sjsuNsMask`), and a row passes when its triple is bounded and its bit is set (`Nat.testBit`): a
constant number of kernel steps per row. Deciding `tripleExp e ∈ sjsuNs` directly (a linear search
per row, about 2,000 rows in degree 9) exceeds the build's 6 GB memory cap (design signal).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The key of a bounded triple. -/
def nsKey (n : ℕ × ℕ × ℕ) : ℕ := (n.1 * 32 + n.2.1) * 32 + n.2.2

/-- The bit mask of the keys of a list of triples. -/
def keyMask (l : List (ℕ × ℕ × ℕ)) : ℕ := l.foldr (fun n acc => acc ||| 1 <<< nsKey n) 0

/-- The mask of N7's groups. -/
def sjsuNsMask : ℕ := keyMask sjsuNs

/-- A row's exponent triple is bounded by 31 and its key is in the mask. -/
def rowGroupOk (e : (Mon × Mon) × ℤ) : Bool :=
  decide ((tripleExp e).1 < 32) && decide ((tripleExp e).2.1 < 32) &&
    decide ((tripleExp e).2.2 < 32) && sjsuNsMask.testBit (nsKey (tripleExp e))

theorem nsKey_inj {a b : ℕ × ℕ × ℕ} (ha : a.1 < 32 ∧ a.2.1 < 32 ∧ a.2.2 < 32)
    (hb : b.1 < 32 ∧ b.2.1 < 32 ∧ b.2.2 < 32) (h : nsKey a = nsKey b) : a = b := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  obtain ⟨b₁, b₂, b₃⟩ := b
  simp only [nsKey] at h ha hb
  simp only [Prod.mk.injEq]
  omega

theorem exists_of_testBit_keyMask {l : List (ℕ × ℕ × ℕ)} {k : ℕ}
    (h : (keyMask l).testBit k = true) :
    ∃ n ∈ l, nsKey n = k := by
  induction l with
  | nil => simp [keyMask] at h
  | cons a l ih =>
    simp only [keyMask, List.foldr_cons, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨n, hn, rfl⟩ := ih (by simpa only [keyMask, Nat.one_shiftLeft] using h)
      exact ⟨n, List.mem_cons_of_mem _ hn, rfl⟩
    · exact ⟨a, List.mem_cons_self, h⟩

theorem mem_of_rowGroupOk {e : (Mon × Mon) × ℤ} (h : rowGroupOk e = true) :
    tripleExp e ∈ sjsuNs := by
  simp only [rowGroupOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, hk⟩ := h
  obtain ⟨n, hn, hk⟩ := exists_of_testBit_keyMask hk
  have hb := sjsuNs_bound n hn
  rwa [← nsKey_inj ⟨by omega, by omega, by omega⟩ ⟨h₁, h₂, h₃⟩ hk]

theorem sjsuHw0_groups : (sjsuHw 0).all rowGroupOk = true := rfl

theorem sjsuHw1_groups : (sjsuHw 1).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw2_groups : (sjsuHw 2).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw3_groups : (sjsuHw 3).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw4_groups : (sjsuHw 4).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw5_groups : (sjsuHw 5).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw6_groups : (sjsuHw 6).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw7_groups : (sjsuHw 7).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw8_groups : (sjsuHw 8).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHw9_groups : (sjsuHw 9).all rowGroupOk = true := by
  decide +kernel

theorem sjsuHwAll_groups : ∀ e ∈ sjsuHwAll, tripleExp e ∈ sjsuNs := by
  have h : sjsuHwAll.all rowGroupOk = true := by
    simp only [sjsuHwAll, List.all_append, sjsuHw0_groups, sjsuHw1_groups, sjsuHw2_groups,
      sjsuHw3_groups, sjsuHw4_groups, sjsuHw5_groups, sjsuHw6_groups, sjsuHw7_groups,
      sjsuHw8_groups, sjsuHw9_groups, Bool.and_true]
  intro e he
  exact mem_of_rowGroupOk (List.all_eq_true.1 h e he)

end KAM.EffectiveStability.SJSU

end
