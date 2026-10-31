/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation

/-!
# Compact integer-list literals (LOCK-DATA, B3 probe)

A list of integers written as one natural-number literal: each entry zigzag-coded (`v ≥ 0 ↦ 2v`,
`v < 0 ↦ -2v - 1`) as a little-endian base-`128` varint (a byte `≥ 128` continues the entry), the
bytes packed little-endian into one `ℕ`. `zdec k n` reads `k` entries back with kernel-accelerated
`Nat` division and remainder only, so a generated module states
`def x : List ℤ := zdecs [(k, 0x…), …]` instead of a long `List ℤ` literal, whose elaboration
dominates the cost of the lock's data. The data stay untrusted: a checker checks whatever `zdecs`
denotes.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

/-- One varint from the low bytes of `n` (at most `f` bytes): the value and the remaining bytes. -/
def zvar : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, n, acc, _ => (acc, n)
  | f + 1, n, acc, sh =>
    if n % 256 < 128 then (acc + n % 256 * 2 ^ sh, n / 256)
    else zvar f (n / 256) (acc + (n % 256 - 128) * 2 ^ sh) (sh + 7)

/-- The zigzag decoding `2v ↦ v`, `2v + 1 ↦ -v - 1`. -/
def unzig (v : ℕ) : ℤ := if v % 2 = 0 then ((v / 2 : ℕ) : ℤ) else -(((v + 1) / 2 : ℕ) : ℤ)

/-- The first `k` entries coded in `n` (entries of at most `168` bits). -/
def zdec : ℕ → ℕ → List ℤ
  | 0, _ => []
  | k + 1, n => unzig (zvar 24 n 0 0).1 :: zdec k (zvar 24 n 0 0).2

/-- The natural number with little-endian chunks of `40` bytes (one short source line each). -/
def zjoin (cs : List ℕ) : ℕ := cs.foldr (fun c a => c + a * 2 ^ 320) 0

/-- The entries of chunked data: each pair `(k, c)` codes `k` whole entries in the chunk `c` (at
most `40` bytes), so every decoding step divides a small number. -/
def zdecs (cs : List (ℕ × ℕ)) : List ℤ := cs.flatMap fun c => zdec c.1 c.2

theorem zdec_test : zdec 5 (zjoin [0x01030405]) = [-3, 2, -2, -1, 0] := by decide +kernel

theorem zdecs_test : zdecs [(2, 0x0405), (3, 0x0103)] = [-3, 2, -2, -1, 0] := by decide +kernel

end KAM.SpinOrbit.Data.LockN65
