/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Data.LockN65.ZCode

/-!
# Whitened compact integer-list literals (LOCK-DATA, DELTA-LAM-3)

`zdecs` (`ZCode`) reads each row literal byte by byte through `n, n / 256, n / 256², …`. For rows
of large fixed-point coefficients (long runs of `0x80`, `0xff`, `0x00` bytes) these intermediate
literals share their low 64 bits massively. The kernel's caches key a large `Nat` literal by its
low limb, so within one declaration the lookups walk long collision chains, and the cost grows
about `n^2.5`. Measured on the 410 rows of `lockL2037T.c0`: 10,536 intermediates with only 6,569
distinct low limbs; the values decode in 67.7 s, against 1.5 s for random rows of the same size.
The lam run's route-E segments, which decode many such models in one `decide +kernel`, did not
finish.

`zdecsX s rows` reads the same entries from WHITENED rows: byte `j` of row `r` is stored XOR
`zkey s r j` (a fixed key stream of a salt `s`, the row index and the position), so the
intermediates have pseudo-random low limbs. The rows of `lockL2037T.c0` then decode in 3.2 s, and
the result is kernel-checked equal to `zdecs` on the original rows (a scratch check over all 410
rows). The data stay untrusted: a checker checks whatever `zdecsX` denotes.
-/

@[expose] public section

namespace KAM.SpinOrbit.Data.LockN65

/-- The key byte of position `j` of row `r` under the salt `s`. -/
def zkey (s r j : ℕ) : ℕ := (s * 167 + r * 199 + j * 131 + r * j * 59 + 97) % 256

/-- One varint of a whitened row from the low bytes of `n` (at most `f` bytes; `j` is the position
of the next byte in the row): the value, the remaining bytes and the next position. -/
def zvarX : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, _, j, n, acc, _ => (acc, n, j)
  | f + 1, s, r, j, n, acc, sh =>
    if Nat.xor (n % 256) (zkey s r j) < 128 then
      (acc + Nat.xor (n % 256) (zkey s r j) <<< sh, n / 256, j + 1)
    else
      zvarX f s r (j + 1) (n / 256) (acc + (Nat.xor (n % 256) (zkey s r j) - 128) <<< sh)
        (sh + 7)

/-- The first `k` entries of row `r` (salt `s`), its bytes from position `j` on coded in `n`. -/
def zdecX (s r : ℕ) : ℕ → ℕ → ℕ → List ℤ
  | 0, _, _ => []
  | k + 1, j, n =>
    unzig (zvarX 24 s r j n 0 0).1 ::
      zdecX s r k (zvarX 24 s r j n 0 0).2.2 (zvarX 24 s r j n 0 0).2.1

/-- The entries of whitened rows from row index `r` on. -/
def zdecsXAux (s : ℕ) : ℕ → List (ℕ × ℕ) → List ℤ
  | _, [] => []
  | r, c :: cs => zdecX s r c.1 0 c.2 ++ zdecsXAux s (r + 1) cs

/-- The entries of chunked whitened data: each pair `(k, c)` codes `k` whole entries. -/
def zdecsX (s : ℕ) (cs : List (ℕ × ℕ)) : List ℤ := zdecsXAux s 0 cs

/-- `zdecs_test`'s rows, whitened under salt 0. -/
theorem zdecsX_test : zdecsX 0 [(2, 0xe064), (3, 0xa4e72b)] = [-3, 2, -2, -1, 0] := by
  decide +kernel

end KAM.SpinOrbit.Data.LockN65
