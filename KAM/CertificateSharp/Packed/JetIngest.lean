/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetSeg

/-!
# Ingestion of packed box nodes from narrow literals

A ledger node on the box `D₀ × D₁` (row stride `S`, slot width `w`) has `D₀ D₁` digits of a few
more bits than its largest coefficient, far fewer than `w`, and `(D₀ - 1)(S - D₁)` gap slots. Its
literal therefore lists only the box digits, in row order, at a narrow width `wn` with the offset
`2^(wn-1)`; the kernel spreads them to the layout by two balanced re-spacings (`respace`: halves by
mask and shift, then one digit at a time) and removes the offset. This is data ingestion, not a
check: the theorems speak of the ingested value, and an export is compared with it exactly.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

/-- `k` digits of width `a` re-spaced to width `b`, one at a time. -/
def respaceLin (a b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, Y => (Y &&& (2 ^ a - 1)) + (respaceLin a b k (Y >>> a) <<< b)

/-- `k` digits of width `a` re-spaced to width `b`: halves by mask and shift (`fuel` levels). -/
def respace (a b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, k, Y => respaceLin a b k Y
  | f + 1, k, Y =>
    if k ≤ 8 then respaceLin a b k Y else
      respace a b f (k / 2) (Y &&& (2 ^ (a * (k / 2)) - 1)) +
        (respace a b f (k - k / 2) (Y >>> (a * (k / 2))) <<< (b * (k / 2)))

/-- A box node part from its narrow literal `Y` (the `D₀ D₁` box digits in row order, `wn` bits
each, offset `2^(wn-1)`). -/
def jIngest (D0 D1 S w wn Y : ℕ) : ℤ :=
  ((respace (D1 * w) (S * w) 16 D0 (respace wn w 16 (D0 * D1) Y) : ℕ) : ℤ) -
    (boxPat w S D0 D1 (2 ^ (wn - 1)) : ℤ)

end KAM.CertificateSharp.Packed
