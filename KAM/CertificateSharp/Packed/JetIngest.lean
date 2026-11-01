/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.JetWit

/-!
# Ingestion of packed box nodes from narrow literals

A ledger node on the box `D₀ × D₁` (row stride `S`, slot width `w`) has `D₀ D₁` digits of a few
more bits than its largest coefficient, far fewer than `w`, and `(D₀ - 1)(S - D₁)` gap slots. Its
literal therefore lists only the box digits, in row order, at a narrow width `wn` with the offset
`2^(wn-1)`. The kernel spreads them to the layout in a logarithmic number of whole-number steps
(`spreadStep`: in every block of `2h` digits the upper `h` move up by `(b - a) h` bits, by one mask,
one multiplication and one addition, the mask in closed form), first the digits from width `wn` to
`w`, then the rows from `D₁ w` to `S w`, and removes the offset. A digit-by-digit spreading costs
one kernel operation per digit (V2-PACKED-JET-MEM: about 37 MB and 0.22 s per part, against a few
megabytes here). This is data ingestion, not a check: the theorems speak of the ingested value, and
an export is compared with it exactly.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

/-- One level: in each of the `k` blocks of `2h` digits (period `b · 2h` bits), the upper `h`
digits of width `a` move up by `(b - a) h` bits. -/
def spreadStep (a b h k Y : ℕ) : ℕ :=
  Y + (Y &&& periodic (b * (2 * h)) k ((2 ^ (a * h) - 1) <<< (a * h))) * (2 ^ ((b - a) * h) - 1)

/-- `2^L` digits of width `a` (in `k` blocks) spread to width `b`, top level first. -/
def spreadAux (a b : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, Y => Y
  | L + 1, k, Y => spreadAux a b L (2 * k) (spreadStep a b (2 ^ L) k Y)

/-- A box node part from its narrow literal `Y`: the `D₀ D₁ ≤ 2^L₁` box digits in row order,
`wn` bits each with the offset `2^(wn-1)`, spread to slots of width `w` and then to rows of stride
`S` (`D₀ ≤ 2^L₂`). -/
def jSpread (D0 D1 S w wn L1 L2 Y : ℕ) : ℤ :=
  ((spreadAux (D1 * w) (S * w) L2 1 (spreadAux wn w L1 1 Y) : ℕ) : ℤ) -
    (boxPat w S D0 D1 (2 ^ (wn - 1)) : ℤ)

end KAM.CertificateSharp.Packed
