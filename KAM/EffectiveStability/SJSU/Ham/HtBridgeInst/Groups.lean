/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridge
public import KAM.EffectiveStability.SJSU.Ledger.H.HData

/-!
# The groups of N7's Horner ledger (T2-CONF, N5a-2)

Facts about N7's group list `sjsuNs` (714 exponent triples), and the per-group check `tdatOk` of the
`T_n` data, used in blocks of 8 by `HtBridgeInst.Tdat0`–`Tdat2`.

`sjsuNs_nodup` goes through the strictly increasing keys `(n₁·32 + n₂)·32 + n₃`: deciding `Nodup`
directly compares all pairs and exceeds the build's 6 GB memory cap (design signal).
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The keys of the groups are strictly increasing (a linear kernel check). -/
theorem sjsuNs_key_chain :
    (sjsuNs.map fun n => (n.1 * 32 + n.2.1) * 32 + n.2.2).IsChain (· < ·) := by
  decide +kernel

theorem sjsuNs_nodup : sjsuNs.Nodup :=
  List.Nodup.of_map _ ((List.isChain_iff_pairwise.1 sjsuNs_key_chain).imp ne_of_lt)

theorem sjsuNs_bound : ∀ n ∈ sjsuNs, n.1 ≤ 18 ∧ n.2.1 ≤ 18 ∧ n.2.2 ≤ 18 := by decide +kernel

theorem sjsuNs_length : sjsuNs.length ≤ 8 * 90 := by decide +kernel

/-- The check of the `T_n` data of one group. -/
def tdatOk (n : ℕ × ℕ × ℕ) : Bool :=
  listBEq (sjsuTdat n) (pDense 9 (tTerms sjsuE sjsuN sjsuHwAll n))

end KAM.EffectiveStability.SJSU

end
