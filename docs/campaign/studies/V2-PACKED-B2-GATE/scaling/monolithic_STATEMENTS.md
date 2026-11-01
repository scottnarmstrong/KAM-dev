# Statements of the `monolithic_*` receipts (superseded design)

These two probes ran against the single-declaration design of the packed Gram check at commit `42608fa1`
(before the memoized boundary of `f43d38ce`), whose `pgGuard` and `gramPackedCheck` evaluated the eight landed
DK models inside one declaration. Their data body is the one `scripts/packed/gram_gate_gen.py` emits, without
the `tz` notation and the memo (`gMre_*`, `gMim_*`, `gMemo`), which that design did not have. They cannot be
regenerated against the current API; their statements were:

`monolithic_GramGuard` (142 s kernel, 2.90 GB charged):

    theorem probe :
        pgGuard 2 lg00Emb lg00GramInv gW gCfg lg00Pi gBook = true := by
      decide +kernel

`monolithic_GramPacked` (OOM-killed at the 4 GB cap after 255 s user):

    theorem probe :
        (gramPackedCheck 2 lg00Emb lg00GramInv gW gCfg lg00Pi gBook
          ((73 / 50 : ℚ) - 1 / 100000)).isSome = true := by
      decide +kernel
