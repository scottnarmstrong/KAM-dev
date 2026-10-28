# Lane N log (Zohar's team)

Rulings and integration notes for lane N after its handoff on 2026-10-28
([`LANE-N-HANDOFF.md`](LANE-N-HANDOFF.md)). Times are UTC.

- **2026-10-28 22:45. Ruling F2-C1 (handoff §10 Q1): option (a).**
  - The signed `iterative` gains `(hc : 0 < b.c)` after `hSL`. This is a source positivity premise: in the
    source the block radius r_B and the slow width w are positive, so c = 2π r_B²/w² > 0. It is the premise
    the 21:15 ruling gave `canonical_map`, which `iterative` applies.
  - Its only consumer, `nf` (K1/K2), obtains it from `ExtNFHyp.radius_pos` and `ExtNFHyp.slow_width_pos`.
    No other signed statement changes.
  - N11-F2's audit-1 FAIL was about consumer completeness only (no soundness defect); with this ruling it is
    resolved and F2 is accepted. The tracked signature file `docs/tracks/N/design/N11-SIGNATURES.md` carries
    the amendment.
- **2026-10-28 22:50. N11-N and N11-P written; trial seal.**
  - `block` (`KAM/Nekhoroshev/Partial/Block.lean`) and the provider
    (`KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean`) compile against the landed E3 and G modules.
  - Trial seal (not committed): the anchor body
    `by exact KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev hn hk G G' D … hHess hdef` (2 lines, 157 bytes)
    builds; `ABI HASHES OK (144 frozen declarations)`. The guard's only failures were the staging `sorry`s of
    the packages still being proved (H, K1/K2, M1, M2).
