# N89-P5 prover handoff (branch inp-n89p5, bd8304e; contains inp-n89p4 (audited) and N89-G1..G7, P1..P3; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Poschel/Theorem1.lean` (207 lines). No other file touched.

**Nodes:** `bpN:p9:thm1` -> `KAM.Nekhoroshev.thm1` (signature verbatim; both branches), with local steps
t1-par (`elementary`, `covering`, `full_rank_zone`), t1-b (exceptional branch: full-rank block `⊤`, `blockAdm`
via `Or.inl`, radius `r0` from `full_rank_zone`), t1-a-choice (`covering` block; `Λ ≠ ⊤` by `full_rank_zone`
iff), t1-a-theta (private `time_bot`), t1-a-res (private `time_mid`), t1-a-concl (exponent identity
`π s/(3√n)·K = 2π(K/√n)s/6`, `Om_Λ ≤ Om0` by attainment of the block-ball maximum and ball inclusion
`r_Λ/2 ≤ r0/(AK) ≤ r0/A`, then `block_stab`).

**Approach:** the numerical comparisons are separate real-arithmetic lemmas `time_bot`, `time_mid`; for
intermediate blocks `r_Λ ≥ A·r_⊥` from `vol ≤ K^d`, `d ≥ 1`, `A ≥ 1`.

**Checks:** `inp_lake_build.sh ... KAM.Nekhoroshev.Poschel.Theorem1`: "Build completed successfully", no
warning/sorry in my file. `scripts/lint_sources.sh`: all checks PASS (frozen anchor guard, ABI hashes OK).
`#print axioms KAM.Nekhoroshev.thm1`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No signature change, no extra hypotheses, no heartbeat
overrides, no design signals (default heartbeats).

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-P5 and proof plan; its design audits; signatures .drafts/design/N89Signatures.lean; blueprint-N p9 bpN:p9:thm1 L111-L136): thm1 is an INTERNAL theorem for Part 10 (not a frozen anchor, not N-HEAD-C). (1) statement of thm1 = signature file exactly, joint two-branch statement with shared constants retained; (2) proof sound: steps t1-par, t1-b, t1-a-choice, t1-a-theta, t1-a-res, t1-a-concl each realized; exponent identity and Om_Lambda <= Om0 by attainment of the block-ball maximum (no arbitrary Omega substituted for the maximum); block_stab, covering, full_rank_zone, elementary consumed as designed; no added premises; (3) hygiene. Audit ONLY KAM/Nekhoroshev/Poschel/Theorem1.lean (compare with branch inp-n89p4).
