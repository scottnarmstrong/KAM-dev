# N12-17 prover handoff (branch inp-n1217, 9a99daa; contains N12-01..N12-15 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Most.lean` (92 lines). No other file changed.

**Node:** `averaging_most_core` (`bpN:p12:s-most#data`, `mo-E`, `mo-z`), statement copied verbatim from N12Signatures.lean.

**Approach:** `bad` gives `M₂, A₁` and the threshold `η ≤ avgStopped` on `K \ avgGood` (η ≤ R/8). `E = K \ avgGood h f R ε η K` is measurable by `good`. Volume bound: Markov (`meas_ge_le_lintegral_div`) on the Borel extension `avgStoppedExt`, which equals `avgStopped` on `K` (`avgStopped_eq_ext`). For `x ∈ K \ E`, `z t = avgFlow … t x`. `z 0 = x` comes from `avgMaximal_spec`. `IsSolutionOn` on `Icc 0 (1/ε)` comes from `ham_reduction` plus `mono` of the maximal solution, using `mem_flowDomain_of_omega`. The displacement is bounded by `sSup < η`.

**Checks:**
- `lake build KAM.Nekhoroshev.Averaging.Most` through the gate: "Build completed successfully (3248 jobs)", no warnings in Most.lean.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. It also prints "KAM.lean is out of date; run scripts/gen_root_imports.py", which is expected because I may not edit KAM.lean.
- `#print axioms KAM.Nekhoroshev.averaging_most_core`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues, no frozen or provider imports.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-17 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statement of averaging_most_core = signature file exactly; (2) proof sound (the solution exists on all of [0,T] for good data; Markov volume bound; N12-15 bad/good and ham_reduction consumed as designed; measurability of E); no added premises; (3) hygiene. Audit ONLY KAM/Nekhoroshev/Averaging/Most.lean (compare with branch inp-n1215).
