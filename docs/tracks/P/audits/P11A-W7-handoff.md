# P11A-W7 prover handoff (branch inp-p11aw7, 526146e; contains inp-p11aw6 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/WeakMeasure/Diophantine.lean` (171 lines). No other file touched (KAM.lean not edited).

**Proved:** `bpP:p11a:diophantine-measure` = `KAM.Planetary.diophantine_measure`, statement copied verbatim from
the signature file (the `P11DioHyp`, `p11Good`, `p11Csub` definitions already existed from W0).
- `stepP:p11a:dm-compact` = `p11_dm_compact` (good set = intersection of closed subsets of compact K).
- `stepP:p11a:dm-union` inlined (`hsub`: K \ H ⊆ ⋃_k {y∈K | |g̃_k(c_k,y)| ≤ ε_k}, c_k = k/|k|₂).
- `stepP:p11a:dm-onek` = `p11_dm_onek_hyp` (builds `P11SublevelHyp` at c_k from `P11DioHyp`) + `sublevel` (W6).
- `stepP:p11a:dm-sum` inlined (`measure_iUnion_le`, `ENNReal.tsum_mul_left`).
Helpers: `p11_K_sub_V`, `continuous_p11dotZ`, `p11euclid_int_pos`, `p11euclid_unit_int`, `p11dot_unit_int`, `p11Csub_nonneg`.

**Approach:** as the blueprint proof; no signature changed, no extra hypotheses.

**Checks:** `inp_lake_build.sh <wt> KAM.Planetary.WeakMeasure.Diophantine` -> "Build completed successfully", no warnings in my file.
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; it reports
"KAM.lean is out of date; run scripts/gen_root_imports.py" (new module not in root; I did not edit the generated file; orchestrator to regenerate).
`#print axioms KAM.Planetary.diophantine_measure`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations / design signals:** none. No heartbeat issues. Statement not changed. Not a provider theorem (module placed at the existing `KAM/Planetary/WeakMeasure/` directory like W0–W6).

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-W7 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures (countable subadditivity, compact intersection); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY WeakMeasure/Diophantine*.lean (compare with branch inp-p11aw6).
