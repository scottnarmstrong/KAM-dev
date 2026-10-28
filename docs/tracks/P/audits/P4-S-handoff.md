# P4-S prover handoff (branch inp-p4s, 53b3ef8; contains inp-p45s (P45-S, audited); offloaded package run by the main orchestrator; prover on claude-12)

Files: new `KAM/Planetary/PGMeasure/Setting.lean` (~100 lines), committed on inp-p4s.
Declarations (copied verbatim from P45Signatures.lean): `secularPolynomial`, `slowFrequency`, `freq`
(bpP:p4:freq), `MeasureData` (bpP:p4:data), `resonanceBad`. All are definitions/structures; no proofs needed.
`joinedActions` (bpP:p4:conv#shell) already exists, identical to the signature, in P45-S
`KAM/Planetary/PG/Setting.lean`; reused, not redeclared (a duplicate would clash).
Not in this module by design: `resonanceBad_eq` (needs P1 predicate; owned by P4-M), `measure_c1/c2`, `latticeS`.
Imports: Mathlib, KAM.Planetary.PG.Setting, frozen Defs HasFastDiffeomorphism, FastFrequency only (no providers/theorem anchors).
Approach: verbatim copy; only whitespace reflow of two lines >100 chars (lint).
Checks: gate build `KAM.Planetary.PGMeasure.Setting` OK (no warnings); `scripts/lint_sources.sh`: all PASS except
"KAM.lean is out of date" (expected; KAM.lean is generated and not mine to edit — orchestrator should run gen_root_imports.py).
`#print axioms` freq / MeasureData / resonanceBad: propext, Classical.choice, Quot.sound.
Uncertainties: none. Errata: none. Deviations: none. Heartbeat design signals: none.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-S and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statements/definitions = design signatures (freq, MeasureData, resonanceBad, joinedActions), faithful on their whole carrier; (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/Setting.lean (compare with branch inp-p45s).
