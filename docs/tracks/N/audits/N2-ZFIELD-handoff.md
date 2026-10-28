# N2-ZFIELD prover handoff (branch inp-n2z, ac46498; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/QcZero/ZeroField.lean` (~100 lines). No other file touched (KAM.lean not regenerated, per brief).

**Nodes:** `zd_zero` (stepN:p2:zd-zero), `zd_diff` (zd-diff), `zd_field` (zd-field), `zero_deriv` (bpN:p2:zero-deriv); all in `KAM.Nekhoroshev`, signatures copied verbatim from N2Signatures.lean (same variables/include).

**Approach:** Data from the four premises; `zd_zero` = `holo_real_e` + `realInclusion₂_preimage_complexDomain`. `zd_diff`: `realPart h` is C³ on the open `realActionDomain = ball (R+s)` (`realActionDomain_eq`), so differentiable at `z.2`; compose with `hasFDerivAt_snd`, transfer by `congr_of_eventuallyEq` using equality on the open `Wdom`. `zd_field` from `HasFDerivAt.fderiv`, evaluated on coordinate vectors. `zero_deriv` packages them.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n2z KAM.Nekhoroshev.QcZero.ZeroField`: "Build completed successfully (2895 jobs)", no warnings/sorry.
- `#print axioms zero_deriv` and `zd_zero`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: the new module is not in the generated root; orchestrator regenerates).

**Uncertainties:** none. No heartbeat/design signals. No suspected errata; no deviations from signatures.

AUDIT FOCUS (design docs/tracks/N/design/N2-LEAN-DESIGN.md row N2-ZFIELD and proof plan; audit DESIGN-N2-design-audit-1.md; signatures .drafts/design/N2Signatures.lean; blueprint-N p2 zero-field nodes): (1) statements = design signatures and blueprint (zd receipts, zero_deriv); the frozen C^3 clause of IsAnalyticIntegrable is consumed, not re-assumed; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N2-ZFIELD module(s) listed in the handoff.
