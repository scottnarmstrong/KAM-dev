# N2-QC prover handoff (branch inp-n2q, 821a18f; contains inp-n2d (N2-DERIV, audited) and N2-KERNEL; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/QcZero/QCResults.lean` (~80 lines). Nothing else changed (KAM.lean untouched).

**Nodes / declarations** (signatures copied verbatim from N2Signatures.lean, namespace `KAM.Nekhoroshev`):
- `bpN:p2:n0` → `n0`: any point of U has nonzero frequency (frozen QC), impossible on `Fin 0 → ℝ` (Subsingleton).
- `stepN:p2:qb-unpack` → `qb_unpack`: unpacks frozen `IsStrictlyQuasiConvex`; `1 ≤ n` from `freq ≠ 0`.
- `stepN:p2:qb-deriv` → `qb_deriv`: `(qc_deriv ..).fderiv`, with hypotheses from `qb_unpack`.
- `stepN:p2:qb-pos` → `qb_pos`: `qd_sym` quadratic identity, `m‖v‖² > 0`, coercivity from `qb_unpack`.
- `bpN:p2:qc-bij`, `stepN:p2:qb-concl` → `qc_bij`: `isoenergetic_bijective_of_qc hqc hI hlam` (existing exact route; as the design says, this does not prove the general matrix lemma route).

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n2q KAM.Nekhoroshev.QcZero.QCResults`: "Build completed successfully (2363 jobs)", no warnings.
- `#print axioms` of n0, qb_unpack, qb_deriv, qb_pos, qc_bij: each `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS (445 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK (144). It also prints "KAM.lean is out of date; run scripts/gen_root_imports.py" — expected: KAM.lean is generated and I did not edit it (new module QCResults, and earlier ones, need regeneration by the orchestrator).

**Uncertainties:** none. No heartbeat options, no file near cap, no provider/DRAFT_SORRY imports (imports only QcZero.Derivative).
**Suspected errata:** none. **Deviations:** none; signatures unchanged.

AUDIT FOCUS (design docs/tracks/N/design/N2-LEAN-DESIGN.md row N2-QC and proof plan; audit DESIGN-N2-design-audit-1.md; signatures .drafts/design/N2Signatures.lean; blueprint-N p2 qc-bijective nodes): (1) statements = design signatures and blueprint (n0, qb receipts, qc_bij); frozen QC predicate consumed, not restated; (2) proofs sound (uses isoenergetic_bijective_of_qc and N2-DERIV as designed); (3) hygiene (lint incl. 100-char lines). Audit ONLY the N2-QC module(s) listed in the handoff (compare with branch inp-n2d).
