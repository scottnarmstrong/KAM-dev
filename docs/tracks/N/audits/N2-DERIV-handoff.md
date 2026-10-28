# N2-DERIV prover handoff (branch inp-n2d, 480b27e; contains inp-n2k (N2-KERNEL, audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- New: `KAM/Nekhoroshev/QcZero/Derivative.lean` (169 lines). No other file changed (KAM.lean untouched).

## Nodes proved (all in `KAM.Nekhoroshev`; signatures copied verbatim from N2Signatures.lean)
- `real_hessian_matrix` (def), `qd_first`, `qd_freq`, `qd_sym` (`stepN:p2:qd-*`), `qd_prod`, `qc_deriv` (`bpN:p2:qc-deriv`).

## Approach
Private lemmas: `hasFDerivAt_first`, `hasFDerivAt_freq` (frequency map derivative via `ContDiffAt.fderiv_right`,
`hasFDerivAt_pi`), `hasFDerivAt_prod` (`HasFDerivAt.smul`), `sym_hess` (C² Schwarz via `ContDiffAt.isSymmSndFDerivAt`),
`hess_apply` (Schwarz + `clm_apply_eq_sum`). `qd_freq` C¹ via `ContDiffOn.fderiv_of_isOpen` + CLM `apply`.
`qc_deriv` = `prodMk` of first/product derivatives, `congr_fderiv` to `bordered_map` by extensionality using
`bordered_map_apply`. Imports: QuasiConvex, QcZero.Kernel, Mathlib Symmetric (no providers/anchors).

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-n2d KAM.Nekhoroshev.QcZero.Derivative`: "Build completed successfully (2362 jobs)", no warnings.
- `#print axioms` (via `lake env lean`) for qd_first, qd_freq, qd_sym, qd_prod, qc_deriv: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS (440 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK (144).
  It also prints "KAM.lean is out of date; run scripts/gen_root_imports.py" (new modules Derivative, and Kernel from the
  merged N2-KERNEL): the orchestrator must regenerate KAM.lean (I did not edit it, per rules).

## Uncertainties / errata / deviations
None. No statement was changed or found wrong; no heartbeat or size issues (default heartbeats throughout).
`inp_sig_check.sh` only sees the main checkout's build, so axioms were checked with `lake env lean` in the worktree.

AUDIT FOCUS (design docs/tracks/N/design/N2-LEAN-DESIGN.md row N2-DERIV and proof plan; audit DESIGN-N2-design-audit-1.md; signatures .drafts/design/N2Signatures.lean; blueprint-N p2 qc-derivative nodes): (1) statements = design signatures and blueprint (matrix helper, qd receipts, qc_deriv); (2) proofs sound (C^2 Schwarz used correctly; consumes N2-KERNEL as designed); (3) hygiene (lint incl. 100-char lines). Audit ONLY the N2-DERIV module(s) listed in the handoff.
