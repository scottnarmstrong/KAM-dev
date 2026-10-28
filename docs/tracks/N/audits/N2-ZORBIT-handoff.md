# N2-ZORBIT prover handoff (branch inp-n2o, f25b8f9; contains inp-n2z (N2-ZFIELD, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/QcZero/ZeroOrbit.lean` (~85 lines). No other file touched (KAM.lean not edited).

**Declarations (verbatim signatures from N2Signatures.lean):** `z_init`, `z_ball`, `z_h`, `z_curve`, `z_eq`, `zero`
(namespace `KAM.Nekhoroshev`). Note: `z_ball` takes `hR I0 hI` (theta0 omitted by the `omit`s, as in the signature file).

**Approach:** `z_init`: simp + rfl. `z_ball`: norm arithmetic. `z_h`: I0 in ball R, hence in ball (R+s) (so orbit in
`Wdom`), differentiability from `zero_deriv` (N2-ZFIELD). `z_curve`: affine `HasDerivAt` (`smul_const`, `const_add`,
`prodMk`). `z_eq` and `zero`: taken from `zero_perturbation_core` (as the design plans). `z_h`/`z_curve` are
receipts and are not used by `z_eq`/`zero`.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n2o KAM.Nekhoroshev.QcZero.ZeroOrbit`: Built successfully, no warnings, no sorry.
- `sh scripts/lint_sources.sh`: line-length, module, frozen-anchor and ABI checks PASS. Only message: "KAM.lean is out of
  date; run scripts/gen_root_imports.py" (expected: KAM.lean is generated, not edited by me; orchestrator regenerates).
- `#print axioms` of z_init, z_ball, z_h, z_curve, z_eq, zero: only `propext`, `Classical.choice`, `Quot.sound`.

**Imports:** `KAM.Nekhoroshev.QcZero.ZeroField`, `KAM.Nekhoroshev.ZeroPerturbation` (no provider or DRAFT_SORRY anchor).
**Uncertainties / design signals:** none (no heartbeat issues). **Suspected errata / deviations:** none.

AUDIT FOCUS (design docs/tracks/N/design/N2-LEAN-DESIGN.md row N2-ZORBIT and proof plan; audit DESIGN-N2-design-audit-1.md; signatures .drafts/design/N2Signatures.lean; blueprint-N p2 zero-orbit nodes): (1) statements = design signatures and blueprint (z receipts, z_eq, zero); frozen orbit/solution predicates consumed, not restated; (2) proofs sound (uses zero_perturbation_core and N2-ZFIELD as designed); (3) hygiene (lint incl. 100-char lines). Audit ONLY the N2-ZORBIT module(s) listed in the handoff (compare with branch inp-n2z).
