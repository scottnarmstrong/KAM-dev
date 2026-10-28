# Handoff N2-ZORBIT

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
