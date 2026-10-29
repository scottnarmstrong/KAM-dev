# SO-RAT prover handoff (branch inp-sorat, 9682cf5c; track SO package run by the main orchestrator)


**Files:** new `KAM/Certificate/Arith/Rat.lean` (~85 lines). Nothing else touched.

**Approach:** `instCertArithRat : CertArith ℚ` (val = cast, all ops exact incl. ofRatUp/Down/upAdd/upMul,
addErr = mulErr = 0, comparisons `decide (a ≤ b)` etc.) and `instLawfulCertArithRat`, both in
`namespace KAM.Certificate` as signed. Laws by `simp`/`decide` extraction. No heartbeat options.
Short names `instCertArithRat`/`instLawfulCertArithRat` were absent from KAM before (grep).

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-sorat KAM.Certificate.Arith.Rat`: "Built ... (2.0s)", success
  (only a pre-existing PiHigh unused-simp-arg warning).
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; it reports
  "KAM.lean is out of date" (generated file, not edited by me; orchestrator must regenerate).
- `decide +kernel` examples (all pass, whole file elaborates in ~2s):
  `ble (upAdd (ofRatUp 1/3) (ofRatUp 1/6)) (ofRatUp 1/2) = true`; same with 1/3+1/3 `= false` (control);
  `blt (upMul 2/3 3/4) 1 = true`; `beq (2 + -(4/2)) 0 = true`;
  `certCExpSmall ⟨1/4,1/4⟩ (1/4) = true`;
  `checkPiEnclosure ⟨(lo+up)/2, (up-lo)/2, 20, 5⟩ = true` and the half-radius control `= false`
  (Machin parameters (20,5)) — reduces in kernel quickly; no design signal.
- `#print axioms` (temporary, removed): `instCertArithRat` and `instLawfulCertArithRat` both depend on
  `[propext, Classical.choice, Quot.sound]` only.

**Uncertainties:** none; the checkPiEnclosure example uses (20,5), not the production (50,15).
No suspected errata, no deviations.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section A 'Backends' (instCertArithRat, instLawfulCertArithRat: exact rationals, val = cast, zero errors; moved pre-gate by design Revision 3 finding F6). Check every LawfulCertArith law is proved for the actual operations (no vacuous law), the rounding-direction operations are exact or correctly directed, and the decide +kernel examples (with false controls) really reduce in the kernel.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/Arith/Rat.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
