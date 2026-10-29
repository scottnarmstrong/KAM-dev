# SO-DIO3 prover handoff (branch inp-sodio3, 20bb4306; track SO package run by the main orchestrator)


Files: new `KAM/Certificate/CubicDiophantine.lean` (~190 lines). Nothing else touched.

Declarations (signed names/types verbatim, namespace KAM.Certificate): `cbrtTwo`, `cubicFreq`,
`cubicFreq_eq_algFreq`, `cubicFreq_isDiophantine : IsDiophantine (1/12) 2 cubicFreq`
(`IsDiophantine` resolves to `KAM.IsDiophantine`). Private helpers: `cbrtTwo_cube`, `cbrtTwo_bounds`,
`norm_form_zero` (infinite descent mod 2), `norm_ne_zero`, `cubic_lower`.

Approach: with x = ∛2 and β = k₂ + k₀x + k₁x², β·Q = N (via x³ = 2, linear_combination), N the integer
norm form, N ≠ 0 by strong-induction descent; |Q| ≤ 6|k|₁² using 5/4 < x < 63/50; so |β| ≥ 1/(6|k|₁²),
and Σ kᵢωᵢ = β/2 gives the constant 1/12.

Checks:
- `inp_lake_build.sh ... KAM.Certificate.CubicDiophantine`: Built successfully, no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; only message
  "KAM.lean is out of date" (generated root, orchestrator regenerates; not edited).
- `#print axioms` of cubicFreq_isDiophantine and cubicFreq_eq_algFreq: [propext, Classical.choice, Quot.sound].

Uncertainties: none. Suspected errata/deviations: none. No heartbeat issues.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4, passed its design audit); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section J, the CubicDiophantine part (cbrtTwo, cubicFreq, cubicFreq_eq_algFreq, the Diophantine theorem for the cubic vector). Check the Liouville-type bound for Q(cbrt 2) is proved (norm form nonvanishing for nonzero integer triples, then the height bound) with the signed constants, and that IsDiophantine is the landed KAM definition used by the KAM theorems.

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/CubicDiophantine.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
