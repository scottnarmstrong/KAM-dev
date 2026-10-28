# S7 prover handoff (branch inp-p14-s7, 0d90d6d7; contains S6 (in audit), S5, S3, S2, S1, S0, S4 (passed); offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/SecularBox/Field.lean` (244 lines, max line <= 100). No other file touched.

## Declarations (signatures verbatim)
`sb_omega`, `reducedSecularH`, `sb_pred` (steps sb-pr-1/2), `sb_field` (sb-fd-1/2),
`secular_field_components`. Private helpers are all `sbField_*` / `sbFieldEmb` (unique names in KAM).

## Approach
- sb_pred: differentiability of H on the open set S (sb_s + sb_smooth_prop.1), then both directions
  are the same derivative clause. (ODE `ham_reduction` does not apply: it needs univ x U in W.)
- sb_field: (1) lambda-invariance (sb_smooth_prop.2.2) along the line w + s e_lambda_i gives
  d_lambda_i H = 0; (2) derivative of g(theta) = H(secularRotation theta w) = 0 at 0 (sb_rot),
  expanded in the coordinate basis.
- secular_field_components: first part is Fin.append(single) = single(castAdd); second part by chain
  rule with the affine embedding of the slow block, using lambda-invariance to replace the point
  assemble I 0 .. by w + L(y - y0).

## Checks
- `lake env lean` on the file: no errors or warnings.
- Gate: `inp_lake_build.sh ... KAM.Planetary.SecularBox.Field` -> Build completed successfully (9110 jobs).
  (Rotation also had to be built first through the gate; it was not in the snapshot.)
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only
  message is "KAM.lean is out of date" (generated; not edited per rule 10).
- `#print axioms` of sb_pred, sb_field, secular_field_components: [propext, Classical.choice, Quot.sound].

## Uncertainties / errata / deviations
None. No heartbeat issues; no set_option; no sorry. No suspected errata in pinned sources.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S7 (sb_omega, reducedSecularH, sb_pred, sb_field; secular_field_components deferred here from S5) and its node table; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean (~lines 381-495). (a) every SIGNED declaration = signature file EXACTLY; definitions mean the source objects on their whole carriers; (b) the slice COMPLETE: every graph node mapped to Field established (in the proof or as an export); an UNSIGNED export named after a graph node states its literal conclusion; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100. Audit ONLY KAM/Planetary/SecularBox/Field.lean.
