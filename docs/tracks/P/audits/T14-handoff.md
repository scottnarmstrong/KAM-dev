# T14 prover handoff (branch inp-p11c-t14, df340cc0; offloaded package run by the main orchestrator)


## Files
- NEW `KAM/Planetary/PlanarTorsion/Frame.lean` (183 lines, ≤100 cols). No other file touched (KAM.lean not edited).

## Declarations (signatures copied verbatim)
- `p11c_frame`, `global_planar_frame` (node `stepP:p11b:bt-rot` / `bt-rot#lift` frame part), `p11c_rotationLift`.
- `p11c_rotateSlow` (verbatim from the signature file; see DEVIATION below).
- Private-name-free helpers (all `p11c_` prefixed, short names unique in KAM): `p11c_Q_off_pos` (Q12>0, via
  Part-9 `pairB_pos` + `p11c_Q_eq_coeffs`), `p11c_frame_norm_pos`, `p11c_frame_eigen`, `p11c_axes_isOpen`,
  `p11c_Q_analyticAt`, `p11c_sigma0_analyticAt`, `p11c_frame_analyticAt`.

## Approach
Q12>0 ⇒ v=(-Q12,Q11-σ1)≠0 on the whole cone; v is a σ1-eigenvector (trace/det from `p11c_sigma_sum_prod`);
e=v/|v|, frame `!![e0,-e1;e1,e0]` has UᵀU=1, det=1 by e0²+e1²=1, and UᵀQU=diag σ by polynomial identities.
Analyticity: `SecularForm.coeffs_analytic` transported through `p11c_Q_eq_coeffs`, σ1 via analytic sqrt of
positive discriminant (Q12>0), then analytic sqrt/inverse/product. No angle, no covering space.

## Checks
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only message is
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, orchestrator regenerates).
- Gate build `inp_lake_build.sh … KAM.Planetary.PlanarTorsion.Frame`: "Built … Frame", build completed
  successfully, no sorry/warning from Frame.lean.
- `#print axioms global_planar_frame` and `p11c_rotationLift`: [propext, Classical.choice, Quot.sound].
- No set_option, no heartbeat issues, no EuclideanSpace.

## Deviation / orchestrator action needed
- `p11c_rotateSlow` is signed in the Beta (T13) block but T14's `p11c_rotationLift` needs it and T13 is not on this
  branch. I defined it verbatim in Frame.lean. T13 must NOT redefine it: on merge, T13 should import Frame (or the
  orchestrator moves the def; identical text, so a conflict is trivial to resolve).
- Imports Part-9 `SecularSpectrum` (via SpectralAdapter) and `SecularForm.Coefficients`; no provider/DRAFT_SORRY.

## Uncertainties / errata
None. No source defects found. `p11c_rotationLift` is a definition only (no theorem about it is signed for T14).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T14 (global_planar_frame, concrete rotationLift; T12, positive Q12/U9) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/PlanarTorsion/Frame*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
