# S6 prover handoff (branch inp-p14-s6, 248a8e8b; offloaded package run by the main orchestrator)


Files: new `KAM/Planetary/SecularBox/Rotation.lean` (188 lines). No other file touched.

Declarations: `KAM.Planetary.sb_rot` (signature verbatim, bpP:p14:sb-rot). Internal private steps:
sb-rot-1 `sbRot_mem`; sb-rot-2 `sbRot_moving` (movingHamiltonian invariant under a common
rotation); sb-rot-3 `sbRot_explicit` (explicit integrand of w^theta = integrand of w at F - theta);
sb-rot-4 `sbRot_box_shift` / `sbRot_pi_shift` (shift of a continuous coordinate-periodic function
over [0,2pi]^2 via finTwoArrow, setIntegral_prod, Function.Periodic.intervalIntegral_add_eq).
Uses sb_cov, secular_integrand_identity, secular_integrand_smooth (continuity + periodicity).

Checks: `inp_lake_build.sh ... KAM.Planetary.SecularBox.Rotation` -> "Build completed successfully",
no warnings. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI OK;
it only reports "KAM.lean is out of date" (generated; not edited by me).
`#print axioms KAM.Planetary.sb_rot`: [propext, Classical.choice, Quot.sound].

Uncertainties/errata/deviations: none. No heartbeat issues; no frozen files touched; S3 radicand
fix not needed (did not merge inp-p14-s3).

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row S6 (sb_rot) and its node table; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean line ~466. Audit ONLY KAM/Planetary/SecularBox/Rotation.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
