# T21 prover handoff (branch inp-p11c-t21, e743c7e4; contains T20 round 1 (fixing: T20b), T16 (passed), T19; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/PlanarTorsion/Patch.lean` (191 lines). No other file touched (KAM.lean not edited).

**Declarations (signed, verbatim):** `p11c_combinedFrequency`, `PlanarFrequencyPatch`, `patch`;
`torsion_patch_geometry` (signed helper) is proved as a projection of `patch`.
Node `bpP:p11b:patch` -> `patch`. Public helpers (unique `p11cPa_` prefix, grepped): `p11cPa_action_eq`,
`p11cPa_axis_eq`, `p11cPa_axes_actions`, `p11cPa_freq_eq`, `p11cPa_euclid`, `p11cPa_unit`, `p11cPa_jet_attain`.
P1213 row P12-C consumes `patch` / `PlanarBirkhoffResult` exactly as signed.

**Approach:** apply upstream `Nondegeneracy.interface` (D = `p11cSecularData`) to f = ![phi4, det beta]
(analytic + nonzero somewhere by T20 lemmas `p11cGe_*`). `remain` (T17) gives B on the compact inner ball;
symmetry from `beta_properties`; `birkhoff_form` (T16) applied with Oa = ball a0 (2r). The frequency patch is
transported from `frequency D` to `p11c_combinedFrequency` (equal on action images via `p11c_sigma_eq_sigma`).
Finite type: from `betaMu` monotonicity (`hmono`), beta := beta_interface/2, with `jetMax` > beta/2 attained by some j<=mu and
unit v (`p11cPa_jet_attain`); order-0 case uses any unit vector. Nonresonance: interface's k4 clause.

**Checks:** `inp_lake_build.sh ... KAM.Planetary.PlanarTorsion.Patch` -> "Build completed successfully (9361 jobs)", no warnings
in Patch.lean. `#print axioms patch` and `torsion_patch_geometry`: [propext, Classical.choice, Quot.sound].
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only message "KAM.lean is out of date"
(expected: generated root not edited; orchestrator regenerates). No maxHeartbeats, lines <= 100, file 191 lines.

**Uncertainties / errata / deviations:** none. Note `patch` uses `Nondegeneracy.interface` (not `interface_stability`),
which suffices; stability consumption is downstream. No heartbeat design signals.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T21 (geometry helper and full patch; T20/T16/T17, U10 interface) and its node table incl. bpP:p11b:patch; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean (p11c_combinedFrequency, PlanarFrequencyPatch, patch, torsion_patch_geometry). Check that the patch is exactly what docs/tracks/P/design/P1213-LEAN-DESIGN.md row P12-C consumes ('11b patch'), that the upstream Nondegeneracy.interface is applied to the actual p11cSecularData, and the finite-type / nonresonance clauses. T20's fix round (nonzero-locus bridge for p11c_phi4) is append-only: note whether T21 depends on that bridge. Audit ONLY KAM/Planetary/PlanarTorsion/Patch.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
