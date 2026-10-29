# T20 prover handoff (branch inp-p11c-t20, 2b0a2707; contains T19 (passed) and T16 (in audit); offloaded package run by the main orchestrator)


## Files
- `KAM/Planetary/PlanarTorsion/Generic.lean` (new, ~140 lines): `torsion` (verbatim signature) and
  helpers `p11cGe_sigma1_analyticAt`, `p11cGe_phi4_analytic`, `p11cGe_axes_eq`,
  `p11cGe_phi4_exists`, `p11cGe_det_analytic`, `p11cGe_det_neg`.
- `KAM/Planetary/PlanarTorsion/Phi4.lean` (new): the signed def `p11c_phi4`, verbatim.

## Nodes
`bpP:p11b:torsion` -> `torsion`; steps to-an (`p11cGe_det_analytic`, from the existing
`beta_properties` in Beta.lean, T13), to-pt (`p11cGe_det_neg`, via `asymptotics_uniform_ratio`
with ratio m0/m1 and a small t), to-id (`Nondegeneracy.generic`, r=1 and r=2, on connected
`p11c_axes` = upstream `axes 2`). `p11c_phi4 != 0` somewhere via upstream `good_point` (nr4),
`p11c_sigma_eq_sigma`. `beta_properties` already proved in T13 (not duplicated).

## Approach
Analytic determinant; negative point from the -117/16 asymptotic; `generic` for open/dense/null.

## Checks
- Gate build `KAM.Planetary.PlanarTorsion.Generic`: success (only pre-existing warnings upstream).
- `#print axioms torsion`: propext, Classical.choice, Quot.sound.
- `scripts/lint_sources.sh`: PASS; only "KAM.lean is out of date" (generated; new module Phi4 /
  Generic need `gen_root_imports.py` by the orchestrator). No lines > 100 columns.

## Uncertainties / deviations (ACTION NEEDED by orchestrator)
- **`p11c_phi4` duplicate**: signed def `p11c_phi4` is on branch `inp-p11c-t16`
  (`Birkhoff/Defs.lean`) but not on this branch (T16 unmerged). To avoid importing T16 I put the
  identical def in the new leaf module `PlanarTorsion/Phi4.lean`. When landing, T16's
  `Birkhoff/Defs.lean` must drop its copy and `public import KAM.Planetary.PlanarTorsion.Phi4`
  (otherwise duplicate declaration). Bodies are character-identical.
- No errata found. No heartbeat issues.
- Orchestrator change (00:05): Phi4.lean removed; Generic imports the signed p11c_phi4 from T16's Birkhoff/Defs (merged inp-p11c-t16; identical definition, avoids a duplicate declaration).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T20 (torsion; T19, U9 analytic null set, U10 good_point/generic) and its node table incl. to-an, to-pt, to-id; design note line 187 (p11c_phi4 is a nonzero-locus adapter: check the locus bridge is proved, not assumed); P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean (torsion). p11c_phi4 is T16's (Birkhoff/Defs, in its own audit). Audit ONLY KAM/Planetary/PlanarTorsion/Generic.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
