# P13-B prover handoff (branch inp-fx13b, bedcc6a9; contains P13-A and P12-C; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/FixedAssembly/TwoPlanet.lean` (~100 lines). No other file touched.

**Declarations:** `KAM.Planetary.FixedAssembly.n2` (bpP:p13:n2; steps n2-const, n2-pg, n2-mu, n2-S,
n2-tori, n2-phys), signature verbatim from P1213Signatures.lean. The graph nodes
`transport`, `tr-torus`, `tr-meas` map to the existing `PlanarAssembly.transport`, `measure`,
`measure_in_tube`, used here at the fixed Hamiltonian (no new declaration). `bpP:p13:quantifiers`
and `data#choices` are the constant choices inside `n2` (`radius_choices`, fresh fixed constants).

**Approach:** modelled on P12-E `PlanarAssembly.planar`. Eliminate `FixedAssembly.pg_hypotheses` once;
feed its data with the fixed perturbation to sealed `properlyDegenerateKAM` (a=b=2); choose
r = secular_radius, threshold = coupling_threshold r c (fresh, not the moving one); apply
`measure`, `measure_in_tube`, `transport` (G := fixedHamiltonian) and `fixedKolmogorovSet_of_tube`.
One private helper `cylinder_subset_of_le` (private, no name clash).

**Checks:** gate build `KAM.Planetary.FixedAssembly.TwoPlanet`: success, no warnings in my file.
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only
message is "KAM.lean is out of date" (generated file, not edited per rules).
`#print axioms KAM.Planetary.FixedAssembly.n2`: [propext, Classical.choice, Quot.sound].
Lines <= 100 columns; no heartbeat options.

**Uncertainties:** none. Imports `KAM.Frozen.Planetary.Theorems.ProperlyDegenerateKAM` (sealed P-G,
same as P12-E); no provider or DRAFT_SORRY anchor imported.

**Errata / deviations:** none.

AUDIT FOCUS: design docs/tracks/P/design/P1213-LEAN-DESIGN.md row P13-B (P13-A, D, SEALED P-G, P6-5 fixed assembly; new constants and fixed P-G application) and its node table (bpP:p13:n2 and n2-* steps, transport, tr-torus, tr-meas, quantifiers, data#choices); P1213 design audits; signatures /root/code/KAM-inp/.drafts/design/P1213Signatures.lean (FixedAssembly.n2). Check the fixed perturbation gets fresh constants and threshold (not the moving ones) and the sealed properlyDegenerateKAM is applied to the fixed data. Audit ONLY KAM/Planetary/FixedAssembly/TwoPlanet.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
