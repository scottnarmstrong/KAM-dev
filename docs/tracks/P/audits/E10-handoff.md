# E10 prover handoff (branch inp-p14-e10, 4db06f49; offloaded package run by the main orchestrator)

Files: new KAM/Planetary/Exponential/Hamiltonian.lean (only).
Declarations: `hnu` (verbatim signature; nodes bpP:p14:hnu, stepP:p14:hn-eq); `fderiv_eq_of_eqOn_open`,
`hamiltonianVectorField_eq_of_eqOn_open` (stepP:p14:hn-field, local fderiv equality on open sets);
`hamiltonianVectorField_neg`, `degenerateHamiltonian_neg` (signs); `workingCylinder_subset_enlargedCylinder`.
`planetaryKeplerC` already in Exponential/Setting (E-package), `degenerateHamiltonian` frozen: imported, not redefined.
Approach: working ⊆ enlarged ⊆ chartSafe (real_domain); movingHamiltonian_poincareProd; realPart_planetaryKeplerC;
B0 ≠ 0 cancellation. Open-set statements are for generic open U; openness of V={Λ∈G,(ξ,η)∈D} is E11's.
Checks: gate build of KAM.Planetary.Exponential.Hamiltonian OK (no warnings from my file); lint_sources.sh:
check_lean_modules PASS, frozen guard OK, ABI OK; only complaint "KAM.lean is out of date" (generated, not edited)
and a pre-existing >100-col line in Frozen AmdConfinement. No line >100 in my file.
#print axioms hnu, hamiltonianVectorField_neg: propext, Classical.choice, Quot.sound.
Uncertainties: none. Errata/deviations: none. Heartbeat design signals: none.

AUDIT FOCUS: design docs/tracks/P/design/P14-LEAN-DESIGN.md row E10 (hnu, local fderiv equality, signs) and its node table; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean line ~353. Audit ONLY KAM/Planetary/Exponential/Hamiltonian.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public helper short name, no root shadow, lines <= 100.
