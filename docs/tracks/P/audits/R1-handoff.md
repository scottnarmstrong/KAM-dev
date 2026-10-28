# R1 prover handoff (branch inp-p11c-r1, e1a6d79d; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/PlanarTorsion/RealFlow/Local.lean` (~95 lines).

**Important finding (design gap):** neither `P11CSignatures.lean` nor the design row/node table names any
declaration for R1. The only R1-related signature is `real_analytic_hamiltonian_local_flow` (node
`bpP:p11b:e-ode`, R1-R3), whose proof belongs to R3 (analyticity, symplecticity). No graph proof step is
mapped solely to R1 (`fl-bd`/`fl-an` are T9). So nothing could be copied verbatim; I wrote helper
declarations from the R1 summary, with new names (grepped unique, `p11c_` prefix), none changing a signature:
- `p11c_hamField_contDiffOn` (C² H ⇒ C¹ Hamiltonian field on open W)
- `p11c_hamField_contDiffOn_of_analytic`
- `p11c_local_flow_uniform`: compact K ⊆ W: δ, M, ε, L; thickening compact in W, field bound M, Lipschitz,
  uniform-time solutions staying δ-close (from `gen_uniform_compact`, `gen_uniform_exist`)
- `p11c_local_flow_compact` (from `gen_local`), `p11c_maximal_flow` (from `gen_maximal`, existence+uniqueness)

**Checks:** gate build `KAM.Planetary.PlanarTorsion.RealFlow.Local` succeeded (no sorry, no warnings shown);
`#print axioms` of all four main results: propext, Classical.choice, Quot.sound. Lines ≤ 100 (checked by awk).
Lint: scripts/lint_sources.sh exits 1 ONLY with "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module not in the generated root; I must not edit KAM.lean, orchestrator regenerates). All other checks PASS (check_lean_modules, frozen guard, ABI hashes).

**Uncertainties:** whether the orchestrator wants these exact helper shapes for R2/R3/T9; adjust if the
signature file is later extended. No errata, no deviations, no heartbeat issues.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row R1 (RealFlow/Local) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. The handoff says bpP:p11b:e-ode's proof belongs to R3: confirm against the node table. Audit ONLY KAM/Planetary/PlanarTorsion/RealFlow/Local.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established; an exported lemma named after a graph node must state that node's literal conclusion; steps the design keeps internal may stay internal; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public helper short name, no root shadow, lines <= 100.
