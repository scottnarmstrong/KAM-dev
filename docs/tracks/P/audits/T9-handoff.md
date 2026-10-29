# T9 prover handoff (branch inp-p11c-t9, a0f6f39a; offloaded package run by the main orchestrator)


## Files (new)
KAM/Planetary/PlanarTorsion/QuarticFlow.lean (facade + `flow`, 135 lines);
QuarticFlow/{Field,Energy,Spec,Compact,Analytic}.lean (177/269/79/71/192 lines).

## Declarations
- `p11c_flow` (Spec.lean) and `flow` (QuarticFlow.lean): signature text verbatim except line wraps (100-col rule).
- Nodes `bpP:p11b:flow`, `fl-bd`, `fl-an`: all inside `flow` (no separate unsigned exports).
- `real_analytic_hamiltonian_local_flow` was R3's; not re-proved. Helpers are all `p11cQ_*`/`p11cQ_aug` (grepped: unused elsewhere).

## Approach
Field: chi.eval jointly analytic on O x Phase 2, homogeneous deg 4 => field homogeneous cubic, ‖X_I z‖ ≤ C0‖z‖^3 on compact K1 (compactness of K1 x sphere).
Energy: u=|z|², u' ≤ 8C0 u² (Riccati comparison with eps=u0/10 trick, zero datum by uniqueness); existence on [-1,1] via `gen_confinement`
when 32 C0 u ≤ 1; flow spec by ODE uniqueness (choice irrelevant).
Analyticity: K1=cthickening δ K, Ω=thickening δ K; augmented field (0,X_I(z)) on (Fin 2→ℝ)×Phase 2; R2 `p11c_analytic_flow_compact_nbhd`
transported to any finite-dim space (`p11cQ_flow_compact_nbhd`); time-one map = m-th iterate of time-1/m map, orbit stays in the compact set by the energy bound.
Inverse: -chi flow from w exists since 32C0u(w)≤1 (r chosen so 2r² ≤ threshold); uniqueness against t↦g(1-t) on [0,1].
Constants: C = 16 C0, r = sqrt(1/(64 C0)).

## Checks
- Gate build `KAM.Planetary.PlanarTorsion.QuarticFlow`: success (9157 jobs), no sorry.
- `scripts/lint_sources.sh`: ABI HASHES OK, passed.
- `#print axioms KAM.Planetary.flow`: [propext, Classical.choice, Quot.sound].
- No maxHeartbeats, no EuclideanSpace, lines ≤ 100.

## Uncertainties / deviations / errata
- Only line-wrapping of signature lines (>100 cols). No errata found. No heartbeat design signals.
- Built R2/R3 modules in this worktree were not in the snapshot; the gate built them (fine).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T9 (flow and compact-uniform cubic displacement/inverse; T7, R3, gen_continuation_compact) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. R2 was accepted by ruling 21:38 (compact analytic flow; Picard rates are the proof route); check T9 needs no more from R2 than that. Audit ONLY KAM/Planetary/PlanarTorsion/QuarticFlow*.lean and QuarticFlow/*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
