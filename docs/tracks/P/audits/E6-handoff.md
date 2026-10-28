# E6 prover handoff (branch inp-p14-e6, 187e5d7c; off inp (E5 on inp); offloaded P14 package run by the main orchestrator)


Files: new `KAM/Planetary/Exponential/ComplexTube.lean` (281 lines). No other file touched.

Declarations (signatures verbatim): `real_trace_identity`, `periodicOrbitSet`, `complexTube`, `tube`.
Helpers (new names, grepped unused): `e5Pack_unpack`, `norm_realInclusion_sub_le`, `complexifyPhase_add`,
`complexifyPhase_sub`, `norm_complexifyPhase`, `fastShift_add`, `exists_glue`, `exists_pos_le_half`, `mem_ball_shift`.

Approach: `real_trace_identity` transports to `Fin (d+d) → ℂ` via the isometric `e5Pack`/`e5Unpack` (E5) and applies
the existing `real_slice_identity` (PGAssembly/RealSlice) on the convex ball intersection, with V = real points
mapping into the intersection (nonempty via componentwise real part). `tube`: local complexification (E5) at each
x ∈ K, shrunk so the real ball lies in W; finite subcover of K by half-radius balls gives uniform ρ; branches
indexed by K × ℤⁿ (centre x + fastShift k, g x (z - c(fastShift k))) glued by `exists_glue` (using
`real_trace_identity`, real-trace values from periodicity); holomorphy, real trace/W-membership, and shift
periodicity checked directly. Empty K handled (ρ = 1).

Checks: gate build `KAM.Planetary.Exponential.ComplexTube` succeeded (only a deprecation warning: `dif_pos`
in `exists_glue`). `scripts/lint_sources.sh`: module/frozen/ABI checks PASS; only message is "KAM.lean is out of
date" (generated file, not edited per rules). `#print axioms real_trace_identity` and `tube`:
[propext, Classical.choice, Quot.sound].

Uncertainties: none; no heartbeat issues (build 11s). No errata, no deviations; all signatures proved as stated.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row E6 and its proof plan; P14 design audits; signatures /root/code/KAM-inp/.drafts/design/P14Signatures.lean): (1) real_trace_identity, periodicOrbitSet, complexTube, tube = signature file EXACTLY, and the E6 slice COMPLETE (read the design row and proof plan line by line; a sibling package failed for an omitted proof-plan obligation); (2) definitions mean the source objects on their whole carriers; (3) proof soundness: transport via e5Pack/e5Unpack, the uniform radius from the finite subcover, the gluing over K x Z^n (exists_glue) and its consistency via real_trace_identity and periodicity; no added premises; (4) hygiene: no EuclideanSpace; no public short name already used elsewhere in KAM (the duplicate helper fastShift_add was removed by the orchestrator in favour of the general KAM.Planetary.fastShift_add in PGAssembly/ExtensionTubeP, now imported: check the import is acceptable; also check the generic helper names exists_glue, exists_pos_le_half, mem_ball_shift); no root shadow. Audit ONLY KAM/Planetary/Exponential/ComplexTube.lean.
