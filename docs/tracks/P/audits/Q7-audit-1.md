# Q7 independent package audit

Verdict: **PASS WITH NOTES** for `KAM.Planetary.physical_interface`.
No frozen anchor is implemented or sealed by this package; seal readiness is not applicable.
The signed infrastructure theorem passes statement, proof and coverage review. The notes are
the permitted stale generated root and the already documented graph-scope discrepancy.

## Scope and authority

Audited HEAD `b3dc2a0cf2bf5fc0df5663cc71e6831c95b34ad9`, against local `inp`
`545882eddb1d26c472732a8b410554b75fe8ecf5`, using `git diff inp...HEAD`.
The complete 590-line diff was inspected: Physical plus inherited Q6 Assembly, AssemblyData,
and AssemblyTori (566 added lines total). Only
`KAM/Planetary/Quantitative/Physical.lean` is adjudicated here, as the handoff explicitly directs.
Those Q6 files are not silently included in this PASS. Physical imports Interface, not Assembly.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, Q7-handoff.md,
P11C-LEAN-DESIGN.md (Q7 and U1/U3), DESIGN-P11C-design-audit-1.md, the standalone
`/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`, track P statement conventions,
blueprint p11a5 L116–134 and the Part-13 consumer context. Inspected actual Interface,
Thresholds, IsLatticeTorus, unitCube, IsSolutionIn, Hamiltonian regularity and uniqueness,
and the frozen Phase, HamiltonianVectorField and ActionNbhd definitions.
No provider/frozen theorem is a Q7 target, so frozen-provider identity/seal probes do not apply.
The exact report destination follows the user's worktree-specific instruction over the generic brief.

Physical SHA-256:
`8f7d08c38d0454faa203850e45f6d78e5894d91b0042e48c96b162bf678cc6f1`.
Standalone signatures SHA-256:
`6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7`.

## Declaration and node review

All Lean names below are in `KAM.Planetary`; helper declarations are private.

| Node / declaration | Lean location | Verdict | Reason |
|---|---|---|---|
| `bpP:p11a:physical-interface` | `physical_interface`, Physical:59–161 | PASS | Exact signed premises, quantifier order, carriers, constants and thirteen conjuncts; fresh two-way type probes pass. |
| `stepP:p11a:pi-zero` | Same theorem, arbitrary `eps` | PASS | No positive-eps premise or positive-branch theorem is used. The proof applies uniformly to the zero family as well; constructing/identifying that family belongs to Q5/Q6. |
| `stepP:p11a:pi-a` | Physical:83–109, 123–124 | PASS | Valid gives strict loss < volume K; family measure and cell_lower yield the two lower comparisons. Upper bound has exact exponent 2N and constant `(1+2^-10)^(2N)`. Compact good set gives finite measure. |
| `stepP:p11a:pi-b` | Physical:125–126 | PASS | Witness in the half-open cell and exact displacement bound; its definition as a minimum supplies the absolute `2^-18` bound. |
| `stepP:p11a:pi-c` | Physical:110–130, 143–161 | PASS | Genuine all-real-time solutions remain in the actual real domain, are invariant in St, and have a compact set of lattice representatives. |
| `stepP:p11a:pi-c-uniq` (source companion) | Physical:128–130 | PASS | `gen_uniqueness` on arbitrary order-connected J containing zero, with C1 field derived from C2 Hamiltonian on an open domain. No assumed uniqueness. |
| `stepP:p11a:pi-d` | Physical:131–142, 153–161 | PASS | Equivariance and strictly positive lower Lipschitz factor imply b=b' even after lattice translation; both saturation inclusions are proved. |
| private helper | `volume_eq_hausdorff`, Physical:28–43 | PASS | Actual Pi/Prod max metric: sum-arrow isometry, measure-preserving coordinate rearrangement, and normalized top-dimensional Hausdorff measure. No Euclidean norm substitution. |
| private helper | `volume_image_lipschitzOn`, Physical:46–52 | PASS | Hausdorff Lipschitz image inequality with exponent 2N, valid for arbitrary A; no extra measurability premise. |
| private helper | `exists_fract_decomp`, Physical:55–57 | PASS | Componentwise floor/fract gives theta0 in `[0,1)^N` and an integer shift for every real angle, including negative and integral angles. |

There are no unsigned public exports named after graph nodes and no missing Q7 local fragment.
The uniform zero-size argument is a valid alternate proof organization, not a claim to have
constructed the zero family inside Physical.

## Signature, premises, definitions and consumers

The Physical header equals standalone L264–285 after whitespace normalization (the sole
formatting difference wraps a long lower-bound line). A scratch theorem copied the literal
standalone type under a fresh name and used
`exact physical_interface d hd H hH cDelta eps Q`. Both directions of
`example : type_of% @... := @...` elaborated at default resource limits.

There are **no new def/abbrev/structure declarations**, instances, global notation or root names
in Physical. The three private declarations are propositions about the actual objects on their
whole carriers; none installs a fallback or alternative representation.

`Q : QuantitativeFamily ...` is the signed, already-constructed output consumed by this
corollary. Its fields are not illicit assumptions replacing the KAM existence proof: Q7 does
not claim weak_kam_quantitative, and Q6 owns producing Q from A1–A4. Likewise the C2
Hamiltonian premise is explicitly signed and supplies the regularity needed for uniqueness.
No additional premise, constant dependence, or hidden conclusion-shaped instance was added.

The signed theorem packages fewer facts than the full prose corollary, as designed. It retains
Q for consumers: the intermediate measure comparison is `Q.measure` plus `Q.cell_lower`;
Diophantine frequency and analytic/immersed/Lagrangian properties are `Q.dio` and `Q.lattice`;
`Q.subset` and the min in displacement give the action-distance statement. The positive lower
Lipschitz factor proves injectivity of joint evaluation; equivariance then identifies the
quotient fibers. The compact representative set proves quotient compactness after applying
any continuous lattice quotient map. No quotient type or chart-specific physical conclusion
is falsely claimed to have been constructed in this module.

The domain proof uses the open preimage of `actionNbhd K (2*vartheta)` and the range clause
of IsLatticeTorus at every shifted angle. It does not compare `2^-18` to vartheta or evaluate
an unguarded Hamiltonian derivative. The Hausdorff argument uses the correct product order
`(theta,b)` throughout; Q.upper has this exact order, so no unproved swap is required.

Current project-wide search finds only this declaration/docstring for `physical_interface`:
there is no existing Lean consumer with an unmet stronger signature. In the blueprint,
Part 13 L139 consumes the wrapper and L200 lists physical-interface administratively;
its actual physical chart/whole-torus transport remains downstream. This audit establishes
the signed interface, not the Part-13 assembly or any track headline.

## Checks and exact receipts

All Lean/Lake/checker invocations were serialized with `LEAN_NUM_THREADS=1`; Lean/Lake
commands ran at niceness 5. No clean/update/cache operation or heartbeat override was used.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-q7 KAM.Planetary.Quantitative.Physical`

   Exit 0. Gate receipt: `[inp-gate] slot 3 acquired 01:05:45 for KAM.Planetary.Quantitative.Physical`.
   Final output: `Build completed successfully (9124 jobs).`
   Replayed upstream unused-variable warnings: Hamiltonian/Algebra:146 (`hc`), Chart:193 (`hc`),
   Diophantine:124 (`hγ`), Transport:55 (`hc`). No warning in Physical.

2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Q7Audit.lean`

   Exit 0; exact standalone-type copy and both type identity examples passed. Output:

   ```text
   'KAM.Planetary.physical_interface' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   This is every new public theorem/export (one). No `sorryAx`.

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.Physical`

   Exit 0. Complete output:

   ```text
   replaying KAM.Planetary.Quantitative.Physical
   ```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`

   Exit 1, solely the explicitly permitted stale generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1185 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`

   Empty output (0 bytes). `git diff --check inp...HEAD`: exit 0, empty output.
   Physical has 163 lines, maximum 98 Unicode columns; correct copyright/module/public-import/
   module-docstring/public-section structure. No forbidden token, resource override,
   EuclideanSpace, reused public helper short name, or harmful root shadow.

6. Recursive inspection of all project imports (78 modules including Physical): no provider
   module and no frozen theorem module, hence no imported DRAFT_SORRY theorem. Frozen
   imports are definitions; no theorem manifest-state exception is needed.

Scratch probe was removed after validation. Only this report was written in repository source/docs;
the pre-existing untracked Q7-handoff.md was preserved. Build/cache artifacts and temporary
logs are verification outputs. No git mutation was performed.

## Notes, suspected defects, deviations and limits

- **Graph scope / provenance note:** P11C-LEAN-DESIGN.md:150 says physical-interface is
  “absent from the supplied 83-node graph slice” and directs reporting the discrepancy.
  Confirmed absent from current DEPGRAPH and P-p11a45 node packet. This is explained by
  `docs/graph/P/reviews/P-p11a45-delta.md:718–746` (“Delete each ... eight complete NODE
  blocks”) and :1085 (“outside every root closure ... only the Part 13 L200 administrative
  forward reference”). Thus absence is documented graph exclusion, not a missing Q7 proof.
  The same graph review preserves uniqueness as SOURCE_GAP if restored; the present Lean
  theorem now proves its signed uniqueness clause, but this audit does not edit graph status.
- **Generated root:** permitted lint exception only; root was not regenerated.
- No newly suspected mathematical defect in the pinned blueprint/source, no frozen-statement
  defect, and no auditor-introduced statement deviation. The quote-backed graph note above
  is administrative and should not be reported as a new source erratum.
- This is an independent package check of the signed Q7 consequence theorem. It does not
  recertify upstream proofs, inherited Q6, frozen anchors, graph integration or a physical KAM headline.
