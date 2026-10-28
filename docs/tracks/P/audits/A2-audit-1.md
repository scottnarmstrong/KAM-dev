# A2 independent package audit 1

**Overall verdict: PASS WITH NOTES. A2 is complete for its assigned helper slice.**
Audit date: 2026-10-28. No mathematical or statement-fidelity failure found. The notes concern the permitted stale generated root, existing dependency warnings, and the scope of this helper package. No frozen anchor is proved or seal-ready through A2 alone; provider/frozen-type and frozen-seal probes are inapplicable because this package introduces no provider or anchor body.

## Scope and authority

Worktree: `/root/code/KAM-inp-p14-a2`; HEAD `3b012b2dbccaabef5d481a68cb17ac359c13592a`; comparison `inp` at inspection: `cbc738ce2a4017c3c06bf565c99f028ec013fcd2`.
`git diff inp...HEAD` adds only `KAM/Planetary/AMD/Geometry.lean` (231 lines). SHA-256: `443c77d25362642496fc74855909d1624e5d897afe980b267a9df4a7cbc17bda`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/P/audits/A2-handoff.md`. The user's exact report destination overrides the generic brief's main-worktree destination. Reviewed the A2 module, imported A0/A1 contracts and definitions, relevant frozen definitions and the AmdConfinement target, track-P statement §D25 (especially lines 472–526), blueprint-P/parts/p14a-amd-expsafe.tex:75–90, P14-LEAN-DESIGN.md node rows, package rows 366–369 and Appendix A:697–712, and both design audits in `docs/tracks/P/design/`.

The untracked signatures are at `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, not in this worktree. Their SHA-256 at inspection is `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`. Both A2 theorem headers are text-identical to that file (lines 174–189) and Appendix A, including binder order, implicit n and z, all conjunctions, strictness, masses, physical lengths, constants, and the unrestricted mu quantifier.

## Declaration and node ledger

All names below are in `KAM.Planetary`; the first three declarations are private.

| Node / declaration | Lean declaration and location in Geometry.lean | Verdict | Reason |
|---|---|---|---|
| Continuity supplier | `continuous_planeLength_aux`, line 36 | PASS | Finite sum of squares and continuous square root on the whole plane. |
| Coordinate supplier | `continuous_bodyVector_aux`, line 41 | PASS | Continuous coordinate selection on the prescribed Pi carrier. |
| Barycentric pair supplier | `pairBounds_bary`, line 46 | PASS | Sun/planet and planet/planet cases cancel the common translation; triangle bound gives 2R. No positive-mu premise is needed. |
| `bpP:p14:geometry`, `geo-a` | `geometry`, line 74 | PASS | A1 ecc_bound with B.outerAMD and B.ecc, and the action-square identity give the exact strict axis/eccentricity bounds. |
| `geo-b` | `geometry`, lines 110–132 | PASS | A1 radial bounds and admissible annuli give distance ≤ radius ≤ B.radius. Elementary axis/eccentricity radial inequalities remain available from A1 elements under hz.1 i. |
| `geo-c` | `geometry`, lines 152–171 | PASS | Admissible ordered annuli and reverse triangle inequality cover both index orders. Exports compact membership, NoCollision, and all barycentric pair bounds including the Sun. |
| `geo-d` | `geometry`, lines 134–151 | PASS | Negative-energy momentum-square bound and r≥d give strict mass times sqrt(2/d). |
| `geo-k` | `amd_compact`, line 174 | PASS | Closed intersections, coordinate boundedness, finite-dimensional properness, and d>0 prove compactness and collision-free inclusion. |

The A2 slice is complete. P14-LEAN-DESIGN.md:366–369 assigns region definitions to A0, precisely geometry and amd_compact to A2, and closure/negative-energy continuity to A3. No closure claim is made here. The blueprint's elementary radial clauses are supplied by the imported A1 theorem, consistently with design-audit-2's geometry row; a scratch example independently elaborated their recovery from outer-region membership. The stated geometry is additionally valid for arbitrary natural n, rather than requiring the blueprint's standing n≥2. This is a harmless strengthening; Fin-empty cases introduce no false nonemptiness claim.

## Definitions, premises, and proof review

There are **no new def, abbrev, structure, or instance declarations** in A2. Its three private helpers are proved theorems, not assumed data. A0's amdOuter/amdInner are literal LowAMDRegion wrappers; amdCollar is the stated stopped-bound subset; amdCompact is exactly the non-strict geometric set K1. A2 neither redefines nor changes them. The compact set carries no ellipticity premise, and its proof correctly uses only its geometric inequalities.

The assumptions are exactly B.Admissible and outer membership for geometry, and B.Admissible for compactness. Neither assumes a desired conclusion. Action denominators are justified by positive masses, radial denominators by prograde ellipticity/d>0. The eccentricity estimate uses the actual physicalAMD from hz; the momentum estimate uses the actual body momenta. Barycentric positions are the frozen definition, and the common translation cancels even when Lean's total division takes its zero-denominator value. This does not assert any physical reconstruction at such masses or mu.

For boundedness, finProdFinEquiv surjectivity reaches every flattened coordinate, coordinate absolute value is bounded by the Pi norm and then physical planeLength, and the momentum sum bounds each nonnegative momentum ceiling. The resulting max bound is valid also for n=0. Closedness imposes every distinct pair, not merely adjacent or ordered pairs. Collision-free inclusion uses the same frozen NoCollision as collisionFreeDomain.

Recursively inspected the 56 KAM modules in this module's import closure: no provider and no frozen theorem is imported. Thus there is no DRAFT_SORRY or sealed-theorem import needing a manifest-state exception. Frozen imports are definitions. Only two new public theorem names are introduced. Searches across KAM find no existing `KAM.Planetary.geometry` or `KAM.Planetary.amd_compact`; `KAM.Apost.geometry` is a distinct existing name, as recorded in the handoff.

## Independent validation

All Lean/Lake/checker invocations were sequential, with LEAN_NUM_THREADS=1 and nice -n 5. The targeted build used the prescribed compile gate; its initial slot wait was respected. No resource override, clean, cache download, broad library rebuild, git mutation, or production edit was performed.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-a2 KAM.Planetary.AMD.Geometry
[inp-gate] slot 1 acquired 15:46:44 for KAM.Planetary.AMD.Geometry
⚠ [9098/9102] Replayed KAM.Kepler.Energy
warning: KAM/Kepler/Energy.lean:106:35: Variable name `hm` is not explicitly referenced.
warning: KAM/Kepler/Energy.lean:106:48: Variable name `hκ` is not explicitly referenced.
Build completed successfully (9102 jobs).
exit 0
```

The two dependency warnings have the standard unused-variable hints. No Geometry warning was emitted; the job count includes replayed dependencies.

### Exact signatures, application bodies, and axioms

Created `.lake/abi-scratch/A2AuditProbe.lean` importing only KAM.Planetary.AMD.Geometry. Copied both exact signature headers from the original signature file under fresh names, supplied `by exact geometry B hB hz` and `by exact amd_compact B hB`, and checked type_of% assignments in both directions. No admitted design module was imported. Also elaborated the elementary radial inequalities from elements and outer membership.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/A2AuditProbe.lean
'KAM.Planetary.geometry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amd_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The supplemental radial example had one unused hB warning at probe line 40; the production declarations and exact-signature checks passed. The probe is removed after validation.

### Kernel replay and lint

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.AMD.Geometry
replaying KAM.Planetary.AMD.Geometry
exit 0
```

This is the sole new lemma module; there is no provider module to add to this invocation.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (777 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the explicitly permitted stale generated root. No regeneration was performed. The forbidden-token, file-size, line-length and errata checks emitted no failures. Module, frozen-anchor and ABI checks all passed.

Static checks:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check inp...HEAD
(no output; exit 0)
rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/AMD/Geometry.lean
(no matches; exit 1)
wc -l KAM/Planetary/AMD/Geometry.lean
231 KAM/Planetary/AMD/Geometry.lean
```

The source has the copyright header, module command, public imports, module docstring, and public noncomputable section. It introduces no new definition requiring an exposure annotation. Whole-carrier ambient coordinates are Fin n → ℝ, with physical lengths represented by planeLength. Final report validation includes whitespace and balanced-fence checks, including the untracked report content.

## Findings, uncertainties, errata, and deviations

No suspected source or blueprint defect, no changed frozen premise, and no new mathematical deviation were found in the audited slice. No new pinned-PDF verification was needed for these algebraic/topological nodes; the comparison is against the local blueprint, signatures, literal frozen objects, and implemented proofs. This audit does not establish the future closure/ODE/continuation assemblies or seal P-AMD-CONFINEMENT, P-EXP-SAFE, or another frozen anchor.

Only this report is added by the audit; the pre-existing untracked A2-handoff.md is preserved. Temporary audit probes are deleted. The generated root and frozen files remain untouched.
