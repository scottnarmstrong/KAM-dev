# T1 independent package audit 1

Audit date: 2026-10-28. Scope: only `KAM/Planetary/PlanarTorsion/Setting.lean` (62 lines), P11C T1. Comparison: `git diff inp...HEAD`, HEAD `9f93390057ade69dce2ee68e54ea273c947dd543`, inp `7ec42a1dd0f6154a1f6a357ba53d92080b367082`. The comparison adds only this module. The pre-existing untracked `T1-handoff.md` was read and left unchanged.

## Verdict

**PASS WITH NOTES** (definitions package accepted; all required checks completed, with only the permitted generated-root lint exception). T1 is a definitions package: no provider export, theorem proof, frozen-anchor seal, torsion result or physical Birkhoff theorem is delivered or certified. Provider/frozen type equality and seal-body probes are consequently not applicable.

Read authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T1-handoff.md and its AUDIT FOCUS, P11C-LEAN-DESIGN.md (T1, U2, Appendix A), DESIGN-P11C-design-audit-1.md, `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`, blueprint P Part 11b setting L14–16 and quartic L100–109, relevant Parts 7/8 coordinate/model interfaces, track P statement, and the actual frozen Phase/Assemble/SecularAverage definitions. The user's exact worktree report destination overrides the generic brief's MAIN-worktree destination.

## Declaration fidelity and definition classification

All names below are in `KAM.Planetary`. Every one of the 13 declarations has the same declaration text, type and body as both the standalone signature and Appendix A after whitespace normalization. T1's explicitly requested slice is complete. Generated `PlanarData` constructor/projections/recursors belong to the three-field structure, not additional analytical assumptions.

| Node / adapter | Declaration (Setting line) | Verdict | Classification and reason |
|---|---|---|---|
| p11b:sec-set#data | `PlanarData` (31) | PASS | Source data structure: G, central mass, two planet masses; no proof or conclusion field. |
| p11b:sec-set#data | `PlanarData.Valid` (36) | PASS | Source predicate: positivity of precisely those physical parameters. |
| p11b:sec-set#data | `PlanarData.kappa` (37) | PASS | Explicit physical parameter G m0. |
| p11b:sec-set#data | `p11c_axes` (38) | PASS | Literal ordered positive-axis cone, inner planet index 0; implies positivity at index 1. |
| p11b:sec-set#data | `PlanarData.actions` (39) | PASS | Explicit action dictionary m_i sqrt(kappa a_i). |
| p11b:sec-set#data | `PlanarData.axes` (41) | PASS | Explicit axis dictionary I_i²/(m_i² kappa). |
| p11b:sec-set#data / U2 | `p11c_hatFix` (44) | PASS | Actual fFix composed with delivered poincareProd, same physical data. |
| p11b:sec-set#data / U2 | `p11c_hatMov` (45) | PASS | Actual fMov composed with the same chart; retains the central-mass kinetic term. |
| p11b:sec-set#data / frozen adapter | `p11c_secular` (48) | PASS | Literal frozen secularAverage, constant mu-family; z=(q,p), so arguments z.2,z.1 are correct. |
| p11b slow-variable dictionary | `p11c_slowLength` (51) | PASS | Euclidean length of all four slow coordinates, explicit finite sum; no change to ambient Pi carrier. |
| p11b:quartic-explicit | `p11c_pairDot` (52) | PASS | Dot product of the two planar slow pairs (q0,p0) and (q1,p1). |
| p11b:quartic-explicit | `p11c_quartic` (53) | PASS | Six invariant quartic monomials in exact source order; c index 0 corresponds to source c1. |
| p11b:quartic-explicit / generic jet | `p11c_homogeneousPart` (59) | PASS | Diagonal j-th iterated Frechet derivative at 0 divided by j!, the homogeneous Taylor term. |

No new abbreviation, global instance, theorem, or conclusion-shaped hypothesis occurs. Physical inputs are raw source data, with validity separated as a predicate. The data dictionary and polynomial adapters are literal formulas on their full Lean carriers, without custom default branches, hidden choice witnesses, or substituted physical objects.

**Domain limits:** sqrt, division, Frechet derivatives and the Bochner integral are existing totalized library operations. These formulas are not claims of positive actions or inverse dictionaries for invalid parameters/negative actions, physical chart regularity at singular or collision points, differentiability of arbitrary f, or integrability of arbitrary P. On the source domain (positive data/actions, admissible collision-free chart, analytic/integrable physical functions) they denote exactly the intended objects. In particular, the frozen integral is used directly, including its total extension; T1 proves no theorem by exploiting a nonintegrable integral or a nonsmooth derivative. No extra carrier restriction or universal regularity claim is asserted.

## Checks

Module SHA-256: `0c71c2c19af8d103d52930974bfd790ec1e8ae9b3289ad3176eebabcff2caddd`.
Standalone signature SHA-256: `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079`.

- Whitespace-normalized extraction/comparison: all 13 declarations `SIGNATURE=True APPENDIX=True`.
- Declaration-name search over all other KAM Lean sources: no existing declaration for any of the 13 names. Generated-field names are covered by the fresh structure name; elaboration also checks namespace collisions in its complete imported environment.
- Recursive local KAM import inspection: 63 modules including Setting; no frozen theorem module, no provider module. All frozen imports are definitions; no DRAFT_SORRY theorem enters the closure.
- Forbidden token scan of Setting: no sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option. Module header, public imports, docstring and exposed public noncomputable section are present. File has 62 lines, below 1500; no resource overrides.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty (exit 0).
- `git diff --check`: exit 0, no output.

All Lean/Lake checks were serialized; every command below used `LEAN_NUM_THREADS=1` and niceness 5 (the compile wrapper supplies `nice -n 5` internally). No heartbeat, recursion or synthesis limits were changed.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t1 KAM.Planetary.PlanarTorsion.Setting
```

Exit **0**. Output starts `[inp-gate] slot 2 acquired 15:46:53 for KAM.Planetary.PlanarTorsion.Setting` and ends `Build completed successfully (9109 jobs).` Replayed pre-existing unused-variable warnings occur in `KAM/Kepler/Energy.lean` and `KAM/Kepler/Mass.lean`; no Setting diagnostic. The compile-gate wait was respected.

2. Disposable probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T1Audit.lean
```

Exit **0**. Although no public theorem or provider exists, all 13 definitions/structure were queried. Exact axiom output:

```text
'KAM.Planetary.PlanarData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarData.Valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarData.kappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarData.actions' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarData.axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hatFix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hatMov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_secular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_slowLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_pairDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_homogeneousPart' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three additional `rfl` examples passed: both physical pullbacks equal their specified compositions, and the secular adapter equals `(2*pi)^(-2)` times the integral of `P (Fin.append phi z.1, Fin.append I z.2)` on the literal two-dimensional `[0,2*pi]` product. The probe's one unused parameter `p` produced only a scratch unused-variable warning. No production declaration or premise was introduced.

3. Kernel replay (single invocation; no provider module exists):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.Setting
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.PlanarTorsion.Setting
```

4. Required source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly allowed generated-root staleness. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module checker, frozen-anchor guard and all 144 frozen ABI hashes pass. `KAM.lean` was not regenerated. This permitted exception is retained as a note rather than misreporting lint exit 0.


## Notes, uncertainties and suspected defects

N1 (dispatch documentation, already identified as design audit N2): design T6 owns `p11c_homogeneousPart` (design node table L104), while the design audit explicitly proposes putting it in Setting for the earlier T12 consumer. T1 implements that proposed relocation, as declared in the handoff. T6 must import Setting and must not redefine the name. T15 must import Setting for `p11c_slowLength`; the design table's “frozen definitions only” at L216 is incomplete. These are scheduling/import documentation notes, not altered signatures or unpaid T1 proofs.

The broad node table at design L108 calls sec-bnf data “T1/T7”; the execution row T7 L205 owns QuarticFamily/characters. The user/handoff's explicit 13-name T1 focus controls this audit; the unimplemented QuarticFamily/NR4/bracket material is T7 work and is not a missing declaration in this T1 slice.

No newly suspected blueprint mathematical defect or pinned-source erratum was found in this scoped definitions audit. Primary-paper computations, future homogeneous-jet identities, analytic regularity, integrability and torsion closure are outside T1 and remain future proof work. No source or frozen statement was repaired. Only this report is a lasting audit edit; disposable probes are confined to `.lake/abi-scratch/` and removed after verification.
