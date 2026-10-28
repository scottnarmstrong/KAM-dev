# R1 independent package audit 1

**Overall verdict: FAIL against AUDIT FOCUS (a), exact signature identity.** The five helper proofs are mathematically appropriate to the R1 implementation role, but none of their declarations occurs in the supplied signature file. This is an interface/design omission, not evidence of an unsound theorem. The local/maximal ODE infrastructure requested by row R1 is present. The shared analytic-flow node is not closed by R1 and must remain open until R2/R3 establish the signed bridge.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-r1`. HEAD `e1a6d79dbc71cb183d0c04add2a0bbc8f2ac0b59`; comparison `inp` resolved to `a81e8d4215d2f99f8c148dd4ca24915a17ca95b5`. `git diff inp...HEAD` adds only the 89-line `KAM/Planetary/PlanarTorsion/RealFlow/Local.lean`. The pre-existing untracked R1 handoff was left unchanged. The user's exact report path overrides the generic brief's main-worktree destination. Only this report is a lasting audit edit; disposable probes belong to this worktree's `.lake/abi-scratch/`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the supplied package-audit brief and handoff, track-P statement conventions, P11C design and its design audit, standalone signatures, the relevant Part-11b blueprint, frozen definitions, and the existing ODE inputs. Applied the statement/hypothesis checks of the `lean-statement-audit` skill. This is a helper-package audit, not a fresh pinned-paper audit.

## Snapshot and scope

| Input | SHA-256 |
|---|---|
| `KAM/Planetary/PlanarTorsion/RealFlow/Local.lean` | `e06a29772d40746e35f5cace83407ed4df2c6f8cf7e14e166642c92361247561` |
| `docs/tracks/P/design/P11C-LEAN-DESIGN.md` | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |

The design/signature/blueprint hashes match the earlier P11C design audit's snapshot. No signature drift explains the missing R1 signatures.

No provider export or frozen anchor is assigned to this slice. Provider/frozen type equality and seal-body probes are **not applicable**. The downstream P-PLANAR anchor `KAM.Planetary.planarTwoPlanetKAM` is still DRAFT_SORRY; R1 does not import or seal it. No anchor receives a seal-ready PASS from this report.

## Finding F1: unsigned public interface (blocking contract finding)

AUDIT FOCUS requires “every declaration = signature file EXACTLY.” At `Local.lean:37,47,57,74,82`, the five new public theorem names have **zero occurrences** in `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean`. Design row R1 (`P11C-LEAN-DESIGN.md:207`) gives only “existing real local/maximal ODE and compact-neighbourhood bounds; U3”. It supplies neither theorem names nor complete types. Thus there is no exact signed R1 interface against which these exports can pass criterion (a). The handoff correctly discloses this omission; disclosure does not amend the audit contract.

Required disposition: reconcile and record the exact five helper types in the controlling design/signature surface, or explicitly authorize R1 implementation helpers outside that requirement. An independent auditor must not silently create that exception. This report makes no such amendment and requests no source/code change within this read-only audit.

## Declaration and node table

Names below are in `KAM.Planetary`. “FAIL (a)” means unsigned interface; the accompanying proof/semantic verdict is separate.

| Node / role | Declaration and line | Verdict | Reason |
|---|---|---|---|
| R1 derivative regularity | `p11c_hamField_contDiffOn`, 37 | FAIL (a); proof/meaning PASS | Open W and C2 H give C1 coordinate Hamiltonian derivatives via `fderiv_of_isOpen`, evaluation on constant basis vectors and product formation. No change of field or norm. C2 is weaker regularity than the analytic input used downstream. |
| R1 analytic specialization | `p11c_hamField_contDiffOn_of_analytic`, 47 | FAIL (a); proof/meaning PASS | AnalyticOnNhd on open W supplies C2; applies the previous result. |
| R1 compact-neighbourhood bounds and existence | `p11c_local_flow_uniform`, 57 | FAIL (a); proof/meaning PASS | Positive delta and epsilon, nonnegative M, compact closed thickening inside W, bounded field, one Lipschitz constant on every closed delta-ball, solutions for every initial point/time. Constants precede y and t0 and depend only on the fixed W,H,K. Uses epsilon = delta / max M 1. |
| R1 compact-uniform local existence | `p11c_local_flow_compact`, 74 | FAIL (a); proof/meaning PASS | Exact compact clause of `gen_local`, with C1 field proved internally. |
| R1 maximal existence and uniqueness | `p11c_maximal_flow`, 82 | FAIL (a); proof/meaning PASS | Applies `gen_maximal`; proves existence and uniqueness of endpoints and equality of solutions on their open maximal interval. No global-time claim. |
| `bpP:p11b:e-ode` | signed `real_analytic_hamiltonian_local_flow` absent from this module | OPEN shared node; no R1-only omission finding | Node table at design:86 assigns R1-R3 jointly; execution row R3 at :209 owns the final signed bridge. R1 establishes the existence infrastructure only. |
| `stepP:p11b:fl-bd` | none in this module | OUT OF SCOPE | Design:116 assigns T9. |
| `stepP:p11b:fl-an` | none in this module | OUT OF SCOPE | Design:117 assigns T9. |

The handoff's assertion that the signed bridge is assembled in R3 is confirmed by the execution table, with the qualification that the graph node is mapped to **R1-R3 jointly**, not solely R3. Blueprint `p11b-planar-torsion.tex:20` literally requires analytic dependence on time, initial data and parameters. Signatures:442-450 require a single jointly analytic local solution map and symplecticity. Neither separate existence witnesses nor maximal uniqueness states that conclusion. Do not mark the graph node PROVED from R1 alone.

The design's internal R1 work is covered: C1 field, uniform compact neighbourhood data, local solutions, and maximal solutions/uniqueness. No export is misleadingly named as the analytic-flow graph result. Analytic parameter dependence, variational equations, symplecticity and the T9 cubic/time-one estimates remain assigned downstream obligations, not missing R1-only steps.

## Expanded binder audit

Classification here checks the helpers' stated mathematical roles under design:207 and U3 (design:45), not nonexistent signed declarations. SOURCE means the role's regularity/domain/compactness inputs; TYPING means the ambient carrier or object being quantified. STANDING=RULED=EXCESS=0. This absence of hidden premises does not cure F1.

| Declaration | Binder (in declaration order) | Bin | Evidence / meaning |
|---|---|---|---|
| `p11c_hamField_contDiffOn` | implicit `d : Nat` | TYPING | Phase dimension, design section 2 |
| same | implicit `W : Set (Phase d)` | TYPING | Open real domain |
| same | `hW : IsOpen W` | SOURCE | R1/U3 open domain |
| same | implicit `H : Phase d -> Real` | TYPING | Real Hamiltonian |
| same | `hH : ContDiffOn Real 2 H W` | SOURCE | Explicit derivative-regularity helper input; C1 field is proved |
| `p11c_hamField_contDiffOn_of_analytic` | implicit `d` | TYPING | Dimension |
| same | implicit `W` | TYPING | Domain |
| same | `hW : IsOpen W` | SOURCE | R1/U3 |
| same | implicit `H` | TYPING | Hamiltonian |
| same | `hH : AnalyticOnNhd Real H W` | SOURCE | Blueprint:20 analytic field route, design real bridge |
| `p11c_local_flow_uniform` | implicit `d` | TYPING | Dimension |
| same | implicit `W` | TYPING | Domain |
| same | `hW` | SOURCE | Open domain |
| same | implicit `H` | TYPING | Hamiltonian |
| same | `hH` | SOURCE | Analytic Hamiltonian, not assumed field regularity |
| same | implicit `K : Set (Phase d)` | TYPING | Compact set to quantify over |
| same | `hK : IsCompact K` | SOURCE | R1 compact-neighbourhood role |
| same | `hKW : K subset W` | SOURCE | Compact set lies in the analytic domain |
| `p11c_local_flow_compact` | implicit `d` | TYPING | Dimension |
| same | implicit `W` | TYPING | Domain |
| same | `hW` | SOURCE | Open domain |
| same | implicit `H` | TYPING | Hamiltonian |
| same | `hH` | SOURCE | Analytic Hamiltonian |
| same | implicit `K` | TYPING | Compact set |
| same | `hK` | SOURCE | Compactness |
| same | `hKW` | SOURCE | Containment |
| `p11c_maximal_flow` | implicit `d` | TYPING | Dimension |
| same | implicit `W` | TYPING | Domain |
| same | `hW` | SOURCE | Open domain |
| same | implicit `H` | TYPING | Hamiltonian |
| same | `hH` | SOURCE | Analytic Hamiltonian |
| same | implicit `y : Phase d` | TYPING | Initial point |
| same | `hy : y in W` | SOURCE | Initial point belongs to the domain |

Counts: 33 input binders = SOURCE 15 + TYPING 18. No instance binders or bundled proof assumptions are added. Quantifiers under the conclusions (delta,M,epsilon,L, initial points/times, curves, and maximal competitors) are outputs/universal claims, not outer assumed obligations. In particular, the maximal-solution predicates in the uniqueness implication are legitimate comparison inputs paired with independently proved existence.

## Definitions and proof dependencies

**New def/abbrev/structure inventory: empty.** BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS, CHARACTERIZATION and CHOICE_INDEPENDENCE: N/A for new definitions. No arbitrary chosen flow or fallback is introduced by R1.

The exact imported frozen `Phase d` is `(Fin d -> Real) x (Fin d -> Real)`; the Hamiltonian field is `(partial_p H, -partial_q H)` via real Frechet derivatives on that carrier. On open W, the regularity premise makes those derivatives actual derivatives, so totalized off-domain derivatives are not exploited. The norm throughout this slice is the existing product/Pi max norm. No physical Euclidean estimate is claimed.

`KAM.ODE.closedThickening` (`Lipschitz.lean:57`) literally means an existential centre in K at norm distance at most delta. The bound proof in Local:70-71 uses that centre and the corresponding closed ball; no global Lipschitz property on a nonconvex thickening is substituted. `IsSolutionIn` (`Basic.lean:41`) includes both membership in W and the actual two-sided `HasDerivAt` equation. `IsMaximalSolution` (`Maximal.lean:42-50`) includes initial value at zero, both endpoint signs, actual solution, and maximal comparison on order-connected time sets. These are used as conclusions, not assumed gates. Empty K and dimension zero are allowed; no nonemptiness or positive dimension is secretly needed.

Recursive project import inspection found 10 modules including Local, no providers, and only these four frozen imports, each manifest state SEALED and kind definition: `kam.hamiltonianVectorField.v1`, `kam.IsDiophantine.v1`, `kam.symplecticForm.v1`, `planetary.Phase.v1`. No DRAFT_SORRY theorem is imported. No signature file containing sorry was imported.

## Validation

All Lean/Lake commands are serialized, with `LEAN_NUM_THREADS=1`; no heartbeat, recursion or synthesis override was used.

1. Targeted build:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-r1 KAM.Planetary.PlanarTorsion.RealFlow.Local
[inp-gate] slot 2 acquired 18:37:54 for KAM.Planetary.PlanarTorsion.RealFlow.Local
Build completed successfully (9056 jobs).
exit 0
```

The gate itself runs `nice -n 5 lake build`; the job count is Lake's build-plan report, not a clean rebuild. No clean/update/cache operation was run.

2. Axiom probe `.lake/abi-scratch/R1Audit.lean` imported only `KAM.Planetary.PlanarTorsion.RealFlow.Local` and issued `#print axioms` for all five exports:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/R1Audit.lean
'KAM.Planetary.p11c_hamField_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_hamField_contDiffOn_of_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_local_flow_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_local_flow_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_maximal_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

3. Kernel replay (the sole scoped module; no provider exists in this package):

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.RealFlow.Local
replaying KAM.Planetary.PlanarTorsion.RealFlow.Local
exit 0
```

4. Required repository lint (after kernel replay completed):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (880 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the brief's explicitly permitted stale generated-root exception; every other lint check passes. No generated file was regenerated.

5. Static checks: 89 lines total (below both 100 and 1500); maximum line length 97 characters. Copyright, `module`, public imports, module docstring and exposed public section are present. No forbidden proof token, resource option or `EuclideanSpace`. All five short names occur in no other production declaration; no public-name reuse, root declaration shadow, new instance or ambient norm modification.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check`: exit 0. No generated root or README repair was performed.

## Errata, deviations and limits

No suspected mathematical defect in the pinned source or blueprint was found in this slice. F1 is a design/interface omission: the handoff explicitly substitutes five newly named helper types for an absent R1 signed interface. Record that deviation even though the helper proofs have no apparent mathematical defect. This auditor introduced no Lean/source deviation and made no source repair.

The earlier design audit's N1 graph provenance and N2 unrelated helper-DAG notes are not silently reclassified as closed. They do not alter the fresh R1 scope assessment. Actual R2/R3 consumer applicability is not proved by name availability or this R1 build. No frozen theorem or campaign theorem closure is claimed.

Closeout: the scratch axiom probe and captured checker/lint logs were deleted after their full output was recorded above. The reviewed Lean file hash is unchanged. Report whitespace validation and `git diff --check` pass. Final status contains only this new report and the pre-existing untracked handoff.
