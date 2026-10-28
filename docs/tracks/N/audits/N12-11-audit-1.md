# N12-11 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the N12-11 infrastructure package. The two new
public theorems are proved with the permitted axioms, the exit signature matches the reviewed
design exactly, and kernel replay succeeds. The notes concern a valid alternative openness
proof, the generated-root lint exception, and the moving comparison branch. No blocking
mathematical or implementation defect was found.

This package has **no provider export and seals no frozen anchor**. In particular this report
does not pronounce `averaging_mean` or `averaging_most` seal-ready. Their frozen files still
contain `by sorry` and are outside the requested Exit-only audit. Provider/frozen type and
seal-body probes are therefore inapplicable; an exact design-type/application probe was run
for `exit` instead.

## Scope and evidence

Audited 2026-10-28 in `/root/code/KAM-inp-n1211`, read-only except this report and temporary
probes in `.lake/abi-scratch/`. No production edits, git mutations, delegation, or generated-root
regeneration. The user's exact report destination overrides the generic brief's main-worktree
output instruction. The pre-existing untracked handoff was preserved.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the shared package-audit brief,
`docs/tracks/N/audits/N12-11-handoff.md`, design row N12-11 and its proof plan/Appendix A,
both design audits (located under `docs/tracks/N/design/`), and the authoritative signatures
at `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`. Also read Part 12's exit statement,
proof and graph records, the averaging section of the track statement, the two relevant
frozen averaging anchors and their defining inputs, and the consumed ODE/averaging interfaces.
The signatures file is absent in this worktree; the shared copy was read without modification.

Snapshot:

| Item | Revision or SHA-256 |
|---|---|
| HEAD | `e8c6a0a69cdfc8ce26ec2cff2318dda2ef273910` |
| `inp` | `5991245cabc06e69ec900cb6006b45f72cc85eb0` |
| current `inp-n1210b` | `921475c33cb76dba47b677e348fce29127afa7b2` |
| Exit source | `797faf60561babacce0eda2814d0fe690725cba792a61f9f0a877409511f48f7` |
| N12 design | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| Part 12 blueprint | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |
| shared signatures | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |

`git diff inp...HEAD` contains Exit plus four inherited N12-10b modules (Flow, FlowChain,
FlowRegular, FlowSymplectic): 1168 added lines in five files. As requested, those inherited
proofs are not re-audited here. `git diff inp-n1210b...HEAD` was also examined: the current
branch reference has diverged, so its full diff includes unrelated packages and generated-root
changes. Filtering to Exit gives precisely the submitted new file. `git diff HEAD^ HEAD`
independently isolates the package commit: only `Exit.lean`, 249 additions. This avoids
misattributing unrelated changes in the moving comparison branch to N12-11.

## Declaration and node ledger

All declaration names below are in `KAM.Nekhoroshev`; locators are in
`KAM/Nekhoroshev/Averaging/Exit.lean`. Blueprint labels abbreviate `bpN:p12:*` and
`stepN:p12:*`. Every new declaration, including private helpers, is accounted for.

| Node / contract | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| exit: stay-set data | `avgStay`, lines 36–39 | PASS | Exact design text; nonnegative time, initial action in the half-ball, endpoint in the maximal domain, and strict displacement bound at every intermediate time. |
| exit: stopping time | `avgTau`, lines 40–42 | PASS | Exact design text; supremum of real times embedded into `EReal`. No finite real supremum is used for an unbounded set. |
| auxiliary finite supremum | private `sSup_coe_image`, lines 47–56 | PASS | Both nonemptiness and boundedness hypotheses are present before applying conditional real supremum facts. |
| auxiliary infinite supremum | private `sSup_coe_image_top`, lines 59–65 | PASS | Containing every nonnegative real forces the embedded supremum to top; no boundedness shortcut. |
| ex-open | `isOpen_avgStay_relative`, lines 75–123 | PASS | Proves exactly the final exit conjunct, for every real epsilon. A valid strengthening of the epsilon-positive setting; no extra premise. |
| periodic continuation interface | private `avgField_periodic`, lines 135–139 | PASS | Repackages proved `avgField_shift` for the existing periodic continuation theorem on the same action domain. |
| exit / ex-exit | `exit`, lines 142–160, 163–181, 191–214, 215–242 | PASS | Exact design telescope and conjunction; finite boundary hit strictly before the maximal endpoint, or infinite exit and endpoint; positivity and endpoint bound included. |
| ex-g | `exit` local `hgV`, lines 182–190, and endpoint cases | PASS | Triangle inequality gives action norm below 5R/8 and hence membership in the closed 3R/4 ball through the exit endpoint. |

The proof also establishes the facts used to interpret the finite/infinite cases: positivity
excludes negative infinity, and every finite `EReal` has a real representative. The design
asks for the real-representative formulation, which is exactly what is exported. The separate
stay-set equality with `{t : 0 ≤ t ∧ (t : EReal) < avgTau ...}` is not exported as a named
lemma; it is consistent with the construction and was not part of the reviewed signature.
No downstream consumer proof is claimed by this audit.

## Definition classification and hypotheses

There are exactly two new definitions and no new abbreviations, structures, or instances on
ambient carriers.

- `avgStay` is a total set predicate, not a chosen orbit extension. Its `avgOmega` guard
  restricts valid times and initial points. Under `AveragingData`, convexity of the maximal
  interval and membership of zero show every intermediate time is in the flow domain.
- `avgTau` is a total complete-lattice supremum in `EReal`. For an empty stay slice it is bottom,
  which correctly represents the empty-set supremum outside the intended hypotheses. In the
  theorem's domain the slice contains zero and in fact a positive interval, so this value is
  never used to obtain a dynamical conclusion. Unbounded slices give top.

The imported maximal-flow representation has a fallback outside its existence domain, as
explicitly documented in `FlowDefs.lean`. Here `hx` and `d.hR` imply `x ∈ avgDomain n R`;
`avgMaximal_spec d epsilon` supplies genuine maximal solutions there. No result relies on
fallback values or an off-domain derivative. Ambient actions and angles use `Fin n → ℝ`
with their maximum norms; no `EuclideanSpace` carrier occurs.

`AveragingData` contains only dimension/positivity, frozen analyticity/size-one perturbation,
and frequency-rank source assumptions. It contains no exit, flow regularity, future
confinement, or desired estimate. The retained `hε : 0 < ε` in `exit` is unused mathematically,
as disclosed in the handoff; it is neither an extra premise relative to the design nor a
hidden smallness assumption. No constants acquire wider dependence.

The source import closure contains 62 project modules, including 26 frozen definition
modules, all recorded `SEALED` in the manifest. It contains **no frozen theorem module and
no provider module**, transitively as well as directly. Reading draft anchors for context
was not an import into the probe or the audited module.

## Refutation checks on the proof

1. **Domain and first exit.** `hstay` identifies the exact time slice with the set used by
   `KAM.ODE.gen_exit`, on the full maximal interval `eIoo Tm Tp`. The generic result only
   needs an order-connected interval containing zero, so using the full interval rather
   than its nonnegative part preserves the forward exit construction.
2. **No exit.** Action displacement below R/8 plus initial action norm below R/2 traps the
   actions in `closedBall 0 (5*R/8)`, a genuine compact subset of the open action ball R.
   `gen_continuation_periodic` is applied with a proved C1 field, proved periodicity, and
   the genuine maximal solution. It needs no compact bound on the real angle lift. The
   endpoint is top; every nonnegative real is then in the stay set, proving `avgTau = top`.
3. **Finite exit.** Generic first exit supplies `ts > 0`, `ts ∈ J`, pre-exit membership,
   frontier membership, and the real supremum identity. The stay slice is nonempty and
   bounded above by ts before the private coercion lemma is applied. Closure membership
   gives displacement ≤ R/8, and failure of strict membership gives ≥ R/8. Thus equality
   and `ts < Tp` are proved without assuming either.
4. **Endpoint and compactum.** Intermediate times lie between zero and ts in the maximal
   interval. Pre-exit strict bounds and boundary equality cover the closed stopped interval.
   The triangle inequality supplies `avgG` membership in both branches.
5. **Relative openness.** Joint continuity of the real flow makes
   `A = flowDomain ∩ {displacement < R/8}` open. The compact segment `[0,t0] × {y0}` lies
   in A. `generalized_tube_lemma` supplies product neighborhoods, and an endpoint collar
   extends the time interval slightly past t0. Pulling back to nonnegative times and initial
   actions in the half-ball gives the stated open set, including t0 = 0. No absolute
   openness in all real times is asserted.

## Independent verification

All Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, recursion-depth, or synthesis-budget override was used.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1211 KAM.Nekhoroshev.Averaging.Exit
[inp-gate] slot 2 acquired 09:49:49 for KAM.Nekhoroshev.Averaging.Exit
Build completed successfully (2972 jobs).
exit 0
```

The build replayed existing warnings in PicardFamilies (lines 60, 82, 203, 208, 268),
LocalDependence (45, 99, 186), CompactMaximum (29), and KAM.ODE.Exit (36). These concern
unused variables/section instances or a style suggestion. No warning from the audited
`Exit.lean` appeared. They are not resource-limit failures.

### Exact signature/application and axioms

Created `.lake/abi-scratch/N1211Audit.lean` importing only
`KAM.Nekhoroshev.Averaging.Exit`. Copied the literal shared `theorem exit` signature under
a fresh name, replaced its draft body with `by exact exit d hε hx`, and checked
`example : type_of% @audit_design_exit := @exit`. This checks binder order, inferred section
parameters and all conclusion clauses, without importing any draft theorem. A textual check
also confirmed that `avgStay` and `avgTau` declarations equal the shared design verbatim.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1211Audit.lean
'KAM.Nekhoroshev.exit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_avgStay_relative' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

These are every new public theorem. No `sorryAx` or additional axiom appears. The temporary
probe was deleted after verification.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Exit
replaying KAM.Nekhoroshev.Averaging.Exit
exit 0
```

One invocation replays the only new module, including its private helpers and both public
proofs. This is independent replay of the submitted module, not a claim to have separately
replayed every inherited dependency module.

### Source hygiene and protected paths

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (524 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the explicitly permitted stale generated-root check. There were no
100-character line violations, oversized files, forbidden constructs, module errors,
anchor-guard failures, or ABI mismatches.

Independent source scan: 249 total lines, maximum line length 98 characters; no forbidden
proof escape, resource override, or prohibited ambient carrier. Copyright/authors, `module`,
public imports, module docstring, exposed public section are present. No new production
consumer import was introduced by this commit.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --check
(no output; exit 0)
```

The package-only `HEAD^..HEAD` protected-path check was also empty. The generated root was
not edited to silence lint. Final report whitespace and scratch cleanup were checked.

## Notes, defects, and limits

- **Valid proof-route deviation:** Part 12 line 82 invokes continuity of a compact-time
  maximum via `ext-markov#compact-max`. The implementation proves the required openness
  directly by a compact tube argument. `CompactMaximum` is imported but not used. This is
  mathematically sound and preserves the entire reviewed exit signature. The handoff's
  “deviations: none” should be read with this implementation-route note. If graph metadata
  is updated, it should describe the actual use rather than claiming a compact-maximum
  theorem invocation.
- The continuation compactum is the centered ball of radius 5R/8 rather than the translated
  closed tube ball in the blueprint. This is a valid enclosing compactum with a strict
  interior collar and no change to assumptions or conclusions.
- **Blueprint wording:** `blueprint-N/parts/p12-averaging.tex:82` calls
  `D ∩ {t ≥ 0}` “the open set”. It is generally only relatively open in the nonnegative-time
  space (it includes time zero). The lemma at line 75, reviewed design, and Lean theorem
  use the correct relative topology. This is a minor wording issue in the proof text, not a
  false Lean theorem or a needed statement change. No new pinned-primary-source erratum
  was found; existing averaging errata are not re-audited here.
- No evidence of a frozen-statement defect, extra hypothesis, weaker conclusion, hidden
  conclusion-shaped field, resource-budget design signal, or reliance on junk values was
  found. Remaining averaging provider assembly and downstream consumer closure are outside
  this focused package audit.

Files written: only this report. Approach: independent source/design comparison, adversarial
proof inspection, exact type/application probe, targeted gate, axioms, kernel replay and lint.
