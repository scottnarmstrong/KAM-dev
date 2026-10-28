# E1 independent package audit 1

**Verdict: PASS WITH NOTES.** The complete E1 ordinary-library contract passes. The sole
validation exception is the brief-permitted stale generated `KAM.lean`. No proof repair is
required. No frozen anchor is delivered or sealed by E1; provider/frozen-type equality and
seal-body probes are therefore not applicable. In particular this is not a seal-readiness
claim for `planetaryExponentialSafety` or any other campaign root.

Audited on 2026-10-28 in `/root/code/KAM-inp-p14-e1`, HEAD
`122dbaee32024a5a80d8731c09ce701f02ef6842`. Scope is exclusively
`KAM/Planetary/Exponential/Dictionary.lean` (91 lines), as required by the handoff.
`git diff inp...HEAD` adds exactly that file. The live `inp` ref advanced during the audit
(initially `0c4b228c40c18845100d2ce1ebc27d8727a509ad`, later
`700477228205080ba6e81c21cb4f1d05acafe970`); the repeated triple-dot comparison remained the
same one-file change, with merge base `7ec42a1dd0f6154a1f6a357ba53d92080b367082`.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, E1 handoff, P14 design and both
design audits, the authoritative signature file in `/root/code/KAM-inp/.drafts/design/`,
the relevant Part 14 blueprint and track P statement, the exponential-safety anchor, and
the frozen definitions and ordinary chart suppliers used here. The report destination
follows the user's exact worktree path, overriding the generic brief's main-worktree rule.

## Declaration and completeness review

All names below have namespace `KAM.Planetary`.

| Node / obligation | Lean declaration and locator | Verdict | Reason |
|---|---|---|---|
| E1 componentwise dictionary helper | `poincareProd_planet_facts`, Dictionary.lean:37–62 | PASS | Positive masses and product-domain membership only. Action, axis and cross-product identities follow from the selected one-planet `poincare_elements`, through `poincareProd_block`, at strength 1. No two-planet specialization or additional premise. |
| `bpP:p14:sec-domain#chart-facts` | `sec_domain_chart_facts`, Dictionary.lean:64–79 | PASS | Telescope is text-identical to P14Signatures.lean:247–257, including binder order, all conjunctions, literal frozen quantities and arbitrary n. Prograde membership follows from `regionProd_one_iff`; AMD is the finite sum of action minus angular momentum. |
| E1 general-n prograde onto bridge / `bpP:p14:ch-chart` onto clause | `poincareProd_image_prograde`, Dictionary.lean:83–88 | PASS | Exact image equality on the entire product chart domain, with target the literal frozen `ProgradeElliptic`. Only positive masses required. Derived from `poincareProd_image` and `regionProd_one_iff`; independently tested as an existential lift at arbitrary n. |

Completeness was checked against P14-LEAN-DESIGN.md:190, 286–287, 346, 374,
406–407 and 455–465, together with the complete E1 signature and blueprint
p14a-amd-expsafe.tex:157–168. Both E1 outputs in the package row are supplied. There is
no separate E1 proof-step row left unimplemented.

The blueprint's larger (Ch1)–(Ch3) discussion does not assign all chart infrastructure
anew to E1: analyticity, symplecticity, lattice periodicity and the Hamiltonian split are
existing Product suppliers, and later packages own the analytic/ODE bridges. For (Ch2),
the approved signature deliberately exports action, axis, cross product, prograde
membership and AMD. Energy and squared eccentricity follow by substitution into A1
`elements` (AMD/Elements.lean:134–165). This agrees with both design audits' dictionary
rows; it is not an omitted additional E1 export. The one-planet vector identity is also
already supplied by `poincare_elements` (Poincare/Symplectic.lean:195–205).

The unsigned bridge has precisely the needed generality: arbitrary `n : ℕ`, arbitrary
positive mass vector, chart carrier `Phase (n+n)`, physical carrier `Phase (n*2)`, and
strength 1, matching this physical model. It covers circular data, since the domain
requires only positive action and Gamma < action, not positive Gamma. It has no
noncollision, axis-order, angle-choice, smallness or n=2 premise. E3 can consume the
forward dictionary and A1 formulas. E4's h-data contract concerns the complex Kepler
function and does not demand a stronger onto statement (its DAG inputs are E2/E5).
E9 can obtain an initial chart lift from the image equality and then recover actions
and AMD with the dictionary. No injectivity or global continuous inverse is asserted
or needed from this onto bridge. These are interface checks, not validation of future
consumer proofs.

## Definitions, assumptions and names

There are **no new defs, abbrevs, structures, classes or instances** in the audited
file. Definition classification is therefore empty. Existing frozen action, energy,
axis, physicalAMD, totalMomentum and bodyVector are used literally; `chartAMD` is the
existing E0 quadratic sum. The domain guards every physical square root/division used
in the proof, so totalized values outside the intended domain do not discharge a goal.

Every new theorem assumes only positive masses, domain membership and, for the helper,
a selected body index. No conclusion-shaped assumption or bundled hard proof step.
A recursive local import scan found 69 KAM modules, including 52 frozen definition
modules, and **zero providers or frozen theorem modules**. Thus there is no imported
DRAFT_SORRY anchor and no sealed-theorem manifest exception to invoke.

A declaration-name scan over every KAM Lean source found each of the three new short
names only at its declaration in Dictionary.lean:37,64,83. All three lie inside the
explicit `KAM.Planetary` namespace; no root shadow or reused public short name was found.

## Independent validation receipts

Commands ran from the audited worktree. Lean/Lake validation was serialized with
`LEAN_NUM_THREADS=1` and `nice -n 5`, including the final lint invocation and its ABI
subprocess. The build used the prescribed compile gate, at default resource settings.
A preliminary lint invocation was stopped during its Python frozen-anchor check and
superseded by the final invocation below, before it could launch an ABI Lean process.

### Targeted gated build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e1 KAM.Planetary.Exponential.Dictionary
[inp-gate] slot 1 acquired 16:22:21 for KAM.Planetary.Exponential.Dictionary
Build completed successfully (9115 jobs).
exit 0
```

The build replayed existing unused-variable warnings in Kepler/Energy.lean:106,
Poincare/Chart.lean:212,247, and Kepler/Mass.lean:147,157,500,524. No warning came from
Dictionary.lean. No heartbeat or other resource override was introduced.

### Exact signature, consumer probe and axioms

An audit-generated `.lake/abi-scratch/E1Audit.lean` imported only the audited module.
It copied the signature's literal telescope to fresh `e1_audit_signature`, proved it
by `exact sec_domain_chart_facts hm hw`, and checked:

```lean
example : type_of% @sec_domain_chart_facts := @e1_audit_signature
```

The same probe derived, for arbitrary n and positive masses, the consumer statement
`ProgradeElliptic m z → ∃ w ∈ poincareProdDom n, poincareProd m 1 w = z` using the new
image equality. A separate text extraction of the authoritative and implemented
telescopes printed `SIGNATURE TEXT EXACT: True`. The sorry-bearing design module
was never imported.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E1Audit.lean
'KAM.Planetary.poincareProd_planet_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sec_domain_chart_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_image_prograde' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Kernel replay

One invocation covered the sole new module and all its new theorem declarations:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Dictionary > .lake/abi-scratch/E1-leanchecker.log 2>&1
replaying KAM.Planetary.Exponential.Dictionary
exit 0
```

### Lint and protected paths

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (784 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint diagnostic is the explicitly permitted stale generated root; it was
not regenerated. The audited file has 91 lines, no lines over 100 characters, the
required copyright/module/public-import/docstring/public-section form, and no
`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or resource override.

```text
git diff --check inp...HEAD
(no output; exit 0)
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
git diff --stat inp...HEAD
 KAM/Planetary/Exponential/Dictionary.lean | 91 +++++++++++++++++++++++++++++++
 1 file changed, 91 insertions(+)
```

## Errata, limits and handoff

No suspected pinned-source, blueprint or frozen-statement defect was found in this
scope; no mathematical deviation was introduced. The newly chosen onto name has no
signature-file counterpart, but its precise statement fulfills the explicit E1 row.
The broader inherited analytic and N-root release obligations remain outside E1;
this audit does not certify them.

Only this report was authored in repository source space. The pre-existing untracked
E1-handoff.md was left alone. Audit-created probe and replay-log files were removed
after validation. No state-changing git command, frozen edit, generated-file edit,
provider edit or source repair was performed.
