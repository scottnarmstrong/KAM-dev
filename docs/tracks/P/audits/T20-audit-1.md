# T20 independent package audit 1

**Overall verdict: FAIL — required nonzero-locus bridge is missing.**
The signed `KAM.Planetary.torsion` statement matches exactly and its proof passes the build,
kernel replay, and axiom checks. The package does not satisfy the explicit adapter-completeness
requirement in the audit focus and design L187. This is a missing correspondence proof, not a
counterexample to `torsion`. No frozen headline anchor is sealed by this package.

## Scope and pinned inputs

Audit date: 2026-10-29. Tier 2, refute-first. Implementation scope is **only**
`KAM/Planetary/PlanarTorsion/Generic.lean`. Authority: user instructions, `AGENTS.md`,
`docs/PLAN.md`, `docs/DECISIONS.md`, the integration audit brief
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `T20-handoff.md`'s AUDIT FOCUS.
The user's exact report destination overrides the brief's generic main-worktree destination.
Only this report is a lasting edit; the disposable probe was confined to `.lake/abi-scratch/`.
No source repair, git mutation, generated-root regeneration, or dependency installation occurred.

Frozen-v1 HEAD: `2b0a2707054a0623c9d78283cf9a6868cffa0f51`.
Initial comparison branch `inp`: `d0978a29ff663d8cdf299ccd48de6d1b5d8b8054`.
`git diff inp...HEAD` warns of multiple merge bases and selects
`d74db2d8a2ace1493c1f084a871138d80988b961`. Its complete inventory contains 41 changed files,
5,442 insertions and 132 deletions; the diff has 6,146 lines. This inventory includes inherited
T16 Birkhoff modules, preparation/weak-KAM integration, graph changes, and older reports.
Those files receive no new proof verdict here. The full target diff and relevant imported
interfaces were inspected. T20 changes are attributable to `9ca84daf`, `49f07b15`, and
`2b0a2707`; the final target has 135 lines. `inp` advanced during this audit; HEAD and the
target/signature hashes stayed unchanged. All comparisons above refer to the initial snapshot.

| Input | SHA-256 |
|---|---|
| `KAM/Planetary/PlanarTorsion/Generic.lean` | `9a3648c780a16f0b4d4495adba7fc4e175a63b3b2aa38d9632355d281cf81116` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7` |
| `docs/tracks/P/design/P11C-LEAN-DESIGN.md` | `8693b4c33b78a6d52c251999b15e08fc68d588b9250e2e4bbe3e64b4510a6437` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |
| `docs/tracks/P/design/DESIGN-P11C-design-audit-1.md` | `b6da04d8b43c384d2a479e88c1a20642aee11b53f81f840f8f1d0bbc9944dba7` |
| `docs/tracks/P/audits/T20-handoff.md` | `92cacec244cdb5d8bbba3609a748f2f4ca66a7a09d2f382a6823d7b029dd2992` |

The prior design audit is design evidence, not evidence that its explicit reconciliation gates
have been proved. Track P's statement document and the actual imported frozen definitions were
consulted; this helper has no manifest anchor (`FROZEN_FILE`, `FROZEN_DECL`, and anchor ID are
all `-` in the graph record). Thus provider-to-frozen and seal-body checks are inapplicable;
the exact signed-type probe is used instead.

## Finding F1: nonzero-locus correspondence is not delivered

**Severity: completeness blocker; disposition: survives adversarial refutation.**

Design L187 requires: “`p11c_phi4` is an adapter for the **nonzero locus** of the Part-9
product” and “Prove the locus bridge”. Design U9, L54, likewise says to “prove its nonzero
locus equals upstream Phi4's locus.” The earlier design audit's `p11c_phi4` row explicitly
retains that requirement. The user's audit focus specifically asks that it be checked.

`Generic.lean:51–60` proves only
`∃ a ∈ p11c_axes, p11c_phi4 p a ≠ 0`. It starts with upstream `good_point`, takes its NR4
component, uses `p11c_sigma_eq_sigma`, and checks every factor of the finite product at that
one point. This is valid and sufficient for the signed adapter-product genericity theorem.
It does **not** establish the required pointwise equivalence on the axis cone:

```lean
∀ a ∈ p11c_axes,
  p11c_phi4 p a ≠ 0 ↔
    SecularSpectrum.good (SecularSpectrum.sigma (p11cSecularData p hp) a) ≠ 0
```

The original product `SecularSpectrum.good` includes a discriminant and products over all
permutations (`SecularSpectrum/GoodPolynomial.lean:35–49`); the signed adapter in
`Birkhoff/Defs.lean:35–38` uses the bounded `Fin 9` encoding of integer modes. Their equality
is not claimed or required, but their nonzero-locus equivalence must be proved. The sorted
spectral equality alone does not reconcile these different products.

Refutation pass: searched all `KAM/Planetary/PlanarTorsion` occurrences of `p11c_phi4` and all
project files combining that identifier with upstream `good`, `nr4`, or the spectral bridge.
Only `Generic.lean` combines the adapter with that upstream spectral equality; it contains no
such equivalence, even as a local assertion. Checked the imported `GoodPolynomial.good_set` /
`good_ne_zero_iff`: they characterize the upstream product but never mention the adapter.
Checked T16's `Birkhoff/Choice.lean:48–101`: `p11cB_NR4` proves a useful implication to NR4
of `2σ` in action coordinates, but not the two-way axis-locus equivalence, and Choice is not
imported by Generic (which imports Defs only). `p11cGe_phi4_analytic` and
`p11cGe_phi4_exists` prove analyticity and existence, not locus equality. Thus renamed or
imported support does not discharge the stated gate.

Required repair: supply a sorry-free pointwise equivalence (or a proved composition of both
directions) on the physical axis cone, using the actual integer-mode enumeration and upstream
NR4 characterization. Export it where consumers can use it. No change to the signed
`p11c_phi4` definition or `torsion` statement is needed. This report does not implement repairs.

## Node and public declaration ledger

All names below are in `KAM.Planetary`. PASS here concerns the individual statement/proof;
the package remains FAIL because of F1.

| Node / role | Declaration or proof location | Verdict | Evidence |
|---|---|---|---|
| `bpP:p11b:torsion`, signed surface | `torsion`, L96–131 | PASS, correspondence gate F1 open | Declaration header through its conclusion is byte-identical to signature L645–653; all eight conjuncts proved without extra premises. |
| `stepP:p11b:to-an` | `p11cGe_det_analytic`, L62–67 | PASS | Expands the 2×2 determinant; entry analyticity is obtained from actual `beta_properties`. |
| `stepP:p11b:to-an`, entrywise support | imported `beta_properties` in Beta | PASS as consumed interface | The source step's entrywise claim is retained, not replaced by determinant analyticity alone; no duplicate implementation or audit of T13 claimed. |
| `stepP:p11b:to-pt` | `p11cGe_det_neg`, L69–94 | PASS | Produces a strictly negative point from T19's relative determinant error. |
| `stepP:p11b:to-id` | `torsion`, L105–131 | PASS for signed loci; FAIL for full source correspondence | Connected/open cone, generic with r=1 and r=2, explicit nonzero/zero-locus rewrites; F1 prevents identification of the adapter with the source Phi4 locus. |
| sigma analyticity support | `p11cGe_sigma1_analyticAt`, L30–37 | PASS | Uses trace minus the first eigenvalue, locally on the open cone. |
| product analyticity support | `p11cGe_phi4_analytic`, L39–45 | PASS | Finite product of analytic linear forms in the sorted eigenvalues. |
| domain adapter | `p11cGe_axes_eq`, L47–49 | PASS | Exact equality between `{0<a0<a1}` and `SecularForm.axes 2`, both directions proved. |
| nonzero point support | `p11cGe_phi4_exists`, L51–60 | PASS | Actual upstream good point supplies every encoded nonzero mode; no nonvanishing premise is assumed. |
| required Part-9 locus adapter | no declaration / local proof found | FAIL | F1; the existential witness cannot replace a pointwise equivalence. |

No unsigned export is named after a graph node while stating a weaker substitute. The helper
names use the distinct `p11cGe_` prefix. T21's full patch and its frequency/Birkhoff consumers
are outside this slice; no geometric-only patch is substituted for them.

## Expanded binders and definition classification

For `torsion`, every logical premise is a literal source standing assumption. Source locators:
Part 11b setting and graph `bpP:p11b:torsion` SOURCE_HYPOTHESES; signed L645;
`Setting.lean:31–38` for the actual data, validity and axis predicate.

| Expanded binder / premise | Bin | Justification |
|---|---|---|
| `p : PlanarData` | TYPING | Physical parameters `G`, `m0`, and `m : Fin 2 → ℝ`; no proof fields. |
| `hp.1 : 0 < p.G` | STANDING | Positive gravitational constant. |
| `hp.2.1 : 0 < p.m0` | STANDING | Positive central mass. |
| `hp.2.2 : ∀ i : Fin 2, 0 < p.m i` | STANDING | Positive two planetary masses, universally quantified on Fin 2. |

Counts: SOURCE 0, STANDING 3, TYPING 1, RULED 0, EXCESS 0. `hp` has no hidden estimate,
analyticity, nonvanishing, or conclusion field. For `sigma1_analyticAt` the additional implicit
`a : Fin 2 → ℝ` is TYPING and `ha : a ∈ p11c_axes` is SOURCE (the stated analytic domain):
SOURCE 1, STANDING 3, TYPING 2, RULED 0, EXCESS 0. Each of `phi4_analytic`, `phi4_exists`,
`det_analytic`, and `det_neg` has exactly the four expanded rows above. `axes_eq` has no
binders or premises. There are no instance binders introduced by the target.

No new `def`, `abbrev`, or `structure` occurs in Generic. Definition classification for the
audited file: N/A (zero). BODY_MATCH / PUBLIC_CARRIER / WELL_DEFINEDNESS / CHARACTERIZATION /
CHOICE_INDEPENDENCE: N/A for new definitions. The imported `p11c_phi4` is T16's literal finite
product, not a choice or fallback; its own package audit remains separate. `p11c_beta` is the
existing explicit invariant matrix, and its determinant is the actual matrix determinant.
The exact inherited `p11c_sigma_eq_sigma` connects the physical eigenvalues to upstream ones.
The remaining unpaid item is F1, not an assumed bridge hidden inside a definition.

## Proof checks and attempted mathematical refutations

For the negative point, C>0 and 0<alpha0<=1 are obtained before t is chosen. The actual choice
is `t = min (alpha0/2) (1/(C+1))`; hence 0<t<alpha0, t<=1/2, and Ct²<1. The T19 bound makes
`det(beta)/(-117/(16*m0²)*t³)` positive. The denominator is strictly negative because m0>0
and t>0, so the determinant is strictly negative. All constants are internal witnesses;
no uniform constant dependence has been widened in the public theorem.

For genericity the proof does not assume one point where both factors are nonzero. It gives
each analytic factor its own nonzero witness, as required by `Nondegeneracy.generic`.
The axis equality and `Nondegeneracy.isConnected_axes 2` supply connectedness, while
`p11c_axes_isOpen` supplies openness. The r=2 output is converted to the product nonzero
locus using `mul_ne_zero` semantics, and its exceptional union to the product zero locus
using `mul_eq_zero`. The consumed generic theorem explicitly proves measure-zero, not just
empty interior. No conditional analytic theorem is promoted without its premises.

Project import closure: 276 modules, 58 frozen modules, all 58 manifest entries SEALED
definitions; zero providers and zero DRAFT_SORRY frozen imports. No frozen theorem is used to
smuggle a proof hole. Main theorem and all six new helpers have only standard axioms.

The only second public short name `torsion` found globally is the pre-existing definition
`KAM.torsion`; the new signed name is `KAM.Planetary.torsion`, not a root declaration.
Both qualified names were checked in the probe. The six helper short names each have exactly
one declaration in KAM. No root shadow or namespace-reopening change occurs in Generic.

## Verification commands and output

All auditor Lean activity was sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The build used the required gate, which acquired slot 1. No library clean/rebuild was run.
The lint script's ABI subprocess ran after kernel replay finished and before the probe.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
     /root/code/KAM-inp-p11c-t20 KAM.Planetary.PlanarTorsion.Generic
   ```

   Exit 0: `Build completed successfully (9322 jobs).` Dependencies emitted replayed
   unused-variable, unused-simp, and deprecation warnings. No target error or heartbeat failure.

2. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Planetary.PlanarTorsion.Generic
   ```

   Exit 0; complete output: `replaying KAM.Planetary.PlanarTorsion.Generic`.
   There is no separate T20 provider module.

3. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the expressly permitted stale generated root:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1148 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other forbidden token, line-width, size, module-system or manifest failure was printed.
   Target-local independent scan: no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
   `EuclideanSpace`, or resource override; 135 lines, maximum width 98 characters.

4. Signed-type / assembly and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T20Audit.lean
   ```

   The probe copies the complete literal signed declaration as
   `T20Audit_exact_signed_torsion` with body `by exact KAM.Planetary.torsion p hp`, and checks
   `example : type_of% @T20Audit_exact_signed_torsion := @KAM.Planetary.torsion`.
   It queries axioms for all seven new theorems and the consumed `beta_properties`,
   `Nondegeneracy.generic`, and `Nondegeneracy.good_point`, and checks both qualified torsion
   names. **Exit 0**, no errors or warnings. The axiom output was:

   ```text
   'KAM.Planetary.p11cGe_sigma1_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cGe_phi4_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cGe_axes_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cGe_phi4_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cGe_det_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cGe_det_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.beta_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.generic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.good_point' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Both qualified torsion names retain their distinct expected types. The scratch file was
   removed after validation.

5. Protected-path and whitespace checks:

   `git diff inp...HEAD -- KAM/Frozen manifest README.md`: empty.
   The broader required protected-path check also includes `KAM.lean`: it is **not** empty,
   containing ten inherited generated import additions. `git log inp..HEAD -- KAM.lean`
   attributes them to merge `cea85d47`, before the T20 work; `git diff 9ca84daf^ HEAD -- KAM.lean`
   is empty. This is integration ancestry, not an auditor or T20 generated-file edit.
   `git diff --check inp...HEAD`: exit 0, only the multiple-merge-base warning.

## Errata, limitations and closeout

No new suspected defect in a pinned paper or blueprint statement was found. Primary source
PDFs were not independently re-audited; fidelity was checked against the pinned local blueprint,
signed text, graph record and design obligations. F1 is an implementation omission. The prior
CP11 coefficient candidate mentioned in the design is not newly verified by this audit.

No implementation deviation was introduced. The only authorized path decision was to use the
user's exact worktree report destination. No source conclusion was weakened, no assumption
added, and no failed gate silently repaired. Full diff inventory and inherited root changes are
reported separately from the target's verdict. No frozen headline, T16, T19, or T21 closure is
claimed. Acceptance requires F1 to be repaired and re-audited; build/axiom success does not
discharge that correspondence requirement.

Final validation: HEAD, target hash and signed-signature hash unchanged; all seven public
declarations and all four assigned graph records classified; one retained completeness
finding with its refutation checks recorded. Report whitespace check produced no diagnostics
(`git diff --no-index --check /dev/null <report>` returns 1 for the new-file difference);
an independent Python trailing-whitespace/control-character check passed. Final git status
adds only this report to the pre-existing untracked handoff, with no tracked-file edits.
