# N-CLOSE-LEAN independent audit 2

Audited 2026-10-29 in `/root/code/KAM-inp-ncloselean`, HEAD
`3949c21c4db37e8c95932bd89eea68b4e9192a7f`, against current `inp`
`9ce9e8482be9e2a6cc40e532d7b1dd767572da1b`, using `git diff inp...HEAD`.
Repair commit: `253b2b84`. The user's exact worktree report destination overrides
the generic brief's main-worktree destination.

**Overall verdict: PASS WITH NOTES. `bpN:p10:hypotheses-check`: PROVED.
Audit-1 finding F1 is closed.** The notes are the explicitly permitted stale
root and an inherited off-domain extension convention. Neither leaves an unpaid
clause of this node. `head_theorem1_setting` passes. No frozen anchor or provider
is changed; this is helper-node closure, not a new seal or a re-audit of the six
existing N anchors.

## Scope and delta

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief, handoff
including ROUND 2 FOCUS, audit 1, and `.drafts/handoff-N-CLOSE-LEAN-R2.md`.
Node authority: `blueprint-N/parts/p10-assembly.tex:59-89` and
`docs/graph/N/DEPGRAPH.md:12999`, including SOURCE_HYPOTHESES,
SOURCE_QUANTIFIERS, SOURCE_CONCLUSION and CONSTANT_SCOPE. The track N statement,
relevant frozen headline/definitions, and Part 9 setting were read for meaning.

The full three-dot diff has four files: HypothesesFull (145 added lines),
Confinement (8 added lines), audit 1 (202 added lines), handoff (59 added lines).
Only the two specified Lean files receive a code verdict. Relative to audit-1
HEAD `0199dcea`, the entire Lean delta adds the two missing conclusion conjuncts,
their proof terms, and wraps the enclosing refine over two lines. No other Lean
change occurred; Confinement is unchanged since audit 1.

## F1 closed

The source at `blueprint-N/parts/p10-assembly.tex:62` requires
“U ⊂ B(0,5R/8) ⊂ B(0,R) ⊂ 𝓑_s(R)”. HypothesesFull:37-38 now exports:

```lean
actionBall n (5 * p.R / 8) ⊆ actionBall n p.R
actionBall n p.R ⊆ realActionDomain n p.R p.s
```

Both quantify over the entire intermediate balls, independently of membership
in U. Proofs are `ball_subset_ball (by linarith [hp.hR])` (line 121) and
`ball_subset_realActionDomain hp.hR hp.hs` (line 117). Both use standing
positivity only. The U memberships, V and W inclusions, P nonemptiness and
half-ball inclusion remain. A fresh elaborated probe extracts the two claims
from the exported conjunction itself, rather than only proving them separately.

## Declaration and clause review

All declaration names below are in `KAM.Nekhoroshev`.

| Node / clause | Declaration or location | Verdict | Reason |
|---|---|---|---|
| `bpN:p10:hypotheses-check` | `hypotheses_check_full`, HypothesesFull:31-87 | PASS / PROVED | Complete (a)-(h) source conclusion; F1 repaired. |
| (a) | HypothesesFull:36-46 | PASS | V inclusion, full U/ball/domain chain, W inclusion, P nonempty, half-ball inclusion. |
| (b) | HypothesesFull:48-52 | PASS | Holomorphy, reality, complex Hessian bound on V, with explicit Euclidean norms. |
| (c) | HypothesesFull:54-57 | PASS | Quantitative quasi-convexity for every real direction; positive mu and mu ≤ Bc. |
| (d) | HypothesesFull:59 | PASS | Literally `p.r0 ≤ p.ell / (2 * p.B)`. |
| (e), setting | HypothesesFull:61-67 | PASS | Analytic real class, summable weighted bound, positive epsPrime ≤ eps1, genuine setting and identities for A, eps1, a, R0. |
| (f) | HypothesesFull:74-75 | PASS | Every I0 in the open half-ball has the Euclidean lower bound and strict exceptional-branch exclusion. |
| (g) | HypothesesFull:69-72 | PASS | Actual setting's omega0Ball maximum, both frequency bounds, A²s1/Omega0 ≥ 2T. |
| (h) | HypothesesFull:77-87 | PASS | Reality and Hamiltonian equality on W; specialize Hlocal to realHamiltonian for field equality. Locality statement is stronger. |
| `stepN:p10:cf-setting` exposure | `head_theorem1_setting`, Confinement:99-104 | PASS | Exact type and ordered premises of private cf_setting, with direct application body. |

`HeadParams` has six positive real data indexed by n. `HeadHyp`
(Interfaces/Constants:73-78) is exactly H1-H5; hf, hε, hε0 give H6-H7.
No orbit, stability or conclusion-shaped hypothesis is introduced. The data and
their defined constants precede h, f, ε. No constant gains dependence on these
functions or initial conditions.

Presentation order is (a),(b),(c),(d),(e with setting and g),(f),(h). Putting (g)
under the existential setting preserves its dependency: one setting precedes
all I0. The proof argument hP does not restrict the open-half-ball domain,
since item (a) supplies membership in P for every such I0. Conjunction ordering
changes no source quantifier scope. V, U, W, epsPrime, Omega0 and T0 are expanded
as their defining expressions, not replaced by arbitrary free objects.

Removing the public wrapper and its docstring restores the Confinement file
from inp byte for byte. Private cf_setting, its proof and consumers are unchanged.

## Definitions and inherited convention

There are **no new def, abbrev or structure declarations**. Relevant existing
objects were inspected:

- P is the closed maximum-norm half-ball, centralSet its real inclusion image,
  V its complex maximum-norm tube, U its real preimage, W = univ × U.
  Wdom agrees with the source real strip domain for positive R,s.
- `Theorem1Setting` (Poschel/Setting:34-49) is the genuine Part 9 record:
  dimension, positive parameters, holomorphy, reality, complex Hessian bound,
  quasi-convexity, radius, analytic real perturbation and finite weighted norm.
  It has no orbit/confinement field. Numerical perturbation smallness is supplied
  outside the record as required.
- `WBound` (Weighted/Norm:62-63) includes summability and the bound on every
  coefficient sum. No unsummable-series fallback supplies the estimate.
- `omega0Ball` (Poschel/Frequency:391-393) fixes center I0 and Euclidean radius
  r0/thmA. Its maximum (lines 270-275) is the supremum of the genuine Euclidean
  frequency norm over that closed ball. `omega0` (395-409) provides attainment
  and the center bound on the compact nonempty ball inside the real tube.
  This is the source Omega0, with no unguarded supremum used in this proof.
- `realH` (Stability/Setting:52-53) is the total real-part restriction, as is
  frozen realHamiltonian. Part 9 blueprint line 37 says “and 0 off W”. This
  inherited global extension convention differs from Lean's total real part.
  All new claims concern the open set W, and locality handles equal local
  extensions. No off-W equality with the zero extension is asserted. This
  records an inherited blueprint/implementation convention discrepancy, with
  no effect on the package verdict.

No new suspected pinned-source defect or blueprint contradiction was found.
F1 was an implementation omission, not a source erratum. Existing N-HEAD's
separate source gap F-N1 is outside this N-HEAD-C helper audit. No auditor repair
or deviation was introduced.

## Independent checks

All audit-launched Lean/Lake checks were serialized with `LEAN_NUM_THREADS=1`
and `nice -n 5`, including lint, whose ABI step invokes Lean. No clean, cache
fetch, package modification, resource override or state-changing git was used.

1. Protected paths and whitespace:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   ```

   Both exit 0, empty output. Protected diff is empty.

2. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-ncloselean KAM.Nekhoroshev.Assembly.HypothesesFull
   ```

   Exit 0. Output starts `[inp-gate] slot 1 acquired 17:36:27 for KAM.Nekhoroshev.Assembly.HypothesesFull`
   and ends `Build completed successfully (3337 jobs).` Replayed unused-variable
   warnings occur in unchanged Period, Gradient, Maximal, Blocks, BlockHypotheses,
   ODE.Exit, Transfer, Nonresonant, Resonant and ResonantStabilityCore dependencies.
   No warning or heartbeat failure in either audited module.

3. Full-signature, conjunct-extraction, wrapper and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/NCloseAudit2.lean
   ```

   Exit 0. The probe copies the entire current proposition as an example and
   applies hypotheses_check_full with all binders; extracts F1 using H.1.2.1
   and H.1.2.2.1; and checks the wrapper against its full setting type.
   Exact axiom output:

   ```text
   'KAM.Nekhoroshev.hypotheses_check_full' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.head_theorem1_setting' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Provider/frozen type and seal-body probes are inapplicable: these are helper
   exports, and no frozen statement or body changes.

4. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.HypothesesFull KAM.Nekhoroshev.Assembly.Confinement
   ```

   Exit 0; exact output:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Confinement
   replaying KAM.Nekhoroshev.Assembly.HypothesesFull
   ```

5. KAM/Mathlib public short names:

   ```sh
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-ncloselean KAM.Nekhoroshev.Assembly.HypothesesFull KAM.Nekhoroshev.Assembly.Confinement
   ```

   Exit 0: `short-name check OK (no reused public short name)`.
   Direct scans found no sorry, admit, axiom, unsafe, opaque, native_decide,
   EuclideanSpace or resource overrides in either audited file. Copyright,
   module command, public imports, module docstring and public section present.
   HypothesesFull: 145 lines, maximum 93 characters; Confinement: 178 lines,
   maximum 100 characters. Recursive import inspection covered 155 project
   modules and found no provider or frozen theorem import, hence no dependency
   on a DRAFT_SORRY theorem. A script confirmed removing only the public wrapper
   restores Confinement from inp byte for byte: `True`.

6. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the explicitly permitted stale generated root. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1343 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Hygiene: PASS WITH NOTES under the brief's generated-root exception. The
   root was not regenerated.

## Disposition

F1 is closed without an extra premise or omitted conclusion; the node can be
recorded PROVED. Consumers destructuring item (a) must account for two inserted
conjuncts. No Lean source, graph, frozen file, manifest, generated root, README
or git state was changed by this audit. The only retained artifact is this
report; audit scratch probes and logs were removed. There are no unresolved
package-specific mathematical uncertainties.
