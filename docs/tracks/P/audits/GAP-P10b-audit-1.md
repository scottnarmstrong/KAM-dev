# GAP-P10b independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gp10b`.
Audited HEAD: `20bf611a462babe8cca749412bf2b1fb2266042a`.
Compared `inp`: `91dc441efbdc614303b82bef60b36c8fbc45819b`.

## Verdict

**PASS WITH NOTES** for GAP-P10b; **PASS** for the literal mathematical contract of
`bpP:p10:scaling`. No frozen anchor is provided or sealed by this package. The
package consists of unsigned graph exports, so frozen-provider type equality,
SIGNED signature equality, and a frozen seal-body probe are not applicable.

**One declaration states the whole scaling node:**
`KAM.Planetary.Nondegeneracy.scaling_index_amount` (lines 45–82).
`rnd_def_scale_iff` alone states only its R-nondegeneracy clause, in greater
generality. The combined export does not take a dependency output as a premise.
All seven nodes skipped by the handoff are actually `PROVED` in the checked-out
graph. No omitted `FiniteTypeNodes.lean` is required under the explicit overnight
skip ruling.

The notes concern inherited comparison history and graph bookkeeping. Regeneration
of `KAM.lean` belongs to the orchestrator and is not a package finding under the
handoff ruling. This audit does not certify a planetary headline or other packages.

## Authority and comparison scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package-audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local handoff including
its AUDIT FOCUS, track P's statement/conventions, and GAP-PLAN-P.md's P10 node table
and GAP-P10b section (lines 297–305, 428–440). Mathematical audit scope is exactly
`KAM/Planetary/Nondegeneracy/RelationNodes.lean`; imported definitions and proofs
were inspected as needed. The user's exact worktree report destination overrides
the generic brief's main-worktree destination.

Ran `git diff inp...HEAD`, its file/stat inventory, the scoped Lean diff, and the
graph/protected-path diffs. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 67f7f681d2178e83ec6223c1781121dd5c221736
```

`git merge-base --all inp HEAD` returns both `67f7f681d2178e83ec6223c1781121dd5c221736`
and `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`. The chosen three-dot comparison has
15 files, 1921 insertions and 36 deletions. Besides RelationNodes, it includes the
inherited GAP-E/P11A-P8a files PreparedBasic, SlowB2Kappa, AssemblyK6 and Situation,
their reports/handoffs, graph records, and four generated root imports. Those
packages are outside this AUDIT FOCUS; their proofs are not re-audited here.

The exact brief check
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
only four `KAM.lean` import additions appear. They are inherited from orchestrator
commit `8dc8bedc` ("Regenerate KAM.lean (GAP-E, P11A-P8a)"). Both
`git diff 8dc8bedc HEAD -- KAM/Frozen manifest KAM.lean README.md` and the same
protected-path comparison for `HEAD^ HEAD` are empty. The GAP-P10b commit itself
adds only the 86-line RelationNodes module. No frozen, manifest, README or root
change is attributable to GAP-P10b. This records the literal full-diff exception
without silently treating the protected-path diff as empty.

## Node and declaration table

All declarations below are in `KAM.Planetary.Nondegeneracy`.

| Node / declaration | Lean declaration and locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p10:scaling`, R-nondegeneracy clause | `rnd_def_scale_iff`, RelationNodes:34 | PASS | Equivalence for any set/map and positive diagonal; stronger than the analytic planetary setting. Not the whole node by itself. |
| `bpP:p10:scaling`, whole node | `scaling_index_amount`, RelationNodes:45 | PASS | One conjunction gives R-nondegeneracy iff, finite-index iff, equality of indices for arbitrary existence witnesses, and both squared diagonal bounds at the common index. |
| `stepP:p10:F-A` | `f_nonzero`, SymmetricRelation; DEPGRAPH:18571 | PASS, skipped | `LEAN_STATUS: PROVED`; graph names its proved parent and audit S10-F:38. |
| `stepP:p10:F-B` | `f_nonzero`, SymmetricRelation; DEPGRAPH:18601 | PASS, skipped | `PROVED`; local to parent under ruling 01:20(b), audit S10-F:26. |
| `stepP:p10:F-C` | `f_nonzero`, SymmetricRelation; DEPGRAPH:18633 | PASS, skipped | `PROVED`; local to parent under ruling 01:20(b), audit S10-F:27. |
| `stepP:p10:ft-pt` | `finite_type`, FiniteType; DEPGRAPH:18848 | PASS, skipped | `PROVED`; local to parent, audit S10-C:46. |
| `stepP:p10:ft-cover` | `finite_type`, FiniteType; DEPGRAPH:18876 | PASS, skipped | `PROVED`; local to parent, audit S10-C:26. |
| `stepP:p10:ft-min` | `finite_type`, FiniteType; DEPGRAPH:18904 | PASS, skipped | `PROVED`; local to parent, audit S10-C:37. |
| `stepP:p10:st-prod` | `stability`, Stability; DEPGRAPH:19020 | PASS, skipped | `PROVED`; local to parent, audit S10-S:31. |

Skipped-node PASS means the authorized status/parent-reference check passed; it
is not a new independent audit of those parent proofs. No AMENDMENTS file was
needed because DEPGRAPH itself contains all seven PROVED records.

## Literal statement and proof audit

Controlling record: `docs/graph/P/DEPGRAPH.md:18787–18816`.
`SOURCE_QUANTIFIERS` says "none beyond the setting of Part 10". Its conclusion is:
"R-nondegeneracy of varpi tilde is unchanged by the positive diagonal rescaling"
and "the index is unchanged and the amount changes by a factor between the squares
of the smallest and largest diagonal entries". This agrees with
`blueprint-P/parts/p10-nondegeneracy.tex:191–193` and the index definition at
lines 210–212.

* **Premises and quantifiers.** The combined theorem fixes B/K, openness,
  compactness, nonemptiness, inclusion, positive target dimension, the analytic
  map, then the diagonal and its positive lower/upper bounds. It introduces no
  existential numerical constant with widened dependence. It drops connectedness
  and the specific planetary formula, so applies more generally than the source.
  Arbitrary `lo`/`hi` enclosing all finitely many positive entries give a stronger
  comparison: choosing their finite minimum/maximum gives the source's extremes.
  Source frequencies with factors 2 and 1/(2π) are special cases. No affine
  change of the input is claimed by this node or by this export.
* **No dependency output premise.** `hB`, `hK`, `hKn`, `hKB`, `hm`, `hAn`, `hlo`
  and `hs` are domain, regularity and diagonal data. In particular neither
  `scaling_amount` nor index invariance is assumed. The existential witnesses
  `h` and `h'` at lines 52–54 occur inside the third conjunct of the conclusion,
  not before the theorem's conclusion. They are typing data for the already
  defined partial index, exactly as the blueprint defines the index only when
  some positive beta exists. The preceding conjunct proves equivalence of that
  existence condition, so this is not a hidden conclusion-shaped hypothesis.
* **Carriers and amount.** `Vec d` is `Fin d → ℝ` (SecularForm/Basic:32).
  `sphere m` is the Euclidean sphere expressed by `length2`, not the Pi-norm
  sphere. `squaredForm` is literally `(∑ i, c i * ω y i)^2`.
  `betaMu` definitionally unfolds to the `betaFamily` expression in the export;
  `index_def` is `Nat.find` of the least positive order. Thus both bounds are
  for the squared convention on the same compact patch, at each map's equal
  index, without a norm or normalization change.
* **Proof.** The iff reverses the diagonal with component inverses and invokes
  the existing `scaling`. For every order, the existing `scaling_amount` supplies
  both inequalities. Positivity transfers forward through `lo² > 0`; the reverse
  uses nonnegativity of beta and the upper bound to contradict a zero original
  beta. `Nat.find_congr'` then identifies the least positive orders. Rewriting
  by that equality supplies the two amount bounds. No circular premise, fallback
  object or unchecked arithmetic step occurs.
* **Consumers.** The direct retained consumer `stepP:p11:nd`
  (DEPGRAPH:19391 ff.; blueprint p11:50) uses positive frequency rescaling;
  the first conjunct supplies it. Its separate input dilation is not charged to
  this scaling node. There is no SIGNED declaration or deliberate signed narrowing
  in the audited file.

## Definition classification and import hygiene

There are **no new def/abbrev/structure declarations**, instances, local axioms,
or bundled assumptions. Both additions are theorems. Inherited definitions were
checked at AnalyticZeros:38, FiniteType:32–40 and DiagonalTensor:34–38:
`rnd_def` is the literal no-linear-relation predicate; `betaFamily` the infimum
of jet maxima; `betaMu` its squared-form/sphere specialization; `index_def` uses
an existence witness, with no undefined-index fallback. The theorem's nonempty
compact analytic domain is precisely where the existing amount comparison
applies. No result here relies on values outside that domain.

A recursive source import scan found 102 KAM modules, no provider, and no frozen
theorem module. The 47 imported frozen anchors are all definitions with manifest
state `SEALED`; no DRAFT_SORRY anchor enters the closure. Direct imports are Mathlib,
AnalyticZeros, Frequency and Stability. Both new short theorem names occur at only
one declaration site in KAM; both remain under the intended Nondegeneracy namespace.
There is no reused public helper short name or harmful root shadow.

## Independent verification

All Lean/Lake invocations below were serialized and run with
`LEAN_NUM_THREADS=1` and `nice -n 5`. No clean/update/cache operation, package
mutation, source repair or state-changing git command was run.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp10b KAM.Planetary.Nondegeneracy.RelationNodes
   ```

   Exit **0**. Output begins `[inp-gate] slot 3 acquired 02:33:30 for
   KAM.Planetary.Nondegeneracy.RelationNodes` and ends
   `Build completed successfully (9148 jobs).` Existing dependency linter warnings
   were replayed; no warning names RelationNodes. The job count is the targeted
   cached dependency plan, not a library clean rebuild.

2. Independent conclusion/application and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-gp10b.lean
   ```

   Exit **0**. The probe restated the iff and whole conjunction, expressing the
   latter's amounts and existence witnesses through `betaMu`, and applied the
   exports to all their explicit premise binders in order. This independently
   checks the `betaFamily`/`betaMu` definitional identification. Output:

   ```text
   'KAM.Planetary.Nondegeneracy.rnd_def_scale_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Nondegeneracy.scaling_index_amount' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (the only new lemma module; no provider exists):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.RelationNodes
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Planetary.Nondegeneracy.RelationNodes
   ```

4. Full source lint, including frozen guard and elaborated ABI hashes:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely for the expressly permitted generated-root mismatch.
   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1202 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint diagnostic occurs. No generated file was regenerated.

5. `git diff --check inp...HEAD`: exit **0**, no whitespace diagnostic (only the
   multiple-merge-base warning). `git diff --check`: exit **0**. Scoped lexical
   scan: no forbidden proof tokens, resource options or prohibited ambient type.
   File size **86 lines**, maximum line width **97 Unicode characters**.
   Copyright, `module`, public imports, module docstring and public section all
   present. Report whitespace was checked separately because it is untracked.

## Notes, defects, uncertainties and deviations

* **Graph bookkeeping:** DEPGRAPH:18813–18815 still says `LEAN_STATUS:
  NOT_STARTED`, `LEAN_REF: -`, and "R-nondegeneracy and index invariance are not
  exported; not marked proved". The latter is now stale: this package exports
  both, and `scaling_index_amount` states the entire node. The orchestrator can
  update the record after accepting this audit. No graph was edited by the auditor.
* **Historical protected-path difference:** the four inherited KAM.lean imports
  make the generic all-history protected-path check nonempty, as documented
  above. The package commit itself satisfies the protected-path restriction.
* **Source defects:** no suspected mathematical defect or contradiction was
  found in the controlling scaling remark or index definition. No new erratum
  or mathematical deviation is proposed. This is a Lean/blueprint audit, not a
  fresh transcription audit of CP09's pinned PDF.
* **Limits:** index/amount assertions correctly concern indices where defined;
  they do not assert finite type for an arbitrary analytic map. The export proves
  finiteness equivalence, and existing finite-type dependencies supply finiteness
  in the source's nondegenerate setting. No seal or headline closure is claimed.

Only this report was written in the repository. The pre-existing untracked
`GAP-P10b-handoff.md` was left intact. The audit probe was deleted from
`.lake/abi-scratch/`. No tracked source, frozen file, manifest, graph, generated
file or git state was modified.
