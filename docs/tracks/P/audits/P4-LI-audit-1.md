# Independent package audit 1: P4-LI

Overall verdict: **PASS WITH NOTES** for the P4-LI infrastructure package, with the independent validation receipts below. No frozen anchor is proved by this package; **P-G is not seal-ready on this evidence**. Provider/frozen-type and seal-body checks are inapplicable here. Instead, all four implemented signatures are checked against the design types and explicit binder applications.

## Scope and evidence

Worktree: `/root/code/KAM-inp-p4li`; audited HEAD `778a9bd71ab0b3812890329d79a980514c09b934`. Only `KAM/Planetary/PGMeasure/CompactLipschitz.lean` is audited, as the handoff explicitly requires. Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff/AUDIT FOCUS, P45 design row and proof plan, all three design audits, the four shared signatures in `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, P4 blueprint lines 13 and 39–60, track-P statement, frozen P-G and its fast-frequency/inverse definitions, and the imported PG setting.

The requested `git diff inp...HEAD` warns `multiple merge bases, using 597e0b09ec12eb4a91c7682b7ae62c379f7e4efe` and includes 31 files / 4,841 insertions. `inp` was `f11c90357967f666b1673409df890dbcec823dff`; `inp-p45s` was `597e0b09ec12eb4a91c7682b7ae62c379f7e4efe`. The comparison against `inp-p45s` likewise includes inherited campaign work. These broader changes are outside the explicitly restricted audit. `git show --stat HEAD` identifies the actual P4-LI commit as exactly one new 170-line file. Its scoped diff against both requested baselines is that same file.

**Protected-path note:** the full `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**: it contains 15 inherited generated-root imports. They belong to earlier root-regeneration commits `4dad814` and `ef8fc42`, not P4-LI. The same comparison restricted to `KAM/Frozen manifest README.md` is empty; `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Thus the blanket branch-level protected-path condition is not literally satisfied, while this package itself changes no protected file. No root regeneration was performed during this audit.

## Declaration and node decisions

All names below are in `KAM.Planetary`, except the private helper's generated internal name.

| Node / role | Declaration and production line | Verdict | Reason |
|---|---|---|---|
| `bpP:p4:ext-deriv` | `ext_deriv`, 31 | PASS | Exact design signature: analytic derivative and C1 regularity. AnalyticOnNhd is neighborhood analyticity, so no separate openness premise is necessary. Local Lipschitz consequences are supplied separately. |
| `stepP:p4:lc-local` | private `lip_local`, 37 | PASS | Joint continuity bounds the partial derivative near the point; max-norm product balls stay in O; MVT is applied on a convex ball. Compact K itself need not be convex. |
| `bpP:p4:lip-compact` | `lip_compact`, 62 | PASS | Exact printed partial-C1 premises and uniform conclusion, with nonnegative constant additionally explicit. No joint-C1 hypothesis substituted. |
| `stepP:p4:lc-contra` | proof of `lip_compact`, 70–117 | PASS | Violating triples have compact subsequence; bounded f and n ≤ φ(n) force endpoint distances to zero; both endpoints converge to the same point; local bound contradicts the violating quotient for φ(n) ≥ M. |
| distinct conditional helper | `lip_compact_c1`, 120 | PASS | Exact separate design signature. Partial derivative identified as joint derivative composed with inr; its continuity follows from C1 on open O. It does not replace `lip_compact`. |
| `bpP:p4:lip-inverse` | `lip_inverse`, 139 | PASS WITH NOTES | Exact design signature, including implicit dimension a and unchanged unused hW. Extracts the inverse supplied by frozen HasFastDiffeomorphism; L ≥ 1 and positive enclosing R are data-only witnesses. R is the documented enlargement below. |
| `stepP:p4:li-cont` | proof of `lip_inverse`, 148–154 | PASS | Analytic H0 gives continuous derivative; evaluations at basis vectors give frozen fastFrequency. Bounded closed closure V is compact, and its continuous image is compact. |
| `stepP:p4:li-lip` | proof of `lip_inverse`, 155–166 | PASS | Apply the separately proved C1 corollary with p=0 to that compact image in the open frozen frequency image. Constants are enlarged by max with 1. |

There are four public theorems and one private theorem; no other new declaration, global instance, custom norm, or notation. Exact binder order, max-norm carriers `Fin n → ℝ`, partial-derivative hypotheses, and constant dependence match the design. Empty compact sets and zero dimensions require no extra assumptions. No conclusion-shaped premise or bundled hard step was introduced.

## Definition classification and frozen attachment

**No new `def`, `abbrev`, or `structure`** occurs in the audited file. Local witnesses and lambda maps are ordinary proof constructions. The selected g is obtained directly by destructuring the frozen predicate at line 148; it is never replaced by a totalized inverse or a junk fallback. Its unconstrained values outside the frequency image are not used. On that image the left-inverse identity uniquely fixes it. The frozen right-inverse clause is available but unnecessary for these conclusions.

The recursive KAM import closure contains 16 modules, zero provider imports and zero frozen-theorem imports. Thus there is no imported DRAFT_SORRY theorem or sealed-theorem state to adjudicate. The imported frozen definitions supply source objects, not assumed theorem conclusions. The broader imported PGData is not an argument of any of these four results.

## Independent validation

All completed Lean checks below are independent auditor runs. Lean invocations are serialized, with `LEAN_NUM_THREADS=1`; build uses the mandated compile gate and nice level 5. No clean/update/cache retrieval or generated-root write was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4li KAM.Planetary.PGMeasure.CompactLipschitz
   [inp-gate] slot 2 acquired 08:31:16 for KAM.Planetary.PGMeasure.CompactLipschitz
   ⚠ [9062/9062] Replayed KAM.Planetary.PGMeasure.CompactLipschitz
   warning: KAM/Planetary/PGMeasure/CompactLipschitz.lean:140:5: Variable name `hW` is not explicitly referenced.
   Build completed successfully (9062 jobs).
   exit 0
   ```

   This targeted invocation replayed the package; it was not a clean rebuild of the library. The unused binder preserves the agreed signature. No heartbeat issue occurred.

2. Signature/axiom probes:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4LIAudit.lean
   'KAM.Planetary.ext_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.P4LIAudit.ext_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lip_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.P4LIAudit.lip_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lip_compact_c1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.P4LIAudit.lip_compact_c1' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lip_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.P4LIAudit.lip_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The scratch fixture imports only the production module, copies each complete type from the shared design signatures under a fresh namespace, and proves it by applying the production theorem to exactly its explicit binders in order. Two `type_of%` assignments per name check the full polymorphic types in both directions. All four textual signatures also match after whitespace normalization and making the section's implicit a binder explicit. No design sorry body was copied. This checks the actual implementation against the design, not a fixture polluted by the design stubs.

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.CompactLipschitz
   replaying KAM.Planetary.PGMeasure.CompactLipschitz
   exit 0
   ```

   One invocation covers the sole module containing all four exports and the private helper. There is no separate new provider or lemma module in this package.

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (480 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only failure is the brief's explicitly permitted stale generated-root condition. This includes the 100-character line check. The lint ABI Lean subprocess inherited one thread and nice level 5. A preliminary lint was stopped in its static frozen guard before reaching its Lean ABI subprocess, then restarted with these environment/priority settings after the build finished.

5. Static hygiene: 170 total lines; zero lines over 100 Unicode characters; module header, copyright, public imports, module docstring and public section present. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option` token in the audited source. No resource override. `git diff --check`: exit 0. Final report/scratch checks are recorded below.

## Notes, errata, deviations and limits

- Blueprint P4 line 52 says `Put R_y:=max_{Y_0}|y|`. The implemented/design interface returns a positive enclosing bound, concretely max C 1. This is not the exact maximum (and an exact maximum is undefined when the image is empty). It is an intentional numeric enlargement already declared in `P45-LEAN-DESIGN.md:641` and design audits 1–3; downstream bounds consistently use the selected positive radius. Record this existing deviation, despite the prover handoff's blanket “none.” No new repair is required for P4-LI.
- The blueprint also describes containment in the open frequency image. This follows directly from `image_mono hVW` and the frozen image-openness clause; the exact audited design signature does not repeat these as output conjuncts. There is no lost proof obligation at that point.
- No new suspected defect in a pinned paper was found. These are classical infrastructure/“Ours” blueprint lemmas; this audit does not adjudicate the pre-existing CP10/CP11 errata allegations or certify later P4/P5 applications.
- Provider seals, downstream measure estimates, remaining source gaps, and campaign/root closure remain outside this package. No frozen declaration was edited or reinterpreted.

Only this report is the persistent audit edit. The handoff was already untracked at audit start. No state-changing git operation was performed.

Final validation: scratch probe deleted; report has balanced fenced blocks, no trailing whitespace, and a terminal newline. `git diff --check` exits 0; final status contains only the pre-existing untracked handoff and this untracked report.
