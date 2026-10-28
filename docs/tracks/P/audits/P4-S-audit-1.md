# Independent package audit 1: P4-S

Overall verdict: **PASS WITH NOTES** for the scoped definition package. No frozen anchor or provider is implemented here; no anchor is certified seal-ready. The notes concern the inherited gradient interpretation and expected generated-root lint exception. No implementation defect was found in the scoped file.

## Scope and authority

Audited HEAD `53b3ef81856d48628d259e8aea8ce3c18d554138`; observed `inp` at `f11c90357967f666b1673409df890dbcec823dff` and `inp-p45s` at `597e0b09ec12eb4a91c7682b7ae62c379f7e4efe`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local P4-S handoff. The user's exact report destination overrides the generic brief's main-worktree destination. The handoff's AUDIT FOCUS limits implementation review to `KAM/Planetary/PGMeasure/Setting.lean`; inherited PG/Setting is checked only as an interface dependency, including reused joinedActions.

Read the P45 design (P4-S row, frequency/S4 contracts and dependency plan), the three design audits at `/root/code/KAM-inp/docs/tracks/P/design/DESIGN-P45-design-audit-{1,2,3}.md`, and the authoritative shared signatures at `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`. The shared signatures are absent locally. Also checked blueprint-P/parts/p4-pg-measure.tex:72–86 and 153–154, the track P statement and relevant P3b/P5 frequency consumers, the imported PG setting, and frozen FastFrequency/HasFastDiffeomorphism definitions. Earlier design approval is treated as interface evidence, not proof closure.

`git diff inp...HEAD` contains PG/Setting (98 lines) and PGMeasure/Setting (111 lines). Git warns of multiple merge bases and selects `ef8fc426c638557035e6101216aad4ef8b8a570e`; that warning is retained, not silently treated as a unique base. The required scoped `git diff inp-p45s...HEAD -- KAM/Planetary/PGMeasure/Setting.lean` adds precisely the reviewed file. Unrelated entries in the full comparison with inp-p45s are outside the explicit focus.

Reviewed file SHA256: `0001cad3c0a5f86438b4bb3f90eb61742948c5859aa8a415ffb45ecbb970166a`.
Shared signature SHA256: `f4c7752bf23b8b149e4e5c0f1fac5288b4c32c10d19c4a17d3afe79af1c13ca2`.

## Declaration disposition and definition classification

All names below are in KAM.Planetary. All five new explicit declarations and reused joinedActions are identical to their intended shared signatures after whitespace normalization. No premise, binder, constant, field, carrier or formula has been changed.

| Node / role | Declaration and implementation line | Verdict | Reason and classification |
|---|---|---|---|
| bpP:p4:freq, polynomial | secularPolynomial, 32 | PASS | Literal finite quadratic polynomial in the original total P0/Omega/beta; no extension, chosen witness, or fallback. Exact on its whole carrier, including zero dimensions. |
| bpP:p4:freq, slow block | slowFrequency, 38 | PASS WITH NOTES | Literal Omega + beta.mulVec xi for every matrix and vector. Its identification as a polynomial gradient requires symmetry; see B1. |
| bpP:p4:freq, actual map | freq, 43 | PASS WITH NOTES | Literal fast gradient of the polynomial plus frozen fastFrequency, appended to mu times the slow block. No period division, norm change, or substituted coefficients. Totalized fderiv is discussed below. |
| bpP:p4:data | MeasureData, 53 | PASS | Standing source-data structure, not a proof or chosen solution. Every field matches the design. N1–N3 are exactly the declared S4 estimates, not the downstream measure conclusion. |
| bpP:p4:freq, resonance helper | resonanceBad, 103 | PASS | Literal subset of D with a nonzero integer resonance, strict inequality, full l1 denominator and alpha2 exactly when the fast block vanishes. Exact formula for arbitrary real parameters. |
| bpP:p4:conv#shell, reused | joinedActions, PG/Setting:91 | PASS | Existing flattened product: fast projection in X and slow projection in Y. Same shared signature, no duplicate declaration. Its upstream proof package is not re-audited here. |

The four new function definitions were copied from the intended planetary signatures into a scratch namespace and independently checked by `rfl` against production definitions. MeasureData's entire field telescope/body was compared statically after whitespace normalization, including order and quantifier scopes. The shared fixture also contains KAM.NormalForm.freq: selecting that unrelated name in the first scratch extraction caused a type mismatch. The harness was corrected to the planetary declaration and the complete probe rerun successfully; this was not a product failure.

S4 details: compact core lies in bounded V, giving finite volume without an extra finite-volume field; hvol is the source's positive-volume premise. Ry is a positive enclosing bound, consistent with the design's declared enlargement rather than the exact maximum. The inverse witness is valid on W and Lipschitz on fastFrequency H0 '' closure V. Its values elsewhere are unconstrained typing data, never used here. All constants are stored before downstream coupling/shell choices. `small` is exactly the printed 1/(2(1+M)a LN Lg), M=2b LN LB. N1/N2 bound the actual fast perturbation mu G by mu LN times distance: on Ioc 0 mu1, cancellation of positive mu recovers the source G bounds. N3 uses beta transpose as printed. No measure theorem, torus family, measurability result or other conclusion is bundled as an input.

Mathlib's fderiv is zero at nondifferentiable points. Thus freq is the specified total expression on all inputs; no theorem here relies on that fallback to satisfy a claimed Hamiltonian identity. On the C1/analytic locus used by the blueprint and frozen P-G data it has the intended derivative interpretation. MeasureData alone does not export regularity or symmetry of arbitrary coefficient functions. Consumers requiring a Hamiltonian-gradient identity must obtain those facts from their actual source data. This package makes no unguarded gradient theorem.

The resonance set agrees algebraically with the intended failure of the two-scale lower-bound predicate: negating either non-strict lower bound gives the strict inequality; a nonzero fast block already implies a nonzero full k. Checked against KAM/Planetary/Hamiltonian/Diophantine.lean:30–36. The proved bridge resonanceBad_eq remains owned by P4-M. measure_c1/c2 and latticeS are also intentionally outside this package. No missing proof body is disguised as a definition.

## Independent checks

All Lean commands were serial with LEAN_NUM_THREADS=1 and nice -n 5. No clean, update, cache retrieval, library rebuild from scratch, resource override or state-changing git operation was issued.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4s KAM.Planetary.PGMeasure.Setting
   [inp-gate] slot 2 acquired 08:26:03 for KAM.Planetary.PGMeasure.Setting
   Build completed successfully (9062 jobs).
   exit 0
   ```

   The wrapper runs nice -n 5 lake build. The job count is Lake's successful dependency accounting, not an instruction to rebuild the library from scratch. No warnings were emitted.

2. Signature/axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4SAudit.lean
   exit 0
   ```

   Four copied-definition equalities elaborate by rfl. Exact axiom output from the successful run:

   ```text
   'KAM.Planetary.secularPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slowFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.freq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.MeasureData' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.resonanceBad' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.joinedActions' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.MeasureData.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   No new explicit theorem/provider export exists, so provider/frozen-type equality and proposed seal-body probes are inapplicable. No seal-readiness claim is made.

3. Kernel replay (one invocation):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.Setting
   replaying KAM.Planetary.PGMeasure.Setting
   exit 0
   ```

4. Static hygiene: 111 lines; maximum line length 99 Unicode characters. Copyright/authors, module, public imports, docstring and exposed public noncomputable section are present. No forbidden proof escape, resource override, EuclideanSpace, or new instance is present. An independent traversal of local KAM imports finds 16 modules total and no theorem-anchor/provider module. All frozen imports in that closure are definitions, so there is no imported DRAFT_SORRY theorem or provider dependency.

5. Full source lint, run after kernel replay (its ABI subprocess was serial too):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (468 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only reported failure is the generated-root staleness explicitly allowed by the audit brief. No other diagnostics were emitted. KAM.lean was not regenerated.

6. Protected paths:

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   [no diff; multiple-merge-base warning only]
   exit 0
   git diff --check inp...HEAD
   [no whitespace errors; same merge-base warning]
   exit 0
   ```

## Blueprint/source notes and limits

**B1 — inherited contextual symmetry guard, blueprint-P/parts/p4-pg-measure.tex:73–74.** The definition says `omega^s_mu := Omega + beta xi = gradient_xi N_mu`, followed by the full gradient identification. For an arbitrary matrix, the quadratic polynomial's slow gradient is Omega + (beta + beta transpose) xi / 2. For example, beta=[[0,1],[-1,0]], Omega=0 makes the quadratic polynomial identically zero while beta xi is generally nonzero. The equality therefore needs symmetric beta, as supplied by PGData.hsymm and the frozen P-G source hypotheses. MeasureData does not contain symmetry, and N3 (invertibility) does not imply it. Read the blueprint equality in that source context, or state its symmetry guard explicitly when proving the later identification. This is a blueprint wording/domain caveat, not a counterexample to frozen P-G or to the literal formula implemented here. No production premise was added to repair it.

No suspected new pinned-paper erratum is certified by this audit: no paper claim needed independent adjudication for this definition-only scope. The already declared positive enclosing Ry enlargement is retained; no new mathematical deviation is introduced. The mapping table's old placement of joinedActions in PGMeasure/Setting is superseded by actual reuse from PG/Setting, consistent with the handoff and acyclic imports. The mapping table mentions resonanceBad_eq there, while the dispatch table assigns it to P4-M; this package correctly follows the latter ownership.

This verdict establishes the faithful definition package and its validation only. It does not pay downstream analytic, resonance-measure, provider or frozen-root obligations.

## Final repository receipt

Only this report was persistently created by the auditor. The pre-existing untracked P4-S-handoff.md is preserved. The scratch P4SAudit.lean probe was deleted. `git diff --check` exits 0, the report has balanced code fences and a final newline with no trailing whitespace, and its required absolute destination is inside this worktree. Production/frozen/manifest/generated files were not edited. No heartbeat design signal occurred.
