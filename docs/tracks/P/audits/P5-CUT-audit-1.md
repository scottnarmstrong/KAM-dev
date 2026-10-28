# P5-CUT independent package audit 1

Overall verdict: **PASS WITH NOTES** for P5-CUT, specifically the abstract finite-measure continuity helper. No mathematical or proof-hygiene blocker found. This is not a seal receipt for P-G or a proof of strictness.

## Scope and authority

Audited only `KAM/Planetary/PGAssembly/CutMeasure.lean`, at HEAD `7b103ba35b990fa26c8b2a25963a806922f12c2b`, using `git diff inp...HEAD` (observed inp `1f9fe4d119e56bd960a52ae5ab677f2522f4a352`). The diff adds this one 107-line file. Its SHA256 is `395756621279e1b3d7f293f527dbc5e1249f2a1188b83f88f88d655f63dd0ff2`.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, P5-CUT-handoff.md, the P45 design (including Revision 4), design audits 1–4 (under `docs/tracks/P/design/`, rather than the handoff's `audits/` locator), shared signatures, blueprint Part 5 strictness, the track statement and the relevant P-G frozen theorem/torus predicates. The user's exact absolute report destination overrides the generic brief's MAIN-worktree output instruction.

The controlling signature is `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:834–836`, SHA256 `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`. Its telescope and conclusion are present verbatim in both the design appendix (lines 1531–1533) and implementation (lines 97–99). No draft signature module was imported for validation.

## Declaration and node review

In the table, `CM` abbreviates `KAM.Planetary.PGAssembly.CutMeasure`. Every new public declaration is listed.

| Node / role | Lean declaration and source line | Verdict | Reason |
|---|---|---|---|
| `stepP:p5:st-ivt`, measurable sublevel sets | `CM.cut_measurableSet`, 30 | PASS | Coordinate evaluation is measurable; closed real sublevels are measurable. No finite-measure or null-slice premise needed. |
| `stepP:p5:st-ivt`, right continuity | `CM.cut_tendsto_right`, 33 | PASS | Increasing sublevel family with right intersection exactly the cut at a. Finite measure supplies the non-infinite upper cut required by `tendsto_measure_biInter_gt`. Null slices are correctly unnecessary. |
| `stepP:p5:st-ivt`, left continuity | `CM.cut_tendsto_left`, 47 | PASS | Increasing cuts at `a - 1/(n+1)` cover the strict cut; the missing equality slice is null. Continuity from below and monotonicity give the full left limit. Same finite/null-slice standing data as the designed helper. |
| P5-CUT / `stepP:p5:st-ivt` helper (handoff calls this `bpP:p5:st-ivt`) | global `finite_measure_coordinate_cut`, 97 | PASS WITH NOTES | Exact designed elaborated type, including implicit N, j, arbitrary finite measure, null coordinate slices and real-valued continuous cumulative mass. Export is global rather than in the shared signature's enclosing `KAM.Planetary` namespace; consumers must use the actual name. |

No frozen anchor is proved by this package. Provider/frozen equality and a frozen seal-body probe are therefore not applicable. The relevant eventual anchor, `KAM.Planetary.properlyDegenerateKAM`, remains `DRAFT_SORRY` in the manifest and is unchanged. Nothing here proves P-G, constructs its parameter measure or deletes a family of tori.

## Independent refutation checks

The abstract measure hypothesis is intentional, not a substituted source law. P45 design lines 306–312 assign construction of a finite Borel measure on original action parameters and proof of coordinate-slice nullity to the downstream strictness argument. P5-CUT accepts precisely those source data. It does not assume continuity, a torus family, or the desired cut as a premise.

At lines 35–43, all hypotheses of the finite-measure right-limit theorem are supplied: measurable cuts, inclusion in the correct direction, a finite witness at `a+1`, and the real-order intersection identity. At lines 53–82, the sequential family is monotone; the proof establishes both measure inequalities using coverage by the union plus the equality slice. Mathlib's `tendsto_measure_iUnion_atTop` explicitly permits nonmeasurable increasing sets, so no measurable-set premise is silently omitted there. The subsequent order-neighbourhood argument only needs each approximating point to lie strictly below a and monotonicity; it does not incorrectly infer a full limit from a sequence alone.

At lines 102–107, right continuity is extended from the open right ray to the closed right ray, combined with the left ray through `nhdsLT_sup_nhdsGE`, and composed with `ENNReal.continuousAt_toReal`. Finiteness is checked at each cut, preventing any reliance on `toReal ∞ = 0`. Zero measures are allowed; N=0 has no j, consistently with the typed coordinate input. No positivity, compact support, absolute continuity or extra dimension premise has been added.

The P5-CUT row mentions `intermediate_value_Icc`, but its exact promised export is continuity only. The blueprint at `blueprint-P/parts/p5-pg-assembly.tex:311` additionally uses tail limits and intermediate value to choose a cut. Those steps belong to P5-ST and are not paid by this file. Their absence here does not weaken the exact P5-CUT signature.

## Definition classification and imports

There are **no new public def, abbrev, structure, instance or notation declarations**. The proof-local `F` at line 50 is exactly the ENNReal cut mass on its whole real carrier; it has no fallback or junk branch. The real-valued map in the conclusion is the designed `toReal` conversion, guarded by finite measure throughout the proof.

The sole production import is `public import Mathlib`. There is no KAM provider or frozen theorem import, hence no imported `DRAFT_SORRY` anchor to quarantine and no assumption hidden in a bundled record. All ambient vectors are `Fin N → ℝ`.

## Independent validation

All Lean/Lake commands below were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper applies nice internally). No build clean/update/cache command or heartbeat override was used.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5cut KAM.Planetary.PGAssembly.CutMeasure
   [inp-gate] slot 1 acquired 13:17:43 for KAM.Planetary.PGAssembly.CutMeasure
   Build completed successfully (9047 jobs).
   ```

   Exit **0**, no warnings/errors. This is the targeted module gate, not a library-from-scratch build.

2. Fresh signature/application and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5CutAudit1.lean
   ```

   Exit **0**, no warnings/errors. The probe copied only the exact shared signature telescope into a fresh declaration, replacing its draft body with:

   ```lean
   theorem audit_signature {N : ℕ} (j : Fin N) (nu : Measure (Fin N → ℝ))
       [IsFiniteMeasure nu] (hnull : ∀ s : ℝ, nu {x | x j=s} = 0) :
       Continuous (fun s : ℝ => (nu {x | x j ≤ s}).toReal) := by
     exact finite_measure_coordinate_cut j nu hnull
   example : type_of% @audit_signature := @finite_measure_coordinate_cut
   example : type_of% @finite_measure_coordinate_cut := @audit_signature
   ```

   It also printed all four public declarations' axioms. Exact output:

   ```text
   'KAM.Planetary.PGAssembly.CutMeasure.cut_measurableSet' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.PGAssembly.CutMeasure.cut_tendsto_right' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.PGAssembly.CutMeasure.cut_tendsto_left' depends on axioms: [propext, Classical.choice, Quot.sound]
   'finite_measure_coordinate_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   `#print finite_measure_coordinate_cut` confirms the global export, the full telescope, and the supplied finite-measure instance. The `open MeasureTheory in` prefix does not change the elaborated type.

3. Single-invocation kernel replay (all four declarations are in this one module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.CutMeasure
   replaying KAM.Planetary.PGAssembly.CutMeasure
   ```

   Exit **0**.

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exact output, exit **1**:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (684 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The sole failing condition is the generated-root freshness check expressly excepted by the audit brief. The root was not regenerated. No other lint failure was emitted.

5. Source/diff checks: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produces no output, exit **0**. `git diff --check inp...HEAD` and final `git diff --check` produce no output, exit **0**. The report has balanced code fences, no trailing whitespace and a terminal newline. The audited file has 107 lines including comments, under the 1500-line cap; copyright, module declaration, public import, module docstring and public section are present. A scan of all its code finds no sorry/admit/axiom/unsafe/opaque, EuclideanSpace or resource-option override.

## Notes, source defects and closeout

- **N1, generated root:** Lint exits 1 solely for `KAM.lean is out of date`, the brief's express exception. Module checks, frozen-anchor guard and all 144 frozen ABI hashes pass; leave root regeneration to the orchestrator.
- **N2, export placement:** the shared signatures enclose the helper in `KAM.Planetary` (namespace begins at shared line 46), whereas implementation line 97 exports it globally after closing CM. This changes the API name, not its mathematical type or proof. No downstream implementation is audited here; a consumer spelling the fully qualified designed name must instead use the delivered global export. Record this naming deviation; no source premise or theorem conclusion changes.
- No new suspected defect in the scoped blueprint argument or pinned paper was found. Revision 4's previously recorded off-cylinder extension-agreement defect concerns P5-EX, not this helper; this audit does not reopen or discharge it.
- The handoff reports 106 lines; the actual committed file has 107. This bookkeeping discrepancy has no proof effect.

Only this report persists from the audit; the temporary probe is removed. The pre-existing untracked handoff is preserved. No production, frozen, manifest, generated file, shared signature or git state was changed. The outstanding strictness obligations remain construction and nullity of the original-action parameter measure, tail limits and an intermediate-value cut, and the whole-torus deletion/measure bookkeeping. There is no unresolved P5-CUT proof obligation.
