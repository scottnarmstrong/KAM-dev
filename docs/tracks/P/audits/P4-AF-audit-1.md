# Independent package audit: P4-AF

Overall verdict: **PASS WITH NOTES** for P4-AF infrastructure. No mathematical or statement-fidelity failure found. This package proves no frozen anchor; provider/frozen ABI equality and seal-body checks are therefore not applicable. This verdict does not seal P-G or establish its remaining dependencies.

Audited HEAD `08e4801d004e3479052c67a75e37785413bbcb95` against `inp` at `f390de8f741ebb8dab2d17ff12ec7f7e5b6d4f46`, on 2026-10-28. Scope is exclusively `KAM/Planetary/PGMeasure/AffineSlab.lean`, as required by the handoff's AUDIT FOCUS. The requested `git diff inp...HEAD` reports multiple merge bases and selects `ef8fc426c638557035e6101216aad4ef8b8a570e`; its complete file inventory is AffineSlab (105 added lines) and inherited Tonelli (70 added lines). Tonelli is outside this audit's scope. The pre-existing untracked handoff was left untouched.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, local handoff, Track P statement conventions, blueprint Part 4 (especially lines 12–14 and 88–93), P45 design ownership/signature/proof-plan sections, and relevant entries in DESIGN-P45-design-audit-{1,2,3}.md (located under `docs/tracks/P/design/`). The shared signature is `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:447–450`; the relative scratch path does not exist in this package worktree. The production module and KAM.Measure.Slab implementation were read in full. The scoped theorem uses no frozen definition or theorem.

## Declaration-by-declaration verdicts

| Node / role | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpP:p4:affine-slab` | `KAM.Planetary.affine_slab` (83–103) | PASS | Signature text, through `:=`, exactly equals the shared design and local design Appendix A. Arbitrary real normal, arbitrary real offset, positive dimension/radius/threshold, max norm, Lebesgue volume, and exact constant `2*eps*(2*lambda)^(n-1)/‖ell‖` are preserved. No added premise, constant dependence, or weakened conclusion. |
| Coordinate-section helper for the same node | `KAM.Planetary.affine_slab_of_coord` (31–80) | PASS | Distinct helper takes only typing data and a nonzero chosen normal coordinate. Proves the explicit section bound on all real `c`, `lambda`, `eps`; dropping positivity here is a valid stronger auxiliary result, not a hidden assumption. |

The implicit `n` is generalized before the explicit design telescope. A scratch copy of that full design statement with body `exact affine_slab hn ell hell c lambda eps hl he` elaborated. A `type_of%` probe checked equality in the reverse direction as well. No provider or frozen-anchor probe is claimed.

## Proof and definitions

There are **no new def/abbrev/structure declarations**, no instances, and no fallback objects. Local proof abbreviations `S` (36–37) and `e` (38) are respectively the literal cube/slab set and Mathlib's coordinate-splitting measurable equivalence; their bodies represent the intended objects on their whole carriers. `KAM.Measure.cube` is the existing literal product of closed intervals, not a replacement norm ball.

The helper proves the slab set is Borel (41–50), transports volume by the measure-preserving inverse coordinate split (38–52), and uses `Measure.prod_apply_symm` to integrate one-dimensional section measures. Inside the remaining-coordinate cube, each section is contained in the affine interval with slope `ell i` and offset `∑ j, ell (i.succAbove j) * y j + c` (59–69), bounded using `KAM.Measure.volume_abs_affine_lt_le`. Outside that cube the section is empty (70–76). Integrating its indicator gives exactly the cube volume times the interval bound (77–80).

The main theorem reduces positive dimension to `m+1`, chooses a coordinate maximizing its absolute value, proves that value equals the Pi max norm and is nonzero (88–98), and performs the exact ENNReal product/power conversion (99–103). Nonnegativity needed for conversion follows from `hl`; no Euclidean norm or dimension factor is substituted. The helper's `n=0` case has a zero-dimensional remaining cube of volume 1, so the one-dimensional case is retained.

No hard proof step is assumed in an argument or bundled field. Direct imports are two Mathlib modules and `KAM.Measure.Slab`; the latter imports Mathlib only. There is no provider or DRAFT_SORRY frozen import, including through this project dependency.

## Notes and deviations

1. **Implementation route:** design package row P4-AF (482) lists P4-TO as a dependency; blueprint line 93 says “apply \ref{bpP:p4:ext-tonelli}”. The implementation instead proves the required Fubini slicing directly using Mathlib's `Measure.prod_apply_symm`, in the same style as KAM.Measure.Slab. It does use the prescribed scalar affine interval lemma. The Borel/section/projection obligations are explicitly discharged, so the alternate route is mathematically complete and needs no added premise. Record the bypass when updating package dependencies; this report does not edit the graph/design or assert any other consumer's bypass.
2. The handoff's claim that `hl` is unused is inaccurate: line 100's `by linarith` uses its positivity to justify `ENNReal.ofReal_pow`. `he` is not needed mathematically by this proof and is retained in the exact design telescope (`have _ := he`, line 87). This is an informational handoff correction.
3. The only permitted lint exception is the generated root being stale; it was not regenerated.

## Independent validation

All Lean/Lake operations below ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no clean/update/cache operation, resource override, production edit, or state-changing git command was issued.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4af KAM.Planetary.PGMeasure.AffineSlab
   [inp-gate] slot 2 acquired 08:20:45 for KAM.Planetary.PGMeasure.AffineSlab
   Build completed successfully (2599 jobs).
   exit 0
   ```

   This is the prescribed targeted gate receipt, not a claimed clean rebuild.

2. Exact-statement and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4AFAudit.lean
   'KAM.Planetary.affine_slab_of_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.affine_slab' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   Probe contained the design statement under a fresh name, its direct application body, `example : type_of% @audit_affine_slab := @affine_slab`, and both axiom commands. No warnings or errors. The scratch file was deleted after use.

3. Kernel replay (single invocation, the only scoped module):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.AffineSlab
   replaying KAM.Planetary.PGMeasure.AffineSlab
   exit 0
   ```

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (468 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   Exit 1 is solely the stale generated-root exception explicitly allowed by the audit brief. No other lint failure was printed. The lint ABI subprocess ran after the other Lean checks, inheriting the thread limit and niceness.

5. Static checks: exact signature text matches shared design **True**; scoped file **105 lines**, maximum line length **98 characters**, thus within both 1500-line and 100-character limits. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, or `EuclideanSpace` token in this file. Copyright/authors, `module`, public imports, module docstring, and `public section` are present; there are no new definition bodies needing exposure.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: no diff (only the multiple-merge-base warning above). `git diff inp...HEAD --check`: exit 0, same warning and no whitespace error. Final report whitespace/status checks are recorded below.

## Source defects, uncertainties, and handoff

No suspected defect in the scoped blueprint statement or a pinned paper was found. This is the blueprint's elementary “Ours” slicing argument; no external paper claim needed adjudication. The direct Fubini route and inaccurate unused-`hl` handoff sentence are the deviations/notes above. There is no remaining unpaid inequality in this scoped lemma, no heartbeat design signal, and no mathematical uncertainty identified. Other P4/P5 nodes and frozen anchors remain outside scope.

Persistent audit output: only `/root/code/KAM-inp-p4af/docs/tracks/P/audits/P4-AF-audit-1.md`. Production sources, original handoff, frozen files, manifest, generated root and README are unchanged. The explicit user destination overrides the generic brief's MAIN-worktree destination.

Final validation: report has balanced fenced blocks, a terminal newline, and no trailing whitespace; `git diff --check` exits 0. Final status contains only the pre-existing untracked handoff and the new audit report. The manually created probe is absent.
