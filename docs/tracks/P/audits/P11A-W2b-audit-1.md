# P11A-W2b independent audit 1

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11aw2b`.
Audited HEAD: `bea460ac74920f2f468a6d0a06ad6bdb863b63de`.
Comparison `inp` observed at `d9183adae208ecf2e726620694b69c8168e33006`.
Scope: **only** `KAM/Planetary/WeakMeasure/FiniteType.lean` (108 lines).
The user's exact report destination overrides the generic brief's main-worktree destination.

## Verdict

**PASS WITH NOTES** for the scoped package. No mathematical repair or missing W2 adapter was found. `rank_compact` has exactly the delivered design signature. No frozen anchor is proved by W2b, so “seal-ready” is inapplicable. In particular P-FIXED remains `DRAFT_SORRY`; this audit does not certify Preparation or the campaign theorem.

Read authority: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the W2b handoff and its AUDIT FOCUS, `docs/tracks/P/design/P11A-LEAN-DESIGN.md` (including W2/P1, reconciliation table and patch signatures), design audits 1–3, the delivered `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, `P810-LEAN-DESIGN.md`, the relevant Part 10/11/11a blueprint statements, track-P statement, downstream P-FIXED and relevant frozen definitions. No repository code was edited.

## Declaration and node review

Names below are in `KAM.Planetary` unless qualified.

| Node / obligation | Declaration and line | Verdict | Reason |
|---|---|---|---|
| Euclidean vocabulary bridge | `p11euclid_eq_length2`, 30 | PASS | Both sides are the same square-root sum of coordinate squares, on the original Pi carrier. All dimensions allowed. |
| Scalar diagonal derivative bridge | `p11dg_scalar_eq_scalarJet`, 35 | PASS | The scalar-to-`Fin 1 → ℝ` linear isometry commutes with iterated derivatives, preserving the absolute scalar length. For order zero the unit-sphere supremum is reduced to a singleton using `hn`; positive orders use identical defining sets. No regularity premise is added. |
| Finite jet maximum bridge | `p11maxJet_scalar_eq_jetMax`, 65 | PASS | Equality of the finite-order value sets, for every natural `mu`. Carries `hn` to the preceding bridge. |
| Amount bridge / `index-def` | `index_def_eq_betaFamily`, 75 | PASS | Equality of the actual infimum sets, matching the same coefficient sphere, patch and scalar power. Holds for arbitrary `rho`, `mu`, map and set, with `hn`; stronger than the analytic/nonempty usage required downstream. |
| `bpP:p11a:rank-compact` | `rank_compact`, 90 | PASS | Signature text before the proof is byte-identical to signature lines 93–98. `rho=1` uses `Nondegeneracy.cp09_unsquared`, `rho=2` uses `Nondegeneracy.cp09_lemma1`; no altered norm, amount, quantifier, constant dependence or extra premise. |
| `stepP:p11a:rc-reduce` | `rank_compact` proof, 96–106 | PASS | Connectedness follows from preconnectedness and the image of nonempty `K ⊆ V`. `hr` is definitionally `rnd_def`; the positive Part 10 order is already at least one. Each amount rewrite receives the theorem's `hn`. |
| Existing Part 10 finite type / CP09 Lemma 1 | imported `Nondegeneracy.finite_type`, `cp09_lemma1`, `cp09_unsquared` | PASS, reuse | Their owning module is publicly imported. No duplication or renamed substitute is needed. |
| Existing physical frequency nondegeneracy | `Nondegeneracy.rnd`, separate `Nondegeneracy.Frequency` module | PASS WITH NOTES | Available on this branch, but **not** imported by W2b. Preparation must import its owning module explicitly. This is an import edge, not a missing mathematical adapter. |

The signature's existential core is exactly delivered. The blueprint's least-positive-index reading is supplied by existing W0 `p11Index_spec`, `p11Index_le`, `p11Amount_pos` (Basic lines 270–281). Its monotonic amount consequence can use the amount equality and imported `betaFamily_mono`; it is not a different choice of gauge.

## Definition classification and applicability

There are **no new public `def`, `abbrev` or `structure` declarations**. The proof-local `e` is the genuine linear isometry between a scalar and its one-component constant function; it has no exceptional value. Existing `p11RNondegenerate V w` and `Nondegeneracy.rnd_def V w` are definitionally equal, independently checked by `rfl` for arbitrary maps and sets.

The amount bridge identifies defining sets even away from regularity/nonemptiness hypotheses; it does not derive positivity from a default infimum. Positivity in `rank_compact` is imported from Part 10's compact analytic theorem, on a nonempty compact patch and nonempty coefficient sphere. The `n ≥ 1` condition is necessary for the order-zero sphere presentation: when `n=0` the sphere is empty although the scalar value need not vanish. Every use in this file supplies `hn` (lines 72, 86/88, 101/105). Preparation has `n ≥ 2` through `P11Physical.n_ge`, hence can supply it; the frequency dimension `2n` is also positive.

## W2 completeness and Preparation boundary

The handoff's reuse deviation is justified. P11A design row W2 (line 704) and the reconciliation row “P10 not yet designed” (line 119) predate the delivered P810 ownership: S10-C owns finite type and CP09 Lemma 1, S10-R owns `rnd`/frequency/scaling (P810 lines 448–452). W2b imports S10-C and adds the exact P11-vocabulary amount adapter and `rank_compact`. The separate Frequency module supplies the physical-frequency theorem on the same `Fin n → ℝ` carriers. No finite-type, CP09, or R-nondegeneracy adapter is missing from this W2 slice.

This does **not** certify all P1 prerequisites. P11A design lines 1541–1563 require a literal secular-Hessian characteristic-root identity, the physical frequency formula, a suitable positive-measure compact patch, and period-one transport. The P810 `Nondegeneracy.Interface` owner is a separate upstream package; that module is absent in this checkout. The physical reconciliation and `norm_dict` remain P1/upstream obligations. `rank_compact` assumes only the source analytic/R-nondegeneracy data and does not hide those obligations in a new premise or structure. No attempt was made to prove or repair them within this audit.

## Comparison and hygiene notes

The requested `git diff inp...HEAD` warns “multiple merge bases, using c1db3418d42896eca8fcc5e95644725aa77c0a48”. Its whole-branch diff includes inherited AMD, PlanarTorsion, ContinuousSeries and audit files in addition to W2b. The protected-path check is **not literally empty**: `KAM.lean` contains four inherited added imports (AMD.Geometry, AMD.MovingODE, PlanarTorsion.Setting, WeakKAM.ContinuousSeries). No `KAM/Frozen`, `manifest` or README diff occurs in that comparison. `git show --stat HEAD` confirms the W2b commit changes only the 108-line scoped file; `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Thus the root-diff discrepancy is recorded, not silently waived as an empty branch diff, and is not attributable to the W2b change.

Static checks found five new public theorems, no forbidden proof escapes/resource overrides/`EuclideanSpace`, and unique project short declaration names. The module has its copyright, `module`, public imports, module docstring and public section. A recursive KAM import review found 71 modules, no provider import and only SEALED frozen-definition imports (47 distinct frozen modules); no DRAFT_SORRY theorem import. The provider/frozen seal probes are inapplicable because this is an infrastructure module, not a provider package.

## Independent check receipts

All Lean/Lake invocations for this audit were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, cache fetch, library-wide rebuild or generated-file edit was performed.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw2b KAM.Planetary.WeakMeasure.FiniteType
   [inp-gate] slot 1 acquired 16:57:00 for KAM.Planetary.WeakMeasure.FiniteType
   Build completed successfully (9117 jobs).
   exit 0
   ```

   Only replayed upstream unused-variable warnings in Kepler.Energy, Poincare.Chart and Kepler.Mass; no warning/error in the audited file.

2. Signature/adapter/axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW2bAudit1.lean
   exit 0
   ```

   Copied the exact design `rank_compact` declaration under a fresh name; its body was `by exact rank_compact hn hm hV hconn hK hne hsub hw hr hp`, with every explicit binder in order. Checked `example : type_of% @audit_rank_compact := @rank_compact`. Also checked definitional equality of R-nondegeneracy, equality `index_def 2 mu w K = Nondegeneracy.betaMu w K mu`, and availability/types of `finite_type`, `cp09_lemma1`, `cp09_unsquared`, `rnd`, `scaling` (Frequency explicitly imported in this probe).

   Exact axiom output:

   ```text
   'KAM.Planetary.p11euclid_eq_length2' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11dg_scalar_eq_scalarJet' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11maxJet_scalar_eq_jetMax' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.index_def_eq_betaFamily' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rank_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.FiniteType
   replaying KAM.Planetary.WeakMeasure.FiniteType
   exit 0
   ```

4. Root-name probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW2bNames.lean
   ROOT NAMES ABSENT (5); package exports are namespaced
   exit 0
   ```

   The Lean environment contains none of the five short names as a root declaration. Project-wide declaration search found each short name only in the scoped file.

5. Full source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (798 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is the generated-root exception expressly permitted by the audit brief. The root was not regenerated. The ABI comparison was slow under host load and completed successfully; no timeout or resource override was introduced.

6. `git diff --check`: exit 0, no output. Report/scratch-only edit discipline was maintained. Both audit Lean probes and their temporary kernel/lint logs were removed after the receipts were recorded; the lint script removed its own ABI scratch file.

## Uncertainties, defects and deviations

No suspected pinned-paper erratum or false blueprint mathematics was discovered in this scope. This audit did not independently re-prove or re-audit the existing Part 10 modules or the full Preparation chain.

Two documentation/scope discrepancies are explicit:

- P11A design line 119 says **“P10 not yet designed”**, and line 704 assigns **“Part10 `finite_type`, `cp09_lemma1`, `rnd` exact port”** to W2. These are stale relative to P810's separately delivered owners. Importing the existing theorems and proving their vocabulary bridges is the appropriate implementation. No replacement definition is warranted. The file imports finite type/CP09, while Frequency must be imported directly by its physical consumer.
- The whole-branch protected-path diff includes inherited `KAM.lean` changes, although the W2b commit itself changes none of the protected paths. This fails the brief's literal empty-whole-branch-diff expectation, but does not establish a W2b hygiene defect; the evidence and scope separation are retained above.

No proof deviation was introduced by the auditor. The report is the only new repository artifact created by this audit. Overall scoped verdict remains **PASS WITH NOTES**; no frozen seal or downstream physical attachment is asserted.
