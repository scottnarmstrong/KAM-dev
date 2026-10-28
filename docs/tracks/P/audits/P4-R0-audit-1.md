# Independent package audit 1: P4-R0

Overall scoped verdict: **PASS WITH NOTES** for `KAM/Planetary/PGMeasure/ResonanceSlow.lean`.
The signed `beta_inverse` contract and the internal slow-resonance branch are correct.
No frozen anchor is proved or sealed by this infrastructure package; provider/frozen-type
and seal-body checks are **not applicable**. The P4-M interface is usable, but the actual
P4-M assembly is not present in this checkout and is not certified here.

Audited HEAD: `f7f01890051e42a8b2041e5a32535b3f63a3b538`.
Comparison ref `inp`: `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9`.
File SHA256: `808136e4a57d5ebbd9cbfa2f14e3efd85f39f3a0aa04d55ba28e5d99bda98601`.

## Scope, authority and comparison notes

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local P4-R0 handoff
(including AUDIT FOCUS), track P statement, frozen P-G anchor and relevant definitions,
blueprint-P Part 4, P45-LEAN-DESIGN (ownership rows, proof plan and signatures), and
DESIGN-P45-design-audit-1/2/3. The original shared signature was read from
`/root/code/KAM-inp/.drafts/design/P45Signatures.lean`; that untracked file is not
present in this package checkout. The three design audits are under
`docs/tracks/P/design/`. Current inputs take precedence over earlier audit summaries.
The user's exact output-path instruction overrides the generic brief's main-worktree destination.

The requested `git diff inp...HEAD` was inspected. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 4c7c4ac655554b0ef294d5920d07649c1405d59c
```

There are four merge bases, and the selected comparison contains 60 changed files,
including previously merged infrastructure. The P4-R0-specific range
`git diff 2a2f395..HEAD --stat` contains only this 464-line file (two P4-R0 commits).
The other Lean packages were read only where needed as interfaces and are not re-audited.

**Literal global protected-diff check: FAIL, inherited comparison note.**
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is not empty:
`KAM.lean` has 26 added import lines. The frozen, manifest and README portions are empty.
`git diff --exit-code 2a2f395..HEAD -- KAM/Frozen manifest KAM.lean README.md`
is empty and exits 0. Thus the scoped P4-R0 commits do not change protected paths;
this report does not claim the broad branch passes the brief's literal empty-diff gate.
No generated file was repaired or regenerated during the audit.

## Declaration-by-declaration assessment

All names below are in `KAM.Planetary`; line numbers refer to ResonanceSlow.lean.
There are 20 public theorems and one public definition.

| Blueprint node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| beta-inverse, Leibniz bound | `abs_det_le_factorial_mul_pow` (34) | PASS | Sums absolute permutation products; coefficient is exactly cardinality factorial. Works for arbitrary finite index type, including the empty type. |
| beta-inverse, minors | `abs_adjugate_le` (51) | PASS | Cofactor sign has absolute value one; minor bound is exactly m! M^m, including m=0. |
| bpP:p4:beta-inverse | `beta_inverse` (60) | PASS | Literal design/shared signature identity; adjugate of the transpose gives the required max-norm estimate with b! M^(b-1)/B. No symmetry premise; strictly stronger than the symmetric blueprint statement, as approved by the design. |
| dm-slow, coordinate carrier | `appendEquivAB` (97) | PASS | Full measurable equivalence between the two coordinate blocks and Fin (a+b) coordinates. |
| dm-slow, coordinates | `appendEquivAB_apply` (101) | PASS | Identifies the equivalence with Fin.append on every input. |
| dm-slow / ext-tonelli | `measurePreserving_appendEquivAB` (114) | PASS | Canonical coordinate permutation and product splitting preserve the actual Lebesgue measures. |
| dm-slow / ext-tonelli | `volume_eq_volume_append_preimage` (120) | PASS | Outer-measure identity for arbitrary sets, without an unnecessary measurability premise. |
| bpP:p4:ext-tonelli, block version | `volume_prod_le_of_sections` (129) | PASS | Integrates the measurable set's section volumes, zero outside measurable P; arbitrary ENNReal section bound. Correct block analogue of the one-coordinate external fact. |
| dm-slow, coordinates | `blockFast_append` (152) | PASS | Exact first-block projection for real coordinates. |
| dm-slow, coordinates | `blockSlow_append` (155) | PASS | Exact second-block projection for real coordinates. |
| stepP:p4:dm-slow, frequency | `sum_append_zero_mul_freq` (158) | PASS | Zero fast modes cancel the fast gradient; the remaining frequency is exactly mu times the slow dot product. |
| dm-slow, lattice norm | `sum_abs_append_zero` (170) | PASS | Full integer l1 norm equals the slow block l1 norm, with casts preserved. |
| dm-slow, affine normal | `dot_slowFrequency` (175) | PASS | Correct normal beta-transpose times ks and offset ks dot Omega; no symmetry assumption. |
| dm-slow, Borelness | `slowFrequency_continuousOn_core` (189) | PASS | Continuity follows from N1's slow Lipschitz clause on the core at every permitted fixed slow action. |
| dm-slow, affine identity | `slowFrequency_expand` (199) | PASS | Exact affine expansion at 0 and l0 times coordinate unit vectors, for all I and xi; only l0>0 is needed. |
| dm-slow, Borelness | `slow_dot_continuousOn` (224) | PASS | Reconstructs all-xi joint continuity from N1 at 0 and lambda0 basis vectors and the exact affine expansion; no hidden coefficient-regularity premise. |
| dm-slow, Borelness | `measurableSet_slow_mode` (256) | PASS | Relative continuity on the closed core times univ plus measurable Q gives a measurable resonance set. |
| stepP:p4:dm-slow, sections | `slow_section_measure_le` (278) | PASS | Applies real-normal affine_slab, bounds l1(ks) by b times its max norm, and uses N3 to obtain normal norm >= l1(ks)/(b LB). Q need not be measurable for this outer-measure bound. |
| stepP:p4:dm-slow, Tonelli | `slow_mode_measure_le` (323) | PASS | With eps=(alpha/mu)/l1(ks)^tau, the section bound integrates to 2(alpha/mu)(b LB)(2lambda)^(b-1) times latticeWeight(tau+1) times volume core. |
| dm-slow, exhaustive modes | `eq_append_zero_of_blockFast_eq_zero` (379) | PASS | Every fast-zero integer vector is exactly append 0 (blockSlow k); used to transfer nonzeroness to the slow block. |
| stepP:p4:dm-slow / lt-a | `slow_resonance_measure_le` (391) | PASS | Countable union over all nonzero slow modes, lattice_tail at (b,tau+1), and exact final normalization to b LB S2 (alpha2/mu)/lambda times volume core times (2lambda)^b. |

No new helper restates or substitutes for a signed declaration. They are internal package
helpers in the design sense, exported publicly for later modules, with distinct names.
The file docstring identifies the common dm-slow node, and the final union theorem repeats
its exact node citation. No new source hypothesis, structure field or typeclass instance
assumes a missing proof step.

## Definition classification and proof audit

The only new definition is `appendEquivAB`. Its body composes the inverse of the sum-Pi /
product-Pi equivalence with the finite-index relabelling `finSumFinEquiv`. It denotes the
intended concatenation on the entire carrier for every a,b, including zero-dimensional
blocks. There is no conditional branch, junk value, chosen extension or fallback.
Its public application theorem exposes all behavior needed downstream; no consumer needs
to unfold an unexposed body. No new abbrev or structure is introduced.

The determinant proof uses only Leibniz, cofactor minors, adjugate multiplication and
coordinate sums. Positivity of B justifies division; hb covers b=1 and removes the
zero-dimensional inverse ambiguity. The slow proof preserves the max norm for real
vectors and the integer l1 norm in all thresholds. Strict resonance inequalities are
unchanged. The section enclosure passes from the open shell to the closed cube by
inclusion, which is a valid strengthening of the domain bound.

In the measurability proof, N1 is evaluated only at xi=0 and xi=lambda0 e_j, both within
its closed radius bound. Affinity then supplies joint continuity for arbitrary xi; no
regularity outside the core is assumed. Tonelli is applied to a measurable product-space
superset with compact measurable fast core. The source resonance sets themselves can
be handled by outer-measure monotonicity. Countable subadditivity does not require any
extra measurability premise on the union.

The final lattice step derives b<tau+1 from d.htau, uses only the full-sum clause of
lattice_tail, and sums over the nonzero slow block subtype. There is no missing factor
of two, b, mu, lambda, or 2pi. The arithmetic identity

```text
2*(alpha2/mu)*(b*LB)*(2*lambda)^(b-1)*S2
  = (2*lambda)^b * (b*LB*S2*(alpha2/mu)/lambda)
```

uses precisely b>0 and lambda>0. The signed P4-M measure_c2 is b*LB*latticeS b (tau+1).
It depends only on the fixed MeasureData and dimensions, never on lambda, mu, Q or alpha2.

## Consumer applicability and limitations

A fresh scratch probe elaborated the exact beta_inverse signature extracted from the
shared signature file under a new name, with body
`by exact beta_inverse hb hB hM hdet hentries`, and then checked
`example : type_of% @audit_beta_inverse_signature := @beta_inverse`.
The signature is also byte-for-byte identical to the design text before its proof body.
This verifies binder order, all premises and the exact conclusion without importing the
sorry-containing design fixture.

Two further scratch examples elaborated: (1) the slow bound with P4-M's measure_c2 formula
written explicitly, using a direct application of slow_resonance_measure_le; (2) the full
resonanceBad inclusion in the union of the fast-zero alpha2 set and fast-nonzero alpha1
set, by a case split on blockFast k=0. Thus the slow component is attachable to the
literal resonanceBad predicate without changing a threshold or carrier. This is an
interface receipt, not a build of a nonexistent TwoScale module or a proof of its fast cases.

`hl0 : lambda <= d.lambda0` is retained in the two outer helpers but unused. It is already
an explicit premise of the signed consumer, not an added requirement. N3 is an allowed
S4 standing premise, whose production from frozen data belongs to later packages;
this module's beta_inverse establishes the intended independent matrix estimate.
No source gap is silently closed by assuming N3 here.

## Independent checks

All Lean/Lake invocations were sequential, with LEAN_NUM_THREADS=1 and nice -n 5.
Only one targeted module build was requested; no clean, update, cache retrieval,
root regeneration, frozen/manifest edit or state-changing git operation occurred.
Scratch files were confined to this worktree's `.lake/abi-scratch/`.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4r0 KAM.Planetary.PGMeasure.ResonanceSlow
   [inp-gate] slot 2 acquired 09:08:13 for KAM.Planetary.PGMeasure.ResonanceSlow
   Build completed successfully (9067 jobs).
   exit 0
   ```

   The gate itself executes nice -n 5 lake build. No warning was returned.

2. Exact signature, consumer examples and all public theorem axioms:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4R0Audit1.lean
   exit 0
   ```

   All examples elaborated without warnings. Exact axiom output follows:

   ```text
   'KAM.Planetary.abs_det_le_factorial_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.abs_adjugate_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.beta_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.appendEquivAB_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measurePreserving_appendEquivAB' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_eq_volume_append_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.volume_prod_le_of_sections' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.blockFast_append' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.blockSlow_append' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sum_append_zero_mul_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sum_abs_append_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.dot_slowFrequency' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slowFrequency_continuousOn_core' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slowFrequency_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slow_dot_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.measurableSet_slow_mode' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slow_section_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slow_mode_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.eq_append_zero_of_blockFast_eq_zero' depends on axioms: [propext, Quot.sound]
   'KAM.Planetary.slow_resonance_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Independent kernel replay (one invocation; this package has one lemma module and no provider):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.ResonanceSlow
   replaying KAM.Planetary.PGMeasure.ResonanceSlow
   exit 0
   ```

4. Import quarantine and frozen states: a recursive scan of the 21 local KAM modules in
   the import closure finds no provider and no frozen theorem module. All 14 imported
   frozen definition modules have manifest state SEALED: HamiltonianVectorField,
   IsDiophantine, SymplecticForm, Assemble, Cylinder, Fast, FastFrequency, FastShift,
   HasFastDiffeomorphism, HasSecularBirkhoffForm, OscillatorAction, Phase, SecularAverage,
   Slow. No DRAFT_SORRY anchor is imported. The separate P-G target anchor was read as
   context only, not imported by the probe or audited module.

5. Static checks of the scoped module:

   ```text
   beta_inverse literal signature identity: True
   Lean module header: True
   new def/abbrev/structure: ['appendEquivAB']
   forbidden tokens/overrides: []
   lines over 100: []
   line count: 464
   ```

   Copyright, module, public imports, module docstring and public section are present.
   There are no global instances, forbidden escapes, heartbeat/recursion/synthesis
   overrides, EuclideanSpace uses or over-cap files in the scoped change.
   `git diff --check inp...HEAD -- KAM/Planetary/PGMeasure/ResonanceSlow.lean` exits 0
   (only the already quoted multiple-merge-base warning).

6. Full repository source lint, run after kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (496 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   This is **PASS under the brief's explicit stale-root exception**, not a literal
   zero-exit receipt. There was no other diagnostic, including no 100-character-line
   violation anywhere in the checked source tree. The ABI subprocess ran sequentially
   within this nice-prioritized lint invocation with LEAN_NUM_THREADS=1.

7. Final artifact checks: `git diff --check` exits 0. The untracked report was checked
   separately for trailing whitespace (none), balanced code fences (true), and terminal
   newline (present). The manually created P4R0Audit1.lean probe was deleted. Final
   status contains only the new audit report and the pre-existing untracked handoff;
   there are no tracked modifications. The scoped Lean file's SHA256 is unchanged.

## Errata, deviations and remaining work

No new suspected pinned-source or blueprint defect was found in the audited mathematics.
The dm-slow estimates agree with blueprint-P/parts/p4-pg-measure.tex:118-119; the
matrix estimate agrees with :62-67 and the design signature. Dropping symmetry in
beta_inverse is the declared, mathematically valid strengthening at
P45-LEAN-DESIGN.md:439. The internal-helper split is authorized by the handoff's
orchestrator ruling and does not weaken or rename a signed result.

The handoff's "463 lines" is an immaterial count discrepancy: the current file has
464 lines including its terminal blank line. It has zero lines over 100 characters.
The retained unused hl0 premise, broad comparison's protected-root delta, and stale
root lint exception are the notes supporting the scoped PASS WITH NOTES verdict.
No source theorem or frozen statement was repaired during this audit. Inherited
CP10/CP11 source allegations in the blueprint were not re-adjudicated against PDFs;
no new paper erratum is asserted here.

P4-M must still implement the fast resonance cases, identify the exact two-scale
predicate, and add their bounds to the now-proved slow component. This audit does not
certify those future obligations, a complete P-G provider, any frozen seal, or campaign
root closure. The literal broad-branch protected-diff gate remains nonempty as recorded
above and must be accounted for by the orchestrator during integration.

Persistent audit output: only
`/root/code/KAM-inp-p4r0/docs/tracks/P/audits/P4-R0-audit-1.md`.
