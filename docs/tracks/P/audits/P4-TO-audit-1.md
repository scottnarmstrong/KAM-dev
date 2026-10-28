# Independent package audit 1: P4-TO

Overall verdict: **PASS WITH NOTES** (the two package declarations pass; generated-root lint exception).

Audited commit `4ecc0c8d29e553511d8343424f401dd9ded72bb3`, compared using
`git diff inp...HEAD` with current `inp` at `ef8fc426c638557035e6101216aad4ef8b8a570e`.
The entire committed diff adds only `KAM/Planetary/PGMeasure/Tonelli.lean` (70 lines).
This is an infrastructure package, with **no frozen anchor or provider export**; frozen-type equality and
provider seal-body checks are consequently not applicable. This verdict approves these helper proofs,
not P-G sealing, downstream coordinate adapters, or campaign/root closure.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local
`docs/tracks/P/audits/P4-TO-handoff.md`. Applied its AUDIT FOCUS to **only** the Tonelli module.
Read the P4-TO row and signatures in `docs/tracks/P/design/P45-LEAN-DESIGN.md`
(lines 481, 1535–1546), the three design audits under `docs/tracks/P/design/`,
`/root/code/KAM-inp/.drafts/design/P45Signatures.lean` (839–848),
`blueprint-P/parts/p4-pg-measure.tex` (conventions and line 11), and the track-P statement conventions.
The explicit user instruction places this report in this package worktree, overriding the generic
brief's main-worktree destination. No source PDF claim is needed for these Mathlib measure lemmas.

## Declaration review

| Node | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| `bpP:p4:ext-tonelli`, diameter helper | `KAM.Planetary.section_measure_le_of_pairwise_dist` (26–46) | PASS | Exact design signature, including binder order and nonnegative real delta. Arbitrary real sets, without measurability or nonemptiness assumptions; outer-measure conclusion retained. Supplies the helper requested in design audit 1, N2, and approved in audits 2–3. |
| `bpP:p4:ext-tonelli`, product formulation | `KAM.Planetary.ext_tonelli` (48–68) | PASS | Exact design signature on `(Fin m → ℝ) × ℝ`, same measurable sets, containment, section bound, and ENNReal product. No extra premise, dimension restriction, finiteness restriction, or changed constant. |

A script extracted each declaration's text before `:=` from the production file and signature fixture:

```text
section_measure_le_of_pairwise_dist: signature text identical = True
ext_tonelli: signature text identical = True
```

Fresh examples copied from the fixture elaborate when supplied the production exports with every
explicit premise in order: `hd hE`, respectively `hR hP hsub hd hsections`.
The signature fixture itself was not imported (it contains design-only sorry bodies).

**Diameter proof.** The empty case is separate. In the nonempty case a chosen member gives a lower
bound; the pairwise-distance inequality proves every member lies between `sInf E` and `sInf E + delta`.
Thus the conditional infimum API is used with its boundedness/nonemptiness obligations discharged.
Outer-measure monotonicity and the exact length of that interval yield the claim. No measurability
of E is needed. Empty sets, singleton sets, and delta zero are covered.

**Tonelli proof.** Mathlib's `Measure.volume_eq_prod` is the actual product volume identity
(`Mathlib/MeasureTheory/Measure/Prod.lean:182–184`). `Measure.prod_apply` (226–229) applies to
measurable R with the s-finite Lebesgue measure on the real factor. The preimage by `Prod.mk x` is
exactly the section in the hypothesis. Sections vanish outside P by containment; inside P their
measure is bounded by `ofReal delta`. Monotonicity of the nonnegative integral and
`lintegral_indicator hP` give precisely `ofReal delta * volume P`.
The proof stays in ENNReal, so infinite base volume and the zero-times-infinity convention cause no
unjustified real conversion. The zero-dimensional base is allowed. Measurable R is the intended
Borel specialization in this finite-dimensional real space.

The blueprint's arbitrary-coordinate wording is implemented by the expressly approved product-form
interface; coordinate permutation and subsequent bounds on `volume P` belong to consumers.
No coordinate-permutation theorem is claimed by this file. Both unused `hd` premises are retained
exactly as designed and referenced by `have _ := hd`; their mathematical redundancy is harmless.
There is no conclusion-shaped assumption: the section estimate is the explicit premise of Tonelli,
and the independent diameter theorem proves the separate short-section step.

## Definition classification and imports

There are **no new def, abbrev, structure, instance, or auxiliary public declarations**; the two
theorems above exhaust the public output. Hence no junk-value/fallback or bundled-hard-step issue.
Both direct public imports are Mathlib modules, exactly as listed in the handoff. No KAM frozen
anchor (DRAFT_SORRY or otherwise) or provider is imported, so no imported anchor state requires a
manifest exception.

## Independent validation

All Lean/Lake/checker invocations were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The targeted build used the prescribed gate, whose implementation invokes `nice -n 5 lake build`.
No clean, cache download, update, root generation, or protected-path edit was performed.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4to KAM.Planetary.PGMeasure.Tonelli
   ```

   Exit 0; output:

   ```text
   [inp-gate] slot 2 acquired 07:58:48 for KAM.Planetary.PGMeasure.Tonelli
   Build completed successfully (2596 jobs).
   ```

   This is the targeted Lake dependency check, not a whole-library build. No module warning appeared.

2. Fixture-signature examples and all public theorem axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4TOAudit1.lean
   ```

   Exit 0; exact output:

   ```text
   'KAM.Planetary.section_measure_le_of_pairwise_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.ext_tonelli' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Single kernel replay invocation (the sole lemma module; no provider exists):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.Tonelli
   ```

   Exit 0; exact output:

   ```text
   replaying KAM.Planetary.PGMeasure.Tonelli
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the explicitly permitted stale-root exception; exact combined output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (464 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, size, 100-character-line, or other lint failure was reported.

5. Static hygiene and scope: `git diff --check inp...HEAD` exited 0 with no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0 with no output.
   The module has 70 lines, maximum line length **97 Unicode characters**, a copyright header,
   `module`, two public imports, module docstring, and `public section`.
   No sorry/admit/axiom/unsafe/opaque, resource overrides, EuclideanSpace, or quarantined imports occur.

## Findings, uncertainties, errata, and deviations

No mathematical, signature, hypothesis, carrier, constant, or source/blueprint defect found within
this package. No new suspected pinned-source erratum or implementation deviation.
The only expected repository check exception is the stale generated `KAM.lean`, which the brief
explicitly allows and the orchestrator must regenerate. No generated file was changed for this audit.
The product-coordinate interface limitation is explicit in the approved design, not an unpaid claim
inside either theorem. No downstream application or frozen anchor closure was audited.

Only this report was written outside `.lake/abi-scratch/`; the local handoff was already untracked
before the audit. The temporary probe is removed before handoff. No state-changing git command used.
