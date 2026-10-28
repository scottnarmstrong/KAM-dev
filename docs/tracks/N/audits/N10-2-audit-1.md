# Independent package audit: N10-2, round 1

Verdict: **PASS WITH NOTES** for N10-2. All eight scoped declarations preserve the approved design signatures and implement their assigned conversion obligations without an extra source premise. **N-HEAD-C is not seal-ready on the strength of this package:** no provider export is delivered here, and the Part 9 setting/maximum/stopped-theorem applications and remaining assembly are outside scope.

## Scope and authority

Audited `/root/code/KAM-inp-n102` at `cafc3440f912d28d15b1541ec14c2233b9faa83d`; comparison `inp` resolved to `6f750b07107c6e7b82c074f306331c93f50d0151`. Ran `git diff inp...HEAD`: Git warns of multiple merge bases and selects `fc9999550e1af9ee704bf1c7032361475a2bc0de`. Its two additions are `Assembly/Choice.lean` (inherited N10-1) and `Assembly/Hypotheses.lean` (N10-2). As expressly instructed by the handoff, only `KAM/Nekhoroshev/Assembly/Hypotheses.lean` is audited; Choice and existing analytic interfaces are inspected as dependencies, without recertifying their packages.

Read the package brief, AGENTS.md, PLAN, DECISIONS, N10-2 handoff and AUDIT FOCUS, N10 Lean design and its first audit, canonical `/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, Track N statement, blueprint-N Part 10, frozen N-HEAD-C and relevant frozen definitions. The user's explicit absolute destination overrides the generic brief's main-worktree destination. No repository source was edited.

## Declaration-by-declaration review

Names are in `KAM.Nekhoroshev`; line numbers refer to `KAM/Nekhoroshev/Assembly/Hypotheses.lean`. Mechanical comparison of each complete telescope and result, up to `:=`, against the canonical design file reports `SIGNATURE_IDENTICAL` for all eight declarations.

| Blueprint node | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| `stepN:p10:hc-tubes` | `hc_tubes` (35) | PASS | Existing max-norm complex tube inclusion, real bounds through `5R/8`, real-domain membership, nonempty central set, and half-ball initial membership. Uses `const_tubes` and the actual closed central set. |
| `stepN:p10:hc-h` | `hc_h` (57) | PASS | Restricts frozen holomorphy/reality to the tube; converts the complex Hessian to the Euclidean matrix-action estimate `n*Mc <= B`. No second ambient norm instance. |
| `stepN:p10:hc-qc` | `hc_qc` (80) | PASS | Applies the established cone conversion on the real action ball to obtain exactly `ell`, `mu` and the real second derivative. No tilde/time scaling. |
| `stepN:p10:hc-f` | `hc_f` (93) | PASS | Restricts frozen holomorphy, integer periodicity and reality; existing weighted estimate includes summability and bound `epsPrime epsilon` at geometric width `s/2`. Positivity and cutoff are correctly unnecessary here. |
| `stepN:p10:hc-exc` | `hc_exc` (114) | PASS | Derives strict exclusion from `mu*r0 <= 4*wmin` and positive `wmin`; obtains the Euclidean lower frequency bound in the valid direction from the frozen max-norm bound. |
| `stepN:p10:hc-time` | `hc_time` (131) | PASS | On the Euclidean closed ball of radius `R0`, the max-norm triangle inequality and size bounds place actions in the frozen derivative domain; `partials` yields `sqrt(n)*M`. This is a pointwise estimate, not an assumed maximum bound. |
| `stepN:p10:hc-field` | `head_field_locality` (149) | PASS | Equality of Hamiltonian values on the open real tube gives eventual equality and equality of total fderivs, hence equality of the actual frozen vector fields. The value-equality premise is the intended local extension premise, not a dynamical conclusion. |
| `bpN:p10:hypotheses-check` (analytic component) | `hypotheses_check` (164) | PASS WITH NOTES | Constructs existing ODE `Data`, analytic/QC/class/reality/weighted clauses and positive smallness from the original inputs and `cp_dict`. The design explicitly distributes the full blueprint proposition among helpers and later setting construction; this conjunction does not claim the whole setting or Omega0 specification. |

All constants are existing functions of the seven fixed data. `HeadHyp` is precisely the frozen H1-H5 conjunction; `IsAnalyticPerturbation` supplies H6 and the two explicit epsilon premises supply H7. No confinement, normal form, stability, maximum property, typeclass instance encoding a hard step, or conclusion-shaped hypothesis was introduced. `head_field_locality` is stronger than the fully analytic blueprint situation: eventual equality makes differentiability and parameter positivity unnecessary.

## Definitions, imports and frozen interface

There are **no new definitions, abbreviations, structures or instances** in the scoped module. Existing carriers were checked: `centralSet` is the complex image of the closed real max ball, `polyNbhd` uses a strict max-norm distance witness, `Dom` is the angle-strip/action-tube product, `InClass` is holomorphy and period-one membership, and `RealOn` quantifies actual real points. `WBound` includes `WSummable` as well as the sum bound, so no divergent-tsum fallback is exploited. `Data` bundles only positivity and original analytic predicates. Locality uses the original `realHamiltonian` and `hamiltonianVectorField`, with angles first.

Recursive source-import inspection found 116 module names, 19 frozen definition modules, **no frozen theorem modules and no provider modules**. Thus there is no imported DRAFT_SORRY theorem or provider, directly or transitively. Provider/frozen `type_of%` identity and seal-body probes are **not applicable**: this package defines no provider and proposes no seal. They remain mandatory for the eventual provider package; no identity check for N-HEAD-C is claimed here.

## Independent validation

All Lean/lake/checker invocations were sequential, with `LEAN_NUM_THREADS=1` and priority `nice -n 5`; the build used the mandated compile gate. No resource-budget override was used.

1. Targeted build:

   ```sh
   env LEAN_NUM_THREADS=1 LAKE_JOBS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n102 KAM.Nekhoroshev.Assembly.Hypotheses
   ```

   Exit 0. Output: `[inp-gate] slot 1 acquired 06:20:23 for KAM.Nekhoroshev.Assembly.Hypotheses`; `Build completed successfully (3194 jobs).` Four replayed unused-variable warnings are confined to existing `Interfaces/Period.lean`, at 351:71, 351:84, 367:73 and 368:5. No warning from the audited module.

2. Axioms, with a temporary probe importing only the scoped module and issuing `#print axioms` for each theorem:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/n102-audit.lean
   ```

   Exit 0. Exact output:

   ```text
'KAM.Nekhoroshev.hc_tubes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hc_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hc_qc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hc_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hc_exc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hc_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.head_field_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hypotheses_check' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation for the sole scoped implementation module (no provider is delivered):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.Hypotheses
   ```

   Exit 0. Complete output:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Hypotheses
   ```

4. Source lint (run after the checker completed; its ABI Lean subprocess inherits the thread limit and niceness):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1, solely the brief-permitted generated-root mismatch. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (418 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The orchestrator must regenerate the root on landing. No line-length, forbidden-pattern, module-system, frozen-anchor or ABI failure was reported.

5. Mechanical hygiene: 189 lines; no line over 100 Unicode characters; no forbidden escape, resource override, `EuclideanSpace`, new instance or new definition. Copyright, `module`, public imports, module docstring and public section are present. `git diff --check inp...HEAD` and `git diff --check` exit 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has no patch output (only the multiple-merge-base warning noted above). Final status contains only the auditor's new report and the pre-existing untracked handoff. No state-changing git command was run.

## Notes, uncertainties, errata and deviations

The design's explicit Part 9 reconciliation gate remains: constructing the actual setting, attaching `hc_time` to the delivered maximum specification and proving the time prefactor/field-value application are later assembly obligations. N10-2 does not supply or assume those results. The prior design audit expressly accepts this multi-lemma realization of the blueprint proposition. This is a boundary on the package's completion claim, not a missing premise in any delivered helper.

No new suspected frozen, blueprint or pinned-source mathematical defect was found. No new source deviation was introduced. This audit checks the conversion code against the blueprint and frozen authority; it does not independently recertify the Pos93 PDF or inherited source errata. No frozen or generated file, manifest, blueprint or source was changed. Temporary auditor artifacts under `.lake/abi-scratch/` are removed after verification. The pre-existing untracked handoff is preserved.
