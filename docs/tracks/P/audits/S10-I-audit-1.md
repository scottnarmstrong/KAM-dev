# Independent S10-I package audit 1

Overall verdict: **FAIL — literal graph-slice completeness**. The signed theorem and its proof **PASS**. The failure concerns conclusions retained in the published graph/source but absent from the delivered interface; it is not a kernel failure or a counterexample to the theorem actually proved.

Audited worktree `/root/code/KAM-inp-s10i`, HEAD `49f4ff147620428d0f67becf95d13a32cf4c18af`, comparison `inp` = `d9183adae208ecf2e726620694b69c8168e33006`, using `git diff inp...HEAD`. The sole changed production file is `KAM/Planetary/Nondegeneracy/Interface.lean` (191 lines). The handoff was already untracked. This report follows the user's exact worktree destination, overriding the generic brief's main-worktree destination.

No frozen anchor is assigned or closed: the design explicitly says Parts 8–10 close none. Provider/frozen-type and frozen-seal-body tests are therefore inapplicable. Instead, the independently extracted signature was elaborated with the implementation as its proof. No production file was edited, no git state-changing command was run, and all auditor-started Lean/Lake operations were serial with `LEAN_NUM_THREADS=1` and `nice -n 5`.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the package brief and handoff, P810 design and both design audits, original signature at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean:557`, Part 10 blueprint, the five assigned graph records, track-P statement conventions, and the relevant upstream declarations/definitions and frozen average/coordinate definitions. Earlier design approval is evidence about its scope, not a replacement for the present explicit literal-cut audit.

## Findings

### F1 — The literal `if-b` conclusion is not delivered

Design `P810-LEAN-DESIGN.md:241` assigns `stepP:p10:if-b` to this module. The record at `docs/graph/P/packets/P-p10.nodes.md:1639` (node begins at line 1630) says:

> a -> min_k abs(k.2sigma(a)) is continuous and positive on G_n; compactness gives a positive minimum

The source is `blueprint-P/parts/p10-nondegeneracy.tex:251`. `Interface.lean:82–85` exports the positive infimum over the **whole compact patch** and its modewise lower bound. Lines 103–148 prove this soundly by continuous image of `closedBall ×ˢ k4`, compact attainment, and NR4. They do not state or prove continuity/pointwise positivity of the **function of a obtained by minimizing over k** on `goodAxes D`. None of the other two public declarations states that conclusion either.

Refutation attempt: the compact-product argument is a valid alternative proof of the parent's NR4 bound, and `sorted_analytic` plus finiteness can prove the omitted function statement. That establishes the parent bound, but does not export the literal graph conclusion explicitly required by this audit. The current graph has no recorded alternate-route/bypass for this cut. Thus do not mark the whole cut delivered merely from the parent theorem compiling. Retain the exact signed `interface` type and add a distinctly named companion for the literal finite-minimum function, including nonempty/finite mode guards discharged from `2 ≤ n`; alternatively obtain an explicit graph-owner disposition. No extra source premise is necessary.

### F2 — The promised S10-S/stability part of the full interface is missing

The design's S10-I row (`P810-LEAN-DESIGN.md:452`) lists S10-S as an input. The parent graph record (`P-p10.nodes.md:1567`) retains “stability applies with its positivity guard”; its direct stability edge is at line 1587. The blueprint at `p10-nondegeneracy.tex:245` says “Lemma … stability holds for omega = tilde-varpi”, with positivity guaranteed for every order above the index.

`Interface.lean:8–12` does not import Stability; recursive inspection of its 101-module KAM import closure confirms Stability is absent. Its export at lines 75–93 has no stability conclusion or specialized stability companion. The monotone positive amount guard itself is correctly delivered, but the rest of the stability assertion is not available from importing this interface.

Refutation attempt: the proved general theorem `Nondegeneracy.stability` in `Nondegeneracy/Stability.lean:208` can be applied after an additional import; the exported open/compact/analytic patch properties discharge its patch hypotheses, and beta monotonicity supplies positivity. Consequently this is a small interface/completeness repair, not unpaid new analysis. Nevertheless that application/import is absent, so the explicitly requested complete S10-S consumption cannot be certified. Preserve the signed theorem and add the designed import plus a named specialization with the original perturbation/bound hypotheses, or explicitly reconcile the source/graph contract. Importing Stability alone would expose the general supplier, but is not a receipt for the literal specialized graph clause.

### N1 — Ancillary parent clauses need an explicit scope disposition

The parent `SOURCE_CONCLUSION` (`P-p10.nodes.md:1567`; blueprint lines 238,242) also mentions sorted simple negative analytic spectrum/local rotations, and R-nondegeneracy of nu alone and the secular vector under the stated rescalings/relabellings. The signature returns goodAxes membership and full-frequency analyticity/R-nondegeneracy, rather than these expanded assertions. In particular `Interface.lean:171` explicitly discards the final two results of `rnd`.

These consequences have genuine upstream suppliers (`good_ne_zero_iff`, `sorted_analytic`, `definite`, `local_analytic`, `rnd`, `scaling`) and are recoverable on the same exported patch; they are not counterexamples or new assumptions. Record them as implicit upstream consequences, or add patch-specialized companions if the full parent record is to be advertised literally. This note does not ask for unrelated diagonalization work, and does not change the exact-signature PASS.

## Node and declaration coverage

All names below are in `KAM.Planetary.Nondegeneracy`.

| Node / declaration | Lean declaration or proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p10:interface` — signed type | `interface`, lines 75–93 | PASS | Type text byte-identical to the supplied signature; fresh explicit-binder proof elaborates. All witnesses shared. |
| `bpP:p10:interface` — full retained source/graph | `interface` | FAIL | F1/F2 prevent complete literal graph-slice receipt; N1 records ancillary expansion. |
| `stepP:p10:if-a` | `exists_good_patch`; `interface` lines 95–104 | PASS WITH NOTES | One outer closed cube avoids all extra zeros and lies in goodAxes and prescribed ball. Simple-locus/continuity facts are proved locally; expanded spectrum/rotation assertions use upstream suppliers (N1). |
| `stepP:p10:if-b` | `interface` lines 105–148 | FAIL | Positive compact minimum and all mode bounds pass; literal finite-minimum function continuity/positivity remains unexported (F1). |
| `stepP:p10:if-c` | `image_action_open`; `interface` lines 149–172 | PASS | Open connected action image, compact inner image, inclusion, positive volume, analyticity and full-frequency R-nondegeneracy all returned. |
| `stepP:p10:if-d` | `interface` lines 174–187 | PASS | Least positive order, exact betaMu value, minimality, monotonicity and sphere/patch jet bound returned; coupling absent. Parent stability tail is separately F2. |
| helper, no separate graph node | `image_action_open`, lines 33–46 | PASS | Exact image/preimage identity using true inverse on axes and openness of actionDomain; no new analytic premise. |
| helper / extra finite family | `exists_good_patch`, lines 48–72 | PASS | Fin.cons joins good polynomial and every extra analytic nonzero function before choosing the patch; includes r=0. |

The design maps exactly these five graph records to S10-I (lines 239–243). Distinct theorem names for every internal cut are not inherently required; the finding is the missing literal mathematical conclusion, not a naming/counting requirement.

## Proof and definition audit

No new top-level `def`, `abbrev`, structure or instance is introduced. Local F is exactly the good-polynomial/extra-function family; local S is exactly the finite-mode absolute-frequency image over the inner compact cube. There is no fallback object. `Nat.find` is used only with the proved positive-order/positive-amount existence certificate. `sInf S` is over a proved nonempty compact set, attains a positive value, and is bounded below; no empty-infimum convention is exploited.

Ambient `Vec n` is literally `Fin n → ℝ`, so metric balls are max-norm cubes. The integer modes are `Fin n → ℤ`; the parameter sphere is explicitly the length2 unit sphere and jets are the existing squared-scalar convention, not an ambient-norm substitution. `frequency` is the actual appended Kepler frequency and twice the sorted secular spectrum. The factor two is preserved in the NR4 calculation.

S10-H supplies a real good point, good-set polynomial identification and sorted analyticity. S10-Z supplies generic simultaneous nonvanishing. S10-R supplies the actual action/axis inverse and analytic action map, and `rnd` on the chosen simple-axis ball. Its frequency/scaling declarations are available, but scaling is not used by this proof. S10-C supplies `cp09_lemma1` (which proves finite type), beta monotonicity and the pointwise beta bound. S10-S is neither imported nor consumed (F2).

Simultaneity passes: line 95 selects a0,r0 once; lines 181–185 package that same pair with its exact compact infimum and least index and beta. There are no second independent patch existentials. Data and the finite function family precede all patch witnesses, and no coupling variable or coupling-dependent hypothesis exists. `Data` contains physical positivity/dimension data only. No hard step is hidden in a hypothesis, field or typeclass.

The recursive KAM import closure has 101 modules, no provider and no frozen theorem; all 47 reached frozen files are definition anchors marked SEALED in the current manifest. Direct imports are Mathlib plus GoodAxes, Frequency, FiniteType and AnalyticZeros. No DRAFT_SORRY dependency appears. All three new public short names occur as declarations only in this file when searching KAM; all are namespaced, with no root declaration/shadowing introduced.

## Verification receipts

Commands below ran from `/root/code/KAM-inp-s10i` unless an absolute worktree argument is shown. Each Lean/Lake command finished before the next started.

1. Targeted gated build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s10i KAM.Planetary.Nondegeneracy.Interface
```

Exit **0**. Output: `[inp-gate] slot 2 acquired 17:17:48 for KAM.Planetary.Nondegeneracy.Interface`; `Build completed successfully (9147 jobs).` Replayed warnings occur in upstream Energy, Poincare.Chart, Mass, Coefficients, Definiteness, LocalAnalytic.Unique, Weyl, SymmetricRelation.Analytic; no warning in Interface. This was a targeted build through the existing overlay, not a clean library rebuild.

2. Signature and axioms probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10IAudit.lean
```

Exit **0**. The probe imports only Interface, opens the original namespaces/scopes and takes the literal signature from the supplied file under fresh name `audit_signature`, with body `by exact interface D hn ha hη f hf hne`. Independent text comparison printed `SIGNATURE_TEXT_IDENTICAL True`. Output:

```text
'KAM.Planetary.Nondegeneracy.image_action_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.exists_good_patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Nondegeneracy.interface' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay (the only changed module contains all three new theorems; no separate provider or lemma module):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Nondegeneracy.Interface
```

Exit **0**. Exact output: `replaying KAM.Planetary.Nondegeneracy.Interface`.

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the brief-permitted generated-root mismatch. Complete substantive output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (804 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Hygiene verdict: **PASS WITH NOTES** under the explicit stale-root exception. The root was not regenerated. No forbidden proof escape, resource override, EuclideanSpace, module-format violation, overlong file or source-line violation was reported.

5. Protected paths and whitespace:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0**, no output. `git diff --stat inp...HEAD` reports only Interface (191 insertions). New definitions: none. New public declarations: exactly the three axiom-checked theorems above.

6. Import-availability refutation probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S10IAvailability.lean
```

Probe contents: import Interface, then `#check KAM.Planetary.Nondegeneracy.scaling` and `#check KAM.Planetary.Nondegeneracy.stability`. Expected diagnostic exit **1**. The first check prints the general positive-rescaling/permutation theorem; the second reports:

```text
.lake/abi-scratch/S10IAvailability.lean:3:7: error(lean.unknownIdentifier): Unknown identifier `KAM.Planetary.Nondegeneracy.stability`
```

This independently confirms the S10-S import gap rather than inferring it just from a textual import list.

Both auditor-created scratch files were deleted after their commands completed. Final Python checks found no pending placeholders or trailing whitespace in the report; `git diff --check` exited 0. Final `git status --short` contains only the new audit report and the pre-existing untracked S10-I handoff. No tracked file was modified.

## Errata, deviations and limits

No suspected false frozen statement or new pinned-paper mathematical erratum was found. F1/F2 are implementation/design-to-graph coverage gaps with the exact source quotes and locations above; N1 records the remaining implicit source consequences. They must not be silently repaired in the blueprint, manifest or audit. The compact-product NR4 argument is mathematically valid; it changes the route without paying the literal function-level cut. Earlier P810 design audit PASS does not waive the present user's explicit completeness focus.

No production repair or root regeneration was performed. Passing elaboration, axioms and kernel replay certifies the theorem actually stated; it does not certify full graph coverage or a frozen/root closure. Re-audit the missing companions/import reconciliation before marking S10-I complete.
