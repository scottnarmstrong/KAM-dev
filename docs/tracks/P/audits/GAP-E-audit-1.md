# GAP-E independent audit 1

Overall verdict: **FAIL** for literal completion of `bpP:p11a:weak-kam-quantitative`
and `stepP:p11a:qt-k6`. **PASS** for `stepP:p11:as-b2` and
`bpP:p11a:situation`. The Lean proofs checked are sound; the failure is an
unsigned export whose conclusion omits part of its source contract.
No frozen anchor is proposed for sealing by this package.

Audited HEAD: `44378ed49ef831ed4823c41756b5629930beb5df`.
Comparison ref `inp`: `c2be145a358746329fa8147c2f951d8bfc7ecbfb`.
Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package brief in
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the GAP-E handoff,
track P statement, P11A/B/C design mappings, graph records and cited blueprint text.
The user's exact report destination overrides the generic brief's main-worktree destination.
Scope is exactly the three new files below; inherited proofs were inspected as interfaces,
not re-audited as independent packages. No repository source was changed.

## Blocking finding: the chosen Delta is not bounded in the exported statement

`KAM/Planetary/Quantitative/AssemblyK6.lean:30-41` exports one
`QuantitativeFamily` and the direct pointwise estimate
`norm(Q.torus b' θ - (θ,b')) ≤ cD * eps^(1/2) * b^(-G0)`.
The family already carries `norm(...) ≤ p11c_displacement ...` through its
`displacement` field (`Quantitative/Interface.lean:61-77`). But neither the new
conclusion nor a field of that family asserts

```lean
p11c_displacement { d with beta := b } cDelta eps ≤
  cD * eps ^ (1 / 2 : ℝ) * b ^ (-p11c_G0 d)
```

for the **same existentially exported cD**.

The required source is unambiguous:

- `docs/graph/P/DEPGRAPH.md:28482`: “sup¦u_b¦<=Delta<=c_Delta c_gamma
  eps_f^{1/2} beta^{-G_0}”.
- `blueprint-P/parts/p11a5-quantitative-theorem.tex:87`: “where $\Delta$
  is the number of (K3)”; that clause requires both inequalities.
- The same missing intermediate inequality is required by the parent graph
  `SOURCE_CONCLUSION` at DEPGRAPH.md:28197 and the proof step at blueprint line 109.

Two separate upper bounds on an actual defect do not order those upper bounds.
The distinction matters even when the actual defect vanishes. This is the precise
issue previously identified in `blueprint-P/reviews/p11a5-review-1.md`, row P11A5-01.
The source was strengthened accordingly; the new unsigned export must retain it.

This is a small export repair, not an unpaid analytic estimate:
AssemblyK6.lean:45 obtains `hflat` from `displacement_power_flat`, and line 51
uses `(Q.displacement ...).trans (hflat ...)`, discarding the intermediate bound.
Export `hflat b hb eps he0` alongside that same Q and cD, preferably as the
literal two-inequality chain. Do not infer the missing clause from compilation.
An independent probe confirmed the imported numerical lemma already supplies it.

K5 note: the new theorem conjoins the beta lower bound only. Its inherited
`p11c_budget` supplies monotonicity/comparison and `qb_poly` supplies the general
all-data bound; this split is disclosed by the handoff and P11C design. Therefore
those clauses remain available as separate exports, but the new theorem alone is
not a self-contained statement of all K5 clauses. This does not repair the missing
same-cD Delta conclusion above.

## Node and declaration results

All names in this table have prefix `KAM.Planetary.`.

| Node | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| bpP:p11a:weak-kam-quantitative | weak_kam_quantitative_full, AssemblyK6:30 | FAIL | One Q carries K1–K4; beta budget and actual-defect power bound are joined, but the literal K6 bound on Delta is absent. |
| stepP:p11a:qt-k6 | weak_kam_quantitative_full, AssemblyK6:41,45,51 | FAIL | Correct composed proof internally; its exported conclusion loses Delta ≤ the same cD power bound. |
| stepP:p11:as-b2 | slow_b2_literal, SlowB2Kappa:24 | PASS | Literal B2 inequality, closed form, multiplicative ratio identity, kappa identity and kappa ≥ 6, eventually as eps tends to zero through positive values. |
| bpP:p11a:situation | StandingSituation, Situation:29 | PASS | Positive small eps, literal perturbation premises and selected iteration at the adapted schedule. Output packaging, not an extra hypothesis of an existence theorem. |
| bpP:p11a:situation / schedule | standingSituation_schedule, Situation:37 | PASS | Gamma, T0, t0, eps0=2eps, free radius, admissibility and positive radius. |
| bpP:p11a:situation / selection delivery | standingSituation_of_selection, Situation:48 | PASS | Retains exactly the supplied SelectionOutput with source scalar and perturbation premises. |
| bpP:p11a:situation / evaluation delivery | standingSituation_of_evaluation, Situation:54 | PASS | Uses the existing output's inherited selection iteration; no invented replacement chain. |
| bpP:p11a:situation / existence | standingSituation_exists, Situation:62 | PASS | Calls parameter_selection_adapted from only source inputs; also proves the evaluation constructor preserves its iteration. |

These four graph nodes are the GAP-E append-only ruling's entire slice. Older
P11A/B/C tables map them to SlowRates/Assembly/Evaluation and their numerical
suppliers, not to these newly added module names. The handoff explicitly assigns
these additions to the remaining literal-export gaps. No other design node is
mapped to these three modules. The two quantitative nodes remain unclosed.

## Fidelity and definition classification

All seven explicitly named declarations are unsigned additions: none occurs in
`/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, P11BSignatures.lean or
P11CSignatures.lean. Existing signed declarations are unchanged. There are no
provider exports, frozen theorem targets, or seal bodies in this diff; frozen-type
and seal-body probes are therefore not applicable.

- `StandingSituation` is a dependent output/data structure on its whole carrier.
  Its four fields are eps positivity, the scalar smallness, SelectionPerturbation
  and SelectionOutput at `selectionAdapted d eps`. It has no default or junk branch.
- `standingSituation_of_selection` and `standingSituation_of_evaluation` are
  transparent record constructors; the latter forgets extra evaluation fields
  through `toSelectionOutput`. Neither selects a fallback or changes the iteration.
- There are no other new def/abbrev/structure commands. All new declarations are
  within the exposed public noncomputable section and the KAM.Planetary namespace.

SelectionData contains the standing analytic/finite-type inputs and h;
SelectionPerturbation contains holomorphy, period-one periodicity, reality and the
literal norm bound on `complexStrip × actionNbhd`. SelectionOutput extends
SelectionIteration (K_nu, X_nu, R_nu, frequency chain), includes compact nested
limit sets and omega-star, and records the parameter-selection conclusions.
These conclusions are carried as **delivered output**: standingSituation_exists
constructs the record rather than assuming one. This satisfies the source's
output interpretation of (S) (blueprint 11a4:30-33; graph 26481-26484).
The signed B19 `situation` remains the unchanged SelectionEvaluationOutput alias;
a fresh rfl probe verified that alias and exact selection-constructor preservation.

For the quantitative theorem, cDelta is chosen before d and depends on precisely
(N,mu,tau,s,C1). cD and the budget constant precede the varying replacement beta b,
h,f and eps; one Q supplies both family clauses and the direct bound. A reference
beta is carried in d, as disclosed in the handoff; the numerical construction uses
qbBetaC and gamma lower bounds without dependence on that reference beta. There
is no new analytic premise beyond weak_kam_quantitative's inputs. The beta interval
and validity reconstruction are correct; eps=0 is included.

For B2, gamma>0, tau≥0, nu≥1 and sigma>0 are source numerical data; c0 may be any
real (stronger than the positive source constant). K is precisely
`3*nu/(pi*sigma)*log(1/eps)`. The identity is E2 = closed-form bound times the
stated ratio; eventual positivity of eps, log and K legitimizes that ratio.
The nhdsWithin formulation is the source's sufficiently-small-positive-eps claim.

## Independent checks

All Lean/Lake commands were serialized, with LEAN_NUM_THREADS=1 and nice -n 5.
The compile-gate script itself applies nice. No resource override was used.

1. Full `git diff inp...HEAD`: exactly 202 added lines in AssemblyK6.lean (55),
   SlowB2Kappa.lean (73), Situation.lean (74), with no other committed changes.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0.
2. Targeted gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gape KAM.Planetary.Quantitative.AssemblyK6 KAM.Planetary.Preparation.SlowB2Kappa KAM.Planetary.WeakKAM.Situation
   ```

   Exit 0. Output starts `[inp-gate] slot 2 acquired 01:16:18` and ends
   `Build completed successfully (9254 jobs).` Replayed warnings belong to
   inherited dependencies, not the three scoped files.
3. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.AssemblyK6 KAM.Planetary.Preparation.SlowB2Kappa KAM.Planetary.WeakKAM.Situation
   ```

   Exit 0. Complete output:

   ```text
   replaying KAM.Planetary.WeakKAM.Situation
   replaying KAM.Planetary.Preparation.SlowB2Kappa
   replaying KAM.Planetary.Quantitative.AssemblyK6
   ```
4. Probe command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GapeAudit.lean
   ```

   Exit 0, including three examples: unchanged B19 alias, exact constructor
   preservation, and the already-available literal numerical Delta bound.
   `#print axioms` output for each of weak_kam_quantitative_full, slow_b2_literal,
   StandingSituation, standingSituation_schedule, standingSituation_of_selection,
   standingSituation_of_evaluation and standingSituation_exists is exactly
   `[propext, Classical.choice, Quot.sound]`. No sorryAx.
5. Recursive local import inspection: 208 KAM modules, 26 reachable frozen
   definition anchors, all manifest state SEALED; no frozen theorem anchor and
   no provider module is reachable. No DRAFT_SORRY import.
6. Public short-name scan across KAM: each of the seven explicit names has exactly
   one declaration. Namespace scope creates no harmful root shadow. Maximum line
   widths are 94 / 95 / 96 respectively; all files satisfy the 1500-line cap and
   module header/public-interface requirements. No forbidden proof escape,
   EuclideanSpace or resource override in the scoped files.
7. Full lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1192 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   This is exactly the generated-root exception permitted by the audit brief.
   The root was not regenerated. No other lint failure occurred.

## Errata, deviations and limits

No suspected pinned-source defect was found in this slice. The blocking item is
a Lean export/blueprint mismatch, not an assertion that the source theorem is false.
AssemblyK6's module documentation at lines 15-17 claims the full chained K6 bound;
its theorem conclusion does not expose that chain. The handoff discloses the split
K5 export and reference-beta formulation; those do not authorize weakening K6.

No auditor-introduced mathematical deviation, changed hypothesis or changed frozen
file. Scratch probes and audit logs were removed after recording results here.
The report is the only auditor-created repository file; the untracked handoff
existed at entry and remains untouched. Final whitespace validation passed.

This audit checks the named gap-fill exports against their literal graph and
blueprint contracts. Kernel success and acceptable axioms establish soundness of
what is stated; they do not close the two incomplete quantitative graph nodes or
seal any campaign theorem.
