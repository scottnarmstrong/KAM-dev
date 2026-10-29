# GAP-E independent audit 2

Overall verdict: **PASS WITH NOTES** for the scoped package. The audit-1 blocking
K6 omission is repaired. All four assigned graph nodes are established by the
scoped exports together with the existing budget exports specified by the design.
No frozen theorem anchor is targeted; this is not a campaign theorem seal.

Audited HEAD: `e8a4a7a679f33c64df8f516f3d4869ba08f1fa05`.
Comparison ref `inp`: `c1839fee225146e0c60e389ca73433801f3a9c52`.
Merge base: `be897bef500bb96a3f0f2bd9243fad22a548cfc1`.
The full `git diff inp...HEAD` contains three new Lean modules (208 lines),
the handoff (45 lines), and audit 1 (210 lines). Reviewed that full comparison,
including the repair relative to audit 1's `44378ed4`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff and audit 1,
track P statement, P11A/B/C designs and signature files, the four graph NODE
records and their cited blueprint text. The user's exact destination overrides
the brief's generic main-worktree destination. Only this report is a persistent
repository edit; temporary probes were confined to `.lake/abi-scratch/`.

## Node and declaration verdicts

Names below have prefix `KAM.Planetary.`.

| Graph node | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| bpP:p11a:weak-kam-quantitative | weak_kam_quantitative_full, Quantitative/AssemblyK6.lean:31 | PASS WITH NOTES | One Q carries K1–K4 and both K6 inequalities, with constants before varying beta. K5 is completed by the separate existing budget exports, as the design specifies. |
| stepP:p11a:qt-k6 | weak_kam_quantitative_full, AssemblyK6.lean:41–57 | PASS | Exports actual defect ≤ named Delta ≤ the same cD power bound, and its composition, including eps=0. |
| stepP:p11:as-b2 | slow_b2_literal, Preparation/SlowB2Kappa.lean:24 | PASS | Eventual B2, exact closed form, ratio identity, kappa identity and kappa ≥ 6 from source numerical data. |
| bpP:p11a:situation | StandingSituation, WeakKAM/Situation.lean:29 | PASS | Source positive-epsilon inputs and the delivered selected iteration at the adapted schedule. |
| bpP:p11a:situation / schedule | standingSituation_schedule, Situation.lean:37 | PASS | Gamma, T0, t0, eps0=2eps, free radius, scalar admissibility and radius positivity. |
| bpP:p11a:situation / selection delivery | standingSituation_of_selection, Situation.lean:48 | PASS | Preserves the supplied SelectionOutput exactly. |
| bpP:p11a:situation / evaluation delivery | standingSituation_of_evaluation, Situation.lean:54 | PASS | Preserves the evaluation output's inherited selection chain exactly. |
| bpP:p11a:situation / existence | standingSituation_exists, Situation.lean:62 | PASS | Constructs the output from source premises through parameter_selection_adapted, with no iteration premise. |

These are the entire append-only GAP-E slice. The older design tables map these
nodes to Preparation/Slow, WeakKAM/Evaluation and Quantitative/Assembly plus
numerical suppliers; none maps additional nodes to the three new module names.
The handoff's explicit overnight ruling assigns these additions to the remaining
literal-export obligations. This audit does not re-audit all inherited packages.

## Quantitative fidelity and repair

Graph `docs/graph/P/DEPGRAPH.md:28188–28228` and `28473–28504`, and blueprint
`blueprint-P/parts/p11a5-quantitative-theorem.tex:72–110`, require the same
family and the chain “sup¦u_b¦<=Delta<=c_Delta c_gamma eps_f^{1/2} beta^{-G_0}”.
In particular blueprint line 87 says “where $\Delta$ is the number of (K3)”.

Current AssemblyK6.lean:42–45 explicitly exports the first inequality and the
bound on `p11c_displacement` using the very same existential `cD`, `cDelta`,
beta and eps. Line 56 returns `Q.displacement` and `hflat b hb eps he0` as separate
conjuncts; line 57 also composes them. This directly repairs audit 1's finding:
it no longer attempts to order two upper bounds merely from a bound on the defect.
The named Delta remains literally
`min (2^(-18)) (cDelta * Real.sqrt eps / d.gamma)` (Interface.lean:58–59).

The cDelta quantifier precedes d and depends only on `(N,mu,tau,s,C1)`.
After valid reference data d, cD and the beta-budget constant precede varying
`b ∈ (0,min 1 d.M]`, h, f and eps. Every analytic input is exactly the existing
`weak_kam_quantitative` input for `{d with beta := b}`; validity is rebuilt from
`qbBeta_valid`, the unchanged tau condition, and b≤1. There is no added analytic
premise or family chosen independently for K6. Nonnegative eps includes zero.
The pointwise norm bounds express the source uniform sup bounds on the ambient
Pi/product max norm, without introducing a different norm or carrier.

Reference-beta note: d contains a reference beta, so the type expresses uniformity
under replacement beta rather than an explicit beta-free data structure. The
actual cD comes from `displacement_power_flat`: `cDelta / k`, with k supplied by
`qbPoly_gamma_lower` using `(N,mu,rho,tau,qbBetaC d)`; `qbBetaC` at Budget.lean:91–93
uses vartheta,s,epsLoss,M,M0,C1,diameter and excludes beta. Thus the construction
has the stated fixed-entry dependence. This is the disclosed formulation, not
an added source hypothesis.

K5 note: `weak_kam_quantitative_full` conjoins its beta lower bound only; it is
not by itself a self-contained statement of every K5 clause. Monotonicity and
comparison remain in `p11c_budget` (Budget.lean:157), with the general all-data
bound in `qb_poly`. P11C-LEAN-DESIGN.md:158 expressly allocates K5 this way;
the node table at lines 75 and 84 likewise lists the assembly and budget suppliers.
These are data-only exports, applicable to the same d using hd.1, and do not
select a second family. Under this documented package allocation the parent node
passes with this qualification. A claim that the new theorem alone states all
of literal K5 would overstate its signature.

## B2 and standing situation

Graph DEPGRAPH.md:20458–20485 and blueprint
`p11-cp09-preparation.tex:183` require E2's eventual smallness and
`kappa = 2*pi*K2*sigma3 = 6*nu2*log(1/eps) >= 6`.
The theorem substitutes the exact K2 coefficient `3*nu/(pi*sigma)`, the literal
E2 majorant, and alpha2=`eps*(gamma/4*K^(-tau))`. Its closed form is
`pi*gamma/512 * eps^2 * K^(-tau-1)` and its ratio factor is
`512*c0/(pi*gamma)*(3*nu/(pi*sigma))^(tau+1) *
(eps^(1/2)*log(1/eps)^(3*tau+2))`.
The multiplicative identity represents the ratio on the eventual positive-eps,
positive-log, positive-K region used in the proof. `nhdsWithin 0 (Ioi 0)` is
exactly sufficiently small positive eps. Gamma>0, tau≥0, nu≥1 and sigma>0
are source numerical data; arbitrary real c0 strengthens the positive source case.
It composes the inherited numerical bound and proves the additional identities
and kappa lower bound. No full averaging theorem is claimed in this slice.

Graph DEPGRAPH.md:26474–26507 and blueprint `p11a4-limit-family.tex:30–33`
require the iteration as a delivered output, with the adapted schedule and
positive eps. `SelectionData` and `SelectionPerturbation` carry the standing
analytic and scalar inputs; `selectionGamma` is the specified half gamma-star.
`selectionAdapted` fixes gamma,T0,t0 from d, eps0=2eps and
s0=sqrt(2eps/(n*C1)); the schedule theorem proves its admissibility.
`SelectionOutput` extends the iteration record, carrying the same K_nu,X_nu,
R_nu,frequency chain, Kinf=intersection K_nu, Hinf⊆Kinf and omega-star.
Its existing Diophantine field is a delivered conclusion of parameter selection,
not an added premise of `standingSituation_exists`. The explicit constructors
accept earlier delivered outputs and preserve them; the existence theorem takes
only source inputs and invokes parameter_selection_adapted.

## Signatures and definition classification

All seven explicitly named additions are UNSIGNED: none is declared in the
P11A/B/C signature files under `/root/code/KAM-inp/.drafts/design/`.
No signed declaration is changed. The signed B19 `situation` alias in
WeakKAM/Evaluation.lean still unfolds to SelectionEvaluationOutput; an independent
rfl probe checked this and both constructors' exact iteration preservation.
There are no new providers, frozen targets or seal bodies; provider/frozen-type
and seal-body equality probes are not applicable.

- `StandingSituation`: dependent output/data structure, intended over its whole
  carrier, with eps positivity, smallness, perturbation and selected iteration.
- `standingSituation_of_selection`: transparent record constructor; no fallback.
- `standingSituation_of_evaluation`: transparent record constructor using
  `toSelectionOutput`; no replacement chain or fallback.

There are no other new def/abbrev/structure commands. All additions are in the
exposed public noncomputable section and KAM.Planetary namespace. No harmful
root shadow or duplicated explicit public helper short name was found.

## Independent validation

All Lean/Lake invocations were sequential with `LEAN_NUM_THREADS=1` and
`nice -n 5` (the compile gate itself supplies nice). No resource override,
clean, dependency update, cache fetch or generated-root regeneration was used.

1. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0.
2. Targeted gate command:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gape KAM.Planetary.Quantitative.AssemblyK6 KAM.Planetary.Preparation.SlowB2Kappa KAM.Planetary.WeakKAM.Situation
   ```

   Exit 0. `[inp-gate] slot 1 acquired 01:32:16 ...`;
   final output `Build completed successfully (9254 jobs).`
   Replayed warnings were in inherited dependencies, not the scoped modules.
3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Quantitative.AssemblyK6 KAM.Planetary.Preparation.SlowB2Kappa KAM.Planetary.WeakKAM.Situation
   ```

   Exit 0; complete output:

   ```text
   replaying KAM.Planetary.WeakKAM.Situation
   replaying KAM.Planetary.Preparation.SlowB2Kappa
   replaying KAM.Planetary.Quantitative.AssemblyK6
   ```
4. Probe command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GapeAudit2.lean
   ```

   Exit 0. Three rfl examples passed (B19 alias, selection constructor and
   evaluation constructor preservation). `#print axioms` of every explicit
   export produced exactly:

   ```text
   'KAM.Planetary.weak_kam_quantitative_full' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.slow_b2_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.StandingSituation' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.standingSituation_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.standingSituation_of_selection' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.standingSituation_of_evaluation' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.standingSituation_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

5. Recursive local-import inspection: 208 KAM modules, no provider and no frozen
   theorem; all anchors in the 26 reachable frozen definition modules are SEALED
   in the current manifest. No DRAFT_SORRY import.
6. Scoped files have respectively 61/73/74 lines, maximum widths 98/95/96.
   Copyright, module, public imports, module docstrings and public sections pass.
   All seven explicit names have exactly one declaration in KAM. No forbidden
   proof escapes, EuclideanSpace or resource override in the scoped files.
7. Full lint command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1; complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1192 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The sole failure is exactly the generated-root exception allowed by the
   audit brief. The root remains untouched.

## Errata, deviations and limits

No new suspected pinned-source defect or frozen-statement defect was found.
The earlier K6 mismatch is repaired in the unsigned export, not by changing the
source or a frozen signature. The K5 split and reference-beta representation
are disclosed above. The handoff still describes the older direct-composition
formulation, but the current code now exposes the intermediate Delta bound too.
Graph LEAN_STATUS fields remain historical metadata; this report does not edit them.
No auditor-introduced mathematical deviation or change to protected files.
Scratch was removed. Final whitespace validation passed; git status shows only
this new report. HEAD remained at the audited revision.
