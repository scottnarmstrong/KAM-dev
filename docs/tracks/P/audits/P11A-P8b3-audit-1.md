# P11A-P8b3 independent audit 1

Verdict: **PASS WITH NOTES** for `stepP:p11:pr-d` and its export `KAM.Planetary.p11_pr_d`.
No blocking finding in the audited module. This is an infrastructure-node audit, not a frozen-anchor seal or a proof of the complete signed `prepared` theorem. No frozen anchor is supplied by this package, so provider/frozen-type equality and frozen seal-body probes are not applicable.

Audited checkout: `/root/code/KAM-inp-p11ap8b3`, HEAD `2526f740b776df512dd67a7d60a6202209cb2eda`; comparison branch `inp` at `f38de76be1689652e630490c1007aac7dbd74080`. Report destination follows the user's explicit worktree-path instruction, overriding the generic brief's main-worktree destination.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff/AUDIT FOCUS, track P statement, design node table and prepared clauses, graph node `stepP:p11:pr-d`, blueprint `p11-cp09-preparation.tex:196–211`, and the signed `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` prepared definitions. Reviewed the associated frozen P-G/P-FIXED theorem context and relevant frozen definitions, including `actionNbhd` and `fixedHamiltonian`.

`git diff inp...HEAD` contains seven new modules (3974 added lines). The six prerequisite modules are `PreparedOps`, `PreparedDev`, `PreparedNum`, `PreparedResc`, `PreparedFreq`, and `PreparedClose`; the handoff's explicit orchestrator ruling excludes their independent proof audits. Reviewed that diff's scope/import/declaration changes and audited the entire 730-line `KAM/Planetary/Preparation/PreparedM.lean`. No inherited-module audit verdict is implied here. The untracked handoff existed before this audit.

## Literal conclusion and consumer compatibility

Let `mu = (p11PatchData D).mu`, `ell = log (1/eps)` and `Qe = 5*C.tau+2+(C.tau+1)*(mu+1)`.

* `p11_pd_jet` proves the full Euclidean operator jet bound through order `mu+1`, including zero, with bound `2*C.L+1`. The zero-order argument uses the FullSpec Euclidean bound on `Fin.append omega ((2*pi)^-1 • Omega)`, contracts the second block by `eps ≤ 1`, and pays the perturbation dimension factor explicitly. Higher orders use `p11op_re_le` and `p11_pd_num`, paying `sqrt(2n)*(2n)^j`; no sup/Euclidean identification occurs.
* In `PreparedM.lean:699–703`, `hMb := M_bound ... hjet'` establishes the literal sharper bound `2^j*(2*C.L+1)^2`, for every unit direction, every `1 ≤ j ≤ mu+1`, and every point of the closed Euclidean `1/4` thickening. The export then bounds `2^j` by `2^(mu+1)`. This establishes the graph's intermediate `2^k M1^2` estimate in the proof and exports exactly the uniform `M*` clause required by the signed `P11PreparedSpec`; it does not discard an unmet consumer requirement.
* The second export conjunct is the signed diagonal vector jet bound through `mu`, including zero, with exactly `p11M0 n mu C.L = (2*n+1)^(mu+1)*(2*C.L+1)`. The proof first bounds it by `2*C.L+1`, then enlarges to this constant. The standing `1 ≤ C.L` also gives `1 ≤ p11M0 n mu C.L`.
* The third conjunct proves the scalar order-zero bound for every Euclidean unit direction by Cauchy–Schwarz and the zero-order vector estimate. This is the last clause of signed `P11PreparedFullSpec`.

There are no SIGNED declarations newly defined in `PreparedM`. As a consumer-context check, whitespace-normalized declarations `p11PreparedFreq`, `p11PreparedFreqR`, `P11PreparedSpec`, `p11M0`, and `P11PreparedFullSpec` in the imported `PreparedData.lean` are equal to the signed file. In particular, the three export conclusions have the same carrier, frequency, radii, derivative orders and constants as the corresponding signed clauses. The design table maps `pr-d` to a local proof in `Preparation/Prepared`; the split module supplies that entire node as an unsigned export. Final signed assembly remains P8e work as ruled in the handoff.

## Premises and constant dependence

`p11_pr_d` chooses `K > 0` before `Fast`, `eps`, `c`, `A` and `Q`. Its hypotheses are the standing `P11SecularFullSpec D C`, `1 ≤ nu`, positive epsilon, `eps*C.MF ≤ exp(-1)`, `0 ≤ c`, explicit numeric conditions `K*(1+c)*eps*ell^Qe ≤ 1`, `3*pi*eps ≤ pi*C.rz^2/16`, `5*eps ≤ p11s2 C nu eps`, and the actual fast/slow source specifications. `K` may depend on fixed data, `nu` and fixed derivative order, as allowed by the recorded P-A002 ruling. Neither `M*` nor `M0*` depends on epsilon or nu.

The remaining `hN` premise identifies the arbitrary supplied `Q.N` with the actual rescaled `(A.h0+A.g2)/eps` on `actionNbhd box 1`. This is construction/identification data for a generic prepared object, not an assumed derivative, jet or scalar estimate. It is the same defining identity required by the first clause of the signed prepared specification (specialize its angle to zero). The theorem proves differentiability and all required bounds from this identity; it assumes none of the quantitative outputs of `pr-b`, `pr-c`, `M_bound`, or this node. Helpers with explicit numeric bounds are separately named and are discharged in `p11_pd_dev0`, `p11_pd_ord`, `p11_pd_jet` and the export.

The FullSpec input is intentional: design lines 847–855 declare the enlargement of the freely chosen initial L to a Euclidean main-term bound before averaging constants, nu and epsilon. `holo_chart` constructs that full specification. It is not an extra physical hypothesis or an unreported repair.

## Declaration-by-declaration results

All names in the table are in namespace `KAM.Planetary`; locations are in `PreparedM.lean`.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| pr-d / Euclidean perturbation | `p11_pd_euclid_add` (30) | PASS | Cauchy–Schwarz gives the explicit `sqrt N*d` error. |
| pr-d / main derivative | `p11_pd_omega_partial` (63) | PASS | Actual first partial of `C.h` equals `omega` on its original ball. |
| pr-d / J deviation | `p11_pd_dev_pure` (75) | PASS | Derived deviation bound with explicit numeric helper premises. |
| pr-d / rho deviation | `p11_pd_dev_rho` (145) | PASS | Retains epsilon and `1/(2*pi)` normalization. |
| pr-d / zero-order input | `p11_pd_dev0` (209) | PASS | Derives both deviations with common Qe and K fixed before eps. |
| pr-d / rescaled domain | `p11_pd_point` (311) | PASS | Explicit decomposition and strict Cauchy-region inclusions. |
| pr-d / regularity | `p11_pd_freq_diff` (343) | PASS | Derives holomorphy from the supplied construction identity. |
| pr-d / real domain | `p11_pd_thick_mem` (376) | PASS | Correct closed Euclidean to open sup-neighbourhood comparison. |
| pr-d / contraction | `p11_pd_euclid_mono` (389) | PASS | Coordinatewise complex norm monotonicity. |
| pr-d / index conversion | `p11_pd_single_cast` (394) | PASS | Literal first-block multi-index identity. |
| pr-d / index conversion | `p11_pd_single_nat` (418) | PASS | Literal second-block multi-index identity. |
| pr-d / vector order zero | `p11_pd_zero` (427) | PASS | FullSpec controls the main vector; dimension error is paid. |
| pr-d / numeric weakening | `p11_pd_prem` (525) | PASS | Monotonicity under a nonnegative common smallness factor. |
| pr-d / tensor constants | `p11_pd_num` (530) | PASS | Explicit finite-dimensional derivative loss absorbed into K. |
| pr-d / positive vector orders | `p11_pd_ord` (552) | PASS | All orders `1..mu+1`; no derivative-bound premise. |
| pr-d / real regularity | `p11_pd_contdiff` (612) | PASS | Holomorphic frequency restricted to the real slice. |
| pr-d / complete vector jet | `p11_pd_jet` (621) | PASS | Includes zero and every positive order through `mu+1`. |
| `stepP:p11:pr-d` | `p11_pr_d` (655) | PASS WITH NOTES | All three signed-consumer clauses; sharper `2^j` bound established internally. Generated-root lint note below. |

## Definition classification and hygiene

No new `def`, `abbrev`, `structure`, instance or notation is introduced in the audited module. Local `set`/`generalize` expressions name actual arithmetic quantities, domains or main vectors. No selected fallback or junk branch is used. `p11PreparedFreq` is the actual complex derivative; the equality premise and proved local regularity prevent reliance on a totalized non-differentiable fallback. The inherited choice-based `p11PreparedData` selector is never used in this proof: arbitrary Q is handled through its explicit identity.

Source scan: 730 total lines; zero lines over 100 Unicode characters; no forbidden proof escape, resource override or `EuclideanSpace`. Copyright/module/public imports/module docstring/public section are present. All 18 newly declared short names occur only once among KAM declaration headers; there is no new root declaration or harmful shadow. The KAM import closure has 380 modules, no provider and no frozen theorem module; all 64 imported frozen definitions are manifest `SEALED`. In particular there is no transitive DRAFT_SORRY theorem dependency.

The following checks were independent reruns in this worktree, serialized with `LEAN_NUM_THREADS=1`; every Lean/Lake command used `nice -n 5` (the build gate supplies it internally).

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8b3 KAM.Planetary.Preparation.PreparedM` — exit 0. Output starts `[inp-gate] slot 1 acquired 03:10:41 for KAM.Planetary.Preparation.PreparedM` and ends `Build completed successfully (9426 jobs).` Existing prerequisite linter warnings were replayed; none was reported from PreparedM. No heartbeat override was used.
2. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP8b3Audit.lean` — exit 0. The probe imports PreparedM, prints axioms for all 18 theorems, and copies the entire literal `p11_pr_d` declaration under a fresh name with body `by exact p11_pr_d hCF hnu`. The copied-type/body check elaborated with no error. No frozen provider was claimed, so no unrelated anchor equality probe was substituted.

Exact axiom output:

```text
'KAM.Planetary.p11_pd_euclid_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_omega_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_dev_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_dev_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_dev0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_point' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_freq_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_thick_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_euclid_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_single_cast' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.p11_pd_single_nat' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.p11_pd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_prem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_contdiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pd_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pr_d' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedM` — exit 0. Exact output:

```text
replaying KAM.Planetary.Preparation.PreparedM
```

4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` — exit 1, solely the brief-permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1200 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The handoff's four inherited overlong-line warnings are absent at this HEAD (the merged branch includes line-length cleanup). No substantive lint failure remains. The generated root was not edited or regenerated.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` — exit 0, empty output. `git diff --check inp...HEAD` — exit 0, empty output. The full comparison contains only the seven preparation modules listed above. Final report whitespace and report-only edit checks also passed.

## Notes, uncertainties and errata

* **Generated root:** the sole lint failure is the explicitly allowed stale generated root. Regeneration belongs to integration; it is not a defect in this proof module.
* **Assembly boundary:** this audit establishes all of pr-d, including its intermediate sharper scalar estimate. It does not establish `prepared`, `amount`, final same-Q selection, the existence of the common epsilon threshold, or a frozen P-FIXED provider. Those remain their assigned packages' obligations. In particular all smallness conditions are explicit numeric premises here, as the focus requests; no existential threshold closure is claimed.
* **Gauge wording:** graph `docs/graph/P/DEPGRAPH.md:20716` and blueprint `p11-cp09-preparation.tex:211` say “max-norm operator norm” in the comparison with the diagonal norm. Signed `p11op` uses Euclidean input balls and Euclidean output lengths. Design `P11A-LEAN-DESIGN.md:847–855` explicitly reconciles this through the enlarged initial Euclidean L and paid finite-dimensional factors. This module follows that declared design; it does not silently identify the gauges. No new source erratum or unreported mathematical deviation was found.
* The reported original monolithic default-heartbeat failure is a prover receipt, not an independently reproduced failure. The split proof passed the independent targeted build with default budgets.

No blocking uncertainty remains for the scoped node. No repository file except this report was edited by the auditor; temporary probe/diff/log files created for this audit under `.lake/abi-scratch/` were removed after recording their results. No state-changing git action was taken.
