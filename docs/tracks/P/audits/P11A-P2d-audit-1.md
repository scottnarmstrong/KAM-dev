# Independent package audit: P11A-P2d (audit 1)

Overall verdict: **PASS WITH NOTES for the authorized P2d chart slice**. No blocking defect found in `KAM/Planetary/Preparation/HoloChart.lean`. The chart's analyticity, symplecticity, membership and both lattice clauses are proved from the P2b interface. This is helper-package approval, not a frozen-anchor seal or closure of `holo_chart`/P-FIXED.

## Scope, authority and snapshot

Audited HEAD `5755075900eece8bfe50130916b12742554f8d83`; comparison ref `inp` was `8f19267d4a71f86284c9979293b8f991fb2c0b96`. Ran the required `git diff inp...HEAD`. Git reports multiple merge bases and selects `d69dedecde7104870d7281ffe9dba51228f5e523`. The full comparison contains eight added files (1953 lines): the seven inherited P2b files plus HoloChart. The delta since P2b merge `19aa780f` is exactly HoloChart. Substantive proof review is restricted to that file by AUDIT FOCUS; P2b is an accepted input, not independently re-certified here.

Read AGENTS, PLAN, DECISIONS, the absolute audit brief, the supplied handoff and its overnight 20:40 split ruling, P11A design/node table, design audits 1–3 and their disposition, current signature chart clauses, track P statement, blueprint P Part 11 L63–84 and graph packet hc-id/hc-lat rows, the downstream preparation signatures, and relevant imported/frozen coordinate, Hamiltonian, domain and symplectic definitions. The user's exact report destination overrides the generic brief's main-worktree destination.

Snapshot SHA-256:

- HoloChart: `ffe22c726fc9ea7720b0913b3f88e17f6969aeb48ba6c5f94fd0e0738f905393`.
- `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`: `627ab032a68be7aca3f547d898c1e82fe8146c18a363a5dd63163916b8d3beee`.
- `docs/tracks/P/design/P11A-LEAN-DESIGN.md`: `2a76150dbcbee3ca01974d01e2d0ec73a2a0dd1063301bb519b9136a54652d4a`.

## Node coverage, fidelity and consumers

`stepP:p11:hc-id`: **PASS for the chart/domain/analyticity/symplecticity slice assigned to P2d**. `chartInput_eq` identifies the literal signed chart input with `liftInv R (T1 z)`. `chartInput_mem` pays the action displacement by the patch's δ/8 bound and rC/π ≤ δ/8; each slow component is bounded by Brho*rz, so Gamma ≤ (Brho*rz)^2 ≤ δ. The forward tube supplies actual product-chart domain membership and the circular tube. The latter implies the exact `collisionFreeDomain`. Analyticity uses equality on a neighborhood, rather than pointwise equality to justify differentiation. The chain-rule proof preserves the frozen positions/momenta order and symplectic multiplier 1.

`stepP:p11:hc-lat`: **PASS**. Unit shifts in θ become 2π shifts before the product chart; the inverse lift commutes with them. Domain saturation is proved. Equality of chart images implies equality modulo exactly the unit fast-position lattice, with actions and slow blocks unchanged. Both Q1 and Q2 are exported, not merely mentioned locally.

There is no newly SIGNED declaration and no provider/frozen theorem to seal in this slice. The helper `chart_spec` conclusion is the signed `P11SecularSpec` final `let O := ...` conjunct **exactly after whitespace removal**. A separate Lean probe copies that conjunct from the absolute signature file and applies `d.chart_spec C hJ0 hrC hrho hh hsig hrz hch hF`; this checks the intended P2f call against the independently sourced target, not just the helper's own type. Frozen-provider `type_of%` and frozen seal-body probes are therefore not applicable.

The input equalities identify chosen data; `hch` is the literal definition to use when constructing the output chart, not an assumed analytic or symplectic conclusion. The needed `P11HoloData` fields are established in the accepted P2b construction. No chart theorem assumes its hard analytic, symplectic, collision or lattice conclusion. The radius condition is genuine construction smallness; it can be achieved before epsilon is selected. No widened constant dependence or changed norm/carrier was found.

The energy identity's real-F identification belongs to **P2f**, by the explicit handoff ruling at L60. `chart_energy` and the energy part of `chart_spec` are useful conditional helpers only. They do not prove that P2c's selected F satisfies `hF`, nor prove `holo_chart`. Do not mark the unsplit hc-id node fully closed on this report alone. The broader design node table still names the original Holomorphic assembly module; this split audit certifies its assigned geometric suppliers, not other P2 subpackages. No unsigned export is named `hc_id`, `hc_lat` or `holo_chart` while stating a narrowed node theorem.

All 33 new declarations are covered below. Names without a namespace prefix are in `KAM.Planetary`; `P11HoloData.*` names have that same outer namespace.

| Node / role | Declaration in HoloChart | Verdict | Reason |
|---|---|---|---|
| `hc-id / hc-lat` | `p11FastScaleL` (L43) | PASS | Literal linear fast-block conversion; slow position/momentum order preserved. |
| `hc-id / hc-lat` | `p11FastScale` (L56) | PASS | Continuous linear realization of the same finite-dimensional map. |
| `hc-id` | `p11FastScale_apply` (L59) | PASS | Unfolding equation on the whole carrier. |
| `hc-id` | `fast_snd_p11FastScale` (L63) | PASS | Exactly J/(2π). |
| `hc-id` | `p11FastScale_symplectic` (L68) | PASS | Direct cancellation of 2π in the frozen momentum-wedge-position form. |
| `hc-lat` | `p11FastScale_injective` (L78) | PASS | Global injectivity; no domain premise. |
| `hc-lat` | `p11FastScale_shift` (L97) | PASS | Unit fast-position lattice becomes the literal frozen fastShift. |
| `hc-id` | `p11FastScale_isSymplecticOn` (L104) | PASS | Derivative of the continuous linear map on univ. |
| `hc-id` | `p11RealDom` (L117) | PASS | Actual real working carrier; unrestricted real fast angle. |
| `hc-id` | `p11_preimage_workingDom` (L120) | PASS | Exact set equality for positive strip width; norm preserved by real inclusion. |
| `hc-lat` | `p11RealDom_shift` (L134) | PASS | Fast shifts preserve the real domain, including slow coordinates. |
| `hc-id` | `P11HoloData.fast_close` (L142) | PASS | Rescaling gives rC/π and strict containment in both t2 and t1 balls. |
| `hc-id` | `P11HoloData.chartInput_eq'` (L170) | PASS | Inherited real/complex derivative identification on the t2 ball; rho equality only. |
| `hc-id` | `P11HoloData.chartInput_eq` (L177) | PASS | Same identification from the working action bound. |
| `hc-id` | `P11HoloData.R_row_bound` (L183) | PASS | Uses the inherited complex row-sum bound and rho_real; no isometry in max norm assumed. |
| `hc-id` | `P11HoloData.R_mulVec_bound` (L198) | PASS | Correct max-norm row-sum estimate, with factor Brho. |
| `hc-id` | `p11_noCollision_of_circularTube` (L211) | PASS | Physical axis separation and zeta give literal NoCollision. |
| `hc-id` | `P11HoloData.chartInput_mem` (L221) | PASS | Forward-tube action and Gamma bounds; exports both product-domain and circular-tube membership. |
| `hc-id` | `P11HoloData.fast_chartInput` (L287) | PASS | The inverse lift preserves the scaled fast action. |
| `hc-id` | `P11HoloData.frameBall` (L301) | PASS | Literal open action ball of the inherited real frame. |
| `hc-id` | `P11HoloData.isOpen_frameBall` (L304) | PASS | Standard open ball. |
| `hc-id` | `P11HoloData.fast_scale_mem` (L307) | PASS | Actual fast action belongs to liftDomain frameBall. |
| `hc-id` | `P11HoloData.liftInv_facts` (L316) | PASS | Analyticity and symplecticity from the existing lift theorem, analytic frame and SO property. |
| `hc-lat` | `P11HoloData.liftInv_isSO` (L325) | PASS | Inherited SO property on the entire frame ball. |
| `hc-id` | `P11HoloData.chart_eventuallyEq` (L329) | PASS | Equality on an open t2 neighborhood, sufficient for derivatives and analytic germs. |
| `hc-id` | `p11_kappa_pos` (L353) | PASS | Source physical positivity G*m0. |
| `hc-id` | `P11HoloData.chartInput_dom` (L357) | PASS | Literal inverse-lift image belongs to poincareProdDom. |
| `hc-id` | `P11HoloData.chart_analyticAt` (L365) | PASS | Analytic composition on the full real working domain. |
| `hc-id` | `P11HoloData.chart_symplectic` (L379) | PASS | Two chain-rule compositions, multiplier 1 throughout, with all domain inclusions supplied. |
| `hc-lat` | `P11HoloData.chart_lattice` (L408) | PASS | Q1 with zero physical shift, using equivariance of liftInv and product-chart periodicity. |
| `hc-lat` | `P11HoloData.chart_injective` (L420) | PASS | Q2 with the correct direction z-prime = shifted z; lift injectivity uses the SO frame ball. |
| `hc-id / P2f` | `P11HoloData.chart_energy` (L440) | PASS WITH NOTES | Conditional energy helper: hF remains explicit, as authorized by the split ruling. |
| `hc-id / hc-lat` | `P11HoloData.chart_spec` (L468) | PASS WITH NOTES | Exact signed final conjunct, conditional on data identifications, radius and P2f hF. |

## Definition classification

All four definitions are intended objects on their whole carriers:

- L43 `p11FastScaleL`: explicit global real linear map, `(theta,x;J,y)` to `(2π theta,x;J/(2π),y)`.
- L56 `p11FastScale`: the continuous linear realization, no modified values.
- L117 `p11RealDom`: precisely the three strict max-norm inequalities for the real working domain; positive strip width is correctly required for the complex-preimage equality.
- L301 `P11HoloData.frameBall`: the actual inherited real-frame action ball of radius t1.

No new structure, bundled proof premise, choice, fallback, instance, root declaration or ambient norm is introduced. Definitions are exposed by the file's `@[expose] public noncomputable section`.

## Notes and suspected defects

**N1 — P2f radius obligation; inaccurate handoff implication.** Handoff L37 says `(Brho*rz)^2 ≤ δ` is “implied by `rz <= min{1, delta/(8 Brho)}`”. That scalar implication alone is false: δ=128, Brho=16, rz=1 satisfies the displayed linear bound but gives 256 > 128. There is no upper normalization of δ in the imported `forward_tube` contract that justifies this implication. The Lean theorem correctly assumes the square bound explicitly (HoloChart L223, L471), and does not use the false implication. Handoff L57–58 correctly adds the sufficient condition `Brho*rz ≤ min(1, δ/8)`. A further positive shrink, e.g. `rz ≤ min(1,δ)/(8*Brho)` with Brho≥1 and δ>0, supplies this sufficient condition and the square bound. P2f must actually prove its chosen rz meets the explicit hypothesis; this report does not certify that unimplemented assembly. This is a handoff clarification, not a refutation of the source, the signed chart clauses, or P2d's proofs.

**N2 — split closure.** Keep hF unpaid at P2f, as ruled; no finding is charged to P2d for that reassigned identity. No frozen anchor is a seal candidate from this helper-only package.

No suspected pinned-paper erratum, frozen-statement defect, hidden source premise or additional implementation deviation found. The accepted design audits' broader open interfaces remain outside this slice.

## Independent checks

All Lean/Lake-related commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`. No resource override, clean, cache update, source repair, root regeneration, git mutation or provider import was performed. Temporary probes were confined to `.lake/abi-scratch/` and removed after checking.

### Targeted compile gate — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap2d KAM.Planetary.Preparation.HoloChart
```

Output begins `[inp-gate] slot 1 acquired 21:59:08 for KAM.Planetary.Preparation.HoloChart` and ends `Build completed successfully (9281 jobs).` Lake replayed upstream unused-variable/simp/deprecation warnings; no warning or error was reported in HoloChart. This independent gate succeeded at default heartbeats.

### Signed-conjunct application and all theorem axioms — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP2dAudit.lean
```

The final probe includes the independent signature-derived chart target and all 29 `#print axioms` commands. Two earlier auditor probe runs failed to parse the extracted multiline `let` target (expected semicolon/line break); adding an explicit `;` after the let binding fixed the scratch formatting. These were probe-generation syntax errors, not package elaboration failures or heartbeat signals. The successful final run has exactly the following output and no warnings/errors:

```text
'KAM.Planetary.p11FastScale_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fast_snd_p11FastScale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastScale_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastScale_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastScale_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11FastScale_isSymplecticOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_preimage_workingDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RealDom_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.fast_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chartInput_eq'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chartInput_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.R_row_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.R_mulVec_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_noCollision_of_circularTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chartInput_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.fast_chartInput' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.isOpen_frameBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.fast_scale_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.liftInv_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.liftInv_isSO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_kappa_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chartInput_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.P11HoloData.chart_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — PASS, exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.HoloChart
```

Exact output:

```text
replaying KAM.Planetary.Preparation.HoloChart
```

One invocation covers the entire in-scope lemma module; there is no separate provider module.

### Static/import/name checks — PASS

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty diff, exit 0; Git emits only the multiple-merge-base warning recorded above.
- `git diff --check inp...HEAD` and `git diff --check`: exit 0, no whitespace findings.
- HoloChart has 503 total lines; maximum Unicode line length is 99. Its copyright, module header, public imports, module docstring, public exposed section and namespace structure satisfy the module rules.
- Explicit forbidden-token/override scan of HoloChart: no matches for sorry, admit, axiom, unsafe, opaque, EuclideanSpace or set_option.
- Declaration short-name scan against every other KAM source: no reused declared short name. Independent declaration scan against Mathlib: no reused short name. All additions are under KAM.Planetary or its P11HoloData namespace; no root shadow or new instance.
- Traversed all 235 KAM modules in the import closure: no provider and no frozen theorem import. All 64 imported frozen modules are definitions, listed in the manifest as SEALED; no DRAFT_SORRY anchor is imported. The manifest's sealed-definition state is independently enforced by the lint/ABI checks below.

### Repository lint — PASS WITH EXPECTED EXCEPTION, exit 1

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (986 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the expressly permitted generated-root staleness. Module validation, frozen-anchor guard and all 144 frozen ABI hashes passed. KAM.lean was not regenerated or edited.

### Final artifact and worktree check

The report is written at `/root/code/KAM-inp-p11ap2d/docs/tracks/P/audits/P11A-P2d-audit-1.md`. All 33 declaration rows and all 29 axiom receipts are present. Audited source/design/signature hashes were rechecked unchanged after verification. The two auditor scratch files were deleted. Final tracked diff is empty; status shows only this new report and the handoff that was already untracked on arrival. No other repository artifact was edited. Final report whitespace check: `git diff --no-index --check /dev/null docs/tracks/P/audits/P11A-P2d-audit-1.md`, exit 0, no output.
