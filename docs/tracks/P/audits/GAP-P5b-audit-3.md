# GAP-P5b independent audit 3

Overall verdict: **PASS WITH NOTES for the assigned graph-gap slice**. Audit 2's remaining torus-conv constant finding is repaired: the export now certifies its frequency-data witness and proves bounds using that witness's A_N. No substantive statement or proof failure was found. The notes concern the explicitly scoped kset export, the already-PROVED location steps, one inaccurate docstring, and the permitted stale generated root. No frozen anchor is newly sealed by this package; provider/frozen type equality and seal-body probes are not applicable.

Audited 2026-10-29 in `/root/code/KAM-inp-gp5b`, HEAD `1fe83b6adec15206876307fe684248582e93f77d`, against `inp` observed at `65cc4db4e4401d6f0ae79281801299241e87b601`; merge base `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`. Reviewed the full `git diff inp...HEAD`: two new Lean files (238 and 389 lines), audits 1 and 2, and the handoff, five files / 885 inserted lines. The user's exact absolute report destination overrides the generic brief's MAIN-worktree parenthetical.

Read AGENTS.md, PLAN, DECISIONS, the audit brief, handoff/AUDIT FOCUS, both preceding audits, the round-3 appendix in `.drafts/handoff-GAP-P5b.md`, GAP-PLAN-P's package definition, relevant P45 node mappings and signature text, track-P statement, the frozen P-G anchor and pertinent definitions. Read every NODE record listed below, its SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION, and the cited blueprint lines. Code-audit scope is only `LocationNodes.lean` and `LowerNodes.lean`; inherited code was read to resolve carriers, source assumptions, constants, and dependency interfaces. Only this report was edited in the repository. Probes/logs were confined to `.lake/abi-scratch/` and removed after transcription.

## Per-node and declaration results

All names below are in `KAM.Planetary`; p5/p4 mean `blueprint-P/parts/p5-pg-assembly.tex` / `p4-pg-measure.tex`.

| Node | Declaration / locator | Verdict | Literal contract and quantifiers |
|---|---|---|---|
| `stepP:p5:lo-range` | inherited `location`, `Chart.lean:109` | PASS, already closed/skipped | DEPGRAPH:9726, p5:245. Recorded PROVED under location, covered by the explicit skip ruling. Internal `hdom` proves the fast neighbourhood and slow interval inclusion. No new wrapper is required by the controlling ruling. |
| `stepP:p5:lo-act` | inherited `location`, `Chart.lean:109` | PASS, already closed/skipped | DEPGRAPH:9755, p5:246. Recorded PROVED. The action displacement and triangle inequality yield the collar inclusion in V. Accepted under the same skip ruling. |
| `stepP:p5:lo-disc` | inherited `location`, `Chart.lean:109` | PASS, already closed/skipped | DEPGRAPH:9787, p5:247. Recorded PROVED. Radial-margin/disc estimates establish cylinder membership. This audit accepts the inherited closure under the skip ruling; it does not claim a new public export of each displayed intermediate square-root inequality. |
| `bpP:p5:kset`, relative closedness and sigma-compactness slice | `pgD0_relClosed`, `LocationNodes.lean:29` | PASS WITH NOTES | DEPGRAPH:9818, p5:250–254. Exact closed-trace equality and sigma-compactness from data and admissibility. Continuity/closedness are built inside. The broader definition node uses inherited pgD0, physicalTorus, pgFamily, kset and rawUnion; this theorem alone is not an inventory of the full definition node. |
| `stepP:p5:tc-freq` | `tc_freq_node`, `LocationNodes.lean:60` | PASS WITH NOTES | DEPGRAPH:9994, p5:263. Matches the package's explicit existential-Cw contract: data, then a positive Cw, then all r,mu and J in D0. Both max-norm bounds, the single-scale Diophantine clause, and tau=n+1>n are present. The fast/slow formulas unfold from freq (`PGMeasure/Setting.lean:43`). The source's specified common Cw is supplied by torus_conv_node; see documentation note below. |
| `bpP:p5:torus-conv` | `torus_conv_node`, `LocationNodes.lean:86` | PASS | DEPGRAPH:9851, p5:256–258; frequency-data dependency DEPGRAPH:9880 / p5:104–108. Certified data-only p, then the defining Cw equality, then all r,mu,h,J. Exports the frozen cylinder torus, single-scale Diophantine condition, exponent, both bounds with precisely `(M_omega+p.AN)/(2*pi)+1`, and range inclusion. No dependency output is an input premise. |
| `stepP:p5:lo-bad` | `lo_bad_ratio`, `LowerNodes.lean:108` | PASS | DEPGRAPH:10430, p5:296. Exact ratio and coefficient `(A+Cdio*Cgamma)/meas V + 6*b*k1`, lambda2=r²/2. Data/admissibility only. Core, shell, positivity and finite denominator obligations are proved internally. |
| `stepP:p5:lo-lost`, displayed chain | `lo_lost_budget`, `LowerNodes.lean:173` | PASS | DEPGRAPH:10462, p5:297. Lost-tori estimate with meas D, comparison meas D≤meas F', and F' bound, all in the common angle/action coordinate order. |
| `stepP:p5:lo-lost`, final addition | `lo_lost_complement`, `LowerNodes.lean:218` | PASS WITH NOTES | Same NODE and source line. Calls lo_lost_budget and lo_bad_ratio inside, then exports `volume(F' \ L) ≤ ofReal(C_* sqrt r)*volume F'` with the exact sum of source coefficients. This closes the assigned raw-cell complement step. Physical-cell transfer is inherited, outside these exports. |
| `stepP:p4:dc-prod` | `dc_prod_node`, `LowerNodes.lean:366` | PASS | DEPGRAPH:7877, p4:151–162. Exact real product-neighbourhood equality and inclusion in V times positive orthant. The source fixes lambda1<lambda2 at p4:151. The boundary hypothesis is standing source data; collar output is proved internally. |

All seven public theorems are UNSIGNED exports; there is no new SIGNED declaration and no altered signed interface. The relevant inherited `frequency_bounds` signature is explicitly existential in P45-LEAN-DESIGN:1949, and its consumer discussion at :568–572 chooses Cw before r,mu. The package plan:454–465 assigns these two modules exactly the exports audited above. The stronger torus-conv wrapper now also pays the literal specified-constant obligation; consumer sufficiency alone was not used to waive it. The slice is complete under the handoff's already-PROVED skip ruling and its expressly limited kset assignment.

## Independent review of the round-3 repair

The previous failure was an uncertified fresh AN chosen from an arbitrary Cw bound. The new theorem type instead says `∃ p : PGAnalytic, PGAnalyticSpec d p ∧ 1 ≤ p.AN ∧ ...`. The proof supplies **pgAnalytic d** itself (:105), obtained from freq_data (`FrequencyBounds.lean:104,162,168`). Thus the proof uses the same selected frequency-data constants as the rest of the parameter construction; it does not inflate AN independently or change rStar. PGAnalyticSpec is a conclusion here, never a premise supplied by the caller.

The analytic specification's polynomial/first-/second-derivative bounds (`FrequencyDefs.lean:87–89`) certify the actual jetPolynomial. At :113–133 the proof places the real action point in analyticBoundDomain, using the source shell and r<1. Its first derivative L has norm ≤AN. Evaluating L on embedded coordinate unit vectors gives both block-gradient bounds ≤AN (:148–153). complexFrequency_eq and complexFrequency_realSlice identify these with the original frequency, rather than a replacement function (:134–137).

At :154–180 the proof derives `BddAbove` for the image of the fast-frequency norm on closure V from the analytic extension's H0 derivative bound. It uses agreement on a neighbourhood to identify real and complex derivatives even at boundary points; no compactness or continuity assumption is silently added. The supremum therefore bounds the actual fast frequency (:178–182). With 0<mu<1, the unscaled fast block is bounded by M_omega+AN (:184–203), and the slow block by mu*AN (:204–215). Division by 2*pi gives the specified Cw bounds. The extra +1 supplies slack; M_omega≥0 and AN≥1 are justified.

The defining Cw equality is harmless typing data: instantiate Cw with its displayed expression and use rfl. It is neither a free larger constant nor a missing inequality. All data-only witnesses precede r,mu. J indexing is the source frequency reparameterization: pg_kam_dictionary identifies D0 as the frequency pullback, and `Family.lean:74–85` constructs frequency-image membership and the inverse-action identity. Every omega in Omega-star has the corresponding J; the chosen physicalTorus is the inherited jointly constructed family. No arbitrary torus or proved dependency output is assumed.

## Definitions, hypotheses, and proof hygiene

Neither audited module adds any def, abbrev or structure. Definition classification is empty; there are no new totalized fallback objects. Local `set` abbreviations denote the actual volumes, cells, derivative and coefficients being estimated.

PGData (`PG/Setting.lean:46`) contains precisely source typing/geometric/analytic premises, checked against the frozen P-G binders. It contains no KAM or measure conclusion. admissible (`Parameters.lean:71`) is the five source positivity/smallness inequalities. dc-prod's hc is the source boundary-collar hypothesis, not the collar theorem's output. Its unused positive-t / t<d arguments are source assumptions, not new obligations.

Phase has angle/action order; block spaces use Pi max norms on finite function spaces. outputRepresentative (`CellTransfer.lean:36`) is rawUnion intersected with the unit angle cell, matching source L after the common coordinate permutation. Product Lebesgue measure is preserved by that permutation. The physical factor `(2*pi)^n` belongs to inherited cell-transfer, not the raw-cell lost-tori bound.

Private helpers reviewed: lbn_volume_unitCube (:28), lbn_core_bad (:33), lbn_ell_pow (:82), dcn_nbhd_Ioo (:320), dcn_nbhd_shell (:346). They prove unit volume, collar/Diophantine core loss, Bernoulli shell bound, and interval/product neighbourhood identities. The ratio proof clips its core lower bound by max with zero before multiplying. The complement proof establishes measurability/finiteness before measure subtraction, proves `F' \ L ⊆ (F' \ Q) ∪ (Q \ L)`, and adds the bad-action and lost-tori bounds. No soundness defect or conclusion-shaped premise was found.

## Independent checks

All Lean/Lake checks initiated by this audit were sequential with LEAN_NUM_THREADS=1; the compile gate executes nice -n 5 lake build internally. No clean, dependency update, cache fetch, frozen/manifest edit, generated-root edit or git mutation was performed.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp5b KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
[inp-gate] slot 1 acquired 02:52:52 for KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
Build completed successfully (9402 jobs).
exit 0
```

The build emitted inherited unused-variable, unused-simp and deprecation warnings; this is the gate/completion output, not a verbatim warning transcript. No target error or heartbeat-budget failure occurred.

Probe: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP5bAudit3.lean`, exit 0. Imports both target modules, prints all seven public theorem axioms and checks the elaborated torus-conv type. Complete axiom output:

```text
'KAM.Planetary.pgD0_relClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tc_freq_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torus_conv_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lo_bad_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lo_lost_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lo_lost_complement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.dc_prod_node' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
replaying KAM.Planetary.PGAssembly.LowerNodes
replaying KAM.Planetary.PGAssembly.LocationNodes
exit 0
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1202 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole lint failure is the expressly permitted generated-root staleness. The module, frozen-anchor and ABI checks pass. Root regeneration belongs to the orchestrator at merge and is not a package finding.

Additional source checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0.
- Python recursive traversal of source import lines: 356 KAM modules; no provider or frozen theorem module anywhere in the closure. Thus no DRAFT_SORRY import. Frozen definition imports are permitted.
- Full target-file token scan: zero sorry/admit/axiom/unsafe/opaque/EuclideanSpace/set_option matches; no resource overrides.
- File lengths: 238 / 389 lines; maximum Unicode line widths: 99 / 100. Both meet 1500-line and 100-character limits and have copyright, module, public imports, module docstring, public section.
- Repository declaration-name search found each of the seven public short names only at its own declaration. Namespace KAM.Planetary throughout; no reused public helper short name or harmful root shadow.

## Source defects, deviations and limitations

No new suspected defect in a pinned external source was found; this audit compares local graph/blueprint contracts, not external PDF transcriptions. No mathematical deviation was introduced by this report. The old handoff's claimed existential torus-conv constant and missing complement description are stale; the round-3 and round-2 appendices respectively supersede them.

Documentation defect: `LocationNodes.lean:57` says “w = omega_0(J)/2pi”. In the cited blueprint p5:251 and :257, omega_0 is **already** F_mu/(2pi), and w=omega. The actual theorem at :62–66 correctly uses `(2*pi)^(-1) • freq`; only the docstring has an extra period conversion. Correct the prose to w=omega_0(J) or w=F_mu(J)/(2pi). This is a nonblocking documentation note, not a theorem-type failure.

The dc-prod NODE abbreviates away lambda1<lambda2, while its cited standing blueprint context p4:151 supplies it; this is not an unsourced Lean premise. Graph status and references were not edited. This report certifies the assigned exports and explicit inherited skips only; it does not newly seal the inherited P-G theorem or certify every statement in its transitive source development.

Final reference recheck: inp advanced to `4d8a6848e381c8baaa9072e8d9867e3fc7a36f2a`; HEAD and the merge base remained unchanged. The full three-dot diff still has the same five files / 885 inserted lines; protected-path diff, three-dot whitespace check and working-tree `git diff --check` are empty.

Scratch probe and both captured logs were deleted after transcription. Final repository status contains only this untracked audit report.
