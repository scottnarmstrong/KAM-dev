# GAP-P5b independent audit 2

Overall verdict: **FAIL for literal graph closure**. The round-2 `lo-lost` repair passes. The revised `torus_conv_node` still fails the source-constant contract: its existential `AN` is not certified as the `A_N` of `freq-data`. All seven public propositions actually exported pass elaboration, axiom inspection and kernel replay. This is a statement-fidelity failure, not a proof-soundness failure.

Audited 2026-10-29 in `/root/code/KAM-inp-gp5b`, HEAD `82e500448d2d9ce8849bd7332c0c961ace7d8019`, against `inp` observed initially at `d6fa120cc475a689316bdbf716406c2fcc856747`, using **the full `git diff inp...HEAD`**, merge base `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`. The diff contains two new Lean modules (124 and 389 lines), audit 1, and the handoff. The only repository edit made by this audit is this report; temporary probes/logs were confined to `.lake/abi-scratch/` and removed after transcription. The user's exact worktree-local destination overrides the generic brief's MAIN-worktree parenthetical.

Read: AGENTS.md, PLAN, DECISIONS, the package audit brief, the named handoff and AUDIT FOCUS, audit 1, the round-2 appendix in `.drafts/handoff-GAP-P5b.md`, GAP-PLAN-P's GAP-P5b section, the relevant P45 design/signatures, track-P statement and P-G frozen anchor/definitions, every NODE record in the handoff table and its cited blueprint lines. The code audit is confined to `KAM/Planetary/PGAssembly/LocationNodes.lean` and `LowerNodes.lean`; inherited declarations are inspected only to identify carriers, assumptions and dependencies. No graph or source text was changed.

## Per-node results

Names are in `KAM.Planetary`. Blueprint p5 means `blueprint-P/parts/p5-pg-assembly.tex`; p4 means `blueprint-P/parts/p4-pg-measure.tex`.

| Node | Declaration / locator | Verdict | Source comparison |
|---|---|---|---|
| `stepP:p5:lo-range` | inherited `location`, `Chart.lean:109` | PASS, already closed / skipped | DEPGRAPH:9726, p5:245. Recorded PROVED under location. Its internal `hdom` builds the fast neighbourhood and slow interval inclusion. Covered by the explicit skip ruling; no new wrapper required. |
| `stepP:p5:lo-act` | inherited `location`, `Chart.lean:109` | PASS, already closed / skipped | DEPGRAPH:9755, p5:246. Recorded PROVED. The proof combines the action displacement, triangle inequality and `chart_dyn` margin to obtain membership in V. |
| `stepP:p5:lo-disc` | inherited `location`, `Chart.lean:109` | PASS, already closed / skipped | DEPGRAPH:9787, p5:247. Recorded PROVED. Existing disc-location proof and margin lemmas discharge the cylinder conclusion. This accepts the inherited closure under the skip ruling, rather than newly claiming an export of every displayed intermediate square-root inequality. |
| `bpP:p5:kset`, assigned relative-closedness and sigma-compactness slice | `pgD0_relClosed`, `LocationNodes.lean:29` | PASS WITH NOTES | DEPGRAPH:9818, p5:250–254. Exports a closed C with `pgD0 = pgActionDomain ∩ C`, plus sigma-compactness. Only data and admissibility are premises; continuity and closedness are built inside. The rest of the definition node is inherited, outside this assigned export slice. |
| `stepP:p5:tc-freq` | `tc_freq_node`, `LocationNodes.lean:60` | PASS WITH NOTES | DEPGRAPH:9994, p5:263. Matches the package plan's expressly existential Cw export: data, then one positive Cw, then all r, mu and J. Contains both max-norm bounds and the single-scale Diophantine clause, with tau=n+1>n. The displayed fast/slow formulas unfold from `freq` (`PGMeasure/Setting.lean:43`). This does not establish the fixed source-constant identity required separately by torus-conv. |
| `bpP:p5:torus-conv` | `torus_conv_node`, `LocationNodes.lean:86` | **FAIL** | DEPGRAPH:9851, p5:256–258, direct `freq-data` edge at DEPGRAPH:9880. Qualitative torus, Diophantine, exponent, range, parameter uniformity and carriers are correct. The new `∃ AN, 1 ≤ AN` is independent of the established frequency-data witness: the source's A_N identity remains unpaid. See finding below. |
| `stepP:p5:lo-bad` | `lo_bad_ratio`, `LowerNodes.lean:108` | PASS | DEPGRAPH:10430, p5:296. Exact relative-loss ratio and source coefficient, with lambda2=r²/2. Finite positive denominator and core/shell losses are proved internally. |
| `stepP:p5:lo-lost` | `lo_lost_budget`, `LowerNodes.lean:173`; **new** `lo_lost_complement`, :218 | PASS WITH NOTES | DEPGRAPH:10462, p5:297. First theorem gives the lost-tori chain and `meas D ≤ meas F'`; second calls it and `lo_bad_ratio` internally and exports the combined `meas(F' \ L) ≤ C_* sqrt(r) meas F'` with the exact sum of coefficients. Together they close the assigned raw-cell step. The subsequent physical-cell transfer is inherited, not a new theorem in these two modules. |
| `stepP:p4:dc-prod` | `dc_prod_node`, `LowerNodes.lean:366` | PASS | DEPGRAPH:7877, p4:151–162. Exact product-neighbourhood equality and inclusion in V times the positive orthant. `l1 < l2` comes from the standing source assumption at p4:151. Collar output is constructed from source boundary data, not assumed. |

There is no new provider or frozen anchor in this package. Thus there is no anchor newly seal-ready, and provider/frozen type-equality and copied seal-body probes are **not applicable**. All seven new public exports are UNSIGNED; no signed interface is altered. The inherited P45 signature for existential `frequency_bounds` explains consumer sufficiency, but does not relax the literal contract of an UNSIGNED graph-node export.

## Remaining finding: A_N has been renamed, not attached

The exact obligation is at DEPGRAPH:9858 and blueprint p5:257:

> C_w := (M_omega + A_N)/(2 pi) + 1

The graph directly depends on `bpP:p5:freq-data` for **that A_N**. Blueprint p5:105 says the constructed polynomial, its first derivative and its second derivative are “bounded by A_N”; DEPGRAPH:8704–8706 records that same data-only witness and its quantifiers. In Lean, this is represented by `PGAnalyticSpec` (`FrequencyDefs.lean:61–94`), particularly its bounds at :87–89, obtained by `freq_data` (`FrequencyBounds.lean:104`) and selected as `(pgAnalytic d).AN` (:162, :168).

By contrast, `LocationNodes.lean:86–88` introduces a fresh existential AN constrained **only** by `1 ≤ AN`. The proof at :99–101 obtains an arbitrary uniform frequency bound Cw0 from `tc_freq_node`, then sets

```text
AN := max 1 (2*pi*Cw0)
```

The rest of the proof uses only nonnegativity of the supremum and this algebraic construction to dominate Cw0. It neither uses the frequency-data AN nor proves that its new witness bounds the polynomial/derivatives, or is at least a certified source witness. The formula with `sSup` is now displayed correctly, and AN is chosen before r,mu; those repairs are real, but they do not identify the source constant. Introducing a positive AN this way can repackage any existential Cw bound in the desired formula. It therefore remains weaker than the graph's identified-constant statement.

The round-2 handoff says “A_N has no named Lean constant” and calls this “the ... constant of bpP:p5:freq-data.” That is not justified by the theorem type or proof; `(pgAnalytic d).AN` is an existing selected constant. This finding does **not** assert that the numerical witness is too small or that the desired source bound is false. It identifies the missing formal connection. Discharge the bounds with the established source AN, or jointly certify an alternative AN as the source frequency-data witness, with consistent parameter choices. Do not add a dependency output as a new hypothesis. An explicit contract amendment would also require authority outside this audit.

No other literal-contract failure was found in the assigned slice. The previous missing bad-action addition is repaired: `lo_lost_complement` forms `F' \ L ⊆ (F' \ Q) ∪ (Q \ L)`, proves the finite-measure subtraction for `F' \ Q`, and adds the two source coefficients. No measure bound or torus existence is assumed as a premise.

## Definitions, assumptions and proof review

Neither audited module introduces a `def`, `abbrev` or `structure`. Definition classification is therefore empty; there are no new junk-value or fallback constructions. Proof-local `set` abbreviations name the actual cells, volumes and coefficients.

`PGData` (`PG/Setting.lean:46`) contains the source P-G binders, not a KAM output or measure conclusion. `admissible` (`Parameters.lean:71`) is the five source positivity/smallness inequalities. Export premises are data and admissibility, except dc-prod's explicit standing domain/collar data. None assumes a proved dependency's output.

Carriers checked: `Phase` is angle/action order; block projections are finite function spaces with Pi max norms; `pgD0` is the two-scale frequency pullback in the actual action domain; `outputRepresentative` (`CellTransfer.lean:36`) is the raw union intersected with the unit angle cell. Thus the lo-lost coordinate permutation does not lose a Jacobian factor. The `(2*pi)^n` physical conversion belongs to the inherited cell-transfer step. The J indexing represents omega in Omega-star: `pg_kam_dictionary` and `Family.lean:74–85` give image membership and the inverse-action identity. It does not introduce an extra restriction on the selected torus family.

Inspected all private helpers: `lbn_volume_unitCube` (:28), `lbn_core_bad` (:33), `lbn_ell_pow` (:82), `dcn_nbhd_Ioo` (:320), `dcn_nbhd_shell` (:346). They prove cell volume, collar/Diophantine loss, the shell Bernoulli bound, and real-neighbourhood identities. The ratio proof clips the lower core-volume estimate by max with zero before multiplication. The complement proof establishes measurability and finiteness before subtraction and proves coefficient positivity before converting real inequalities to ENNReal. No proof-soundness defect was found.

## Independent verification

All Lean/Lake invocations below were sequential, with `LEAN_NUM_THREADS=1`. No clean, cache fetch, dependency update, generated-root edit, protected-path edit or git mutation was performed. The compile gate runs `nice -n 5 lake build` internally.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp5b KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
[inp-gate] slot 1 acquired 02:28:36 for KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
Build completed successfully (9402 jobs).
exit 0
```

The build replayed inherited unused-variable/unused-simp warnings; the above is the gate and completion output, not a verbatim warning log. There was no target error or default-heartbeat failure.

Probe command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP5bAudit2.lean`, exit 0. Probe imports both audited modules and prints all seven new public theorem axioms. Complete output:

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

The sole lint failure is the expressly permitted stale generated root. Root regeneration belongs to the orchestrator at merge and is not a package finding.

Additional independent checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0. Working-tree `git diff --check`: empty, exit 0.
- Python recursive source-import traversal: 356 KAM modules; zero provider imports and zero frozen theorem imports. Thus no transitive DRAFT_SORRY theorem dependency; frozen definitions are permitted.
- Token scan of both complete target files: zero matches for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, `set_option`. No resource overrides.
- File sizes 124 / 389 lines; maximum Unicode line widths 94 / 100. Both satisfy the 1500-line cap and 100-character line rule. Both have copyright, `module`, public imports, module docstring and exposed public noncomputable section.
- Repository declaration-name search for all seven new public short names found exactly their definitions in these two modules, with no reused helper short name. All are in `KAM.Planetary`; no root shadow introduced.

## Errata, deviations and limits

No new suspected defect in a pinned external mathematical source was found. This is a local graph/blueprint fidelity audit, not a fresh verification of the external PDFs. The unsourced identification of AN in `torus_conv_node` and its docstring (:84–85) is the remaining package deviation. The round-1 handoff's frequency/complement descriptions are stale; its round-2 appendix correctly lists the new complement export but overstates the AN repair.

The dc-prod NODE abbreviates away `lambda1 < lambda2`; the cited blueprint p4:151 supplies it, so this is source context, not an added Lean premise or a new erratum. The source's literal intermediate location steps remain covered only by the explicit already-PROVED skip ruling. No status or frozen proof is sealed by this report. Package literal closure remains FAIL until the torus-conv source-constant connection is established.

Final reference check: `inp` advanced during this audit to `91bbf02db68cf8d79eb6addd803d10d8af52cc01`; HEAD stayed fixed. Re-running `git diff --stat inp...HEAD`, the merge-base query, protected-path diff and three-dot whitespace check gave the same four-file diff and merge base, with empty protected-path and whitespace output. No audited package content changed. Final `git status --short` lists only this untracked report.
