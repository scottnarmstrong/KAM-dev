# GAP-P5b independent audit 1

Overall verdict: **FAIL for literal graph closure**. The six exported theorems are kernel-checked and have acceptable axioms, but `bpP:p5:torus-conv` and `stepP:p5:lo-lost` do not export their full literal contracts. This is a statement-completeness finding, not a refutation of the propositions actually proved.

Audited 2026-10-29 in `/root/code/KAM-inp-gp5b`, HEAD `3372c73a2e24218e73c31fe7986c743c9239fd43`, against `inp` at `9208f71fad9c557fdee5db7c9a1b7bd222094650`, using the full `git diff inp...HEAD`. The entire diff consists of the two new modules, 106 and 284 lines respectively. The pre-existing untracked handoff was read and left untouched. Only this report and temporary worktree-local audit scratch were written.

Scope and authority: read AGENTS.md, PLAN, DECISIONS, the package audit brief, the handoff including AUDIT FOCUS and its overnight ruling, GAP-PLAN-P's GAP-P5b section, P45 design, track-P statement, and all nine named NODE records and their cited blueprint lines. The user's exact report destination overrides the generic brief's MAIN-worktree destination. The package is an UNSIGNED graph-gap leaf package, with no new provider or frozen anchor to seal. Provider/frozen type equality and copied seal-body probes are therefore not applicable. No SIGNED declaration is introduced in these modules; the inherited P45 signatures are not new signatures for these six exports.

## Node and declaration verdicts

Names below are in `KAM.Planetary`; module paths are under `KAM/Planetary/PGAssembly/`.

| Node | Declaration / locator | Verdict | Comparison with source contract |
|---|---|---|---|
| `stepP:p5:lo-range` | inherited `location`, `Chart.lean:109` | PASS, already closed / skipped | NODE at DEPGRAPH:9726 explicitly says PROVED under `location`. Blueprint p5:245 is the range argument; the inherited proof's `hdom` constructs the fast neighbourhood and slow interval bounds. No new wrapper is required under the explicit skip ruling. |
| `stepP:p5:lo-act` | inherited `location`, `Chart.lean:109` | PASS, already closed / skipped | NODE at DEPGRAPH:9755 is PROVED. Blueprint p5:246; inherited proof combines the fast displacement and distance bounds with `chart_dyn`, then proves membership in V. No new source premise is introduced by this package. |
| `stepP:p5:lo-disc` | inherited `location`, `Chart.lean:109` | PASS, already closed / skipped | NODE at DEPGRAPH:9787 is PROVED. Blueprint p5:247; inherited `chart_radial_margin` and `chart_disc_aux` give the needed strict disc inclusion. This audit accepts the recorded closure under the skip ruling; it does not newly certify that the inherited proof exports the displayed intermediate 3/2-margin inequality. |
| `bpP:p5:kset`, relative-closedness / sigma-compactness slice | `pgD0_relClosed`, `LocationNodes.lean:29` | PASS WITH NOTES | DEPGRAPH:9818; blueprint p5:250–254. Exactly exports `pgD0 = pgActionDomain ∩ C` for a closed C, and sigma-compactness, from data and admissibility. No dependency output is assumed. This is the explicitly assigned slice, not a new export of the entire definition node. |
| `stepP:p5:tc-freq` | `tc_freq_node`, `LocationNodes.lean:60` | PASS WITH NOTES | DEPGRAPH:9994; blueprint p5:263. Supplies both max-norm bounds and the previously missing single-scale Diophantine conclusion. Data precede the positive Cw witness, which precedes r, mu, admissibility and J. This matches GAP-PLAN-P's expressly existential tc-freq export. The displayed fast/slow formula is encoded by the body of `freq` in `PGMeasure/Setting.lean:43`, rather than repeated as equality conjuncts. See the separate exact-constant failure for torus-conv. |
| `bpP:p5:torus-conv` | `torus_conv_node`, `LocationNodes.lean:84` | **FAIL** | DEPGRAPH:9851; blueprint p5:256–258. All qualitative torus, Diophantine, exponent, range and uniformity clauses are present, but the source's specified Cw is replaced by an unconstrained existential constant. Neither statement nor proof identifies it with, or bounds it by, the displayed source value. |
| `stepP:p5:lo-bad` | `lo_bad_ratio`, `LowerNodes.lean:108` | PASS | DEPGRAPH:10430; blueprint p5:296. Exact relative-loss ratio, with the source sum `(A + Cdio Cgamma)/meas V + 6 b k1`, and `l2 = r²/2`. Source data and admissibility suffice; collar, Diophantine loss and shell estimates are proved or called inside the proof. Finite positive volume and denominator positivity are justified before real division. |
| `stepP:p5:lo-lost` | `lo_lost_budget`, `LowerNodes.lean:173` | **FAIL** for full node; PASS for displayed lost-tori chain | DEPGRAPH:10462; blueprint p5:297. Correctly exports the lost-tori estimate, `meas D ≤ meas F'`, and the resulting F' estimate in angle/action order. It does not add the bad-action part to establish the claim, as required by SOURCE_CONCLUSION and the package's complement-bound item. The proof never calls `lo_bad_ratio` or assembles that final bound. |
| `stepP:p4:dc-prod` | `dc_prod_node`, `LowerNodes.lean:261` | PASS | DEPGRAPH:7877; blueprint p4:151–162. Exact product neighbourhood equality and inclusion in V times the positive orthant. `l1 < l2` is a source standing assumption at p4:151, not an invented premise. Openness, boundedness and collar data are the standing p4 data; the collar conclusion is constructed internally. |

No frozen anchor is newly established by GAP-P5b. In particular, this verdict does not reopen or independently re-audit the inherited sealed P-G provider. The package is not ready to mark all its assigned graph conclusions closed.

## Exact findings and required closure

1. **Torus-conv changes a specified constant.** Blueprint `p5-pg-assembly.tex:257` says: `C_w := (M_omega + A_N)/(2 pi) + 1`, with `M_omega := sup over closure V of |omega-bar_0|`. `LocationNodes.lean:84` instead starts `∃ Cw : ℝ, 0 < Cw ∧ ...`. Its proof obtains that witness from `tc_freq_node`, hence `frequency_bounds`. The actual witness in `FamilyFreq.lean:38` is `(2*pi)⁻¹ * (M0 + jpBound + jetK2 + b*jetK4)`. Data-only dependence is correct, but it does not prove bounds with the specified constant. The older P45 design deliberately uses an existential Cw to meet the frozen headline's needs (design:559–570); that consumer sufficiency does not override AUDIT FOCUS's literal requirement for a new UNSIGNED export. Establish the source value, or obtain an explicit amendment of this graph contract. This audit makes neither change.

2. **Lo-lost omits the final addition.** DEPGRAPH:10471 concludes: “adding the bad-action part gives the claim”; blueprint p5:297 ends “Add.” The package definition also asks for “the complement bound.” `LowerNodes.lean:173–212` supplies only bounds for `Q \ L`, where Q is the D-cell; the combined `F' \ L` bound with the bad-action coefficient is absent. `Lower.lean:120` is an inherited lower-volume theorem for the physical cylinder, so its availability does not turn this new UNSIGNED statement into the literal full node export. Export the combined complement estimate under data and admissibility, constructing its dependencies inside. The lost-tori chain already present needs no extra hypotheses.

3. **Indexing and kset scope notes.** The source uses omega in Omega-star; the exports use J in pgD0 and `w = (2*pi)⁻¹ • freq ... J`. This is a reparameterization, not an extra restriction: the inherited `pg_kam_dictionary` identifies the frequency pullback, and `Family.lean:74–85` constructs frequency-image membership and the inverse-action identity. The physical torus is the chosen joint KAM family, not an arbitrary torus assumed as input. The new closedness theorem certifies only the assigned last clause of kset. Existing `physicalTorus`, `pgFamily`, `kset`, `rawUnion` and the dictionary carry the other definitions; do not cite `pgD0_relClosed` alone as a full definition-node inventory.

## Definitions, hypotheses and proof inspection

There are **no new `def`, `abbrev` or `structure` declarations** in either audited module. Thus there are no new fallback or junk-value definitions to classify. Local `set` abbreviations in proofs name the actual volume, domain, cell, coefficient or maximum used in the estimates.

The inherited carriers used here were checked where needed: `Phase` is angle/action order; `realNbhd` uses an existential distance witness, including on empty sets; `innerCore` is the frontier-distance core; `actionShell` is a coordinatewise open box; `pgD0` is the two-scale frequency preimage within the action domain. `outputRepresentative = rawUnion ∩ {angle ∈ unitCube}` (`CellTransfer.lean:36`), so it is precisely the source L in the swapped coordinate order. The same permutation applies to the cells and product Lebesgue measure; there is no quotient-volume factor missing from the lost-tori estimate. The physical conversion's `(2*pi)^n` factor belongs to the inherited cell-transfer step, not this raw-cell estimate.

`PGData` (`PG/Setting.lean:46`) bundles the frozen source hypotheses, including actual analyticity, boundary, frequency-inverse and torsion data. It contains no assumed torus, measure conclusion or KAM output. The five admissibility inequalities are source smallness/positivity conditions. None of the new exports takes a proved dependency's output as a premise. In dc-prod, `hc` is the source boundary hypothesis, not the collar theorem's conclusion.

Private declarations checked in `LowerNodes.lean`: `lbn_volume_unitCube` (28), `lbn_core_bad` (33), `lbn_ell_pow` (82), `dcn_nbhd_Ioo` (215), `dcn_nbhd_shell` (241). These respectively prove unit-cell volume, collar/Diophantine core loss, shell Bernoulli estimate, scalar interval enlargement and finite-product enlargement. Their actual conclusions are appropriate; they introduce no public short-name collision. The ratio proof clips the core-volume lower bound with `max (... ) 0`, avoiding multiplication of an uncontrolled negative bound. The product proof uses interval nonemptiness from the source. No proof-soundness defect was found.

## Independent checks and output

All Lean-related commands were run sequentially with `LEAN_NUM_THREADS=1`. The build gate itself executes `nice -n 5 lake build`; the probe, kernel replay and lint were also run with `nice -n 5`. No clean, dependency update, cache fetch or generated-root edit was performed.

Build command:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp5b KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
[inp-gate] slot 2 acquired 02:10:58 for KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes
Build completed successfully (9402 jobs).
exit 0
```

The build replayed inherited unused-variable/unused-simp warnings. No target-module error or heartbeat failure occurred.

Probe command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP5bAudit.lean`, exit 0. The probe imported the two modules and ran `#print axioms` on every new public theorem:

```text
'KAM.Planetary.pgD0_relClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tc_freq_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torus_conv_node' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lo_bad_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lo_lost_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.dc_prod_node' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel command: `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.LocationNodes KAM.Planetary.PGAssembly.LowerNodes`, exit 0. Complete output:

```text
replaying KAM.Planetary.PGAssembly.LowerNodes
replaying KAM.Planetary.PGAssembly.LocationNodes
```

Lint command: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`, exit 1. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1202 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole lint failure is expressly permitted by the brief and handoff ruling; root regeneration belongs to the orchestrator. It is not a substantive package finding.

Additional checks:

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD`: empty, exit 0. Working-tree `git diff --check` also empty.
- Forbidden-token/resource-option scan of both target files: no matches for sorry, admit, axiom, unsafe, opaque, EuclideanSpace or set_option. All ambient coordinate types are finite function spaces.
- Source import traversal from both modules: 356 KAM modules; **no provider imports and no frozen theorem imports**, including transitively. Frozen definitions are allowed. No DRAFT_SORRY theorem is in that import closure.
- Both files have copyright, module, public imports, module docstring and public noncomputable section. File lengths 106 / 284 are below 1500; maximum line lengths 94 / 100 characters satisfy the focus's 100-character rule. The handoff's “Lines ≤ 100” is true as a line-width statement, not as a file-length statement.
- Declaration-name scan found no other theorem/def/abbrev/structure with any of the six new public short names. Namespace is `KAM.Planetary`; no harmful root shadow was introduced.
- Temporary probe and captured logs were removed after their results were transcribed here.

## Source defects, deviations and uncertainty

No new mathematical defect in a pinned external source was found. This audit checks the local graph/blueprint contracts, not a fresh PDF transcription. The two export deviations above must remain visible even though the frozen headline can consume the weaker existential frequency bound and an inherited lower-volume theorem.

The dc-prod NODE's abbreviated hypotheses omit `lambda1 < lambda2`; the cited blueprint p4:151 explicitly fixes `0 < lambda1 < lambda2`, so this is inherited source context and not a Lean deviation. No erratum is requested for that premise. Existing graph status remains untouched. Passing kernel replay and acceptable axioms certify the actual exported statements; they do not resolve the identified missing literal conclusions.
