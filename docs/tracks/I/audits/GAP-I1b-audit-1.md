# GAP-I1b independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gi1b`.
Audited HEAD: `3bbffc1614817fee36ece86782ab83243eacfdba`.
Comparison: `git diff inp...HEAD`, with `inp` at
`74976f317ab6852d2a7222801accf8ce39ba0615` and merge base
`db305f13e101faf5499dada636f9038bc561cbb4`.

The shared `inp` ref advanced during the audit to
`4717d6b5449a6b370f166c1f2a9350e9fd99f0f9`. The final three-dot comparison was
rechecked: the merge base and the same five-file, 854-insertion patch are unchanged;
the protected-path comparison and whitespace check still pass.

## Verdict

**FAIL for complete literal GAP-I1b coverage: `stepI:p1:ea-defect` alone fails.**
The other 28 requested node exports pass. This is an interface completeness failure,
not an unsound proof or an additional-premise failure. All 29 proofs compile, have
only the permitted axioms, and pass kernel replay.

No frozen theorem anchor or provider is introduced, replaced, or sealed by this
package. The per-anchor seal test is therefore **not applicable**; this report does
not re-audit the already sealed I-G1 theorem. The five changed files are step
infrastructure. Their protected-path diff is empty.

## Controlling material and method

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the supplied
`docs/tracks/I/audits/GAP-I1b-handoff.md`, including its AUDIT FOCUS.
The user's exact worktree-local report path overrides the generic brief's main-worktree
output instruction.

Compared the complete five-file three-dot patch with the 29 corresponding NODE records
in `docs/graph/I/DEPGRAPH.md`, reading each record's SOURCE_HYPOTHESES,
SOURCE_QUANTIFIERS, SOURCE_CONCLUSION and cited blueprint text. Also read the Part 1
standing setting and parent statements in `blueprint-I/parts/p1-iso-linear.tex`,
`docs/tracks/I/statement.md`, the Part 1 design in
`docs/tracks/I/design/PART123-LEAN-DESIGN.md` (including Amendment D21), and the
GAP-I1b section of `/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md`.
Inspected the reused `SettingSrc`, `FullRange`, energy, frame, matrix and extended-row
definitions/proofs, and the frozen energy/extended-torsion/frame definitions and I-G1
anchor relevant to their interpretation.

All 29 exports are **UNSIGNED step declarations**: none occurs in the design's
Appendix A signatures. The older signed parent declarations are unchanged. There is
no new SIGNED declaration requiring a signature-file equality probe and no provider
requiring a frozen-type/seal-body probe. Literal graph/source fidelity is the applicable
test; agreement with the type of an existing parent alone would not discharge it.

No export assumes a dependency's proved output as a premise. Source error bounds,
Gram invertibility, the bordered system and the conditional averaged energy datum
are actual source premises, not substituted proof obligations. Constants keep their
source dependence. The table records weakened premise sets as stronger results.
Source binders remain universal, with local strip/scalar data in dependency order;
reordering independent implicit data and using curried conditional conclusions does
not change quantifier dependence. In particular `ea-size` retains the nested
`δ` then `δ'` losses, and perturbation constants are fixed before `K'` and its bound.

## Finding F1: missing first averaged bound in `ea-defect`

Graph: `docs/graph/I/DEPGRAPH.md:1996`, especially SOURCE_CONCLUSION at line 2005:
"bound on E^omega_lin by the suprema of D(H o K), eta^N, Omega_K, xi^L over the cube".
Blueprint: `blueprint-I/parts/p1-iso-linear.tex:292` and `:328`–`:334`.
The literal first estimate is

```text
|avg(D(H ∘ K) ξL)| ≤ sup_cube |D(H ∘ K)| · sup_cube |ξL|.
```

`KAM/Iso/Linear/FullRangeStepsEnergy.lean:99`–`:127` states the pointwise identities,
average splitting, the conditional energy consequence, a pointwise operator-norm
inequality, and the final averaged `n (Aη + |ω| AΩ) X` estimate. But lines 116–119
only say, at an individual cube point,

```text
|D(H ∘ K)(x) ξL(x)| ≤ |D(H ∘ K)(x)| X.
```

That is not the required bound on the norm of the average using a uniform derivative
bound. The final estimate in lines 120–127 supplies the second endpoint of the source
chain, but does not export its first endpoint. In particular it cannot preserve an
independently smaller bound `A` for `D(H ∘ K)` without another integral argument.

The omission is especially concrete because `energy_defect_src` in
`KAM/Iso/Linear/FullRange.lean` already exports the required cube-bound form:

```text
∀ A X, (∀ x ∈ cube, |D(H ∘ K)(x)| ≤ A) →
       (∀ x ∈ cube, |ξL(x)| ≤ X) →
       |avg(D(H ∘ K) ξL)| ≤ A X.
```

The new proof obtains this as `hbd` at line 128, then specializes it at line 134 to
`A = n (Aη + |ω| AΩ)` and discards the general averaged clause from its public type.
Thus the underlying mathematics is already established inside the imported parent;
the named unsigned step export still does not state its literal full conclusion,
as required explicitly by AUDIT FOCUS (b). Merely saying the parent proves it would
not satisfy that export requirement. Retain the general `∀ A X` averaged clause
alongside the final estimate (or the literal supremum chain); no new premise or new
analytic proof is needed. No implementation change was made in this audit.

## Per-node ledger

All declarations below have prefix `KAM.Iso.Linear.`. `DG` is the NODE line in
`docs/graph/I/DEPGRAPH.md`; `BP` is the cited line range in
`blueprint-I/parts/p1-iso-linear.tex`. Lean locators are in
`KAM/Iso/Linear/FullRangeSteps{Ext,Energy,Frame,Pert}.lean`.

| Node | DG / BP | Declaration and Lean locator | Verdict | Reason |
|---|---|---|---|---|
| eb-holo | 1175 / 130–146 | `step_eb_holo`, Ext:39 | PASS | N, T, Y, every bordered entry holomorphic; real-restriction continuity. Only needed standing data retained. |
| eb-holo-inverse | 1236 / 136–137 | `step_eb_holo_inverse`, Ext:58 | PASS | B, N, P holomorphic from hK and invertible G alone; stronger premise set. |
| eb-holo-field | 1266 / 139–140 | `step_eb_holo_field`, Ext:70 | PASS | A and DH along K holomorphic; drops unnecessary frame hypotheses. |
| eb-holo-torsion | 1297 / 142–143 | `step_eb_holo_torsion`, Ext:81 | PASS | All six regularity conclusions and literal bordMat entry formula. |
| eb-holo-conclude | 1329 / 145–146 | `step_eb_holo_conclude`, Ext:103 | PASS | Same full holomorphy/continuity conclusion as source. |
| eb-period | 1360 / 148–153 | `step_eb_period`, Ext:116 | PASS | Periodicity/reality of Y, N, T and DH along K; K premises are standing source data. |
| eb-average | 1390 / 155–160 | `step_eb_average`, Ext:144 | PASS | Entry integrability, entrywise frozen integral, reality, omega border and zero corner. |
| eb-bounds | 1421 / 162–166 | `step_eb_bounds`, Ext:169 | PASS | Both row-sum chain links and max bound; free local CT; no norm/carrier change. |
| lr-gradient | 1711 / 250–252 | `step_lr_gradient`, Ext:227 | PASS | Both signed gradient identities, for every z even outside D; stronger total algebraic statement. |
| lr-average | 1773 / 263–269 | `step_lr_average`, Ext:242 | PASS | Full (b)/(c): invariant row, pointwise/averaged border, correction and 2n² bound. |
| ea-chain | 1843 / 301–305 | `step_ea_chain`, Energy:38 | PASS | Composition regularity/chain rule, periodicity, reality, average and cube integrability. |
| ea-gradient | 1904 / 311–314 | `step_ea_gradient`, Energy:55 | PASS | Both vector identities; etaN is defined without an inverse, so no Gram premise needed. |
| ea-avg | 1935 / 316–319 | `step_ea_avg`, Energy:75 | PASS | All three zero averages; no additional premise. |
| ea-size | 1964 / 321–326 | `step_ea_size`, Energy:85 | PASS | Both energy/derivative bounds with exact losses and constants, δ before δ'. |
| ea-defect | 1996 / 328–334 | `step_ea_defect`, Energy:99 | FAIL | Missing averaged derivative-supremum estimate; see F1. All included conclusions are sound. |
| ec-derivative | 2061 / 351–353 | `step_ec_derivative`, Energy:141 | PASS | Centered holomorphic periodic u, average zero and Du omega = 0; realness not needed. |
| ec-unique | 2090 / 355–359 | `step_ec_unique`, Energy:160 | PASS | u vanishes for every admissible δ and on full strip; parent derivation is legitimate. |
| ec-pointwise | 2119 / 361–362 | `step_ec_pointwise`, Energy:174 | PASS | Constant energy, conditional E0 and actual sSup equality; strip nonemptiness proved. |
| rd-expand | 2453 / 510–514 | `step_rd_expand`, Frame:43 | PASS | Literal projected identity, including minus DK Delta omega with Delta omega = -xiomega omega. |
| rd-consequence | 2485 / 516–521 | `step_rd_consequence`, Frame:73 | PASS | Residual, norm bound, radius-one Neumann invertibility, inverse residual and equivalence. |
| geo-de | 2552 / 547–548 | `step_geo_de`, Frame:119 | PASS | Error regularity/bound and derivative/transpose estimates; no torsion assumption. |
| geo-red | 2583 / 549–559 | `step_geo_red`, Frame:134 | PASS | Both source estimates with exact coefficient and C_red. |
| geo-red-domega | 2613 / 552–556 | `step_geo_red_domega`, Frame:149 | PASS | Expanded/factored constants equal and directional defect estimate. |
| geo-red-ered | 2646 / 558–559 | `step_geo_red_ered`, Frame:159 | PASS | C_red = 2n(n+1)m² and bound on E_red. |
| geo-sym | 2679 / 561–562 | `step_geo_sym`, Frame:167 | PASS | Regularity, periodicity, zero average, C_Omega bound and m² comparison on larger strip. |
| pt-small | 2745 / 579–581 | `step_pt_small`, Pert:34 | PASS | Constant domination and all four smallness inequalities; d nonnegative derived at θ=0. |
| pt-domain | 2774 / 582–583 | `step_pt_domain`, Pert:58 | PASS | Both ball inclusions and both field-bound links; weaker local premises suffice. |
| pt-frame | 2803 / 584–585 | `step_pt_frame`, Pert:83 | PASS | Both L differences, both L bounds, Gram invertibility and both inverse bounds. |
| pt-torsion | 2835 / 586–589 | `step_pt_torsion`, Pert:134 | PASS | Three N estimates and both X_N/torsion differences on correct strips. |

## Disclosed deviations and completeness

1. **Extra K hypotheses: accepted.** Blueprint lines 31–38 explicitly require
   K "holomorphic, primary and real on reals on T_r, with K(T_r) subset D".
   These are exactly standing I5/I6. `eb-period`, `eb-average`, `ea-*`, and `ec-*`
   do not add hypotheses beyond the source setting. Some exports omit unused
   standing premises and are stronger. `SettingSrc` intentionally bundles the
   H/domain/frequency data only, leaving K/r data explicit.
2. **`lr-average` omits `lr-insert`: accepted.** Its own NODE requires last-row
   (b)/(c), not (a). Those are fully stated. `lr-insert` is not among the 29 nodes;
   its content exists separately in `LastRowAux.energyRow_eq_sub_etaL` and
   `sum_norm_energyRow_sub_le`. No missing (a) is charged to `lr-average`.
3. **Global det P premise in reduced (d): accepted.** Blueprint line 494 explicitly
   says "det P != 0 on T_{r'}". The new final implication matches that source,
   rather than assuming invertibility from det G. The new Neumann clause even
   proves P/Q invertibility at arbitrary θ under norm E_sym < 1. The inverse
   residual conclusion remains conditional on the bordered system, as required
   by (c); the zero-residual equivalence is unconditional in that system.
4. **Row-sum DH norm: accepted.** Blueprint lines 44–46 explicitly identify a
   one-row norm with the sum of absolute entries, the max-norm operator norm of
   DH. The code uses the complex phase-coordinate sum over `Fin n ⊕ Fin n`.
   `sum_norm_apply_le_opNorm` bounds it by the actual complex-linear operator
   norm, and the row-product estimate preserves the dimension factor exactly.
   It does not use the max norm of `energyRow` in place of its row sum.
5. **`ec-unique` via `energy_conservation_src`: accepted with graph note.** The
   parent is proved in `Energy.lean:221` directly using cohomological uniqueness
   and strip margins. It does not import a new step module. The new proof
   derives the requested substrip and full-strip vanishing and takes no parent
   conclusion as a hypothesis. There is no Lean dependency cycle. A source
   proof graph which lists the parent as using this step must not add the
   reverse parent-to-step Lean edge as if both were actual import dependencies.

The exact 29-node plan list matches 29 distinct new public theorem names. No node
was skipped. The two ea-average alternative route records are not extra requested
exports; the inherited proof uses exactness, and the unused gradient route need
not be separately exported. F1 prevents calling this a complete literal unsigned
export slice despite the underlying parent's stronger available bound.

Free sigma parameters in geometry/perturbation are legitimate: the inherited
`mSize_max_one` identity preserves every constant when positive standing sigma
data are built as `max sigma 1`. Positive r is already a source premise, not an
extra smallness assumption. Some perturbation exports drop `2δ < r` and unused
source premises, giving stronger statements (possibly empty target strips).

## Definition and totality classification

**No new def, abbrev, structure, class, instance or notation** occurs in any of
the five changed files. The facade contains imports only; the other four contain
the 29 theorems. There is no object whose new body could hide junk/fallback values.

Reused objects retain their literal carriers and signs: `SettingSrc` contains
source data, `AdmissibleNoTwist` contains A1–A4/A6 and no torsion-average field,
`energyRow = DH(K)N`, `bordMat = (T omega; Y 0)`, `energyAverage` and the extended
average integrate over the unit cube. P/Q and error objects are the existing
bilinear symplectic objects, not Hermitian substitutes. Gram inverses in analytic
frame assertions are guarded by unit determinants. `eb-bounds` and `lr-gradient`
are algebraic statements valid for their total definitions even without such
guards. Frozen energy averages are used with proved integrability. The new
`ec-pointwise` sSup equality explicitly reduces a nonempty image to a singleton;
it does not exploit the empty/unbounded sSup fallback. No new fallback is relied on.

## Independent checks

All audit-initiated Lean/Lake checks were serialized, with `LEAN_NUM_THREADS=1`
and `nice -n 5`. No library clean, cache fetch, package edit or root regeneration
was performed. Scratch files/logs were confined to `.lake/abi-scratch/` and
removed after recording their results.

### Build

```sh
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-gi1b KAM.Iso.Linear.FullRangeSteps
```

Exit 0, output:

```text
[inp-gate] slot 1 acquired 05:35:33 for KAM.Iso.Linear.FullRangeSteps
Build completed successfully (3210 jobs).
```

### Axiom probe

An untracked `GAP_I1b_Audit.lean` imported `KAM.Iso.Linear.FullRangeSteps` and
contained one `#print axioms KAM.Iso.Linear.<name>` for every theorem in the table.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean \
  .lake/abi-scratch/GAP_I1b_Audit.lean
```

Exit 0. Exact output is appended below. Every export uses exactly
`[propext, Classical.choice, Quot.sound]`; none uses `sorryAx`.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Iso.Linear.FullRangeSteps \
  KAM.Iso.Linear.FullRangeStepsExt \
  KAM.Iso.Linear.FullRangeStepsEnergy \
  KAM.Iso.Linear.FullRangeStepsFrame \
  KAM.Iso.Linear.FullRangeStepsPert
```

Exit 0, exact output:

```text
replaying KAM.Iso.Linear.FullRangeStepsPert
replaying KAM.Iso.Linear.FullRangeStepsFrame
replaying KAM.Iso.Linear.FullRangeStepsEnergy
replaying KAM.Iso.Linear.FullRangeStepsExt
replaying KAM.Iso.Linear.FullRangeSteps
```

### Lint, import quarantine, names and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1274 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is exactly the permitted generated-root exception. There is no other lint
failure. The root was left untouched as required.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0 with empty output. All five files have copyright, `module`, public
imports, a module docstring and `public section`. Counts/max Unicode line lengths:

| File suffix | Lines | Maximum line length |
|---|---:|---:|
| FullRangeSteps | 20 | 93 |
| FullRangeStepsExt | 267 | 99 |
| FullRangeStepsEnergy | 194 | 100 |
| FullRangeStepsFrame | 187 | 97 |
| FullRangeStepsPert | 186 | 100 |

A recursive traversal of the five modules' KAM imports reached 81 KAM modules,
including **zero provider modules and zero frozen theorem modules**. Hence no
DRAFT_SORRY anchor is imported and no imported theorem-anchor state exception is
needed. All new theorem short names were searched against every other KAM Lean
file: zero collisions and zero production consumers outside the new modules.
Every new theorem is under `KAM.Iso.Linear`; no root shadow, HELPER-name reuse,
EuclideanSpace, forbidden proof escape or resource override was found.

## Errata, deviations and limits

No new suspected defect in a pinned mathematical source or frozen statement was
found. F1 is a package omission relative to the literal blueprint, not a source
erratum. Existing HL19 sign deviations were not changed. The stale graph
LEAN_STATUS/LEAN_NOTE fields remain integration work; this audit edits no graph.
The ec-unique proof-route direction should be represented honestly as discussed
above. The handoff's Frame line count says 186; actual audited HEAD has 187,
well below the cap. No default-heartbeat design failure occurred.

Only this report was added outside scratch. The already untracked handoff was
left untouched. No state-changing git operation or source repair was performed.

## Exact axiom output

```text
'KAM.Iso.Linear.step_ea_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ec_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ec_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ec_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_holo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_holo_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_holo_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_holo_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_holo_conclude' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_eb_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_lr_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_lr_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_rd_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_rd_consequence' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_geo_de' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_geo_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_geo_red_domega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_geo_red_ered' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_geo_sym' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_pt_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_pt_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_pt_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_pt_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
```
