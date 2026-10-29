# GAP-I1b independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gi1b`.
Audited HEAD: `bf00abe3a75077f697dbf05b50e6c331675d0d7c`.
Compared **the complete `git diff inp...HEAD`**, with `inp` at
`c4eb8ee678c28f33132857abe6eb87447d248893` and merge base
`db305f13e101faf5499dada636f9038bc561cbb4`.
The patch adds five Lean files (892 lines), audit 1 and the handoff. The last
commit adds only `step_ea_defect_node` (38 lines).

## Verdict

**FAIL under the supplied AUDIT FOCUS's named-export contract:** the handoff's
`ea-defect` export is still `step_ea_defect`, and that declaration still omits
the first averaged estimate. The other 28 handoff-named exports pass.

**The mathematical omission has been repaired in the new public export
`step_ea_defect_node`: PASS.** All 29 requested node conclusions now have public
proofs available in the package if `ea-defect` is assigned to this new export.
There is no remaining analytic proof gap identified here. The outstanding failure
is the explicit requirement to check the declaration named by the supplied handoff,
not proof unsoundness, a missing source premise, or failure of the new bound.
Do not read this report as saying the added wrapper fails.

No frozen anchor or provider is added or changed. Per-anchor provider/type and
seal-body tests are **not applicable**; I-G1 is already sealed and is not re-audited
as a theorem here. With the new wrapper accepted as the node's designated export,
the infrastructure would merit **PASS WITH NOTES** (the permitted generated-root
lint exception and documentation/graph integration notes below). The current
handoff is not silently rewritten by this audit.

## Material and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the exact package audit brief
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff and
`GAP-I1b-audit-1.md`. The user's explicit absolute worktree-local output path
controls over the generic brief's main-worktree destination.

For each of the 29 handoff nodes, read the NODE's SOURCE_HYPOTHESES,
SOURCE_QUANTIFIERS, SOURCE_CONCLUSION and CONSTANT_SCOPE in
`docs/graph/I/DEPGRAPH.md`, and its cited `blueprint-I/parts/p1-iso-linear.tex` text.
Read the Part 1 standing setting, parent statements, track I statement, the Part
1–3 design including Appendix A and Amendment D21, and the GAP-I1b section of
`/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md:341`.
Inspected the actual new proofs and their reused SettingSrc, FullRange, Energy,
frame/perturbation and extended-row objects, plus the relevant frozen energy,
extended torsion, Gram/normal-frame definitions and I-G1 statement.

All **30 new public declarations are unsigned theorems**. None of their names
occurs in the design signature text. No new signed declaration or definition
needs a signature equality/body probe; the signed parents are unchanged. The
applicable gate is literal source fidelity, not equality with a parent's type.
The facade adds imports only.

## F1: original named export remains incomplete; replacement passes

The source is `blueprint-I/parts/p1-iso-linear.tex:292` and `:328–334`, and
`docs/graph/I/DEPGRAPH.md:1996` (SOURCE_CONCLUSION at `:2005`). It requires both
averaged estimates, starting with

```text
|avg(D(H ∘ K) ξL)| ≤ sup_cube |D(H ∘ K)| · sup_cube |ξL|.
```

The controlling focus says: "an UNSIGNED export named after a graph node must
state that node's literal conclusion". The handoff at line 33 still designates
`step_ea_defect`. Its statement in
`KAM/Iso/Linear/FullRangeStepsEnergy.lean:99–127` is byte-for-byte unchanged since
`3bbffc16` (independently compared). Lines 116–119 are a pointwise operator-norm
bound, whereas lines 120–127 give only the final averaged estimate with
`n (Aη + |ω| AΩ) X`. It still does not export the first averaged bound for arbitrary
uniform derivative bound `A`. This is the same precise interface failure as audit 1.

The added `step_ea_defect_node` at Energy:142–175 **does** export the missing
clause at lines 159–164:

```text
∀ A X, (∀ x ∈ cube, |D(H ∘ K)(x)| ≤ A) →
       (∀ x ∈ cube, |ξL(x)| ≤ X) →
       |avg(D(H ∘ K) ξL)| ≤ A X.
```

It also retains both pointwise identities, the splitting of the average, the
conditional eta-omega consequence, and the final averaged bound. Its premise
list is identical to the original's; it adds no boundedness/integrability premise
to the theorem itself. `A`, `X` are universally quantified uniform bounds over
the compact cube, consistent with Amendment D21. Holomorphy on a positive strip
supplies continuity/integrability, and actual suprema can be used as these bounds.
The proof obtains the general bound from the already proved
`energy_defect_src` and the other clauses from `step_ea_defect`; no dependency
output is assumed as a hypothesis. Fresh build, axioms and kernel replay pass.

Thus the source node is mathematically covered by the new wrapper, but the
handoff-named export still fails the strict focus. To remove that contract failure,
strengthen the designated export, or explicitly revise the designation to
`step_ea_defect_node` and identify the old theorem as a partial compatibility helper.
The latter requires a corresponding interpretation/update of the supplied
named-export contract; this report does not invent one. No source repair was made.

## Per-node / declaration ledger

All declarations have prefix `KAM.Iso.Linear.`. DG is the NODE line in
`docs/graph/I/DEPGRAPH.md`; BP is the cited line range in
`blueprint-I/parts/p1-iso-linear.tex`. Ext, Energy, Frame and Pert denote the four
`KAM/Iso/Linear/FullRangeSteps*.lean` implementation files.

| Node | DG / BP | Declaration / locator | Verdict | Source comparison |
|---|---|---|---|---|
| eb-holo | 1175 / 130–146 | `step_eb_holo`, Ext:39 | PASS | N, T, Y and each extended entry holomorphic; real-restriction continuity. Unused primary/real premises omitted. |
| eb-holo-inverse | 1236 / 136–137 | `step_eb_holo_inverse`, Ext:58 | PASS | B, N, P holomorphic from hK and unit Gram determinant alone; stronger premises. |
| eb-holo-field | 1266 / 139–140 | `step_eb_holo_field`, Ext:70 | PASS | A and DH along K holomorphic; unused frame hypotheses omitted. |
| eb-holo-torsion | 1297 / 142–143 | `step_eb_holo_torsion`, Ext:81 | PASS | All six regularity conclusions and the exact bordered entry formula. |
| eb-holo-conclude | 1329 / 145–146 | `step_eb_holo_conclude`, Ext:103 | PASS | Full N/T/Y/entry holomorphy and real-restriction continuity. |
| eb-period | 1360 / 148–153 | `step_eb_period`, Ext:116 | PASS | Y/N/T periodic and real; DH periodic along K and real in real directions. |
| eb-average | 1390 / 155–160 | `step_eb_average`, Ext:144 | PASS | Entry integrability, frozen entrywise integral, reality, omega border and zero corner. |
| eb-bounds | 1421 / 162–166 | `step_eb_bounds`, Ext:169 | PASS | Both row-sum chain links and max block-row bound, for every local CT. |
| lr-gradient | 1711 / 250–252 | `step_lr_gradient`, Ext:227 | PASS | Both signed identities for any phase point, stronger than only points in D. |
| lr-average | 1773 / 263–269 | `step_lr_average`, Ext:242 | PASS | Full (b)/(c), including invariant averages, last-row correction and 2n² bound. |
| ea-chain | 1843 / 301–305 | `step_ea_chain`, Energy:38 | PASS | Composition regularity, derivative chain rule, periodicity, realness, average and cube integrability. |
| ea-gradient | 1904 / 311–314 | `step_ea_gradient`, Energy:55 | PASS | Both vector identities; etaN uses no inverse, so no extra Gram premise needed. |
| ea-avg | 1935 / 316–319 | `step_ea_avg`, Energy:75 | PASS | All three zero averages; weaker premise set where Gram data are unused. |
| ea-size | 1964 / 321–326 | `step_ea_size`, Energy:85 | PASS | Both bounds, exact constants and successive losses; δ before δ′. |
| ea-defect (handoff designation) | 1996 / 328–334 | `step_ea_defect`, Energy:99 | FAIL | Still lacks first averaged derivative-bound estimate; included clauses are sound. See F1. |
| ea-defect (new full export) | 1996 / 328–334 | `step_ea_defect_node`, Energy:142 | PASS | Both averaged bounds and all source identities/consequences under the same premises. See F1. |
| ec-derivative | 2061 / 351–353 | `step_ec_derivative`, Energy:179 | PASS | Centered holomorphic periodic u, zero average and Du omega = 0; unused realness omitted. |
| ec-unique | 2090 / 355–359 | `step_ec_unique`, Energy:198 | PASS | Vanishing on every admissible substrip and on the full strip, proved using the landed parent. |
| ec-pointwise | 2119 / 361–362 | `step_ec_pointwise`, Energy:212 | PASS | Constant energy, conditional E0 equality, and actual sSup equality with nonempty strip. |
| rd-expand | 2453 / 510–514 | `step_rd_expand`, Frame:43 | PASS | Exact projected identity, signs and Delta omega = -xiomega omega retained. |
| rd-consequence | 2485 / 516–521 | `step_rd_consequence`, Frame:73 | PASS | Residual/bound, radius-one Neumann clause for P/Q, inverse residual and equivalence. |
| geo-de | 2552 / 547–548 | `step_geo_de`, Frame:119 | PASS | Error regularity/bound and both derivative estimates, no torsion-average premise. |
| geo-red | 2583 / 549–559 | `step_geo_red`, Frame:134 | PASS | Both estimates with exact 2n(n+1)m and C_red constants. |
| geo-red-domega | 2613 / 552–556 | `step_geo_red_domega`, Frame:149 | PASS | Expanded/factored coefficient equality and directional derivative bound. |
| geo-red-ered | 2646 / 558–559 | `step_geo_red_ered`, Frame:159 | PASS | Exact C_red = 2n(n+1)m² and E_red bound. |
| geo-sym | 2679 / 561–562 | `step_geo_sym`, Frame:167 | PASS | Regularity, periodicity, zero average, C_Omega bound and m² comparison on T_r. |
| pt-small | 2745 / 579–581 | `step_pt_small`, Pert:34 | PASS | Constant domination and all four smallness inequalities; d nonnegative derived at zero. |
| pt-domain | 2774 / 582–583 | `step_pt_domain`, Pert:58 | PASS | Both ball inclusions and both field-bound links; unused global premises omitted. |
| pt-frame | 2803 / 584–585 | `step_pt_frame`, Pert:83 | PASS | Both L differences, both L bounds, Gram invertibility and both inverse bounds. |
| pt-torsion | 2835 / 586–589 | `step_pt_torsion`, Pert:134 | PASS | Three N estimates and X_N/torsion differences on their correct successive strips. |

The facade `FullRangeSteps.lean:8–11` passes as an import-only public interface.
The 29-node list in the GAP plan matches the handoff; with the new wrapper there
are 30 theorem exports. No other requested node is missing. Alternative
`ea-avg` route records are not extra mandatory exports. The signed parent
`energy_defect` and its existing consumers are unchanged.

## Disclosed deviations, hypotheses and quantifier dependence

1. **K primary/real/domain hypotheses: accepted.** The standing setting explicitly
   says K is "holomorphic, primary and real on reals on T_r, with K(T_r) subset D"
   (blueprint:31–38). Those premises on eb-period, eb-average, ea-* and ec-* are
   I5/I6, not extra assumptions. `SettingSrc` bundles H/domain/frequency data;
   its K/r premises remain explicit. Some exports drop unused standing premises,
   giving stronger statements.
2. **lr-average omits lr-insert: accepted.** Its NODE specifically asks for (b)/(c),
   fully stated here; lr-insert is outside this package's requested list. The
   landed parent proves the last-row identity inside the derivation. This is
   use of a proved dependency, not its output assumed as a premise.
3. **rd-consequence's global det P premise: accepted.** The source at blueprint:494
   literally requires "det P != 0 on T_{r'}". The new Neumann clause proves
   P and Q invertible whenever the pointwise symplectic defect norm is below one.
   The inverse residual is conditional on the bordered system, and the final
   equivalence does not assume that system. No false inference from det G to
   det P is used. The determinant proof factors Omega0 + E_sym using
   I - Omega0 E_sym and uses the actual radius-one criterion.
4. **DH row-sum norm: accepted.** Blueprint:44–46 specifies the one-row norm
   as the sum of absolute entries. Ext:169 uses that norm, over `Fin n ⊕ Fin n`,
   rather than the max norm of the row viewed as a vector. Its product estimate
   sums entries and uses rowSum_le_norm; the bound by M uses the complex-linear
   functional operator norm. No dimensional factor is dropped.
5. **ec-unique from energy_conservation_src: accepted.** The parent is a proved
   theorem, applied inside the proof, not a supplied hypothesis. Its underlying
   proof in `Energy.lean:221` invokes cohomological uniqueness and strip margins,
   and imports no new step module. No Lean cycle exists. Graph edges describing
   the source proof should not be conflated with this reverse re-export route.

Across all declarations the source variables remain universal and no constant
acquires wider dependence. Independent universal binders can be curried/reordered
without changing source dependence; the nested δ then δ' dependence in ea-size
is retained. The perturbation constants are fixed before K' and d. The only
conditional data include source error bounds, unit Gram determinants, the bordered
system and avg(Y xiN) = etaomega, exactly where the source requires them. No hard
proof step is smuggled in as a premise, instance or bundled field.

The geometry bundle `AdmissibleNoTwist` contains the explicit standing frame/error
premises and no unbordered or bordered torsion-average invertibility. Free sigma
parameters do not alter constants: `mSize_max_one` preserves all relevant constants
when the proof passes positive `max sigma 1` to older helpers. Positive r is a source
premise. Several perturbation statements omit `2δ < r` or other unused source
premises, proving stronger statements, including cases with empty target strips.

## Definition and totality classification

No new `def`, `abbrev`, `structure`, `class`, `instance` or notation occurs in the
five Lean files. There is no new object with hidden junk/fallback behavior.

Reused objects preserve the intended carriers and bilinear signs: energyRow is
DH(K)N; bordMat is (T omega; Y 0); averages use the unit cube; P, Q and symplectic
errors are the existing bilinear objects, not Hermitian replacements. Analytic
frame assertions guard the inverse with unit Gram determinant. Algebraic
statements such as lr-gradient and eb-bounds are stronger facts about the total
existing definitions, without relying on a false analytic inverse claim.
Integrability is proved before using energy/extended averages in these exports.
The ec-pointwise proof makes the image of the nonempty strip a singleton before
using csSup_singleton; it does not exploit sSup's empty/unbounded fallback.

## Independent mechanical checks

All audit Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5`. No library clean, cache fetch, root regeneration or package edit was
performed. Scratch was confined to `.lake/abi-scratch/` and removed afterward.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-gi1b KAM.Iso.Linear.FullRangeSteps
```

Exit 0; exact output:

```text
[inp-gate] slot 1 acquired 05:45:09 for KAM.Iso.Linear.FullRangeSteps
✔ [3210/3210] Built KAM.Iso.Linear.FullRangeSteps (2.3s)
Build completed successfully (3210 jobs).
```

### All 30 axiom probes

The scratch probe imported the public facade and executed `#print axioms` for
every theorem in the ledger, including both ea-defect exports:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP_I1b_Audit2.lean
```

Exit 0. Exact output:

```text
'KAM.Iso.Linear.step_ea_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_size' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_defect' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Linear.step_ea_defect_node' depends on axioms: [propext, Classical.choice, Quot.sound]
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

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Iso.Linear.FullRangeSteps KAM.Iso.Linear.FullRangeStepsExt \
  KAM.Iso.Linear.FullRangeStepsEnergy KAM.Iso.Linear.FullRangeStepsFrame \
  KAM.Iso.Linear.FullRangeStepsPert
```

Exit 0; exact output:

```text
replaying KAM.Iso.Linear.FullRangeStepsPert
replaying KAM.Iso.Linear.FullRangeStepsFrame
replaying KAM.Iso.Linear.FullRangeStepsEnergy
replaying KAM.Iso.Linear.FullRangeStepsExt
replaying KAM.Iso.Linear.FullRangeSteps
```

### Source lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1; exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1274 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is exactly the brief's permitted generated-root exception. There is no
other lint failure; the generated root was left untouched.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0, empty output. The targeted forbidden-token/resource-option scan
produced no matches (rg exit 1). Each file has copyright, module, public imports,
module docstring and public section. Fresh counts:

| File suffix | Lines | Maximum Unicode line length |
|---|---:|---:|
| FullRangeSteps | 20 | 93 |
| FullRangeStepsEnergy | 232 | 100 |
| FullRangeStepsExt | 267 | 99 |
| FullRangeStepsFrame | 187 | 97 |
| FullRangeStepsPert | 186 | 100 |

A recursive KAM import traversal from the facade reached 81 KAM modules,
with zero providers and zero frozen theorem modules; no DRAFT_SORRY import or
manifest-state exception is involved. A search of all other KAM Lean files found
zero declarations reusing any of the 30 theorem short names and zero references
to them outside the new modules. All exports remain in `KAM.Iso.Linear`; no
public HELPER-name collision or harmful root shadow was found.

## Errata, integration notes and limits

No new suspected defect in a pinned mathematical source or frozen statement was
found. F1 is an export/designation mismatch, not a source erratum. Existing HL19
sign corrections are preserved. No default-heartbeat design failure occurred.

The handoff's 29-export count, Energy's 194-line count and original ea-defect
mapping predate the new wrapper; actual Energy has 232 lines and the package has
30 theorems. Frame has 187 lines, versus the handoff's 186. The facade/module
summaries also still list the original 29 names. Graph LEAN_STATUS/LEAN_REF fields
remain unupdated in this checkout. Those integration records should name the
full export if it is adopted. No graph or handoff was edited by this auditor.

Only this exact worktree-local report was added; the audit scratch probe was
removed. No source/frozen/manifest/generated file was changed and no state-changing
git command was run. The audit establishes package-local proof and interface
facts only; it makes no new campaign-level theorem or seal claim.
