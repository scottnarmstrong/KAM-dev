# P12-D independent package audit 1

**Overall verdict: PASS WITH NOTES for P12-D.** All four public declarations have exactly the supplied design signatures, pass independent elaboration and kernel replay, and have only standard axioms. No blocking mathematical, signature, definition, or hypothesis defect was found in the two scoped modules. Notes concern the permitted stale generated root and the wider comparison diff.

No frozen anchor is proved by this package. P-PLANAR (`KAM.Planetary.planarTwoPlanetKAM`) and P-FIXED (`KAM.Planetary.fixedSunPlanetaryKAM`) remain `DRAFT_SORRY` in the live manifest; neither is seal-ready on this evidence. Provider/frozen-type and frozen seal-body probes are **not applicable**: P12-D delivers ordinary local infrastructure, with no provider export. Exact design-signature probes replace that check for these four exports.

## Scope and authority

Audit date: 2026-10-28. Worktree and report destination: `/root/code/KAM-inp-p12d`. The user's exact absolute report destination overrides the generic package brief's main-worktree destination.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the P12-D handoff and AUDIT FOCUS, `docs/tracks/P/design/P1213-LEAN-DESIGN.md` (revision 2), both `docs/tracks/P/design/DESIGN-P1213-design-audit-{1,2}.md`, the original `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean`, relevant Track P statement conventions and P-PLANAR/P-FIXED statements, Part 12 blueprint transport/measure and preceding chart clauses, relevant frozen predicates and headline anchors, and delivered dependency interfaces. Existing PP1-4 and P6-5 audits provide prior package-review context; fresh checks below establish the current consumer types and axiom closure.

Only these implementation files are audited:

- `KAM/Planetary/PlanarAssembly/Transport.lean` (97 lines).
- `KAM/Planetary/PlanarAssembly/Measure.lean` (174 lines).

Snapshot: HEAD `b8f076dea17f1abe580feb9648925f380e4187ef`; observed `inp` `fb4f8fd5f66d30a1241f68e28ee3357cd46412c0`; merge base `1f9fe4d119e56bd960a52ae5ab677f2522f4a352`.

`git diff inp...HEAD` contains ten changed files: the two scoped additions and eight other changes in Hamiltonian/TorusUnion, MaximalStep/Cutoff, PGAssembly/FrequencyJets and FrequencyLip, PGMeasure/ResonanceFast/Pullback and ResonanceLarge/Frequency, and SecularForm/AnalyticReal and ModelTransfer. These other changes receive no audit verdict here, as AUDIT FOCUS explicitly limits scope. Thus the handoff's “No other file touched” describes the package, not the entire requested branch comparison. The pre-existing untracked `P12-D-handoff.md` was preserved.

| Input | SHA-256 |
|---|---|
| Transport.lean | `f6539fcbe71d8025fad75b6068c2ee7ea50ab182beb8e1afeb6b18dbd3574e5b` |
| Measure.lean | `d8dfda54bc4f621e873e7de50b75f2d022726518557610b89907cd83cc06695a` |
| Original P1213Signatures.lean | `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447` |

## Node and declaration ledger

Public names below have prefix `KAM.Planetary.PlanarAssembly.`; implementation locators are relative to `KAM/Planetary/PlanarAssembly/`. Blueprint labels have their full prefix.

| Node | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p12:transport` | `transport`, Transport:35 | PASS | Literal design telescope; actual frozen cylinder and physical predicates, same frequency and physical time, exact range identity. General a,b and arbitrary Hamiltonians strengthen reusability as explicitly designed. |
| `stepP:p12:tr-an` | `transport`, Transport:49–60 | PASS | Chart from analytic/symplectic data; equality of Hamiltonians on open O becomes local eventual equality before transporting differentiability. Analytic composition is guarded by range inclusion. |
| `stepP:p12:tr-per` | `transport`, Transport:61–65 | PASS | Frozen cylinder winding plus hQ1 gives periodicity under every integer parameter vector, with fast shifts only. |
| `stepP:p12:tr-inj` | `transport`, Transport:66–68 | PASS | hQ2 gives a fast lattice displacement; frozen cylinder injectivity yields an integer displacement of all parameter phases. |
| `stepP:p12:tr-lag` | `transport`, Transport:69–79 | PASS | Chain rule, bijective chart derivative, injective torus derivative, and factor-one symplectic identity give both immersion and vanishing pullback. |
| `stepP:p12:tr-flow` | `transport`, Transport:83–93 | PASS | Identifies fderiv through local equality, then applies chart_orbit for every real theta,t. No derivative of an unguarded total extension and no time rescaling. |
| `stepP:p12:tr-dio` | `transport`, Transport:80–82 | PASS | Reuses gamma,tau,w; a+b<tau implies (a+b)-1<tau. |
| `bpP:p12:measure` | `measure`, Measure:97; `measure_in_tube`, Measure:158 | PASS | The designed split exports image equality/injectivity/Borelness/exact volume first, then tube inclusion and positive finite volume. |
| `stepP:p12:me-inv` | `cylinder_set_shift`, Measure:66 | PASS | Completes k with zero slow indices; whole torus ranges lie in S. Negative shifts give reverse inclusion. |
| `stepP:p12:me-cell` | `measure`, Measure:114–143 | PASS | Floor reduction lands in [0,2pi); hQ1 preserves image. hQ2 and strict cell width force every integer shift to zero. |
| `stepP:p12:me-meas` | `measure`, Measure:144–155 | PASS | Rewrites away arbitrary V using S subset cylinder, obtains Borel cell intersection, then uses delivered chart image and Liouville theorems at factor one. |
| `stepP:p12:me-tube` | `measure_in_tube`, Measure:158–168 | PASS | Restricts MapsTo using hS, transports positive cell volume through equality, and invokes delivered finite-tube-volume theorem. |
| Auxiliary | private `fast_fst_add_fastShift`, Measure:36 | PASS | Coordinate formula for the literal frozen shift. |
| Auxiliary | private `fastShift_neg`, Measure:40 | PASS | Negation identity on both phase blocks. |
| Auxiliary | private `fastShift_zero`, Measure:47 | PASS | Zero shift identity on the complete carrier. |
| Auxiliary | private `shift_mem`, Measure:53 | PASS | Derives shift closure from the frozen whole-torus union, rather than assuming it. |
| Auxiliary | private `measurableSet_fastCell`, Measure:77 | PASS | Finite coordinate half-open bounds are measurable. |
| Auxiliary | private `cell_inter_eq`, Measure:86 | PASS | Exact intersection identity under only S subset cylinder; no measurability premise on V. |

All four public signature strings, from `theorem` through the conclusion before `:=`, were mechanically compared with the original signature file: each returned `literal signature match: True`. A fresh probe copied each independent signature under `audit_<name>`, proved it by applying the implementation to every explicit binder in order, and checked the reverse assignment:

```lean
example : type_of% @transport := @audit_transport
example : type_of% @cylinder_set_shift := @audit_cylinder_set_shift
example : type_of% @measure := @audit_measure
example : type_of% @measure_in_tube := @audit_measure_in_tube
```

All elaborated without errors or warnings. No premises, quantifier order, carriers, constants, or conclusion conjuncts changed.

## Definitions and hypotheses

**New def/abbrev/structure inventory: empty.** These modules introduce only the four public theorems and six private lemmas. The local `set k` in the cell proof is the literal negative coordinatewise floor, not a fallback object. No junk values or new totalization enter the proof. The implementation deliberately uses frozen `KAM.Planetary.fastShift`, which changes only fast position coordinates by 2pi*k and leaves slow positions and all momenta fixed.

The imported frozen predicates were read by body: `IsCylinderTorus`, `IsPhysicalTorus`, `IsCylinderKolmogorovSet`, `cylinder`, `cylinderCell`, `fastShift`, and `circularTube`. The union predicate supplies measurable S, S subset cylinder, and whole torus ranges. No frozen meaning is replaced by an auxiliary predicate.

**hQ1/hQ2 are legitimate local source premises.** Part 12 chart proposition, `blueprint-P/parts/p12-planar-assembly.tex:94–96`, asserts fast-shift domain invariance, periodicity, and injectivity modulo that same fast lattice; its lattice proof is at line 104. The design's joint `pg_hypotheses` outputs these clauses, so the generic transport/measure lemmas may consume them. They do not assume physical-torus or image-measure conclusions, and the actual upstream chart construction remains P12-C's obligation. No P12-C theorem or P-G theorem is imported.

`measure_in_tube` intentionally consumes hvol (the preceding measure result), hpos (positive input cell measure), and hmap (the upstream chart's tube mapping). This is the explicitly designed local consequence helper, not a substitute for constructing a physical chart or proving P-PLANAR from its source premises. These hypotheses are precisely the frozen-cylinder assembly data assigned in the design; no extra conclusion-shaped root premise is introduced.

The generic statements work at arbitrary a,b without an unstated positivity assumption on V, r, or mu: the conditional torus/set premises supply everything used, and empty/degenerate carriers cause no special fallback. Tube finiteness retains exactly hG, hm0 and ha; no positive-mass or positive-tube-radius premise was added.

## Dependency delivery and quarantine

Consumed interfaces are in-tree and were inspected at their current types:

- `IsChart.bijective_fderiv`, Chart:61; `chart_field_differentiableAt_iff`, Chart:79; `chart_orbit`, Chart:128.
- `measurableSet_chart_image`, Liouville:60; `chart_measure_image`, Liouville:83.
- `volume_lt_top_of_subset_circularTube`, Newtonian/Assembly:101.

All six received fresh axiom checks, with the same standard set as the four exports. The Chart differentiability equivalence uses a local inverse; the Borel-image theorem uses a countable local-injectivity cover; the volume theorem requires null measurability and injectivity for equality; the finite-tube theorem bounds any subset. These hypotheses match the actual applications. The full-position-lattice Transport and Liouville pipeline is not used. Part 1 Transport is a conceptual dependency only; this implementation needs Chart's local orbit theorem directly.

A recursive static traversal of the two modules' KAM imports found 67 KAM modules, **zero provider imports and zero frozen theorem imports**. Thus no DRAFT_SORRY anchor can enter this package through its KAM import closure. Each of the four new public names occurs only once in the PlanarAssembly namespace; there is no public-name collision. Existing upstream audit notes and the broader planetary proof campaign remain outside this scoped verdict.

## Independent validation

All audit-owned Lean/Lake operations were sequential and used `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion, or synthesis override, clean, dependency update, cache retrieval, or root regeneration was used.

### Targeted compile gate

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p12d KAM.Planetary.PlanarAssembly.Measure KAM.Planetary.PlanarAssembly.Transport
[inp-gate] slot 2 acquired 14:30:08 for KAM.Planetary.PlanarAssembly.Measure KAM.Planetary.PlanarAssembly.Transport
Build completed successfully (9113 jobs).
exit 0
```

The build replayed four inherited unused-binder warnings: Hamiltonian/Algebra:146 (`hc`), Hamiltonian/Chart:193 (`hc`), and Kepler/Energy:106 (`hm`, `hκ`). No warnings arose in the two scoped modules. No default-heartbeat design failure occurred.

### Signature and axiom probe

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P12DAudit.lean
exit 0; no errors or warnings
```

Exact axiom output:

```text
'KAM.Planetary.PlanarAssembly.transport' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.cylinder_set_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.measure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.measure_in_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.IsChart.bijective_fderiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_field_differentiableAt_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.measurableSet_chart_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chart_measure_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_lt_top_of_subset_circularTube' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarAssembly.Transport KAM.Planetary.PlanarAssembly.Measure
replaying KAM.Planetary.PlanarAssembly.Measure
replaying KAM.Planetary.PlanarAssembly.Transport
exit 0
```

There is no provider module to replay. One invocation covered both lemma modules.

### Hygiene and source invariants

Static forbidden-token/resource-override/provider scans of the scoped files returned no matches. Both files have copyright, module command, public imports, module docstring, and public noncomputable section; ambient types are Fin-indexed functions. Lengths are 97 and 174 lines, well below 1500. `git diff --check inp...HEAD` exited 0.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
(no output; exit 0)
```

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (698 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the generated-root staleness expressly permitted by the audit brief. The root was left untouched as required. No other lint issue was emitted.

## Defects, deviations, and limits

No new suspected pinned-source, blueprint, or frozen-statement defect was found. In the concrete blueprint application V is an open action box, so the claim “F is Borel” at `blueprint-P/parts/p12-planar-assembly.tex:153` is justified there. The generic signature deliberately allows arbitrary V, and Measure:86–92 and 144–146 discharge the stronger obligation without assuming V measurable. This addresses design audit 1's N3 directly.

The broader-dimension transport/measure statements and direct fast-lattice proof are already explicit design choices (design deviations D4/D8). There is no new implementation deviation. The statements do not reapply the full-position-lattice theorem to a Cartesian cylinder torus, infer slow winding, divide frequency by 2pi, or insert a volume factor. Factor c=1 gives exactly equal volume. P-G sealing, actual P12-C chart construction, and P12-E/P13-B assembly remain separate obligations, not closed by these generic lemmas.

Only this report is a persistent audit addition. Audit-owned scratch probes and logs are removed after recording the receipts. No repository source, generated root, frozen file, manifest, or git state was edited.
