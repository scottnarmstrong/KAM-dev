# P13-B independent package audit 1

**Verdict: PASS WITH NOTES for `KAM.Planetary.FixedAssembly.n2` and the complete P13-B slice.**
No blocking statement, proof, definition, hypothesis, or node-coverage defect was found in
`KAM/Planetary/FixedAssembly/TwoPlanet.lean`. This is a two-planet assembly helper, not a
terminal provider or a seal of the general P-FIXED anchor. The generated-root lint exception
and the wider inherited comparison are recorded below.

## Authority and comparison

Audited 2026-10-29 in `/root/code/KAM-inp-fx13b`, HEAD
`bedcc6a9b9d184b1d6618e5b403bc7baf3e17560`. Read the package brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, AGENTS, PLAN, DECISIONS, the handoff,
P1213 design revision 2 and both design audits, the signed `FixedAssembly.n2` telescope,
Part 13 blueprint, P-FIXED track statement, and relevant frozen theorem/definition and
consumer interfaces. The user's exact worktree report path overrides the brief's generic
instruction to write in the main inp checkout. Only this report persists; temporary probes
were confined to `.lake/abi-scratch/` and removed. No implementation or git mutation.

`git diff inp...HEAD` was inspected. Git warns:

```text
warning: inp...HEAD: multiple merge bases, using a20be6a42facf4d58164200dedf9a38b0e72cb7b
```

The observed inp ref was `38b4d910d07fdfbd342ee170ef8c353750c27470`.
The comparison contains six additions (1080 lines): FixedAssembly Data/TwoPlanet and
PlanarAssembly ChartData/Data/DataBox/SlowSmall. The immediate package commit changes only
TwoPlanet (97 lines). The five inherited modules supply context; their source fidelity is
outside the explicitly scoped verdict. The initial untracked handoff was left untouched.

## Signature, proof and consumer checks

The sole new public declaration is `KAM.Planetary.FixedAssembly.n2` at line 43. Its complete
statement, before the proof separator, is byte-identical to the signed telescope at
`/root/code/KAM-inp/.drafts/design/P1213Signatures.lean:320` (file SHA256
`1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447`).
No additional premise, constant dependence, carrier change, or weakened conclusion occurs.
The scratch probe copied that telescope under a fresh name, supplied exactly
`FixedAssembly.n2 G m0 m a hG hm0 hm ha hsep eta heta`, and checked `type_of%`
assignments in both directions. It elaborated at default heartbeats.

Lines 51–53 eliminate **one fixed** joint output, keeping V,W,O,T and all jets consistent.
Lines 59–62 apply the SEALED frozen P-G theorem with a=b=2, mu0=1, the Kepler restriction,
and **`FixedAssembly.perturbation G m0 m T`** with its matching analytic, periodic,
frequency, Birkhoff, torsion and symmetry certificates. The resulting rG,C,c are fresh
witnesses for that perturbation. No moving threshold or moving P-G result is used.
Lines 63–67 select r and eps0, and the canonical d,D, before the later epsilon.
`radius_choices` supplies r>0, r<rG<1, `2*r^2 <= delta/2`, threshold>0, threshold<=1,
and the strict logarithmic smallness bound. Together with rG<r0 these discharge every
strict P-G radius/coupling condition and the tube domain condition.

Lines 71–82 derive fast-lattice chart clauses and actual domain inclusion, then apply the
generic measure theorems to obtain Borelness, positive volume, finite volume, and tube
inclusion of the actual image. Lines 85–91 transport every whole cylinder torus using
`G := fixedHamiltonian G m0 m epsilon` and its local Hamiltonian identity, preserving
frequency and physical time. The range identity supplies containment of the whole torus
in the image set. P6-5 then supplies the literal frozen fixed predicate, including all-time
fixed-center solutions, no collision, and pair bounds with the Sun at zero.

The signed n2 interface is the original existential frozen conclusion specialized to two
planets, sufficient for P13-C's dimension-split branch after `subst n`. Although it does not
export equalities identifying d,D as canonical formulas, that is the deliberately signed
n2 interface; its proof selects exactly those formulas. The stronger canonical-constant
interface repaired by design audit 2 concerns `n_general`, outside this package. There is
no new unsigned source-node export replacing a stronger blueprint statement.

## Complete node/declaration ledger

Locators in this table refer to TwoPlanet.lean; PA means `KAM.Planetary.PlanarAssembly`.

| Node / declaration | Lean implementation | Verdict | Reason |
|---|---|---|---|
| `bpP:p13:n2` | `FixedAssembly.n2`, 43–91 | PASS | Exact signed telescope; unconditional two-planet fixed conclusion. |
| `stepP:p13:n2-const` | n2, 54–67 | PASS | Positive canonical pair constants; fresh fixed radius and threshold. |
| `stepP:p13:n2-pg` | n2, 51–62 | PASS | Joint fixed data supplied to sealed P-G with the fixed perturbation. |
| `stepP:p13:n2-mu` | n2, 63–70 | PASS | Strict radius, unit upper bound and logarithmic smallness all supplied. |
| `stepP:p13:n2-S` | n2, 71–84 | PASS | Actual chart image is measurable, in the tube, and has positive finite volume. |
| `stepP:p13:n2-tori` | n2, 85–91 | PASS | Every image point lies on a transported whole torus in the image set. |
| `stepP:p13:n2-phys` | `fixedKolmogorovSet_of_tube`, 83–91 | PASS | Exact fixed physical clauses with canonical d,D. |
| `bpP:p13:transport` | PA.transport / measure / measure_in_tube, 71–91 | PASS | Generic delivered exports instantiated at the fixed Hamiltonian and fixed data. |
| `stepP:p13:tr-torus` | PA.transport, 87–91 | PASS | Same w, physical time, full physical predicate and range identity. |
| `stepP:p13:tr-meas` | PA.measure / measure_in_tube, 79–82 | PASS | Fast-cell volume equality, Borel image, tube inclusion, positive finite volume. |
| `bpP:p13:quantifiers` | n2, 51–70 | PASS | All data and eps0,d,D selected before epsilon; S selected afterward. |
| `bpP:p13:data#choices` | PA.radius_choices, 59–67 | PASS | Literal secular_radius and coupling_threshold with newly obtained fixed constants. |
| private auxiliary | `cylinder_subset_of_le`, 38–40 | PASS | Radius-square monotonicity under 0<r and r<=r0; no extra source premise. |

All 12 graph records assigned to P13-B by the design table are implemented, including the
three transport records intentionally mapped to reused exports rather than new declarations.

## Definition and import classification

No new `def`, `abbrev`, `structure`, instance, or notation is introduced. The local `set r`
is the prescribed explicit secular radius; it introduces no totalized fallback. Existing
`perturbation` is the constant coupling family of actual fFix composed with total_chart;
the proof consumes its analytic/domain certificates only on the supplied cylinder/open set.
Existing cylinder, cell, Hamiltonian and physical predicates retain their frozen bodies.

No conclusion-shaped input is assumed: the public theorem has only physical standing data;
all difficult P-G/chart/tube facts are obtained as proved upstream conclusions. No direct
provider import occurs. Traversing the 595-module project import closure found exactly one
frozen theorem module: ProperlyDegenerateKAM, manifest state **SEALED**. Its registered
provider is reached only through the permitted frozen anchor. No DRAFT_SORRY theorem is
imported. FixedSunPlanetaryKAM remains **DRAFT_SORRY**, is not imported, and is not sealed by
this helper. Provider/frozen seal-copy tests are inapplicable to P13-B because it adds no
provider; the analogous exact-telescope application test above was performed for its helper.

The private helper creates no public short-name collision. The signed name n2 is qualified
by FixedAssembly, and calls to potentially ambiguous perturbation/total_chart are qualified.
There is no new root declaration or harmful shadowing.

## Independent checks

Every Lean/Lake command was serialized within this audit, with `LEAN_NUM_THREADS=1` and
`nice -n 5` (the gate applies nice internally). No clean, cache update, broad rebuild,
resource override, or generated-root edit was used.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-fx13b KAM.Planetary.FixedAssembly.TwoPlanet
```

Exit 0. Output begins `[inp-gate] slot 1 acquired 00:45:55 ...` and ends
`Build completed successfully (9641 jobs).` Existing dependency warnings/info were replayed;
no warning/error was emitted for TwoPlanet. This reused the worktree build overlay.

2. Exact signature/application and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P13BAudit1.lean
```

Exit 0, no signature/application errors. The following eight independently probed results
each reported exactly `[propext, Classical.choice, Quot.sound]`:

```text
KAM.Planetary.FixedAssembly.n2
KAM.Planetary.FixedAssembly.pg_hypotheses
KAM.Planetary.properlyDegenerateKAM
KAM.Planetary.PlanarAssembly.transport
KAM.Planetary.PlanarAssembly.measure
KAM.Planetary.PlanarAssembly.measure_in_tube
KAM.Planetary.fixedKolmogorovSet_of_tube
KAM.Planetary.PlanarAssembly.radius_choices
```

In particular the literal main output was:

```text
'KAM.Planetary.FixedAssembly.n2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel replay invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.FixedAssembly.TwoPlanet KAM.Planetary.FixedAssembly.Data KAM.Planetary.PlanarAssembly.Transport KAM.Planetary.PlanarAssembly.Measure KAM.Planetary.Newtonian.Assembly KAM.Planetary.PlanarAssembly.Boxes
```

Exit 0; complete output:

```text
replaying KAM.Planetary.PlanarAssembly.Boxes
replaying KAM.Planetary.Newtonian.Assembly
replaying KAM.Planetary.PlanarAssembly.Measure
replaying KAM.Planetary.PlanarAssembly.Transport
replaying KAM.Planetary.FixedAssembly.Data
replaying KAM.Planetary.FixedAssembly.TwoPlanet
```

Global lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1165 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is a failed global lint invocation whose only diagnostic is the audit brief's
explicitly permitted generated-root exception. It is not described as an unqualified
lint pass. KAM.lean was not regenerated. No substantive hygiene failure was reported.

4. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty stdout,
exit 0 (only the multiple-merge-base warning on stderr). `git diff --check inp...HEAD`:
exit 0, no whitespace defect. The scoped source has 97 lines, maximum line length 100,
full copyright/module/public-import/docstring/public-section form, and no forbidden token,
EuclideanSpace, resource override, new instance, or public auxiliary name.

## Uncertainties, source defects and deviations

No new suspected pinned-source/blueprint defect or implementation deviation was found in
this slice. Previously recorded P1213 design departures (total composition rather than zero
extension, direct fast-lattice transport, no exponent lowering, and joint existential data)
remain intentional and are respected. Part 13's exclusion of Parts 11/11a concerns the
general-n route, not Part 11b, which supplies the fixed Birkhoff data.

This report audits upstream application types and standard axioms and replays the named
modules; it does not replace the separate source-characterization and mathematical audits
of inherited P13-A/P12-C or transitive analytic construction packages. In particular the
P1213 source-gap ledger is not erased by a successful compile. The scoped signed helper is
proved without adding any of those obligations as hypotheses. General-n construction and
terminal P-FIXED sealing remain P13-C's work.

## Closeout

The report's graph ledger was mechanically compared with the design's P13-B rows:
12 mapped nodes, no missing report node. The audit-owned probe was deleted. Final
`git diff --check` exits 0. Final status contains only this untracked report and the
pre-existing untracked P13-B handoff; tracked source/protected paths are unchanged.
No new erratum, uncertainty affecting the scoped proof, or audit-induced deviation.
