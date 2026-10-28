# Independent P7-6 package audit 1

**Overall verdict: PASS WITH NOTES.** Both `bpP:p7:tube` and `bpP:p7:lattice` pass the scoped statement, definition, proof and kernel checks. No material P7-6 defect was found. Notes concern inherited repository hygiene and the non-minimal branch comparison below. This package supplies infrastructure, not a provider export or a frozen-anchor seal; per-anchor seal readiness and provider/frozen ABI/seal-body probes are **not applicable**.

Audited worktree: `/root/code/KAM-inp-p76`. HEAD: `34a40a63e1a04fcf9807c63dbdfad0f43eaaef63`; comparison ref `inp`: `4f65a1f8055d14808ab27ed9bff2e18d69eac46c`. Scope is exactly `KAM/Planetary/Poincare/Lattice.lean` and `KAM/Planetary/Poincare/Tube.lean`, as required by AUDIT FOCUS. Only this report was written outside temporary audit scratch. No source, frozen file, manifest, generated file or git state was modified.

## Authority and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief, P7-6 handoff, Track P statement conventions, `KEPLER-LEAN-DESIGN.md` row P7-6, section 7.1, Part 1 dependency provisions (including lines 594–598 and 624–625), and the relevant entries and findings of Kepler design audits 1–3. Compared against `blueprint-P/parts/p7-kepler-poincare.tex:215–241` and the current audited design signatures at `/root/code/KAM-inp/.drafts/design/KeplerSignaturesP.lean:569–619`. Its SHA256 is `d9903304231afac0841cf0456d90c3dec04b2eb9e1a9752a9d4f9f9b7164d9c8`, matching design audit 3's pinned signature artifact.

Read the actual frozen definitions `Phase`, `Assemble`, `FastShift`, `CircularPoint`, and `CircularTube`, and the consumed chart/product/element definitions and proofs. No frozen theorem is proved or directly consumed here. A recursive local KAM import scan found 69 modules, **zero provider modules and zero frozen theorem modules**. Thus no imported DRAFT_SORRY theorem or provider quarantine violation arises; the axiom checks independently exclude proof dependence on sorryAx.

The required `git diff inp...HEAD` emits:

```text
warning: inp...HEAD: multiple merge bases, using daf4a2c4a6a76725f5bd77c8aa1828efb01f7dbc
```

It contains 53 files, including unrelated I/N/P work and an 11-line addition to generated `KAM.lean`. Therefore the generic audit brief's whole-range protected-path condition is **not literally satisfied**: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is nonempty solely for `KAM.lean`. `KAM/Frozen`, `manifest` and `README.md` have no changes in this comparison. These are integration notes, not changes attributed to the two scoped P7-6 modules. The final three P7-6 commits (`a4ac340`, `bdc5721`, `34a40a6`) touch only Lattice/Tube; the earlier P7-6 WIP commit also concerns Lattice. A direct `git diff inp HEAD` likewise shows these two new modules and inherited root-import drift. No broader branch certification is implied.

## Declaration inventory

All names below are in `KAM.Planetary`; file locators abbreviate the two scoped modules. Every new public declaration is covered (29 total: 22 theorems and 7 definitions). Helpers have no separately frozen blueprint signatures; their literal identities or element facts implement the indicated proof steps without being substituted for the main result.

| Node / role | File:line | Declaration | Verdict | Reason |
|---|---|---|---|---|
| lattice | Lattice:38 | `polarDom` | PASS | Exact design domain: every action I is positive and 0 < R < I. |
| lattice | Lattice:41 | `polarMap` | PASS | Exact design formula; assemble places sine in positions and cosine in momenta. |
| helper | Lattice:48 | `polar1` | PASS | Literal one-planet polar map; no choice or fallback. |
| helper | Lattice:52 | `polarDom1` | PASS | Literal one-planet domain. |
| helper | Lattice:54 | `planetBlock_polarMap` | PASS | Unconditional block identity. |
| helper | Lattice:59 | `mem_polarDom_iff` | PASS | Exact equivalence with all one-planet domains. |
| helper | Lattice:64 | `unblock_planetBlock` | PASS | Unconditional inverse reassembly identity. |
| helper | Lattice:69 | `polarMap_eq_unblock` | PASS | Unconditional block formula. |
| helper | Lattice:77 | `unblockLin` | PASS | Literal reassembly with proved linearity. |
| helper | Lattice:87 | `unblockCLM` | PASS | Same reassembly as a continuous linear map. |
| helper | Lattice:90 | `unblockCLM_apply` | PASS | Definitional identity on the whole carrier. |
| helper | Lattice:190 | `polarMap_eq_unblockCLM` | PASS | Unconditional function equality for derivative composition. |
| lattice | Lattice:196 | `analyticOnNhd_polarMap` | PASS | Exact design signature; positivity guards square-root analyticity. |
| lattice | Lattice:205 | `polarMap_mapsTo` | PASS | Exact signature; squared oscillator radius gives Gamma = R < I. |
| lattice | Lattice:217 | `polarMap_symplectic` | PASS | Exact signature; explicit derivative and sum of canonical block forms. |
| lattice | Lattice:256 | `polarDom_shift` | PASS | Exact signature; shift changes no action coordinate. |
| helper | Lattice:261 | `polarMap_shift` | PASS | Stronger global identity; full input shift becomes frozen fastShift. |
| helper | Lattice:274 | `polarMap_eq_shift` | PASS | Recovers both actions and all angle lattice differences from image equality. |
| lattice | Lattice:319 | `poincareProd_polar_symplectic` | PASS | Exact signature; differentiability and MapsTo discharged in composition. |
| helper | Lattice:326 | `analyticOnNhd_poincareProd_polar` | PASS | Additional analytic conclusion completes the composite chart data. |
| lattice | Lattice:330 | `poincareProd_polar_lattice` | PASS | Exact signature; global invariance and converse modulo the full lattice. |
| lattice | Lattice:344 | `poincareProd_polar_periodOne_symplectic` | PASS | Exact signature; Part 1 isChart_angleScale supplies factor 2*pi. |
| lattice | Lattice:357 | `poincareProd_polar_periodOne_lattice` | PASS | Exact signature; includes shifted-domain membership and converse integer lattice. |
| lattice | Lattice:384 | `polar_hamiltonian_split` | PASS | Exact design moving-Sun split; only masses, positive kappa and domain assumed. |
| tube | Tube:48 | `circularPoint_eq_poincareProd` | PASS | Exact signature; positive data identify axes and the period-one circular torus. |
| helper | Tube:80 | `tubeNbhd` | PASS | Physical element inequalities restricted to regionMK, on the intended ambient Pi norm phase space. |
| helper | Tube:86 | `tubeNbhd_subset_regionProd` | PASS | Unconditional projection of region membership. |
| helper | Tube:89 | `mem_tubeNbhd_poincareProd` | PASS | Exact iff for chart preimages; source positivity/domain premises only. |
| tube | Tube:199 | `tube_in_chart` | PASS | Exact signature; eta0 depends only on fixed data and delta, before eta and all preimages. |

## Definition classification and proof review

The seven definitions are `polarDom`, `polarMap`, `polar1`, `polarDom1`, `unblockLin`, `unblockCLM`, and `tubeNbhd`. All implement the intended literal sets/maps on their whole carriers. The square root in the total polar maps is Lean's ordinary real square root outside the positive domain; no theorem uses an unintended negative-radius value. In-domain positivity explicitly guards differentiation, analyticity and cancellation. `unblockLin`/`unblockCLM` are faithful wrappers around existing `unblock`, not altered reassembly. `tubeNbhd` explicitly includes the physical elliptic region; continuity never relies on total energy/action expressions at singular physical points. There are no new abbrevs, structures, bundled premises or conclusion-shaped hypotheses.

For the polar proof (`Lattice:94–237`), checked the one-planet derivative, inverse-radius coefficient, nonzero square-root cancellation, sine/cosine identity, and frozen symplectic sign. The blockwise chain rule uses actual HasFDerivAt facts; the composition theorem's differentiability premises are discharged, so total `fderiv` is not exploited at a bad point. For injectivity (`274–315`), squared norm recovers R, positive radius permits trig cancellation, and the common sine/cosine values give an integer multiple of 2*pi. R = 0 is correctly excluded. The argument also works at n = 0 without an unguarded nonempty-index choice.

For the tube proof (`Tube:119–236`), action continuity is restricted to the open elliptic region with nonzero negative energy. The reference torus is compact as an image of the closed unit cube; fractional parts recover every real angle, including endpoints. Closed thickening gives a uniform positive r, and the strict frozen tube bound with eta <= r yields containment. The preimage estimate holds for **every** chart preimage, using element identities; no global continuous angle inverse is assumed. All distances are those of the frozen ambient Pi norm, with no replacement by planar Euclidean length.

Part 1 owns `angleScale`, `fullShift`, and `IsChart`. Lattice publicly imports `Hamiltonian.Chart`, uses its `isChart_angleScale` at lines 348–354, and defines no local copies. The period-one factor is 2*pi, not 1 or its reciprocal. Analyticity of the composite is supplied by the additional helper at line 326; symplectic and analytic pieces provide the blueprint's chart content. Source/target dimensions remain the designed `Phase (n+n)` and `Phase (n*2)`; equal-dimension consumers still use the existing designed cast adapter. No assertion that the full polar lattice applies to arbitrary Cartesian cylinder tori is introduced.

## Independent checks

All Lean commands were run sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper supplies nice itself). No heartbeat, recursion-depth or synthesis-heartbeat override was used. No clean, update, cache download or package mutation was performed.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p76 KAM.Planetary.Poincare.Lattice KAM.Planetary.Poincare.Tube
```

Exit **0**. Relevant output:

```text
[inp-gate] slot 2 acquired 06:53:55 for KAM.Planetary.Poincare.Lattice KAM.Planetary.Poincare.Tube
Build completed successfully (9115 jobs).
```

Dependency replay emitted unused-variable warnings in Kepler/Energy, Poincare/Chart and Hamiltonian/Algebra/Chart; no warning in the two scoped files. This was a cached targeted build, supplemented by independent kernel replay below.

2. Signatures and exact application: a Python extraction compared each of the 11 main theorem signatures with the audited design file after removing whitespace; all 11 were identical, including binder order, constants, dimensions and conclusions. A scratch probe copied each design signature under a fresh theorem name and used `by exact <export> <explicit binders in order>`. This does not import or elaborate the design's sorry bodies. Ran:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P76Audit.lean
```

Exit **0**, no warnings/errors. Explicit applications were: circular identity `hG hm0 hm ha φ`; tube `hG hm0 hm ha hδ`; three polar chart results `n`; domain shift `k hz`; composite symplectic `hm hκ`; composite lattice `hm hκ hz hz' k`; period-one symplectic `hm hκ`; period-one lattice `hm hκ hz hz' k`; split `hm hκ hz`.

The same probe issued `#print axioms` for **every** new public theorem. Exact output:

```text
'KAM.Planetary.planetBlock_polarMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_polarDom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.unblock_planetBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarMap_eq_unblock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.unblockCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarMap_eq_unblockCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_polarMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarMap_mapsTo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarMap_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarDom_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarMap_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polarMap_eq_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_polar_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.analyticOnNhd_poincareProd_polar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_polar_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_polar_periodOne_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.poincareProd_polar_periodOne_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.polar_hamiltonian_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.circularPoint_eq_poincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tubeNbhd_subset_regionProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_tubeNbhd_poincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tube_in_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation for both modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Poincare.Lattice KAM.Planetary.Poincare.Tube
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.Poincare.Tube
replaying KAM.Planetary.Poincare.Lattice
```

4. Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, entirely from the two inherited issues below. Exact output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p76/KAM/Planetary/Hamiltonian/Liouville.lean:35:108
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (431 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module, frozen-anchor and all 144 frozen ABI checks pass. The non-root long-line failure is explicitly retained; this is not reported as a fully passing repository lint.

5. Scoped hygiene: Lattice has **394 physical lines**, Tube **242**; each has maximum line width **100**, with zero lines over 100. Both include copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section`. Text scans found no sorry/admit/axiom/unsafe/opaque, resource override, EuclideanSpace or local provider/theorem-anchor import. `git diff --check inp...HEAD -- KAM/Planetary/Poincare/Tube.lean KAM/Planetary/Poincare/Lattice.lean` exited **0** (only the merge-base warning); workspace `git diff --check` also exited **0**. Temporary probe files were removed after the check.

## Findings, uncertainties, errata and deviations

- **No required P7-6 repair.** Tube and lattice main signatures and proofs pass. No suspected defect in the mathematical blueprint or pinned source was found within this scope; no new deviation was introduced.
- **Inherited lint failure:** the 108-character `Hamiltonian/Liouville.lean:35` line is outside P7-6. Both P7-6 files meet the focus's 100-character requirement. The generated root also needs orchestrator regeneration; the auditor did not edit it.
- **Comparison limitation:** the requested three-dot diff includes unrelated merged work and is not a two-file package diff. The nonempty protected root-file comparison is explicitly reported above. The scoped verdict does not waive that whole-branch hygiene condition.
- **Documentation note:** design section 7.1 mentions `tube_in_chart` in the P7-5 paragraph, whereas the package table and audit focus assign it to P7-6. The delivered Tube module follows the latter authority; no mathematical statement changes.
- **Boundary of certification:** this proves the listed local infrastructure. It neither seals P-G/P-PLANAR/P-FIXED nor validates later physical measure/torus assembly. Generic fixed-Sun consequences in the blueprint are not advertised here as a new standalone theorem; the exact P7-6 design target `polar_hamiltonian_split` is the moving-Sun identity listed above.
