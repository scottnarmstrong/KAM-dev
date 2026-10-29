# P12-E independent seal-key audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-p12e`.
Audited HEAD: `60bf4fa595ebb129c067561dae2b860015cd4000`.

## Verdict

**PASS WITH NOTES — `KAM.Planetary.planarTwoPlanetKAM` (manifest `planetary.planarTwoPlanetKAM.v1`), seal-ready at the P12-E terminal-proof level.** The provider has the exact frozen type; the complete prospective seal elaborates without extra premises or `sorryAx`. No blocking P12-E mathematical finding. The generated-root lint exception and moving comparison branch are recorded below. This report does not modify or seal the anchor: its current manifest state remains `DRAFT_SORRY`. P12-C's separate source-characterization audit is not replaced by this terminal audit.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the package brief, P12-E handoff including AUDIT FOCUS, P1213 revision-2 design/node table, design audits 1–2, the supplied signature file, track-P statement, Part 12 blueprint, both theorem anchors and their operative frozen predicates. Both P12-E files were read in full; all six files in the initial three-dot diff were inspected. Only this report is a persistent audit edit. The user's explicit worktree report path overrides the generic brief's main-worktree destination.

## Comparison boundary and protected files

The initial `git diff inp...HEAD` contained six Lean files, 740 added lines: ChartData (72), Data (332), DataBox (83), SlowSmall (138), Main (92), and 23 added provider lines (38 total file lines). The first four belong to inherited P12-C, merged by `b4e41927`; P12-E commit `60bf4fa5` itself changes only Main and the provider (115 added lines). No initial protected-path diff existed.

`inp` advanced externally during this audit. Reproducible initial comparison:

```text
git diff a20be6a42facf4d58164200dedf9a38b0e72cb7b...HEAD
6 files changed, 740 insertions(+)
git diff a20be6a42facf4d58164200dedf9a38b0e72cb7b...HEAD -- KAM/Frozen manifest KAM.lean README.md
(empty)
```

The same six-file result holds against the branch point `3fcfb654e1e10a82cc4ab57401156fc446225ce1`. During validation, live `inp` reached `463375ee3fdc33faa02362b5343333301deed4be`, having independently merged P12-C. A repeated literal `git diff inp...HEAD` then warned `multiple merge bases, using d775cfa33857efd3efd0725c8398516a0e7bc864` and showed 19 files, 2215 additions/90 deletions. Its protected-path diff consists of five inherited generated KAM.lean imports (BirkhoffClauses, Generic, Patch, Displacement, ParameterLipschitz). Frozen files, manifest and README remain absent from that diff. `git log 3fcfb654..HEAD -- KAM.lean` is empty. These are comparison-base artifacts, not P12-E edits; no reset, merge or regeneration was performed. Verdicts here use the pinned initial comparison and the unchanged audited HEAD.

## Declaration and node ledger

Names below abbreviate `PA = KAM.Planetary.PlanarAssembly`, `P = KAM.Planetary`, `PR = KAM.Provider.Planetary`; step IDs have prefix `stepP:p12:` and result IDs `bpP:p12:`.

| Node / declaration | Lean declaration / locator | Verdict | Evidence |
|---|---|---|---|
| planar / frozen P-PLANAR | `PA.planar`, Main:39 | PASS | Exact signed/frozen telescope: physical premises only, existential threshold and bounds before coupling, original physical predicate and positive finite volume. |
| pl-const | Main:46–65; `PA.radius_choices` | PASS | One elimination of joint data, then P-G constants and radius/threshold choices before introducing μ. Canonical d,D depend only on axes. |
| pl-pg | Main:54–57 | PASS | Actual SEALED `P.properlyDegenerateKAM`, a=b=2, μ upper endpoint 1; every analytic, collar, frequency, BNF, determinant and symmetry premise is supplied by `pg_hypotheses`. |
| pl-mu | Main:64–65 | PASS | r<rG<r0; μ<threshold≤1; radius_choices supplies the strict logarithmic bound. Explicit positive cell volume is retained. |
| pl-S | Main:66–80 | PASS | S is literally `total_chart '' Sc`; measure supplies Borelness and exact cell volume; measure_in_tube gives tube inclusion, positivity and finiteness. No full slow-coordinate lattice is assumed. |
| pl-tori | Main:81–86 | PASS | Pointwise Sc torus witness, same w and physical time; transport supplies the physical predicate and exact range image. `image_mono hKS` retains the whole torus in S. |
| pl-phys | Main:79–87; `P.movingKolmogorovSet_of_tube` | PASS | Original frozen physical predicate, all-time Newton solutions, no collisions and canonical pair bounds; μ≥0 comes from μ>0. |
| pl-phys#route-orbit | Newtonian/Assembly: movingKolmogorovSet_of_tube | PASS | Actual helper body calls `orbit_transfer_moving` with all-point noncollision. |
| pl-phys#route-tube | same assembly route | PASS (alternative) | Design marks this an alternative, not a second mandatory proof; orbit-transfer route supplies its physical conclusion. |
| quantifiers | Main:46–65 | PASS | Shared chart/data and μ₀,d,D precede μ; S and torus frequencies may depend on μ/point as intended. |
| data#choices | `PA.secular_radius`, `PA.coupling_threshold`, `PA.radius_choices`; Main:58–61 | PASS | Literal min formulas; radius estimate is the stronger 2r²≤δ/2. No μ-dependent choice. |
| terminal provider | `PR.planarTwoPlanetKAM`, provider:25 | PASS | Direct application of PA.planar to every frozen binder, in order. |
| private monotonicity helper | Main:34, `cylinder_subset_of_le` | PASS | Positive r and r≤r0 give disc inclusion by monotonicity of squaring. No public name/shadowing introduced. |
| inherited chart composition | `PA.chart_of_birkhoff`, ChartData:43 | PASS | Exact signed local composition statement, analyticity and symplecticity actually composed. |
| inherited Hamiltonian identity | `PA.chart_hamiltonian_of_preserves_fast`, ChartData:56 | PASS | Exact signed identity, guarded product domain and fast-action preservation; arbitrary real coupling. |
| inherited joint data | `PA.pg_hypotheses`, Data:83 | PASS (consumer interface) | Exact signed joint output, no assumed data bundle. Construction uses patch/BNF exports, shared T and canonical sigma/beta expressions; all needed P-G and chart clauses established. Finer P12-C source certifications remain its separate audit responsibility. |
| inherited action algebra | `P.p12c_actions_sq`, DataBox:28 | PASS | Actual square identity with nonnegative source axis coordinate. |
| inherited action positivity | `P.p12c_actions_nonneg`, DataBox:35 | PASS | Total square-root formula and positive masses; valid on the whole stated carrier. |
| inherited action box | `P.p12c_box`, DataBox:41 | PASS | Positive endpoints and inverse-axis calculation establish the stated box-image inclusion. Distinct internal helper, not a replacement root premise. |
| inherited flow origin | `P.p12c_flow_zero`, SlowSmall:31 | PASS | Cubic homogeneity forces zero field at zero; uniqueness identifies the constant solution. |
| inherited slow projection | `P.p12c_slow_T`, SlowSmall:48 | PASS | Actual assembly/flow identity; no analyticity or conclusion asserted through a substitute definition. |
| inherited uniform smallness | `P.p12c_slow_small`, SlowSmall:89 | PASS | Continuous actual T on its source tube; compact action set × small closed slow ball, uniform continuity, zero-origin result, and independence from fast angles. The local continuity premise is supplied by Data's proved chart analyticity. |

Every row assigned to P12-E in design lines 155–165 is covered, including choices/quantifiers and both alternative physical routes. The only new public P12-E declarations are planar and its provider; there is no unsigned export pretending to prove a broader graph node.

## Definitions and statement fidelity

Main and the provider introduce no def, abbrev, structure or instance. Inherited ChartData introduces exactly two definitions: `total_chart = poincareProd m (G*m0) ∘ T`, and `perturbation = fun _ z => fMov G m0 m (total_chart ... z)`. Both are the intended total compositions, exact signed bodies, with no fallback, zero extension or arbitrary-choice branch. Their analytic uses are guarded by the proved open chart domain. Local sets/maps in Data are constructive witness choices in the theorem, not new predicates that assume its conclusion.

Whitespace-normalized complete declaration headers match the supplied `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean` for chart_of_birkhoff, chart_hamiltonian_of_preserves_fast, pg_hypotheses and planar. The provider matches after resolving its fully qualified Phase/MovingKolmogorovSet names. Definition bodies also match. Fresh type probes independently establish the terminal definitional type equalities; no extra premise, altered norm, weakened carrier or widened constant dependence was found.

The smaller inherited Data radius `min (rS/2) ρ` (Data:183) is a justified further shrink from the blueprint's r*/2: uniform slow-part control gives the entire forward-tube inclusion. Data returns δ=1 with an inclusion valid on every smaller cylinder, so its required implication is stronger; downstream radius_choices still receives positive δ and supplies its literal conclusion. This is an implementation refinement, not an added hypothesis or an unpaid inequality.

## Provider quarantine

Provider imports only Mathlib and PlanarAssembly.Main, never its target frozen theorem or another provider directly. Main imports the SEALED ProperlyDegenerateKAM anchor. A recursive KAM import scan found 595 KAM modules / 73 frozen modules; the only reachable frozen theorem is `planetary.properlyDegenerateKAM.v1`, state SEALED. The only other provider reachable transitively is its registered provider through that frozen anchor. No DRAFT_SORRY theorem is reachable from the P12-E provider. Importing the target anchor was confined to the audit probe. Axiom results below independently exclude transitive sorry dependencies.

## Independent validation

All audit-owned Lean/Lake invocations ran sequentially, with `LEAN_NUM_THREADS=1` and nice priority 5. No clean, update, cache download, override or library-wide rebuild was invoked.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p12e KAM.Planetary.PlanarAssembly.Main KAM.Provider.Planetary.PlanarTwoPlanetKAM
[inp-gate] slot 1 acquired 00:40:51 for KAM.Planetary.PlanarAssembly.Main KAM.Provider.Planetary.PlanarTwoPlanetKAM
Build completed successfully (9641 jobs).
exit 0
```

The gate itself invokes `nice -n 5 lake build` for these two targets. Output includes replayed upstream linter warnings (unused variables/simp arguments and style suggestions); no build error or P12-E warning was reported. The job count includes cached dependency replay, not a clean rebuild.

Scratch `.lake/abi-scratch/P12EAudit1.lean` imported the target frozen module and provider, and checked:

```lean
example : type_of% @KAM.Planetary.planarTwoPlanetKAM :=
  @KAM.Provider.Planetary.planarTwoPlanetKAM
example : type_of% @KAM.Planetary.planarTwoPlanetKAM :=
  @KAM.Planetary.PlanarAssembly.planar
```

It also copied the entire frozen theorem telescope under `KAM.Planetary.prospectiveP12E`, replacing only the name and proof body with:

```lean
by exact KAM.Provider.Planetary.planarTwoPlanetKAM G m0 m a hG hm0 hm ha hsep eta heta
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P12EAudit1.lean
exit 0
```

Every new public theorem in the initial six-file diff was checked by #print axioms: PA.chart_of_birkhoff, PA.chart_hamiltonian_of_preserves_fast, PA.pg_hypotheses, P.p12c_actions_sq, P.p12c_actions_nonneg, P.p12c_box, P.p12c_flow_zero, P.p12c_slow_T, P.p12c_slow_small, PA.planar and PR.planarTwoPlanetKAM. All output precisely `[propext, Classical.choice, Quot.sound]` (one result wraps across lines). The prospective seal and the actual SEALED properlyDegenerateKAM give the same list, without sorryAx.


The five directly consumed upstream exports PA.radius_choices, PA.transport, PA.measure, PA.measure_in_tube and P.movingKolmogorovSet_of_tube were additionally probed, each with exactly `[propext, Classical.choice, Quot.sound]`. The expanded probe rerun also exited 0, with no warnings or errors.

Kernel replay ran once, in one invocation containing the provider and every lemma module of the initial diff:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.PlanarTwoPlanetKAM KAM.Planetary.PlanarAssembly.Main KAM.Planetary.PlanarAssembly.ChartData KAM.Planetary.PlanarAssembly.Data KAM.Planetary.PlanarAssembly.DataBox KAM.Planetary.PlanarAssembly.SlowSmall
replaying KAM.Planetary.PlanarAssembly.SlowSmall
replaying KAM.Planetary.PlanarAssembly.DataBox
replaying KAM.Planetary.PlanarAssembly.Data
replaying KAM.Planetary.PlanarAssembly.ChartData
replaying KAM.Planetary.PlanarAssembly.Main
replaying KAM.Provider.Planetary.PlanarTwoPlanetKAM
exit 0
```

The six files have 72/332/83/138/92/38 lines respectively, all below 1500; their maximum Unicode line lengths are within 100 (Main maximum 96, provider 100). All use the required copyright/module/import/docstring/public-section format; definitions are in exposed sections. No new generic public HELPER name, harmful root shadow, EuclideanSpace, proof escape, resource override, provider-cycle or conclusion-shaped root hypothesis was found. Additional p12c_* names are distinctive internal construction exports.

Source lint (after kernel and probe completion):

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1163 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the generated-root exception explicitly permitted by the audit brief. KAM.lean was not regenerated. No forbidden-token, line-length, module-format, frozen-anchor or ABI failure occurred. `git diff --check` and the pinned initial comparison's `--check` exited 0. The report itself was separately checked for trailing whitespace, balanced code fences and control characters because it is untracked.

## Uncertainties, source defects and closeout

No new suspected pinned-source erratum, false frozen statement or blueprint contradiction was found in the terminal assembly. The Part 12 documented fast-lattice transport and smaller-radius corrections are preserved. The inherited further radius shrink is explained above. No audit-introduced mathematical deviation exists.

The source-characterization/delivery gates in design lines 64–68 remain owned by the separate upstream package audits, especially P12-C: this report validates its exact consumer interface and axiom closure, and does not independently recertify all underlying celestial-mechanics/source-gap claims. There is no newly assumed helper, hard-step instance or unexplained source premise in P12-E. Its actual P-G input is SEALED, and its physical consumers have the exact required conclusions.

Audit-owned scratch probe and redirected logs were removed after their receipts were transcribed here. HEAD remained `60bf4fa595ebb129c067561dae2b860015cd4000`; only the requested report was added by this audit. The pre-existing untracked P12-E-handoff.md was left untouched. No production source, frozen file, manifest, generated file or git state was changed.

**Final disposition:** P12-E's exact terminal provider and prospective seal pass; all assigned slice nodes are covered. PASS WITH NOTES records only the permitted stale generated root, external movement of inp, and the separate scope of upstream source audits. Sealing is an orchestrator action, not performed by this audit.
