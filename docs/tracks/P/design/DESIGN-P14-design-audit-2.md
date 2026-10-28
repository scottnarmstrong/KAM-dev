# P14 design audit 2 — revision 2 delta

**Overall verdict: PASS.** All five findings F1–F5 of audit 1 are resolved in the actual revised contracts. No new blocking finding was found in the changed statements, their consumers, package assignments or supplier interfaces. The implementation and upstream-release notes remain active; this is design approval, not proof closure.

## Scope and immutable inputs

Audit date: 2026-10-28. Read the audit brief, AGENTS.md, PLAN, DECISIONS, audit 1 and the revision-2 handoff. Applied the same manuscript-audit refutation procedure as audit 1. Reviewed the complete `19d3948...213cfed` design delta and every affected source/packet contract. The original signatures and all production/frozen files remained read-only; only this report is a new persistent change from this audit.

- Revision: `213cfed6606dcde29841ff4f5e2b1c87cdfebbc7`, branch `inp-design-p14`; parent `19d394844f5b9ce0c87aa12832413e9ddc6e893a`.
- Design: `docs/tracks/P/design/P14-LEAN-DESIGN.md`, 1280 lines; SHA-256 `a283ad509cb312a6c3ea06b6d94ce031903d7d05a5604d23553c17b9b7050ef7`.
- Original signatures: `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, 755 lines; SHA-256 `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`.
- Handoff: `.drafts/handoff-DESIGN-P14.md`; SHA-256 `226a275d6112881c5b785f646fc68ea84a079d24aa024390009e50e4d278d847`.
- Audit 1: SHA-256 `9a94441633c8c404710bc5872fabf6a7c52a94f950f96f38dd30e01f74498f8a`.
- Blueprint a (`p14a-amd-expsafe.tex`): SHA-256 `a2735bd6fbc36dc765bafccac43af4e3742b101a7e0f2d97725e70ac37ff8452`; blueprint b (`p14b-secular-box.tex`): SHA-256 `f14536c948f27bc9ccb330b5df0b482846696aa7ea10283d42ee2569be2d0ae7`. Both match audit 1.

The revision commit changes only the design Markdown. Declaration-level comparison of Appendix A at the two commits finds exactly five changed signatures (`elements`, `eccentricity_deficit`, `real_domain`, `h_data`, `uniform_data`), three added signatures (`angle_quadrature`, `interval_constancy`, `complex_division`), no removals and no changed definitions/structures. The other 42 theorem signatures retain their prior statement audit. All 50 declarations are elaborated together afresh; the full ledger below accounts for every signature.

## Earlier findings: disposition and refutation checks

S denotes the revised original signatures; D denotes the revised design. Line locators refer to the hashes above. Source labels are matched against the actual blueprint and `docs/graph/P/packets/P-p14a1.nodes.md`, `P-p14a2.nodes.md`, `P-p14b.nodes.md`.

| Finding | Earlier severity | Revision-2 evidence | Verdict |
|---|---|---|---|
| F1: constants/dependence | Major | S276–298 / D799–821; a195–200, packet `bpP:p14:h-data`. Lower-bound and attaining-index clauses characterize each finite minimum; M is the exact sum. Coordinate margin is an explicit conclusion. | CLOSED / PASS |
| F2: unrelated planet premises | Medium | S126–163 / D649–686; a42–53, packet `bpP:p14:elements`. Four scalar premises refer only to the selected i. All elementary element clauses and the separate threshold deficit are present. | CLOSED / PASS |
| F3: quantitative pair margin | Medium | S257–266 / D780–789; a184–187, packet `bpP:p14:real-domain`. Explicit distance/2 lower bound for every i≠j. | CLOSED / PASS |
| F4: delta upper bound | Low | S333–341 / D856–864; a239–241, packet `bpP:p14:uniform-data`. Returns UniformData and delta≤pi together. | CLOSED / PASS |
| F5: unusable Mathlib interface | Medium | S98–111 / D621–634 and D41–50, D295–296. Correct `_right` FTC name and exact interval-constancy/multivariable-division wrappers; actual APIs checked independently. | CLOSED / PASS |

**F1 refutation check.** Existential placement after rho no longer enlarges the dependence. If g and g' satisfy the two minimum characterizations, evaluating each lower-bound clause at the other's attaining index gives g≤g' and g'≤g. The same applies to v; the equality for M fixes it directly. Thus different rho,e,A choices cannot change these constants at fixed mass/lower/upper/kappa data. Positive planet count guarantees an attaining index exists, and positivity follows from admissibility and positive denominators. The coordinate margin has the correct direction `0 < 5*lower/8 ≤ lower-3*kappa ≤ Re z`. Negated holomorphy, C2, reality and Hessian-bound bridges remain expressly assigned to E4; both frozen definite-fast-part predicates are exported. No new assumption is substituted for an analytic result.

**F2 refutation check.** Frozen `ProgradeElliptic` unfolds to exactly the four-conjunct pointwise premise now accepted by the two helpers. Every global AMD/dictionary consumer can pass `hz i`. The stronger element conclusion exposes C≤Lambda, nonnegative eccentricity and deficit, and both dot-product identities. These are the source's own conclusions and are valid without conditions on any other planet. The revision neither weakens those conclusions nor changes the physical carrier.

**F3 refutation check.** The quantified pair conclusion lies outside the per-planet radial conjunction, so both i and j are independently quantified and the result covers both index orders. The source proof for i<j transfers by symmetry of planar length. `original_cylinder_subset` still supplies the final source inclusion. The stronger conjunction only changes how E3 consumers project its former pointwise bounds; no former hypothesis is lost.

**F4 refutation check.** UniformData still supplies strict positivity and all closed-ball estimates; the new upper-bound conjunct is not a replacement for these fields. Either choosing the smaller radius initially or shrinking it preserves all estimates. E9 can project the first conjunct, and users needing the radian compact-cell cap can project the second.

**F5 refutation check.** `angle_quadrature` has the correct Fin 2→ℝ output for the two fast angles and uses no period or time rescaling. Continuity supplies interval integrability, endpoint-filter strong measurability and endpoint continuity to `intervalIntegral.integral_hasDerivAt_right`, including at t=0 and negative t. `interval_constancy` needs only the actual scalar conservation law on J. The design's convex-set proof handles non-unique differentiation points using the checked scalar-domain `fderivWithin_zero_of_not_uniqueDiffWithinAt`, so singleton/empty sets and endpoints need no extra premise. `complex_division` takes arbitrary complex phase-product domains and nonvanishing denominator there; `DifferentiableOn.inv` and `.mul` have the needed generic domain type. The scalar-domain division and whole-line constancy interfaces are no longer claimed as the suppliers. All three wrapper statements are mathematically valid; their proofs remain future package work.

## Full signature ledger

Names are in `KAM.Planetary` unless prefixed `Provider.Planetary`, meaning `KAM.Provider.Planetary`. Labels `p14:*` mean `bpP:p14:*`; source step suffixes identify internal proof obligations. Unchanged rows retain the bounded statement/source conclusions of audit 1, not a claim to have proved their bodies.

| Lean name | Blueprint label / obligation | Verdict | Reason |
|---|---|---|---|
| `local_complex_restriction` | `p7:ho-hol; p14:x-hol` | PASS | Local derivative restriction, no strip hypothesis. |
| `local_analytic_complexification` | `p14:x-cx` | PASS | Local real-to-complex extension; radius is existential. |
| `real_trace_identity` | `p14:x-id; tb-glue, tb-per` | PASS | Intersections of real-centred max balls; empty intersections harmless. |
| `secular_parametric_integral` | `p14:sb-sm-3; p8:e-diff` | PASS | Finite-order compact-parameter integral; C∞ obtained for every finite order. |
| `angle_quadrature` | `p14:sb-x-int; sb-gl-1` | PASS | Correct continuous Fin 2-valued integrand and two-sided FTC at every t. |
| `interval_constancy` | `p14:x-calc; am-const` | PASS | Interval-local derivatives; empty/singleton/endpoint cases require no added premise. |
| `complex_division` | `p14:x-hol; hd-ii` | PASS | Correct multivariable complex product carrier; inverse and multiplication APIs apply. |
| `elements` | `p14:elements` | PASS | Local four-scalar premises; all (a)–(f) clauses, threshold split below. F2 closed. |
| `eccentricity_deficit` | `p14:elements(f)` | PASS | Selected-planet premises only; existing consumers supply hz i. F2 closed. |
| `ecc_bound` | `p14:ecc-bound` | PASS | All-planet ellipticity is needed here to control every deficit summand. |
| `geometry` | `p14:geometry` | PASS | Geometry plus amdCompact membership; elementary radial clauses also available from elements. |
| `amd_compact` | `p14:geometry, geo-k` | PASS | Exact compact collision-free set, split from geometry. |
| `closure` | `p14:closure` | PASS | Sequential collar closure and outer openness; continuity split below. |
| `element_continuity` | `p14:closure(a)` | PASS | Exact negative-energy domain; arbitrary fixed masses cause no continuity problem. |
| `moving_ode` | `p14:moving-ode` | PASS | Literal frozen predicate bridge and C1 field; negative field follows by negation. |
| `ang_mom` | `p14:ang-mom` | PASS | OrdConnected real time set; actual scalar angular momentum. |
| `enlarge` | `p14:enlarge` | PASS | All E1–E3 fields are source geometric inequalities. |
| `sec_domain_chart_facts` | `p14:ch-elements; sec-domain#chart-facts` | PASS | General n; remaining energy/eccentricity formulas derive using elements and the displayed dictionary. |
| `real_domain` | `p14:real-domain` | PASS | Explicit distance/2 margin for all distinct pairs and radial/eccentricity bounds. F3 closed. |
| `original_cylinder_subset` | `p14:real-domain(last)` | PASS | Separate exact inclusion. |
| `h_data` | `p14:h-data` | PASS | Attained minima and exact sum force width-independent witnesses; real-coordinate margin present. F1 closed. |
| `chart_perturbation_analytic` | `p14:ch-split; p7:pc-share` | PASS | Explicit real-analytic obligation on chartSafe. |
| `tube` | `p14:tube` | PASS | Periodic complex tube, real agreement and membership; empty compact set allowed. |
| `perturbation` | `p14:perturbation` | PASS | Both P and -P; fixed B0 before mu; normalized frozen perturbation. |
| `uniform_data` | `p14:uniform-data` | PASS | UniformData plus delta≤pi; positive delta retained in the structure. F4 closed. |
| `lift` | `p14:lift` | PASS | ChartSafe, physical projection and two-sided derivative on the closed segment; action/AMD bounds follow from hout and dictionary. |
| `hnu` | `p14:hnu` | PASS | Pointwise equality on open workingCylinder; field/differentiability bridges explicitly assigned to E10. |
| `stopped` | `p14:stopped` | PASS | B0 and nu0 before all mu,T,delta,z0; actual frozen stopped predicate. |
| `sb_numerics` | `p14:sb-numerics` | PASS | Every N1–N7 rational and the unused source chain are present. |
| `sb_chart` | `p14:sb-chart` | PASS | Actual frozen formulas; positive radius follows from positive mass/action and e<1. |
| `sb_cov` | `p14:sb-cov` | PASS | All-point strengthening survives total divisions/sqrt; omitted scalar equalities unfold from invariant Gamma and unchanged actions. |
| `sb_s` | `p14:sb-S, sb-Sdef` | PASS | Open S and required safe geometry; quantitative intermediate radii/radicand are internal Region obligations. |
| `sb_smooth_prop` | `p14:sb-smooth-prop` | PASS | Integral identity/smooth integrand split into next two helpers; literal SecularRegular. |
| `secular_integrand_identity` | `p14:sb-sm-1` | PASS | Exact frozen integrand after assemble; no assumed alternative average. |
| `secular_integrand_smooth` | `p14:sb-smooth-prop(b)` | PASS | Joint C∞ and global F periodicity. |
| `sb_rot` | `p14:sb-rot` | PASS | S membership and exact averaged-Hamiltonian invariance. |
| `sb_pred` | `p14:sb-pred` | PASS | Frozen Iso predicate; C2/C1 supplied by Smooth and ODE/Hamiltonian. |
| `sb_field` | `p14:sb-field` | PASS | Zero fast-action velocity and AMD derivative cancellation; other components in next helper. |
| `secular_field_components` | `p14:sb-fd-1` | PASS | Fast angle derivative and reduced slow field in correct coordinate order. |
| `sb_slow` | `p14:sb-slow` | PASS | Actual reduced flow in open slice and conserved AMD; no unbounded-angle compactness claim. |
| `sb_global` | `p14:sb-global` | PASS | Global frozen solution predicate, S membership, exact constants of motion. |
| `sb_unique` | `p14:sb-unique` | PASS | Agreement-set proof supports dropping competitor regularity. |
| `amd` | `p14:amd; p0:amd` | PASS | Frozen telescope, formatting normalized. |
| `expsafe` | `p14:expsafe; p0:expsafe` | PASS | Frozen telescope; constants before mu,z0. |
| `sb_safety` | `p14:sb-safety` | PASS | Frozen telescope including competitor regularity and every F. |
| `sb_cited` | `p14:sb-cited` | PASS | Exact rational specialization. |
| `Provider.Planetary.amdConfinement` | `p14:amd; p0:amd` | PASS | Exact frozen provider telescope. |
| `Provider.Planetary.planetaryExponentialSafety` | `p14:expsafe; p0:expsafe` | PASS | Exact frozen provider telescope. |
| `Provider.Planetary.secularBoxSafety` | `p14:sb-safety` | PASS | Exact frozen provider telescope. |
| `Provider.Planetary.secularBoxAtCitedMasses` | `p14:sb-cited` | PASS | Exact frozen provider telescope. |

## Consumers, frozen objects, definitions and packages

**Consumers: PASS.** Rechecked A1's callers after the selected-index binder change, A2/A3 deficit consumption, E3 quantitative geometry, E4→E11 data selection, E8→E9 UniformData projection, A5's conservation law and S9's angle quadrature. The extra h_data conjunctions require different projections when implemented, but preserve every hypothesis needed by the frozen N root. N still has n fast actions and k=n slow pairs; no exponent, Hessian norm, erosion, sign or interval-duration convention changed. Negative times still use the negated Hamiltonian and perturbation. E11's proof-release condition remains explicit.

The independent F5 wrappers fit the actual consumer carriers: real scalar conservation, a Fin 2-valued quadrature and generic complex phase-product calculus. The surrounding chart/physical interface still uses the phaseCast/poincareProdCast bridge. The fixed-system constants of expsafe still precede mu and z0; the frozen stopped premise is not added to expsafe. The secular result remains about the exactly averaged model, with the actual frozen solution and regularity predicates.

The prescribed I/P/N consumer-search conclusions from audit 1 remain applicable: neither blueprint nor external consumer sources changed in this delta. No direct P14 consumer outside its own two parts was introduced. No shared ODE signature is replaced or narrowed by the new wrappers.

**Frozen objects: PASS.** Re-read the local frozen ProgradeElliptic body, the affected Kepler formulas, HasDefiniteFastPart and the exact N root telescope, and checked the existing UniformData fields. All eight ordinary/provider root telescopes remain byte-identical to their four frozen targets. No frozen definition is replaced with an assumed-equal object, no new frozen hypothesis is introduced, and no frozen file/manifest was edited.

**Definitions/structures: PASS.** All 19 definitions and the single EnlargedData structure are byte-for-byte unchanged at the declaration level. No instance or conclusion-shaped structure field is added. All three new declarations are theorem contracts with source calculus premises, not new axioms or hypotheses on the final targets.

**Packages: PASS.** A5 owns interval_constancy, E5 owns complex_division and S9 owns angle_quadrature. E4 now explicitly depends on E5 in both the package table and DAG; E5 is wave 1 and E4 wave 3, so no cycle or wave inversion is introduced. Module estimates remain 150–750 lines, below the 1500-line cap. The 755-line scratch is also below that cap. No resource override or provider-quarantine bypass is introduced.

## Numbered notes and proof-release status

**N1 — Medium, implementation risk; retained and addressed as a release gate.** D38 and the Revision 2 narrative require successful default-resource proofs of E5/E6 and S4 before dependent analytic/dynamic waves are released. These are still substantial complexification, gluing and parameter-integral obligations. The design gate is now explicit; signature elaboration does not discharge it. Proposed action: enforce those proof checks before starting the dependent packages and split modules if needed.

**N2 — Medium, upstream availability; retained and addressed as a release gate.** The inspected `PartialConvexNekhoroshev.lean` anchor body remains `by sorry`. D39 and the handoff require an ordinary proof export or independently audited sealed anchor with the exact telescope before E11 is released. Proposed action: enforce that prerequisite and retain provider quarantine. This audit makes no N-root proof-closure claim.

No unresolved F finding remains, and no new pinned-source erratum or source deviation was identified. The notes concern future proof work, not a defect in a revised signature. A corrected-signature block is therefore unnecessary in this delta report.

## Independent verification

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-p14 .drafts/scratch/P14Signatures.lean
exit 0
50 warnings: declaration uses sorry
0 other diagnostics
```

A separate `.lake/abi-scratch/P14R2AuditProbe.lean` probe imported the necessary calculus modules and copied the four unchanged root signatures for axiom inspection. Through the same gate it returned exit 0, four expected sorry warnings, successful output for all nine #checks and no errors. The checked APIs were:

- `intervalIntegral.integral_hasDerivAt_right`;
- `Convex.is_const_of_fderivWithin_eq_zero`;
- `fderivWithin_zero_of_not_uniqueDiffWithinAt`;
- `DifferentiableOn.inv` and `DifferentiableOn.mul` (generic domain E, not scalar-only);
- `HasDerivAt.hasFDerivAt`, `HasFDerivAt.hasFDerivWithinAt`, `HasFDerivWithinAt.fderivWithin`;
- `Set.OrdConnected.convex`.

The probe independently printed the axioms of `amd`, `expsafe`, `sb_safety`, `sb_cited`. Each was `[propext, sorryAx, Classical.choice, Quot.sound]`, as expected for admitted design signatures. This is not a proof certificate.

Lint was rerun after the API probe, with the existing adapter routing its ABI Lean invocation through the shared gate:

```text
PATH="$PWD/.drafts/gated-bin:$PATH" LEAN_NUM_THREADS=1 scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The revision diff passes `git diff --check HEAD^ HEAD`. The report has no trailing whitespace and balanced code fences. `git status --short` shows the pre-existing audit-1 report and the new audit-2 report only. No earlier artifact was edited.

The signature gate uses the shared `/root/code/KAM-inp` compiled environment because this design worktree has no private build snapshot. Calls are sequential, with `LEAN_NUM_THREADS=1`, `nice -n 5` and default Lean resource limits. No production build was necessary for a Markdown-only design audit; no clean, update, cache download or broad rebuild was performed. The full revised signatures were elaborated once.

Static checks independently confirm 50 theorem rows, 20 unchanged definition/structure declarations, all eight exact frozen telescopes, and all 182 scoped graph IDs (45+56+81) with no missing or extra row. Appendix A agrees with the original revised signatures up to the trailing blank line around its code fence. Original hashes are rechecked at closeout. Temporary ABI probes are removed; audit 1 and the original signatures are preserved.

The PASS verdict closes the design delta only. Every admitted theorem still requires implementation, its own validation and axiom audit; no provider or frozen root is sealed by this report.
