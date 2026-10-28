# Lean design for planetary Parts 12–13

Design draft, Revision 2, 2026-10-28, branch `inp-design-p1213`. This is a design and signature receipt, not a proof or an approval to freeze. Frozen anchors and the manifest are unchanged. The format model is `docs/tracks/P/design/KEPLER-LEAN-DESIGN.md`, read including its appendix and amendments. The brief and common rules were reread after the orchestrator's source-gap amendment.

## Decisions

1. P-PLANAR and the two-planet P-FIXED route use **P-G after sealing**, the actual product Poincaré chart, and the Part 11b Birkhoff construction. P-FIXED at general dimension uses Part 11's `wrapper`. No KAM theorem is reproved here.
2. Prove direct **fast-lattice** Cartesian-cylinder transport and measure the image through the half-open fast cell. Do not apply Part 1's full-position-lattice measure theorem or infer winding of the slow discs. Keep the original period-one frequency unchanged in physical time.
3. Select the chart, domains, action boxes and secular jets jointly, before the coupling. The exact consumer-level signatures `PlanarAssembly.pg_hypotheses` and `FixedAssembly.pg_hypotheses` conclude the entire shared existential plus all P-G and chart clauses. They assume only the respective frozen root's physical premises. No structure or proposition definition packages unpaid conclusions as assumptions.
4. The names `data`, `chart`, `pg-hypotheses` in the blueprint describe successive clauses of this single existential construction. Their graph records map to that joint declaration; internal lemmas have descriptive names. This avoids independently choosing incompatible charts or torsion witnesses. The finer Part 8/11b objects retain their upstream names and source characterizations; the upstream-interface table is a reconciliation gate, not a license to invent their types.
5. Use `r0 = r*/2`, not the endpoint `r*/√2`: P-G requires analyticity on the **closure** of its cylinder. Choose `r = min rG (√(δ/2))/2`, then `mu0 = min 1 (r^6/(log(1/r))^c)`. The radius and threshold are positive and independent of the later coupling. Recompute the P-G constants for the fixed perturbation.
6. Keep source-defined objects literal. `kepler_h` is a restriction of existing `hProd`, not a replacement formula. `perturbation` is a constant coupling family composed with existing total `fMov` or `fFix`; `total_chart` is the total composition of the existing product chart with the supplied Birkhoff map. Values away from the analytic open set are never used. No new zero/default branch or arbitrary choice definition is introduced.
7. Repeated slugs in Parts 12 and 13 are disambiguated by nested namespaces `KAM.Planetary.PlanarAssembly` and `KAM.Planetary.FixedAssembly`; within them, exported source result slugs use snake_case. Provider exports keep their exact registered names.
8. The orchestrator's `aa7bc30` status sync leaves P7 product-chart (b)'s derivative/analyticity claims unexported. **P12-B owns `PlanarAssembly.product_chart`**, a joint exact signature for analyticity on positive actions, the gradient/frequency, diagonal Hessian (including cross entries and nonzero diagonal), and Kepler decoupling through the existing chart. `hasDerivAt_nu` is only a derivative of the scalar frequency, not an assumed proof of these claims. No unexported quotient/local-diffeomorphism or P7 transport API is consumed: direct transport below uses the genuinely exported analytic/symplectic/lattice facts and Part 1's local tools. d25(e) is not a dependency of either assembly.
9. This design proves no bodies. All scratch theorem bodies, including the provider signatures, are `sorry`. The only scratch dependency prelude copies five literal `Newtonian/Tube.lean` definitions whose shared-build olean is absent. It is not an implementation module and must be replaced by the owning import when that artifact is available.

## Carriers and standing data

| Object | Exact carrier or definition | Use |
|---|---|---|
| planar source and target | frozen `Phase 4`; `Phase (2+2)` and `Phase (2*2)` reduce to it | no equality transport needed for two planets |
| general physical space | frozen `Phase (n*2)` | `subst n` in the two-planet branch; never replace general `n+n` by definitional equality |
| action/fast-angle/oscillator blocks | `Fin 2 → ℝ`; frozen `fast`, `slow`, `assemble` | `assemble I phi p q = ((phi,q),(I,p))` |
| physical body blocks | frozen `bodyVector`, using `finProdFinEquiv` | keep the Sun at index zero with `Fin.cons` |
| chart/Birkhoff map | `Phase 4 → Phase 4` | `poincareProd m (G*m0) ∘ T` |
| domains | `Set (Fin 2 → ℝ)`, `Set (Phase 4)` | raw sets, no parallel chart carrier |
| jets | `P0 : ℝ → (Fin 2 → ℝ) → ℝ`, `Ω : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)`, `β : ℝ → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ` | exactly the frozen Birkhoff predicate |
| phase parameters/frequencies | `Fin d → ℝ`; periods `Fin d → ℤ` | phase period one, fast chart period `2π` |
| geometry | existing `AxisData`, `axisGap`, `axisMax`, `tubeRadius`, `tubeD`, `tubeBigD` | obtain canonical axis data from ordered positive axes |

No new standing structure is introduced. The parameters `G,m0,m,a,eta` and their signs/order are the frozen premises. Generic transport and measure statements have the actual **local** source hypotheses (chart regularity, lattice clauses, a cylinder torus/set and domain inclusion). They are never extra premises of `planar`, `n2`, `n_general`, `fixed`, or a provider. Helpers explicitly named `*_of_*` are conditional tools, not source-result certificates.

## Reuse and exact upstream interfaces

The following names were checked in current implementation sources or the delivered design signature files. None may be shadowed by a new implementation declaration.

| Owner | Exact names consumed | What is supplied and consumed |
|---|---|---|
| `KAM/Planetary/Poincare/Product.lean` (P7-5) | `poincareProd`, `poincareProdDom`, `planetBlock`, `hProd`, `analyticOnNhd_poincareProd`, `poincareProd_symplectic`, `poincareProd_lattice`, `poincareProd_eq_iff`, `keplerPart_poincareProd`, `movingHamiltonian_poincareProd`, `fixedHamiltonian_poincareProd`, `hasDerivAt_nu`, `analyticOnNhd_fMov_poincareProd`, `analyticOnNhd_fFix_poincareProd` | positive masses and `0<G*m0`, point in product domain; obtain analytic symplectic chart, lattice iff, total splitting and perturbation analyticity |
| P12-B, locally owned completion of `bpP:p7:product-chart` (b) at p7 L197/L206 | `PlanarAssembly.product_chart` | prove h analyticity, gradient, frequency derivative/Hessian and decoupling; **not delivered by P7-5**, exact declaration in Appendix A |
| `KAM/Planetary/Poincare/Tube.lean` (P7-6, designed) | `circularPoint_eq_poincareProd`, `tube_in_chart` | exact signature in `KeplerSignaturesP.lean`; circular identity enters forward-tube; converse tube inclusion is not substituted for the new forward direction |
| `KAM/Planetary/Newtonian/Tube.lean` (P6-4) | `axisData_canonical`, `tubeRadius_pos`, `tubeD_lt_tubeBigD`, `circularTube_mono`, `circularTube_pair_bounds`, `circularTube_pairBounds_barycentric`, `circularTube_pairBounds_fixed`, `newton_in_tube`, `fixed_in_tube` | `AxisData a (axisGap a) (axisMax a)` and radius `≤axisGap a/6`; exact pair bounds, no collision, all-time orbit clauses via reconstruction |
| `KAM/Planetary/Newtonian/Assembly.lean` (P6-5, designed) | `volume_lt_top_of_subset_circularTube`, `movingKolmogorovSet_of_tube`, `fixedKolmogorovSet_of_tube` | **unchanged exact Kepler signatures**: measurable set in `circularTube ... (tubeRadius eta gamma)` and whole physical torus witnesses; conclude frozen Kolmogorov predicates with `tubeD gamma`, `tubeBigD gamma A` |
| `KAM/Planetary/Newtonian/Reconstruction.lean` | `orbit_transfer_moving`, `orbit_transfer_fixed`, `reconstruction_all_time`, `reconstruction_fixed_all_time` | two physical reconstruction alternatives; fixed versions quantify arbitrary real epsilon |
| `KAM/Planetary/Hamiltonian/Chart.lean` (P Part 1, designed) | `IsChart`, `IsChart.comp`, `IsChart.bijective_fderiv`, `chart_field_differentiableAt_iff`, `chart_field`, `chart_orbit` | build `IsChart 1 Ψ O` from its **existing** analytic/symplectic conjunction; local Hamiltonian equality is transferred on the open set before differentiation |
| `KAM/Planetary/Hamiltonian/Transport.lean` (P Part 1, designed) | `fderiv_chart_comp_torus` | exact derivative chain rule only; do not force frozen cylinder tori into `IsLatticeTorus` |
| `KAM/Planetary/Hamiltonian/Liouville.lean` (P Part 1, designed) | `chart_measure_image` | apply existing theorem at `c=1`, `A=S∩cylinderCell`; its InjOn implication gives volume equality; no use of full-lattice `measure_chart_image` |
| `KAM/Kepler/Basic.lean` | `IsSymplecticOn`, `IsSymplecticOn.comp` | use existing predicate; its chain rule requires explicit differentiability on both open domains |

### Upstream interface (to reconcile)

These neighbours have no delivered exact signatures in the supplied list. The table fixes only the **needed shape**, not a guessed full declaration. Names follow graph slugs in namespace `KAM.Planetary`; module subnamespaces, if introduced by the owner, must be reconciled before proof assignment. No upstream theorem is assumed as an additional binder in a source-facing result here.

| Graph node / intended name | Carriers and premises we can supply | Conclusion consumed; required reconciliation |
|---|---|---|
| `bpP:p5:main` / `KAM.Planetary.main`; frozen `KAM.Planetary.properlyDegenerateKAM` | `a=b=2`, the **entire exact frozen** P-G argument list from the joint output | `rG,C,c` before `r,mu`, all five positive/strict radius and constant bounds, cylinder Kolmogorov set plus **explicit positive cell volume**. Assembly imports only the SEALED frozen P-G anchor; it never imports its provider or an unsealed anchor. Part 5 implementation naming is not presumed usable across quarantine. |
| `bpP:p8:identification` / `identification`; `same-jets` / `same_jets` | existing `fMov/fFix` in the product chart, positive physical data, collision-free action patch | equality of averages up to an **action-only** function; unchanged slow jets and hence identical `Ω=2σ`, `β=beta-hat`; fixed `P0=C0`, moving `P0=C0+δS`. Obtain actual owner definitions and characterization, not arbitrary jet witnesses. |
| `bpP:p11b:patch` / `patch` | the same positive ordered two-planet data, any positive axis-neighbourhood radius | a smaller closed axis cube in the given neighbourhood, nonzero `Φ4` and torsion determinant throughout a surrounding open set; positive minimum `B` on the compact cube |
| `bpP:p11b:beta-def` / `beta_def`; `remain` / `remain` | cube and same secular normalization | real symmetric torsion, determinant bounded below by its compact minimum; exact `1/2 Σ βij Ri Rj` normalization in frozen `HasSecularBirkhoffForm` |
| `bpP:p11b:lift-map` / `lift_map`; `flow` / `flow` | compact cube with a collar; real analytic quartic generator and nonresonance | **one** total map `T` on an open `O`, analyticity, symplecticity, injectivity, fast-action preservation, fast-shift equivariance, `sum slow squares` growth `≤2` under the quartic flow; source gaps below must be paid |
| `bpP:p11b:birkhoff-form` / `birkhoff_form` | positive physical data and that cube | common `T` for fixed and moving perturbations, image in actual collision-free Poincaré domain, positive `r*`, analytic open action collar, averaged expansion with `O(|z|^6)` and the **actual** `P0,Ω,β`; frozen HasSecularBirkhoffForm for smaller disc radius. Need `closure C(V,r*/2) ⊆ O`, not merely open-cylinder inclusion. |
| `bpP:p11:wrapper` / `KAM.Planetary.wrapper` | `n≥2`, exactly the original frozen physical data/sign/order/eta premises | threshold before epsilon; for each epsilon, Borel `S` with positive finite volume, inclusion in `tubeRadius eta (axisGap a)`, and at each point whole physical torus data for `fixedHamiltonian G m0 m eps`. Frequency can depend on the point. No uniform Diophantine constant is demanded. |

### Characterization and delivery gates (P12-C / P13-A)

Before assigning either package, its brief must bind the exact owner declaration names and full characterization types for the actual axis cube, `C0`, `δS`, `σ`, `beta-hat` and the Birkhoff map. Require certificates of `P0mov=C0+δS`, `P0fix=C0`, `Ω=2σ`, `β=beta-hat` on that same cube and domain, and one jointly constructed T used by both models. Use the upstream common construction directly, or prove distinct local characterization lemmas from those exports; two independently eliminated existence statements cannot identify their witnesses. No guessed upstream signature or extra root premise may fill this gate. The two `pg_hypotheses` outputs are consumer projections for P-G and physical assembly, not certificates of these finer source claims.

Every package brief must also carry its applicable SOURCE_GAP rows below and require delivery plus a proof/axiom audit of every consumed upstream result. P12-C/P13-A specifically retain analytic-eigenframe, uniform real-flow existence and real-versus-holomorphic Lie/Taylor/symplectic applicability gates. P12-D retains the Part 1 and P6-5 delivery gates; P12-A retains P7-6 delivery. P12-E/P13-B cannot import P-G until sealed. P13-C additionally requires the actual Part 11 K1–K6 chain and P6-5 audit. An analytic real generator alone does not meet N’s holomorphic small-field hypotheses. These are assignment gates; this revision does not claim their mathematical discharge.

## Node to declaration table

This table covers **every graph node whose STATEMENT_SOURCE is in the two assigned files**, including external facts, definitions, choices, route nodes and proof steps. A step mapped to its enclosing theorem is proved **inside** that theorem; it is not a new premise or a separate global theorem. Source definition/choice records map to raw definitions or shared existential elimination. The result's statement and proof locators are copied from the current graph; the cited blueprint files are the source authority.

In the table, unqualified new declarations belong to `KAM.Planetary.PlanarAssembly` unless the row explicitly names `FixedAssembly`; exact upstream declarations are in the reuse tables. The supplementary `bpP:p7:product-chart` (b) completion is assigned to P12-B in the reuse table and Appendix A; it does not replace or expand the 89-node local scope. `P12:` and `P13:` locators below are not inferred from graph titles: full paths and author labels are retained.

| Graph node | Declaration / proof assignment | Package | Statement locator | Proof locator |
|---|---|---|---|---|
| `bpP:p13:fixed-hamiltonian-form` | `FixedAssembly.fixed_hamiltonian_form`; exact `fixedHamiltonian_poincareProd` | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:fixed-hamiltonian-form@L51-L61` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:fixed-hamiltonian-form@L62-L66` |
| `stepP:p13:fh-chart` | `FixedAssembly.fixed_hamiltonian_form`; exact `fixedHamiltonian_poincareProd` | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fh-chart@L63-L63` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fh-chart@L63-L63` |
| `stepP:p13:fh-id` | `perturbation_difference`; upstream `identification`, `same_jets` (8), `beta_def` (11b) | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fh-id@L64-L64` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fh-id@L64-L64` |
| `stepP:p13:fh-bnf` | upstream `birkhoff_form` (11b), fixed branch; conclusions in `FixedAssembly.pg_hypotheses` | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fh-bnf@L65-L65` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fh-bnf@L65-L65` |
| `bpP:p13:data` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:data@L72-L88` | `-` |
| `bpP:p13:chart` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:chart@L90-L93` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:chart@L94-L97` |
| `stepP:p13:ch-same` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ch-same@L95-L95` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ch-same@L95-L95` |
| `stepP:p13:ch-ham` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ch-ham@L96-L96` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ch-ham@L96-L96` |
| `bpP:p13:pg-hypotheses` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:pg-hypotheses@L99-L101` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:pg-hypotheses@L102-L109` |
| `stepP:p13:pg-sets` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-sets@L103-L103` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-sets@L103-L103` |
| `stepP:p13:pg-h1` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h1@L104-L104` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h1@L104-L104` |
| `stepP:p13:pg-h2` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h2@L105-L105` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h2@L105-L105` |
| `stepP:p13:pg-h3` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h3@L106-L106` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h3@L106-L106` |
| `stepP:p13:pg-h4` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h4@L107-L107` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h4@L107-L107` |
| `stepP:p13:pg-h56` | `FixedAssembly.pg_hypotheses`, `chart_of_preserves_fast`; shared geometric chart construction | `P13-A` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h56@L108-L108` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:pg-h56@L108-L108` |
| `bpP:p13:transport` | reuse `PlanarAssembly.transport`, `measure`, `measure_in_tube` at fixed Hamiltonian | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:transport@L111-L113` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:transport@L114-L117` |
| `stepP:p13:tr-torus` | reuse `PlanarAssembly.transport`, `measure`, `measure_in_tube` at fixed Hamiltonian | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:tr-torus@L115-L115` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:tr-torus@L115-L115` |
| `stepP:p13:tr-meas` | reuse `PlanarAssembly.transport`, `measure`, `measure_in_tube` at fixed Hamiltonian | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:tr-meas@L116-L116` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:tr-meas@L116-L116` |
| `bpP:p13:n2` | `FixedAssembly.n2` (new P-G application) | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:n2@L119-L123` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:n2@L124-L131` |
| `stepP:p13:n2-const` | reuse `secular_radius`, `coupling_threshold`, `radius_choices`; fresh fixed P-G constants | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-const@L125-L125` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-const@L125-L125` |
| `stepP:p13:n2-pg` | `FixedAssembly.n2` (new P-G application) | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-pg@L126-L126` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-pg@L126-L126` |
| `stepP:p13:n2-mu` | `FixedAssembly.n2` (new P-G application) | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-mu@L127-L127` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-mu@L127-L127` |
| `stepP:p13:n2-S` | `FixedAssembly.n2` (new P-G application) | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-S@L128-L128` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-S@L128-L128` |
| `stepP:p13:n2-tori` | `FixedAssembly.n2` (new P-G application) | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-tori@L129-L129` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-tori@L129-L129` |
| `stepP:p13:n2-phys` | P6-5 `fixedKolmogorovSet_of_tube` inside `n2` | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-phys@L130-L130` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-phys@L130-L130` |
| `bpP:p13:n-general` | `FixedAssembly.n_general`; upstream `KAM.Planetary.wrapper` (11) | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:n-general@L135-L140` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:n-general@L141-L145` |
| `stepP:p13:ng-const` | `FixedAssembly.n_general`; upstream `KAM.Planetary.wrapper` (11) | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ng-const@L142-L142` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ng-const@L142-L142` |
| `stepP:p13:ng-wrap` | `FixedAssembly.n_general`; upstream `KAM.Planetary.wrapper` (11) | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ng-wrap@L143-L143` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ng-wrap@L143-L143` |
| `stepP:p13:ng-phys` | P6-5 `fixedKolmogorovSet_of_tube` inside `n_general` | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ng-phys@L144-L144` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:ng-phys@L144-L144` |
| `bpP:p13:fixed` | `FixedAssembly.fixed` (dimension split); exact provider signature | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:fixed@L153-L156` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:fixed@L157-L161` |
| `stepP:p13:fx-split` | `FixedAssembly.fixed` (dimension split); exact provider signature | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fx-split@L158-L158` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fx-split@L158-L158` |
| `stepP:p13:fx-2` | `FixedAssembly.fixed` (dimension split); exact provider signature | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fx-2@L159-L159` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fx-2@L159-L159` |
| `stepP:p13:fx-n` | `FixedAssembly.fixed` (dimension split); exact provider signature | `P13-C` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fx-n@L160-L160` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:fx-n@L160-L160` |
| `bpP:p13:quantifiers` | reuse `secular_radius`, `coupling_threshold`, `radius_choices`; fresh fixed P-G constants | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:quantifiers@L163-L164` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:quantifiers@L164-L164` |
| `bpP:p13:data#choices` | reuse `secular_radius`, `coupling_threshold`, `radius_choices`; fresh fixed P-G constants | `P13-B` | `blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:data@L84-L85` | `blueprint-P/parts/p13-fixed-assembly.tex#stepP:p13:n2-const@L125-L127` |
| `bpP:p12:f-unif` | Mathlib `IsCompact.uniformContinuousOn_of_continuous` | `P12-A` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:f-unif@L25-L25` | `-` |
| `bpP:p12:f-mono` | `radius_choices`; Mathlib `ContDiffAt.rpow_const_of_ne` | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:f-mono@L27-L27` | `-` |
| `bpP:p12:sec-set#data` | `action_center`, frozen `assemble`, `fast`, `slow` | `P12-A` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:sec-set#data@L15-L20` | `-` |
| `bpP:p12:forward-tube` | `PlanarAssembly.forward_tube` (internal proof step where applicable) | `P12-A` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:forward-tube@L32-L35` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:forward-tube@L36-L40` |
| `stepP:p12:ft-cpt` | `compact_cell`, `compact_cell_isCompact` | `P12-A` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ft-cpt@L37-L37` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ft-cpt@L37-L37` |
| `stepP:p12:ft-uc` | `PlanarAssembly.forward_tube` (internal proof step where applicable) | `P12-A` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ft-uc@L38-L38` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ft-uc@L38-L38` |
| `stepP:p12:ft-cmp` | `PlanarAssembly.forward_tube` (internal proof step where applicable) | `P12-A` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ft-cmp@L39-L39` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ft-cmp@L39-L39` |
| `bpP:p12:collar` | `PlanarAssembly.collar` (shell inclusion/product-volume proof) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:collar@L42-L47` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:collar@L48-L52` |
| `stepP:p12:co-inc` | `PlanarAssembly.collar` (shell inclusion/product-volume proof) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:co-inc@L49-L49` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:co-inc@L49-L49` |
| `stepP:p12:co-meas` | `PlanarAssembly.collar` (shell inclusion/product-volume proof) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:co-meas@L50-L51` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:co-meas@L50-L51` |
| `bpP:p12:fast-diffeo` | `PlanarAssembly.fast_diffeo` (analytic frequency/product image/cube-root inverse) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:fast-diffeo@L54-L56` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:fast-diffeo@L57-L61` |
| `stepP:p12:fd-an` | `PlanarAssembly.fast_diffeo` (analytic frequency/product image/cube-root inverse) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:fd-an@L58-L58` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:fd-an@L58-L58` |
| `stepP:p12:fd-open` | `PlanarAssembly.fast_diffeo` (analytic frequency/product image/cube-root inverse) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:fd-open@L59-L59` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:fd-open@L59-L59` |
| `stepP:p12:fd-inv` | `PlanarAssembly.fast_diffeo` (analytic frequency/product image/cube-root inverse) | `P12-B` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:fd-inv@L60-L60` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:fd-inv@L60-L60` |
| `bpP:p12:data` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:data@L65-L72` | `-` |
| `bpP:p12:data#pg-data` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:d-pg@L73-L73` | `-` |
| `bpP:p12:perturbation` | `kepler_h`, `total_chart`, `PlanarAssembly.perturbation`; jet objects owned by 8/11b | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:perturbation@L81-L89` | `-` |
| `bpP:p12:chart` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:chart@L91-L100` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:chart@L101-L107` |
| `stepP:p12:ch-dom` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-dom@L102-L102` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-dom@L102-L102` |
| `stepP:p12:ch-chart` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-chart@L103-L103` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-chart@L103-L103` |
| `stepP:p12:ch-lat` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-lat@L104-L104` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-lat@L104-L104` |
| `stepP:p12:ch-ham` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-ham@L105-L105` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-ham@L105-L105` |
| `stepP:p12:ch-tube` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-tube@L106-L106` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-tube@L106-L106` |
| `bpP:p12:pg-hypotheses` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:pg-hypotheses@L111-L122` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:pg-hypotheses@L123-L130` |
| `stepP:p12:pg-sets` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-sets@L124-L124` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-sets@L124-L124` |
| `stepP:p12:pg-h1` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h1@L125-L125` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h1@L125-L125` |
| `stepP:p12:pg-h2` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h2@L126-L126` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h2@L126-L126` |
| `stepP:p12:pg-h3` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h3@L127-L127` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h3@L127-L127` |
| `stepP:p12:pg-h4` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h4@L128-L128` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h4@L128-L128` |
| `stepP:p12:pg-h56` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h56@L129-L129` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pg-h56@L129-L129` |
| `bpP:p12:transport` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:transport@L134-L136` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:transport@L137-L145` |
| `stepP:p12:tr-an` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-an@L139-L139` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-an@L139-L139` |
| `stepP:p12:tr-per` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-per@L140-L140` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-per@L140-L140` |
| `stepP:p12:tr-inj` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-inj@L141-L141` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-inj@L141-L141` |
| `stepP:p12:tr-lag` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-lag@L142-L142` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-lag@L142-L142` |
| `stepP:p12:tr-flow` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-flow@L143-L143` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-flow@L143-L143` |
| `stepP:p12:tr-dio` | `PlanarAssembly.transport` (direct frozen-predicate proof) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-dio@L144-L144` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:tr-dio@L144-L144` |
| `bpP:p12:measure` | `PlanarAssembly.measure`, `measure_in_tube` (cell reduction, Borel image, Liouville, tube) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:measure@L147-L149` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:measure@L150-L155` |
| `stepP:p12:me-inv` | `cylinder_set_shift` | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-inv@L151-L151` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-inv@L151-L151` |
| `stepP:p12:me-cell` | `PlanarAssembly.measure`, `measure_in_tube` (cell reduction, Borel image, Liouville, tube) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-cell@L152-L152` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-cell@L152-L152` |
| `stepP:p12:me-meas` | `PlanarAssembly.measure`, `measure_in_tube` (cell reduction, Borel image, Liouville, tube) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-meas@L153-L153` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-meas@L153-L153` |
| `stepP:p12:me-tube` | `PlanarAssembly.measure`, `measure_in_tube` (cell reduction, Borel image, Liouville, tube) | `P12-D` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-tube@L154-L154` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:me-tube@L154-L154` |
| `bpP:p12:planar` | `PlanarAssembly.planar` (P-G application and image witnesses) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:planar@L159-L163` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:planar@L164-L171` |
| `stepP:p12:pl-const` | `secular_radius`, `coupling_threshold`, `radius_choices`; witness scope in `planar` | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-const@L165-L165` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-const@L165-L165` |
| `stepP:p12:pl-pg` | `PlanarAssembly.planar` (P-G application and image witnesses) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-pg@L166-L166` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-pg@L166-L166` |
| `stepP:p12:pl-mu` | `PlanarAssembly.planar` (P-G application and image witnesses) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-mu@L167-L167` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-mu@L167-L167` |
| `stepP:p12:pl-S` | `PlanarAssembly.planar` (P-G application and image witnesses) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-S@L168-L168` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-S@L168-L168` |
| `stepP:p12:pl-tori` | `PlanarAssembly.planar` (P-G application and image witnesses) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-tori@L169-L169` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-tori@L169-L169` |
| `stepP:p12:pl-phys` | P6-5 `movingKolmogorovSet_of_tube`, used inside `planar` | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-phys@L170-L170` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-phys@L170-L170` |
| `stepP:p12:pl-phys#route-orbit` | existing `orbit_transfer_moving`, `reconstruction_all_time` (alternative route) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-phys#route-orbit@L170-L170` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-phys#route-orbit@L170-L170` |
| `stepP:p12:pl-phys#route-tube` | existing `newton_in_tube` (alternative route) | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-phys#route-tube@L170-L170` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:pl-phys#route-tube@L170-L170` |
| `bpP:p12:quantifiers` | `secular_radius`, `coupling_threshold`, `radius_choices`; witness scope in `planar` | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:quantifiers@L173-L195` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:quantifiers@L173-L195` |
| `bpP:p12:data#choices` | `secular_radius`, `coupling_threshold`, `radius_choices`; witness scope in `planar` | `P12-E` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:data@L74-L79` | `blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:data@L74-L79` |
| `bpP:p12:chart#cylinder-domain` | `PlanarAssembly.pg_hypotheses` (one joint construction); `chart_of_birkhoff`, `chart_hamiltonian_of_preserves_fast`, `birkhoff_mono_radius` | `P12-C` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-tube@L106-L106` | `blueprint-P/parts/p12-planar-assembly.tex#stepP:p12:ch-tube@L106-L106` |

## Conventions and construction details

`G*m0` is positive and every mass is positive wherever the Kepler action/frequency inverse is used. The axes are strictly increasing in Lean order, inner planet first. Derive injectivity of `a` from the frozen order premise; pass it to `axisData_canonical`. Set `gamma=axisGap a`, `A=axisMax a`, `zeta=tubeRadius eta gamma`, `d=tubeD gamma`, `D=tubeBigD gamma A`. This proves `0<d<D` before introducing the coupling. `d,D` depend only on the axes; `eta` can shrink the patch and coupling threshold.

**Forward tube.** Use `compact_cell` at `δ0=min_i LambdaStar_i/4`; it is closed and bounded in the finite Pi/Prod max norm and is contained in `poincareProdDom 2`. `IsCompact.uniformContinuousOn_of_continuous` applies to the existing analytic product chart restricted there. For arbitrary fast angles choose residues in `[0,2π)`; `poincareProd_lattice` and the circular identity reduce to this compact cell. With `δ≤δ1/2` and `δ≤δ1²/4`, the action and slow-coordinate differences are strictly below `δ1`. This is a forward direction; `tube_in_chart` proves a different implication. No use of an ambient inner-product-space carrier is needed.

**Boxes and the fast inverse.** For `V=∏(l_i,u_i)`, its `t`-collar lies in `∏(l_i-t,u_i+t) \ ∏[l_i+t,u_i-t]`. On `0<t<min_i(u_i-l_i)/2`, the difference of volumes is exactly `4t((u0-l0)+(u1-l1))`; use Lebesgue product measure and interval volumes. This is the full frontier collar, including points outside `V`. For positive action coordinates the frequency is `kappa² m_i³/I_i³`. Its open image has endpoints in reversed order. The inverse is `(kappa² m_i³/v_i)^(1/3 : ℝ)`, on positive `v_i`; analytic real powers go through `ContDiffAt.rpow_const_of_ne` at differentiability order `ω`, followed by `.analyticAt`. In P12-B, instantiate the identity/composition at this analytic order; a `C¹` or `C∞` result does not supply `.analyticAt`. `product_chart` first supplies the missing h-analyticity and gradient/Hessian export in P12-B, by finite sums of reciprocal-square functions on positive coordinates. It states all cross entries are zero and the diagonal Hessian entries are nonzero. `hasDerivAt_nu` alone proves neither this gradient identification nor open image nor inverse existence; the last two are obligations of `fast_diffeo`.

**Joint physical application data.** Choose `zeta`, forward-tube `δ`, an axis-neighbourhood `eta'`, the 11b torsion/nonresonance cube and its surrounding open set, then positive nested action boxes by the componentwise monotone action map. The images of closed/open max balls are closed/open boxes. Prove nonempty interior, `closure V=K`, connectedness, boundedness and `closure V⊆W`. Take the compact positive minimum of `|det beta-hat|` on the same cube, never a pointwise lower bound depending on `I` or the coupling. Select the 11b chart and all its jets jointly. The entire jet is transported from upstream: `P0mov=C0+δS`, `P0fix=C0`, `Ω=2σ`, `β=beta-hat`; the frozen quartic term is `(1/2)Σ βij Ri Rj`. Prove the factor dictionary before applying `HasSecularBirkhoffForm`.

With `r0=r*/2`, each point of the **closed** cylinder has real slow sum of squares `≤2r0²=r*²/2<r*²`. The action box closure is inside the open action collar, hence `closure (cylinder V r0) ⊆ O`. The constant coupling family is analytic on `ℝ×O`; compose the first/second projections, not just slice analyticity. Periodicity uses fast-shift equivariance of `T` followed by the product chart lattice theorem. The Hamiltonian identity on `O` uses exact fast-action preservation. The flow bound and orthogonal slow rotation give `Γ_i(Tz)<2r²`; the small physical radius follows from `2r²≤δ`. `birkhoff_mono_radius` transfers the frozen little-o formulation to a smaller radius with `min oldDelta r`; it also restricts the integral clause on oscillator discs.

**Transport.** Read all seven conjuncts of `IsCylinderTorus`. On the open `O`, local equality `G∘Ψ=H` identifies derivatives before invoking `chart_field` or `chart_orbit`. Composition gives analyticity and the derivative formula; invertibility of `DΨ` follows from nondegeneracy of the frozen symplectic form at factor one. Fast shifts alone give periodicity and injectivity modulo all integer torus phases; the slow torus coordinates are periodic. Lagrangianity follows from the same symplectic identity. Keep the exact `HasDerivAt` clause for **all** real `theta,t`. The input `tau>a+b` implies the physical requirement `tau>(a+b)-1`. There is no time or frequency scaling in this transport. The range identity is `range (Ψ∘K)=Ψ '' range K`.

**Image measure.** From the frozen union-of-whole-tori predicate derive `cylinder_set_shift`: complete `k:Fin a→ℤ` by zero on the slow indices. Shift each fast angle into the half-open cell, showing `Ψ '' S=Ψ '' (S∩cylinderCell V r)`. The chart is injective on that cell because two fast angles in `[0,2π)` differing by `2πk` force `k=0`. For P12-D, first use `S ⊆ cylinder V r` from the frozen set predicate to rewrite `S∩cylinderCell V r` as `S∩{z | ∀ i, fast z.1 i ∈ Ico (0 : ℝ) (2*π)}`. The latter is Borel since S is Borel and the fast coordinate maps are continuous. V is arbitrary in `measure`; never assume it is Borel. Then `MeasurableSet.image_of_continuousOn_injOn` proves the Borel image. `chart_measure_image` at factor one gives exact equality of volumes on this injective subset. This avoids a hidden global-injectivity assumption. Positive cell measure gives positive physical measure; `volume_lt_top_of_subset_circularTube` gives finiteness. Do not multiply by `(2π)^4` or divide the frequency: the chart has symplectic factor one and the physical torus parameters were already period one.

**General dimension.** Import the exact future `wrapper` conclusion, then use P6-5 at `gamma=axisGap a`, `A=axisMax a`. The wrapper owns the R-nondegeneracy, amount, analytic KAM, displacement and family/measure obligations; none becomes a new premise of `n_general`. The final source `fixed` performs `n=2` or `3≤n` from `hn`. In the equality branch `subst n` transports `m,a,hsep` and all dependent phase types together. In the other branch apply `n_general` with the original `hn`, eliminate only `eps0`, and insert `tubeD (axisGap a)` and `tubeBigD (axisGap a) (axisMax a)` as the frozen root’s existential pair witnesses. The helper exports these literal constants, so their dependence on a alone survives its interface.

## Departures and blueprint issues

| ID | Location and quoted source text | Design action and reason |
|---|---|---|
| D1 | p12 L81–89: “and :=0 elsewhere”; p13 L58 and L90–93 | Use the already total composition instead of introducing a new zero extension. The functions agree on the actual source open domain. Every derivative is identified there by local equality; no claim is made about an off-domain extension. This does not alter frozen definitions. |
| D2 | p12 L65–79 and p13 L72–88: “choose successively” | Existentially construct one tuple in `pg_hypotheses` and eliminate it in the assembly proof. No nonunique selected chart definition or theorem-shaped standing predicate. The fine jet and patch identities remain upstream proof obligations in that construction. |
| D3 | p12 L205 (Deviations): “the closure ... reaches ... outside the open T” | Keep the blueprint's repair `r0=r*/2`. Add `birkhoff_mono_radius`. Merely having `HasSecularBirkhoffForm` at an endpoint does not supply closed-cylinder analyticity. |
| D4 | p12 L205: “shifts the slow position coordinates q as well” | New direct `transport` and `measure`; reuse only local chart and Liouville tools of Part 1. P7-6 polar-lattice theorems do not apply to arbitrary frozen cylinder tori. |
| D5 | p12 L144: “if one wishes to lower tau” | No exponent lowering is used or needed. Retain the same tau and the same Diophantine constant; `tau>4` directly implies `tau>3`. Diophantine monotonicity does not generally allow lowering tau. |
| D6 | p12 L15/L173–195, p13 L163–164: dependence claims | Root and joint-construction signatures have the original input data before all witnesses; `radius_choices` handles explicit arithmetic. No coupling-dependent physical pair bounds. |
| D7 | repeated `chart`, `data`, `transport`, `pg-hypotheses` labels | Two assembly subnamespaces plus shared output theorem for data/chart/PG; internal steps map to the enclosing proof. Avoid duplicate definitions of upstream objects. |
| D8 | p12 transport/measure dimension four | Generic `transport`, `measure`, `cylinder_set_shift` allow arbitrary `a,b` with the same local hypotheses. This strictly strengthens the reusable conclusion without discarding any needed hypothesis. |
| B1 | p12 L58–60: explicit inverse `(.../v_i)^{1/3}` | Needs positivity of kappa and masses from section standing data; these are explicit in `fast_diffeo`. No new root premise. |
| B2 | p13 L135–140: “the only open dependency” / current general-n route | The global review records several transitive source gaps. The phrase must not be read as mathematical proof closure once wrapper is named. The gaps remain in the upstream ownership ledger below. |

No new pinned-paper erratum is asserted. The suspected defects above are blueprint/application issues or clarifications; the design does not edit the blueprint. Existing paper errata mentioned in p12/p13 (E-P-Fej04r-2/-3, E-P-CP11-1/-2, E-P-CP09-1..7) remain owned by Parts 8–11b. Frozen statement defects found: none. No hypotheses of either frozen provider have been added, removed or reordered.

### SOURCE_GAP disposition after the global review

The amended common brief and `docs/graph/P/reviews/GLOBAL-review.md` were read, including “Existing SOURCE_GAP records” and “Suspected blueprint defects and source limitations”. **Zero of the 89 local nodes contains a SOURCE_GAP note.** This is a statement about this slice, not its transitive prerequisites. The following table records every group of the review's 34 gap records; the exact node IDs are retained so no group is silently treated as solved.

| Owner / gap node(s) | Explicit design disposition |
|---|---|
| Part 2 `stepP:p2:ob-der` | P-G remains blocked on the target-width Cauchy correction. Do not borrow the invalid denominator `e(S0-S)`. Part 2 must provide the actual bound consumed by Part 5. |
| Part 3 `bpP:p3:rem-norm`, `bpP:p3:step`, `stepP:p3:inv-conj`, `stepP:p3:inv-lim` | P-G seal gate: correct normalization monotonicity and name/domain of the larger-domain map, then prove conjugacy and real limit on their genuine domains. No repair is assumed by this design. |
| Part 5 `bpP:p5:kam-cond#scales`, `stepP:p5:be-an`, `be-coef`, `be-jet`, `bl-comp`, `bl-real`, `ext-glue`, `ext-loc`, `fi-blk`, `fi-inv`, `st-ivt`, `ur-schwarz` (all `stepP:p5:` prefixes) | P-G seal gate: owner proves growth selection; complexification, coefficients/jets, real restrictions; gluing/local extension; block estimates; measure continuity; higher-order Schwarz. The exact P-G root is consumed only after all are paid and sealed. No imported provider shortcut. |
| Part 6 `bpP:p6:reconstruction-fixed#real-eps` | Use the **already designed exact arbitrary-real-epsilon** `reconstruction_fixed`, `reconstruction_fixed_all_time`, `orbit_transfer_fixed`. Actual implementation sources also quantify real epsilon without a sign premise. Require their proof/axiom audit before P6-5 assembly; do not add epsilon positivity to these lemmas. Root coupling positivity is still retained. |
| Part 7 `stepP:p7:ho-hol`, `stepP:p7:pc-share` | Need general real-derivative restriction and genuine analytic square-root/reciprocal reasoning. Current source `analyticOnNhd_fMov`, `analyticOnNhd_fFix` and `analyticOnNhd_*_poincareProd` supplies the latter with exact source names; proof auditing and P7-4 boundary obligations stay with the owners. |
| Part 1 `stepP:p1:hc-real-derivative` | Local transport in this design is wholly real and does not use a strip-only real-restriction theorem on an arbitrary complex domain. Any holomorphic preparation upstream still owes the general-domain bridge. |
| Part 9 `bpP:p9:diagonalize`, `stepP:p9:d-d` | Geometric chart facts here use the real lifted map and direct fast lattice. If the upstream rotation/torus proof invokes period-one transport on radians, require its named period-conversion bridge before delivery. Never silently divide the physical frequency downstream. |
| Part 9 `stepP:p9:gs-c#roots-route` | Keep the roots-continuity route unpaid; prefer the graph's distinct local-analytic route when the owner establishes it. Part 12 does not assume either route's conclusion as a premise. |
| Part 11 `stepP:p11:hc-rot`, `stepP:p11:hc-mean` | General-n wrapper gate: reverse complexification/identity theorem and fourth-order radial Schwarz are additional proof obligations. K holomorphic-to-analytic and N first-derivative Cauchy do not supply them. |
| Part 11a `stepP:p11a:cs-lip`, `ps-lim`, `rl-deriv`, `rl-global` (all `stepP:p11a:` prefixes) | General-n wrapper gate: real-flow reality guard; continuous uniform-limit theorem on the compact carrier; nonlinear flow derivative/variational bridge; nonlinear existence/uniqueness with uniform data. These are distinct from linear ODE/Gronwall inputs. No extra reality/flow premise reaches the frozen root. |
| Part 11b `stepP:p11b:bt-rot#lift` | Ask the owner for an actual analytic eigenframe on the chosen convex cube (e.g. the proved explicit two-planet frame), or a proved analytic lift with sign gluing. Simple connectedness alone is not a delivered proof. |
| Part 11b `stepP:p11b:fl-bd` | Need initial local/maximal real solutions and uniform `delta,M,L` on the compact action collar and confining slow ball, in addition to the a-priori differential inequality. Shrink `r*` uniformly before using time one. |
| Part 11b `stepP:p11b:li-tay`, `stepP:p11b:lm-prop` | **Explicit applicability gate for both two-planet providers.** Owner must either prove general real Lie/Taylor and symplectic-flow lemmas, or construct one complex neighbourhood of the compact real data, an analytic extension of the full generator including its fast-angle derivatives, a compatible norm and a verified small-field bound on a smaller domain. Only then may the imported N holomorphic results be applied. This design does not assert that the cited N statements already apply. |

These are prerequisite proof packages, not permissions to weaken the frozen theorems. Design signature elaboration does not discharge any source gap. P-PLANAR and the two-planet fixed branch do not require Part 11a, but still require P-G and the full Part 11b construction. The general-n branch requires the wrapper and its actual K1–K6 proof chain. The excluded unused Part 11a “physical-interface” component is not restored as a dependency merely because p13 lists its label in a forward-reference paragraph.

## Modules, import DAG and packages

All planned paths below are relative to the repository. No implementation module imports a provider. Provider files are terminal, quarantined consumers. All regular modules use the required module header, public imports for statement dependencies, module docstring, public section and exposed formula definitions. The scratch-only five-definition Tube prelude is **deleted** upon replacing it by `public import KAM.Planetary.Newtonian.Tube`.

| Package | Owned module(s) | Estimated proof lines | Wave / exact inputs |
|---|---|---:|---|
| P12-A | `KAM/Planetary/PlanarAssembly/Geometry.lean` | 350–600 | 1: Product, Poincare/Tube (`circularPoint_eq_poincareProd`), frozen definitions, Mathlib compactness; compact-cell/forward-tube |
| P12-B | `KAM/Planetary/PlanarAssembly/Boxes.lean` | 400–650 | 2: P12-A Geometry, Product, frozen HasFastDiffeomorphism, Mathlib Pi measure and real powers; collar/fast inverse/radius arithmetic/BNF radius restriction; locally owned missing `product_chart` (b) derivatives and analyticity |
| P12-C | `KAM/Planetary/PlanarAssembly/Data.lean` | 500–800 | 3: A+B, actual Part 8 identification and 11b patch/birkhoff_form/lift_map/flow/jet definitions; Part 1 Chart. Construct all witnesses and prove all joint clauses; no P-G theorem import. |
| P12-D | `KAM/Planetary/PlanarAssembly/Transport.lean`, `KAM/Planetary/PlanarAssembly/Measure.lean` | 550–800 total | 1: frozen cylinder/physical predicates, Part 1 Chart, Transport, Liouville, P6-5 finite tube volume. Generic local lemmas are independent of C. Split measure/transport into separate files (~350/~400). |
| P12-E | `KAM/Planetary/PlanarAssembly/Main.lean` and `KAM/Provider/Planetary/PlanarTwoPlanetKAM.lean` | 180–350 total | 4: C+D, SEALED `KAM/Frozen/Planetary/Theorems/ProperlyDegenerateKAM.lean`, P6-5 Assembly. Prove `planar`; terminal provider matches the frozen type. |
| P13-A | `KAM/Planetary/FixedAssembly/Data.lean` | 400–750 | 4: P12-C, Product, same actual Part 8/11b objects as C; share geometry/chart helpers; fixed perturbation gets fresh joint witnesses. |
| P13-B | `KAM/Planetary/FixedAssembly/TwoPlanet.lean` | 180–350 | 5: P13-A, D, SEALED P-G, P6-5 fixed assembly; new constants and fixed P-G application. |
| P13-C | `KAM/Planetary/FixedAssembly/General.lean`, `KAM/Planetary/FixedAssembly/Main.lean`, `KAM/Provider/Planetary/FixedSunPlanetaryKAM.lean` | 200–400 total | 6: P13-B, exact Part 11 wrapper, P6-5 Assembly; general route, dimension split, terminal provider. General.lean may be completed independently at wave 1 after wrapper delivery. |

Each package is 150–800 lines. Each file is below 1500 lines; split at ~1100 if estimates grow, preserving a cheap facade if needed. Do not pad a small provider to a package: provider files belong to their assembly package. Waves are local to this design after the listed upstream owners deliver.

The import DAG is exactly:

```text
Product + Poincare.Tube + FrozenDefs + Mathlib -> PlanarAssembly.Geometry
PlanarAssembly.Geometry + Product + FrozenDefs + Mathlib -> PlanarAssembly.Boxes
P1.Chart + P1.Transport + FrozenDefs -> PlanarAssembly.Transport
P1.Liouville + FrozenDefs + P6.Assembly -> PlanarAssembly.Measure
Geometry + Boxes + P8.* + P11b.* + P1.Chart -> PlanarAssembly.Data
Data + Transport + Measure + SEALED P-G + P6.Assembly -> PlanarAssembly.Main
PlanarAssembly.Main -> Provider.Planetary.PlanarTwoPlanetKAM
PlanarAssembly.Data + P8.* + P11b.* -> FixedAssembly.Data
FixedAssembly.Data + Transport + Measure + SEALED P-G + P6.Assembly -> FixedAssembly.TwoPlanet
P11.Wrapper + P6.Assembly + Newtonian.Tube -> FixedAssembly.General
FixedAssembly.General + FixedAssembly.TwoPlanet -> FixedAssembly.Main
FixedAssembly.Main -> Provider.Planetary.FixedSunPlanetaryKAM
```

`P8.*`, `P11b.*`, `P11.Wrapper` are owner module paths to reconcile, not invented imports. Their exact exports and required shapes are above. All other path abbreviations expand uniquely to the complete paths in the reuse table. Generic `measure_in_tube` belongs to Measure. `total_chart` and both literal perturbation definitions live in the corresponding Data files. `kepler_h`/action_center/compact_cell belong to Geometry; Boxes imports Geometry for `kepler_h`. The definitive package dependency table is:

| Package | After | Final wave |
|---|---|---:|
| P12-A | delivered owners only | 1 |
| P12-D | delivered owners only | 1 |
| P12-B | P12-A | 2 |
| P12-C | P12-A, P12-B | 3 |
| P12-E | P12-C, P12-D | 4 |
| P13-A | P12-C | 4 |
| P13-B | P13-A, P12-D | 5 |
| P13-C | P13-B; wrapper owner delivered | 6 |

No module is owned twice. The two frozen anchors remain untouched. Only the orchestrator can later seal them after independent proof audits and standard-axiom checks.

## Exact provider assemblies

Both provider signatures in Appendix A were transcribed from the actual frozen theorem commands, changing only the declaration namespace. They are not conditional assembly lemmas. The frozen anchors are read, never imported into implementation or scratch.

| Frozen binder, in order | P-PLANAR consumption | P-FIXED consumption |
|---|---|---|
| implicit `n`, `hn : 2≤n` | absent, literal two planets | dimension split; `n_general` uses original `hn`; equality branch substitutes all dependent data |
| `G m0 : ℝ` | chart, Kepler actions and physical reconstruction | same in either branch |
| `m a` | exact `Fin 2→ℝ` | exact `Fin n→ℝ`, transported only under `subst n` |
| `hG`, `hm0`, `hm` | positivity for Kepler chart, inverses and Newton reconstruction | same, fixed velocities divide by each positive `m_i` |
| `ha` | circular actions and tube geometry | same, all coordinates |
| `hsep` | `a 0<a 1`; derive injectivity on `Fin 2` | literal `∀ i j, i<j→a i<a j`; no numeric separation added |
| `eta`, `heta` | choose `zeta=tubeRadius eta gamma`; axis patch/radius before mu | same, wrapper in general route |
| existential `mu0/eps0,d,D` | choose canonical d,D and the P-G radius-derived positive threshold | n=2 same with fresh fixed constants; general threshold from wrapper, canonical d,D |
| `0<threshold`, `0<d`, `d<D` | `radius_choices`, `axisData_canonical`, `tubeD_lt_tubeBigD` | same |
| later `mu/eps`, its two strict inequalities | apply P-G with fixed r; `mu<1`, `mu<r^6/log^c` from threshold | two-planet P-G or wrapper; never move the threshold after epsilon |
| `S`, positive finite `volume` | exact image of cylinder set; positivity from cell; finite tube volume | same in n=2, exact wrapper set in general |
| frozen Kolmogorov predicate | P6-5 `movingKolmogorovSet_of_tube` | P6-5 `fixedKolmogorovSet_of_tube` |

**Planar proof assembly.** Eliminate `PlanarAssembly.pg_hypotheses` once. Feed `V,hV,hVc,hVb,W,hW,hVW,hboundary,r0,1,B,hr0,zero_lt_one,hB,H0,P,P0,Ω,β,hP,hperiod,hfreq,hBNF,htorsion,hsymm` to SEALED `properlyDegenerateKAM` at `a=b=2` with their positivity proofs. Select `rG,C,c`, then r and mu0 with `radius_choices`. For each permitted mu get `S_cyl` and its positive cell measure. Take `S=total_chart '' S_cyl`, applying Measure and Transport using the **same** existential chart data. At a physical point choose its cylinder preimage, then the torus witnesses from the frozen cylinder Kolmogorov predicate; composition supplies the required range inclusion and physical torus. Finish with P6-5 at the exact canonical tube radius and pair bounds.

**Fixed two-planet proof assembly.** Repeat the application with `FixedAssembly.pg_hypotheses`, keeping `P0fix` and actual fixed perturbation. Never reuse the moving P-G threshold merely because the secular torsion is shared. Shared chart geometry and transport/measure lemmas are Hamiltonian-independent. Finish with `fixedKolmogorovSet_of_tube`; the Sun-position clause is exactly `Fin.cons 0 bodyVector`.

**General fixed proof assembly.** Eliminate the wrapper's threshold before introducing epsilon. At each epsilon preserve its set, positive finite volume and all torus witnesses. Apply `fixedKolmogorovSet_of_tube`; it fills all-time fixed equations and collision/pair clauses. The final `fixed` theorem chooses the two-planet branch at equality and the general route otherwise. The general helper fixes `d := tubeD (axisGap a)` and `D := tubeBigD (axisGap a) (axisMax a)` in its conclusion and existentially selects only eps0. In `fixed`, eliminate that eps0, then existentially package `(eps0, tubeD (axisGap a), tubeBigD (axisGap a) (axisMax a))` with its positivity and later-epsilon clauses. This recovers exactly the anchor’s witness/strict-inequality order; the n2 branch already has that telescope. Neither provider type changes.

**Terminal providers.** The future proof bodies are applications of `PlanarAssembly.planar G m0 m a hG hm0 hm ha hsep eta heta` and `FixedAssembly.fixed hn G m0 m a hG hm0 hm ha hsep eta heta`, respectively. No additional instance or premise is required. Only these providers are named in the corresponding anchor sealing expression. Ordinary assembly modules never import these terminal provider files.

## Risks, validation and remaining gates

The largest local mathematical tasks are the fast inverse/product frontier volume and direct fast-lattice image measure. Split rational derivative algebra and finite-coordinate calculations into focused helpers instead of raising resources. Default-heartbeat failure is a design signal. The large joint existence statements are interface outputs; proofs should build their clauses in small local helper results and assemble one tuple at the end.

The dominant upstream risks are **unpaid** 11b flow/Lie/symplectic applicability, the exact actual jet dictionary and shared chart identity, P-G sealing, and the Part 11/11a wrapper at general dimension. An elaborating signature cannot certify any of them. The full P7 quotient/local-diffeomorphism and transport exports and d25(e) remain NOT_STARTED after the aa7bc30 sync and are not used; h derivative/analyticity is locally assigned to P12-B. P6-5 and P7-6 are designed dependencies and are not claimed delivered by this document. The shared build currently lacks the Tube olean despite implementation source being present. No rebuild or new upstream implementation was attempted.

Before any prover package is assigned, reconcile its listed upstream signatures, carry the exact original hypotheses and jet characterizations, append every applicable source-gap gate above, and repeat all repository hard rules in the Lean brief. The full rules are quoted below to make these package briefs reusable.

### Hard rules to repeat verbatim in each Lean brief

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


### Revision 1 validation receipt (historical)

- Worktree base: `081967912d5200ad4711d6d16abde6a8cfafea71`, branch `inp-design-p1213`.
- Blueprint Part 12 sha256 `83eee5fc9d881bf115be39e811ffc58cc206d45355d7956599115c9c7e0965db`; Part 13 sha256 `8b208fe0799dec36bf3ff95b51a08bda6d2ca705491e045fe7d3c150838bb9e5`. Both byte-identical to the supplied inp copy when checked.
- Graph read from `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` (the worktree has no copy): sha256 `7d58c7597a6e498eddaa56d6b062d015a466131dcd2e9abde2bc852f07b6e8ca`. Global review sha256 `39f5a84a7d261187fa474fa94ecc839a1fac463810fdd8ce674fe5766d539e65`.
- Exact scope filter: `STATEMENT_SOURCE` starts with either assigned blueprint path. **89/89** unique graph nodes mapped, with statement and proof locators. Source-gap grouping retains all **34** records from the global review, as upstream obligations.
- Exact six root-signature text comparisons passed (declaration names changed; the `n2` specialization additionally changes the coupling variable and Moving/Fixed predicate). The five principal root/provider commands retain their literal frozen binder lists and conclusions.
- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p1213 .drafts/scratch/P1213Signatures.lean`: **exit 0**, **24** warnings, all `declaration uses 'sorry'`; no other warning or error. Log `.drafts/scratch/P1213-elaboration.log`. One local gated check at a time; no direct Lake invocation or resource override.
- Signature: **381** lines, **24** theorem bodies, every one `sorry`; sha256 `83c26d562e951b5aee941703518bd879dfcfcf63cb0757a3fecf0229a53ce128`. No theorem anchor/provider import. No new source implementation was written.
- The same gated signature run prints axioms of `planar`, `n2`, `n_general`, `fixed`, and both registered provider signatures: each is exactly `[propext, sorryAx, Classical.choice, Quot.sound]`. These are intentionally unproved signatures, not standard-axiom-only proof closures.
- `PATH="/root/code/KAM-inp-design-p1213/.drafts/scratch/gated-bin:$PATH" scripts/lint_sources.sh`: **exit 0**. Output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`. The local `lake` shim accepts only the lint ABI command and routes it to `inp_sig_check.sh`, restoring the original PATH inside the gate. No direct Lean elaboration or library build. Log `.drafts/scratch/P1213-lint.log`.
- `git -C /root/code/KAM-inp-design-p1213 diff --cached --check -- docs/tracks/P/design/P1213-LEAN-DESIGN.md`: exit 0 after staging only this design document.
- `python3 .drafts/scratch/audit_p1213.py`: **exit 0**; exact six root transcriptions, all 89 graph IDs and both locators, all 24 sorry-only bodies, missing P7(b) completion, exact Appendix A and axiom/warning checks passed. External signature copy is byte-identical. Log `.drafts/scratch/P1213-static.log`.

## Revision 2

This revision addresses `DESIGN-P1213-design-audit-1.md` (FAIL). No proof, frozen statement, or upstream source gap is certified closed by these design changes.

| Finding | Resolution |
|---|---|
| F1 (medium, blocking) | Strengthened only `FixedAssembly.n_general` to let-bound canonical `tubeD (axisGap a)` and `tubeBigD (axisGap a) (axisMax a)`; only eps0 remains existential. Updated general construction and `fixed` assembly to package these constants as the frozen existential witnesses. Both provider types and `fixed` remain byte-exact frozen transcriptions. |
| N1 (medium) | Added explicit pre-assignment characterization gates for P12-C/P13-A, including exact owner names/types, the actual cube/jet dictionary and a common jointly constructed T. Signature comments mark joint P-G outputs as consumer projections, without claiming they identify source objects or each other. Exact upstream declarations remain to reconcile with their owners. |
| N2 (medium) | Preserved every group of the 34 transitive gaps and made applicable gap/delivery/proof-audit requirements mandatory in package briefs. P-G sealing, P6-5/P7-6, the eigenframe and real-flow/Lie applicability, and the general wrapper K1–K6 chain remain explicit gates. |
| N3 (low) | P12-B explicitly uses differentiability order `ω` before `.analyticAt`; P12-D explicitly obtains Borelness by rewriting the cell intersection using S⊆cylinder V r, with no measurability assumption on V. Added the latter instruction to the signature comment. |

### Revision 2 validation receipt

- Signature check: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p1213 .drafts/scratch/P1213Signatures.lean`, exit 0; exactly 24 `declaration uses sorry` warnings, no errors or other warnings. Log: `.drafts/scratch/P1213-elaboration.log`.
- Current standalone signature and scratch copy are byte-identical: 389 lines, 24 sorry-only bodies, sha256 `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447`. Appendix A is byte-identical too.
- All six diagnostic axiom prints are `[propext, sorryAx, Classical.choice, Quot.sound]`; these are unproved design signatures.
- `python3 .drafts/scratch/audit_p1213.py`, exit 0: five unchanged frozen-type transcriptions; exact audit-replacement telescope for canonical `n_general`; 89/89 unique nodes and locators; 24 sorry-only bodies; appendix/external-copy equality; F1/N1/N2/N3 dispositions. Log: `.drafts/scratch/P1213-static-r2.log`.
- `PATH="$PWD/.drafts/scratch/gated-bin:$PATH" LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh`, exit 0: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`. The existing shim routes ABI elaboration through `inp_sig_check.sh`. Log: `.drafts/scratch/P1213-lint-r2.log`.
- `git -C /root/code/KAM-inp-design-p1213 diff --check`, exit 0. Only the owned design document is committed. No implementation module was changed or built: the targeted elaboration is the required design check. The Revision 1 receipt above is historical.

## Appendix A. Exact signatures

The following is the complete standalone untracked file `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean`, copied to `.drafts/scratch/P1213Signatures.lean` for the gated check. The prelude is explicitly a scratch dependency copy, not a proposed duplicate module. Implementation imports its owning Tube module instead.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Poincare.Product
public import KAM.Frozen.Planetary.Defs.MovingKolmogorovSet
public import KAM.Frozen.Planetary.Defs.FixedKolmogorovSet
public import KAM.Frozen.Planetary.Defs.IsCylinderKolmogorovSet
public import KAM.Frozen.Planetary.Defs.CylinderCell
public import KAM.Frozen.Planetary.Defs.HasFastDiffeomorphism
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian

/-!
# Parts 12 and 13: assembly design signatures

Design only. All theorem bodies are sorry. No theorem anchor or provider is imported.
Assembly namespaces disambiguate the repeated source slugs data/chart/transport.
The joint existential below is an output theorem, never an assumption bundle.
-/

@[expose] public noncomputable section
open Set Real MeasureTheory Function
open scoped BigOperators
namespace KAM.Planetary
open KAM KAM.Kepler

/- Dependency prelude only: literal definitions from P6-4 (Tube.lean), whose olean
is absent in the shared snapshot. Implementation imports that module and deletes
this prelude; no new representation or upstream theorem is declared here. -/
def axisMax {n : ℕ} (a : Fin n → ℝ) : ℝ := ⨆ i, a i
def axisGap {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  sInf ({x | ∃ i, x = a i} ∪ {x | ∃ i j, i ≠ j ∧ x = |a i - a j|})
def tubeRadius (η γ : ℝ) : ℝ := min η (γ / 6)
def tubeD (γ : ℝ) : ℝ := γ / 2
def tubeBigD (γ A : ℝ) : ℝ := 2 * A + γ

namespace PlanarAssembly

/-- The action-only Kepler Hamiltonian, reusing hProd rather than a second formula. -/
def kepler_h {n : ℕ} (κ : ℝ) (m : Fin n → ℝ) (I : Fin n → ℝ) : ℝ :=
  hProd κ m (assemble I (0 : Fin n → ℝ) (0 : Fin n → ℝ) (0 : Fin n → ℝ))

def action_center (G m0 : ℝ) (m a : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => m i * √(G * m0 * a i)

/-- No arbitrary zero extension: the existing total chart supplies a total composition. -/
def total_chart (G m0 : ℝ) (m : Fin 2 → ℝ) (T : Phase 4 → Phase 4) :
    Phase 4 → Phase 4 := poincareProd m (G * m0) ∘ T

/-- The moving-Sun constant coupling family, on the existing total fMov. -/
def perturbation (G m0 : ℝ) (m : Fin 2 → ℝ) (T : Phase 4 → Phase 4) :
    ℝ → Phase 4 → ℝ := fun _ z => fMov G m0 m (total_chart G m0 m T z)

/-- The compact set used in the proof of forward_tube. -/
def compact_cell (G m0 : ℝ) (m a : Fin 2 → ℝ) (δ : ℝ) : Set (Phase 4) :=
  {w | (∀ i, fast (a := 2) (b := 2) w.1 i ∈ Icc (0 : ℝ) (2 * π)) ∧
    (∀ i, |fast (a := 2) (b := 2) w.2 i - action_center G m0 m a i| ≤ δ) ∧
    (∀ i, poincareGamma (planetBlock (n := 2) w i) ≤ δ)}

theorem compact_cell_isCompact (G m0 : ℝ) (m a : Fin 2 → ℝ) (δ : ℝ) :
    IsCompact (compact_cell G m0 m a δ) := sorry

/-- bpP:p12:forward-tube, including its explicit upper radius bound. -/
theorem forward_tube (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i) (ha : ∀ i, 0 < a i)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ≤ action_center G m0 m a i / 4) ∧
      ∀ w : Phase 4,
        (∀ i, |fast (a := 2) (b := 2) w.2 i - action_center G m0 m a i| ≤ δ) →
        (∀ i, poincareGamma (planetBlock (n := 2) w i) ≤ δ) →
        w ∈ poincareProdDom 2 ∧
        ‖poincareProd m (G * m0) w -
          circularPoint G m0 m a (fun i => fast (a := 2) (b := 2) w.1 i / (2 * π))‖ < ζ ∧
        poincareProd m (G * m0) w ∈ circularTube G m0 m a ζ := sorry

/-- bpP:p12:collar, both sides of the boundary, with the source constant. -/
theorem collar (l u : Fin 2 → ℝ) (hlu : ∀ i, l i < u i)
    (t : ℝ) (ht : 0 < t) (htl : ∀ i, t < (u i - l i) / 2) :
    volume {I : Fin 2 → ℝ | ∃ J ∈ frontier (pi univ (fun i => Ioo (l i) (u i))),
      dist I J < t} ≤ ENNReal.ofReal (4 * ((u 0 - l 0) + (u 1 - l 1)) * t) := sorry

/-- bpP:p7:product-chart (b), p7 L197/L206: locally owned missing export.
The delivered Product module's splitting identity alone does not supply these derivatives.
The action carrier is the same one used by hProd, restricted via assemble, not a new model. -/
theorem product_chart {n : ℕ} (hn : 0 < n) (κ : ℝ) (m : Fin n → ℝ)
    (hκ : 0 < κ) (hm : ∀ i, 0 < m i) :
    AnalyticOnNhd ℝ (kepler_h κ m) {I : Fin n → ℝ | ∀ i, 0 < I i} ∧
    (∀ I : Fin n → ℝ, (∀ i, 0 < I i) →
      (fastFrequency (kepler_h κ m) I = fun i => κ ^ 2 * m i ^ 3 / I i ^ 3) ∧
      (∀ i, fderiv ℝ (kepler_h κ m) I (Pi.single i 1) =
        κ ^ 2 * m i ^ 3 / I i ^ 3) ∧
      (∀ i j, fderiv ℝ (fastFrequency (kepler_h κ m)) I (Pi.single j 1) i =
        if i = j then -3 * κ ^ 2 * m i ^ 3 / I i ^ 4 else 0) ∧
      (∀ i, -3 * κ ^ 2 * m i ^ 3 / I i ^ 4 ≠ 0)) ∧
    (∀ w : Phase (n + n), hProd κ m w =
      kepler_h κ m (fast (a := n) (b := n) w.2)) ∧
    (∀ w ∈ poincareProdDom n, keplerPart κ m (poincareProd m κ w) =
      kepler_h κ m (fast (a := n) (b := n) w.2)) := sorry

/-- bpP:p12:fast-diffeo. Positivity of kappa and masses is standing section data. -/
theorem fast_diffeo (κ : ℝ) (m l u : Fin 2 → ℝ) (hκ : 0 < κ)
    (hm : ∀ i, 0 < m i) (hl : ∀ i, 0 < l i) (hlu : ∀ i, l i < u i) :
    HasFastDiffeomorphism (kepler_h κ m) (pi univ (fun i => Ioo (l i) (u i))) := sorry

/-- Elementary output of the P-G radius/threshold choices, not a P-G premise. -/
def secular_radius (rG δ : ℝ) : ℝ := min rG (√(δ / 2)) / 2

def coupling_threshold (r c : ℝ) : ℝ := min 1 (r ^ 6 / (log (1 / r)) ^ c)

theorem radius_choices (rG δ c : ℝ) (hrG : 0 < rG) (hrG1 : rG < 1)
    (hδ : 0 < δ) (hc : 0 < c) :
    let r := secular_radius rG δ
    0 < r ∧ r < rG ∧ r < 1 ∧ 2 * r ^ 2 ≤ δ / 2 ∧
    0 < coupling_threshold r c ∧ coupling_threshold r c ≤ 1 ∧
    ∀ μ, 0 < μ → μ < coupling_threshold r c → μ < r ^ 6 / (log (1 / r)) ^ c := sorry

/-- Restrict the frozen oscillator-disc expansion; useful also for fixed-Sun assembly. -/
theorem birkhoff_mono_radius {a b : ℕ} {P : ℝ → Phase (a + b) → ℝ}
    {V : Set (Fin a → ℝ)} {r r0 μ0 : ℝ}
    {P0 : ℝ → (Fin a → ℝ) → ℝ}
    {Ω : ℝ → (Fin a → ℝ) → (Fin b → ℝ)}
    {β : ℝ → (Fin a → ℝ) → Matrix (Fin b) (Fin b) ℝ}
    (hr : 0 < r) (hrr0 : r ≤ r0)
    (h : HasSecularBirkhoffForm P V r0 μ0 P0 Ω β) :
    HasSecularBirkhoffForm P V r μ0 P0 Ω β := sorry

/-- Conditional chart-composition helper, not a replacement for the source construction. -/
theorem chart_of_birkhoff {G m0 : ℝ} {m : Fin 2 → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < G * m0) {O : Set (Phase 4)}
    {T : Phase 4 → Phase 4} (hTan : AnalyticOnNhd ℝ T O)
    (hTs : IsSymplecticOn 1 T O) (hTm : MapsTo T O (poincareProdDom 2)) :
    AnalyticOnNhd ℝ (total_chart G m0 m T) O ∧
    IsSymplecticOn 1 (total_chart G m0 m T) O := sorry

/-- Conditional Hamiltonian identity; fast-action preservation is supplied by 11b. -/
theorem chart_hamiltonian_of_preserves_fast {G m0 : ℝ} {m : Fin 2 → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < G * m0) {T : Phase 4 → Phase 4}
    {z : Phase 4} (hz : T z ∈ poincareProdDom 2)
    (hI : fast (a := 2) (b := 2) (T z).2 = (fast (a := 2) (b := 2) z.2 : Fin 2 → ℝ)) (μ : ℝ) :
    movingHamiltonian G m0 m μ (total_chart G m0 m T z) =
      degenerateHamiltonian (a := 2) (b := 2) (kepler_h (G * m0) m) (perturbation G m0 m T) μ z := sorry

/-- Joint output of data, chart and pg-hypotheses. All derived clauses are conclusions.
T, O, V and the jet witnesses are shared, selected once before the coupling.
The 11b writer owns their finer source characterization; see the upstream table.
This projection is not a certificate of canonical jets, the axis cube, or a common
moving/fixed T. Exact characterization exports must be reconciled before P12-C/P13-A. -/
theorem pg_hypotheses (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1) (η : ℝ) (hη : 0 < η) :
    ∃ (V W : Set (Fin 2 → ℝ)) (O : Set (Phase 4)) (T : Phase 4 → Phase 4)
      (r0 δ B : ℝ) (P0 : ℝ → (Fin 2 → ℝ) → ℝ)
      (Ω : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ))
      (β : ℝ → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ),
      IsOpen V ∧ IsConnected V ∧ Bornology.IsBounded V ∧
      IsOpen W ∧ closure V ⊆ W ∧
      (∃ A dc : ℝ, 0 < A ∧ 0 < dc ∧ ∀ t : ℝ, 0 < t → t < dc →
        volume {I : Fin 2 → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤
          ENNReal.ofReal (A * t)) ∧
      0 < r0 ∧ 0 < δ ∧ 0 < B ∧
      IsOpen O ∧ closure (cylinder (b := 2) V r0) ⊆ O ∧
      (∀ z ∈ O, ∀ k : Fin 2 → ℤ, z + fastShift (a := 2) (b := 2) k ∈ O) ∧
      MapsTo T O (poincareProdDom 2) ∧
      MapsTo (total_chart G m0 m T) O (collisionFreeDomain 2) ∧
      AnalyticOnNhd ℝ (total_chart G m0 m T) O ∧
      IsSymplecticOn 1 (total_chart G m0 m T) O ∧
      (∀ z ∈ O, Bijective (fderiv ℝ (total_chart G m0 m T) z)) ∧
      (∀ z ∈ O, ∀ k : Fin 2 → ℤ,
        total_chart G m0 m T (z + fastShift (a := 2) (b := 2) k) = total_chart G m0 m T z) ∧
      (∀ z ∈ O, ∀ z' ∈ O, total_chart G m0 m T z' = total_chart G m0 m T z →
        ∃ k : Fin 2 → ℤ, z' = z + fastShift (a := 2) (b := 2) k) ∧
      (∀ μ : ℝ, ∀ z ∈ O, movingHamiltonian G m0 m μ (total_chart G m0 m T z) =
        degenerateHamiltonian (a := 2) (b := 2) (kepler_h (G * m0) m) (perturbation G m0 m T) μ z) ∧
      (∀ r : ℝ, 0 < r → r ≤ r0 → 2 * r ^ 2 ≤ δ →
        MapsTo (total_chart G m0 m T) (cylinder (b := 2) V r)
          (circularTube G m0 m a (tubeRadius η (axisGap a)))) ∧
      AnalyticOnNhd ℝ (fun z : ℝ × Phase 4 => perturbation G m0 m T z.1 z.2)
        (Icc 0 1 ×ˢ closure (cylinder (b := 2) V r0)) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ z ∈ cylinder (b := 2) V r0, ∀ k : Fin 2 → ℤ,
        perturbation G m0 m T μ (z + fastShift (a := 2) (b := 2) k) = perturbation G m0 m T μ z) ∧
      HasFastDiffeomorphism (kepler_h (G * m0) m) W ∧
      HasSecularBirkhoffForm (perturbation G m0 m T) V r0 1 P0 Ω β ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ I ∈ V, B ≤ |(β μ I).det|) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ I ∈ V, (β μ I).IsSymm) := sorry

/-- Direct fast-lattice transport, stronger in dimension and Hamiltonian generality.
These are the local source hypotheses of transport, not frozen-root assumptions. -/
theorem transport {a b : ℕ} {O : Set (Phase (a + b))} (hO : IsOpen O)
    {Ψ : Phase (a + b) → Phase (a + b)}
    (hΨa : AnalyticOnNhd ℝ Ψ O) (hΨs : IsSymplecticOn 1 Ψ O)
    {H G : Phase (a + b) → ℝ} (hHG : EqOn (G ∘ Ψ) H O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin a → ℤ, z + fastShift k ∈ O ∧ Ψ (z + fastShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin a → ℤ, z' = z + fastShift k)
    {U : Set (Phase (a + b))} (hUO : U ⊆ O)
    {w : Fin (a + b) → ℝ} {K : (Fin (a + b) → ℝ) → Phase (a + b)}
    (hK : IsCylinderTorus H U w K) {γ τ : ℝ} (hγ : 0 < γ)
    (hτ : (a + b : ℕ) < τ) (hw : IsDiophantine γ τ w) :
    IsPhysicalTorus G w (Ψ ∘ K) ∧ range (Ψ ∘ K) = Ψ '' range K := sorry

/-- Invariance under the fast lattice follows from the frozen union-of-whole-tori predicate. -/
theorem cylinder_set_shift {a b : ℕ} {H : Phase (a + b) → ℝ}
    {V : Set (Fin a → ℝ)} {r μ C : ℝ} {S : Set (Phase (a + b))}
    (hS : IsCylinderKolmogorovSet H V r μ C S) (k : Fin a → ℤ) :
    (fun z => z + fastShift k) '' S = S := sorry

/-- Borel image and exact volume through the half-open fast cell.
V is arbitrary: use S subset cylinder V r to rewrite the cell intersection as S
intersected with just the Borel fast-angle bounds; do not assume V measurable. -/
theorem measure {a b : ℕ} {O : Set (Phase (a + b))} (hO : IsOpen O)
    {Ψ : Phase (a + b) → Phase (a + b)}
    (hΨa : AnalyticOnNhd ℝ Ψ O) (hΨs : IsSymplecticOn 1 Ψ O)
    (hQ1 : ∀ z ∈ O, ∀ k : Fin a → ℤ, z + fastShift k ∈ O ∧ Ψ (z + fastShift k) = Ψ z)
    (hQ2 : ∀ z ∈ O, ∀ z' ∈ O, Ψ z' = Ψ z → ∃ k : Fin a → ℤ, z' = z + fastShift k)
    {H : Phase (a + b) → ℝ} {V : Set (Fin a → ℝ)} {r μ C : ℝ}
    {S : Set (Phase (a + b))} (hS : IsCylinderKolmogorovSet H V r μ C S)
    (hSO : S ⊆ O) :
    Ψ '' S = Ψ '' (S ∩ cylinderCell V r) ∧
    InjOn Ψ (S ∩ cylinderCell V r) ∧ MeasurableSet (Ψ '' S) ∧
    volume (Ψ '' S) = volume (S ∩ cylinderCell V r) := sorry

/-- Tube, positivity and finiteness after the measure theorem; no lattice strengthening. -/
theorem measure_in_tube {G m0 : ℝ} {m a : Fin 2 → ℝ} {ζ r μ C : ℝ}
    (hG : 0 < G) (hm0 : 0 < m0) (ha : ∀ i, 0 < a i)
    {Ψ : Phase 4 → Phase 4} {H : Phase 4 → ℝ} {V : Set (Fin 2 → ℝ)}
    {S : Set (Phase 4)} (hS : IsCylinderKolmogorovSet (a := 2) (b := 2) H V r μ C S)
    (hvol : volume (Ψ '' S) = volume (S ∩ cylinderCell (b := 2) V r))
    (hpos : 0 < volume (S ∩ cylinderCell (b := 2) V r))
    (hmap : MapsTo Ψ (cylinder (b := 2) V r) (circularTube G m0 m a ζ)) :
    Ψ '' S ⊆ circularTube G m0 m a ζ ∧
    0 < volume (Ψ '' S) ∧ volume (Ψ '' S) < ⊤ := sorry

/-- bpP:p12:planar: exactly the frozen type. -/
theorem planar (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ mu0 d D : ℝ, 0 < mu0 ∧ 0 < d ∧ d < D ∧
      ∀ mu : ℝ, 0 < mu → mu < mu0 →
        ∃ S : Set (Phase (2 * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          MovingKolmogorovSet G m0 m a mu eta d D S := sorry

end PlanarAssembly

namespace FixedAssembly

/-- Fixed-Sun constant coupling family; the same total chart, a different perturbation. -/
def perturbation (G m0 : ℝ) (m : Fin 2 → ℝ) (T : Phase 4 → Phase 4) :
    ℝ → Phase 4 → ℝ := fun _ z => fFix G m (PlanarAssembly.total_chart G m0 m T z)

/-- bpP:p13:fixed-hamiltonian-form (a); exact existing product chart identity. -/
theorem fixed_hamiltonian_form {n : ℕ} {G m0 ε : ℝ} {m : Fin n → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < G * m0) {z : Phase (n + n)}
    (hz : z ∈ poincareProdDom n) :
    fixedHamiltonian G m0 m ε (poincareProd m (G * m0) z) =
      hProd (G * m0) m z + ε * fFix G m (poincareProd m (G * m0) z) := sorry

/-- Conditional difference identity; no restriction on either real coupling. -/
theorem perturbation_difference (G m0 : ℝ) (m : Fin 2 → ℝ) (T : Phase 4 → Phase 4)
    (μ : ℝ) (z : Phase 4) :
    PlanarAssembly.perturbation G m0 m T μ z - perturbation G m0 m T μ z =
      planeSq (∑ i : Fin 2, bodyVector (PlanarAssembly.total_chart G m0 m T z).2 i) /
        (2 * m0) := sorry

/-- The fixed counterpart of the fast-action-preserving chart identity. -/
theorem chart_of_preserves_fast {G m0 : ℝ} {m : Fin 2 → ℝ}
    (hm : ∀ i, 0 < m i) (hκ : 0 < G * m0) {T : Phase 4 → Phase 4}
    {z : Phase 4} (hz : T z ∈ poincareProdDom 2)
    (hI : fast (a := 2) (b := 2) (T z).2 = (fast (a := 2) (b := 2) z.2 : Fin 2 → ℝ)) (ε : ℝ) :
    fixedHamiltonian G m0 m ε (PlanarAssembly.total_chart G m0 m T z) =
      degenerateHamiltonian (a := 2) (b := 2) (PlanarAssembly.kepler_h (G * m0) m)
        (perturbation G m0 m T) ε z := sorry

/-- Fresh P-G constants for the fixed perturbation; no equality of thresholds is claimed.
Separate existential outputs do not identify the moving/fixed chart or jets.
Their common-map and canonical-jet certificates are upstream delivery gates. -/
theorem pg_hypotheses (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1) (η : ℝ) (hη : 0 < η) :
    ∃ (V W : Set (Fin 2 → ℝ)) (O : Set (Phase 4)) (T : Phase 4 → Phase 4)
      (r0 δ B : ℝ) (P0 : ℝ → (Fin 2 → ℝ) → ℝ)
      (Ω : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ))
      (β : ℝ → (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ),
      IsOpen V ∧ IsConnected V ∧ Bornology.IsBounded V ∧
      IsOpen W ∧ closure V ⊆ W ∧
      (∃ A dc : ℝ, 0 < A ∧ 0 < dc ∧ ∀ t : ℝ, 0 < t → t < dc →
        volume {I : Fin 2 → ℝ | ∃ J ∈ frontier V, dist I J < t} ≤
          ENNReal.ofReal (A * t)) ∧
      0 < r0 ∧ 0 < δ ∧ 0 < B ∧
      IsOpen O ∧ closure (cylinder (b := 2) V r0) ⊆ O ∧
      (∀ z ∈ O, ∀ k : Fin 2 → ℤ, z + fastShift (a := 2) (b := 2) k ∈ O) ∧
      MapsTo T O (poincareProdDom 2) ∧
      MapsTo (PlanarAssembly.total_chart G m0 m T) O (collisionFreeDomain 2) ∧
      AnalyticOnNhd ℝ (PlanarAssembly.total_chart G m0 m T) O ∧
      IsSymplecticOn 1 (PlanarAssembly.total_chart G m0 m T) O ∧
      (∀ z ∈ O, Bijective (fderiv ℝ (PlanarAssembly.total_chart G m0 m T) z)) ∧
      (∀ z ∈ O, ∀ k : Fin 2 → ℤ,
        PlanarAssembly.total_chart G m0 m T (z + fastShift (a := 2) (b := 2) k) = PlanarAssembly.total_chart G m0 m T z) ∧
      (∀ z ∈ O, ∀ z' ∈ O, PlanarAssembly.total_chart G m0 m T z' = PlanarAssembly.total_chart G m0 m T z →
        ∃ k : Fin 2 → ℤ, z' = z + fastShift (a := 2) (b := 2) k) ∧
      (∀ μ : ℝ, ∀ z ∈ O, fixedHamiltonian G m0 m μ (PlanarAssembly.total_chart G m0 m T z) =
        degenerateHamiltonian (a := 2) (b := 2) (PlanarAssembly.kepler_h (G * m0) m) (perturbation G m0 m T) μ z) ∧
      (∀ r : ℝ, 0 < r → r ≤ r0 → 2 * r ^ 2 ≤ δ →
        MapsTo (PlanarAssembly.total_chart G m0 m T) (cylinder (b := 2) V r)
          (circularTube G m0 m a (tubeRadius η (axisGap a)))) ∧
      AnalyticOnNhd ℝ (fun z : ℝ × Phase 4 => perturbation G m0 m T z.1 z.2)
        (Icc 0 1 ×ˢ closure (cylinder (b := 2) V r0)) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ z ∈ cylinder (b := 2) V r0, ∀ k : Fin 2 → ℤ,
        perturbation G m0 m T μ (z + fastShift (a := 2) (b := 2) k) = perturbation G m0 m T μ z) ∧
      HasFastDiffeomorphism (PlanarAssembly.kepler_h (G * m0) m) W ∧
      HasSecularBirkhoffForm (perturbation G m0 m T) V r0 1 P0 Ω β ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ I ∈ V, B ≤ |(β μ I).det|) ∧
      (∀ μ ∈ Icc (0 : ℝ) 1, ∀ I ∈ V, (β μ I).IsSymm) := sorry

/-- bpP:p13:n2: independent of the general-n KAM route. -/
theorem n2 (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (2 * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S := sorry

/-- bpP:p13:n-general: canonical pair bounds depend on a alone; n >= 2. -/
theorem n_general {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    let d := tubeD (axisGap a)
    let D := tubeBigD (axisGap a) (axisMax a)
    ∃ eps0 : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S := sorry

/-- bpP:p13:fixed: dimension split, exact frozen type. -/
theorem fixed {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S := sorry

end FixedAssembly
end KAM.Planetary

namespace KAM.Provider.Planetary
open KAM.Planetary

/-- Signature only; quarantined provider, matching the anchor binder for binder. -/
theorem planarTwoPlanetKAM (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ mu0 d D : ℝ, 0 < mu0 ∧ 0 < d ∧ d < D ∧
      ∀ mu : ℝ, 0 < mu → mu < mu0 →
        ∃ S : Set (Phase (2 * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          MovingKolmogorovSet G m0 m a mu eta d D S := sorry

/-- Signature only; quarantined provider, matching the anchor binder for binder. -/
theorem fixedSunPlanetaryKAM {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S := sorry

end KAM.Provider.Planetary
end

-- Design diagnostics only: every result still contains the explicit sorry proof.
#print axioms KAM.Planetary.PlanarAssembly.planar
#print axioms KAM.Planetary.FixedAssembly.n2
#print axioms KAM.Planetary.FixedAssembly.n_general
#print axioms KAM.Planetary.FixedAssembly.fixed
#print axioms KAM.Provider.Planetary.planarTwoPlanetKAM
#print axioms KAM.Provider.Planetary.fixedSunPlanetaryKAM
```
