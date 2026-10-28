# DESIGN-P1 independent design audit 1

**Overall verdict: PASS WITH NOTES.** All 76 declaration targets pass mathematical fidelity and applicability review. No false target, added conclusion-shaped premise, weakened source conclusion, widened constant dependence, or frozen-object substitution was found. The package/import plan needs the concrete housekeeping corrections N1–N3 before package briefs are dispatched. This is signature/design approval only: all 64 theorem bodies remain `sorry`; no proof or root is certified.

Audited snapshot: branch `inp-design-p1`, HEAD `f6c32fb6116c2b6857386116d4348e6aed250393`; comparison branch `inp` at `cf91d0eb53d4b0b03586d20e54b7fc8ede4b7150`. `git diff inp...HEAD` contains only the 909-line design document. The original 568-line signatures file has SHA-256 `78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7`; Appendix A is byte-identical to it. Read the assigned brief, AGENTS.md, PLAN, DECISIONS, and designer handoff. Compared the complete Part 1 blueprint and the Part 1 records of `docs/graph/P/packets/P-p1p2.nodes.md`, then searched the downstream blueprints. No designer/auditor coordination or delegation.

## Findings and proposed fixes

**N1 — Medium; package dependency corrections, with no signature change.** Design lines 207–215 and 227–230 put `isAddHaarMeasure_volume_phase` in downstream P1-7/Liouville, while P1-4/Chart's proof of `volume_angleScale_image` explicitly uses that helper at lines 253–254 (Decision 10). Following those instructions literally would create Chart → Liouville → Chart. Also Transport's `phys_pipeline` proof uses `isDiophantine_smul_iff` at line 268, but Transport's imports and package prerequisites omit Diophantine. The monolithic signature elaboration does not test either module boundary.

Proposed fix: move the Haar helper, unchanged, to Chart before `volume_angleScale_image`, remove its duplicate ownership from Liouville, and add Diophantine to Transport's imports and P1-2 to P1-6's prerequisites. The same three waves then work. Alternatively Chart can install the explicit product instance directly in its proof, leaving the named helper in Liouville; record that alternative explicitly. The unchanged helper signature and available proof term are:

```lean
theorem isAddHaarMeasure_volume_phase (d : ℕ) :
    (volume : Measure (Phase d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _
```

This proof term was independently elaborated for arbitrary `d`. Corrected dependency rows:

```text
Chart:      imports Algebra, KAM.Kepler.Basic, KAM.ODE.Basic;
            owns the Haar helper if its named form is reused here.
Transport:  imports Chart, Diophantine; P1-6 needs P1-4 and P1-2.
Liouville:  imports Chart; reuses the Haar helper, without redeclaring it.
```

**N2 — Low; exact helper names/types in the proof sketches need correction.** A separate `#check` probe verified the actual external APIs, not merely the draft's seven checks. The following literal names fail at this snapshot:

| Design reference | Result / proposed fix |
|---|---|
| `Basis.prod` (risk 1) | Use `Module.Basis.prod`, or explicitly open `Module`. |
| `Matrix.det_fromBlocks_zero₂₂` (risk 1) | Does not exist. Available triangular-block lemmas are `Matrix.det_fromBlocks_zero₂₁` and `Matrix.det_fromBlocks_zero₁₂`; an off-diagonal symplectic matrix needs a block permutation or the proposed bilinear-form route. |
| `IsClosed.isSigmaCompact` (line 288) | Use `isSigmaCompact_univ.of_isClosed_subset hs (Set.subset_univ s)`; an independent generic example elaborated. |
| `KAM.Strip.RealRestriction.realRestriction_fderiv` (line 259) | The declaration is `KAM.realRestriction_fderiv`. Its whole-strip domain is only a proof-pattern reference; retain the new arbitrary-open-domain bridge. |
| `ContinuousOn.measurableSet_preimage` (line 272) | Does not exist under that name. The same paragraph already supplies the valid route: `MeasurableSet.image_of_continuousOn_injOn` on local IFT sources. Remove the speculative name. |

Additional type details: `ContinuousLinearEquiv.ofBijective` takes kernel-equals-bottom and range-equals-top proofs, not a single `Function.Bijective` argument. `ContinuousLinearEquiv.finTwoArrow` identifies a two-element function space with a product; it is not directly the append equivalence on `Fin (d+d)`. `Fin.appendIsometry` is an isometry equivalence and still needs linearity to construct a CLE. The proposed inner-product transpose argument at lines 241–243 must not install a Euclidean inner-product structure on the existing max-norm carrier. Prefer the explicitly offered bilinear-form/toMatrix argument. These are proof-plan repairs, not counterexamples to any of the 76 targets.

**N3 — Low; graph provenance and optional coverage.** The referenced `docs/graph/P/DEPGRAPH.md` does not exist in this checkout. The packet records are available and were compared directly. Update the design's graph locator to the actual packet/assembled artifact. The optional `torus_orbit` target has blueprint label `bpP:p1:torus-orbit` (lines 237–242), but no Part 1 node in the reviewed packet; the older `draft/coverage-p1.md` does list it. Reconcile coverage or record exclusion before allocating optional P1-8. Do not treat an old coverage entry as a reviewed graph node. This confirms the substance of the designer's B1 without assuming the absent assembled file.

There are no F findings and no failed mathematical signatures requiring replacement statements.

## Declaration-by-declaration fidelity

Names below are relative to `KAM.Planetary`; labels are in `blueprint-P/parts/p1-hamiltonian-tools.tex`. Helpers inherit the indicated source contract. Steps folded into parent proofs remain proof obligations, not extra assumed hypotheses. Algebra uses continuous linear maps rather than matrices; every finite-dimensional linear form/map here is continuous, so this changes no carrier or quantifier. The matrix-specific identities are internal to the coordinate-free proof rather than public declarations.

| Lean name | Blueprint label / contract | Verdict | Reason |
|---|---|---|---|
| `linearField` | `bpP:p1:conv#data` | PASS | The displayed position/momentum formula, including its sign. |
| `hamiltonianVectorField_eq_linearField` | `bpP:p1:conv#data` | PASS | Definitional equality with the frozen total field. |
| `symplecticForm_antisymm` | `bpP:p1:omega-algebra(a)` | PASS | Equivalent bilinear antisymmetry. |
| `eq_zero_of_symplecticForm_right` | `bpP:p1:omega-algebra(a)` | PASS | Nondegeneracy in the second slot; first slot follows by antisymmetry. |
| `symplecticForm_linearField` | `bpP:p1:omega-algebra(a)` | PASS | Correct sign: Omega(w,X_l)=l(w). |
| `eq_linearField_iff` | `bpP:p1:omega-algebra(a)` | PASS | Existence and uniqueness characterization. |
| `symplecticForm_hamiltonianVectorField` | `bpP:p1:omega-algebra(a)` | PASS | Uses the frozen field and total fderiv, without a differentiability premise. |
| `bijective_of_symplectic` | `bpP:p1:omega-algebra(b)` | PASS | Nonzero conformal factor and finite-dimensional endomorphism. |
| `abs_det_of_symplectic` | `bpP:p1:omega-algebra(b)` | PASS | Absolute determinant and absolute conformal factor, exponent d. |
| `apply_linearField_comp_of_symplectic` | `bpP:p1:omega-algebra(b)` | PASS | Equivalent inverse-free formula given the preceding bijectivity theorem. |
| `symplectic_neg_iff` | `bpP:p1:omega-algebra(c)` | PASS | Bilinear replacement preserves the sign-independence assertion. |
| `IsChart` | `bpP:p1:chart` | PASS | Exactly analyticity and the delivered symplectic predicate; positivity/openness supplied at use sites. |
| `isChart_iff` | `bpP:p1:chart` | PASS | Unfolding interface, with no added property. |
| `IsChart.analyticOnNhd` | `bpP:p1:chart` | PASS | Projection of the definition. |
| `IsChart.symplectic` | `bpP:p1:chart` | PASS | Projection to the delivered predicate. |
| `IsChart.mono` | `bpP:p1:chart` | PASS | Restriction of both defining clauses. |
| `chartPullback` | `bpP:p1:chart` | PASS | Exactly c inverse times H composed with Psi, including total scalar inverse. |
| `IsChart.bijective_fderiv` | `bpP:p1:chart`; `bpP:p1:omega-algebra(b)` | PASS | Positive c implies nonzero c; no openness needed for pointwise analyticity. |
| `IsChart.abs_det_fderiv` | `bpP:p1:liouville`; `stepP:p1:li-det` | PASS | Correct determinant power c^d, on the chart domain. |
| `chart_field_differentiableAt_iff` | `bpP:p1:chart-field`; `stepP:p1:cf-diff` | PASS | Local IFT gives the reverse implication, even when O is not open. |
| `chart_field` | `bpP:p1:chart-field`; `stepP:p1:cf-field` | PASS | Unconditional total-field identity follows from differentiability equivalence. |
| `chart_orbit` | `bpP:p1:chart-orbit` | PASS | Both differentiability and HasDerivAt conclusions retained; interval assumption unnecessary. |
| `IsChart.comp` | `bpP:p1:typical(3)` | PASS | Correct MapsTo requirement and scalar product; delivered opposite product order commutes. |
| `chartPullback_comp` | `bpP:p1:typical(3)` | PASS | Scalar inverse multiplication identity remains true at zero factors. |
| `isChart_continuousLinearEquiv` | `bpP:p1:typical(2),(3)` | PASS | Analytic CLE plus the exact symplectic identity; typing helper. |
| `angleScale` | `bpP:p1:conv#data`; `bpP:p1:period-convert(a)` | PASS | Scales positions only, preserving the Kepler body. |
| `angleScaleCLM` | `bpP:p1:period-convert(a)` | PASS | Actual continuous linear map for the same scaling. |
| `angleScaleCLM_apply` | `bpP:p1:period-convert(a)` | PASS | Identification on the entire carrier. |
| `fullShift` | `bpP:p1:period-convert(c),(d)` | PASS | Full radian position lattice; dimension generalization preserves old instances. |
| `fullShift_eq_angleScale` | `bpP:p1:period-convert(a),(d)` | PASS | Correct 2*pi scaling of the integer position lattice. |
| `isChart_angleScale` | `bpP:p1:period-convert(a)` | PASS | Global positive-factor conformally symplectic chart. |
| `angleScale_add_angleShift` | `bpP:p1:period-convert(a)` | PASS | Correct c*k position shift; stronger for arbitrary real c. |
| `abs_det_fderiv_angleScale` | `bpP:p1:period-convert(a)` | PASS | Absolute determinant c^d for positive c. |
| `volume_angleScale_image` | `bpP:p1:period-convert(a)`; `bpP:p1:measure-use` | PASS | All-set outer-measure scaling by an invertible linear map; N1 concerns helper ownership only. |
| `chartPullback_angleScale` | `bpP:p1:period-convert(b)` | PASS | Literal Hamiltonian dictionary, with the inverse factor. |
| `angleScale_hamiltonianVectorField` | `bpP:p1:period-convert(b)` | PASS | Same-time transport, valid also at nondifferentiability by totality. |
| `fastShift_eq_angleScale` | `bpP:p1:period-convert(d)` | PASS | Uses the frozen fastShift, with Fin.append in the correct fast block. |
| `fderiv_real_slice` | `bpP:p1:hol-chart`; `stepP:p1:hc-real-derivative` | PASS | Explicit arbitrary-open-domain analytic/derivative bridge; no whole-strip assumption added. |
| `hol_chart` | `bpP:p1:hol-chart` | PASS | Correct complex bilinear identity on real points and agreement of total extensions. |
| `IsLatticeTorus` | `bpP:p1:lattice-torus` | PASS | All six clauses retained at L=angleShift; arbitrary L is a valid explicit generalization. |
| `torus_transport_cyl` | `bpP:p1:torus-transport(a)` | PASS | Frozen cylinder conclusion and exact fastShift; arbitrary L proof uses only L2/L3 and Q1/Q2. |
| `torus_transport_phys` | `bpP:p1:torus-transport(b)` | PASS | Frozen physical conclusion; positive Diophantine constant and strict exponent threshold retained. |
| `fderiv_chart_comp_torus` | `bpP:p1:torus-transport` | PASS | Full derivative identity with the required analytic maps and range guard. |
| `periodOne` | `bpP:p1:period-convert(c)` | PASS | Parameter scaling, without rescaling the Hamiltonian or time. |
| `IsTwoPiLatticeTorus` | `bpP:p1:period-convert(c)`; `bpP:p1:phys-pipeline` | PASS | All six clauses in the radian convention, including immersion and Lagrangian clauses. |
| `analyticOnNhd_periodOne_iff` | `bpP:p1:period-convert(c)` | PASS | Composition with a nonzero scalar CLE is reversible. |
| `fderiv_periodOne` | `bpP:p1:period-convert(c)` | PASS | Unconditional derivative formula is valid via comp_right_fderiv for a CLE. |
| `periodOne_lattice_iff` | `bpP:p1:period-convert(c)` | PASS | Correct parameter period conversion for arbitrary target shifts T. |
| `periodOne_injMod_iff` | `bpP:p1:period-convert(c)` | PASS | Both lattice-injectivity implications and their orientations retained. |
| `periodOne_hasDerivAt_iff` | `bpP:p1:period-convert(c)` | PASS | The two curves agree identically; same derivative and same time. |
| `isLatticeTorus_periodOne_iff` | `bpP:p1:period-convert(c)` | PASS | Packages every clause, including derivative injectivity and Lagrangianity. |
| `cyl_pipeline` | `bpP:p1:cyl-pipeline` | PASS | Unscaled K3, one angleScale, same w; exact pullback Hamiltonian and range inclusion. |
| `phys_pipeline` | `bpP:p1:phys-pipeline` | PASS | Radian torus of H composed with Phi gives frozen w=omega/(2*pi), plus full range equality. |
| `twoScaleDiophantine` | `bpP:p1:two-scale` | PASS | Correct first-block test and full l1 denominator in both alternatives. |
| `IsDiophantine.mono` | `bpP:p1:dio-basic(a)` | PASS | Dropped positivity is valid: nonpositive target gamma is automatic; otherwise compare positive denominators. |
| `isDiophantine_of_le_l1` | `bpP:p1:dio-basic(b)` | PASS | Strict positivity of nu retained; omitted positivity of gamma is harmless by a sign split. |
| `isDiophantine_smul_iff` | `bpP:p1:dio-basic(c)` | PASS | Positive scaling and gamma/s; valid for arbitrary gamma and tau. |
| `isDiophantine_min_of_mem_twoScale` | `bpP:p1:dio-basic(d)` | PASS | Split by the first block and decrease the numerator over a positive denominator. |
| `smul_mem_twoScale` | `bpP:p1:dio-sources(a)` | PASS | Both constants divided by the same positive scale. |
| `cp10_isDiophantine` | `bpP:p1:dio-sources(a)` | PASS | Exact minimum constant and positive existential gamma with exponent greater than the whole dimension. |
| `cp09_isDiophantine` | `bpP:p1:dio-sources(b)` | PASS | Euclidean norm written explicitly; mu at least one and tau>d*mu imply the required exponent. |
| `isAddHaarMeasure_volume_phase` | `bpP:p1:liouville (helper)` | PASS | Actual product-volume Haar property; no global instance; move ownership as in N1. |
| `unitCell` | `bpP:p1:liouville-lattice` | PASS | Ambient position cell only; all momenta unrestricted. |
| `chart_measure_image` | `bpP:p1:liouville` | PASS | Lebesgue measurability, sharp upper bound, and injective equality all retained. |
| `measurableSet_chart_image` | `bpP:p1:liouville` | PASS | Borel result for any Borel subset of O by countably many local inverses. |
| `liouville_lattice` | `bpP:p1:liouville-lattice` | PASS | Full lattice, cell image, exact volume, positivity equivalence, and bounded-cell finiteness. |
| `liouville_lattice_measurableSet` | `bpP:p1:liouville-lattice` | PASS | Separate Borel interface; no null-measurable/Borel substitution. |
| `measure_chart_image` | `bpP:p1:liouville-lattice`; `bpP:p1:P6 measure-positive(b)` | PASS | Byte-identical theorem block in KeplerSignaturesP.lean; full-lattice caveat retained. |
| `unitCube` | `bpP:p1:torus-union` | PASS | Half-open unit cube, of volume one also in dimension zero. |
| `torus_union` | `bpP:p1:torus-union` | PASS | Exact max-norm bound and power 2*d, with Lebesgue measurability only. |
| `torus_union_measurableSet_of_sigmaCompact` | `bpP:p1:torus-union(B1)` | PASS | Sigma-compact image and Borelness with no injectivity premise. |
| `torus_union_measurableSet_of_injOn` | `bpP:p1:torus-union(B2)` | PASS | Borel domain, Lipschitz continuity, and injectivity on the actual product domain. |
| `torus_union_lower` | `bpP:p1:torus-union` | PASS | Lower estimate, positivity equivalence, and finiteness equivalence, with positive lower constant. |
| `torus_union_saturation` | `bpP:p1:torus-union` | PASS | Full tori equal the countable lattice saturation of the cell image. |
| `nullMeasurableSet_torus_union_saturation` | `bpP:p1:torus-union` | PASS | Lebesgue saturation and separate conditional Borel conclusion. |
| `torus_orbit` | `bpP:p1:torus-orbit` | PASS | Global solution, equality with every global competitor, and constant energy; exact delivered solution predicate. |

## Consumers

**Verdict: PASS, within each blueprint's stated lattice scope.** Direct Part 1 references were searched throughout I/N/P; I and N have no direct Part 1 consumer that changes these targets. The brief's generic `\Nref{bpN:p3:` search was also run in I/P and N Parts 7/11/12: those consumers use the delivered ODE layer, not a newly substituted Part 1 solution predicate. This report does not re-audit the entire N Part 3 layer.

| Consumer / exact source location | Applicability |
|---|---|
| P3 `p3b-two-scale-limit.tex:216`; P5 `:260–263` | `cyl_pipeline` accepts the unscaled period-one `K3`, the chart pullback, Q1/Q2 from `phi-chart`, and the supplied image containment. One factor `2*pi`; same frequency w. Equality of locally defined Hamiltonians is transferred to derivatives on the consumer's open domain. |
| P3 period dictionary; P2 `use5` | Scaling positions alone is the all-angle dictionary. The reciprocal angle/action canonical conversion in P2 is a different linear chart, covered by `isChart_continuousLinearEquiv`; it must not be identified with `angleScale`. |
| P5 `:274`, `:310` | `chart_measure_image` gives injective equality on the selected measurable cell; `volume_angleScale_image` gives `(2*pi)^n`. `torus_union` handles null parameter slices. Prod.swap restores the source's action/angle order for saturation. |
| P6 `p6-newtonian-models.tex:253–258` | Lebesgue input uses `liouville_lattice`; Borel input uses its separate Borel theorem. `measure_chart_image` is exactly the Kepler Borel wrapper, not a replacement for the more general Lebesgue theorem. |
| P7 `p7-kepler-poincare.tex:196–207`, `:226–237` | Delivered `poincareProdCast` and its analytic/symplectic results give a homogeneous chart on `Phase (n*2)`; the cast is accounted for. The polar/full-lattice composition fits transport with `angleShift` after scaling, or `fullShift` before it. Part 1 owns angleScale/fullShift; P7-6 must remove its draft copies. |
| P8 `p8-secular-form.tex:101`; P9 `p9-secular-spectrum.tex:120–143` | Field identity and chart composition use the frozen form/sign and total field. Heterogeneous chart data is first passed through the delivered cast. |
| P11 `p11-cp09-preparation.tex:87–90`, `:250–252` | After the polar chart all position coordinates carry the lattice. `IsChart.comp`, physical transport with `L=angleShift`, and lattice Liouville apply to the epsilon-chart; determinant factor is epsilon^(2*n). The earlier fast-only lattice assertion is used before polar conversion only as fast-lattice data. |
| P12 `p12-planar-assembly.tex:138–153` | The blueprint explicitly redoes cylinder transport. Use `chart_field_differentiableAt_iff`, `chart_orbit`, `measurableSet_chart_image`, and injective equality in `chart_measure_image` on `S ∩ F`. Its cylinder torus is not required to satisfy full-position-lattice LT. |
| P13 `p13-fixed-assembly.tex:115–116` | Same direct transport/measure proof as P12, with the fixed Hamiltonian. No misuse of `phys_pipeline` or full-lattice Liouville is required. |
| P14 `p14a-amd-expsafe.tex:253`; optional torus-orbit | `chart_orbit` is pointwise on the actual solution interval. The optional torus result uses the delivered arbitrary-interval uniqueness with J=univ and ham_energy, requiring only the stated open W and C2 H. |

The design's section 7.2 shorthand suggesting `phys_pipeline`/lattice Liouville among P12/P13 imports is not a valid reason to apply them to Cartesian cylinder tori. Its Decision 4 and the explicit blueprint scope warning at Part 1 lines 208–209 correctly preserve that restriction.

## Frozen objects, definitions, dropped premises, packages

**Frozen-object verdict: PASS.** Read `KAM/Frozen/Defs/{SymplecticForm,HamiltonianVectorField,IsDiophantine}.lean` and `KAM/Frozen/Planetary/Defs/{Phase,FastShift,IsCylinderTorus,IsPhysicalTorus}.lean`, along with the delivered `Kepler/Basic`, `ODE/Basic`, `ODE/Hamiltonian`, and `ODE/Uniqueness` interfaces. The targets use those exact constants. `linearField` is a linear-functional object with an explicit bridge to the frozen field. `IsChart` uses `KAM.Kepler.IsSymplecticOn`, not an assumed parallel symplectic predicate. No signature asserts a replacement definition equal to a frozen solution predicate. The only solution predicate directly used is delivered `KAM.ODE.IsSolutionIn`; Newton/Hamiltonian/restricted frozen solution bridges remain in their existing owning layers.

**Definition verdict: PASS.** All twelve new definitions have their intended values on their whole carriers. No junk off-domain value is used to infer a derivative. `IsLatticeTorus L` generalizes the lattice explicitly; the transport proof never needs an unprovided group law for L: Q2 gives a single m, L2 identifies `K(theta+m)` with `K(theta)+L m`, and L3 finishes. All six lattice-torus clauses are source premises defining the input object. The frozen output predicate is not assumed. `hagree` entails reality on real points and leaves arbitrary extensions harmless outside the preimage of V. No new global instance is introduced.

**Dropped-premise verdict: PASS.** Chart analyticity at each z supplies a neighborhood on which the IFT works, so openness of the chosen O is unnecessary for field/orbit/transport and pipeline targets. Orbit transfer is pointwise, so J need not be an interval. The Diophantine lemmas with nonpositive numerator have automatic conclusions; for positive numerator the denominator is positive and the standard monotonicity argument applies. The norm-comparison target still requires `0 < nu k`; gamma positivity was also dropped there (not listed explicitly in section 4.1) and is harmless by the same sign split. Positivity of tau/gamma in the scaling and two-scale elementary clauses is likewise unnecessary; positivity is retained at the physical/cylinder existential consumer interfaces. Definitions outside the source's positive-parameter range extend the formulas without claiming chart invertibility at c=0. Negative Lambda in torus_union is harmless: the domain is subsingleton (or empty); handle dimension zero separately, where the singleton has volume one and Lambda^0=1. For d>0 its image is null.

**Package verdict: PASS WITH NOTES N1–N2.** Eight focused modules, estimated 80–600 lines each, with the planned split threshold at 1,000 for Liouville, are credible under the 1,500-line cap. The intended dependency order works after N1; no provider/Poincare import is needed in Part 1. The arbitrary-open real-slice derivative bridge is explicitly assigned to HolChart, so the packet's `stepP:p1:hc-real-derivative` SOURCE_GAP is a designed proof obligation, not a claimed delivered result. A successful design audit does not close that proof obligation.

## Independent checks and limits

All Lean invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource overrides, cache updates, full builds, or state-changing git commands. Other workers' processes were not altered.

1. Exactly once: copied the original signatures to `.drafts/scratch/PPart1Signatures-audit-1.lean`, then ran `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .drafts/scratch/PPart1Signatures-audit-1.lean`. **Exit 0: exactly 64 warnings, all `declaration uses sorry`; no errors.** The file's #synth and seven #check commands also printed their expected results. The two SHA-256 values matched.
2. Separate `.lake/abi-scratch/P1AuditNames.lean` probe: checked the external composition/IFT/Jacobian/Borel/determinant APIs, the named proof-sketch helpers, delivered KAM bridges, and the generic product Haar proof term. **Exit 1**, with precisely the five unknown names listed in N2. All remaining checked names elaborated. The Jacobian null-measurable equality API and differentiable-null-image API have the required domain/injectivity assumptions.
3. Correction probe: checked the replacement declarations and a generic closed-set sigma-compactness example. The final run with both required KAM imports **exited 0**. An earlier correction run omitted `KAM.Measure.Lipschitz` and failed only to find `KAM.appendMeasurableEquiv`; that declaration is available with its owning import. This was an audit-probe import omission, not a design defect.
4. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`: **exit 0**. Output: `check_lean_modules: PASS (401 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`.
5. No implementation modules were changed or created, so no new module build target exists; the specified targeted Lean elaboration was used instead of a library build. All audit-created scratch sources were deleted afterwards. Only this report remains changed.
6. `#print axioms KAM.ODE.ham_smooth_c1`, `KAM.ODE.ham_energy`, and `KAM.ODE.gen_uniqueness`: each prints `[propext, Classical.choice, Quot.sound]`. The 64 draft theorem bodies are placeholders and provide no axiom-clean result to certify; elaboration success is not proof closure.
7. Final `git diff --check` and report row-count/working-tree checks passed.

No new suspected defect in a pinned mathematical source was established; no source PDF claim was needed beyond the supplied blueprint/packet contracts. The blueprint/graph discrepancies and design deviations discussed above are reported, not silently repaired. No frozen file, manifest, design, original signature, generated file, or handoff was edited. No commit was made.
