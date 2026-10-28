# Independent S8-4 package audit 1

Overall package verdict: **FAIL** (public short-name hygiene F1, and incomplete literal q4-a proof-cut coverage F2). The three signed theorem statements and their mathematical proof routes pass the source review; validation receipts follow below. This is an infrastructure package: no frozen anchor or physical KAM/torsion theorem is sealed by it.

Audited worktree: `/root/code/KAM-inp-s84`; HEAD `f581afcd1e99f301428ecb5b630c15aaa44ef023`; comparison `inp` at `2b7e97e2173c0d889c0b5d22c2c1f762fca4366c` when inspected. `git diff inp...HEAD` warned of two merge bases and selected `9400863e51e5f140a497a3774d3dff7b479e0d04` (the other is `aff048b7e4ec66d1eb3f7ac45e5b03552f95434e`). The comparison contains 20 Quartic files (2211 lines) and five inherited DiagonalJet files (942 lines). Only the 20 Quartic files were audited; dependencies were inspected for applicability/import quarantine, not recertified. The handoff was already untracked at audit start. Only this report is retained as an auditor repository change; temporary probes reside under `.lake/abi-scratch/` and are removed.

Authority read: AGENTS.md, PLAN.md, DECISIONS.md, supplied package audit brief and handoff/AUDIT FOCUS, P810 design and both design audits, exact draft signatures, track P statement conventions and relevant frozen definitions. The user's explicit absolute report destination overrides the generic brief's main-worktree destination. There are no provider exports here, so frozen/provider type equality and seal-body probes are inapplicable; the corresponding fresh probes use copied signed theorem declarations under distinct names with direct applications of the proved exports.

Pinned signatures SHA-256: `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`.
Blueprint p8 SHA-256: `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc`.
Design SHA-256: `f555e21a468123ce906f6818359cb8faaffc5d0435ea0f70c65967cec38722c4`.

## Findings and scope limits

**F1 — FAIL, public short-name reuse / enclosing-namespace shadow.** `KAM/Planetary/SecularForm/Quartic/PairJet.lean:29` declares public `KAM.Planetary.SecularForm.iteratedFDeriv_comp_clm_of_isOpen`. The pre-existing public `KAM.Planetary.iteratedFDeriv_comp_clm_of_isOpen` is at `KAM/Planetary/PGAssembly/JetsPolar.lean:34` (already on inp; commits `5c1908bf`, `c19d5117`, `ab33230b`). Its theorem is generic in the field and finite differentiability order; the Quartic copy specializes to ℝ and order four. Both are true, and their fully qualified names differ, but the explicit AUDIT FOCUS forbids a public short name already used elsewhere in KAM. The new declaration also takes precedence over the enclosing-namespace declaration in unqualified SecularForm resolution. Rename the Quartic helper and its local uses, or arrange an approved shared helper dependency without changing signed declarations; auditor made no repair. No new `_root_` declaration or namespace-root replacement was found. The other textual leaf-name match, `exists_angle` in `PGMeasure/Polar.lean:482`, is private and therefore does not violate the public-name rule.

**F2 — FAIL, graph proof-cut completeness (signed statements still pass).** The design inventory `P810-LEAN-DESIGN.md:141` assigns the entire `stepP:p8:q4-a` at `blueprint-P/parts/p8-secular-form.tex:232` to S8-4. Its final sentence is “The conversion is the expansion of $(1-t)^{1/2}$ with $t=|u|^2/(4\Lambda)$.” The proposition at p8:221 explicitly concludes the general W₂/W₄ conversion with the A/4, A′/4 and B/8 correction terms. None of the 119 new public declarations states this conversion or an equivalent fourth-jet chain rule specialized to the eccentricity/canonical-coordinate map. `quartic_pair_scaling` proves only the exact full-function rescaling; `quartic_scaling` proves analyticity; `quartic` proves structure and two diagonal coefficients directly. The diagonal computation does not export the mixed B/8 conversion. Consequently the three signed exports are proved, but the requested complete graph-cut slice is not fully exported. This is a source/graph coverage failure, not a refutation of a Lean theorem. Supply an explicit conversion helper/jet equality, or have the orchestrator explicitly narrow/defer this sub-obligation in the graph; do not mark the entire prose cut complete merely from exact signature equality. Auditor does not modify the design or signatures.

**N1 — provenance note.** Neither this checkout's nor the live `/root/code/KAM-inp` copy of `docs/campaign/OVERNIGHT.md` contains the cited 13:08 S8-D/S8-X ruling. The controlling design at lines 430–434,454–457 explicitly assigns literal DiagonalJet/CrossJet helpers and says “DiagonalJet/CrossJet return identities for the literal pair average, Quadratic sums them.” The current S8-4 brief agrees. S8-4 consumes S8-D through `pairSlowSecular_diag_jet` at `Quartic/Diagonal.lean:85,122`; it does not assume a diagonal coefficient. CrossJet/S8-X is a prerequisite of S8-Q, not the S8-4 row, so no direct CrossJet consumption is required here. This audit does not invent the missing historical log entry.

**N2 — handoff wording.** “pair decomposition of secular D false on the perturbation_analytic polydisc” means the Lean term `secular D false`: `false` selects the fixed model. `PairDecomp.lean:135` proves its equality to the finite sum of literal pair averages on the real analytic polydisc. It does not claim a false proposition. The integrability premises of intermediate average lemmas are discharged by separation and compactness before use.

**N3 — mathematical completion boundary.** All named S8-4 signed exports have implementations; F2 identifies the unexported part of the assigned graph cut. The literal signed interface is narrower than every sentence of the blueprint: there is no separate exported theorem expressing the general W₂/W₄ square-root conversion displayed in p8:221, no independently named c-to-radialR1 equation, and no repaired CP11 polynomial certificate. The signed diagonal identities plus transparent `radialR1` pay q4-c's algebraic identification; the corrected polynomial certificate remains explicitly unpaid by design:382–399. The canonical quartic is proved directly, so it does not rely on an unproved general conversion formula. Do not describe these three signatures as formalizing every sentence of the prose proposition. Mixed c3..c6 values and torsion remain Part 11b obligations. No S8-Q qf-diag2 ownership is silently transferred here.

## Signed exports and graph coverage

| Export / node | Verdict | Evidence |
|---|---|---|
| `quartic` / `bpP:p8:quartic` | PASS WITH NOTES | Exact signed type; explicit six-coefficient witness; F1 affects a helper in its proof chain. No frozen anchor closed. |
| `quartic_pair_scaling` | PASS | Exact signed type; literal pair factor -G m_i m_j/a_j. |
| `quartic_scaling` | PASS | Exact signed type; real analyticity on the separated domain, including circular points. |
| `q4-str` (p8:231) | PASS WITH NOTES | PairAverage/PairDecomp → pairData joint analyticity → local O(2) symmetry → homogeneous polynomial/Weyl reduction → six explicit linear coefficients → Jet finite-sum assembly. F1 is naming hygiene. |
| `q4-a` (p8:232) | FAIL (incomplete export) | Literal scaling and separated analyticity pass; general W₂/W₄ canonical conversion remains unexported, F2. |
| `q4-b` (p8:233) | PASS | S8-D O(|u|^6) literal expansion → analytic Taylor uniqueness with factor 24 → c0; continuous integral swap → c1. |
| `q4-c` (p8:234) | PASS WITH NOTES | Both exact diagonal formulas and definition of radialR1; its algebraic identification is reducible arithmetic, not printed-r1 equality. N3 limits claims. |

The five required definition bodies are text-identical to the signature file. The three required theorem headers are text-identical as well, including binder/quantifier order and expression spelling. `hn` in quartic and `hij`, `hI`, `hSep` in pair scaling are already signed premises, not added assumptions. The proof actually uses `hJ`, chart-domain bounds and positive masses; unused signed premises do not weaken the specified conclusions. Analytic coefficient constants depend on only the original fixed data and the two actions; no third action is smuggled into the witness.

Proof review: `avg_pair` proves the distinct-coordinate pushforward measure including the (2π)^(n−2) factor; continuous compact-square kernels are integrable before `integral_prod`. `pairData` retains G,m0 and the two masses and has no bundled conclusion. Analyticity is joint before differentiation in slow variables. Rotation/reflection equalities hold as germs at zero, sufficient to identify actual fourth derivatives under continuous linear maps; no global orbit symmetry outside the neighbourhood is required. The invariant reduction represents the multilinear diagonal as a homogeneous polynomial of degree four, and the six test vectors invert its coefficient system. Taylor uniqueness uses analytic order, rather than taking an unjustified derivative of an O-term. Swap has a continuity guard discharged on the pair neighbourhood. Scaling changes variables twice with both positive Kepler Jacobians, establishes positive radial separation, complexifies using bilinear coordinate squares, obtains uniform slit-plane conditions by compactness, applies e_param, and restricts the resulting complex analytic function to real parameters. No assumed hard proof step survives in a signed export.

## Every new public declaration

Names have prefix `KAM.Planetary.SecularForm.`. Row locations are relative to `KAM/Planetary/SecularForm/`. PASS in this table concerns that declaration's statement/body; the package-level naming failure is explicit on its own row. Conditional generic helpers are distinguished by their names and are discharged by the application chain above.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| quartic | `quartic` (Quartic.lean:44) | PASS | Joint witness, exact ordered action domain, 1/24 normalization and both diagonal values. |
| q4-str | `pairQuartic` (Quartic/Coefficients.lean:30) | PASS | Literal fourth Fréchet derivative on the repeated vector, divided by 24; no surrogate polynomial. |
| q4-str | `testPt` (Quartic/Coefficients.lean:34) | PASS | Six fixed planar test pairs, including the asymmetric (e1,2e1) needed to separate c4 and c5. |
| q4-str | `quarticCoeff` (Quartic/Coefficients.lean:39) | PASS | Explicit linear inversion of the six literal jet evaluations. Valid representation and analyticity proved on the ordered positive action domain. |
| q4-str | `pairQuartic_eq` (Quartic/Coefficients.lean:49) | PASS | Six test-vector evaluations invert the six-monomial matrix; joint fourth derivative yields analytic coefficients. |
| q4-str | `analyticAt_pairQuartic` (Quartic/Coefficients.lean:71) | PASS | Six test-vector evaluations invert the six-monomial matrix; joint fourth derivative yields analytic coefficients. |
| q4-str | `analyticAt_quarticCoeff` (Quartic/Coefficients.lean:114) | PASS | Six test-vector evaluations invert the six-monomial matrix; joint fourth derivative yields analytic coefficients. |
| quartic; q4-a/c | `quarticMonomials` (Quartic/Defs.lean:29) | PASS | Intended six invariant quartic monomials on all planar pairs. |
| quartic; q4-a/c | `radialR1` (Quartic/Defs.lean:33) | PASS | Exact derivative formula on all real axes; no printed CP11 polynomial substituted. |
| quartic; q4-a/c | `unitPosition` (Quartic/Defs.lean:37) | PASS | Literal dimensionless regular Kepler orbit expression; physical/analytic use is guarded by eccentricity bounds. |
| quartic; q4-a/c | `separatedDomain` (Quartic/Defs.lean:42) | PASS | Exact open domain: positive ratio below one, each eccentricity <1/4, strict radial separation. |
| quartic; q4-a/c | `dimensionlessPair` (Quartic/Defs.lean:46) | PASS | Literal normalized double Bochner integral of inverse physical distance. Total integral/inverse conventions outside the separated domain are not used to claim physical regularity. |
| q4-b/c | `planeSq_smul_e1` (Quartic/Diagonal.lean:32) | PASS | Consumes literal S8-D sixth-order remainder; Taylor uniqueness reads c0/c1, with swap for the outer planet. |
| q4-b/c | `planeLength_smul_e1` (Quartic/Diagonal.lean:35) | PASS | Consumes literal S8-D sixth-order remainder; Taylor uniqueness reads c0/c1, with swap for the outer planet. |
| q4-b/c | `pairQuartic_of_ray` (Quartic/Diagonal.lean:43) | PASS | Consumes literal S8-D sixth-order remainder; Taylor uniqueness reads c0/c1, with swap for the outer planet. |
| q4-b/c | `quarticCoeff_zero` (Quartic/Diagonal.lean:75) | PASS | Consumes literal S8-D sixth-order remainder; Taylor uniqueness reads c0/c1, with swap for the outer planet. |
| q4-b/c | `quarticCoeff_one` (Quartic/Diagonal.lean:112) | PASS | Consumes literal S8-D sixth-order remainder; Taylor uniqueness reads c0/c1, with swap for the outer planet. |
| q4-str | `PairVec` (Quartic/Invariant.lean:30) | PASS | Transparent Pi carrier for two planar vectors. |
| q4-str | `exists_poly_of_multilinear` (Quartic/Invariant.lean:34) | PASS | Explicit homogeneous degree-four polynomial and proved Weyl invariant reduction; conditional helper is distinct. |
| q4-str | `quartic_form_of_invariant` (Quartic/Invariant.lean:63) | PASS | Explicit homogeneous degree-four polynomial and proved Weyl invariant reduction; conditional helper is distinct. |
| q4-str | `pairProjLM` (Quartic/Jet.lean:29) | PASS | Coordinate extraction of the two planet vectors, proved real-linear. |
| q4-str | `pairProj` (Quartic/Jet.lean:36) | PASS | Continuous-linear realization of pairProjLM. |
| q4-str | `pairProj_apply` (Quartic/Jet.lean:39) | PASS | Continuous linear pair projection and eventual pair decomposition permit differentiation of the finite sum. |
| q4-str | `action_axes_lt` (Quartic/Jet.lean:42) | PASS | Continuous linear pair projection and eventual pair decomposition permit differentiation of the finite sum. |
| q4-str | `quartic_jet` (Quartic/Jet.lean:48) | PASS | Continuous linear pair projection and eventual pair decomposition permit differentiation of the finite sum. |
| q4-str | `exists_angle` (Quartic/Orthogonal.lean:25) | PASS | Elementary O(2) rotation/reflection classification from orthogonality. |
| q4-str | `orth_cases` (Quartic/Orthogonal.lean:38) | PASS | Elementary O(2) rotation/reflection classification from orthogonality. |
| q4-str | `pairData` (Quartic/PairAnalytic.lean:30) | PASS | Two-planet restriction of original positive masses and G,m0; only positivity and dimension fields bundled, no theorem assumed. |
| q4-str | `pairEmbLM` (Quartic/PairAnalytic.lean:40) | PASS | Real-linear rearrangement of two actions and four slow coordinates into Slow 2. |
| q4-str | `pairEmb` (Quartic/PairAnalytic.lean:49) | PASS | Continuous-linear realization of pairEmbLM. |
| q4-str | `pairEmb_apply` (Quartic/PairAnalytic.lean:52) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str | `vec2_eta` (Quartic/PairAnalytic.lean:55) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str | `pairSlowSecular_pairData` (Quartic/PairAnalytic.lean:58) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str | `action_axis` (Quartic/PairAnalytic.lean:63) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str | `axis_mem_axes` (Quartic/PairAnalytic.lean:73) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str | `pair_secular_nbhd` (Quartic/PairAnalytic.lean:81) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str | `analyticAt_pairSlowSecular` (Quartic/PairAnalytic.lean:122) | PASS | Two-planet data and linear embedding identify literal averages on an open neighbourhood; positive ordered axes only. |
| q4-str / qf-pair | `avg_pair` (Quartic/PairAverage.lean:93) | PASS | Distinct-coordinate pushforward and compact integrability justify Fubini; all 2π factors retained. |
| q4-str / qf-pair | `continuous_ppos` (Quartic/PairDecomp.lean:37) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `planeSq_ppos_sub_pos` (Quartic/PairDecomp.lean:43) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `perturbation_false_pairs` (Quartic/PairDecomp.lean:68) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `avg_finset_sum` (Quartic/PairDecomp.lean:82) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `secular_eq_avg` (Quartic/PairDecomp.lean:88) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `pairKernel` (Quartic/PairDecomp.lean:92) | PASS | Literal negative gravitational pair potential using original orbit positions. |
| q4-str / qf-pair | `continuous_pairKernel_comp` (Quartic/PairDecomp.lean:95) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `integrableOn_pairKernel` (Quartic/PairDecomp.lean:111) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `pairKernel_avg` (Quartic/PairDecomp.lean:122) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str / qf-pair | `secular_false_eq_pairs` (Quartic/PairDecomp.lean:135) | PASS | Literal fixed-model pair sum on analytic real polydisc; separation discharges continuity and integrability. |
| q4-str | `iteratedFDeriv_comp_clm_of_isOpen` (Quartic/PairJet.lean:29) | FAIL | F1: duplicates existing public short name in enclosing namespace. |
| q4-str | `pair_matW_invariant` (Quartic/PairJet.lean:45) | PASS | Open-set chain rule transports local O(2) invariance to the fourth derivative; no invariant tensor assumed. |
| q4-str | `pair_contDiffOn` (Quartic/PairJet.lean:64) | PASS | Open-set chain rule transports local O(2) invariance to the fourth derivative; no invariant tensor assumed. |
| q4-str | `pair_quartic_structure` (Quartic/PairJet.lean:80) | PASS | Open-set chain rule transports local O(2) invariance to the fourth derivative; no invariant tensor assumed. |
| q4-a | `poincare_fst_eq_unitPosition` (Quartic/PairScaling.lean:31) | PASS | Literal orbit rescaling; positive outer axis permits norm scaling; constants pulled through both integrals. |
| q4-a | `quartic_pair_scaling` (Quartic/PairScaling.lean:38) | PASS | Literal orbit rescaling; positive outer axis permits norm scaling; constants pulled through both integrals. |
| q4-str | `PairW` (Quartic/PairSymmetry.lean:33) | PASS | Transparent product carrier for two planar vectors. |
| q4-str | `matW` (Quartic/PairSymmetry.lean:36) | PASS | Block continuous-linear action of a real 2 by 2 matrix. |
| q4-str | `matW_apply` (Quartic/PairSymmetry.lean:40) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `rotW` (Quartic/PairSymmetry.lean:43) | PASS | Simultaneous planar rotation. |
| q4-str | `reflW` (Quartic/PairSymmetry.lean:45) | PASS | Simultaneous reflection of second coordinates. |
| q4-str | `continuous_rotW` (Quartic/PairSymmetry.lean:51) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `continuous_reflW` (Quartic/PairSymmetry.lean:54) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `pairEmb_rotW` (Quartic/PairSymmetry.lean:58) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `pairEmb_reflW` (Quartic/PairSymmetry.lean:63) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `eventually_pair_mem` (Quartic/PairSymmetry.lean:68) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `pair_rot_invariant` (Quartic/PairSymmetry.lean:82) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-str | `pair_refl_invariant` (Quartic/PairSymmetry.lean:94) | PASS | Local rotation/reflection invariance derived from evenness after embedding the literal two-planet system. |
| q4-a | `quartic_scaling` (Quartic/Scaling.lean:33) | PASS | Restricts holomorphic integral to real parameters, takes real part, and uses local agreement. |
| q4-a | `qscKC` (Quartic/ScalingComplex.lean:29) | PASS | Principal complex square-root power; analytic uses explicitly require slit-plane membership. |
| q4-a | `qscU0` (Quartic/ScalingComplex.lean:32) | PASS | First algebraic complexified orbit coordinate with root supplied as parameter. |
| q4-a | `qscU1` (Quartic/ScalingComplex.lean:36) | PASS | Second algebraic complexified orbit coordinate with root supplied as parameter. |
| q4-a | `qscSepK` (Quartic/ScalingComplex.lean:40) | PASS | Sum of two complex coordinate squares, not a conjugate/Hermitian norm; correct holomorphic extension. |
| q4-a | `qscIntK` (Quartic/ScalingComplex.lean:45) | PASS | Inverse square-root separation times both Kepler Jacobians, with supplied roots. |
| q4-a | `qscIntC` (Quartic/ScalingComplex.lean:51) | PASS | qscIntK with both principal roots substituted. |
| q4-a | `qscSep` (Quartic/ScalingComplex.lean:55) | PASS | qscSepK with both principal roots substituted. |
| q4-a | `qscGood` (Quartic/ScalingComplex.lean:59) | PASS | Explicit slit-plane and nonzero-denominator branch conditions; proved near each separated real parameter, not assumed in final export. |
| q4-a | `qsc_diffAt_K` (Quartic/ScalingComplex.lean:63) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_diffAt_KC` (Quartic/ScalingComplex.lean:75) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_contAt_sepK` (Quartic/ScalingComplex.lean:95) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_contAt_intK` (Quartic/ScalingComplex.lean:102) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_contAt_kC` (Quartic/ScalingComplex.lean:113) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_contAt_KC` (Quartic/ScalingComplex.lean:118) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_contAt_sep` (Quartic/ScalingComplex.lean:142) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qscEmb` (Quartic/ScalingComplex.lean:168) | PASS | Five real parameter coordinates embedded into complex Pi space. |
| q4-a | `qsc_planeSq_lt` (Quartic/ScalingComplex.lean:171) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_kC_real` (Quartic/ScalingComplex.lean:175) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_qscU_zero` (Quartic/ScalingComplex.lean:186) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_qscU_one` (Quartic/ScalingComplex.lean:192) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_sep_real` (Quartic/ScalingComplex.lean:198) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_good_real` (Quartic/ScalingComplex.lean:216) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qsc_intC_real` (Quartic/ScalingComplex.lean:249) | PASS | Explicit bilinear squared separation, slit-plane powers, joint continuity, holomorphy and agreement on real parameters. |
| q4-a | `qscEmbLM` (Quartic/ScalingEmb.lean:26) | PASS | Real-linear realization of qscEmb. |
| q4-a | `qscEmbCLM` (Quartic/ScalingEmb.lean:34) | PASS | Continuous real-linear realization of qscEmb. |
| q4-a | `qscEmbCLM_apply` (Quartic/ScalingEmb.lean:37) | PASS | Real-linear parameter embedding and openness of the exact separated domain. |
| q4-a | `qsc_isOpen_separatedDomain` (Quartic/ScalingEmb.lean:39) | PASS | Real-linear parameter embedding and openness of the exact separated domain. |
| q4-a | `qscU` (Quartic/ScalingReal.lean:30) | PASS | Regular orbit as function of eccentric longitude; agrees definitionally with unitPosition after keplerLong. |
| q4-a | `qsc_unitPosition` (Quartic/ScalingReal.lean:34) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_planeSq_two` (Quartic/ScalingReal.lean:37) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_planeDot_two` (Quartic/ScalingReal.lean:40) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_continuous_planeLength` (Quartic/ScalingReal.lean:43) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_continuous_qscU` (Quartic/ScalingReal.lean:48) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_periodic_qscU` (Quartic/ScalingReal.lean:55) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_planeLength_qscU` (Quartic/ScalingReal.lean:58) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_sep_lower` (Quartic/ScalingReal.lean:72) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_sep_pos` (Quartic/ScalingReal.lean:79) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qscG` (Quartic/ScalingReal.lean:91) | PASS | Separated inverse distance multiplied by the two longitude Jacobians. |
| q4-a | `qsc_continuous_sep` (Quartic/ScalingReal.lean:94) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_continuous_G` (Quartic/ScalingReal.lean:101) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qsc_dimensionlessPair` (Quartic/ScalingReal.lean:108) | PASS | Positive separated radius and two exact Kepler-longitude substitutions retain both Jacobians. |
| q4-a | `qscAvgC` (Quartic/ScalingTube.lean:29) | PASS | Normalized complex cell integral with factor (2π)^(-2). |
| q4-a | `qsc_tube` (Quartic/ScalingTube.lean:32) | PASS | Compact-angle tube yields uniform branch conditions; e_param proves holomorphic normalized integral. |
| q4-a | `qsc_differentiableOn` (Quartic/ScalingTube.lean:61) | PASS | Compact-angle tube yields uniform branch conditions; e_param proves holomorphic normalized integral. |
| q4-a | `qsc_avgC_real` (Quartic/ScalingTube.lean:80) | PASS | Compact-angle tube yields uniform branch conditions; e_param proves holomorphic normalized integral. |
| q4-b | `double_integral_swap` (Quartic/Swap.lean:30) | PASS | Continuous compact-square kernel permits integral exchange; separation norm symmetry swaps the planets. |
| q4-b | `quarticPairKernel` (Quartic/Swap.lean:43) | PASS | Literal pair kernel in two actions and two planar slow vectors; a rearrangement, not replacement, of pairSlowSecular. |
| q4-b | `pairSlowSecular_eq_kernel` (Quartic/Swap.lean:48) | PASS | Continuous compact-square kernel permits integral exchange; separation norm symmetry swaps the planets. |
| q4-b | `pairKernel_eq_quarticPairKernel` (Quartic/Swap.lean:52) | PASS | Continuous compact-square kernel permits integral exchange; separation norm symmetry swaps the planets. |
| q4-b | `pairSlowSecular_swap` (Quartic/Swap.lean:59) | PASS | Continuous compact-square kernel permits integral exchange; separation norm symmetry swaps the planets. |
| q4-b | `iteratedDeriv_eq_zero_of_isBigO` (Quartic/Taylor.lean:26) | PASS | Analytic order and nonzero punctured points prove O(s^6) uniqueness through degree five; quartic factor is 24. |
| q4-b | `iteratedDeriv_four_of_expansion` (Quartic/Taylor.lean:83) | PASS | Analytic order and nonzero punctured points prove O(s^6) uniqueness through degree five; quartic factor is 24. |

## Definition classification

All 34 definitions/abbreviations are individually classified in the table. They are mathematical objects, finite coordinate maps/carriers, explicit coefficient extraction, or explicit branch/domain predicates. There is no conclusion-bearing structure introduced. Real square roots, complex powers, inverses, derivatives and Bochner integrals are Lean-total objects; physical/analytic claims are restricted to the positive separated neighbourhoods where those operations have their intended meaning. No theorem uses an invalid-domain fallback to obtain its conclusion. The six test evaluations are of the multilinear jet, which is meaningful for arbitrary test vectors even when those vectors lie outside the original nonlinear function's physical neighbourhood.

## Independent validation receipts

All auditor-controlled Lean/Lake commands ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`. The compile gate was used for the targeted build. No cache update, clean, full-library build, production mutation, or state-changing git command was run.

1. Targeted build (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s84 KAM.Planetary.SecularForm.Quartic
```

Exact gate/result lines:

```text
[inp-gate] slot 1 acquired 16:53:34 for KAM.Planetary.SecularForm.Quartic
Build completed successfully (9175 jobs).
```

The replayed build log contains 48 warnings, including unused signed variables and tactic linter suggestions. A warning's suggestion to disable a linter is not a source-level option override.

2. Fresh signature/definition and axiom probe (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-s84-probe.lean
```

The probe copies the three signed theorem headers under `audit_` names and proves them with exactly their original explicit arguments (`D hn`; `D hij hI hJ u v hu hv hSep`; no arguments for `quartic_scaling`). Five copied signed definitions are equated to production definitions by `rfl`. Thus neither old draft `sorry` bodies nor a locally rewritten statement are used as evidence. Static comparison found all five definition bodies and all three theorem headers text-identical. There were zero probe errors, and the following are the complete 85 `#print axioms` outputs:

```text
'KAM.Planetary.SecularForm.quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairQuartic_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_pairQuartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_quarticCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeSq_smul_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeLength_smul_e1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairQuartic_of_ray' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quarticCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quarticCoeff_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.exists_poly_of_multilinear' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_form_of_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairProj_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action_axes_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.exists_angle' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.orth_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.vec2_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_pairData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.action_axis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.axis_mem_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_secular_nbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.analyticAt_pairSlowSecular' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_ppos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.planeSq_ppos_sub_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.perturbation_false_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.avg_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular_eq_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_pairKernel_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.integrableOn_pairKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairKernel_avg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.secular_false_eq_pairs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedFDeriv_comp_clm_of_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_matW_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_quartic_structure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.poincare_fst_eq_unitPosition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_pair_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.matW_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_rotW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.continuous_reflW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairEmb_rotW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairEmb_reflW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.eventually_pair_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_rot_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pair_refl_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.quartic_scaling' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_diffAt_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_diffAt_KC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_sepK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_intK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_kC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_KC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_contAt_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeSq_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_kC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_qscU_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_qscU_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_sep_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_good_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_intC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qscEmbCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_isOpen_separatedDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_unitPosition' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeSq_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeDot_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_planeLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_qscU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_periodic_qscU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_planeLength_qscU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_sep_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_sep_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_continuous_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_dimensionlessPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.qsc_avgC_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.double_integral_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairKernel_eq_quarticPairKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.pairSlowSecular_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedDeriv_eq_zero_of_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.iteratedDeriv_four_of_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

KERNEL_AND_LINT_PENDING

Static hygiene: all 20 files contain copyright headers, `module`, public imports, module documentation and exposed public noncomputable sections; no file exceeds 1500 lines (maximum 273). Masked-code search found no sorry/admit/axiom/unsafe/opaque, resource overrides or EuclideanSpace. New declarations stay in `KAM.Planetary.SecularForm`. The public short-name check found F1; the other leaf-name match is private. The local KAM import closure has 129 modules, zero providers, zero frozen theorem files, and exactly 56 frozen definition modules, all with manifest state SEALED.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Both commands exit 0 with no diff/check output (the first repeats the multiple-merge-base warning recorded above). No frozen/manifest/generated file is changed.


## Suspected errata, deviations and remaining uncertainties

No new suspected pinned-paper defect was found. Existing E-P-CP11-2 (blueprint p8:238; design:397–399) concerns printed “37 alpha^4 beta_4^(9)” versus alpha power three; this package correctly uses exact radial derivatives and supplies no proof of the corrected printed-polynomial certificate. The old product eccentricity domain is excluded by `separatedDomain`; no transfer to that false larger domain is asserted. No auditor deviation or production edit was introduced. F1 and F2 must be resolved before package acceptance; N1 and N3 must remain visible in landing/completion claims. Prior memory was used only to recall the serial audit workflow and permitted generated-root exception; all package-specific claims above were checked against current files.
