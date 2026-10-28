# Lean design: planetary averaging and the two-scale KAM construction (Parts 2–3)

2026-10-28; branch `inp-design-p23`. Design evidence only: no proofs, frozen declarations, source repairs, or closure claims are landed here. Scope: all 131 graph records whose statement source is `p2-averaging.tex`, `p3a-two-scale-iteration.tex`, or `p3b-two-scale-limit.tex`. The exact signature commands appear in Appendix A. All their proof bodies are `sorry`.

## Revision 2

This revision responds to `DESIGN-P23-design-audit-1.md` (FAIL at design commit `6d3620a`). That audit has one major finding, F1, and three minor notes; no blocking or medium finding is listed. It repairs the design targets, not their proofs, and does not claim a second independent audit has passed.

| Finding | Resolution and verification boundary |
|---|---|
| F1 — inherited oscillator step contract | Appendix A `osc_iter` now has the complete replacement command proposed in audit 1, with unchanged source premises, generator, time-one map, normal-form functions and quantitative remainder. It returns generator class/norm, three-halves-loss holomorphy and maps-to, fast-lattice equivariance, inverse flow on the twice-shrunk domain, normal-form increment class/bound, explicit Hamiltonian identity, gauge displacement and derivative bounds, symplecticity, and the four component displacements on the larger domain. Reality of generator, normal form, remainder and map is a conditional conclusion under inherited realness premises. P23-13 owns every clause; P23-15 obtains periodicity and reality from this same step map, not an isotropic N instantiation or output assumptions. The revised command is signature-checked below; its anisotropic transfer proof remains to be written and audited. |
| N1 — selected N views | `direct` and `direct_step` are explicitly selected views, not the full inherited N contract. Their signature docstrings and the package boundary below require `homological_direct` and `iterative_direct_a`–`iterative_direct_e` on the same generator and flow, with `p_N=2`, `alpha_N=2alpha/q`. In particular P23-12 must call `_a` for the integer-translation law. |
| N2 — private limit interfaces | P23-17–21 remain unimplemented private conditional interfaces, not certified by the 33 public signature commands or 131 node rows. Their release gate below now requires an exact private-signature inventory and independent applicability audit on the same P23-16 witnesses before package release. This note is addressed by making the existing obligation explicit; it does not claim those future interfaces have been supplied or audited. |
| N3 — validation and provenance | The receipt below distinguishes the new gated signature check from the failed full source lint and retains `sorryAx`. No theorem is proved or provider sealed. CP10 errata remain carried blueprint reports, without fresh pinned-PDF verification. The five blueprint gap dispositions and their exact corrected domains/conventions are unchanged. |

### Oscillator and ordinary step package boundaries

Write `O = oscDom D (r-rho) (rp-rhop) (rq-rhoq) (S-sigma)`, `U` for the three-halves-loss domain, and `V` for the twice-loss domain, exactly as in `osc_iter`. P23-13 proves the flow on `O`; holomorphy, maps-to `O`, symplecticity, lattice equivariance, gauge and component displacement assertions hold on `U`; injectivity, inverse flow, derivative bound, transformed identity and remainder hold on `V`. Generator and normal-form class/norm assertions use the original domain. All reality conclusions are guarded by reality of `h`, `g`, and `f` on the original domain. The zero-mode increment is independent of fast angles by its explicit coefficient formula. The stronger smallness implies the canonical-flow smallness; anisotropic Lie-series equality still requires both ratios in the risks section.

P23-15 carries reality of the accumulated `g` and current remainder through each step and composes the returned fast-lattice laws on the actual maps-to domains. P23-13 is not ready for that consumer until every conjunction of the revised `osc_iter` is proved and audited. No separate output-realness or periodicity premise is permitted. P23-05/P23-12 instead retain the complete ordinary N upstream theorems: use `homological_direct` for additional generator projections, `_a` for the exact flow's lattice/maps-to/inverse properties, and `_b`–`_e` for displacement/derivative, normal form, remainder and reality. The wrappers alone are insufficient as the complete proof input.

## Decisions

1. Use `KAM.Weighted` and `KAM.Canonical` directly. `WBound` expresses a finite, summable Fourier norm bound; it is not a sum of parameter suprema. Use the frozen `actionNbhd`, `hamiltonianVectorField`, `hamiltonianVectorFieldℂ`, `Phase`, `symplecticForm`, `fast`, and `slow`. `conv_data` and `block_bridge` give the exact adapters.
2. Keep frozen phase order `(angle,action)` throughout. The source's `(action,angle)` is just a coordinate presentation. Oscillators occupy `((theta,q),(I,p))`; Fourier expansion is only in `theta`. Flatten the parameter `(I,p,q)` once by `oscPack`; evaluate the existing `Weighted.coeff`, `WSummable`, and `wsum` on that parameter. No new Fourier norm or coefficient representation is introduced.
3. Part 2 widths are geometric. Every Part 3 call explicitly uses `geometricWidth σ = σ/(2π)`. The effective small divisor is `2πα`. Pure-angle CP conversion divides the Hamiltonian by `2π`; conversion while Cartesian oscillators remain instead scales fast actions inversely and leaves the Hamiltonian unchanged (`use5`).
4. Reuse the EXACT designed N Part 6 interface, including its `p`, rather than silently renaming it `q`: instantiate `p_N=2`, `alpha_N=2alpha/q`. Then `conjExp 2=2`, `alpha_N/conjExp 2=alpha/q`, and `conjExp 2/alpha_N=q/alpha`. The existing `homGen` does not depend on either parameter. This pays the `q=1` interface obligation without changing any N declaration. The source remains the direct divisor bound on the whole complex neighbourhood; no extra frequency Lipschitz premise is added.
5. Use explicit formula data `ScaleData`, a source-premise predicate `KamHyp`, and existential witnesses. Initial `L=initialL`; subsequent stages use the permitted larger `2^j L`, never recompute a smaller maximum. No `stepChoice`, default stage, arbitrary global inverse, or fallback definition is used. The optional partial signature file was inspected: its renamed upstream APIs and default-valued step selection are not adopted.
6. Keep large-domain `Ψ` as a total map and restrict only the DOMAIN of assertions about `Ψ+`. `step` retains holomorphy, symplecticity and displacement on the large averaging domain, and the new Hamiltonian identity on the smaller stage domain. This is the domain repair requested by the global graph review.
7. Preserve shared witnesses across the iteration, limits, tori and complement estimate. Some graph lemmas are **local named obligations in the joint construction theorem**, not independently exported theorems selecting potentially unrelated witnesses. This fusion is explicit in the node table. Their source statements and proof locators remain obligations; the table does not claim they already have separate Lean proofs. `two_scale_kam` is the full source-premise-only public contract; the internal limit packages pass the same existential witnesses forward. A prover must not introduce a `LimitExists`, `IterationWorks`, or theorem-shaped input structure.
8. No frozen theorem closes here. Part 5 still owns its complex neighbourhood, uniform constants, numerical choices, measure positivity, strict upper bound, reconstruction, and provider assembly for P-G.

## Carriers, source premises and conventions

| Object | Exact representation |
|---|---|
| real / complex vector | `Fin n → ℝ` / `Fin n → ℂ`; existing Pi max norm |
| phase | frozen `KAM.Planetary.Phase n`; `CPhase n` is just an abbrev for the existing product |
| real tube | preimage of frozen `actionNbhd D r` under existing `realInclusion n` |
| neighbourhood / strip | `Weighted.Dom n (realBase D) r s`; `coefficientDom` changes widths only |
| Fourier data | `Weighted.coeff`, `WSummable`, `wsum`, `WBound`, `projMode`, `truncate` |
| block projections | generic coordinate restriction for complex/integer data, proved equal to frozen `fast` / `slow` on real vectors |
| matrix bounds | continuous linear map operator norms; row restrictions explicitly bounded on all vectors; no default entrywise matrix norm |
| inverse Hessian | existence of a continuous linear equivalence with derivative as forward map and the stated inverse/row bounds |
| real dynamics | frozen field on `Hr z = Re(h(I_C)+f(z_C))`; `HasDerivAt` at every real time |
| torus | EXACT upstream `KAM.Planetary.IsLatticeTorus KAM.ODE.angleShift Hr O omega K` |
| two scales | EXACT upstream `KAM.Planetary.twoScaleDiophantine a b gamma1 gamma2 tau` |
| measure | `volume : Measure _`, ENNReal bounds; torus quotient measure is intersection with the half-open unit angle cell |
| rescaling | `limitmap_data R s z = max (norm angle * 2π/s) (norm action/R)`; no global instance |

`DirectHyp`, `AvgHyp`, `OscHyp`, `KamHyp` contain only literal source assumptions and typing/positivity data. They contain no solution, limit, invariant torus, measure bound, or transformed Hamiltonian. Expand every field during statement review. `ScaleData` contains numbers only; all meaningful operations are guarded by `KamHyp` when used in a theorem. Empty `D` is allowed. `E>0` is essential for the Part 3 logarithm; Part 2 allows `E=0`. Numerical `E` is chosen before `K`. Source constants are exactly 128, 4096, 400, 3, 9, 640, 2560, 768 and `max(8192n,24^(tau+1)/3)`, with the coefficient/geometric conversion shown in the signatures.

No measurability of arbitrary `D` or of the torus union is asserted here. Outer measure bounds are meaningful for all sets. Part 5 must supply the measurable set and whole-torus saturation required by the frozen root. The source uniqueness assertion is not reinstated: phase translations give other embeddings. The inverse-frequency estimate is local at distance `<rho/Mbar`, and global only under `Bornology.IsBounded D`.

## Reuse and upstream interfaces (to reconcile)

The shared upstream files are design evidence, not proof imports. The scratch signature contains verbatim definition-body fixtures only for the five needed N objects and two P1 objects. Existing landed `Weighted` definitions are imported, never redeclared. Remove fixtures and add imports when their owners land. Their namespace, argument order and types are preserved. No upstream theorem is replaced by a new assumption.

| Graph input | Exact Lean dependency and applicability |
|---|---|
| N p4 domains/norm | `KAM.Weighted.polyNbhd`, `Dom`, `InClass`, `WBound`, `WBound.mono`, `actionNbhd_eq_polyNbhd` |
| N p4 coefficients | `KAM.Weighted.coeff_differentiableOn`, `coefficients_deriv`, `coefficients_series`, `coefficients_repr`; finite generating polynomials |
| N p4 algebra / projections | `KAM.Weighted.wbound_mul`, `projections`, `truncation_tail`; fixed-parameter sums before parameter supremum |
| N p4 Cauchy / sup | `KAM.Weighted.cauchy_theta`, `cauchy_action`, `sup_le_wbound`; target-width loss as corrected below |
| N p5 setting | `KAM.Canonical.poissonBracket`, `RealOn`, `scaledNorm`, `symplFormC`; existing frozen complex field |
| N p5 flow | `KAM.Canonical.flow_a`, `flow_b`, `flow_c`, `flow_d`, `flow_e`, with `SmallField` and its actual open/gauge domain |
| N p5 canonical / symplectic | `KAM.Canonical.symplectic`, `canonical_field`, `canonical_orbit`; supply holomorphic small-field hypotheses for oscillator flow, not just real smoothness |
| N p5 adjoint / composition | `KAM.Canonical.adjoint_bound`, `composition_domain`, `composition_series`, `composition_t`, `composition_real`, `composition_integral` |
| N p5 transform / canonical map | designed `KAM.Canonical.transform`, `canonical_map_a`–`canonical_map_e`; transfer their PROOFS to oscillator losses using `osc_bracket`, not their isotropic hypotheses verbatim |
| N p5 field estimate | `KAM.Canonical.vf_bound`; coordinatewise fast-action estimate uses `firstGen` |
| N p6 setting / divisor | EXACT `KAM.NormalForm.zBall`, `freq`, `dotC`, `DivisorBound`, `IsDecomp`, `starNorm`, `divisor`; P uses the bound already on the neighbourhood |
| N p6 homological | EXACT `KAM.NormalForm.homGen K Lambda h f`, `homological_direct`; instantiate `p=2`, `alpha_N=2alpha/q` |
| N p6 iteration + special remark | EXACT `KAM.NormalForm.IterHyp`, `iterMap`, `iterG`, `iterF`, `iterative_direct_a`–`iterative_direct_e`; same substitution, `g=0` first step |
| N p6 telescope | EXACT `KAM.NormalForm.telescope`; apply separately to angle / fast action / slow action seminorms |
| N p6 numerics | `Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`, real geometric-series API; prove each numerical inequality in a small lemma, not as a new analytic premise |
| P1 chart / period | EXACT designed `KAM.Planetary.IsChart c Psi O`, `chartPullback c H Psi`, `chart_field`, `angleScale`, `cyl_pipeline`; argument order is the delivered P1 order, not the optional partial file's `Tools.IsChart` |
| P1 two scales | EXACT `KAM.Planetary.twoScaleDiophantine`, `isDiophantine_min_of_mem_twoScale`, `smul_mem_twoScale` |
| K mean value / Cauchy | `Convex.norm_image_sub_le_of_norm_fderiv_le`, `KAM.norm_fderiv_le_of_closedBall_bound`, `KAM.Weighted.general_cauchy`; open radii via limits |
| K Fourier / rectangle | `KAM.torusCoeffW`, `KAM.torusAverage_imag_shift`, `KAM.norm_torusCoeff_le_of_lt`, `KAM.decay`, `KAM.hasSum_torusCoeff_mul_character`; `fourier_compact` supplies the new uniform tail/all-derivative assembly |
| K Banach / McShane | `ContractingWith.exists_fixedPoint`, `KAM.mcshane_components`, `KAM.mcshane_prod`; exact Pi max norm and `0≤lambda<1` |
| K Lebesgue / image | `KAM.lip_image`, `KAM.lip_image_prod`, `appendMeasurableEquiv`, `volume_image_appendMeasurableEquiv`; no unproved measurability premise |
| P3 IFT / Neumann | new `ext_ift`, `ext_neumann`; Mathlib inverse function and inverse-series APIs, with actual CLM derivative equivalences |
| P3 Weierstrass | `KAM.uniform_limits`, `KAM.Weighted.uniform_limit_holomorphic`; open finite-dimensional complex domains |

For P1's real restriction gap the usable input is already `KAM.hamiltonian_real_fderiv` / `hamiltonianVectorField_eq_of_real` from `KAM/Strip/RealRestriction.lean`. `real_symplectic_conjugation` explicitly supplies the new map/field composition bridge. `real_curve_limit` is paid by Mathlib's `hasDerivAt_of_tendsto_locally_uniformly_on'` (open set `univ`), not by the complex Weierstrass statement.

## Every graph node → Lean obligation

The following table is generated from the live graph, not from a list of LaTeX labels. `P2`, `P3a`, `P3b` expand to the three exact blueprint filenames in the scope paragraph. `Lx–Ly` locators are inclusive. `local:name` denotes a named proof obligation within the given declaration, with the full statement at the source locator; it is deliberately not a new hypothesis or an independently selected witness. Definition/data nodes map to their actual carrier definitions. Every graph dependency remains binding; the final column records its node IDs, and the reuse table resolves external IDs to exact Lean names. Local dependencies consume earlier obligations of the same construction.

| Node | Declaration or named local obligation | Statement locator | Proof locator | Required graph inputs |
|---|---|---|---|---|
| `bpP:p2:setting` | `setting` | `P2#bpP:p2:setting@L40-L43` | `-` | `bpP:p2:conv#data` |
| `bpP:p2:direct` | `direct / direct_step` | `P2#bpP:p2:direct@L45-L50` | `P2#bpP:p2:direct@L51-L55` | `stepP:p2:dr-use`, `bpP:p2:setting`, `N:bpN:p6:homological`, `N:bpN:p6:iterative`, `bpN:p6:iterative-special`, `N:bpN:p6:setting`, `bpP:p2:conv#data` |
| `stepP:p2:dr-use` | `direct_step / local:dr_use` | `P2#stepP:p2:dr-use@L52-L54` | `P2#stepP:p2:dr-use@L52-L54` | `N:bpN:p6:homological`, `N:bpN:p6:setting`, `N:bpN:p6:divisor`, `N:bpN:p6:iterative`, `bpP:p2:setting` |
| `bpP:p2:split` | `split` | `P2#bpP:p2:split@L57-L67` | `P2#bpP:p2:split@L68-L74` | `stepP:p2:sp-coef`, `stepP:p2:sp-field`, `stepP:p2:sp-int`, `bpP:p2:direct`, `bpP:p2:conv#data`, `N:bpN:p5:setting` |
| `stepP:p2:sp-coef` | `split / local:sp_coef` | `P2#stepP:p2:sp-coef@L69-L70` | `P2#stepP:p2:sp-coef@L69-L70` | `N:bpN:p6:homological`, `N:bpN:p4:coefficients`, `bpP:p2:direct`, `bpP:p2:conv#data` |
| `stepP:p2:sp-field` | `split / local:sp_field` | `P2#stepP:p2:sp-field@L71-L72` | `P2#stepP:p2:sp-field@L71-L72` | `N:bpN:p5:setting`, `N:bpN:p5:flow`, `N:bpN:p5:canonical-map`, `N:bpN:p5:vf-bound`, `stepP:p2:sp-coef`, `bpP:p2:conv#data` |
| `stepP:p2:sp-int` | `split / local:sp_int` | `P2#stepP:p2:sp-int@L73-L73` | `P2#stepP:p2:sp-int@L73-L73` | `K:bp:p1:ext-mvt`, `stepP:p2:sp-field`, `bpP:p2:conv#data` |
| `bpP:p2:nfb` | `nfb` | `P2#bpP:p2:nfb@L78-L93` | `P2#bpP:p2:nfb@L94-L127` | `stepP:p2:nfb-first`, `stepP:p2:nfb-N`, `stepP:p2:nfb-ind`, `stepP:p2:nfb-concl`, `stepP:p2:nfb-disp`, `bpP:p2:conv#data`, `bpP:p2:setting`, `bpP:p2:direct`, `N:bpN:p6:setting` |
| `stepP:p2:nfb-first` | `nfb / local:nfb_first` | `P2#stepP:p2:nfb-first@L99-L105` | `P2#stepP:p2:nfb-first@L99-L105` | `bpP:p2:direct`, `bpP:p2:split`, `bpP:p2:conv#data` |
| `stepP:p2:nfb-N` | `nfb / local:nfb_N` | `P2#stepP:p2:nfb-N@L107-L111` | `P2#stepP:p2:nfb-N@L107-L111` | `N:bpN:p6:ext-numerics`, `stepP:p2:nfb-first`, `bpP:p2:direct`, `bpP:p2:conv#data`, `bpP:p2:split` |
| `stepP:p2:nfb-ind` | `nfb / local:nfb_ind` | `P2#stepP:p2:nfb-ind@L113-L117` | `P2#stepP:p2:nfb-ind@L113-L117` | `bpP:p2:direct`, `N:bpN:p4:projections`, `N:bpN:p6:setting`, `stepP:p2:nfb-N`, `stepP:p2:nfb-first`, `N:bpN:p6:ext-numerics`, `bpP:p2:conv#data` |
| `stepP:p2:nfb-concl` | `nfb / local:nfb_concl` | `P2#stepP:p2:nfb-concl@L119-L121` | `P2#stepP:p2:nfb-concl@L119-L121` | `N:bpN:p6:telescope`, `N:bpN:p6:iterative`, `N:bpN:p4:sup-weighted`, `stepP:p2:nfb-ind`, `stepP:p2:nfb-N`, `N:bpN:p6:ext-numerics`, `bpP:p2:conv#data`, `stepP:p2:nfb-first` |
| `stepP:p2:nfb-disp` | `nfb / local:nfb_disp` | `P2#stepP:p2:nfb-disp@L123-L126` | `P2#stepP:p2:nfb-disp@L123-L126` | `N:bpN:p6:telescope`, `N:bpN:p6:iterative`, `bpP:p2:split`, `stepP:p2:nfb-ind`, `stepP:p2:nfb-first`, `stepP:p2:nfb-N`, `bpP:p2:conv#data` |
| `bpP:p2:avg` | `avg` | `P2#bpP:p2:avg@L136-L146` | `P2#bpP:p2:avg@L147-L150` | `stepP:p2:av-dict`, `stepP:p2:av-hyp`, `bpP:p2:conv#data` |
| `stepP:p2:av-dict` | `avg / local:av_dict` | `P2#stepP:p2:av-dict@L148-L148` | `P2#stepP:p2:av-dict@L148-L148` | `bpP:p2:conv#data` |
| `stepP:p2:av-hyp` | `avg / local:av_hyp` | `P2#stepP:p2:av-hyp@L149-L149` | `P2#stepP:p2:av-hyp@L149-L149` | `bpP:p2:nfb`, `stepP:p2:av-dict`, `bpP:p2:conv#data` |
| `bpP:p2:osc-bracket` | `osc_bracket / ob_field` | `P2#bpP:p2:osc-bracket@L171-L175` | `P2#bpP:p2:osc-bracket@L176-L181` | `stepP:p2:ob-der`, `stepP:p2:ob-prod`, `stepP:p2:ob-field`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:ob-der` | `ob_der` | `P2#stepP:p2:ob-der@L177-L177` | `P2#stepP:p2:ob-der@L177-L177` | `N:bpN:p4:cauchy`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:ob-prod` | `osc_bracket / local:ob_prod` | `P2#stepP:p2:ob-prod@L178-L179` | `P2#stepP:p2:ob-prod@L178-L179` | `N:bpN:p4:algebra`, `stepP:p2:ob-der`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:ob-field` | `ob_field` | `P2#stepP:p2:ob-field@L180-L180` | `P2#stepP:p2:ob-field@L180-L180` | `bpP:p2:s-osc#data`, `N:bpN:p4:cauchy`, `N:bpN:p4:sup-weighted`, `bpP:p2:conv#data` |
| `bpP:p2:osc-iter` | `osc_iter` | `P2#bpP:p2:osc-iter@L183-L189` | `P2#bpP:p2:osc-iter@L190-L195` | `stepP:p2:oi-transfer`, `stepP:p2:oi-ratio`, `stepP:p2:oi-range`, `stepP:p2:oi-disp`, `bpP:p2:direct`, `N:bpN:p6:iterative`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:oi-transfer` | `osc_iter / local:oi_transfer` | `P2#stepP:p2:oi-transfer@L191-L191` | `P2#stepP:p2:oi-transfer@L191-L191` | `bpP:p2:osc-bracket`, `N:bpN:p6:homological`, `N:bpN:p5:flow`, `N:bpN:p5:symplectic`, `N:bpN:p5:canonical`, `N:bpN:p5:adjoint`, `N:bpN:p5:composition`, `N:bpN:p5:transform`, `N:bpN:p5:canonical-map`, `bpP:p2:s-osc#data`, `bpP:p2:direct`, `bpP:p2:conv#data` |
| `stepP:p2:oi-ratio` | `osc_iter / local:oi_ratio` | `P2#stepP:p2:oi-ratio@L192-L192` | `P2#stepP:p2:oi-ratio@L192-L192` | `N:bpN:p5:transform`, `N:bpN:p5:composition-integral`, `bpP:p2:osc-bracket`, `stepP:p2:oi-transfer`, `N:bpN:p5:adjoint`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `stepP:p2:oi-range` | `osc_iter / local:oi_range` | `P2#stepP:p2:oi-range@L193-L193` | `P2#stepP:p2:oi-range@L193-L193` | `N:bpN:p5:composition`, `N:bpN:p6:iterative`, `stepP:p2:oi-ratio`, `stepP:p2:oi-transfer`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `stepP:p2:oi-disp` | `osc_iter / local:oi_disp` | `P2#stepP:p2:oi-disp@L194-L194` | `P2#stepP:p2:oi-disp@L194-L194` | `bpP:p2:osc-bracket`, `stepP:p2:sp-field`, `stepP:p2:oi-transfer`, `stepP:p2:oi-range`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `bpP:p2:osc-averaging` | `osc_averaging` | `P2#bpP:p2:osc-averaging@L198-L210` | `P2#bpP:p2:osc-averaging@L211-L220` | `stepP:p2:oa-first`, `stepP:p2:oa-iter`, `stepP:p2:oa-concl`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:oa-first` | `osc_averaging / local:oa_first` | `P2#stepP:p2:oa-first@L213-L215` | `P2#stepP:p2:oa-first@L213-L215` | `bpP:p2:osc-iter`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:oa-iter` | `osc_averaging / local:oa_iter` | `P2#stepP:p2:oa-iter@L216-L218` | `P2#stepP:p2:oa-iter@L216-L218` | `stepP:p2:nfb-N`, `bpP:p2:osc-iter`, `stepP:p2:oa-first`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `stepP:p2:oa-concl` | `osc_averaging / local:oa_concl` | `P2#stepP:p2:oa-concl@L219-L219` | `P2#stepP:p2:oa-concl@L219-L219` | `stepP:p2:nfb-concl`, `bpP:p2:osc-iter`, `N:bpN:p6:telescope`, `stepP:p2:oa-iter`, `stepP:p2:oa-first`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `bpP:p2:averaged-remainder` | `averaged_remainder` | `P2#bpP:p2:averaged-remainder@L222-L234` | `P2#bpP:p2:averaged-remainder@L235-L238` | `stepP:p2:ar-apply`, `stepP:p2:ar-collect`, `bpP:p2:osc-averaging`, `bpP:p2:s-osc#data`, `bpP:p2:conv#data` |
| `stepP:p2:ar-apply` | `averaged_remainder / local:ar_apply` | `P2#stepP:p2:ar-apply@L236-L236` | `P2#stepP:p2:ar-apply@L236-L236` | `bpP:p2:osc-averaging`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `stepP:p2:ar-collect` | `averaged_remainder / local:ar_collect` | `P2#stepP:p2:ar-collect@L237-L237` | `P2#stepP:p2:ar-collect@L237-L237` | `bpP:p2:osc-averaging`, `stepP:p2:ar-apply`, `bpP:p2:conv#data`, `bpP:p2:s-osc#data` |
| `bpP:p2:use5` | `use5` | `P2#bpP:p2:use5@L240-L246` | `P2#bpP:p2:use5@L240-L246` | `bpP:p2:averaged-remainder`, `bpP:p2:conv#data`, `bpP:p1:chart` |
| `bpP:p2:conv#data` | `conv_data / geometricWidth / realBase` | `P2#bpP:p2:conv#data@L24-L36` | `-` | `N:bpN:p4:norm`, `N:bpN:p4:domains`, `N:bpN:p6:ext-numerics` |
| `bpP:p2:s-osc#data` | `oscPack / oscDom / oscBound / oscGauge` | `P2#bpP:p2:s-osc#data@L167-L169` | `-` | `bpP:p2:conv#data`, `N:bpN:p4:norm` |
| `bpP:p3:constants` | `constants` | `P3a#bpP:p3:constants@L42-L55` | `-` | `-` |
| `bpP:p3:two-scale-kam` | `two_scale_kam` | `P3a#bpP:p3:two-scale-kam@L59-L87` | `P3b#bpP:p3:two-scale-kam@L193-L204` | `stepP:p3:pf-constr`, `stepP:p3:pf-ad`, `stepP:p3:pf-bc`, `stepP:p3:pf-inj`, `stepP:p3:pf-meas`, `bpP:p3:constants`, `bpP:p3:conv#data`, `bpP:p3:limitmap#data` |
| `bpP:p3:rem-norm` | `rem_norm` | `P3a#bpP:p3:rem-norm@L89-L93` | `P3a#bpP:p3:rem-norm@L89-L93` | `bpP:p3:conv#data`, `bpP:p3:constants` |
| `bpP:p3:period-dictionary` | `period_dictionary / period_dictionary_field` | `P3a#bpP:p3:period-dictionary@L95-L100` | `P3a#bpP:p3:period-dictionary@L101-L109` | `stepP:p3:pd-subst`, `stepP:p3:pd-invar`, `stepP:p3:pd-dyn`, `bpP:p1:period-convert`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:pd-subst` | `period_dictionary / local:pd_subst` | `P3a#stepP:p3:pd-subst@L102-L103` | `P3a#stepP:p3:pd-subst@L102-L103` | `bpP:p3:conv#data` |
| `stepP:p3:pd-invar` | `period_dictionary / local:pd_invar` | `P3a#stepP:p3:pd-invar@L104-L106` | `P3a#stepP:p3:pd-invar@L104-L106` | `bpP:p3:constants`, `stepP:p3:pd-subst` |
| `stepP:p3:pd-dyn` | `period_dictionary / local:pd_dyn` | `P3a#stepP:p3:pd-dyn@L107-L108` | `P3a#stepP:p3:pd-dyn@L107-L108` | `bpP:p1:period-convert`, `bpP:p3:conv#data` |
| `bpP:p3:ext-ift` | `ext_ift` | `P3a#bpP:p3:ext-ift@L114-L114` | `-` | `-` |
| `bpP:p3:ext-neumann` | `ext_neumann` | `P3a#bpP:p3:ext-neumann@L118-L118` | `-` | `-` |
| `bpP:p3:ball` | `ball` | `P3a#bpP:p3:ball@L124-L126` | `P3a#bpP:p3:ball@L127-L136` | `stepP:p3:ball-inv`, `stepP:p3:ball-lift`, `stepP:p3:ball-closed`, `stepP:p3:ball-lip` |
| `stepP:p3:ball-inv` | `ball / local:ball_inv` | `P3a#stepP:p3:ball-inv@L128-L129` | `P3a#stepP:p3:ball-inv@L128-L129` | `bpP:p3:ext-ift` |
| `stepP:p3:ball-lift` | `ball / local:ball_lift` | `P3a#stepP:p3:ball-lift@L130-L131` | `P3a#stepP:p3:ball-lift@L130-L131` | `K:bp:p1:ext-mvt`, `stepP:p3:ball-inv` |
| `stepP:p3:ball-closed` | `ball / local:ball_closed` | `P3a#stepP:p3:ball-closed@L132-L133` | `P3a#stepP:p3:ball-closed@L132-L133` | `stepP:p3:ball-lift` |
| `stepP:p3:ball-lip` | `ball / local:ball_lip` | `P3a#stepP:p3:ball-lip@L134-L135` | `P3a#stepP:p3:ball-lip@L134-L135` | `stepP:p3:ball-closed`, `stepP:p3:ball-inv`, `K:bp:p1:ext-mvt` |
| `bpP:p3:lip-sup` | `lip_sup` | `P3a#bpP:p3:lip-sup@L138-L140` | `P3a#bpP:p3:lip-sup@L141-L146` | `stepP:p3:ls-close`, `stepP:p3:ls-far` |
| `stepP:p3:ls-close` | `lip_sup / local:ls_close` | `P3a#stepP:p3:ls-close@L142-L143` | `P3a#stepP:p3:ls-close@L142-L143` | `K:bp:p1:cauchy-open`, `K:bp:p1:ext-mvt` |
| `stepP:p3:ls-far` | `lip_sup / local:ls_far` | `P3a#stepP:p3:ls-far@L144-L145` | `P3a#stepP:p3:ls-far@L144-L145` | `-` |
| `bpP:p3:avg` | `avg` | `P3a#bpP:p3:avg@L150-L163` | `P3a#bpP:p3:avg@L164-L166` | `bpP:p2:avg`, `bpP:p3:conv#data`, `bpP:p2:nfb` |
| `bpP:p3:step` | `step` | `P3a#bpP:p3:step@L170-L190` | `P3a#bpP:p3:step@L192-L226` | `stepP:p3:st-nonres`, `stepP:p3:st-small`, `stepP:p3:st-avg`, `stepP:p3:st-disp`, `stepP:p3:st-dg`, `stepP:p3:st-U`, `stepP:p3:st-inj`, `stepP:p3:st-ihat`, `stepP:p3:st-const`, `stepP:p3:st-quad`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:st-nonres` | `step / local:st_nonres` | `P3a#stepP:p3:st-nonres@L193-L197` | `P3a#stepP:p3:st-nonres@L193-L197` | `K:bp:p1:ext-mvt`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:st-small` | `step / local:st_small` | `P3a#stepP:p3:st-small@L198-L199` | `P3a#stepP:p3:st-small@L198-L199` | `bpP:p3:constants`, `stepP:p3:st-nonres`, `bpP:p3:conv#data` |
| `stepP:p3:st-avg` | `step / local:st_avg` | `P3a#stepP:p3:st-avg@L200-L202` | `P3a#stepP:p3:st-avg@L200-L202` | `bpP:p3:avg`, `stepP:p3:st-small`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:st-disp` | `step / local:st_disp` | `P3a#stepP:p3:st-disp@L203-L205` | `P3a#stepP:p3:st-disp@L203-L205` | `bpP:p3:avg`, `stepP:p3:st-nonres`, `bpP:p3:constants`, `bpP:p3:conv#data`, `stepP:p3:st-avg` |
| `stepP:p3:st-dg` | `step / local:st_dg` | `P3a#stepP:p3:st-dg@L206-L209` | `P3a#stepP:p3:st-dg@L206-L209` | `K:bp:p1:cauchy-open`, `stepP:p3:st-avg`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:st-U` | `step / local:st_U` | `P3a#stepP:p3:st-U@L210-L212` | `P3a#stepP:p3:st-U@L210-L212` | `stepP:p3:st-dg`, `bpP:p3:ext-neumann`, `bpP:p3:conv#data`, `bpP:p3:constants`, `stepP:p3:st-avg` |
| `stepP:p3:st-inj` | `step / local:st_inj` | `P3a#stepP:p3:st-inj@L213-L215` | `P3a#stepP:p3:st-inj@L213-L215` | `bpP:p3:ball`, `stepP:p3:st-dg`, `stepP:p3:st-U`, `bpP:p3:ext-ift`, `K:bp:p1:ext-mvt`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:st-ihat` | `step / local:st_ihat` | `P3a#stepP:p3:st-ihat@L216-L219` | `P3a#stepP:p3:st-ihat@L216-L219` | `bpP:p3:ball`, `bpP:p3:lip-sup`, `stepP:p3:st-inj`, `stepP:p3:st-dg`, `stepP:p3:st-U`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:st-const` | `step / local:st_const` | `P3a#stepP:p3:st-const@L220-L223` | `P3a#stepP:p3:st-const@L220-L223` | `bpP:p3:constants` |
| `stepP:p3:st-quad` | `step / local:st_quad` | `P3a#stepP:p3:st-quad@L224-L225` | `P3a#stepP:p3:st-quad@L224-L225` | `stepP:p3:st-const`, `bpP:p3:constants` |
| `bpP:p3:seq` | `seq` | `P3a#bpP:p3:seq@L236-L240` | `-` | `bpP:p3:constants`, `bpP:p3:conv#data` |
| `bpP:p3:iterative` | `iterative` | `P3a#bpP:p3:iterative@L242-L253` | `P3a#bpP:p3:iterative@L254-L265` | `stepP:p3:it-ind`, `stepP:p3:it-base`, `stepP:p3:it-step`, `stepP:p3:it-comp`, `stepP:p3:it-rates`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3:constants` |
| `stepP:p3:it-ind` | `iterative / local:it_ind` | `P3a#stepP:p3:it-ind@L255-L256` | `P3a#stepP:p3:it-ind@L255-L256` | `bpP:p3:seq`, `bpP:p3:constants`, `bpP:p3:conv#data` |
| `stepP:p3:it-base` | `iterative / local:it_base` | `P3a#stepP:p3:it-base@L257-L258` | `P3a#stepP:p3:it-base@L257-L258` | `bpP:p3:seq`, `stepP:p3:it-ind`, `bpP:p3:conv#data` |
| `stepP:p3:it-step` | `iterative / local:it_step` | `P3a#stepP:p3:it-step@L259-L260` | `P3a#stepP:p3:it-step@L259-L260` | `bpP:p3:step`, `bpP:p3:seq`, `stepP:p3:it-ind`, `bpP:p3:conv#data` |
| `stepP:p3:it-comp` | `iterative / local:it_comp` | `P3a#stepP:p3:it-comp@L261-L262` | `P3a#stepP:p3:it-comp@L261-L262` | `stepP:p3:it-step`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:it-rates` | `iterative / local:it_rates` | `P3a#stepP:p3:it-rates@L263-L264` | `P3a#stepP:p3:it-rates@L263-L264` | `bpP:p3:step`, `stepP:p3:it-step`, `bpP:p3:constants`, `bpP:p3:seq` |
| `bpP:p3:sums` | `sums` | `P3b#bpP:p3:sums@L6-L8` | `P3b#bpP:p3:sums@L9-L16` | `stepP:p3:sum-doubling`, `stepP:p3:sum-weighted`, `stepP:p3:sum-radii`, `bpP:p3b#kam-bounds`, `bpP:p3:constants`, `bpP:p3:seq` |
| `stepP:p3:sum-doubling` | `sums / local:sum_doubling` | `P3b#stepP:p3:sum-doubling@L10-L11` | `P3b#stepP:p3:sum-doubling@L10-L11` | `bpP:p3:iterative`, `bpP:p3:constants`, `bpP:p3:seq` |
| `stepP:p3:sum-weighted` | `sums / local:sum_weighted` | `P3b#stepP:p3:sum-weighted@L12-L13` | `P3b#stepP:p3:sum-weighted@L12-L13` | `stepP:p3:sum-doubling`, `bpP:p3b#kam-bounds`, `bpP:p3:constants`, `bpP:p3:seq` |
| `stepP:p3:sum-radii` | `sums / local:sum_radii` | `P3b#stepP:p3:sum-radii@L14-L15` | `P3b#stepP:p3:sum-radii@L14-L15` | `bpP:p3:constants`, `bpP:p3:seq` |
| `bpP:p3:limit-actions` | `two_scale_kam / local:limit_actions` | `P3b#bpP:p3:limit-actions@L20-L29` | `P3b#bpP:p3:limit-actions@L30-L39` | `stepP:p3:la-wp`, `stepP:p3:la-tele`, `stepP:p3:la-loc`, `stepP:p3:la-lip`, `bpP:p3:iterative`, `bpP:p3:seq`, `bpP:p3:constants`, `bpP:p3:conv#data`, `bpP:p3b#kam-bounds` |
| `stepP:p3:la-wp` | `two_scale_kam / local:la_wp` | `P3b#stepP:p3:la-wp@L31-L32` | `P3b#stepP:p3:la-wp@L31-L32` | `bpP:p3:iterative`, `bpP:p3:seq` |
| `stepP:p3:la-tele` | `two_scale_kam / local:la_tele` | `P3b#stepP:p3:la-tele@L33-L34` | `P3b#stepP:p3:la-tele@L33-L34` | `bpP:p3:iterative`, `bpP:p3:sums`, `stepP:p3:la-wp`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:la-loc` | `two_scale_kam / local:la_loc` | `P3b#stepP:p3:la-loc@L35-L36` | `P3b#stepP:p3:la-loc@L35-L36` | `stepP:p3:la-tele`, `bpP:p3:sums`, `bpP:p3b#kam-bounds`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:la-lip` | `two_scale_kam / local:la_lip` | `P3b#stepP:p3:la-lip@L37-L38` | `P3b#stepP:p3:la-lip@L37-L38` | `bpP:p3:iterative`, `bpP:p3:sums`, `bpP:p3b#kam-bounds`, `bpP:p3:constants`, `bpP:p3:seq` |
| `bpP:p3:psi-lip` | `two_scale_kam / local:psi_lip` | `P3b#bpP:p3:psi-lip@L45-L51` | `P3b#bpP:p3:psi-lip@L52-L62` | `stepP:p3:pl-dom`, `stepP:p3:pl-disp`, `stepP:p3:pl-lip`, `stepP:p3:pl-sum`, `bpP:p3:limitmap#data`, `bpP:p3:iterative`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3b#kam-bounds` |
| `stepP:p3:pl-dom` | `two_scale_kam / local:pl_dom` | `P3b#stepP:p3:pl-dom@L53-L54` | `P3b#stepP:p3:pl-dom@L53-L54` | `bpP:p3:iterative`, `bpP:p3:limitmap#data`, `bpP:p3:sums`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3b#kam-bounds` |
| `stepP:p3:pl-disp` | `two_scale_kam / local:pl_disp` | `P3b#stepP:p3:pl-disp@L55-L56` | `P3b#stepP:p3:pl-disp@L55-L56` | `bpP:p3:iterative`, `bpP:p3:sums`, `bpP:p3:limitmap#data`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:pl-lip` | `two_scale_kam / local:pl_lip` | `P3b#stepP:p3:pl-lip@L57-L59` | `P3b#stepP:p3:pl-lip@L57-L59` | `bpP:p3:lip-sup`, `bpP:p3:iterative`, `stepP:p3:pl-disp`, `bpP:p3:limitmap#data`, `bpP:p3b#kam-bounds`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:pl-sum` | `two_scale_kam / local:pl_sum` | `P3b#stepP:p3:pl-sum@L60-L61` | `P3b#stepP:p3:pl-sum@L60-L61` | `bpP:p3:sums`, `bpP:p3b#kam-bounds`, `stepP:p3:pl-lip`, `bpP:p3:constants`, `bpP:p3:seq` |
| `bpP:p3:fourier-compact` | `fourier_compact` | `P3b#bpP:p3:fourier-compact@L64-L66` | `P3b#bpP:p3:fourier-compact@L67-L75` | `stepP:p3:fc-decay`, `stepP:p3:fc-coef`, `stepP:p3:fc-tail` |
| `stepP:p3:fc-decay` | `fourier_compact / local:fc_decay` | `P3b#stepP:p3:fc-decay@L68-L69` | `P3b#stepP:p3:fc-decay@L68-L69` | `K:bp:p1:ext-rectangle` |
| `stepP:p3:fc-coef` | `fourier_compact / local:fc_coef` | `P3b#stepP:p3:fc-coef@L70-L71` | `P3b#stepP:p3:fc-coef@L70-L71` | `stepP:p3:fc-decay` |
| `stepP:p3:fc-tail` | `fourier_compact / local:fc_tail` | `P3b#stepP:p3:fc-tail@L72-L74` | `P3b#stepP:p3:fc-tail@L72-L74` | `stepP:p3:fc-decay`, `stepP:p3:fc-coef`, `bpP:p3:ext-weierstrass`, `K:bp:p1:ext-fourier` |
| `bpP:p3:limit-phi` | `two_scale_kam / local:limit_phi` | `P3b#bpP:p3:limit-phi@L77-L85` | `P3b#bpP:p3:limit-phi@L86-L95` | `stepP:p3:lp-tele`, `stepP:p3:lp-cauchy`, `stepP:p3:lp-per`, `stepP:p3:lp-an`, `bpP:p3:iterative`, `bpP:p3:limit-actions`, `bpP:p3:limitmap#data`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3b#kam-bounds` |
| `stepP:p3:lp-tele` | `two_scale_kam / local:lp_tele` | `P3b#stepP:p3:lp-tele@L87-L88` | `P3b#stepP:p3:lp-tele@L87-L88` | `bpP:p3:limit-actions`, `bpP:p3:iterative`, `bpP:p3:sums`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:lp-cauchy` | `two_scale_kam / local:lp_cauchy` | `P3b#stepP:p3:lp-cauchy@L89-L90` | `P3b#stepP:p3:lp-cauchy@L89-L90` | `bpP:p3:psi-lip`, `stepP:p3:la-lip`, `bpP:p3:limit-actions`, `bpP:p3:limitmap#data`, `bpP:p3:constants`, `bpP:p3:seq` |
| `stepP:p3:lp-per` | `two_scale_kam / local:lp_per` | `P3b#stepP:p3:lp-per@L91-L92` | `P3b#stepP:p3:lp-per@L91-L92` | `bpP:p3:iterative`, `stepP:p3:lp-cauchy`, `bpP:p3:conv#data`, `bpP:p3:limitmap#data` |
| `stepP:p3:lp-an` | `two_scale_kam / local:lp_an` | `P3b#stepP:p3:lp-an@L93-L94` | `P3b#stepP:p3:lp-an@L93-L94` | `bpP:p3:fourier-compact`, `stepP:p3:lp-tele`, `stepP:p3:lp-cauchy`, `bpP:p3:iterative`, `bpP:p3:limit-actions`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `bpP:p3:estimates` | `two_scale_kam / local:estimates` | `P3b#bpP:p3:estimates@L102-L106` | `P3b#bpP:p3:estimates@L107-L112` | `stepP:p3:es-sup`, `stepP:p3:es-loc`, `bpP:p3:tori#data`, `bpP:p3:limit-phi`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:es-sup` | `two_scale_kam / local:es_sup` | `P3b#stepP:p3:es-sup@L108-L109` | `P3b#stepP:p3:es-sup@L108-L109` | `bpP:p3:limit-phi`, `bpP:p3:limit-actions`, `bpP:p3:tori#data`, `bpP:p3:constants`, `bpP:p3:seq` |
| `stepP:p3:es-loc` | `two_scale_kam / local:es_loc` | `P3b#stepP:p3:es-loc@L110-L111` | `P3b#stepP:p3:es-loc@L110-L111` | `bpP:p3:limit-actions`, `bpP:p3:limit-phi`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3:tori#data` |
| `bpP:p3:lagr` | `two_scale_kam / local:lagr` | `P3b#bpP:p3:lagr@L114-L116` | `P3b#bpP:p3:lagr@L117-L124` | `stepP:p3:lg-cauchy`, `stepP:p3:lg-j`, `stepP:p3:lg-lim`, `bpP:p3:tori#data`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3b#kam-bounds` |
| `stepP:p3:lg-cauchy` | `two_scale_kam / local:lg_cauchy` | `P3b#stepP:p3:lg-cauchy@L118-L119` | `P3b#stepP:p3:lg-cauchy@L118-L119` | `bpP:p3:estimates`, `K:bp:p1:cauchy-open`, `bpP:p3:limit-phi`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3:tori#data` |
| `stepP:p3:lg-j` | `two_scale_kam / local:lg_j` | `P3b#stepP:p3:lg-j@L120-L121` | `P3b#stepP:p3:lg-j@L120-L121` | `bpP:p3:iterative`, `bpP:p3:conv#data`, `bpP:p3:tori#data`, `bpP:p3:limit-actions` |
| `stepP:p3:lg-lim` | `two_scale_kam / local:lg_lim` | `P3b#stepP:p3:lg-lim@L122-L123` | `P3b#stepP:p3:lg-lim@L122-L123` | `bpP:p3:limit-phi`, `stepP:p3:lp-an`, `bpP:p3:fourier-compact`, `stepP:p3:lg-j`, `bpP:p3:conv#data`, `bpP:p3:tori#data` |
| `bpP:p3:invariance` | `two_scale_kam / local:invariance` | `P3b#bpP:p3:invariance@L126-L129` | `P3b#bpP:p3:invariance@L130-L144` | `stepP:p3:inv-conj`, `stepP:p3:inv-dphi`, `stepP:p3:inv-err`, `stepP:p3:inv-lim`, `bpP:p3:tori#data`, `bpP:p3:conv#data` |
| `stepP:p3:inv-conj` | `real_symplectic_conjugation` | `P3b#stepP:p3:inv-conj@L132-L134` | `P3b#stepP:p3:inv-conj@L132-L134` | `bpP:p3:iterative`, `bpP:p3:conv#data`, `bpP:p3:tori#data`, `bpP:p3:limit-actions` |
| `stepP:p3:inv-dphi` | `two_scale_kam / local:inv_dphi` | `P3b#stepP:p3:inv-dphi@L135-L136` | `P3b#stepP:p3:inv-dphi@L135-L136` | `stepP:p3:lp-cauchy`, `bpP:p3:limitmap#data`, `bpP:p3:limit-phi`, `bpP:p3:constants`, `bpP:p3:seq` |
| `stepP:p3:inv-err` | `two_scale_kam / local:inv_err` | `P3b#stepP:p3:inv-err@L137-L141` | `P3b#stepP:p3:inv-err@L137-L141` | `bpP:p3:limit-actions`, `K:bp:p1:cauchy-open`, `bpP:p3:iterative`, `bpP:p3:seq`, `bpP:p3:constants`, `bpP:p3:conv#data`, `bpP:p3:tori#data`, `stepP:p3:inv-conj`, `stepP:p3:inv-dphi`, `K:bp:p1:ext-mvt` |
| `stepP:p3:inv-lim` | `real_curve_limit` | `P3b#stepP:p3:inv-lim@L142-L143` | `P3b#stepP:p3:inv-lim@L142-L143` | `bpP:p3:limit-phi`, `stepP:p3:inv-err`, `K:bp:p1:cauchy-open`, `bpP:p3:limitmap#data`, `bpP:p3b#kam-bounds`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3:tori#data`, `K:bp:p1:ext-mvt`, `bpP:p3:estimates` |
| `bpP:p3:cover` | `cover` | `P3b#bpP:p3:cover@L150-L152` | `P3b#bpP:p3:cover@L153-L160` | `stepP:p3:cv-ext`, `stepP:p3:cv-bij`, `stepP:p3:cv-loc` |
| `stepP:p3:cv-ext` | `cover / local:cv_ext` | `P3b#stepP:p3:cv-ext@L154-L155` | `P3b#stepP:p3:cv-ext@L154-L155` | `K:bp:p1:mcshane` |
| `stepP:p3:cv-bij` | `cover / local:cv_bij` | `P3b#stepP:p3:cv-bij@L156-L157` | `P3b#stepP:p3:cv-bij@L156-L157` | `K:bp:p1:ext-banach`, `stepP:p3:cv-ext` |
| `stepP:p3:cv-loc` | `cover / local:cv_loc` | `P3b#stepP:p3:cv-loc@L158-L159` | `P3b#stepP:p3:cv-loc@L158-L159` | `stepP:p3:cv-bij`, `stepP:p3:cv-ext` |
| `bpP:p3:meas-actions` | `two_scale_kam / local:meas_actions` | `P3b#bpP:p3:meas-actions@L162-L164` | `P3b#bpP:p3:meas-actions@L165-L170` | `stepP:p3:ma-ext`, `stepP:p3:ma-meas`, `bpP:p3:measure#data` |
| `stepP:p3:ma-ext` | `two_scale_kam / local:ma_ext` | `P3b#stepP:p3:ma-ext@L166-L167` | `P3b#stepP:p3:ma-ext@L166-L167` | `bpP:p3:cover`, `bpP:p3:limit-actions`, `bpP:p3:measure#data`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `stepP:p3:ma-meas` | `two_scale_kam / local:ma_meas` | `P3b#stepP:p3:ma-meas@L168-L169` | `P3b#stepP:p3:ma-meas@L168-L169` | `K:bp:p1:lip-image`, `stepP:p3:ma-ext`, `bpP:p3:measure#data`, `bpP:p3:conv#data`, `K:bp:p1:ext-lebesgue` |
| `bpP:p3:meas-torus` | `two_scale_kam / local:meas_torus` | `P3b#bpP:p3:meas-torus@L172-L174` | `P3b#bpP:p3:meas-torus@L175-L189` | `stepP:p3:mt-split`, `stepP:p3:mt-ext`, `stepP:p3:mt-pre`, `stepP:p3:mt-meas`, `stepP:p3:mt-shell`, `stepP:p3:mt-sum`, `bpP:p3:measure#data` |
| `stepP:p3:mt-split` | `two_scale_kam / local:mt_split` | `P3b#stepP:p3:mt-split@L177-L178` | `P3b#stepP:p3:mt-split@L177-L178` | `bpP:p3:meas-actions`, `bpP:p3:measure#data`, `K:bp:p1:ext-lebesgue` |
| `stepP:p3:mt-ext` | `two_scale_kam / local:mt_ext` | `P3b#stepP:p3:mt-ext@L179-L180` | `P3b#stepP:p3:mt-ext@L179-L180` | `bpP:p3:limit-phi`, `bpP:p3:cover`, `bpP:p3:limitmap#data`, `bpP:p3:measure#data`, `bpP:p3:constants`, `bpP:p3:seq`, `K:bp:p1:ext-lebesgue` |
| `stepP:p3:mt-pre` | `two_scale_kam / local:mt_pre` | `P3b#stepP:p3:mt-pre@L181-L182` | `P3b#stepP:p3:mt-pre@L181-L182` | `stepP:p3:mt-ext`, `bpP:p3:measure#data`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `bpP:p3:limitmap#data` |
| `stepP:p3:mt-meas` | `two_scale_kam / local:mt_meas` | `P3b#stepP:p3:mt-meas@L183-L184` | `P3b#stepP:p3:mt-meas@L183-L184` | `K:bp:p1:lip-image`, `stepP:p3:mt-pre`, `stepP:p3:mt-ext`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3b#kam-bounds`, `bpP:p3:limitmap#data`, `bpP:p3:measure#data`, `K:bp:p1:ext-lebesgue` |
| `stepP:p3:mt-shell` | `two_scale_kam / local:mt_shell` | `P3b#stepP:p3:mt-shell@L185-L186` | `P3b#stepP:p3:mt-shell@L185-L186` | `bpP:p3:meas-actions`, `bpP:p3:limit-actions`, `stepP:p3:mt-pre`, `bpP:p3:measure#data`, `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:conv#data`, `K:bp:p1:ext-lebesgue` |
| `stepP:p3:mt-sum` | `two_scale_kam / local:mt_sum` | `P3b#stepP:p3:mt-sum@L187-L188` | `P3b#stepP:p3:mt-sum@L187-L188` | `stepP:p3:mt-split`, `stepP:p3:mt-meas`, `stepP:p3:mt-shell`, `bpP:p3:measure#data` |
| `stepP:p3:pf-constr` | `two_scale_kam / local:pf_constr` | `P3b#stepP:p3:pf-constr@L194-L195` | `P3b#stepP:p3:pf-constr@L194-L195` | `bpP:p3:iterative`, `bpP:p3:limit-actions`, `bpP:p3:limit-phi`, `bpP:p3:tori#data`, `bpP:p3:seq` |
| `stepP:p3:pf-ad` | `two_scale_kam / local:pf_ad` | `P3b#stepP:p3:pf-ad@L196-L197` | `P3b#stepP:p3:pf-ad@L196-L197` | `bpP:p3:limit-phi`, `bpP:p3:estimates`, `bpP:p3:tori#data` |
| `stepP:p3:pf-bc` | `two_scale_kam / local:pf_bc` | `P3b#stepP:p3:pf-bc@L198-L199` | `P3b#stepP:p3:pf-bc@L198-L199` | `bpP:p3:invariance`, `bpP:p3:lagr`, `bpP:p3:tori#data` |
| `stepP:p3:pf-inj` | `two_scale_kam / local:pf_inj` | `P3b#stepP:p3:pf-inj@L200-L201` | `P3b#stepP:p3:pf-inj@L200-L201` | `bpP:p3:limit-phi`, `bpP:p3:limit-actions`, `bpP:p3:ball`, `bpP:p3:tori#data`, `bpP:p3:constants`, `bpP:p3:conv#data`, `bpP:p3:limitmap#data` |
| `stepP:p3:pf-meas` | `two_scale_kam / local:pf_meas` | `P3b#stepP:p3:pf-meas@L202-L203` | `P3b#stepP:p3:pf-meas@L202-L203` | `bpP:p3:estimates`, `bpP:p3:meas-torus`, `bpP:p3:measure#data`, `bpP:p3:conv#data`, `K:bp:p1:ext-lebesgue` |
| `bpP:p3:conv#data` | `KamHyp / coefficientDom / twoScaleDiophantine` | `P3a#bpP:p3:conv#data@L11-L34` | `-` | `N:bpN:p4:norm`, `N:bpN:p4:sup-weighted`, `bpP:p1:two-scale` |
| `bpP:p3b#kam-bounds` | `KamHyp.small / kamConstant` | `P3b#bpP:p3b#kam-bounds@L3-L4` | `P3b#bpP:p3b#kam-bounds@L3-L4` | `bpP:p3:constants`, `bpP:p3:seq` |
| `bpP:p3:limitmap#data` | `limitmap_data` | `P3b#bpP:p3:limitmap#data@L43-L43` | `-` | `bpP:p3:constants`, `bpP:p3:seq`, `bpP:p3:iterative`, `bpP:p3:conv#data` |
| `bpP:p3:tori#data` | `two_scale_kam (K / I₀ witnesses)` | `P3b#bpP:p3:tori#data@L99-L100` | `-` | `bpP:p3:limit-actions`, `bpP:p3:limit-phi`, `bpP:p3:seq`, `bpP:p3:conv#data` |
| `bpP:p3:measure#data` | `two_scale_kam (KO / r / D₀ witnesses)` | `P3b#bpP:p3:measure#data@L148-L148` | `-` | `bpP:p3:tori#data`, `bpP:p3:limit-actions`, `bpP:p3:limit-phi`, `bpP:p3:conv#data`, `bpP:p3:constants` |
| `bpP:p3:ext-weierstrass` | `KAM.uniform_limits / KAM.Weighted.uniform_limit_holomorphic` | `P3a#bpP:p3:ext-weierstrass@L116-L116` | `-` | `-` |

## Departures and explicit source-gap dispositions

| ID | Source / quoted text | Design disposition and reason |
|---|---|---|
| G1 | P2 L177: `e(S_0-S)` under only `S-sigma<S_0` | `ob_der` uses `e(S_0-S+sigma)` at target width `S-sigma`. This is positive under the original outer-width condition. Do not add `S<S_0`: that would weaken the stated bracket lemma and is unnecessary. At a fixed parameter, sum the angular derivative coefficient norms before taking the parameter supremum; never sum global norms. |
| G2 | P3a L91: lowering the slow bound “can increase ... hat E” with `L` unchanged | `rem_norm` proves `rhoHat p ≤ rhoHat p'` and `eHat p' ≤ eHat p`, with `cutoff` unchanged and equal `initialL`. This corrects the direction; it does not retain constants computed before normalization. Constants are chosen compatibly first. |
| G3 | P3a L184–185 / L202–204: displacement of `Psi_+` on `D_(rhohat/2)` although `Psi_+` is a restriction | Keep `Ψ` on the large averaging domain and use the same total function with a restricted source domain for `Ψ+`. `step` states each domain explicitly. The final stage identity and all subsequent compositions use the smaller source domain. |
| G4 | P3b L132–134: `X_H o Phi_j = D Phi_j X_(H_j)` from complex canonical results | `real_symplectic_conjugation` proves the real identity from complex holomorphy, symplecticity and reality. Prove openness of the image by the invertible derivative/local inverse theorem, restrict derivatives using `hamiltonian_real_fderiv`, then use `Canonical.map_hamiltonianJ_comp`. Do not assume real conjugation as a standing premise. |
| G5 | P3b L142–143: a real uniform `C^1` limit is invoked | `real_curve_limit` explicitly states the applicable real locally uniform derivative-limit theorem. For the constructed curves, prove uniform field convergence on close pairs by the common inner-domain Hessian bound, then apply the theorem on every finite time interval. Complex Weierstrass alone is insufficient. |
| D1 | P2/P3 use norms as numbers | Use finite-bound predicates with summability; numerical `E` may be any upper bound. Every theorem is monotone in the supplied bound. No junk `tsum=0` inference is possible. |
| D2 | P3 inverse Hessian in printed matrix norms | Use CLM operator bounds and explicit row operator bounds. Prove the finite-Pi matrix/operator row-sum dictionary once if a matrix consumer needs it. Never use Mathlib's default matrix norm without a bridge. |
| D3 | P3 graph `avg` and P2 graph `avg` | One `avg` export provides the stronger constant `3E` for both action blocks; P3 may weaken to `9E`. P2 `nfb` also retains the stronger `E/(Ks)` average-correction bound. |
| D4 | P3 limit and measure nodes | Named local obligations of one joint existential construction, preserving the same `D_j`, `ihat_j`, `Phi_j`, limit actions and torus family. No source premise is dropped. Private conditional helpers must have distinct `_of_...` names and may consume PROVED induction invariants; none may stand in for the source theorem. |
| D5 | P3a `ball` implicitly uses positive `m,delta` | Make both explicit in the generic helper; actual KAM applications supply positive `Mbar`, positive radii. Zero-dimensional `lip_sup` is handled by subsingleton domain, not by assuming positive dimension in a stronger theorem. |
| D6 | optional partial design | Do not adopt its renamed `Tools`/`freqC`/`kdot`/`ZK` interfaces, matrix norms, default-valued choices or full Parts 4–5 scope. Only Parts 2–3 are owned here. |

These are all five SOURCE_GAP records in this scope (`ob-der`, `rem-norm`, `step`, `inv-conj`, `inv-lim`). Their proof tasks are assigned below; listing a repair does not mark a graph node proved. The blueprint and graph remain unchanged.

## Pinned-source errata carried forward

These are **reported by the blueprint**, not independently reverified against a PDF during this design task. Preserve that provenance when updating the errata ledger. The two source-normalization repairs above concern the blueprint rather than a pinned paper.

- CP10 p.564 (66): target printed `W_{v,sigma}`; the original width is `s`, so the target should be `W_{v,s}` (P2 L250–253; P3b end).
- CP10 p.563 Step 1: `rho=bar rho`, `r=bar rho` conflicts with the `rho<r/2` input of A.1; output radius `bar rho/2` suggests loss `bar rho/4`. The finite schedule here does not rely on that inferred repair. The former allegation `r_p=r_q=0` is withdrawn: the rendering says `epsilon_0` (P2 L251).
- CP10 p.565 (70): `k in Lambda` appears where `k notin Lambda` is required; otherwise the zero divisor would be used at `Lambda={0}` (P3b end).
- CP10 p.554: “n by n1 submatrix” conflicts with last-row index ranges; use the `n2 by n` slow row block (P3a L36–39).
- CP10 p.565 B.1: `Mhat_0:=M` should be `Mhat`; p.566 B.1(i): the printed composition `omega_(j-1) o omega_(j-1)^(-1)` is the identity, while the intended map is `omega_j^(-1) o omega_(j-1)` (P3b E2–E3).
- CP10 (74)/(35): compatible row upper bounds are needed; the slow-action estimate proved in (107) carries `+1`, not `+Mhat/M`. No counterexample to a potentially sharper estimate is asserted (P3b E4).
- CP10 p.569 (91): the computation gives exponent `2(tau+1)`; the printed `tau+1` bound is weaker and true (P3b E6).
- CP10 pp.555/573 “a unique real-analytic embedding”: phase translations invalidate literal uniqueness. Global inverse-frequency Lipschitz dependence also needs bounded `D` or another global hypothesis; separated unbounded islands need only satisfy local bounds (P3b E9).
- CP10 Prop.1/A.1 refers to unpinned [4, Lemma A.5] and a finite induction “as in [4]”. P2's finite iteration and oscillator extension are the assigned replacement proof obligations, not external black boxes. The pointer to Arnold is historical (P3b E11).

No allegation that CP10's constants “cannot all hold” is carried forward. Max norms and the N norm are declared convention changes, not a newly verified source error.

## Modules, packages, and import DAG

All paths below are under `KAM/Planetary/`. Each row is one prover package of 150–800 expected implementation lines. A module may be split further before 1200 lines, keeping its public import path as a cheap facade; none may reach 1501 lines. Module imports are exactly the earlier package modules in the “Inputs” column plus the upstream declarations listed in the reuse table. This table is the import DAG; there is no reverse edge from averaging to the KAM assembly or from either to Parts 4–5.

| Package | Owned path(s) | Expected lines | Inputs | Wave | Obligations / exact exports |
|---|---|---:|---|---:|---|
| P23-01 | `Averaging/Setting.lean` | 250 | landed Weighted, Canonical, frozen definitions | 1 | `conv_data`, `block_bridge`, source input structures, `setting`, `TwoDiv`, width/block adapters |
| P23-02 | `TwoScale/Constants.lean` | 300 | frozen/Mathlib only | 1 | `ScaleData`, `constants`, `initialL`, `nextScale`, `seq`, `rem_norm`, `rem_norm_blocks`, scalar `sums` |
| P23-03 | `TwoScale/Inverse.lean` | 650 | Mathlib inverse/Neumann APIs | 1 | `ext_ift`, `ext_neumann`, `ball`; path lift, Cauchy continuation, convex image-ball bound |
| P23-04 | `TwoScale/Cover.lean` | 300 | landed Measure.McShane, Measure.Lipschitz | 1 | `cover`; fixed point for inverse, including `eta=0` and empty base |
| P23-05 | `Averaging/Direct.lean` | 350 | P23-01; EXACT N Part6 homological/iterative | 2 | `direct`, `direct_step` selected views; full N `homological_direct`, `iterative_direct_a`–`_e` on the same generator/flow |
| P23-06 | `Averaging/OscillatorSetting.lean` | 300 | P23-01 | 2 | `oscPack`, `oscUnpack`, `oscFunction`, `oscParams`, `oscClass`, `oscBound`, `oscGauge`, `s_osc_data` |
| P23-07 | `TwoScale/Lipschitz.lean` | 250 | P23-01; Weighted.general_cauchy | 2 | `lip_sup`; near/far pairs, zero-dimensional case |
| P23-08 | `TwoScale/Period.lean` | 250 | P23-01, P23-02; P1 period conversion | 2 | `period_dictionary`, `period_dictionary_coeff`, `period_dictionary_field`, `use5`, `use5_constants`, `oscPeriodChart`; distinguish both conversions |
| P23-09 | `TwoScale/FourierCompact.lean` | 700 | landed Strip contour/limits and Weighted coefficients | 1 | `fourier_compact`; all iterated derivatives, finite modes plus summable exponential tail |
| P23-10 | `Averaging/Splitting.lean` | 400 | P23-05 | 3 | `firstGen`, `split`, `directMap`; coefficient split, field, integration |
| P23-11 | `Averaging/OscillatorBracket.lean` | 500 | P23-06; Weighted Cauchy/algebra | 3 | `ob_der`, `osc_bracket`, `ob_field`; pays G1 without new premise |
| P23-12 | `Averaging/Finite.lean` | 700 | P23-10, P23-02; N telescope | 4 | `nfb`, `avg`; full N `_a` lattice law on the same flow; tail/quadratic cases, N=0, loss-budget schedule |
| P23-13 | `Averaging/OscillatorStep.lean` | 700 | P23-11, P23-05; Canonical flow/Lie/series | 4 | `oscGen`, `oscStepMap`, full `osc_iter` clauses (Revision 2); domains U/O/V, lattice/inverse/gauge, class/norm, conditional reality |
| P23-14 | `TwoScale/Step.lean` | 800 | P23-12, P23-03, P23-07, P23-02 | 5 | `KamHyp`, `step`; G2/G3, nonresonance, Hessian, inverse images, block constants |
| P23-15 | `Averaging/OscillatorFinite.lean` | 700 | P23-13, P23-12 | 5 | `osc_averaging`, `averaged_remainder`; g correction and tail stay separate |
| P23-16 | `TwoScale/Iteration.lean` | 600 | P23-14 | 6 | `iterative`; existential dependent induction, maps-to/reality/lattice invariants |
| P23-17 | `TwoScale/LimitActions.lean` | 600 | P23-16, P23-02 | 7 | local `limit_actions` and `_of_steps` helpers: uniform convergence, tail, location and 2560n bound |
| P23-18 | `TwoScale/LimitMap.lean` | 750 | P23-17, P23-07, P23-09 | 8 | local `psi_lip`, `limit_phi` and distinct conditional helpers; scaled composition, 768n bound, common strip |
| P23-19 | `TwoScale/RealDynamics.lean` | 400 | P23-01, P23-03; landed RealRestriction, Canonical.SymplecticForm, Mathlib UniformLimitsDeriv | 2 | `real_symplectic_conjugation`, `real_curve_limit`; pays G4/G5 |
| P23-20 | `TwoScale/Tori.lean` | 700 | P23-18, P23-19 | 9 | local `estimates`, `lagr`, `invariance`; same witnesses and uniform field error |
| P23-21 | `TwoScale/Measure.lean` | 600 | P23-18, P23-04, P23-17; Measure.Lipschitz | 9 | local `meas_actions`, `meas_torus`; closed shells as existential distances, cell and rescaling |
| P23-22 | `TwoScale/Theorem.lean` | 400 | P23-20, P23-21, P23-08; P1 IsLatticeTorus | 10 | `two_scale_kam`, unique source inverse locus, local/global inverse-frequency estimates |

The source-free definitions of `coefficientDom`, block adapters and hypothesis bundles are physically placed with their earliest owner. `KamHyp` is split between `TwoScale/Constants.lean` (numbers) and a `TwoScale/Setting.lean` module owned by P23-14 if the proof file approaches 800 lines; this has only P23-01/P23-02 upstream imports, never `Step`. For the same reason, `OscHyp` is defined in P23-06, not the late finite-iteration module. No imports of providers, frozen theorem anchors, draft signatures or the optional partial file are allowed in production.

### Shared-witness implementation contract

P23-16 introduces all stage witnesses in one existence theorem. P23-17–21 prove generic, distinctly named conditional lemmas about those witnesses and the exact proved recurrence relations, then retain the witnesses in one joint existence construction used by P23-22. Their conditional hypotheses are **derived dependencies in the proof**, not premises of `two_scale_kam` and not source-hypothesis fields. The node table's `local:` names refer to the source-facing applications inside that joint proof. Do not expose five unrelated existential theorems and attempt to identify their arbitrary witnesses. No definition is introduced by choosing an arbitrary nonunique averaged map.

Use the following exact local obligations from the blueprint when splitting that proof:

- `limit_actions`: compose `ihat_j`; tail `20 rhohat_j Ehat_j`, block displacement `20(Mbar_i/Mbar) Ehat_0 rhohat_0`; `Dstar` lies in every real half-radius stage; defect Lipschitz `2560n Ehat_0`; frequency identity for **the same** check-i_j.
- `psi_lip`: maps-to between real half-radius stage domains; scaled displacement `(3/4) Ehat_(k-1) 12^(-(k-1))`; defect constant `192n c^(k-1) Ehat_(k-1)`; sum at most `384n Ehat_0`.
- `limit_phi`: uniform real limit on `R^n × Dstar`; scaled defect bound `768n Ehat_0`, lower/upper factors `9/10`, `11/10`; full lattice identity; complex angle extension and the three block sup bounds of source (i). It is not necessary, or asserted, that the limit is holomorphic in actions on an open action set.
- `estimates`, `lagr`: use sharper summed displacement `3/2`, together with the check-i bound, before enlarging to `20(...)`; strict total location `<22 Ehat rhohat<32 Ehat rhohat`; angle Cauchy bound `3n Ehat/4`; Lagrangian form passes through convergence of the **same first derivatives**.
- `invariance`: errors are the three terms in P3b L138–141; the uniform derivative bound on finite-stage maps comes from the open real half-radius domains. To pass the field to the limit use a common inner complex domain for close real pairs, not global uniform continuity on an unbounded set.
- `meas_actions`: cover inverse preimage is within `eta/(1-lambda) ≤30 Ehat rhohat<r`; use Lipschitz image on the full ambient extension. `meas_torus`: rescale, use inverse action displacement `2 Ehat rhohat` and angle displacement `Ehat s/pi`, enlarge the half-open angle cell, and cancel the scaling determinant on both sides. Shell inclusion gives the factor `(1+(4/3)^n)`; the phase extension gives `2^n`; adding the original shell gives EXACT `complementConstant n`.

**Private-interface release gate (audit 1 N2).** Before releasing any of P23-17–21, attach its complete `_of_...` helper commands and an inventory mapping each local obligation above to a helper and to its application in the joint construction. Record the actual P23-16 witness variables and the proved recurrence supplying each conditional hypothesis. Obtain independent signature/applicability review of those commands and applications before dependent packages release. Reject any construction that selects fresh unrelated stage or limit witnesses, or turns a derived invariant into a source hypothesis. These private commands are not yet present in Appendix A and are not covered by the 33-command elaboration receipt.

These local obligations are not discharged by signature elaboration. Each package handoff must include its actual private-lemma signatures and the independent audit of its application in the common construction; a changed private interface never authorizes a changed public theorem or source hypothesis.

## Provider boundary and consumer assembly

No provider is edited or introduced. Part 5 supplies the exact `KamHyp` fields, compatible numerical bounds, and equality `L=initialL` to `two_scale_kam`. It receives one period-one family `K omega theta` already in frozen phase order, and applies the EXACT P1 `cyl_pipeline` with `K3=K omega`, `w=omega`, reconstruction chart `Phi_phys o angleScale(2π)`. It must not divide `omega` again or feed a torus whose angles were already multiplied by `2π` into this pipeline.

The numerical choice from P3b's interface is `M=C`, `Mhat=C mu`, `Mbar=Mbar2=C/mu`, `Mbar1=C`, `E=C mu epsilon^5`; hence `L=C/mu`, `EL=C^2 epsilon^5`, and `x=C^4 epsilon^5/gamma1^2`. Do not infer an upper bound on `K` from an upper bound on `x`; use these equalities before evaluating the logarithm. Keep physical oscillator radius `epsilon`, ambient oscillator radius `epsilon0`, action radius `rhohat` and final enlargement `r=32 Ehat rhohat` distinct. Part 4 consumes the complement bound with the same `c_n` and unit torus cell. This scope proves no P-G root, no root measure positivity, and no strict root upper bound.

## Risks and validation limits

The largest mathematical tasks are the oscillator Lie-series extension, the quantitative image-ball continuation lemma, all-order Fourier compactness, and the common-witness limit construction. Their estimates are represented as proof goals, not as structure assumptions. The oscillator bracket proof requires the fixed-parameter sum before supremum; the full isotropic N composition theorem cannot simply be instantiated with a minimum radius. P23-13 must transfer its proof with the explicit anisotropic gauge and the corrected bracket constant. The ratio is `2 e (1+m) delta/(2π alpha delta_nu)`, and smallness `delta≤2π alpha delta_nu/(16(1+m))` also pays the shrunken-loss ratio. Prove both, not merely formal convergence of a series.

All new implementation files use copyright, `module`, public interface imports, a module docstring and `@[expose] public noncomputable section`. Every proof writer receives the verbatim hard rules below. The supplied scratch file is design-only and may contain `sorry` by the explicit brief exception; no implementation file may contain it.

## Hard rules (verbatim; repeat in every prover brief)

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


## Snapshot and verification receipts

The worktree base was `081967912d5200ad4711d6d16abde6a8cfafea71`. The graph is absent from this design checkout; the brief-authorized `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` is the inventory authority. The three blueprint files were compared byte for byte against that checkout and match. Stable node IDs are preserved; no graph record was edited.

| Source | SHA256 |
|---|---|
| `blueprint-P/parts/p2-averaging.tex` | `d0ae8194e5e562a01289b2e53cad100a0ad197a0ff15fad6fa7ac9bb2c27764b` |
| `blueprint-P/parts/p3a-two-scale-iteration.tex` | `94327df07e9c89e6ff5186a71261fa66120a18993bfd9b3764ce4607c856328c` |
| `blueprint-P/parts/p3b-two-scale-limit.tex` | `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a` |
| `/root/code/KAM-inp/.drafts/design/PPart1Signatures.lean` | `78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7` |
| `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| `/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` (Revision 2 live inventory) | `5b1eff327a09a63a553686ba14a4763978e0f589fde8ad42cc67d6545f819f44` |
| `/root/code/KAM-inp/docs/graph/P/reviews/GLOBAL-review.md` | `39f5a84a7d261187fa474fa94ecc839a1fac463810fdd8ce674fe5766d539e65` |

`P23Signatures.lean` has 861 lines, 33 theorem commands, all with `sorry` proof bodies, and no resource overrides. Its SHA256 is `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`. The deliverable path is `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`; the worktree-local master and scratch check copy have identical bytes. Appendix A below is the entire file, including its upstream fixtures and five axiom-print commands.

Revision 2 gated elaboration command:

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p23 .drafts/scratch/P23Signatures.lean
```

Revision 2 result: **exit 0**, exactly 33 warnings, all indicating that the declaration uses `sorry`; no errors and no other warnings. The five `#print axioms` commands (`nfb`, `osc_averaging`, `step`, `iterative`, `two_scale_kam`) each report `[propext, sorryAx, Classical.choice, Quot.sound]`. Log: `.drafts/scratch/P23-r2-check.log`. The checked scratch copy is byte-identical to Appendix A and the shared deliverable; this establishes elaboration only. The initial log-validator assertion expected single quotes around sorry instead of Lean's backticks; correcting that parser made the receipt validation pass without changing signatures or rerunning Lean.

Revision 1 historical result: **exit 0**, 33 warnings, all `declaration uses 'sorry'`; no errors and no other warnings. The five `#print axioms` commands (`nfb`, `osc_averaging`, `step`, `iterative`, `two_scale_kam`) each report `[propext, sorryAx, Classical.choice, Quot.sound]`. Log: `.drafts/scratch/P23-check.log`. This is signature elaboration, not proof verification.

Revision 1 historical `scripts/lint_sources.sh` result: exit 1. Output includes `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`; its later ABI subprocess fails `unknown module prefix 'KAM'` because the design worktree has no built-library overlay. This is not a passing full lint. **Workflow deviation:** I should have inspected the linter's tail before running it: it invokes `abi_hashes.py`, which attempts an ungated Lean scratch probe. That failed probe did not elaborate a module. No further ungated Lean or direct build was run. The user-prescribed signature gate is used for all subsequent elaboration; no overlay rebuild or library build is attempted. The linter log is `.drafts/scratch/P23-lint.log`.

Revision 2 reran `scripts/lint_sources.sh` with scratch PATH guards that reject `lake`/`lean`, because the script's ABI tail otherwise attempts an ungated elaboration. Exit **1**: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, then `Revision 2: ABI elaboration blocked; Lean may run only via inp_sig_check.sh`. This is a partial source-lint receipt, not a full lint or ABI PASS. Log: `.drafts/scratch/P23-r2-lint.log`. No ungated Lean process was started in Revision 2, and no production module changed, so no production build is claimed or attempted.

**Gate recovery in Revision 2.** Before the signature run acquired a slot, a different checkout's ABI PATH wrapper recursively invoked `inp_sig_check.sh` and held all three slots while waiting for a fourth acquisition. After verifying its innermost waiter (PID 1339717) had only a `sleep` child and no Lean child, I terminated that waiter with SIGTERM. The recursive chain unwound and slots became available; the interrupted ABI check must be rerun by its owner. No active Lean process, source file or build artifact was terminated or edited by this recovery. This shared-process intervention is disclosed separately from the design changes.

Revision 2 static checks: exact audit-F1 replacement-command equality; Appendix/shared/local/scratch byte equality; 131 unique rows equal to the live scoped graph-node inventory; 33 theorem commands and 33 `sorry` bodies; 861-line cap; no forbidden code tokens or resource overrides; `git diff --check`: all **PASS**. Blueprint, P1/N6 fixture-source and global-review SHA256 values were rechecked and match the original receipt. The live DEPGRAPH changed concurrently; its refreshed hash above records the inventory used for Revision 2, whose scoped node set still matches exactly. No graph edits were made here.

No proof-closure or axiom-cleanliness claim follows from a successful signature check. The expected axiom set includes `sorryAx` for each new theorem. The final handoff records the actual gated exit code and diagnostics. Markdown whitespace, node coverage and exact Appendix/signature equality are checked separately, since the design document was initially untracked.

## Appendix A: exact signatures

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Weighted.Projections
public import KAM.Weighted.Cauchy
public import KAM.Weighted.Bracket
public import KAM.Weighted.SupWeighted
public import KAM.Canonical.Flow
public import KAM.Canonical.Setting
public import KAM.Frozen.Planetary.Defs.Phase
public import KAM.Frozen.Defs.HamiltonianVectorField
public import KAM.Frozen.Defs.SymplecticForm
public import KAM.Measure.Lipschitz
public import KAM.Measure.McShane
public import KAM.ODE.Basic
public import KAM.Frozen.Planetary.Defs.Fast
public import KAM.Frozen.Planetary.Defs.Slow

/-! # P23 design signatures. All proofs deliberately `sorry`.
Upstream definition fixtures below are verbatim extracts, not replacement APIs.
Delete fixtures and import their owning modules when landed. -/
@[expose] public noncomputable section
open Set Metric MeasureTheory Real

namespace KAM.NormalForm
-- VERBATIM NPart67Signatures.lean: zBall, freq, dotC, DivisorBound, homGen.
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}
def freq {n : ℕ} (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)
def dotC {n : ℕ} (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i
def DivisorBound {n : ℕ} (V : Set (Fin n → ℂ)) (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (c : ℝ) : Prop :=
  ∀ I ∈ V, ∀ k ∈ zBall n K \ Λ, c ≤ ‖dotC k (freq h I)‖
def homGen {n : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    KAM.Weighted.coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (freq h z.2)) * KAM.character k z.1) k
end KAM.NormalForm

namespace KAM.Planetary
open KAM.Weighted KAM.Canonical KAM.NormalForm
-- VERBATIM bodies and binder order from PPart1Signatures.lean.
def twoScaleDiophantine (n₁ n₂ : ℕ) (γ₁ γ₂ τ : ℝ) : Set (Fin (n₁ + n₂) → ℝ) :=
  {ω | (∀ k : Fin (n₁ + n₂) → ℤ, (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) ≠ 0 →
        γ₁ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|) ∧
    (∀ k : Fin (n₁ + n₂) → ℤ, k ≠ 0 → (fun i : Fin n₁ => k (Fin.castAdd n₂ i)) = 0 →
        γ₂ / (∑ i, |(k i : ℝ)|) ^ τ ≤ |∑ i, (k i : ℝ) * ω i|)}
def IsLatticeTorus {d : ℕ} (L : (Fin d → ℤ) → Phase d) (G : Phase d → ℝ) (O : Set (Phase d))
    (w : Fin d → ℝ) (K : (Fin d → ℝ) → Phase d) : Prop :=
  (AnalyticOnNhd ℝ K univ ∧ ∀ θ, K θ ∈ O ∧ DifferentiableAt ℝ G (K θ)) ∧
  (∀ θ (k : Fin d → ℤ), K (θ + fun i => (k i : ℝ)) = K θ + L k) ∧
  (∀ θ θ', K θ = K θ' → ∃ k : Fin d → ℤ, θ' = θ + fun i => (k i : ℝ)) ∧
  (∀ θ, Function.Injective (fderiv ℝ K θ)) ∧
  (∀ θ u v, KAM.symplecticForm (fderiv ℝ K θ u) (fderiv ℝ K θ v) = 0) ∧
  (∀ θ t, HasDerivAt (fun s : ℝ => K (θ + s • w))
    (KAM.hamiltonianVectorField G (K (θ + t • w))) t)
-- END upstream fixtures.

abbrev CPhase (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ)
abbrev CHam (n : ℕ) := CPhase n → ℂ

def geometricWidth (σ : ℝ) : ℝ := σ / (2 * π)
def realBase {n : ℕ} (D : Set (Fin n → ℝ)) : Set (Fin n → ℂ) := KAM.realInclusion n '' D
-- The frozen actionNbhd is used directly; no second tube representation.
def coefficientDom {n : ℕ} (D : Set (Fin n → ℝ)) (r σ : ℝ) : Set (CPhase n) :=
  Dom n (realBase D) r (geometricWidth σ)
def realTube {n : ℕ} (D : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℝ) :=
  (KAM.realInclusion n) ⁻¹' KAM.actionNbhd D r

def firstBlock {a b : ℕ} {𝕜 : Type*} (x : Fin (a + b) → 𝕜) : Fin a → 𝕜 :=
  fun i => x (Fin.castAdd b i)
def lastBlock {a b : ℕ} {𝕜 : Type*} (x : Fin (a + b) → 𝕜) : Fin b → 𝕜 :=
  fun i => x (Fin.natAdd a i)

theorem block_bridge {a b : ℕ} (v : Fin (a + b) → ℝ) :
    firstBlock (b := b) v = fast v ∧ lastBlock (a := a) v = slow v := sorry

theorem conv_data {n : ℕ} (D : Set (Fin n → ℝ)) (r σ : ℝ) :
    polyNbhd (realBase D) r = KAM.actionNbhd D r ∧
    coefficientDom D r σ = KAM.complexStrip n (σ / (2 * π)) ×ˢ KAM.actionNbhd D r := sorry

/-- P2 setting, the exact N direct-divisor predicate with arbitrary q >= 1. -/
abbrev setting {n : ℕ} (D : Set (Fin n → ℂ)) (r K α q : ℝ)
    (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  DivisorBound (polyNbhd D r) K Λ h (α / q)

/-- Source premises shared by direct homological solve and splitting. -/
structure DirectHyp {n : ℕ} (D : Set (Fin n → ℂ)) (r s K α q δ : ℝ)
    (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (f : CHam n) : Prop where
  r_pos : 0 < r
  s_pos : 0 < s
  K_nonneg : 0 ≤ K
  α_pos : 0 < α
  q_ge : 1 ≤ q
  δ_nonneg : 0 ≤ δ
  holo : DifferentiableOn ℂ h (polyNbhd D r)
  div : setting D r K α q Λ h
  cls : InClass D r s f
  bound : WBound D r s f δ

/-- Selected solve/norm view of N homological_direct, not its full contract.
Use that upstream theorem on this same homGen for all other projections. -/
theorem direct {n : ℕ} {D : Set (Fin n → ℂ)} {r s K α q δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : CHam n}
    (H : DirectHyp D r s K α q δ Λ h f) :
    InClass D r s (homGen K Λ h f) ∧
    WBound D r s (homGen K Λ h f) (q * δ / (2 * π * α)) ∧
    ∀ z ∈ Dom n D r s,
      poissonBracket (homGen K Λ h f) (fun w => h w.2) z +
        projMode Λ (truncate K f) z = truncate K f z := sorry

/-- Full-neighbourhood two-scale nonresonance, no derived Lipschitz premise. -/
def TwoDiv {a b : ℕ} (V : Set (Fin (a + b) → ℂ)) (K α₁ α₂ q : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) : Prop :=
  ∀ I ∈ V, ∀ k : Fin (a + b) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ K →
    (if firstBlock (b := b) k = 0 then α₂ else α₁) / q ≤ ‖dotC k (freq h I)‖

def firstGen {a b : ℕ} (K : ℝ) (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : CHam (a + b) :=
  projMode {k | firstBlock (b := b) k ≠ 0} (homGen K {0} h f)

def directMap {n : ℕ} (D : Set (Fin n → ℂ)) (r s ρ σ K : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam n) : CPhase n → CPhase n :=
  flow (KAM.hamiltonianVectorFieldℂ (homGen K {0} h f)) (Dom n D (r - ρ) (s - σ)) 1

theorem split {a b : ℕ} {D : Set (Fin (a + b) → ℂ)} {r s K α₁ α₂ q δ ρ σ : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : DirectHyp D r s K α₂ q δ {0} h f)
    (hα : α₂ ≤ α₁) (hd : TwoDiv (polyNbhd D r) K α₁ α₂ q h)
    (hρ : 0 < ρ) (hρr : 2 * ρ < r) (hσ : 0 < σ) (hσs : 2 * σ < s)
    (hsmall : q * δ / (2 * π * α₂ * ρ * σ) ≤ 1 / 4) :
    WBound D r s (firstGen K h f) (q * δ / (2 * π * α₁)) ∧
    (∀ I ∈ polyNbhd D r, ∀ k, firstBlock (b := b) k ≠ 0 →
      coeff (homGen K {0} h f - firstGen K h f) I k = 0) ∧
    ∀ z ∈ Dom (a + b) D (r - 3 * ρ / 2) (s - 3 * σ / 2),
      ‖firstBlock (b := b) ((directMap D r s ρ σ K h f z).2 - z.2)‖ ≤ q * δ / (exp 1 * (2 * π * α₁) * σ) ∧
      ‖lastBlock (a := a) ((directMap D r s ρ σ K h f z).2 - z.2)‖ ≤ q * δ / (exp 1 * (2 * π * α₂) * σ) ∧
      ‖(directMap D r s ρ σ K h f z).1 - z.1‖ ≤ q * δ / (2 * π * α₂ * ρ) := sorry

/-- Averaging premises; E is a numerical bound, fixed before cutoff selection. -/
structure AvgHyp {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (r sbar s K α₁ α₂ E : ℝ)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop where
  r_pos : 0 < r
  sbar_nonneg : 0 ≤ sbar
  s_pos : 0 < s
  K_pos : 0 < K
  budget : 6 ≤ 2 * π * K * s
  α₂_pos : 0 < α₂
  α_order : α₂ ≤ α₁
  E_nonneg : 0 ≤ E
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D r)
  real_h : RealOn (Dom (a + b) (realBase D) r (sbar + s)) (fun z => h z.2)
  real_f : RealOn (Dom (a + b) (realBase D) r (sbar + s)) f
  cls : InClass (realBase D) r (sbar + s) f
  bound : WBound (realBase D) r (sbar + s) f E
  div : TwoDiv (KAM.actionNbhd D r) K α₁ α₂ 1 h
  small : E ≤ α₂ * r / (128 * K)

/-- Joint witnesses, all clauses of P2 nfb; no conclusion bundle becomes a premise. -/
theorem nfb {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : AvgHyp D r sbar s K α₁ α₂ E h f) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)),
      let V := Dom (a + b) (realBase D) (r / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧
      MapsTo Ψ V (Dom (a + b) (realBase D) r (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (KAM.actionNbhd D (r / 2)) ∧
      RealOn V (fun z => g z.2) ∧ RealOn V fs ∧
      (∀ z ∈ V, h (Ψ z).2 + f (Ψ z) = h z.2 + g z.2 + fs z) ∧
      WBound (realBase D) (r / 2) (sbar + s / 6) (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0) (E / (2 * π * K * s)) ∧
      WBound (realBase D) (r / 2) (sbar + s / 6) (fun z : CPhase (a + b) => g z.2 - coeff f z.2 0) (E / 4) ∧
      InClass (realBase D) (r / 2) (sbar + s / 6) fs ∧
      WBound (realBase D) (r / 2) (sbar + s / 6) fs (exp (-(2 * π * K * s) / 6) * E) ∧
      ∀ z ∈ V,
        (2 * π * α₁) * s * ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        (2 * π * α₂) * s * ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        (2 * π * α₂) * r * ‖(Ψ z).1 - z.1‖ ≤ 9 * E := sorry

/-- P2 avg and P3 avg share one export; coefficient-radius conversion is explicit in input. -/
theorem avg {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {r sbar s K α₁ α₂ E : ℝ}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : AvgHyp D r (geometricWidth sbar) (geometricWidth s) K α₁ α₂ E h f)
    (hstrict : 64 * exp 1 * K * E < α₂ * r) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ) (fs : CHam (a + b)),
      let V := coefficientDom D (r / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (coefficientDom D r (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (KAM.actionNbhd D (r / 2)) ∧ RealOn V (fun z => g z.2) ∧ RealOn V fs ∧
      (∀ z ∈ V, h (Ψ z).2 + f (Ψ z) = h z.2 + g z.2 + fs z) ∧
      (∀ I ∈ KAM.actionNbhd D (r / 2), ‖g I - coeff f I 0‖ ≤ E / 4 ∧ ‖g I - coeff f I 0‖ ≤ E / (K * s)) ∧
      InClass (realBase D) (r / 2) (geometricWidth (sbar + s / 6)) fs ∧
      WBound (realBase D) (r / 2) (geometricWidth (sbar + s / 6)) fs (exp (-K * s / 6) * E) ∧
      ∀ z ∈ V, α₁ * s * ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        α₂ * s * ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        2 * π * α₂ * r * ‖(Ψ z).1 - z.1‖ ≤ 9 * E := sorry


/-- Selected view of N iterative_direct_a through iterative_direct_e. Instantiate
p=2, alpha_N=2alpha/q on this same generator/flow. In particular, finite averaging
uses upstream iterative_direct_a for integer translations; this wrapper is not
the entire inherited N contract. -/
theorem direct_step {n J : ℕ} {D : Set (Fin n → ℂ)} {r s K α q δ ρ σ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : CHam n}
    {gj : Fin J → CHam n} {rj sj Mj : Fin J → ℝ}
    (H : DirectHyp D r s K α q δ Λ h f)
    (hρ : 0 < ρ ∧ 2 * ρ < r) (hσ : 0 < σ ∧ 2 * σ < s)
    (hsmall : q * δ / (2 * π * α * ρ * σ) ≤ 1 / 4)
    (hg : ∀ j, InClass D (rj j) (sj j) (gj j) ∧ WBound D (rj j) (sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ s ≤ sj j) :
    let φ := homGen K Λ h f
    let Ψ := flow (KAM.hamiltonianVectorFieldℂ φ) (Dom n D (r - ρ) (s - σ)) 1
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + projMode Λ (truncate K f) z
    let fp := fun z => h (Ψ z).2 + g (Ψ z) + f (Ψ z) - h z.2 - gp z
    let u := q * δ / (2 * π * α * ρ * σ)
    let star := ∑ j, (1 / 2) * (ρ / (rj j - r + ρ) + σ / (sj j - s + σ)) * Mj j
    let V := Dom n D (r - 2 * ρ) (s - 2 * σ)
    DifferentiableOn ℂ Ψ (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)) ∧
    MapsTo Ψ (Dom n D (r - 3 * ρ / 2) (s - 3 * σ / 2)) (Dom n D (r - ρ) (s - σ)) ∧
    Set.InjOn Ψ V ∧
    (∀ z ∈ V, ∀ v w, symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w) ∧
    InClass D (r - 2 * ρ) (s - 2 * σ) fp ∧
    WBound D (r - 2 * ρ) (s - 2 * σ) fp
      ((1 - 2 * u)⁻¹ * (2 * q / (exp 1 * (2 * π * α) * ρ * σ) * (star + δ) +
        exp (-(2 * π * K * σ))) * δ) ∧
    (∀ z ∈ V, ‖(Ψ z).1 - z.1‖ ≤ q * δ / (2 * π * α * ρ) ∧
      ‖(Ψ z).2 - z.2‖ ≤ q * δ / (exp 1 * (2 * π * α) * σ)) ∧
    ((∀ k ∈ Λ, -k ∈ Λ) → RealOn (Dom n D r s) (fun z => h z.2) →
      RealOn (Dom n D r s) f → (∀ j, RealOn (Dom n D (rj j) (sj j)) (gj j)) →
      RealOn V gp ∧ RealOn V fp ∧
      ∀ x : Phase n, KAM.realInclusion₂ n x ∈ V → Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n)) := sorry

/-! ## Oscillators: use the existing Weighted.coeff/wsum at a flattened parameter.
Flat parameter order (I,p,q); phase order ((theta,q),(I,p)), frozen order. -/
def oscPack {n m : ℕ} (z : CPhase (n + m)) : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) :=
  (firstBlock (b := m) z.1, Fin.append (firstBlock (b := m) z.2)
    (Fin.append (lastBlock (a := n) z.2) (lastBlock (a := n) z.1)))
def oscUnpack {n m : ℕ} (z : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ)) : CPhase (n + m) :=
  (Fin.append z.1 (lastBlock (a := m) (lastBlock (a := n) z.2)),
    Fin.append (firstBlock (b := m + m) z.2) (firstBlock (b := m) (lastBlock (a := n) z.2)))
def oscFunction {n m : ℕ} (f : CHam (n + m)) : (Fin n → ℂ) × (Fin (n + (m + m)) → ℂ) → ℂ := f ∘ oscUnpack

def oscParams {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq : ℝ) : Set (Fin (n + (m + m)) → ℂ) :=
  {x | firstBlock (b := m + m) x ∈ KAM.actionNbhd D r ∧
    ‖firstBlock (b := m) (lastBlock (a := n) x)‖ < rp ∧
    ‖lastBlock (a := m) (lastBlock (a := n) x)‖ < rq}
def oscDom {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) : Set (CPhase (n + m)) :=
  oscPack ⁻¹' (KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq)
def oscBound {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) (f : CHam (n + m)) (E : ℝ) : Prop :=
  ∀ x ∈ oscParams (m := m) D r rp rq,
    WSummable (oscFunction f) S x ∧ wsum (oscFunction f) S x ≤ E

def oscClass {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S : ℝ) (f : CHam (n + m)) : Prop :=
  DifferentiableOn ℂ f (oscDom D r rp rq S) ∧
    ∀ j : Fin n, ∀ z ∈ oscDom D r rp rq S,
      f (z.1 + Pi.single (Fin.castAdd m j) 1, z.2) = f z

def oscGauge {n m : ℕ} (ρ ρp ρq σ : ℝ) (z : CPhase (n + m)) : ℝ :=
  max (max (‖firstBlock (b := m) z.1‖ / σ) (‖firstBlock (b := m) z.2‖ / ρ))
    (max (‖lastBlock (a := n) z.1‖ / ρq) (‖lastBlock (a := n) z.2‖ / ρp))

theorem s_osc_data {n m : ℕ} (z : CPhase (n + m)) : oscUnpack (oscPack z) = z := sorry

theorem osc_bracket {n m : ℕ} {D : Set (Fin n → ℝ)} {r₀ rp₀ rq₀ S₀ r rp rq S ρ ρp ρq σ A B : ℝ}
    {u w : CHam (n + m)} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hu : oscClass D r₀ rp₀ rq₀ S₀ u) (hw : oscClass D r rp rq S w)
    (hA : oscBound D r₀ rp₀ rq₀ S₀ u A) (hB : oscBound D r rp rq S w B)
    (hρ : 0 < ρ ∧ ρ < r) (hρp : 0 < ρp ∧ ρp < rp) (hρq : 0 < ρq ∧ ρq < rq)
    (hσ : 0 < σ ∧ σ < S) (houter : r - ρ < r₀ ∧ rp - ρp < rp₀ ∧ rq - ρq < rq₀ ∧ S - σ < S₀) :
    let W := (1 / exp 1) * (ρ / (r₀ - r + ρ) + σ / (S₀ - S + σ)) +
      m * (ρq / (rq₀ - rq + ρq) + ρp / (rp₀ - rp + ρp))
    oscClass D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket u w) ∧
    oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ) (poissonBracket u w)
      (W / min (ρ * σ) (ρp * ρq) * A * B) := sorry

/-- This generic field bound is the other clause of osc-bracket. -/
theorem ob_field {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ E : ℝ} {φ : CHam (n + m)}
    (hφ : oscClass D r rp rq S φ) (hE : oscBound D r rp rq S φ E)
    (hρ : 0 < ρ ∧ ρ < r) (hρp : 0 < ρp ∧ ρp < rp) (hρq : 0 < ρq ∧ ρq < rq)
    (hσ : 0 < σ ∧ σ < S) :
    ∀ z ∈ oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ),
      oscGauge ρ ρp ρq σ (KAM.hamiltonianVectorFieldℂ φ z) ≤ E / min (ρ * σ) (ρp * ρq) := sorry

/-- Joint source hypotheses for oscillator averaging. -/
structure OscHyp {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq sbar s K α E : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : Prop where
  n_pos : 1 ≤ n
  m_pos : 1 ≤ m
  positive : 0 < r ∧ 0 < rp ∧ 0 < rq ∧ 0 < s ∧ 0 < K ∧ 0 < α
  sbar_nonneg : 0 ≤ sbar
  E_nonneg : 0 ≤ E
  budget : 6 ≤ 2 * π * K * s
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D r)
  real_h : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd D r → (h (KAM.realInclusion n I)).im = 0
  cls : oscClass D r rp rq (sbar + s) f
  bound : oscBound D r rp rq (sbar + s) f E
  real_f : RealOn (oscDom D r rp rq (sbar + s)) f
  divisor : DivisorBound (KAM.actionNbhd D r) K {0} h α
  small : 2 ^ 12 * (1 + (m : ℝ)) * K * E * s ≤ α * min (r * s) (rp * rq)

theorem osc_averaging {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq sbar s K α E : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} (H : OscHyp D r rp rq sbar s K α E h f) :
    ∃ (Ψ : CPhase (n + m) → CPhase (n + m)) (g fs : CHam (n + m)),
      let V := oscDom D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (oscDom D r rp rq (sbar + s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin n → ℤ,
        Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) = Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
      (∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ V →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) ∧
      oscClass D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) g ∧ RealOn V g ∧
      (∀ x ∈ oscParams (m := m) D (r / 2) (rp / 2) (rq / 2),
        ∀ θ θ', oscUnpack (θ, x) ∈ V → oscUnpack (θ', x) ∈ V → g (oscUnpack (θ, x)) = g (oscUnpack (θ', x))) ∧
      (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + f (Ψ z) = h (firstBlock (b := m) z.2) + g z + fs z) ∧
      oscBound D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6)
        (fun z => g z - coeff (oscFunction f) (oscPack z).2 0)
        (400 * (1 + (m : ℝ)) * E ^ 2 / (2 * π * α * min (r * s) (rp * rq))) ∧
      oscClass D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) fs ∧ RealOn V fs ∧
      oscBound D (r / 2) (rp / 2) (rq / 2) (sbar + s / 6) fs (exp (-(2 * π * K * s) / 6) * E) ∧
      ∀ z ∈ V,
        2 * π * α * s * ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ 3 * E ∧
        2 * π * α * r * ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ 9 * E ∧
        2 * π * α * rq * ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ 9 * E ∧
        2 * π * α * rp * ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ 9 * E := sorry

/-- P2 averaged-remainder, retaining both g and the exponentially small fs. -/
theorem averaged_remainder {n m : ℕ} {D : Set (Fin n → ℝ)} {r ε₀ s₀ ε μ α : ℝ}
    {h : (Fin n → ℂ) → ℂ} {P : CHam (n + m)}
    (hε : 0 < ε ∧ ε < exp (-1 / 5)) (hμ : 0 < μ)
    (H : OscHyp D r ε₀ ε₀ 0 s₀ (15 / (π * s₀) * log (1 / ε)) α μ h (μ • P))
    (hP : oscBound D r ε₀ ε₀ s₀ P 1) :
    ∃ (Ψ : CPhase (n + m) → CPhase (n + m)) (g fs R : CHam (n + m)),
      let V := oscDom D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6)
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (oscDom D r ε₀ ε₀ s₀) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin n → ℤ,
        Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) = Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
      (∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ V →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) g ∧ RealOn V g ∧
      (∀ x ∈ oscParams (m := m) D (r / 2) (ε₀ / 2) (ε₀ / 2), ∀ θ θ',
        oscUnpack (θ, x) ∈ V → oscUnpack (θ', x) ∈ V → g (oscUnpack (θ, x)) = g (oscUnpack (θ', x))) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) fs ∧ RealOn V fs ∧ RealOn V R ∧
      (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + μ * P (Ψ z) =
        h (firstBlock (b := m) z.2) + μ * coeff (oscFunction P) (oscPack z).2 0 + R z) ∧
      (∀ z ∈ V, R z = g z - μ * coeff (oscFunction P) (oscPack z).2 0 + fs z) ∧
      oscClass D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) R ∧
      oscBound D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) R
        (400 * (1 + (m : ℝ)) * μ ^ 2 / (2 * π * α * min (r * s₀) (ε₀ ^ 2)) + μ * ε ^ 5) ∧
      oscBound D (r / 2) (ε₀ / 2) (ε₀ / 2) (s₀ / 6) fs (μ * ε ^ 5) ∧
      ∀ z ∈ V,
        2 * π * α * s₀ * ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ 3 * μ ∧
        2 * π * α * r * ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ 9 * μ ∧
        2 * π * α * ε₀ * ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ 9 * μ ∧
        2 * π * α * ε₀ * ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ 9 * μ := sorry


/-- Corrected ob-der: every angular derivative is evaluated at the TARGET width S-sigma. -/
theorem ob_der {n m : ℕ} {D : Set (Fin n → ℝ)} {r₀ rp₀ rq₀ S₀ r rp rq S ρ ρp ρq σ A : ℝ}
    {u : CHam (n + m)} (hu : oscClass D r₀ rp₀ rq₀ S₀ u)
    (hA : oscBound D r₀ rp₀ rq₀ S₀ u A)
    (hpos : 0 < r - ρ ∧ 0 < rp - ρp ∧ 0 < rq - ρq ∧ 0 < S - σ)
    (houter : r - ρ < r₀ ∧ rp - ρp < rp₀ ∧ rq - ρq < rq₀ ∧ S - σ < S₀) :
    (∀ j : Fin n, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (Pi.single (Fin.castAdd m j) 1, 0)) (A / (exp 1 * (S₀ - S + σ)))) ∧
    (∀ j : Fin n, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (0, Pi.single (Fin.castAdd m j) 1)) (A / (r₀ - r + ρ))) ∧
    (∀ j : Fin m, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (0, Pi.single (Fin.natAdd n j) 1)) (A / (rp₀ - rp + ρp))) ∧
    (∀ j : Fin m, oscBound D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
      (fun z => fderiv ℂ u z (Pi.single (Fin.natAdd n j) 1, 0)) (A / (rq₀ - rq + ρq))) := sorry

/-- P2 oscillator homological polynomial, same coefficients as Weighted.coeff. -/
def oscGen {n m : ℕ} (K : ℝ) (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : CHam (n + m) :=
  fun z => ∑' k : Fin n → ℤ, (zBall n K \ {0}).indicator (fun k =>
    coeff (oscFunction f) (oscPack z).2 k /
      (2 * (π : ℂ) * Complex.I * dotC k (freq h (firstBlock (b := m) z.2))) *
        KAM.character k (firstBlock (b := m) z.1)) k

def oscStepMap {n m : ℕ} (D : Set (Fin n → ℝ)) (r rp rq S ρ ρp ρq σ K : ℝ)
    (h : (Fin n → ℂ) → ℂ) (f : CHam (n + m)) : CPhase (n + m) → CPhase (n + m) :=
  flow (KAM.hamiltonianVectorFieldℂ (oscGen K h f)) (oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)) 1

/-- Full inherited oscillator step contract (audit 1 F1, Revision 2).
Finite source decomposition only; reality is a conditional conclusion. -/
theorem osc_iter {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} {gj : Fin J → CHam (n + m)}
    {rj rpj rqj Sj Mj : Fin J → ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hg : ∀ j, oscClass D (rj j) (rpj j) (rqj j) (Sj j) (gj j) ∧
      oscBound D (rj j) (rpj j) (rqj j) (Sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ rp ≤ rpj j ∧ rq ≤ rqj j ∧ S ≤ Sj j) :
    let Ψ := oscStepMap D r rp rq S ρ ρp ρq σ K h f
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + coeff (oscFunction f) (oscPack z).2 0
    let fp := fun z => h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) -
      h (firstBlock (b := m) z.2) - gp z
    let d := min (ρ * σ) (ρp * ρq)
    let Rsum := ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
      (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j
    let φ := oscGen K h f
    let O := oscDom D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    oscClass D r rp rq S φ ∧
    oscBound D r rp rq S φ (δ / (2 * π * α)) ∧
    DifferentiableOn ℂ Ψ U ∧ MapsTo Ψ U O ∧ Set.InjOn Ψ V ∧
    (∀ z ∈ U, ∀ k : Fin n → ℤ,
      Ψ (z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) =
        Ψ z + (Fin.append (fun i => (k i : ℂ)) 0, 0)) ∧
    (∀ z ∈ V, flow (KAM.hamiltonianVectorFieldℂ φ) O (-1) (Ψ z) = z) ∧
    oscClass D r rp rq S gp ∧
    oscBound D r rp rq S (fun z => gp z - g z) δ ∧
    (∀ z ∈ V, h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) =
      h (firstBlock (b := m) z.2) + gp z + fp z) ∧
    (∀ z ∈ U, oscGauge ρ ρp ρq σ (Ψ z - z) ≤ u) ∧
    (∀ z ∈ V, ∀ v,
      oscGauge ρ ρp ρq σ (fderiv ℂ Ψ z v - v) ≤
        2 * u * oscGauge ρ ρp ρq σ v) ∧
    (∀ z ∈ U, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
    oscClass D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp ∧
    oscBound D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ) fp
      ((1 - 2 * exp 1 * (1 + (m : ℝ)) * δ / (2 * π * α * d))⁻¹ *
        (2 * (1 + (m : ℝ)) / (2 * π * α * d) * (Rsum + δ) + exp (-(2 * π * K * σ))) * δ) ∧
    (∀ z ∈ U,
      ‖firstBlock (b := m) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρ) ∧
      ‖firstBlock (b := m) ((Ψ z).2 - z.2)‖ ≤ δ / (exp 1 * (2 * π * α) * σ) ∧
      ‖lastBlock (a := n) ((Ψ z).1 - z.1)‖ ≤ δ / (2 * π * α * ρp) ∧
      ‖lastBlock (a := n) ((Ψ z).2 - z.2)‖ ≤ δ / (2 * π * α * ρq)) ∧
    (RealOn (oscDom D r rp rq S) (fun z => h (firstBlock (b := m) z.2)) →
      RealOn (oscDom D r rp rq S) g → RealOn (oscDom D r rp rq S) f →
      RealOn (oscDom D r rp rq S) φ ∧ RealOn (oscDom D r rp rq S) gp ∧
      RealOn V fp ∧
      ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ U →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) := sorry

/-! ## Two-scale constants: formula data only. Positivity stays in KamHyp. -/
structure ScaleData where
  τ : ℝ
  γ₁ : ℝ
  γ₂ : ℝ
  s : ℝ
  ρ : ℝ
  E : ℝ
  M : ℝ
  Mhat : ℝ
  Mbar : ℝ
  Mbar₁ : ℝ
  Mbar₂ : ℝ
  L : ℝ

def constants (p : ScaleData) : ℝ × ℝ × ℝ :=
  let x := p.E * p.M ^ 2 * p.L / p.γ₁ ^ 2
  let K := 6 / p.s * max 1 (log (1 / x))
  let R := min (min (p.γ₁ / (3 * p.M * K ^ (p.τ + 1)))
    (p.γ₂ / (3 * p.Mhat * K ^ (p.τ + 1)))) p.ρ
  (K, R, p.E * p.L / R ^ 2)
def cutoff (p : ScaleData) : ℝ := (constants p).1
def rhoHat (p : ScaleData) : ℝ := (constants p).2.1
def eHat (p : ScaleData) : ℝ := (constants p).2.2
def kamConstant (n : ℕ) (τ : ℝ) : ℝ := max (2 ^ 13 * (n : ℝ)) ((24 : ℝ) ^ (τ + 1) / 3)
def complementConstant (n : ℕ) : ℝ := 1 + (1 + 2 ^ n) * (1 + (4 / 3 : ℝ) ^ n)
def initialL (M Mhat Mbar : ℝ) : ℝ := max Mbar (max M⁻¹ Mhat⁻¹)
def nextScale (p : ScaleData) : ScaleData :=
  { p with
    s := p.s / 12
    ρ := rhoHat p / 16
    E := p.E ^ 2 * p.L * p.M ^ 2 / p.γ₁ ^ 2
    M := 2 * p.M
    Mhat := 2 * p.Mhat
    Mbar := 2 * p.Mbar
    Mbar₁ := 2 * p.Mbar₁
    Mbar₂ := 2 * p.Mbar₂
    L := 2 * p.L }
def seq (p : ScaleData) : ℕ → ScaleData
  | 0 => p
  | j + 1 => nextScale (seq p j)

def realFreq {n : ℕ} (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (freq h (KAM.realInclusion n I) i).re

def dioBase {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (h : (Fin (a + b) → ℂ) → ℂ)
    (p : ScaleData) : Set (Fin (a + b) → ℝ) :=
  D ∩ realFreq h ⁻¹' twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ

def omegaSet {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (h : (Fin (a + b) → ℂ) → ℂ)
    (p : ScaleData) : Set (Fin (a + b) → ℝ) :=
  realFreq h '' D ∩ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ

/-- Source bound on a derivative and its row restrictions, using CLM operator norms.
The inverse is supplied as a map, with a two-sided inverse law at each point. -/
structure KamHyp {a b : ℕ} (D : Set (Fin (a + b) → ℝ)) (sbar : ℝ) (p : ScaleData)
    (h : (Fin (a + b) → ℂ) → ℂ) (f : CHam (a + b)) : Prop where
  a_pos : 1 ≤ a
  b_pos : 1 ≤ b
  τ_gt : ((a + b : ℕ) : ℝ) < p.τ
  positive : 0 < p.γ₂ ∧ 0 < p.s ∧ 0 < p.ρ ∧ 0 < p.E ∧
    0 < p.M ∧ 0 < p.Mhat ∧ 0 < p.Mbar ∧ 0 < p.Mbar₁ ∧ 0 < p.Mbar₂
  gamma_order : p.γ₂ ≤ p.γ₁
  widths : 4 * p.s ≤ sbar ∧ sbar < 1
  normalized : p.Mhat ≤ p.M ∧ p.Mbar₁ ≤ p.Mbar ∧ p.Mbar₂ ≤ p.Mbar
  L_bound : initialL p.M p.Mhat p.Mbar ≤ p.L
  holo : DifferentiableOn ℂ h (KAM.actionNbhd D p.ρ)
  real_h : RealOn (coefficientDom D p.ρ (sbar + p.s)) (fun z => h z.2)
  real_f : RealOn (coefficientDom D p.ρ (sbar + p.s)) f
  f_class : InClass (realBase D) p.ρ (geometricWidth (sbar + p.s)) f
  f_bound : WBound (realBase D) p.ρ (geometricWidth (sbar + p.s)) f p.E
  injective : Set.InjOn (freq h) (KAM.actionNbhd D p.ρ)
  hessian : ∀ I ∈ KAM.actionNbhd D p.ρ,
    ‖fderiv ℂ (freq h) I‖ ≤ p.M ∧
    (∀ v, ‖lastBlock (a := a) (fderiv ℂ (freq h) I v)‖ ≤ p.Mhat * ‖v‖) ∧
    ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
      (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ (freq h) I ∧
      ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ p.Mbar ∧
      (∀ v, ‖firstBlock (b := b) (A.symm v)‖ ≤ p.Mbar₁ * ‖v‖) ∧
      (∀ v, ‖lastBlock (a := a) (A.symm v)‖ ≤ p.Mbar₂ * ‖v‖)
  small : kamConstant (a + b) p.τ * eHat p < 1

/-- Correct normalization direction: lowering Mhat cannot increase Ehat when L is fixed. -/
theorem rem_norm (p : ScaleData) (hp : 0 < p.E ∧ 0 < p.M ∧ 0 < p.Mhat ∧ 0 < p.Mbar ∧
    0 < p.s ∧ 0 < p.γ₁ ∧ 0 < p.γ₂ ∧ 0 < p.ρ ∧ 0 < p.L ∧ 0 < p.τ) :
    let p' := {p with Mhat := min p.Mhat p.M}
    initialL p'.M p'.Mhat p'.Mbar = initialL p.M p.Mhat p.Mbar ∧
    cutoff p' = cutoff p ∧ rhoHat p ≤ rhoHat p' ∧ eHat p' ≤ eHat p := sorry

/-- Pure numerical invariant of the c=2pi period conversion. -/
theorem period_dictionary (p : ScaleData) :
    let c := 2 * π
    let p' := {p with
      E := p.E / c
      M := p.M / c
      Mhat := p.Mhat / c
      Mbar := c * p.Mbar
      Mbar₁ := c * p.Mbar₁
      Mbar₂ := c * p.Mbar₂
      L := c * p.L
      γ₁ := p.γ₁ / c
      γ₂ := p.γ₂ / c}
    constants p' = constants p := sorry


/-- Pure-angle period dictionary, no Cartesian oscillator coordinates. -/
theorem period_dictionary_field {n : ℕ} (H : CHam n) (z : CPhase n)
    (hH : DifferentiableAt ℂ H ((2 * π : ℂ) • z.1, z.2)) :
    let c : ℂ := 2 * π
    let Q := fun x : CPhase n => (c • x.1, x.2)
    fderiv ℂ Q z (KAM.hamiltonianVectorFieldℂ (fun x => H (Q x) / c) z) =
      KAM.hamiltonianVectorFieldℂ H (Q z) := sorry

/-- use5: the fast angle/action chart leaves Cartesian oscillators untouched. -/
def oscPeriodChart {n m : ℕ} (z : CPhase (n + m)) : CPhase (n + m) :=
  (Fin.append ((2 * π : ℂ) • firstBlock (b := m) z.1) (lastBlock (a := n) z.1),
    Fin.append ((2 * π : ℂ)⁻¹ • firstBlock (b := m) z.2) (lastBlock (a := n) z.2))

theorem use5 {n m : ℕ} (H : CHam (n + m)) (z : CPhase (n + m))
    (hH : DifferentiableAt ℂ H (oscPeriodChart z)) :
    (∀ u v, symplFormC (fderiv ℂ (oscPeriodChart (n := n) (m := m)) z u)
      (fderiv ℂ (oscPeriodChart (n := n) (m := m)) z v) = symplFormC u v) ∧
    fderiv ℂ (oscPeriodChart (n := n) (m := m)) z
      (KAM.hamiltonianVectorFieldℂ (H ∘ oscPeriodChart) z) =
        KAM.hamiltonianVectorFieldℂ H (oscPeriodChart z) := sorry


/-- Remaining scalar invariants of use5, with the Hamiltonian and oscillator size unchanged. -/
theorem use5_constants (αcp rcp sc ε₀ K E b : ℝ) :
    let c := 2 * π
    let α := αcp / c
    let r := c * rcp
    let s := sc / c
    2 * π * α = αcp ∧ min (r * s) (ε₀ ^ 2) = min (rcp * sc) (ε₀ ^ 2) ∧
    K * s / α = K * sc / αcp ∧
    (2 ^ 12 * b * K * E * s ≤ α * min (r * s) (ε₀ ^ 2) ↔
      2 ^ 12 * b * K * E * sc ≤ αcp * min (rcp * sc) (ε₀ ^ 2)) := sorry

/-- CP's coefficient functions are read at phi=2pi theta; normalizing the
Hamiltonian divides every coefficient and its norm bound by 2pi. -/
theorem period_dictionary_coeff {n : ℕ} {D : Set (Fin n → ℂ)} {r S E : ℝ}
    (H : CHam n) (hbound : WBound D r S (fun z => H ((2 * π : ℂ) • z.1, z.2)) E) :
    (∀ I k, coeff (fun z => H ((2 * π : ℂ) • z.1, z.2) / (2 * π : ℂ)) I k =
      coeff (fun z => H ((2 * π : ℂ) • z.1, z.2)) I k / (2 * π : ℂ)) ∧
    WBound D r S (fun z => H ((2 * π : ℂ) • z.1, z.2) / (2 * π : ℂ)) (E / (2 * π)) := sorry

/-- Row restrictions cannot exceed the full operator bound (also for inverse rows). -/
theorem rem_norm_blocks {a b : ℕ} (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) :
    (∀ v, ‖firstBlock (b := b) (A v)‖ ≤ ‖A‖ * ‖v‖) ∧
    (∀ v, ‖lastBlock (a := a) (A v)‖ ≤ ‖A‖ * ‖v‖) := sorry

/-- Multivariable global inverse on the open image; existence is proved, not assumed. -/
theorem ext_ift {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {F : (Fin n → ℂ) → (Fin n → ℂ)} (hF : DifferentiableOn ℂ F Ω) (hinj : Set.InjOn F Ω)
    (hD : ∀ x ∈ Ω, Function.Bijective (fderiv ℂ F x)) :
    IsOpen (F '' Ω) ∧ ∃ G : (Fin n → ℂ) → (Fin n → ℂ),
      DifferentiableOn ℂ G (F '' Ω) ∧ MapsTo G (F '' Ω) Ω ∧
      (∀ x ∈ Ω, G (F x) = x) ∧ (∀ y ∈ F '' Ω, F (G y) = y) ∧
      ∀ y ∈ F '' Ω, ∀ v, fderiv ℂ G y (fderiv ℂ F (G y) v) = v := sorry

theorem ext_neumann {n : ℕ} (B : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (hB : ‖B‖ ≤ 1 / 2) :
    ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = ContinuousLinearMap.id ℂ _ + B ∧
      ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ ≤ 2 := sorry

/-- Ball continuation includes positivity absent from the prose statement. -/
theorem ball {n : ℕ} {Ω : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin n → ℂ)}
    (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω) (hinj : Set.InjOn F Ω)
    {m δ : ℝ} (hm : 0 < m) (hδ : 0 < δ)
    (hder : ∀ x ∈ Ω, ∃ A : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ),
      (A : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = fderiv ℂ F x ∧
        ‖(A.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))‖ ≤ m)
    {x₀ : Fin n → ℂ} (hx : Metric.ball x₀ δ ⊆ Ω) :
    Metric.ball (F x₀) (δ / m) ⊆ F '' Metric.ball x₀ δ ∧
    ∀ x ∈ Metric.ball x₀ δ, ∀ y ∈ Metric.ball x₀ δ,
      F x ∈ Metric.ball (F x₀) (δ / m) → F y ∈ Metric.ball (F x₀) (δ / m) →
      ‖x - y‖ ≤ m * ‖F x - F y‖ := sorry

theorem lip_sup {N m : ℕ} {S : Set (Fin N → ℝ)} {r A : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    {Δ : (Fin N → ℂ) → (Fin m → ℂ)}
    (hΔ : DifferentiableOn ℂ Δ (KAM.actionNbhd S r)) (hbound : ∀ z ∈ KAM.actionNbhd S r, ‖Δ z‖ ≤ A) :
    ∀ x ∈ S, ∀ y ∈ S,
      ‖Δ (KAM.realInclusion N x) - Δ (KAM.realInclusion N y)‖ ≤ 4 * N * A / r * ‖x - y‖ := sorry

/-- P3 step: Ψ is retained on the large averaging domain; Ψ+ is its restriction,
represented by the SAME total function. All statements name their own domain. -/
theorem step {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
    (H : KamHyp D sbar p h f)
    (hD : ∀ I ∈ D, realFreq h I ∈ twoScaleDiophantine a b p.γ₁ p.γ₂ p.τ) :
    ∃ (Ψ : CPhase (a + b) → CPhase (a + b)) (g : (Fin (a + b) → ℂ) → ℂ)
      (fs : CHam (a + b)) (Dp : Set (Fin (a + b) → ℝ))
      (ihat : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      let hp := fun I => h I + g I
      let R := rhoHat p
      let V := coefficientDom D (R / 2) (sbar + p.s / 6)
      KamHyp Dp sbar (nextScale p) hp fs ∧
      Dp ⊆ realTube D (R / 16) ∧
      KAM.actionNbhd Dp (R / 16) ⊆ KAM.actionNbhd D (R / 8) ∧
      DifferentiableOn ℂ Ψ V ∧ Set.InjOn Ψ V ∧ MapsTo Ψ V (coefficientDom D R (sbar + p.s)) ∧
      (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v) ∧
      (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
        Ψ (z + ((fun i => (k i : ℂ)), 0)) = Ψ z + ((fun i => (k i : ℂ)), 0)) ∧
      (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
        Ψ (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
      DifferentiableOn ℂ g (KAM.actionNbhd D (R / 2)) ∧
      (∀ I ∈ KAM.actionNbhd D (R / 2), ‖g I‖ ≤ 5 / 4 * p.E) ∧
      (∀ z ∈ coefficientDom Dp (R / 16) (sbar + p.s / 12),
        h (Ψ z).2 + f (Ψ z) = hp z.2 + fs z) ∧
      Set.InjOn (freq hp) (KAM.actionNbhd D (R / 8)) ∧
      (∀ I ∈ KAM.actionNbhd D (R / 4),
        ‖fderiv ℂ (freq hp) I‖ ≤ 2 * p.M ∧
        (∀ v, ‖lastBlock (a := a) (fderiv ℂ (freq hp) I v)‖ ≤ 2 * p.Mhat * ‖v‖) ∧
        ∃ A : (Fin (a + b) → ℂ) ≃L[ℂ] (Fin (a + b) → ℂ),
          (A : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ)) = fderiv ℂ (freq hp) I ∧
          ‖(A.symm : (Fin (a + b) → ℂ) →L[ℂ] (Fin (a + b) → ℂ))‖ ≤ 2 * p.Mbar ∧
          (∀ v, ‖firstBlock (b := b) (A.symm v)‖ ≤ 2 * p.Mbar₁ * ‖v‖) ∧
          (∀ v, ‖lastBlock (a := a) (A.symm v)‖ ≤ 2 * p.Mbar₂ * ‖v‖)) ∧
      realFreq hp '' Dp = realFreq h '' D ∧
      DifferentiableOn ℂ ihat (KAM.actionNbhd D (R / 16)) ∧
      (∀ I ∈ KAM.actionNbhd D (R / 16),
        ihat I ∈ KAM.actionNbhd D (R / 8) ∧ freq hp (ihat I) = freq h I ∧
        ‖firstBlock (b := b) (ihat I - I)‖ ≤ 10 * (p.Mbar₁ / p.Mbar) * eHat p * R ∧
        ‖lastBlock (a := a) (ihat I - I)‖ ≤ 10 * (p.Mbar₂ / p.Mbar) * eHat p * R) ∧
      Dp = (fun I => fun j => (ihat (KAM.realInclusion (a + b) I) j).re) '' D ∧
      (∀ I ∈ D, ∀ J ∈ D,
        ‖(ihat (KAM.realInclusion (a + b) I) - KAM.realInclusion (a + b) I) -
          (ihat (KAM.realInclusion (a + b) J) - KAM.realInclusion (a + b) J)‖ ≤
            640 * (a + b) * eHat p * ‖I - J‖) ∧
      (∀ z ∈ V,
        ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤ 3 / 4 * (p.Mhat / p.M) * eHat p * R ∧
        ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 / 4 * eHat p * R ∧
        2 * π * ‖(Ψ z).1 - z.1‖ ≤ 3 / 4 * eHat p * p.s) ∧
      rhoHat (nextScale p) ≥ R / (2 * (24 : ℝ) ^ (p.τ + 1)) ∧
      cutoff (nextScale p) ≤ 24 * cutoff p ∧
      eHat (nextScale p) ≤ (8 / 9) * (4 * p.s) ^ (2 * (p.τ + 1)) * eHat p ^ 2 ∧
      eHat (nextScale p) < eHat p ^ 2 := sorry

/-- P3 iterative: common sequences are existentially quantified once, not chosen
by a default-valued function. Limits below remain local obligations on these witnesses. -/
theorem iterative {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧ hs 0 = h ∧ fs 0 = f ∧ Φ 0 = id ∧ is 0 = id ∧
      (∀ j, KamHyp (Ds j) sbar (seq p j) (hs j) (fs j)) ∧
      (∀ j, Φ (j + 1) = Φ j ∘ Ψ (j + 1)) ∧
      (∀ j, let pj := seq p j
        DifferentiableOn ℂ (is (j + 1)) (KAM.actionNbhd (Ds j) (rhoHat pj / 16)) ∧
        (∀ I ∈ KAM.actionNbhd (Ds j) (rhoHat pj / 16),
          freq (hs (j + 1)) (is (j + 1) I) = freq (hs j) I ∧
          ‖firstBlock (b := b) (is (j + 1) I - I)‖ ≤ 10 * (p.Mbar₁ / p.Mbar) * eHat pj * rhoHat pj ∧
          ‖lastBlock (a := a) (is (j + 1) I - I)‖ ≤ 10 * (p.Mbar₂ / p.Mbar) * eHat pj * rhoHat pj) ∧
        (∀ I ∈ Ds j, ∀ J ∈ Ds j,
          ‖(is (j + 1) (KAM.realInclusion (a + b) I) - KAM.realInclusion (a + b) I) -
            (is (j + 1) (KAM.realInclusion (a + b) J) - KAM.realInclusion (a + b) J)‖ ≤
              640 * (a + b) * eHat pj * ‖I - J‖) ∧
        Ds (j + 1) = (fun I => fun k => (is (j + 1) (KAM.realInclusion (a + b) I) k).re) '' Ds j) ∧
      (∀ j, let pj := seq p j
        let V := coefficientDom (Ds j) pj.ρ (sbar + pj.s)
        DifferentiableOn ℂ (Φ j) V ∧ Set.InjOn (Φ j) V ∧
        (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
          Φ j (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
        (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
          Φ j (z + ((fun i => (k i : ℂ)), 0)) = Φ j z + ((fun i => (k i : ℂ)), 0)) ∧
        MapsTo (Φ j) V (coefficientDom D p.ρ (sbar + p.s)) ∧
        (∀ z ∈ V, h (Φ j z).2 + f (Φ j z) = hs j z.2 + fs j z) ∧
        (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ (Φ j) z u) (fderiv ℂ (Φ j) z v) = symplFormC u v)) ∧
      (∀ j, Ds (j + 1) ⊆ realTube (Ds j) (rhoHat (seq p j) / 16) ∧
        realFreq (hs j) '' Ds j = realFreq h '' dioBase D h p ∧
        MapsTo (is (j + 1)) (realBase (Ds j)) (realBase (Ds (j + 1)))) ∧
      (∀ j, let pj := seq p j
        let V := coefficientDom (Ds (j + 1)) (rhoHat pj / 16) (sbar + pj.s / 12)
        DifferentiableOn ℂ (Ψ (j + 1)) V ∧
        (∀ x : Phase (a + b), KAM.realInclusion₂ (a + b) x ∈ V →
          Ψ (j + 1) (KAM.realInclusion₂ (a + b) x) ∈ range (KAM.realInclusion₂ (a + b))) ∧
        (∀ z ∈ V, ∀ k : Fin (a + b) → ℤ,
          Ψ (j + 1) (z + ((fun i => (k i : ℂ)), 0)) = Ψ (j + 1) z + ((fun i => (k i : ℂ)), 0)) ∧
        (∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ (Ψ (j + 1)) z u)
          (fderiv ℂ (Ψ (j + 1)) z v) = symplFormC u v) ∧
        MapsTo (Ψ (j + 1)) V (coefficientDom (Ds j) (rhoHat pj) (sbar + pj.s)) ∧
        (∀ z ∈ V,
          ‖firstBlock (b := b) ((Ψ (j + 1) z).2 - z.2)‖ ≤ 3 / 4 * (p.Mhat / p.M) * eHat pj * rhoHat pj ∧
          ‖lastBlock (a := a) ((Ψ (j + 1) z).2 - z.2)‖ ≤ 3 / 4 * eHat pj * rhoHat pj ∧
          2 * π * ‖(Ψ (j + 1) z).1 - z.1‖ ≤ 3 / 4 * eHat pj * pj.s)) ∧
      (∀ j, eHat (seq p (j + 1)) < eHat (seq p j) ^ 2 ∧
        rhoHat (seq p j) / (2 * (24 : ℝ) ^ (p.τ + 1)) ≤ rhoHat (seq p (j + 1)) ∧
        rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16 ∧
        cutoff (seq p j) ≤ 24 ^ j * cutoff p) := sorry

/-- Scalar sums package independent of a particular choice of KAM witnesses. -/
theorem sums {e R s : ℕ → ℝ} {c : ℝ}
    (he : ∀ j, 0 ≤ e j) (he₀ : e 0 < 1 / 2) (hquad : ∀ j, e (j + 1) ≤ e j ^ 2)
    (hc : 0 ≤ c) (hce : c * e 0 ≤ 1 / 2)
    (hR : ∀ j, 0 ≤ R j ∧ R (j + 1) ≤ R j / 16)
    (hs : ∀ j, s (j + 1) = s j / 12) :
    (∀ m k, m ≤ k → e k ≤ e m ^ (2 ^ (k - m))) ∧
    (∀ m, Summable (fun k => e (m + k)) ∧ ∑' k, e (m + k) ≤ 2 * e m) ∧
    Summable (fun k => c ^ k * e k) ∧ (∑' k, c ^ k * e k) ≤ 2 * e 0 ∧
    (∀ k, R k ≤ R 0 / 16 ^ k ∧ s k = s 0 / 12 ^ k) := sorry

/-- Rescaled norm is a function, never a global Pi/Prod instance. Angles first. -/
def limitmap_data {n : ℕ} (R s : ℝ) (z : Phase n) : ℝ := max (‖z.1‖ * (2 * π / s)) (‖z.2‖ / R)

/-- All derivatives means the full iterated Frechet derivative at each order. -/
theorem fourier_compact {n : ℕ} {w B : ℝ} (hw : 0 < w) (hB : 0 ≤ B)
    {F : ℕ → (Fin n → ℂ) → ℂ} {f : (Fin n → ℝ) → ℂ}
    (hhol : ∀ j, DifferentiableOn ℂ (F j) (KAM.complexStrip n w))
    (hper : ∀ j θ, θ ∈ KAM.complexStrip n w → ∀ k : Fin n → ℤ,
      F j (θ + fun i => (k i : ℂ)) = F j θ)
    (hb : ∀ j θ, θ ∈ KAM.complexStrip n w → ‖F j θ‖ ≤ B)
    (hconv : TendstoUniformly (fun j x => F j (KAM.realInclusion n x)) f Filter.atTop) :
    ∃ G : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ G (KAM.complexStrip n w) ∧
      (∀ x, G (KAM.realInclusion n x) = f x) ∧
      (∀ z ∈ KAM.complexStrip n w, ‖G z‖ ≤ B) ∧
      (∀ θ ∈ KAM.complexStrip n w, ∀ k : Fin n → ℤ, G (θ + fun i => (k i : ℂ)) = G θ) ∧
      ∀ v : ℝ, 0 < v → v < w → ∀ m : ℕ,
        TendstoUniformlyOn (fun j => iteratedFDeriv ℂ m (F j)) (iteratedFDeriv ℂ m G)
          Filter.atTop {z | ∀ i, |(z i).im| ≤ v} := sorry

/-- Explicit bridge for the inv-conj SOURCE_GAP. Source assumptions only. -/
theorem real_symplectic_conjugation {n : ℕ} {V : Set (CPhase n)} (hV : IsOpen V)
    {Ψ : CPhase n → CPhase n} {G : CHam n}
    (hΨ : DifferentiableOn ℂ Ψ V) (hG : DifferentiableOn ℂ G (Ψ '' V))
    (hsym : ∀ z ∈ V, ∀ u v, symplFormC (fderiv ℂ Ψ z u) (fderiv ℂ Ψ z v) = symplFormC u v)
    (hrealΨ : ∀ x : Phase n, KAM.realInclusion₂ n x ∈ V → Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hrealG : RealOn (Ψ '' V) G) :
    let Ψr := fun x : Phase n => KAM.realPartCLM₂ n (Ψ (KAM.realInclusion₂ n x))
    let Gr := fun x : Phase n => (G (KAM.realInclusion₂ n x)).re
    ∀ x : Phase n, KAM.realInclusion₂ n x ∈ V →
      KAM.hamiltonianVectorField Gr (Ψr x) = fderiv ℝ Ψr x (KAM.hamiltonianVectorField (Gr ∘ Ψr) x) := sorry

/-- Explicit bridge for inv-lim; local uniform convergence suffices for each finite interval. -/
theorem real_curve_limit {n : ℕ} {x : ℕ → ℝ → Phase n} {y v : ℝ → Phase n}
    (hx : ∀ j, Differentiable ℝ (x j))
    (hc : TendstoLocallyUniformly x y Filter.atTop)
    (hd : TendstoLocallyUniformly (fun j t => deriv (x j) t) v Filter.atTop)
    (hv : Continuous v) : ∀ t, HasDerivAt y (v t) t := sorry

/-- No bound on g_e off X is needed. The inverse is an actual equivalence. -/
theorem cover {N : ℕ} {X : Set (Fin N → ℝ)} {g : (Fin N → ℝ) → (Fin N → ℝ)} {lam η : ℝ}
    (hlam : 0 ≤ lam ∧ lam < 1) (hη : 0 ≤ η)
    (hlip : ∀ x ∈ X, ∀ y ∈ X, ‖g x - g y‖ ≤ lam * ‖x - y‖)
    (hbound : ∀ x ∈ X, ‖g x‖ ≤ η) :
    ∃ F : (Fin N → ℝ) ≃ (Fin N → ℝ),
      (∀ x ∈ X, F x = x + g x) ∧
      (∀ x y, (1 - lam) * ‖x - y‖ ≤ ‖F x - F y‖ ∧ ‖F x - F y‖ ≤ (1 + lam) * ‖x - y‖) ∧
      ∀ y ∈ X, ‖F.symm y - y‖ ≤ η / (1 - lam) := sorry

/-- Main joint construction, frozen phase order. No witness selection definition.
The source torus (v,theta+u) is represented as (theta+u,v), so this is the exact
unscaled input for P1 cyl_pipeline, with the same frequency. -/
theorem two_scale_kam {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f)
    (hL : p.L = initialL p.M p.Mhat p.Mbar) :
    ∃ (i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ))
      (Φ : Phase (a + b) → Phase (a + b))
      (K : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ) → Phase (a + b))
      (I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ))
      (KC : (Fin (a + b) → ℝ) → (Fin (a + b) → ℂ) → CPhase (a + b)),
      let D₀ := dioBase D h p
      let Ω := omegaSet D h p
      let Dstar := i '' D₀
      let r := 32 * eHat p * rhoHat p
      let Hr := fun z : Phase (a + b) => (h (KAM.realInclusion (a + b) z.2) + f (KAM.realInclusion₂ (a + b) z)).re
      let KO := ⋃ ω ∈ Ω, range (K ω)
      (∀ ω ∈ Ω, I₀ ω ∈ D₀ ∧ realFreq h (I₀ ω) = ω ∧ ∀ I ∈ D₀, realFreq h I = ω → I = I₀ ω) ∧
      (∀ I ∈ D₀,
        ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
        ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p) ∧
      (∀ I ∈ D₀, ∀ J ∈ D₀, ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ y ∈ (univ ×ˢ Dstar : Set (Phase (a + b))),
        limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
          768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y)) ∧
      (∀ x ∈ (univ ×ˢ Dstar : Set (Phase (a + b))), ∀ k : Fin (a + b) → ℤ,
        Φ (x + KAM.ODE.angleShift k) = Φ x + KAM.ODE.angleShift k) ∧
      (∀ ω ∈ Ω, ∀ θ, K ω θ = Φ (θ, i (I₀ ω))) ∧
      (∀ ω ∈ Ω,
        IsLatticeTorus KAM.ODE.angleShift Hr (univ ×ˢ realTube D r) ω (K ω) ∧
        DifferentiableOn ℂ (KC ω) (KAM.complexStrip (a + b) (geometricWidth sbar)) ∧
        (∀ θ, KC ω (KAM.realInclusion (a + b) θ) = KAM.realInclusion₂ (a + b) (K ω θ)) ∧
        (∀ θ ∈ KAM.complexStrip (a + b) (geometricWidth sbar),
          ‖(KC ω θ).1 - θ‖ ≤ 3 / (4 * π) * eHat p * p.s) ∧
        (∀ θ,
          ‖firstBlock (b := b) ((K ω θ).2 - I₀ ω)‖ ≤ 20 * (p.Mbar₁ / p.Mbar + p.Mhat / p.M) * eHat p * rhoHat p ∧
          ‖lastBlock (a := a) ((K ω θ).2 - I₀ ω)‖ ≤ 20 * (p.Mbar₂ / p.Mbar + 1) * eHat p * rhoHat p ∧
          ‖fderiv ℝ (fun θ => (K ω θ).1 - θ) θ‖ ≤ 3 / 4 * (a + b) * eHat p)) ∧
      (∀ ω ∈ Ω, ∀ ω' ∈ Ω, ∀ θ θ', ∀ k : Fin (a + b) → ℤ,
        K ω θ = K ω' θ' + KAM.ODE.angleShift k → ω = ω' ∧ θ = θ' + fun j => (k j : ℝ)) ∧
      (∀ ω ∈ Ω, ∀ ω' ∈ Ω, ‖ω - ω'‖ < p.ρ / p.Mbar → ‖I₀ ω - I₀ ω'‖ ≤ p.Mbar * ‖ω - ω'‖) ∧
      (Bornology.IsBounded D → ∀ ω ∈ Ω, ∀ ω' ∈ Ω,
        ‖I₀ ω - I₀ ω'‖ ≤ p.Mbar * max 1 (Metric.diam D / p.ρ) * ‖ω - ω'‖) ∧
      volume (((univ ×ˢ realTube D r) \ KO) ∩ {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico 0 1}) ≤
        ENNReal.ofReal (complementConstant (a + b)) *
          (volume (D \ D₀) + volume (realTube D r \ D)) := sorry

#print axioms nfb
#print axioms osc_averaging
#print axioms step
#print axioms iterative
#print axioms two_scale_kam

end KAM.Planetary
```
