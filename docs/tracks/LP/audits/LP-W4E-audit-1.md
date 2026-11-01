# LP-W4E independent package audit 1

Audited HEAD `7ef177a6a6faf0ca096bf69e9c2d776a595a0165`, 2026-11-01. Nothing in LP is frozen. This is a bounded statement, definition, and assembly audit, not owner approval or a re-audit of the upstream analytic engine.

Read: repository AGENTS/PLAN/DECISIONS; `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`; W4E handoff and component handoffs; `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W4E.md` and component SAFE/SRC/SRCB2 briefs; SPEC; MAIN §1, L14, L16, L18, T19 and normative AMENDMENTS; statement reviews 4 and 5.

Scope note S1: both requested three-dot comparisons (`git diff inp...HEAD`, `git diff inp-lp...HEAD -- KAM`) warn `multiple merge bases, using dd8a51fd693c87682fccf47ba665d2be751e4975` and include upstream W4D files. The endpoint comparison `git diff inp-lp HEAD -- KAM` agrees with `git diff inp-lp-w4d HEAD -- KAM`: 10 files, 1462 insertions, 1 deletion. The handoff's “9 files” description omits the Algebra docstring change discussed below. The reviewed executable additions are the eight SourceCarrier/SpatialSafety modules (1453 lines); the other changes are eight generated root imports and one docstring line. Earlier DOM/LIFT/NRR code was consulted only at the direct interfaces used here. `git diff inp-lp HEAD -- KAM/Frozen manifest KAM.lean README.md` and the corresponding three-dot protected-path comparison are empty. `KAM/Root/Planetary.lean` is the declared generated-root exception; I did not edit it.

## LP-SP-SAFE (LP2)

**PASS WITH NOTES** for `lp2_spatial_strongAMD_safety`, `_normalized`, and `_halfInteger`. No blocking mathematical or statement-fidelity finding in this scope.

The MAIN §1 data and hypotheses (6) are preserved: `n ≥ 2`, positive masses, compact ordered positive axes, positive δ and γ, τ > n−1, negative initial energy and nonzero star distances, initial axes in A, all nonzero integer Diophantine modes with the ℓ¹ mode size, and the strong-AMD margin. The general theorem drops only MAIN's mass normalization and is strictly stronger; `_normalized` restores it without using it. The dependent `hch` is threshold typing data, not an extra dynamical restriction: orbital positivity gives positive actions, and `actionAxis_spatialActionVector` identifies their axis ordering with the assumed axes in A. The canonical energy is ν times MAIN's specific energy, so positivity of ν makes its sign equivalent. No prograde, inclination, alignment, nonzero-L, normal-form, secular-confinement, or stopped-drift premise occurs in LP2.

All nine positive constants, including Aelem, and both N10 inequalities precede μ and z₀. Aligned assembly uses the same compact shared tube U for the budget and physical barrier, chooses r = √μ ≤ min(r1, rg), and proves the N6 improvement r/2 with D₀=1. Choosing minima of the geometric and osculating gaps preserves both gap families; μ₀ is also decreased for each N10 gap. Empty A or empty admissible level is allowed: no witness initial point is assumed in the constant construction.

The direct edge is checked: `SpatialStoppedOn` unfolds to exactly CONF's strict antecedent on `uIcc 0 t`; `spatialChartLift_premises_nrr` constructs the chart and supplies the same block, real-domain membership, initial fast actions, and whole slow ball as NRR requires. Its ball identity uses addition of the two n-component quadratic sums, not a restriction to an aligned slow subset. The Hamilton fields agree on the open chart-safe domain via `spLiftChartHam_field_eq` and the NRR Hamiltonian's definitional equality to the pulled Hamiltonian. The NRR exponent `scaleExponent τ` is the displayed exponent definitionally. Both time signs use `uIcc`, including t=0. The stopped bound is proved locally in Aligned, then passed to CONF; it is never assumed in LP2. This follows amendment N7's L13 route rather than treating L12 and L13 as simultaneous suppliers.

Main derives L ≠ 0 from C < B⋆ and the orbital bound; it constructs one proper orthogonal rotation for each initial state after constants have been fixed. Orientation transports all thirteen state clauses, including the norm of the osculating-minus-canonical eccentricity vector. `SpatialSafeSol.of_rotate` rotates arbitrary competing solutions forward, applies uniqueness, and rotates the equality back, so uniqueness is not restricted to already-rotated competitors. Circular and coplanar cases acquire no exclusion. The final inverse rotation preserves physical lengths and action norms.

The conclusion supplies the physical-time exponential interval (7), both drifts and AMD drift/margin (8), canonical annulus and actual-distance bounds (9), the L16 element estimate and osculating half-gaps, and Newtonian reconstruction with `(1, μν)` masses. The canonical strict eccentricity bound follows from positive a and positive canonical perihelion; it need not be an independent conjunct. Source's maximal-solution wording is represented by existence on the closed certified interval and agreement with every local solution on overlap; the underlying CONF edge uses the maximal ODE solution. The half-integer corollary proves the algebraic exponent identity 1/(2n+1).

The following table covers every new SAFE declaration. Names have namespace prefix `KAM.Planetary.Spatial.`; file paths are relative to the repository.

| Node / location | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `KAM/Planetary/Spatial/SpatialSafety/Aligned.lean:46` | `spatial_safety_of_aligned` | PASS | Distinct aligned helper; alignment discharged by Main, stopped drift proved. |
| `KAM/Planetary/Spatial/SpatialSafety/Bridge.lean:42` | `spLiftSecularBall_eq_spatialSecularBall` | PASS | Equal whole (47) balls by sum algebra on the full carrier. |
| `KAM/Planetary/Spatial/SpatialSafety/Bridge.lean:51` | `spatialStoppedBlock_eq_lpBlockNM` | PASS | Equal blocks for all r,w, not only positive widths. |
| `KAM/Planetary/Spatial/SpatialSafety/Bridge.lean:56` | `spLiftChartSafe_eq_spatialChartSafe` | PASS | Definitional equality of safe sets. |
| `KAM/Planetary/Spatial/SpatialSafety/Bridge.lean:60` | `lpChartHamNM_eq_spatialPulledHam` | PASS | Definitional equality of Hamiltonians. |
| `KAM/Planetary/Spatial/SpatialSafety/Bridge.lean:71` | `SpatialLiftData.spatialChartLift_premises_nrr` | PASS | LIFT-to-NRR interface; assumptions are source/typing data bundled in SpatialLiftData. |
| `KAM/Planetary/Spatial/SpatialSafety/Constants.lean:38` | `exists_spatialBudget_radius` | PASS | MAIN (39), uniform modulus continuity; compact U may be empty. |
| `KAM/Planetary/Spatial/SpatialSafety/Constants.lean:58` | `spatialKeplerAxis_eq_action_sq` | PASS | Orbital identity on negative-energy carrier; ν nonzero follows from carrier. |
| `KAM/Planetary/Spatial/SpatialSafety/Constants.lean:67` | `spatial_norm_axis_sub_le` | PASS | Action-to-axis estimate using Pi max norm and a uniform action bound; n=0 is vacuous. |
| `KAM/Planetary/Spatial/SpatialSafety/Constants.lean:98` | `mem_strongLSet_spatialActionVector` | PASS | Definitional image membership; no physical premise needed. |
| `KAM/Planetary/Spatial/SpatialSafety/Main.lean:43` | `lp2_spatial_strongAMD_safety` | PASS | T19 plus L16 and L1; stronger without mass normalization. |
| `KAM/Planetary/Spatial/SpatialSafety/Main.lean:153` | `lp2_spatial_strongAMD_safety_normalized` | PASS | Exact intended normalized LP2. |
| `KAM/Planetary/Spatial/SpatialSafety/Main.lean:210` | `lp2_spatial_strongAMD_safety_halfInteger` | PASS | τ=n−1/2; exponent exactly 1/(2n+1). |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:48` | `spaceLength_bodyVector3_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:52` | `spaceLength_bodyVector3_rotate_sub` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:60` | `spatialOscVelocity_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:68` | `spatialOscEnergy_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:73` | `spatialOscAxis_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:78` | `spatialOscEccVector_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:86` | `spatialOscEcc_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:91` | `spatialOscPeri_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:96` | `spatialOscApo_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:101` | `spatialKeplerPeri_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:106` | `spatialKeplerApo_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:113` | `spaceLength_oscEccVector_sub_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:121` | `spatialActionVector_rotate` | PASS | Direct orthogonal invariance/equivariance; no ellipticity or orientation restriction added. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:131` | `SpatialSafeState` | PASS | Exposed Prop conjunction of all thirteen per-time clauses; no fallback. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:161` | `SpatialSafeSol` | PASS | Exposed Prop for initial value, ODE, uniqueness, and per-time state. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:169` | `SpatialSafeState.of_rotate` | PASS | Transport helper with explicit input state assertion, not a supplier assumed in LP2. |
| `KAM/Planetary/Spatial/SpatialSafety/Orientation.lean:196` | `SpatialSafeSol.of_rotate` | PASS | Inverse rotation transports state, ODE and arbitrary local uniqueness competitors. |

Definitions: `SpatialSafeState` and `SpatialSafeSol` are literal exposed propositions on their entire declared carriers. They add no hidden assumption and choose no default value. For nonpositive parameters they simply assert their written conjunctions; LP2 supplies positive constants and μ,T. Assuming a rotated safety assertion in a transport theorem is an ordinary transport premise, not a conclusion-shaped hypothesis in the source theorem. There are no new bundled structures or instances. The facade has no declarations and reexports the intended modules.

## LP-SP-SRC (part A and part B as amended by SRCB2)

**PASS** for both carrier aliases, all source definitions and characterizations, and both restatement theorems. No remaining R4.1 statement blocker.

`SpatialSourceCanonicalPhase n ν` is exactly `SpatialElliptic ν`, whose underlying predicate is `SpatialNegativeEnergy ν`: positive masses, positive star distance, negative energy. It permits radial states with e=1 and does not demand nonzero individual or total angular momentum. For example ν=1, q=(1,0,0), p=0 has energy −1, a=1/2, e=1 and lies on this carrier. This is why the exported eccentricity bound is correctly non-strict. Circular states are also included. The carrier does not itself assert pairwise noncollision: individual Kepler elements are meaningful there; the safety theorem separately proves pairwise separation. At n=0 the canonical constraints and finite sums are vacuous and C=0; this is coherent, while the theorem requires n≥2. No signed-orientation or chart subdomain is substituted.

`SpatialSourceOsculatingPhase` is exactly the existing `SpatialOscPhase`, including positive masses, μ>0, nonzero star distances, negative osculating energies and eosc<1. The last condition is source-valid nondegenerate ellipse typing, not a hypothesis smuggled into LP2: the restatements construct ho from LP2's conclusions. The source k is 1+μν>0. The reused peri/apo and all eight osculating definitions retain their original carrier; no duplicate definitions were introduced.

Every new source function is a thin restriction: axis, action, eccentricity vector/norm, individual/total angular momentum and strong AMD. In particular C is exactly ΣΛ−|L|, not a positive part or signed projection. Every defining equation is rfl. Canonical positivity, Λ²=ν²a, eccentricity identity and e≤1, momentum formula, radial bounds, C≥0 and ΣΛD(e)≤C are the intended semantic unit. Reused osculating ellipse identities give positivity and radial bounds.

Independent text extraction gives byte equality between review 4 lines 335–415 and the normalized Source theorem type after removing only the declaration terminator. The general variant differs only in the declaration name and absence of hνmax/hνle. Neither type contains unrestricted `spatialKeplerAxis`, `spatialKeplerAction` or `spatialKeplerEccVector`. The initial h₀ is redundant typing derived from hν and the preceding physical premise; hch depends on h₀. At each time the single ∃hs scopes hcht, threshold, and every canonical clause, and ∃ho scopes the osculating clauses. Proof irrelevance prevents these proofs from choosing different quantities. The proofs derive hs and ho from the existing LP2 conclusions and reuse every clause by definitional unfolding. Raw energy/eccentricity sign tests occur inside the typing predicates, consistently with R5.1; they are not unrestricted physical-element outputs.

The following table covers every new SRC declaration, with the same namespace convention.

| Node / location | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `KAM/Planetary/Spatial/SourceCarrier.lean:50` | `SpatialSourceCanonicalPhase` | PASS | Exact alias of the intended source subtype; no extra restriction. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:53` | `SpatialSourceOsculatingPhase` | PASS | Exact alias of the intended source subtype; no extra restriction. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:57` | `spatialSourceCanonicalPhase_property` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:62` | `spatialSourceOsculatingPhase_property` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:71` | `spatialSourceKeplerAxis` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:75` | `spatialSourceKeplerAction` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:79` | `spatialSourceKeplerEccVector` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:83` | `spatialSourceKeplerEcc` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:87` | `spatialSourcePlanetAngularMomentum` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:91` | `spatialSourceAngularMomentum` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:95` | `spatialSourceStrongAMD` | PASS | Exposed thin source restriction; physical on every member of the carrier. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:100` | `spatialSourceKeplerAxis_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:103` | `spatialSourceKeplerAction_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:107` | `spatialSourceKeplerEccVector_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:115` | `spatialSourceKeplerEcc_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:119` | `spatialSourcePlanetAngularMomentum_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:124` | `spatialSourceAngularMomentum_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:127` | `spatialSourceStrongAMD_def` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:132` | `spatialSourceStrongAMD_eq_on` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:137` | `spatialSourceKeplerPeri_eq_source` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:144` | `spatialSourceKeplerApo_eq_source` | PASS | Defining characterization by rfl; no replacement object. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:152` | `spatialSourceKeplerAxis_pos` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:157` | `spatialSourceKeplerAction_pos` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:162` | `spatialSourceKeplerAction_sq` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:167` | `spatialSourceKeplerEcc_sq` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:175` | `spatialSourceKeplerEcc_nonneg` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:180` | `spatialSourceKeplerEcc_le_one` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:185` | `spatialSourcePlanetAngularMomentum_length` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:192` | `spatialSourcePlanetAngularMomentum_length_le` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:198` | `spatialSourceKeplerPeri_le_length` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:203` | `spatialSourceKeplerApo_ge_length` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:208` | `spatialSourceStrongAMD_nonneg` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:213` | `spatialSourceAction_mul_eccDeficit_le` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:222` | `spatialSourceOscParam_pos` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:229` | `spatialSourceOscEnergy_neg` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:234` | `spatialSourceOscEcc_lt_one` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:239` | `spatialSourceOscEcc_nonneg` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:244` | `spatialSourceOscAxis_pos` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:249` | `spatialSourceOscPeri_pos` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:254` | `spatialSourceOscPeri_le_length` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SourceCarrier.lean:260` | `spatialSourceOscApo_ge_length` | PASS | Carrier characterization from orbital identities, L3 or L16; no extra analytic premise. |
| `KAM/Planetary/Spatial/SpatialSafety/Source.lean:42` | `lp2_spatial_strongAMD_safety_source_general` | PASS | Exact R4.1(A) restatement except name and omitted normalization binders. |
| `KAM/Planetary/Spatial/SpatialSafety/Source.lean:145` | `lp2_spatial_strongAMD_safety_source` | PASS | Exact R4.1(A) type; all physical elements use source restrictions. |

## Combined verdict and notes

**LP-W4E: PASS WITH NOTES**, for the bounded package and exact non-frozen statements. This is not a freeze or seal authorization; final owner choices remain outside this audit. No conclusion-shaped source-theorem hypotheses, missing SAFE/SRC conclusion, carrier substitution, or mathematical source defect was found.

- **N1 — introduced documentation error, nonblocking for the proofs.** `KAM/Planetary/Spatial/AnalyticDomain/Bounds/Algebra.lean:22` now advertises “Re (w · w) ≥ |u|² − (2ε² + 4Qε)”. The actual unchanged theorem `re_cDot3_ge` at lines 58–62 proves subtraction of `3ε(ε+2Q)` instead. The new summary inequality is false: take u=(10,10,10), w=(9,9,9), ε=1, Q=10. All coordinate hypotheses hold, but the advertised bound says 258≤243. Restore the summary to the proved estimate. This one-line change is also absent from the W4E handoff's file enumeration. It is a Lean documentation defect, not an erratum in MAIN and not a new theorem failure.
- **N2 — confirmed R4.6 carry-overs outside the bounded executable additions.** `Elements.lean:35` says “Osculating semimajor axis” for the canonical `spatialKeplerAxis`; `Model.lean:21` says “full action domain” for the physical collision-guarded Hamiltonian phase domain (the continuation line also follows a frozen planar pattern although this spatial definition is non-frozen). Correct those descriptions before freeze. SourceCarrier's physical-quantity claim is now accurate for the SRCB2 surface.
- **N3 — confirmed R4.2 / R5.1 preparation notes.** The final anchor name under OD-11(b) is still an owner choice. Proposal wording must describe raw canonical energy and osculating energy/eccentricity tests as sign guards inside carrier predicates; the exact theorem types already do so. These notes do not weaken LP2 or SRCB2.
- Deviations retained and acceptable: generated root imports; duplicate spatial budget proof; exposed safety conjunction helpers; explicit LIFT/NRR naming bridge. General mass premises are stronger than the normalized source statement. No new design signal, MAIN erratum, hypothesis repair, or third proof route was introduced by this audit.

## Verification evidence

All commands were serial. The mandated lint/build wrappers apply `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1` to their commands; no additional Lean process was started while lint/build was running. The explicit axiom invocation used that same prefix. No heartbeat, recursion-depth, or synthesis-budget override was used.

1. Exact lint command:

   ```sh
   /root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w4e
   ```

   Exit 0; complete emitted output:

   ```text
   check_lean_modules: PASS (3777 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   The application's hash-only exception is exactly the lint output; this audit did not build any application.

2. Exact targeted build command (the wrapper takes the compile gate and invokes one capped `lake build <Module>` at a time):

   ```sh
   /root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-w4e KAM.Planetary.Spatial.SpatialSafety.Source KAM.Planetary.Spatial.SpatialSafety
   ```

   Exit 0. Completion output, in target order:

   ```text
   [lp_build] slot 1: KAM.Planetary.Spatial.SpatialSafety.Source (08:33:10)
   Build completed successfully (9365 jobs).
   [lp_build] slot 1: KAM.Planetary.Spatial.SpatialSafety (08:33:23)
   Build completed successfully (9364 jobs).
   ```

   Lake also replayed existing dependency warnings (unused variables/section variables/simp arguments, tactic lint, and deprecated `dif_pos`); no new package-module warning or build error was emitted. These job counts include cached dependencies, not a library rebuild from scratch. The Source target imports SourceCarrier and Main; Main imports the complete assembly. The facade target checks the public SAFE import path as well.

3. Exact independent axiom command:

   ```sh
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW4EAudit.lean > .lake/abi-scratch/LPW4EAudit-axioms.log 2>&1
   ```

   Exit 0. Probe imports `KAM.Planetary.Spatial.SpatialSafety.Source` and `KAM.Planetary.Spatial.SpatialSafety`, then issues `#print axioms` for each of the 62 theorem names in the tables. Parsed output names equal the enumerated theorem set; every axiom set is exactly `[propext, Classical.choice, Quot.sound]`. Complete output:

   ```text
   'KAM.Planetary.Spatial.spatialSourceCanonicalPhase_property' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOsculatingPhase_property' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerAxis_def' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerAction_def' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerEccVector_def' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerEcc_def' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_def' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceAngularMomentum_def' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceStrongAMD_def' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceStrongAMD_eq_on' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerPeri_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerApo_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerAction_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerAction_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscParam_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscEnergy_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscAxis_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscPeri_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscPeri_le_length' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialSourceOscApo_ge_length' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatial_safety_of_aligned' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spLiftSecularBall_eq_spatialSecularBall' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.spatialStoppedBlock_eq_lpBlockNM' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spLiftChartSafe_eq_spatialChartSafe' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.lpChartHamNM_eq_spatialPulledHam' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.SpatialLiftData.spatialChartLift_premises_nrr' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.exists_spatialBudget_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialKeplerAxis_eq_action_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatial_norm_axis_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.mem_strongLSet_spatialActionVector' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_normalized' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_halfInteger' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.spaceLength_bodyVector3_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spaceLength_bodyVector3_rotate_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscVelocity_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscEnergy_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscAxis_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscEccVector_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscEcc_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscPeri_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialOscApo_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialKeplerPeri_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialKeplerApo_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spaceLength_oscEccVector_sub_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.spatialActionVector_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.SpatialSafeState.of_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.SpatialSafeSol.of_rotate' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source_general' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'KAM.Planetary.Spatial.lp2_spatial_strongAMD_safety_source' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Kernel replay and short-name checks: **not rerun**. The user expressly states that the launcher already ran them and authorizes avoiding a repeat. Their hidden pane output was not available to this auditor, so no independently observed leanchecker command or exit code is claimed here. The builds above are targeted Lake build checks, not a substitute claim of a new independent leanchecker replay. No frozen/provider type or seal-body comparison applies: these are ordinary non-frozen LP theorems.

5. Static checks on the eight new modules: 73 declarations = 62 theorems, 7 source function definitions, 2 carrier aliases, 2 safety proposition definitions. Literal searches found zero occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `EuclideanSpace`, provider imports or direct frozen imports. Every file has copyright, `module`, public imports, module documentation, and public section; definitions are exposed through the section attribute. File lengths: SourceCarrier 267; facade 28; Aligned 208; Bridge 97; Constants 105; Main 278; Orientation 222; Source 248. All are below 1500. The additional Algebra edit changes only a comment, and root changes are imports only. Source review-text equality and unrestricted-element-name checks returned `True`, `True`, `[]`, `[]` for normalized equality, general-variant equality, and the two occurrence lists, respectively.

Only this report was written in tracked repository paths. The axiom probe and its enumeration/output files were deleted from `.lake/abi-scratch/` after incorporating the evidence. No source fix, root regeneration, state-changing git command, or memory update was performed. Remaining uncertainty is limited to the stated upstream audit boundary, uninspected launcher replay/name-check output, and the owner/documentation notes above.

