# Independent LP-W4B audit 1

Auditor: maud-lp-w4b-1. Date: 2026-11-01. Independent, refute-first, report-only audit; no delegation.

## Scope and controlling inputs

Audited HEAD `9faeaaee27e5408b1eae9be7e95108ba86f74e9b`; `inp` = `d2802dae2400f4fe1ba9c03263ad59d9ada87cf9`; `inp-lp` = `13a98df759d86f40601ef5dbdc7cc2dfa4fa0d9a`.
Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md and `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`. Compared both `git diff inp...HEAD` and the controlling package scope `git diff inp-lp...HEAD -- KAM`: 12 new implementation modules and 12 generated root imports. MAIN.md as amended by AMENDMENTS.md, SPEC.md, the combined handoff, six component briefs and their handoffs control statement review. Nothing in this LP package is frozen; provider/seal equality tests are inapplicable.

**Input note N1:** `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W4B.md` does not exist. The combined handoff explicitly identifies LP-SRC and LP-SP-{GEO,OSC,CONF,TUBE,ADAPT}; their existing briefs at that directory supply the bounded intended statements. This report certifies that concrete scope, not an unavailable umbrella brief.

## LP-SRC — PASS WITH NOTES

Read review 1 F4, FREEZE-PROPOSAL §3b, source carrier implementation and both restatement proofs. `SourceCanonicalPhase` and `SourceOsculatingPhase` have exactly the specified predicates, including positive masses, positive μ for actual ellipses, nonzero positions, negative energy and strict osculating eccentricity < 1. Every source definition is literally its total helper restricted to that subtype; all defining equations are rfl. `sourceOscParam` correctly ignores the phase: its value is 1 + μν_i.

The canonical carrier allows radial negative-energy states (e = 1); the exported canonical conclusion correctly says e ≤ 1 and does not assert positive canonical perihelion on that whole carrier. The osculating carrier excludes radial degeneracy and proves positive axis/perihelion and incidence. Circular states are included. For n = 0 planetwise claims are vacuous and C = 0; neither carrier invents a planet or a minimizer.

The normalized source theorem preserves all constants before μ and z₀, the original Diophantine condition, physical-time exponent, uniqueness/Newtonian outputs, AMD margin and drift, both endpoint estimates, F2 summed element error and ellipse validity, and both half-gaps with N10. The added universal h₀ is derivable as ⟨hν,hphys⟩; it is typing evidence, not an analytical restriction. Existential subtype proofs at later times are built from the original theorem's outputs. Proof irrelevance prevents dependence on their choice.

**Note N2 (proof-route wording):** the brief says “proved from ..._normalized”. The implementation instead proves the general source theorem from `lp1_planar_strongAMD_safety`, then adds the two unused normalization binders as a wrapper. The old normalized theorem is itself the corresponding wrapper around that same general theorem. This is a stronger base statement with the same normalized specialization, not a missing supplier or changed hypothesis.

## LP-SP-GEO — PASS

Geometry and Continuation faithfully transcribe MAIN L5–L6, N2 and N11 to Phase (n*3). Physical lengths use `spaceLength`, whereas action displacement uses the Pi sup norm. The threshold/modulus and abstract `DeficitBarrier` remain dimension-free. G2 chooses positive constants before the state, exports perihelia, adjacent/all-pairs separation, bounded positions/momenta, uniformly negative total energies, and L ≠ 0 with m ≤ L_i · spatialUnit L. The nonzero vector follows from `proj_margin` at index 0, justified by n ≥ 2; no alignment or prograde hypothesis is added.

G3 constructs a closed bounded set of separated configurations and bounded momenta, contained in the collision-free domain. This particular K need not consist entirely of negative-energy states; the separate uniform energy estimate on barrier states supplies that margin. The brief asks for compact containment in the collision-free domain, which is exactly proved. N11 obtains the positive perihelion floor before bounding momenta.

M3 derives (17) from conservation and the shared modulus, without assuming negative energy along the entire interval (a harmless strengthening of the physical formulation). M4 is explicitly conditional on a barrier tail, with a genuine maximal solution of the C¹ field on the open nonsingular domain. Its tube corollary retains ellipticity along that tail. Empty U/barrier sets are allowed; no nonemptiness premise or arbitrary physical witness is inserted.

## LP-SP-OSC — PASS WITH NOTES

All four modules translate L16 to Fin 3 using Euclidean dot/cross products and lengths. Literal actual velocity is p_i/ν_i + μ Σp_j, and the gravitational parameter is 1 + μν_i. The entire eccentricity numerator is divided by that parameter. Canonical comparison uses parameter one and velocity p_i/ν_i, not the canonical momentum as velocity. `spatialKeplerEnergy_eq_spec` proves the total/specific energy bridge; `SpatialOscEstimate` correctly exports E_osc ≤ -(c/ν_i)/2, not -c/2.

The uniform theorem chooses constants before μ, z and i. It works for arbitrary fixed positive masses by using finite positive lower/upper mass bounds (M ≥ 1), scaling the small perturbation parameter to Mμ. Thus it does not silently assume ν_i ≤ 1. Its geometric hypotheses are the source safe-compact-set data, subsequently derived for barrier states, not the desired osculating estimates assumed as inputs. F2 is explicitly paid by the summed axis/eccentricity-vector bound, negative energy, positive axis, strict e_osc < 1, incidence, both endpoint errors and N10 half-gaps. These arguments use the norm difference inequality at circular states and do not differentiate the norm at zero.

`SpatialOscPhase` and all ten source restrictions/defining equations follow OD-11 (b). `spatialOscPhase_ellipse` proves positive axis/perihelion and incidence; `spatialOscPhase_of_estimates` derives subtype membership from the already proved validity. The latter is a distinctly named packaging lemma; its estimate premise is not substituted for the supplier theorem. Canonical `SpatialElliptic` still permits radial e = 1, so its source perihelion is only a formula/radial endpoint there. Negative-energy radial actual states can occur in the total helper but are excluded by the osculating carrier's strict eccentricity bound.

**Note N3 (documentation only):** `KAM/Planetary/Spatial/Osculating.lean:264`, docstring immediately before `spatial_osculating_barrier`, says “MAIN Lemma 16 with N10, planar”. The theorem is spatial (Phase (n*3), bodyVector3, spaceLength); change that word to “spatial”. The Basic/Estimates tangency names denote radial incidence and axis positivity. Full geometric two-body tangency is represented here by the literal actual velocity and invariants, not a separately exported Kepler-trajectory construction; this agrees with the explicitly enumerated brief.

## LP-SP-CONF — PASS

The new tube is exactly negative energy, drift < r and AMD < B - δ/2; the core uses drift ≤ r/2 and AMD ≤ B - 3δ/4. This preserves MAIN (40) and N6. The closed-core lemma is relative sequential closedness at limits with positive star distances, as its signature and docstring state; it is not an unconditional IsClosed claim. Uniform energy ≤ -c recovers strict negative energy at such a limit. The first-exit proof obtains those positive distances from collision-free solutionhood, not from its desired conclusion.

The main helper retains the exact strict, segmentwise hstop from the component brief. That premise is intentionally the external stopped-drift supplier for this distinct conditional theorem; it does not claim to prove L13 or spatial T19. It quantifies arbitrary connected solution intervals containing zero and assumes neither global existence nor unrestricted drift. The proof constructs the maximal solution, applies hstop only in the strict tube, improves the margin via (17) and modulus monotonicity, runs both first exits, excludes finite maximal endpoints using the compact barrier, and proves overlap uniqueness. No extra angular alignment, eccentricity or separation premise is inserted. The spatial headline must still discharge hstop; it is outside this package.

## LP-SP-TUBE — PASS

`tubeNM` is track P's tube theorem with Phase (n+n) replaced by Phase (n+m). Its assumptions are exactly openness, compact containment, fast-lattice domain periodicity and real analyticity/periodicity of f. The proof reuses generic local complexification and gluing, covers the compact set, then translates branches by the fast lattice. Both periodic orbit set and complex tube agree definitionally with the old objects at m = n. Openness, radius monotonicity and lattice invariance have the advertised statements.

For empty K the orbit set/tube are empty, so the positive-width assertion is legitimately vacuous; for r ≤ 0 the literal tube is empty. Zero fast/slow dimensions cause only empty coordinate families. No nonempty-K premise, selected physical state, or fake positive-radius tube is introduced.

## LP-SP-ADAPT — PASS WITH NOTES

The generic layout is (θ,(I,q,p)) = (fast w.1/(2π), (fast w.2, slow w.1/ℓ, slow w.2/ℓ)). The inverse uses engine indices natAdd n (castAdd m i) for q and natAdd n (natAdd m i) for p; both land in physical slow index natAdd n i. Basis computations and the field proof split n, m, m explicitly, so they do not depend on m = n. In particular q-dot uses the p derivative with positive sign, and p-dot uses the q derivative with negative sign. The transformed Hamiltonian is G∘unrescale/(2π), and coefficient 2π/ℓ² yields the original physical time. All three planar-agreement lemmas are rfl.

The real indicator Hamiltonian is identified only on the open real domain by equality of germs. Orbit conversion assumes an actual G-orbit plus differentiability, the trace identity and real-domain membership. The conditional composition passes ExtNFHyp, its explicit smallness, centre, time and stopped slow-membership premises to the existing engine nonresonant theorem; it does not assume fast drift. These are explicit analytic/typing inputs to a distinctly named conditional adapter, not a declaration of completed spatial L13 or chart/domain construction.

**Note N4 (whole-carrier interpretation):** the bare maps are total linear formulas even at ℓ = 0, where Lean division sends the slow coordinates to zero and the maps are not inverses. Every inverse/equivalence and field conversion needing invertibility has ℓ ≠ 0. The engine composition derives positive ℓ from the ExtNFHyp positive width/radius data. Negative nonzero ℓ also satisfies the algebraic equivalence/field identity, a harmless strengthening. Empty n/m blocks are handled by the literal append/index formulas. The introductory phrase “is its inverse” must be read with the nonzero qualification already explicit in the inverse declaration docstring and all theorems.

## Definition classification (all 54 new definitions/abbreviations)

| Family | Classification and complete-carrier boundary |
|---|---|
| SourceCanonicalPhase, SourceOsculatingPhase; sourceStrongAMD, sourceKeplerPeri/Apo, eight sourceOsc* | Exact source subtypes and literal restrictions; canonical radial boundary allowed, osculating nondegenerate boundary enforced; no chosen witnesses/fallbacks. |
| spatialActionVector | Literal vector of existing total canonical actions; physical use guarded by SpatialNegativeEnergy. |
| SpatialBarrierState | Literal physical/action-membership/AMD inequality predicate; chamber follows from U ⊆ chamber in consumers. |
| spatialBarrierCompact | Literal closed geometric inequalities for arbitrary real parameters; compactness theorem uses R,P ≥ 0, nonsingularity theorem uses dS,dP > 0. No claim that every point has negative energy. |
| spatialMovingField | Literal existing Hamiltonian-vector-field application; analytic/C¹ interpretation restricted to the collision-free domain. |
| spatialFirstExitTube, spatialFirstExitCore | Literal strict/improved predicates for all parameters; subset/first-exit use δ,r > 0. No artificial off-domain branch. |
| spatialSpecEnergy/Axis/EccVector | Literal rational formulas on all k,q,V, with Lean division totalized at zero; orbital interpretation requires positive k, positive radius and negative energy where used. |
| ten spatialOsc*/spatialKeplerPeri/Apo total definitions | Literal (42) and canonical endpoints; formulas alone are not ellipses at arbitrary phases, zero energy, zero/nonpositive mass or parameter. The physical supplier theorems establish all guards. |
| SpatialOscPhase; eight spatialSourceOsc*, two spatialSourceKeplerPeri/Apo | Source subtypes and literal restrictions; positive ν,μ imply k > 0; source equations rfl; carrier validity and incidence proved separately. |
| periodicOrbitSetNM, complexTubeNM | Literal lattice saturation and open metric neighborhood; empty K and nonpositive radii behave as stated in SP-TUBE above. |
| lpRescaleNMFun, lpUnrescaleNMFun, lpRescaleNMLin, lpUnrescaleNMLin, lpRescaleNM, lpUnrescaleNM | Literal coordinate maps, linear and continuous wrappers; at ℓ = 0 slow blocks collapse, with no unguarded inverse claim. |
| lpRescaleNMEquiv | Genuine continuous linear equivalence, explicitly requires ℓ ≠ 0. |
| lpRescaleHamNM | Literal scalar multiple of composition, with inverse interpretation only under ℓ ≠ 0. |
| SpatialOscEstimate | Transparent output-conjunction abbreviation as a Prop-valued def; no hidden fields or instances. Its standalone carrier-packaging consumer is explicitly conditional. |

There are no new structures, instances, recursive definitions, arbitrary optimizers, selected physical states or conditional fallback branches. Every definition body was read; literal-formula totality is distinguished from source physical meaning throughout.

## Declaration-by-declaration ledger

Names below are relative to the namespace shown per module. Every new declaration is listed; the source reasoning and whole-carrier qualifications in the package sections above apply. PASS here certifies the scoped declaration, not the spatial headline or a future frozen anchor.

### KAM/Planetary/Spatial/ComplexTube.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `periodicOrbitSetNM` | PASS | Literal body/carrier; classified above. |
| `complexTubeNM` | PASS | Literal body/carrier; classified above. |
| `mem_ball_shiftNM` | PASS | N12 generic tube/translation identity. Axioms: STD3. |
| `tubeNM` | PASS | N12 generic tube/translation identity. Axioms: STD3. |
| `complexTubeNM_self` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `periodicOrbitSetNM_self` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `isOpen_complexTubeNM` | PASS | N12 generic tube/translation identity. Axioms: STD3. |
| `complexTubeNM_mono` | PASS | N12 generic tube/translation identity. Axioms: STD3. |
| `complexTubeNM_add_fastShift` | PASS | N12 generic tube/translation identity. Axioms: STD3. |

### KAM/Planetary/Spatial/Confinement.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `spatialFirstExitTube` | PASS | Literal body/carrier; classified above. |
| `spatialFirstExitCore` | PASS | Literal body/carrier; classified above. |
| `spatialFirstExitCore_subset_tube` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `spatialMovingSolutionOn_mono` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuous_bodyVector3_snd'` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuous_bodyVector3_fst'` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuous_spaceSq'` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuous_spaceCross'` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuous_angularMomentum3'` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuousAt_spatialKeplerEnergy'` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuousAt_spatialActionVector` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuousAt_spatialStrongAMD` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `continuousAt_spatialStrongGap` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `eventually_spatialNegativeEnergy` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `isOpen_spatialFirstExitTube` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `spatialFirstExitCore_closed` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |
| `spatialStrongFirstExit_of_stopped_drift` | PASS | L14/N6 continuity, first exit or conditional assembly. Axioms: STD3. |

### KAM/Planetary/Spatial/Continuation.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `spatialMovingField` | PASS | Literal body/carrier; classified above. |
| `spatial_moving_ode` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatialStrongAMD_le_of_tube` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatial_maximal_global_of_barrier` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatial_maximal_global_of_tube` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |

### KAM/Planetary/Spatial/Geometry.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `spatialActionVector` | PASS | Literal body/carrier; classified above. |
| `SpatialBarrierState` | PASS | Literal body/carrier; classified above. |
| `actionAxis_spatialActionVector` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spaceLength_le_add_sub` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `norm_le_spaceLength` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatialStrongBarrier_physical` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `continuous_bodyVector3'` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatialBarrierCompact` | PASS | Literal body/carrier; classified above. |
| `spatialBarrierCompact_isCompact` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatialBarrierCompact_subset` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `exists_spatialBarrierCompact` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |
| `spatialPerihelionFloor_le` | PASS | L5/L6/N11 spatial geometry or continuation. Axioms: STD3. |

### KAM/Planetary/Spatial/NonresonantAdapter.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `lpRescaleNM_eq_lpRescale` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpUnrescaleNM_eq_lpUnrescale` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRescaleHamNM_eq_lpRescaleHam` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpContinuousNM_extCx` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRealDomNM_isOpen` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRealWfieldNM_congr_eventuallyEq` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpIndicatorNM_field` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpBlockNM_c_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `lpBlockNM_lam_pos` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpOrbitNM_hasDerivAt` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `nonresonant_drift_of_chartDataNM` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |

### KAM/Planetary/Spatial/NonresonantAdapterRescale.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `lpRescaleNMFun` | PASS | Literal body/carrier; classified above. |
| `lpUnrescaleNMFun` | PASS | Literal body/carrier; classified above. |
| `lpRescaleNMLin` | PASS | Literal body/carrier; classified above. |
| `lpUnrescaleNMLin` | PASS | Literal body/carrier; classified above. |
| `lpRescaleNM` | PASS | Literal body/carrier; classified above. |
| `lpUnrescaleNM` | PASS | Literal body/carrier; classified above. |
| `lpRescaleNM_apply` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `lpUnrescaleNM_apply` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `lpUnrescaleNM_lpRescaleNM` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRescaleNM_lpUnrescaleNM` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRescaleNMEquiv` | PASS | Literal body/carrier; classified above. |
| `fastAction_lpRescaleNM` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `slowPair_lpRescaleNM` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `smul_slowPair_lpRescaleNM` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpUnrescaleNM_theta` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpUnrescaleNM_fast` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpUnrescaleNM_q` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpUnrescaleNM_p` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRescaleHamNM` | PASS | Literal body/carrier; classified above. |
| `lpRescaleHamNM_hasFDerivAt` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRescaleNM_field` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |
| `lpRescaleNM_hasDerivAt` | PASS | L13/N6 generic coordinates or explicit conditional adapter. Axioms: STD3. |

### KAM/Planetary/Spatial/Osculating.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `SpatialOscEstimate` | PASS | Literal body/carrier; classified above. |
| `exists_spatial_osc_estimates` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatialBarrier_osc_data` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatial_osculating_barrier` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatialOscPhase_of_estimates` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |

### KAM/Planetary/Spatial/Osculating/Basic.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `spatialOscVelocity` | PASS | Literal body/carrier; classified above. |
| `spatialOscParam` | PASS | Literal body/carrier; classified above. |
| `spatialOscEnergy` | PASS | Literal body/carrier; classified above. |
| `spatialOscAxis` | PASS | Literal body/carrier; classified above. |
| `spatialOscEccVector` | PASS | Literal body/carrier; classified above. |
| `spatialOscEcc` | PASS | Literal body/carrier; classified above. |
| `spatialOscPeri` | PASS | Literal body/carrier; classified above. |
| `spatialOscApo` | PASS | Literal body/carrier; classified above. |
| `spatialKeplerPeri` | PASS | Literal body/carrier; classified above. |
| `spatialKeplerApo` | PASS | Literal body/carrier; classified above. |
| `spatialOscVelocity_eq_hamiltonianVectorField` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatialOscEnergy_eq_spec` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialOscAxis_eq_spec` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialOscEccVector_eq_spec` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spaceSq_smul_scalar` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatialKeplerEnergy_eq_spec` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialKeplerAxis_eq_spec` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialKeplerEccVector_eq_spec` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialOsc_tangency` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `SpatialOscPhase` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscVelocity` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscParam` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscEnergy` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscAxis` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscEccVector` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscEcc` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscPeri` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscApo` | PASS | Literal body/carrier; classified above. |
| `spatialSourceKeplerPeri` | PASS | Literal body/carrier; classified above. |
| `spatialSourceKeplerApo` | PASS | Literal body/carrier; classified above. |
| `spatialSourceOscVelocity_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscParam_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscEnergy_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscAxis_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscEccVector_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscEcc_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscPeri_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceOscApo_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceKeplerPeri_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialSourceKeplerApo_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spatialOscPhase_ellipse` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |

### KAM/Planetary/Spatial/Osculating/Core.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `spatial_osc_core` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |

### KAM/Planetary/Spatial/Osculating/Estimates.lean

Namespace `KAM.Planetary.Spatial`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `spatialSpecEnergy` | PASS | Literal body/carrier; classified above. |
| `spatialSpecAxis` | PASS | Literal body/carrier; classified above. |
| `spatialSpecEccVector` | PASS | Literal body/carrier; classified above. |
| `spaceSq_sub_spaceSq` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spaceLength_sub_le_add` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `abs_spaceSq_sub_le` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `abs_spaceLength_sub_spaceLength_le` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spaceSq_spatialSpecEccVector` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spaceDot_spatialSpecEccVector` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatialSpecAxis_tangency` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spaceLength_le_of_sub` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `abs_spaceSq_sub_le_of_sub` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `abs_spatialSpecEnergy_sub_le` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spatialSpecEccVector_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `spaceLength_eccNumerator_sub_le` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |
| `spaceLength_spatialSpecEccVector_sub_le` | PASS | L16/(42)/(43)/N10 spatial orbital algebra or estimate. Axioms: STD3. |

### KAM/Planetary/StrongAMD/PlanarSafety/Source.lean

Namespace `KAM.Planetary.StrongAMD`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `lp1_planar_strongAMD_safety_source_general` | PASS | LP1 source restatement; typing proofs only (N2). Axioms: STD3. |
| `lp1_planar_strongAMD_safety_source` | PASS | LP1 source restatement; typing proofs only (N2). Axioms: STD3. |

### KAM/Planetary/StrongAMD/SourceCarrier.lean

Namespace `KAM.Planetary.StrongAMD`.

| Declaration | Verdict | Reason / node |
|---|---|---|
| `SourceCanonicalPhase` | PASS | Literal body/carrier; classified above. |
| `SourceOsculatingPhase` | PASS | Literal body/carrier; classified above. |
| `sourceStrongAMD` | PASS | Literal body/carrier; classified above. |
| `sourceKeplerPeri` | PASS | Literal body/carrier; classified above. |
| `sourceKeplerApo` | PASS | Literal body/carrier; classified above. |
| `sourceOscVelocity` | PASS | Literal body/carrier; classified above. |
| `sourceOscParam` | PASS | Literal body/carrier; classified above. |
| `sourceOscEnergy` | PASS | Literal body/carrier; classified above. |
| `sourceOscAxis` | PASS | Literal body/carrier; classified above. |
| `sourceOscEccVector` | PASS | Literal body/carrier; classified above. |
| `sourceOscEcc` | PASS | Literal body/carrier; classified above. |
| `sourceOscPeri` | PASS | Literal body/carrier; classified above. |
| `sourceOscApo` | PASS | Literal body/carrier; classified above. |
| `sourceStrongAMD_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceKeplerPeri_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceKeplerApo_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscVelocity_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscParam_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscEnergy_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscAxis_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscEccVector_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscEcc_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscPeri_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceOscApo_def` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `SourceCanonicalPhase.hz` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceStrongAMD_eq` | PASS | Defining/algebraic identity; guards preserved. Axioms: STD3. |
| `sourceStrongAMD_nonneg` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sum_action_mul_eccDeficit_le_sourceStrongAMD` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceKepler_axis_pos` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceKepler_ecc_le_one` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceKeplerPeri_le_planeLength` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `planeLength_le_sourceKeplerApo` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceOscAxis_pos` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceOscPeri_pos` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `sourceOscPeri_le_planeLength` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |
| `planeLength_le_sourceOscApo` | PASS | L2/L3/L16 carrier characterization. Axioms: STD3. |

## Source and scope identity

| File | SHA-256 |
|---|---|
| `docs/tracks/LP/source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` |
| `docs/tracks/LP/source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` |
| `docs/tracks/LP/SPEC.md` | `ffd8a2793b9b37ca35e4a626d38d9af3c2f79d5cefa7c36e5e2aa844978dad22` |
| `docs/tracks/LP/audits/LP-W4B-handoff.md` | `ff193b820ea7f2f9feed9aa0a5fae5bd25dfb6832d94ddab35406530793611bd` |

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The generated `KAM/Root/Planetary.lean` is the sole protected-root exception in this package: exactly twelve new public imports, corresponding to the twelve new modules, with no theorem/body change. It is disclosed by the combined and component handoffs; no generated file was edited by this auditor. `git diff --check inp-lp...HEAD` exits 0 with no output. Initial git status was clean.

All implementation files have copyright, module command, public interface imports, module docstring and exposed public section; largest is 337 lines. No new import names a provider, frozen theorem or DRAFT_SORRY anchor. Direct frozen imports in the rescaling module are definitions only. No proof escape, forbidden declaration, resource override or EuclideanSpace occurs in the twelve-file diff. One local tactic macro expands only to ordinary tactics.

## Suspected source defects, deviations and remaining boundaries

No new mathematical defect in the pinned MAIN plus AMENDMENTS was found in this scope. The specific/total energy distinction in L5/L16 is handled explicitly, consistent with the existing LP-OSC audit note. The concrete documentation defect is N3 above; it does not change a declaration. The supplied nonexistent umbrella brief is N1; the implementation's general-base proof route is N2. Neither has been silently repaired. No source, frozen file, manifest, implementation, generated root or ledger was changed by this audit.

These results do not approve a freeze, resolve OD-11 for the owner, prove a spatial product chart/complex physical domain, discharge the stopped drift for spatial physical solutions, or certify T19. They certify the exact component surfaces identified in the W4B handoff. Kernel replay and short-name checks were stated by the user to have run in the launcher, whose output is unavailable here; no unseen launcher exit code is invented below.

## Hygiene and validation receipts

All reviewer Lean/Lake work was serialized, and each invocation ran within the exact D53 scope:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

The LP wrappers below implement that exact scope; the build wrapper also holds the compile gate and invokes one targeted module at a time. No clean, library/root rebuild, cache update, package mutation, heartbeat override or replay invocation was requested.

### Lint (independently rerun)

Exact command:

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w4b
```

Exit **0**. Complete stdout:

```text
check_lean_modules: PASS (3732 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

No stale-root exception was needed. The stated application-anchor limitation is lint's own output; this audit did not build a certificate application.

### Targeted builds (independently rerun)

Exact command (the LP gated wrapper invokes the five targeted builds serially under D53):

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-w4b KAM.Planetary.StrongAMD.PlanarSafety.Source KAM.Planetary.Spatial.Confinement KAM.Planetary.Spatial.Osculating KAM.Planetary.Spatial.ComplexTube KAM.Planetary.Spatial.NonresonantAdapter
```

Exit **0**. These five import closures cover all twelve new implementation modules. Relevant output, in invocation order:

```text
[lp_build] slot 2: KAM.Planetary.StrongAMD.PlanarSafety.Source (06:45:49)
Build completed successfully (9315 jobs).
[lp_build] slot 2: KAM.Planetary.Spatial.Confinement (06:46:10)
Build completed successfully (9127 jobs).
[lp_build] slot 2: KAM.Planetary.Spatial.Osculating (06:46:25)
Build completed successfully (9141 jobs).
[lp_build] slot 2: KAM.Planetary.Spatial.ComplexTube (06:46:41)
Build completed successfully (9096 jobs).
[lp_build] slot 2: KAM.Planetary.Spatial.NonresonantAdapter (06:46:56)
Build completed successfully (9235 jobs).
```

Build output replays upstream linter/deprecation warnings; none names a new module. No new-module warning, design signal, resource failure or elaboration error occurred. Full build stdout SHA-256: `c865fd242dc9753f4bc80d2b276ba2c1bea825094ae6dad44d247c28e5703e20`.

### Axioms (independently rerun for all 123 new public theorems)

The temporary `.lake/abi-scratch/maud-lp-w4b-1/Audit.lean` imports the twelve implementation modules and issues one `#print axioms` for each public theorem in the ledger (including SourceCanonicalPhase.hz). Exact command (stdout redirected to a scratch log):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/maud-lp-w4b-1/Audit.lean
```

Exit **0**. Every theorem row above has profile `STD3`, meaning exactly `[propext, Classical.choice, Quot.sound]`. Output contains all 123 expected names, with no missing output, errors or other axiom. Long names sometimes cause multiline printing; the log was parsed across line breaks without rerunning Lean.

Verbatim main-result output:

```text
'KAM.Planetary.Spatial.tubeNM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStrongFirstExit_of_stopped_drift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.spatialStrongAMD_le_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_maximal_global_of_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_maximal_global_of_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStrongBarrier_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialBarrierCompact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPerihelionFloor_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.nonresonant_drift_of_chartDataNM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.lpRescaleNM_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.lpRescaleNM_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatial_osc_estimates' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_osculating_barrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.StrongAMD.lp1_planar_strongAMD_safety_source' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Complete axiom stdout SHA-256: `dc1e62cd43f25395c493a158252c5968a4f51783985ac441d8d7e98906158aa1`.

### Replay, names and report-only boundary

The user explicitly supplied launcher completion of kernel replay and name checks and allowed omitting a repeat. They were not rerun; no independent leanchecker exit code is claimed. The combined handoff separately states all-module build, lint exit 0 and short-name OK. Independent results in this report are the five targeted builds, 123 theorem axiom checks, lint, diff/hygiene inspection and mathematical statement/body review. Probe files and logs were removed after transferring receipts into this report.

## Combined verdict — PASS WITH NOTES

| Package | Verdict | Qualification |
|---|---|---|
| LP-SRC | PASS WITH NOTES | Equivalent normalized specialization from the more general proved base (N2). |
| LP-SP-GEO | PASS | L5/L6 spatial geometry, projection and continuation as bounded by its brief. |
| LP-SP-OSC | PASS WITH NOTES | Correct specific-energy scale and full F2/N10 outputs; docstring typo N3. |
| LP-SP-CONF | PASS | Deliberately conditional stopped-drift first-exit helper. |
| LP-SP-TUBE | PASS | Generic n+m tube, including exact planar agreement. |
| LP-SP-ADAPT | PASS WITH NOTES | Correct generic slots/signs; nonzero-scale qualification N4. |

No blocking statement mismatch, meaning-changing carrier, unpaid source result hidden in a premise, or nonstandard axiom was found. The source objects remain unfrozen; the conditional spatial helpers retain their stated external obligations. The unavailable umbrella brief (N1), harmless proof-route deviation (N2), concrete typo (N3) and total-map qualification (N4) are disclosed above. Only this report is a persistent audit edit.
