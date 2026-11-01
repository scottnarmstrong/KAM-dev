# LP-W4D independent audit 1

Audited HEAD: `4f02ec3bec33e81866643d7964e6495c4083add4` (2026-11-01). **Combined verdict: PASS WITH NOTES**, for the non-frozen package statements only. No source theorem is sealed by this report, and no LP2 headline assembly is claimed.

Read AGENTS.md, PLAN.md, DECISIONS.md, the audit brief, SPEC, MAIN as amended by AMENDMENTS, the combined handoff and all four component briefs/handoffs. The specified `packages/LP-W4D.md` is absent; the four LP-SP component briefs supply the bounded targets. No frozen/provider type-equivalence probe is applicable: this package has no LP frozen anchor or provider.

Scope: inspected `git diff inp...HEAD` and `git diff inp-lp...HEAD -- KAM`. Both report multiple merge bases and use `8b678fc94372ab9df786d87a369ab4a0e9329028`, including separately audited W4C chart/product additions. Following the explicit handoff boundary, detailed declaration review uses `git diff inp-lp-w4c HEAD -- KAM`, base `b6796b2f5bd60c642c687091dc65ec101204de0d`: 22 new modules plus the generated root (23 files; 3,132 lines in the new modules). W4C is an imported prerequisite, not re-certified here. The broad protected-path comparison is empty for KAM/Frozen, manifest, KAM.lean and README.md. The generated KAM/Root/Planetary.lean import additions are a disclosed package deviation; the auditor did not edit them.

## LP-SP-DOM — PASS WITH NOTES

D2 uses the closed whole ball (47), with both Fin (n+n) slow blocks and the shared 4r action tube. The 3δ/16 margin follows from the shared modulus. D3 uses only C≤Cₑ₃, so no alignment restriction contaminates the analytic core. D4 supplies a uniform periodic holomorphic scalar extension and real trace; constants precede I⁰ and μ. D5 uses castAdd (n+n) for fast and natAdd n for slow blocks, with floor(Re λ/(2π)) reducing the angle cell. D6 is the exact untruncated Hamiltonian split. Rotation/alignment premises are source typing data.

The original DOM handoff says the scalar tube alone carries the denominator clause. That is insufficient as an explicit denominator receipt; in this combined package DOMX supplies precisely that missing clause. Read DOM together with DOMX for full L18.

| Node / location under Spatial | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| AnalyticDomain/Alignment.lean:39 | `spaceE3_eq_e₃` | PASS | L18: alignment is explicit typing data; one fixed SO(3) rotation and conservation. |
| AnalyticDomain/Alignment.lean:42 | `spatialStrongAMD_eq_spatialFixedPlaneDeficit_of_aligned` | PASS | L18: alignment is explicit typing data; one fixed SO(3) rotation and conservation. |
| AnalyticDomain/Alignment.lean:53 | `eq_smul_e₃_of_spatialUnit_eq` | PASS | L18: alignment is explicit typing data; one fixed SO(3) rotation and conservation. |
| AnalyticDomain/Alignment.lean:63 | `spatialStrongAMD_eq_spatialSlowDeficit_of_aligned` | PASS | L18: alignment is explicit typing data; one fixed SO(3) rotation and conservation. |
| AnalyticDomain/Alignment.lean:74 | `aligned_rotated_solution_stays_aligned` | PASS | L18: alignment is explicit typing data; one fixed SO(3) rotation and conservation. |
| AnalyticDomain/Alignment.lean:90 | `exists_aligned_rotated_solution` | PASS | L18: alignment is explicit typing data; one fixed SO(3) rotation and conservation. |
| AnalyticDomain/Containment.lean:36 | `spatialSecularBall` | PASS | L8 (22)/L18 (47), N3: correct fast/slow blocks and floor angle reduction. |
| AnalyticDomain/Containment.lean:40 | `spatialStrongCore_containment` | PASS | L8 (22)/L18 (47), N3: correct fast/slow blocks and floor angle reduction. |
| AnalyticDomain/Core.lean:42 | `spatialSlowDeficit` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:47 | `spatialStrongCore` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:57 | `continuous_spatialFast_snd` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:60 | `continuous_spatialSlowDeficit` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:70 | `spatialSlowDeficit_nonneg` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:75 | `spatialPhase_norm_le` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:87 | `isCompact_spatialStrongCore` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:195 | `spatialStrongCore_margin` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:211 | `spatialGammaBody_add_spatialZBody_le` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Core.lean:221 | `spatialStrongCore_subset_dom` | PASS | L18 (47), L8 and N2: closed whole core; all 4n slow coordinates and shared-tube margin. |
| AnalyticDomain/Extension.lean:36 | `fastShift_zero_phase` | PASS | L8/L18/N12: periodic scalar extension, real trace and exact split, uniform before centre/mass. |
| AnalyticDomain/Extension.lean:42 | `spatialChartSafe_shift_iff` | PASS | L8/L18/N12: periodic scalar extension, real trace and exact split, uniform before centre/mass. |
| AnalyticDomain/Extension.lean:57 | `fSpatial_spatialPoincareProd_shift` | PASS | L8/L18/N12: periodic scalar extension, real trace and exact split, uniform before centre/mass. |
| AnalyticDomain/Extension.lean:66 | `exists_spatialStrongTube` | PASS | L8/L18/N12: periodic scalar extension, real trace and exact split, uniform before centre/mass. |
| AnalyticDomain/Extension.lean:123 | `spatialHamiltonian_split_chartSafe` | PASS | L8/L18/N12: periodic scalar extension, real trace and exact split, uniform before centre/mass. |
| AnalyticDomain/Safety.lean:36 | `spatialChartSafe` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |
| AnalyticDomain/Safety.lean:39 | `spatialChartSafe_subset_dom` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |
| AnalyticDomain/Safety.lean:44 | `spatialNegativeEnergy_spatialPoincareProd` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |
| AnalyticDomain/Safety.lean:67 | `spatialActionVector_spatialPoincareProd` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |
| AnalyticDomain/Safety.lean:74 | `spatialStrongAMD_le_spatialSlowDeficit` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |
| AnalyticDomain/Safety.lean:83 | `spatialStrongCore_barrierState` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |
| AnalyticDomain/Safety.lean:96 | `spatialStrongCore_subset_chartSafe` | PASS | L18: whole-ball safety from C ≤ fixed-plane deficit, with no alignment premise. |

## LP-SP-DOMX — PASS WITH NOTES

SpatialTubeData has the intended field list: holomorphy/real trace/periodicity at R, scalar and full chart/momentum sup bounds at R/2, operator first derivatives at R/4, and positive-real denominator control with holomorphic reciprocal principal roots and real Euclidean traces at ρ≤R/4. The body blocks use finProdFinEquiv (i,k), k:Fin 3. The estimate loses 3ε(ε+2Q). With d=min(dS,dP), Q=2 max R 0 and ε=min(1,d²/(6+12Q)), that loss is ≤d²/2; pair errors use ε/2+ε/2. The final width ρ is positive and controls chart displacement through its derivative bound.

lemma18_complete chooses all data and rStar,s,b before I⁰, has no μ parameter, and explicitly gives rStar≤4r (N3). Bounds on the larger quarter/half tubes restrict to its final thin tube. A common positive bound M can be obtained by enlarging the finitely many bounds; the separately named M,M′ do not weaken the estimate.

Documentation note N1: Bounds/Algebra.lean:22 still says “Re (w · w) ≥ |u|² − (2ε² + 4Qε)”. This is the planar coefficient, whereas its actual theorem at :59 and all uses correctly have 3ε(ε+2Q). Correct the docstring; no proof repair is required.

| Node / location under Spatial | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| AnalyticDomain/Bounds.lean:58 | `SpatialTubeData` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds.lean:112 | `exists_spatialTubeData` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds.lean:191 | `lemma18_complete` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Algebra.lean:35 | `cBody3` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Algebra.lean:39 | `cDot3` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Algebra.lean:41 | `cBody3_ofReal` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Algebra.lean:44 | `cDot3_ofReal` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Algebra.lean:48 | `cDot3_cpow_ofReal` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Algebra.lean:59 | `re_cDot3_ge` | PASS WITH NOTE N1 | Correct 3ε(ε+2Q) theorem; stale module-doc coefficient (N1). |
| AnalyticDomain/Bounds/Algebra.lean:90 | `differentiableOn_inv_sqrt_cDot3` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Chart.lean:35 | `IsSpatialChartExtension` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Chart.lean:51 | `IsSpatialChartExtension.toSmallerSpatialTube` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Chart.lean:66 | `exists_spatialChart` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Denominator.lean:41 | `exists_spatialTube_re_cDot3_ge` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Denominator.lean:141 | `exists_spatialDenominatorTube` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Tube.lean:37 | `mem_periodicOrbitSetNM_self` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Tube.lean:45 | `closedBall_subset_complexTubeNM` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Tube.lean:59 | `exists_norm_le_halfTubeNM` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Tube.lean:98 | `norm_fderiv_le_quarterTubeNM` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |
| AnalyticDomain/Bounds/Tube.lean:112 | `norm_sub_le_of_quarterTubeNM` | PASS | L8/L18: literal analytic object or bound; fields are proved before centre and μ. |

## LP-SP-NRR — PASS

lpUnrescaleCNM reads the flattened input as θ and (I,q,p): q at natAdd n (castAdd m i), p at natAdd n (natAdd m i), and fast I at castAdd (m+m). Both slow blocks have all 2n entries when m=n+n. lpTraceNM uses only the n fast actions for the Kepler Hamiltonian. μ/(2π), period-one angles and the unchanged-time weighted bracket match MAIN L13. The Diophantine premise in spatial_stopped_drift is (5) in radian frequencies ν³/I³; engine frequencies divide by 2π.

lpExtNFHypNM constructs every field, including 64π(2n)s rB≤w². The source constants precede μ, I⁰ and curves. N6 is strict: rs=min(4rg,R/4)>0, ρ=min(rs,Imin)/2<rs, and scale choice gives D₀√μ≤ρ; equality at the stopped-radius cap therefore cannot hit rStar=rs. The premises of spatial_stopped_drift give chart solution, projection and localization only. A separate physical-solution hypothesis is unnecessary here (the chart solution projects physically); it is a strengthening, not an assumed drift. LPChartTubeNM is supplied internally by DOM, not an extra hypothesis of the source-level stopped-drift result.

| Node / location under Spatial | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| NonresonantReuse/Drift.lean:40 | `lpBlockNM` | PASS | L13/N6/T19: constants precede μ/centre/curves; stopped drift is derived, not assumed. |
| NonresonantReuse/Drift.lean:45 | `spatial_stopped_drift` | PASS | L13/N6/T19: constants precede μ/centre/curves; stopped drift is derived, not assumed. |
| NonresonantReuse/Hyp.lean:41 | `lpChartHamNM` | PASS | L13: trace uses only n Kepler actions; every engine field supplied with 2n slow pairs. |
| NonresonantReuse/Hyp.lean:48 | `lpTraceNM` | PASS | L13: trace uses only n Kepler actions; every engine field supplied with 2n slow pairs. |
| NonresonantReuse/Hyp.lean:82 | `lpExtNFHypNM` | PASS | L13: trace uses only n Kepler actions; every engine field supplied with 2n slow pairs. |
| NonresonantReuse/Pert.lean:37 | `lpUnrescaleCNM` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/Pert.lean:44 | `lpPertNM` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/Pert.lean:50 | `LPChartTubeNM` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/Pert.lean:62 | `lpUnrescaleCNM_extCx` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/Pert.lean:71 | `lpUnrescaleCNM_differentiable` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/Pert.lean:82 | `lpUnrescaleCNM_shift` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/Pert.lean:99 | `lpUnrescaleCNM_mem_complexTube` | PASS | L13/N12: literal complex unrescaling and period-one μ/(2π) perturbation. |
| NonresonantReuse/PertClass.lean:35 | `lpTubeNM_mono` | PASS | L13: holomorphy, periodicity, real trace and weighted bound follow from supplied tube data. |
| NonresonantReuse/PertClass.lean:43 | `lpPertNM_dom_mem` | PASS | L13: holomorphy, periodicity, real trace and weighted bound follow from supplied tube data. |
| NonresonantReuse/PertClass.lean:51 | `lpPertNM_extClass` | PASS | L13: holomorphy, periodicity, real trace and weighted bound follow from supplied tube data. |
| NonresonantReuse/PertClass.lean:76 | `lpPertNM_sup_le` | PASS | L13: holomorphy, periodicity, real trace and weighted bound follow from supplied tube data. |
| NonresonantReuse/PertClass.lean:88 | `lpPertNM_wbound` | PASS | L13: holomorphy, periodicity, real trace and weighted bound follow from supplied tube data. |

## LP-SP-LIFT — PASS WITH NOTES

SpatialLiftData.aligned is its only orientation datum. Its other fields are source initial data, the shared chamber and budget; no improved drift or confinement is assumed. SpatialStoppedOn literally matches SP-CONF's hstop antecedent, including strict action and AMD bounds. Conservation plus proj_margin gives positive individual e₃ projections. Chart AMD is identified with strong AMD only after alignment; safety of the entire compact chart cylinder uses only C≤fixed-plane deficit.

uniformDataNM has exactly the parameters and conclusion of track P's uniform_data after replacing Phase(n+n) by Phase(a+b); in particular the zero-angle cylinder, shift conditions, UniformData and delta≤π are retained. The lift uses a maximal chart ODE, physical projection uniqueness and compact-cylinder continuation, rather than assuming an inverse curve or a confinement conclusion. It gives two-sided derivatives on an open interval containing uIcc 0 t. The real-domain rescaling proof uses castAdd(m+m) and both slow subblocks, with strict action distance. It remains a valid localization statement even for wS=0: no invertibility or engine-dynamics claim is made at zero width.

spLiftChartHam is the split expression; spatialPulledHam and lpChartHamNM are definitionally Hμ∘Ψ. Split/pulled equality is used on the valid chart domain and their fields are compared through equality on an open neighbourhood, so no off-domain totalization is exploited. spatialStopped_drift_of_chartData is clearly named/documented conditional, with ExtNFHyp, smallness and trace premises. It is not presented as an unconditional MAIN result or the discharged SP-CONF hstop.

Cross-package note N2: spatialSecularBall and spLiftSecularBall are equal on their whole carriers by Finset.sum_add_distrib and Finset.sum_div (independently probed). Recommend one canonical definition or an exported equality lemma before LP2 freeze assembly. spatialChartSafe=spLiftChartSafe and lpChartHamNM=spatialPulledHam are definitional equalities; split-field equality already has a theorem. The two block constructors consequently agree after rewriting the ball equality. These are routine interface identifications, not unpaid analytic hypotheses. This diff supplies ingredients for DOM→NRR→LIFT→SP-CONF; it does not itself perform the LP-SP-SAFE assembly.

| Node / location under Spatial | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| ChartLift/Lift.lean:40 | `spLiftActionVector_spatialPoincareProd` | PASS | L14: existence by maximal chart ODE, projection uniqueness and compact-cylinder continuation. |
| ChartLift/Lift.lean:47 | `spatialChartAMD_eq_of_aligned` | PASS | L14: existence by maximal chart ODE, projection uniqueness and compact-cylinder continuation. |
| ChartLift/Lift.lean:76 | `SpatialLiftData.zeroAngle_mem_spatialLiftQ` | PASS | L14: existence by maximal chart ODE, projection uniqueness and compact-cylinder continuation. |
| ChartLift/Lift.lean:94 | `SpatialLiftData.mem_spatialChartSafe_of_liftQ` | PASS | L14: existence by maximal chart ODE, projection uniqueness and compact-cylinder continuation. |
| ChartLift/Lift.lean:163 | `SpatialLiftData.spatialChartLift_of_stopped` | PASS | L14: existence by maximal chart ODE, projection uniqueness and compact-cylinder continuation. |
| ChartLift/Premises.lean:45 | `spatialStoppedBlock` | PASS | L14/L13: derives localization/slow membership; conditional adapter distinctly named. |
| ChartLift/Premises.lean:51 | `lpRescaleNM_mem_realDom` | PASS | L14/L13: derives localization/slow membership; conditional adapter distinctly named. |
| ChartLift/Premises.lean:80 | `SpatialLiftData.spatialChartLift_premises` | PASS | L14/L13: derives localization/slow membership; conditional adapter distinctly named. |
| ChartLift/Premises.lean:125 | `SpatialLiftData.spatialStopped_drift_of_chartData` | PASS | L14/L13: derives localization/slow membership; conditional adapter distinctly named. |
| ChartLift/Setting.lean:42 | `spatialChartAMD` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:46 | `spLiftChartSafe` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:50 | `spatialPulledHam` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:54 | `spLiftChartHam` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:57 | `spLiftChartHam_eq_pulled` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:62 | `isOpen_spLiftChartSafe` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:66 | `spLiftChartSafe_subset_dom` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:69 | `analyticOnNhd_spatialPulledHam` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:75 | `spLiftChartHam_field_eq` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:84 | `differentiableAt_spatialChartHam` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:92 | `contDiffOn_spatialLiftField` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:100 | `spatialDim_eq` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:103 | `spatialPoincareProdCast` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:107 | `spatialPoincareProdCastDom` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:110 | `spatialPoincareProdCast_isChart` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:125 | `spatialLiftPhysicalDeriv` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:166 | `spatialFastShift_neg` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:173 | `spLiftChartSafe_shift_iff` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:190 | `spatialLiftField_periodic` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:214 | `spatialLiftQ` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:218 | `spatialLiftQ_isClosed` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:234 | `spatialLiftQ_slow_bound` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:248 | `spatialLiftQ_fast_bound` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:259 | `spatialLiftQ_isCompact` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:285 | `spatialChartAMD_zeroAngle` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Setting.lean:295 | `spatialChartAMD_eq_sum_body` | PASS | L14/L18: literal chart definitions, germ field equality, symplectic casting and compact cylinder. |
| ChartLift/Stopped.lean:43 | `spLiftSecularBall` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:52 | `SpatialLiftData` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:68 | `SpatialStoppedOn` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:78 | `SpatialLiftData.spLift_n_mul_r_pos` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:85 | `SpatialLiftData.spLift_abs_threshold_sub_le` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:94 | `SpatialLiftData.spLift_threshold_ball_le` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:102 | `SpatialLiftData.spLift_strongAMD_le_of_stopped` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:111 | `SpatialLiftData.spatialUnit_of_aligned` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Stopped.lean:123 | `SpatialLiftData.spLift_prograde_of_stopped` | PASS | L14/L18: exact strict stopped conditions; source budget and alignment; projection/AMD margins. |
| ChartLift/Uniform.lean:36 | `udZeroFstCastAdd` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:40 | `udZeroSnd` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:45 | `udZeroFstNatAdd` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:50 | `udShiftFstCastAdd` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:55 | `udAngleNM` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:57 | `udAngleNM_continuous` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:65 | `udCellNM_isCompact` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |
| ChartLift/Uniform.lean:71 | `uniformDataNM` | PASS | L14/N12: faithful n+n to a+b retyping of uniform_data, including empty carriers. |

## Definitions and carriers

Every new non-theorem declaration is classified below. All are literal constructions or clearly labelled Prop specifications. No junk fallback, hidden optimizer or conclusion-shaped record field was found. Existing physical/chart total functions can have nonphysical values outside their source domains; all physical identities here use domain/negative-energy premises. Empty cores and empty level sets are permitted and the uniform extensions are then vacuous, consistent with MAIN L8. Circular/coplanar zero slow coordinates are included, with no division by eccentricity or inclination in these new definitions.

| Definition (namespace KAM.Planetary.Spatial) | Classification and edge cases |
|---|---|
| `SpatialTubeData` | Prop collection of explicitly proved analytic data, including R>0, ρ>0, ρ≤R/4 and dS,dP>0. M,M' need not be positive; bounds suffice and can be enlarged. |
| `cBody3` | Literal body-major finProdFinEquiv block; Fin 0 bodies supplies no spurious body. |
| `cDot3` | Bilinear sum of three complex squares, never Hermitian norm. Null complex vectors may have zero square; branch theorems require positive real part. |
| `IsSpatialChartExtension` | Prop specification of holomorphy, real trace/safety and periodicity. Existence is proved, not a standing source premise. |
| `spatialSecularBall` | Literal Euclidean sublevel over 4n real coordinates. Negative RHS gives empty set; zero RHS gives the zero slow point. |
| `spatialSlowDeficit` | Literal half sum of squares of both Fin (n+n) slow blocks; nonnegative, zero at zero, defined for every n. |
| `spatialStrongCore` | Literal closed angle cell, existential centre, closed 4r action distance and closed ball (47). Empty level set gives empty core; negative r gives empty core. No fallback. |
| `spatialChartSafe` | Literal intersection of chart domain and collision-free preimage, on the full phase carrier. |
| `spatialStoppedBlock` | Literal block with spLiftSecularBall. Arbitrary wS, including zero, is harmless in localization; dynamics requires positive width in ExtNFHyp. |
| `spatialChartAMD` | Literal half sum of slow-pair squares, equal to spatialSlowDeficit algebraically. Equals strong AMD only under alignment. |
| `spLiftChartSafe` | Definitionally identical to spatialChartSafe; no extra orientation restriction. |
| `spatialPulledHam` | Definitionally identical to lpChartHamNM; literal Hμ∘Ψ. |
| `spLiftChartHam` | Literal Kepler plus μ perturbation; equal to pulled Hamiltonian on chart domain, field equality on open safe domain. No off-domain equality used. |
| `spatialPoincareProdCast` | Composition with canonical phaseCast for n*3=n+(n+n); no coordinate permutation of physical bodies beyond this identity cast. |
| `spatialPoincareProdCastDom` | Literal preimage of product chart domain under the same cast; meaningful also for n=0. |
| `spatialLiftQ` | Literal zero-angle closed action box and slow sublevel, compact even when empty (e.g. negative c or negative radius for n>0). |
| `spLiftSecularBall` | Same ball as spatialSecularBall by sum_add_distrib and sum_div; equality checked by Lean probe. |
| `SpatialLiftData` | Prop source/typing record: masses, dimension, compact chamber U, positive δ,r, budget, negative energy, closed action ball, initial AMD margin and alignment. No conclusion field. |
| `SpatialStoppedOn` | Literal strict antecedent of spatialStrongFirstExit_of_stopped_drift.hstop on uIcc, including t=0 and t<0. |
| `udAngleNM` | Literal fast-angle injection with all other blocks zero; valid for a=0 or b=0. |
| `lpBlockNM` | Literal PartialBlock with centre, spatialSecularBall, radius and width. Positivity imposed at engine use, not silently totalized. |
| `lpChartHamNM` | Literal Hμ∘Ψ everywhere using the existing total physical Hamiltonian/chart. Physical identities used only in the valid domain. |
| `lpUnrescaleCNM` | Literal complex linear rescaling (2πθ, ℓq; I, ℓp); all indices checked against real unrescaling. Defined also at ℓ=0; no inverse claim there. |
| `lpPertNM` | Literal μ/(2π) times fc at unrescaled argument, all real μ,ℓ; μ=0 gives zero. |
| `LPChartTubeNM` | Prop specification of the scalar tube already constructed by exists_spatialStrongTube; no dynamical conclusion fields. |

## Checks and limitations

All Lean/Lake invocations in this audit were serial and under the exact owner D53 scope:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

1. Required lint, invoked only through the prescribed wrapper:

```sh
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w4d
```

Exit 0. Output:

```text
check_lean_modules: PASS (3769 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

2. Targeted builds, through the LP serial compile-slot wrapper (its actual Lake calls use the exact D53 scope above):

```sh
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-w4d KAM.Planetary.Spatial.AnalyticDomain KAM.Planetary.Spatial.NonresonantReuse KAM.Planetary.Spatial.ChartLift
```

Exit 0. Final output per target, respectively:

```text
Build completed successfully (9203 jobs).
Build completed successfully (9330 jobs).
Build completed successfully (9274 jobs).
```

Lake replayed existing dependency linter warnings (unused variables/simp arguments and a deprecated dif_pos); these are outside the W4D delta. No resource setting was changed and no application library was built.

3. Exhaustive axiom and interface probe, importing the three facades and issuing `#print axioms` for every one of the 94 new public theorems listed in the tables:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW4DAudit.lean
```

Final exit 0, no warnings/errors. 93 theorem outputs are exactly `[propext, Classical.choice, Quot.sound]`; `KAM.Planetary.Spatial.spatialDim_eq` outputs `[propext, Quot.sound]`. Thus no new public result has sorryAx or a nonstandard axiom. Main-result output (line wrapping normalized):

```text
'KAM.Planetary.Spatial.exists_aligned_rotated_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialTubeData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.lemma18_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStrongCore_containment' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.exists_spatialStrongTube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialLiftData.spatialChartLift_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialLiftData.spatialChartLift_premises' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialLiftData.spatialStopped_drift_of_chartData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.SpatialLiftData.spLift_prograde_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_stopped_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same probe also elaborated the following independent interface checks:

```lean
open KAM.Planetary.Spatial KAM.Planetary.StrongAMD
example {n : ℕ} (ν : Fin n → ℝ) (δ : ℝ) (I0 : Fin n → ℝ) :
    spatialSecularBall ν δ I0 = spLiftSecularBall ν δ I0 := by
  ext y
  simp only [spatialSecularBall, spLiftSecularBall, Set.mem_ofPred_eq]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
example {n : ℕ} (ν : Fin n → ℝ) :
    spatialChartSafe ν = spLiftChartSafe ν := rfl
example {n : ℕ} (ν : Fin n → ℝ) (μ : ℝ) :
    lpChartHamNM ν μ = spatialPulledHam ν μ := rfl
```

The first attempt exited 1 only because the auditor used forward simp rules for sum_div in the ball equality; all 94 axiom queries already succeeded. Changing that probe to the explicit reverse rewrite above resolved the goal. No package file was changed. The scratch probe was deleted after the successful check.

4. Read-only source hygiene: forbidden-token/resource-option/provider-import/EuclideanSpace search in the 22 new modules returned no matches. All carry copyright/module/public imports/module documentation; declaration-bearing files have an exposed public section. The import-only AnalyticDomain facade has no declarations to expose. Largest new file: ChartLift/Setting.lean, 302 lines. There are 119 public declarations (94 theorems and 25 definitions/structures); all have a table row, and all 25 objects have a carrier classification. `git diff --check` exited 0. Protected paths were unchanged against inp as stated above; the generated root import delta was inspected and not modified.

Kernel replay and short-name checks: **not rerun**, as the user expressly states the launcher already ran them and asks for an economical package audit. Their prior output/exit codes are not visible in this pane, so this report does not invent a locally observed leanchecker exit code or name-check result. The independently observed checks here are lint, targeted builds, all public theorem axioms, and the three interface probes. No provider/seal ABI equality is applicable to this non-frozen package.


No suspected new defect in MAIN or AMENDMENTS was found. The stale local docstring N1, duplicate interfaces N2, absent combined brief and generated-root deviation are the notes above. No proof-resource override, default-heartbeat design signal or OOM was observed by this auditor. Imported engine, tube, chart and geometry results remain prerequisites with their previously audited scope; source fidelity of this package is not inferred merely from lint or kernel acceptance.
