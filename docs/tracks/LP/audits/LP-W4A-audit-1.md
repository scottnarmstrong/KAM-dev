# LP-W4A independent package audit 1

Audited 2026-11-01. HEAD `f3f62042fb15d8d50132ebb48866cc2d2462d144`; `inp` =
`ff50f80fec849069d80749214b135d97aa3f1edb`; `inp-lp` = `8e5482a17732010f88d3a42fc2a1c9097d4ece86`.
Read AGENTS.md, PLAN, DECISIONS, the independent audit brief, SPEC, combined/individual handoffs,
MAIN with AMENDMENTS, roadmap §§1–2 and OD-11. The requested aggregate package brief
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W4A.md` does not exist. The combined handoff
explicitly supplies `LP-SP-MODEL.md` and `LP-SP-ROT.md`; those two briefs define this bounded audit.

Compared `git diff inp...HEAD` and `git diff inp-lp...HEAD -- KAM`. The KAM scope agrees:
12 new spatial component modules plus the 26-line facade, and 13 generated imports in
`KAM/Root/Planetary.lean` (2,362 added lines total). Nothing in LP is frozen; no provider/seal
identity probe applies. Only this report is a persistent repository edit.

## LP-SP-MODEL — PASS WITH NOTES

No blocking mathematical or statement-fidelity defect found for the bounded package. This is
acceptance of the present non-frozen statements, not approval of a freeze proposal or proof of
later spatial-chart/headline results.

- **L1/model:** `spatialHamiltonian` literally has Σ|p|²/(2ν), central potential −ν/|q|,
  recoil μ|Σp|²/2 and one attractive pair term per i<j. `spaceSq_sum` establishes the algebra
  relating this recoil form to the planar diagonal-plus-cross-term convention. The solution and
  uniqueness predicates match the frozen planar patterns, including `DifferentiableAt` and
  `Set.univ`. The Newton predicate is the same finite-time pattern in Fin 3. Barycentric star
  position is −μΣνq/(1+μΣν), star velocity −μΣp, planet velocity p/ν; masses are (1,μν).
  Reconstruction retains the same time variable. Its μ≥0 assumption strengthens the source's
  μ>0 result by including the consistent massless-planet acceleration equations at μ=0.
  The elementary results also omit unnecessary global n≥2 and max ν=1 restrictions,
  a harmless strengthening for this bounded algebraic package.
  It does not separately export the full symplectic-reduction claim in MAIN L1; the package's
  requested theorem is the reconstruction implication.
- **L2:** energy is total νE, hence axis −ν/(2 energy), not −1/(2 energy).
  All ten advertised conjuncts are present with no prograde premise. The scalar helper's
  eccentricity and radial identities are proved from these spatial vectors before application;
  they are not assumed by the public physical theorem. L=0 gives e=1 and is included.
- **L3:** the vector derivative is proved zero, including recoil μP×P and paired force torques.
  `OrdConnected` is the interval premise, not a conservation assumption. Constancy yields the
  difference identity for any two times. Nonnegativity uses the actual negative-energy carrier.
  Nonzero total momentum, unit direction and individual projection bounds have appropriate
  guards. The per-action margin formulation implies the source's finite-minimum formulation;
  the strict positive-projection corollary is immediate but is not separately named.
- **Rotations/alignment:** orthogonality suffices for the Hamiltonian, lengths and solution iff.
  Properness is required for vector angular-momentum equivariance. Alignment constructs det=1
  rotations including the south-pole branch; it does not assume their existence as a premise.

**N1 — carrier surface before freezing.** `SpatialNegativeEnergy` is exactly positive ν, nonzero
positions and negative individual energy; it correctly permits radial states and does not impose
pair separation, which is unnecessary for Kepler elements. `SpatialElliptic` and
`spatialStrongAMDOn`, with its rfl characterization, provide a genuine source-carrier AMD.
However, `spatialKeplerAxis`, `spatialKeplerAction`, etc. remain public total helpers, with no
separately named subtype restrictions/characterizations. OD-11(b)'s eventual freeze policy says
“source subtypes for every frozen meaning-carrying definition” and “the total helpers stay
internal”. The current subtype supports such restrictions but is not itself a finished freeze
surface for every element. Preserve this distinction in the LP2 proposal; do not freeze the
unrestricted helpers as physical quantities. No current theorem uses an off-carrier fallback to
pay a physical conclusion. The literal total formulas are explicitly requested by this package.

**N2 — module/documentation hygiene.** The facade has only public imports and a module docstring,
but no `public section` (AGENTS rule 3 literally asks for one). It exports no local declaration,
so there is no visibility defect. Rotation46 has the required information, but not SPEC §4's
literal sentence: its text says “track LP, non-frozen.” and later “The statement surface …”.
Normalize these details when preparing the final surface; no auditor source edits made.

### Declaration inventory

All names below are in `KAM.Planetary.Spatial`. Rows cover every new public definition,
theorem and lemma. Supporting algebra is assessed against its literal type; main nodes against
MAIN and the briefs. `PASS/N1` flags only the freeze-surface caveat above.

| Node/module:line | Declaration | Verdict | Reason |
|---|---|---|---|
| Vector:31 | `spaceDot` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:34 | `spaceSq` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:37 | `spaceLength` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:40 | `spaceCross` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:44 | `bodyVector3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:49 | `spaceSq_def` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:52 | `spaceDot_def` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:56 | `spaceCross_apply_zero` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:58 | `spaceCross_apply_one` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:60 | `spaceCross_apply_two` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:63 | `spaceCross_eq_crossProduct` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:67 | `spaceDot_eq_dotProduct` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:71 | `spaceSq_eq_dotProduct` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:74 | `spaceSq_eq_spaceDot` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:77 | `spaceSq_nonneg` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:80 | `spaceLength_sq` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:83 | `spaceLength_nonneg` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:85 | `spaceSq_eq_zero_iff` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:95 | `spaceLength_eq_zero_iff` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:99 | `spaceLength_pos_iff` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:102 | `spaceLength_neg` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:105 | `spaceLength_sub_comm` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:108 | `spaceLength_smul` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:115 | `spaceSq_mul_spaceSq` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:120 | `abs_spaceDot_le` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:126 | `spaceDot_comm` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:129 | `spaceDot_add_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:133 | `spaceDot_sub_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:137 | `spaceDot_smul_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:141 | `spaceDot_zero_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:143 | `spaceSq_sub` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:147 | `spaceSq_add` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:151 | `spaceLength_add_le` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:161 | `spaceSq_sum_eq_sum_sum` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:170 | `spaceCross_anticomm` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:173 | `spaceCross_self` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:176 | `spaceCross_add_left` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:180 | `spaceCross_add_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:184 | `spaceCross_sub_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:188 | `spaceCross_smul_left` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:192 | `spaceCross_smul_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:196 | `spaceCross_zero_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:199 | `spaceDot_cross_self_left` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:202 | `spaceDot_cross_self_right` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:206 | `spaceDot_cross_cross` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:216 | `spaceDotCLM` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:219 | `spaceDotCLM_apply` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:222 | `hasFDerivAt_spaceSq` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:233 | `analyticAt_spaceSq` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:245 | `analyticAt_spaceLength` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:259 | `analyticAt_inv_spaceLength` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:264 | `hasFDerivAt_spaceLength` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:277 | `hasFDerivAt_inv_spaceLength` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:287 | `continuous_spaceLength` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:297 | `bodyVector3_zero` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:299 | `bodyVector3_add` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:302 | `bodyVector3_sub` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:305 | `bodyVector3_smul` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:309 | `ofBodies3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:312 | `bodyVector3_ofBodies3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:317 | `ofBodies3_bodyVector3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:324 | `posCLM3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:331 | `momCLM3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:337 | `posCLM3_apply` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:339 | `momCLM3_apply` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Vector:343 | `hasDerivAt_bodyVector3` | PASS | Literal Euclidean/block algebra; zero vectors included; calculus guards singularities. |
| Model:41 | `spatialHamiltonian` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:48 | `SpatialNoCollision` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:54 | `IsSpatialMovingSolutionOn` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:61 | `SpatialMovingUniqueOn` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:67 | `spatialGKernel` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:72 | `spatialFKernel` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:76 | `spatialCollisionFreeDomain` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:81 | `sum_sum_eq_diag_add_two_mul` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:106 | `spaceSq_sum` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:117 | `sum_mass_smul_spatialFKernel` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:146 | `hasFDerivAt_spaceSq_comp` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:151 | `hasFDerivAt_inv_spaceLength_comp` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:157 | `analyticAt_spaceSq_comp` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:161 | `analyticAt_inv_spaceLength_comp` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:167 | `isOpen_spatialCollisionFreeDomain` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:186 | `analyticOnNhd_spatialHamiltonian` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Model:226 | `differentiableAt_spatialHamiltonian` | PASS | Literal (1), collision guard and planar predicate pattern; general algebraic parameters. |
| Field:175 | `hamiltonianVectorField_spatial` | PASS | Differentiates (1); pair sign and recoil correct; no assumed field formula. |
| Field:203 | `bodyVector3_hamiltonianVectorField_spatial_fst` | PASS | Differentiates (1); pair sign and recoil correct; no assumed field formula. |
| Field:214 | `bodyVector3_hamiltonianVectorField_spatial_snd` | PASS | Differentiates (1); pair sign and recoil correct; no assumed field formula. |
| Elements:32 | `spatialKeplerEnergy` | PASS/N1 | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:36 | `spatialKeplerAxis` | PASS/N1 | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:40 | `spatialKeplerAction` | PASS/N1 | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:44 | `spatialKeplerEccVector` | PASS/N1 | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:50 | `planetAngularMomentum3` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:54 | `angularMomentum3` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:58 | `spatialStrongAMD` | PASS/N1 | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:63 | `SpatialNegativeEnergy` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:67 | `SpatialElliptic` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:70 | `spatialStrongAMDOn` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:73 | `spatialStrongAMDOn_eq` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Elements:76 | `angularMomentum3_eq_sum` | PASS | Literal (2), total energy is νE; carrier caveat N1. |
| Orbital:33 | `spaceSq_smul_sub_smul` | PASS | L2; positive mass, nonzero radius, negative energy only; radial case included. |
| Orbital:38 | `spaceDot_smul_sub_smul` | PASS | L2; positive mass, nonzero radius, negative energy only; radial case included. |
| Orbital:43 | `spaceSq_eccVector_identity` | PASS | L2; positive mass, nonzero radius, negative energy only; radial case included. |
| Orbital:58 | `spaceDot_eccVector` | PASS | L2; positive mass, nonzero radius, negative energy only; radial case included. |
| Orbital:73 | `spatial_orbital_identities` | PASS | L2; positive mass, nonzero radius, negative energy only; radial case included. |
| Momentum:39 | `hasDerivAt_spaceCross` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:59 | `spaceCross_sum_right` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:64 | `spaceCross_self_smul_right` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:68 | `sum_mass_smul_cross_spatialFKernel` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:98 | `sum_cross_rate_eq_zero` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:123 | `angularMomentum3_const` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:149 | `spaceLength_zero` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:152 | `spaceLength_sum_le` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:161 | `spaceDot_sum_left` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:167 | `spatialUnit` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:169 | `spaceLength_spatialUnit` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:175 | `spaceDot_spatialUnit` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:196 | `spatialStrongAMD_sub_eq_sum` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:206 | `spatialStrongAMD_nonneg` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:214 | `angularMomentum3_ne_zero_of_strongAMD_lt` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:226 | `proj_le_length_cross` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:234 | `sum_proj_eq` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:240 | `spatialStrongAMD_eq_sum_sub_proj` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:248 | `action_sub_strongAMD_le_proj` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:265 | `proj_margin` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Momentum:275 | `sum_action_mul_eccDeficit_le_spatialStrongAMD` | PASS | L3; torque cancellation and guarded projection/AMD algebra; see carrier classification. |
| Newton:33 | `spatialBarycentricPositions` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:39 | `spatialBarycentricVelocities` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:44 | `spatialMasses` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:48 | `IsSpatialNewtonSolutionOn` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:58 | `spatialBarycentricPositions_succ_sub_zero` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:64 | `spatialBarycentricPositions_succ_sub_succ` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:70 | `spatialBarycentricPositions_zero` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:75 | `spatialBarycentricVelocities_zero` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:79 | `spatialBarycentricVelocities_succ` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| Newton:236 | `isSpatialNewtonSolutionOn_of_isSpatialMovingSolutionOn` | PASS | L1 reconstruction; mass 1, G=1, physical time; μ=0 extension valid. |
| RotationAlgebra:30 | `spaceDot_sub_left` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:36 | `mul_transpose_eq_one` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:39 | `spaceDot_mulVec` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:44 | `spaceSq_mulVec` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:47 | `spaceLength_mulVec` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:53 | `spaceDot_cross_eq_det` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:61 | `rows_mulVec` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| RotationAlgebra:70 | `mulVec_spaceCross` | PASS | Orthogonal dot/length invariance; cross equivariance requires det=1. |
| Rotation:33 | `rotateBlocks` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:37 | `spatialRotatePhase` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:40 | `bodyVector3_rotateBlocks` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:44 | `eq_of_bodyVector3_eq` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:50 | `rotateBlocks_rotateBlocks` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:56 | `spatialRotatePhase_rotatePhase` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:65 | `spatialHamiltonian_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:72 | `spatialNoCollision_rotate_iff` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:77 | `spatialKeplerEnergy_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:82 | `spatialKeplerAxis_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:86 | `spatialKeplerAction_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:91 | `spatialKeplerEccVector_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:98 | `spaceLength_spatialKeplerEccVector_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:104 | `spatialNegativeEnergy_rotate_iff` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:115 | `planetAngularMomentum3_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:120 | `angularMomentum3_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| Rotation:125 | `spatialStrongAMD_rotate` | PASS | Literal block rotation; invariant/equivariant quantities have correct guards. |
| RotationSolution:32 | `rotateBlocksLin` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:41 | `spatialRotatePhaseCLM` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:44 | `spatialRotatePhaseCLM_apply` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:47 | `spatialGKernel_rotate` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:51 | `spatialFKernel_rotate` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:58 | `hamiltonianVectorField_spatial_rotate` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:79 | `isSpatialMovingSolutionOn_rotate` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| RotationSolution:94 | `isSpatialMovingSolutionOn_rotate_iff` | PASS | ODE transported by actual continuous linear rotation; inverse uses transpose. |
| Alignment:30 | `spaceE3` | PASS | Constructs proper rotation; handles south pole separately; L≠0 for alignment. |
| Alignment:77 | `exists_rotation_unit_eq_e3` | PASS | Constructs proper rotation; handles south pole separately; L≠0 for alignment. |
| Alignment:83 | `spatialUnit_mulVec` | PASS | Constructs proper rotation; handles south pole separately; L≠0 for alignment. |
| Alignment:88 | `exists_rotation_align` | PASS | Constructs proper rotation; handles south pole separately; L≠0 for alignment. |
| Alignment:96 | `exists_rotation_align_angularMomentum3` | PASS | Constructs proper rotation; handles south pole separately; L≠0 for alignment. |

## LP-SP-ROT — PASS WITH NOTES

Formula (46) is literal: `incTilt = (u,−v,0)/(2√G)`, `skewMatrix t w = t×w`, and the
positive cross term is 2c[t]×. The third column is exactly (−cv/√G,−cu/√G,1−Z/G).
Orthogonality and det=1 follow from polynomial identities, not hypotheses asserting the desired
rotation properties. Generic orthogonal cross-equivariance is a distinct, properly conditional
lemma; the concrete rotation discharges both conditions. The Q×P=G e₃ premise is the source
planar angular-momentum identity explicitly allowed by the brief, not an assumed rotated result.

The inverse recovers both coordinates from the actual R e₃ and fixed G; injectivity has both
carrier premises. `incRotation_mulVec_e₃` and cosine recovery are stronger than requested:
G>0 alone suffices. Analyticity is entrywise `AnalyticOnNhd` on the exact open carrier
G>0, (u²+v²)/2<G. At u=v=0 it gives the identity rotation and exact zero recovery without
node angles. This package does not claim full chart surjectivity, symplecticity, or an inverse
for arbitrary spatial states; those belong to LP-SP-CHART. Notes N2 and the total-formula
classification below apply; no blocking formula/sign/domain defect found.

| Node/module:line | Declaration | Verdict | Reason |
|---|---|---|---|
| Rotation46:33 | `skewMatrix` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:37 | `tiltRotation` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:42 | `incTilt` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:45 | `incCos` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:48 | `incRotation` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:53 | `incRotation_eq_tiltRotation` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:57 | `e₃` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:60 | `planarEmbed` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:62 | `skewMatrix_mulVec` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:68 | `skewMatrix_mul_skewMatrix` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:79 | `tiltRotation_eq` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:89 | `tiltRotation_transpose_mul` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:105 | `tiltRotation_det` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:114 | `mulVec_cross_mulVec` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:141 | `incTilt_apply_zero` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:144 | `incTilt_apply_one` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:147 | `incTilt_apply_two` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:150 | `incTilt_dot` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:160 | `incTilt_dot_lt_half` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:165 | `incCos_sq` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:170 | `incCos_pos` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:175 | `incRotation_transpose_mul` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:180 | `incRotation_det` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:185 | `incRotation_mulVec_e₃` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:203 | `incRotation_cross` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:208 | `planarEmbed_cross` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:214 | `incRotation_cross_eq_smul` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:220 | `incRotation_cross_dot_e₃` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:228 | `incRotation_e₃_two` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:232 | `incRotation_e₃_two_pos` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:239 | `incCos_eq_sqrt_of_e₃` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:247 | `incRotation_recover_u` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:257 | `incRotation_recover_v` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:267 | `incRotation_e₃_injective` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:275 | `incCarrier` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |
| Rotation46:278 | `incRotation_analyticOn` | PASS | Literal L17 rotation algebra and carrier; signs, inverse and analyticity checked. |

## Definition classification and edge cases

Every new public definition is inventoried above; the only private definition is `pairW3`
(Field:131), the explicit antisymmetric derivative kernel. There are no new abbrevs or structures.

| Definitions | Whole-carrier assessment |
|---|---|
| `spaceDot`, `spaceSq`, `spaceLength`, `spaceCross` | Genuine Euclidean algebra on every Fin 3 vector. Square-root argument is always nonnegative. Zero length iff zero vector. |
| `bodyVector3`, `ofBodies3` | Actual inverse block extraction/assembly via finProdFinEquiv, including n=0. |
| `spaceDotCLM`, `posCLM3`, `momCLM3` | Genuine linear functionals/projections, with application characterizations; no supplied proof invoice. |
| `spatialHamiltonian` | Literal total algebraic helper; collision/zero-mass values use Lean's inverse-zero convention, not a physical extension. Physical solutions exclude collisions and source applications use positive masses. |
| `SpatialNoCollision`, `spatialCollisionFreeDomain` | Exact nonzero star/pair differences, all momenta; no hidden energy condition. Empty body family is vacuously collision-free. |
| `IsSpatialMovingSolutionOn`, `SpatialMovingUniqueOn` | Actual ODE and local uniqueness predicates. Empty time sets are vacuous as in the planar predicates. Uniqueness alone is not asserted to imply existence; no theorem assumes it here. |
| `spatialGKernel`, `spatialFKernel`, private `pairW3` | Literal inverse-cube force algebra; at collisions inverse-zero totalizes summands to zero. Physical field formulas are guarded; algebraic antisymmetry identities remain valid there. |
| `spatialKeplerEnergy`, `spatialKeplerAxis`, `spatialKeplerAction`, `spatialKeplerEccVector` | Literal total helpers. For ν=0 energy/action/eccentricity can collapse; E=0 gives axis=0; positive E with positive ν gives negative axis and sqrt/action=0. These have no elliptic physical meaning. All physical L2 conclusions require positive ν, radius and negative E. See N1. |
| `planetAngularMomentum3`, `angularMomentum3` | Genuine cross product/sum on every phase point, including collisions and n=0 (sum zero). |
| `spatialStrongAMD` | Literal sum of total actions minus Euclidean total momentum length; physical nonnegativity is guarded, not claimed globally. |
| `SpatialNegativeEnergy`, `SpatialElliptic`, `spatialStrongAMDOn` | Exact source region and restriction, no conclusion-shaped field. Radial e=1 allowed. For n=0 the carrier is vacuous, AMD=0. The name Elliptic does not impose nondegeneracy. |
| `spatialUnit` | Normalization on L≠0; at L=0 equals zero, not a unit vector. Unit/projection/alignment conclusions carry nonzero guards. |
| `spatialBarycentricPositions`, `spatialBarycentricVelocities`, `spatialMasses` | Literal formulas for every algebraic input. M=0 or ν=0 has nonphysical inverse-zero values; reconstruction assumes ν>0 and μ≥0, ensuring M≥1. At μ=0 star rests at origin and planets satisfy unit-central-mass test-particle equations. n=0 leaves the single stationary star. |
| `IsSpatialNewtonSolutionOn` | Collision-free acceleration ODE for arbitrary supplied masses, including zero masses. Uses ordinary HasDerivAt at each time in J, exactly the planar pattern. |
| `rotateBlocks`, `spatialRotatePhase`, `rotateBlocksLin`, `spatialRotatePhaseCLM` | Genuine linear block actions for any matrix; no claim of invertibility without a matrix inverse/orthogonality premise. |
| `spaceE3`, `e₃`, `planarEmbed` | Literal basis vectors/embedding everywhere. Two names for the same basis vector are harmless. |
| `skewMatrix`, `tiltRotation` | Polynomial matrix expressions everywhere. Generic tiltRotation is a rotation only under c²=1−t·t; the conditional lemmas are distinctly named. |
| `incTilt`, `incCos`, `incRotation` | Literal total formula (46), physical analytic rotation on incCarrier. For G≤0 sqrt G=0 and inverse-zero makes t=0, c=1, R=Id; for excessively large tilt c may be zero and R need not be orthogonal. No unguarded rotation theorem relies on those values. These totals must retain their guarded interpretation or be restricted for freezing. |
| `incCarrier` | Exactly G>0 and Z<G; open strict inequalities, Z≥0 automatic. Boundary Z=G excluded; no inverse/analyticity conclusion claims otherwise. |

No conclusion-shaped hypotheses found in any new public theorem. Source premises, algebraic identities,
actual ODE solutions and carriers account for all hypotheses. In particular the scalar orbital helper,
proper-orthogonal cross lemma and planar Q×P identity are discharged by producers in concrete uses.
No provider or DRAFT_SORRY anchor is directly imported by any new module.

## Checks and limitations

All invocations serial, with D53's exact scope, MemoryMax=4G, MemorySwapMax=0, nice 10,
LEAN_NUM_THREADS=1. No resource-budget overrides, clean, cache fetch, root regeneration or source edits.

1. `/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-thr KAM.Planetary.Spatial KAM.Planetary.Spatial.Rotation46`
   uses the compile-slot gate and the required capped command once per target. Exit 0.
   Output: `Build completed successfully (9113 jobs).` and
   `Build completed successfully (9047 jobs).` These are dependency replays, not fresh full-library builds.
   Warnings: pre-existing Kepler.Energy unused hm/hκ; Alignment:39,56 unused simp argument Matrix.one_apply.
2. `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW4AAudit1.lean`
   exited 0. Probe imports Spatial and Rotation46 and issues `#print axioms` for all 164 new
   public theorems/lemmas in the inventory. Every record reports exactly
   `[propext, Classical.choice, Quot.sound]` (155 one-line and 9 wrapped records); no additional
   axiom. This includes every L1–L3, solution rotation, alignment and L17 export. Probe deleted afterwards.
   Full output captured during audit at `/tmp/lp-w4a-audit-1-axioms.log`.
3. Kernel replay/name checks: supplied by the launcher per the task, not rerun. Their pane output
   is unavailable here; no independently observed replay exit code is claimed. Read lp_audit.sh
   to confirm its capped, serial replay/name-check procedure. Current builds/axiom checks above
   are independently observed; the audit does not upgrade launcher provenance into a fresh replay.
4. `/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-thr`: exit 0.
   This is the only lint invocation; its wrapper caps the entire script and its serial ABI Lean child.
   Exact output:

```text
check_lean_modules: PASS (3720 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

5. `git diff --check inp...HEAD`: exit 0, no output. Protected-path check
   `git diff --name-only inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0,
   empty output. The generated root part IS changed, by the reported generator output:
   13 public imports only; no mathematical declaration. This is an explicit package deviation
   from the generic protected-root instruction, acknowledged rather than hidden.
6. Largest component is Vector.lean, 353 lines; Rotation46 is 330; every component has copyright,
   module/import/docstring/public exposed section. Facade exception recorded in N2.

## Combined verdict — PASS WITH NOTES

Both bounded non-frozen packages pass the source/statement audit, subject to N1's explicit
freeze-surface limitation and N2's minor documentation/module-header cleanup. No source erratum
suspected in the reviewed MAIN (1)–(2), L1–L3 or the bounded algebra of L17; AMENDMENTS are respected.
No claim is made about later spatial chart, headline assembly, frozen-statement identity or
full symplectic reduction exports. Auditor deviations: none; missing aggregate brief handled
through the handoff's two exact briefs. Existing package deviation: generated root imports.

Final verification: scratch probe removed; `git status --short` shows only this untracked report;
`git diff --check` and `git diff --exit-code -- KAM docs/PLAN.md docs/DECISIONS.md` exit 0.
