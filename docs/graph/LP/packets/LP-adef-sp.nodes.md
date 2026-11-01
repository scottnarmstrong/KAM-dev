NODE: lpM:s1:data#spaceDot
KIND: definition
TITLE: spaceDot (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceDot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Euclidean scalar product on Fin 3 → ℝ. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceDot
FROZEN_ANCHOR_ID: planetary.d59.spaceDot.v1
FROZEN_ABI_SHA256: 4551abaaa4755d552dd5bab7eac43b0405360fabfc32ef52b3d98fda3049a324
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceDot (KAM/Frozen/Planetary/Spatial/Defs/SpaceDot.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:data#spaceSq
KIND: definition
TITLE: spaceSq (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L15-L15
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceSq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Squared Euclidean length on Fin 3 → ℝ. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceSq
FROZEN_ANCHOR_ID: planetary.d59.spaceSq.v1
FROZEN_ABI_SHA256: bcae08a71ff40c78513831da5ca7c3ca114dc45666dafcf71956999cc38f1cfd
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceSq (KAM/Frozen/Planetary/Spatial/Defs/SpaceSq.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:data#spaceLength
KIND: definition
TITLE: spaceLength (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L15-L15
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Euclidean length on Fin 3 → ℝ, independent of the ambient Pi sup norm. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceLength
FROZEN_ANCHOR_ID: planetary.d59.spaceLength.v1
FROZEN_ABI_SHA256: 70ce223ee332d660b3e6917f1766402e3c9336962a2f8c5c59b4dc57511cbe03
DEPS: lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L15-L15 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceLength (KAM/Frozen/Planetary/Spatial/Defs/SpaceLength.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spaceCross
KIND: definition
TITLE: spaceCross (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spaceCross
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The standard cross product on Fin 3 → ℝ, written out in components. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean
FROZEN_DECL: KAM.Planetary.Spatial.spaceCross
FROZEN_ANCHOR_ID: planetary.d59.spaceCross.v1
FROZEN_ABI_SHA256: 87bc64bdb88d2ae2e38e01091904aa638633c9f8cb56ebb79f2759351e9f9c89
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spaceCross (KAM/Frozen/Planetary/Spatial/Defs/SpaceCross.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#bodyVector3
KIND: definition
TITLE: bodyVector3 (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L20
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.bodyVector3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Extract the three Cartesian coordinates of body i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean
FROZEN_DECL: KAM.Planetary.Spatial.bodyVector3
FROZEN_ANCHOR_ID: planetary.d59.bodyVector3.v1
FROZEN_ABI_SHA256: b5de44382a31d04a5940a23b52e58abda7a369f2ea78bbea0e5aff75c91a860c
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.bodyVector3 (KAM/Frozen/Planetary/Spatial/Defs/BodyVector3.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#planetAngularMomentum3
KIND: definition
TITLE: planetAngularMomentum3 (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.planetAngularMomentum3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Individual angular momentum L_i = q_i × p_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean
FROZEN_DECL: KAM.Planetary.Spatial.planetAngularMomentum3
FROZEN_ANCHOR_ID: planetary.d59.planetAngularMomentum3.v1
FROZEN_ABI_SHA256: e03d68e8041e465fb213075e42c6fbbc65755b88d5d79c7da8b41b4130e3d079
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:elements#spaceCross
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses bodyVector3
EDGE: lpM:s1:elements#spaceCross | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceCross
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.planetAngularMomentum3 (KAM/Frozen/Planetary/Spatial/Defs/PlanetAngularMomentum3.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#angularMomentum3
KIND: definition
TITLE: angularMomentum3 (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.angularMomentum3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Total angular momentum L = Σ_i q_i × p_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean
FROZEN_DECL: KAM.Planetary.Spatial.angularMomentum3
FROZEN_ANCHOR_ID: planetary.d59.angularMomentum3.v1
FROZEN_ABI_SHA256: ecc6c04d768f5c59f00a205d5a712118a800b6f0be7c82789cbfdb83d46040b7
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:elements#spaceCross
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses bodyVector3
EDGE: lpM:s1:elements#spaceCross | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceCross
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.angularMomentum3 (KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#spatialHamiltonian
KIND: definition
TITLE: spatialHamiltonian (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The exact spatial Hamiltonian H_μ (LP:MAIN §1 (1), d = 3): positions q_i and scaled canonical momenta p_i in Phase (n * 3), masses m_i = μ ν_i, central Kepler parameter one. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialHamiltonian
FROZEN_ANCHOR_ID: planetary.d59.spatialHamiltonian.v1
FROZEN_ABI_SHA256: b4614c6f0dba469b5409ef80174b3d0f5043fbb6fca3f6158fc225da6d76e7e0
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialHamiltonian (KAM/Frozen/Planetary/Spatial/Defs/SpatialHamiltonian.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#SpatialNoCollision
KIND: definition
TITLE: SpatialNoCollision (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialNoCollision
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The open physical domain of H_μ: no planet at the star and no two planets together. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialNoCollision
FROZEN_ANCHOR_ID: planetary.d59.SpatialNoCollision.v1
FROZEN_ABI_SHA256: cca4510b4e971c550607d55d4583b5b1dfbcf2c1cd25f20cbee2f803a18a8ba4
DEPS: lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the declaration uses spaceLength
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialNoCollision (KAM/Frozen/Planetary/Spatial/Defs/SpatialNoCollision.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#IsSpatialMovingSolutionOn
KIND: definition
TITLE: IsSpatialMovingSolutionOn (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.IsSpatialMovingSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: A genuine spatial moving-Sun solution on J: the frozen differentiability-guarded Hamiltonian ODE for H_μ together with collision exclusion (LP:MAIN §1 (1)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean
FROZEN_DECL: KAM.Planetary.Spatial.IsSpatialMovingSolutionOn
FROZEN_ANCHOR_ID: planetary.d59.IsSpatialMovingSolutionOn.v1
FROZEN_ABI_SHA256: 6499ca1d550e8d07037e70c29dff5e48c33dc6c9f7e978637c8c24b09f8fb5e5
DEPS: lpM:s1:model#IsHamiltonianSolutionOn, lpM:s1:model#Phase, lpM:s1:model#spatialHamiltonian, lpM:s1:model#SpatialNoCollision
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#IsHamiltonianSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses IsHamiltonianSolutionOn
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses Phase
EDGE: lpM:s1:model#spatialHamiltonian | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses spatialHamiltonian
EDGE: lpM:s1:model#SpatialNoCollision | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the declaration uses SpatialNoCollision
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.IsSpatialMovingSolutionOn (KAM/Frozen/Planetary/Spatial/Defs/IsSpatialMovingSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#SpatialMovingUniqueOn
KIND: definition
TITLE: SpatialMovingUniqueOn (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L69-L72
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialMovingUniqueOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Agreement with every other local spatial solution on its overlap with the certified interval (the pattern of the frozen planar MovingUniqueOn). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialMovingUniqueOn
FROZEN_ANCHOR_ID: planetary.d59.SpatialMovingUniqueOn.v1
FROZEN_ABI_SHA256: ca45020ff13ad89b7ed4e3077306848600850bc604bc4f07eadc4bd043d62d31
DEPS: lpM:s1:model#Phase, lpM:s1:model#IsSpatialMovingSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the declaration uses Phase
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the declaration uses IsSpatialMovingSolutionOn
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialMovingUniqueOn (KAM/Frozen/Planetary/Spatial/Defs/SpatialMovingUniqueOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialBarycentricPositions
KIND: definition
TITLE: spatialBarycentricPositions (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialBarycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Barycentric positions (star first, then the planets) from heliocentric q, with m₀ = 1. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialBarycentricPositions
FROZEN_ANCHOR_ID: planetary.d59.spatialBarycentricPositions.v1
FROZEN_ABI_SHA256: b5ef0dbc1e597050da5bb1fcca1a9608e9730cdb090fb893239f686c8d069f61
DEPS: lpM:s1:model#bodyVector3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses bodyVector3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialBarycentricPositions (KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricPositions.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialBarycentricVelocities
KIND: definition
TITLE: spatialBarycentricVelocities (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialBarycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Barycentric velocities: actual planet momenta are μ p, total momentum zero. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialBarycentricVelocities
FROZEN_ANCHOR_ID: planetary.d59.spatialBarycentricVelocities.v1
FROZEN_ABI_SHA256: cc092f40cafa08fca2fadf837a911b0cb22cf2dec98cae504beb31b40ea620ab
DEPS: lpM:s1:model#bodyVector3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses bodyVector3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialBarycentricVelocities (KAM/Frozen/Planetary/Spatial/Defs/SpatialBarycentricVelocities.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#spatialMasses
KIND: definition
TITLE: spatialMasses (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialMasses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The masses (1, μ ν_1, …, μ ν_n). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialMasses
FROZEN_ANCHOR_ID: planetary.d59.spatialMasses.v1
FROZEN_ABI_SHA256: aca567c2ed9ffb877daf85b2616eaa757cd2274656175e2de1d601f7886ff1ad
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialMasses (KAM/Frozen/Planetary/Spatial/Defs/SpatialMasses.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#IsSpatialNewtonSolutionOn
KIND: definition
TITLE: IsSpatialNewtonSolutionOn (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.IsSpatialNewtonSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Finite-interval Newton equations in dimension three, with Euclidean lengths (G = 1). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean
FROZEN_DECL: KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn
FROZEN_ANCHOR_ID: planetary.d59.IsSpatialNewtonSolutionOn.v1
FROZEN_ABI_SHA256: e0c5f38f79b55a20c71405151c0cde2c1c4a1cb3aaed11a4f685048977fb282d
DEPS: lpM:s1:data#spaceLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses spaceLength
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.IsSpatialNewtonSolutionOn (KAM/Frozen/Planetary/Spatial/Defs/IsSpatialNewtonSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerEnergy
KIND: definition
TITLE: spatialKeplerEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Total Kepler energy ν_i E_i of planet i (planar convention). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerEnergy
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerEnergy.v1
FROZEN_ABI_SHA256: c302a0603f146706db847d139cc2d8b2222c86a91adacde2a7325699d8b894a1
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerAxis
KIND: definition
TITLE: spatialKeplerAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Canonical semi-major axis a_i = −ν_i/(2 ν_i E_i) = −1/(2 E_i). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerAxis.v1
FROZEN_ABI_SHA256: 54bc0be144da1d819d43ee79ea7ad6aa9988e2b0852aced684e006af8bb9e96c
DEPS: lpM:s1:model#Phase, lpM:s1:elements#spatialKeplerEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerAction
KIND: definition
TITLE: spatialKeplerAction (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Kepler action Λ_i = ν_i √a_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerAction
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerAction.v1
FROZEN_ABI_SHA256: d60e5dfcf1d7572d8fcf00135d5b846dd640a5bbb35057b9db282ef49ee7f2bd
DEPS: lpM:s1:model#Phase, lpM:s1:elements#spatialKeplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerAxis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerAction (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerAction.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerEccVector
KIND: definition
TITLE: spatialKeplerEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Eccentricity vector 𝐞_i = (¦v¦² − 1/¦q¦) q − (q·v) v with v = p/ν. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerEccVector.v1
FROZEN_ABI_SHA256: 1bb4b8de6655df78aa778f7210f66704c5ced8b411bb6cbc5b5dc96195503017
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceDot, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceDot | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceDot
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spaceSq
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#SpatialNegativeEnergy
KIND: definition
TITLE: SpatialNegativeEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialNegativeEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The source carrier of the Kepler elements: positive masses, no planet at the star, negative energy of every planet. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialNegativeEnergy
FROZEN_ANCHOR_ID: planetary.d59.SpatialNegativeEnergy.v1
FROZEN_ABI_SHA256: 28c34d877b59da45e883d96289365dbd2a6ede92b5b660372666e1ae5efc18d7
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialNegativeEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialNegativeEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#SpatialElliptic
KIND: definition
TITLE: SpatialElliptic (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialElliptic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Phase points of the carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialElliptic
FROZEN_ANCHOR_ID: planetary.d59.SpatialElliptic.v1
FROZEN_ABI_SHA256: fec96f298327ab83e94caa4f136616dc8c2a7db23c675039543320c8e120853b
DEPS: lpM:s1:model#Phase, lpM:s1:elements#SpatialNegativeEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses Phase
EDGE: lpM:s1:elements#SpatialNegativeEnergy | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialNegativeEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialElliptic (KAM/Frozen/Planetary/Spatial/Defs/SpatialElliptic.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerPeri
KIND: definition
TITLE: spatialKeplerPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Canonical perihelion a_i (1 - e_i). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerPeri.v1
FROZEN_ABI_SHA256: cea64bbc7890c8a63c7b7c163c3314f979815bd8feece862103919a771ab394c
DEPS: lpM:s1:model#Phase, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#spatialKeplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses Phase
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerAxis
EDGE: lpM:s1:elements#spatialKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialKeplerApo
KIND: definition
TITLE: spatialKeplerApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialKeplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Canonical aphelion a_i (1 + e_i). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialKeplerApo
FROZEN_ANCHOR_ID: planetary.d59.spatialKeplerApo.v1
FROZEN_ABI_SHA256: 087f10dfe3d4707ae053044dc986422b593ed76bc17ac18922db4faa4a6e5289
DEPS: lpM:s1:model#Phase, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#spatialKeplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses Phase
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerAxis
EDGE: lpM:s1:elements#spatialKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialKeplerApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialKeplerApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscVelocity
KIND: definition
TITLE: spatialOscVelocity (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscVelocity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The actual heliocentric velocity V_i = p_i/ν_i + μ ∑_j p_j (LP:MAIN (10), L16, d = 3). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscVelocity
FROZEN_ANCHOR_ID: planetary.d59.spatialOscVelocity.v1
FROZEN_ABI_SHA256: c5c4e1fac529168f8c43646d947206434b2525754db216fb2bafe5766d04ba35
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses bodyVector3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscVelocity (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscVelocity.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscParam
KIND: definition
TITLE: spatialOscParam (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscParam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The gravitational parameter k_i = 1 + μ ν_i. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscParam
FROZEN_ANCHOR_ID: planetary.d59.spatialOscParam.v1
FROZEN_ABI_SHA256: 874d4be03742a7a5e7a10fbdb31a55a42e93db6be29cf92f5e6df89e9f94b8be
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscParam (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscParam.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscEnergy
KIND: definition
TITLE: spatialOscEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: E_i^osc = ¦V_i¦²/2 - k_i/¦q_i¦ (LP:MAIN L16 (42)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscEnergy
FROZEN_ANCHOR_ID: planetary.d59.spatialOscEnergy.v1
FROZEN_ABI_SHA256: 1c3f1059f7aab9156865ebab07de7d8efada5b3ed5d9ea145891ada687adeb61
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq, lpM:L16:defs#spatialOscParam, lpM:L16:defs#spatialOscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceSq
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscParam
EDGE: lpM:L16:defs#spatialOscVelocity | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscVelocity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscAxis
KIND: definition
TITLE: spatialOscAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a_i^osc = -k_i/(2 E_i^osc) (LP:MAIN L16 (42)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialOscAxis.v1
FROZEN_ABI_SHA256: be13a432a32f06eaf7bf8e65c1dc9d063c2d35c806b93a362f96952437312439
DEPS: lpM:s1:model#Phase, lpM:L16:defs#spatialOscEnergy, lpM:L16:defs#spatialOscParam
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEnergy
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscParam
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscEccVector
KIND: definition
TITLE: spatialOscEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: 𝐞_i^osc = ((¦V_i¦² - k_i/¦q_i¦) q_i - (q_i·V_i) V_i)/k_i (LP:MAIN L16 (42)). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialOscEccVector.v1
FROZEN_ABI_SHA256: 322e50eedad1837dd96e547926abc70730d48c48ac3ae6b98891357042b75e84
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceDot, lpM:s1:data#spaceLength, lpM:s1:data#spaceSq, lpM:L16:defs#spatialOscParam, lpM:L16:defs#spatialOscVelocity
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceDot | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceDot
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceLength
EDGE: lpM:s1:data#spaceSq | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceSq
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscParam
EDGE: lpM:L16:defs#spatialOscVelocity | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscVelocity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscEcc
KIND: definition
TITLE: spatialOscEcc (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: e_i^osc = ¦𝐞_i^osc¦ (LP:MAIN L16 (42)), Euclidean length. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscEcc
FROZEN_ANCHOR_ID: planetary.d59.spatialOscEcc.v1
FROZEN_ABI_SHA256: c01dad3160ba00498e7091749a0dcd3bca75e959f5c61d545518f7497ee54b55
DEPS: lpM:s1:model#Phase, lpM:s1:data#spaceLength, lpM:L16:defs#spatialOscEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses Phase
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spaceLength
EDGE: lpM:L16:defs#spatialOscEccVector | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscEcc (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscPeri
KIND: definition
TITLE: spatialOscPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Osculating perihelion a^osc (1 - e^osc). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialOscPeri.v1
FROZEN_ABI_SHA256: f607bde6f14125867faf6530601b3735a0ce944d9b8b547a85b040814db5c2d1
DEPS: lpM:s1:model#Phase, lpM:L16:defs#spatialOscAxis, lpM:L16:defs#spatialOscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses Phase
EDGE: lpM:L16:defs#spatialOscAxis | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscAxis
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialOscApo
KIND: definition
TITLE: spatialOscApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Osculating aphelion a^osc (1 + e^osc). (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialOscApo
FROZEN_ANCHOR_ID: planetary.d59.spatialOscApo.v1
FROZEN_ABI_SHA256: 4169a2ca2838fccbe5e583252d933a154f84da08f26d48250d740df2555d87e6
DEPS: lpM:s1:model#Phase, lpM:L16:defs#spatialOscAxis, lpM:L16:defs#spatialOscEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses Phase
EDGE: lpM:L16:defs#spatialOscAxis | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscAxis
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialOscApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#SpatialOscPhase
KIND: definition
TITLE: SpatialOscPhase (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialOscPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Valid actual-velocity osculating states (LP:MAIN L16, nondegenerate ellipses): positive masses, μ > 0, and for every planet ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialOscPhase
FROZEN_ANCHOR_ID: planetary.d59.SpatialOscPhase.v1
FROZEN_ABI_SHA256: 55de99be412cc3aa6d71e52e3b46f9157294990b777c1ffa3662c9440a3794c2
DEPS: lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spaceLength
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spatialOscEnergy
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialOscPhase (KAM/Frozen/Planetary/Spatial/Defs/SpatialOscPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#SpatialSourceCanonicalPhase
KIND: definition
TITLE: SpatialSourceCanonicalPhase (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialSourceCanonicalPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The canonical source carrier (LP:MAIN §1 (2)): phase points with positive masses, no planet at the star and negative Kepler energy of every planet. This is SP-MODEL's SpatialElliptic ν. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialSourceCanonicalPhase
FROZEN_ANCHOR_ID: planetary.d59.SpatialSourceCanonicalPhase.v1
FROZEN_ABI_SHA256: b2abbd09007c6b34051abd4fd40f13363f3f2b72a883d30af4f7c02919a30758
DEPS: lpM:s1:elements#SpatialElliptic
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SpatialElliptic | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses SpatialElliptic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialSourceCanonicalPhase (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceCanonicalPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#SpatialSourceOsculatingPhase
KIND: definition
TITLE: SpatialSourceOsculatingPhase (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.SpatialSourceOsculatingPhase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The osculating source carrier (LP:MAIN L16): SP-OSC's SpatialOscPhase n ν μ. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean
FROZEN_DECL: KAM.Planetary.Spatial.SpatialSourceOsculatingPhase
FROZEN_ANCHOR_ID: planetary.d59.SpatialSourceOsculatingPhase.v1
FROZEN_ABI_SHA256: 9363a6265245b1e5a17f1b1bfa0b9c1185326f524c8baf505f27fe25c1226828
DEPS: lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.SpatialSourceOsculatingPhase (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOsculatingPhase.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerAxis
KIND: definition
TITLE: spatialSourceKeplerAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAxis.v1
FROZEN_ABI_SHA256: 2d8e5041c2666c4ea07cf34d4b57420b868bcb362ef63a95b5b787235082651c
DEPS: lpM:s1:elements#spatialKeplerAxis, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#spatialKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerAxis
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerAction
KIND: definition
TITLE: spatialSourceKeplerAction (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: Λ_i = ν_i √a_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAction
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAction.v1
FROZEN_ABI_SHA256: 5dfa254c39d05876472ccc2036741976e8bcde824b39509d0e78e411d66018d5
DEPS: lpM:s1:elements#spatialKeplerAction, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#spatialKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialKeplerAction
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAction (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerAction.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerEccVector
KIND: definition
TITLE: spatialSourceKeplerEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L29
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The eccentricity vector 𝐞_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEccVector.v1
FROZEN_ABI_SHA256: 19466c1f4e528379a1f780425e508e4e093bad6bbb8a7a9acfc0ac7beec3c53f
DEPS: lpM:s1:elements#spatialKeplerEccVector, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#spatialKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses spatialKeplerEccVector
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L26-L26 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerEcc
KIND: definition
TITLE: spatialSourceKeplerEcc (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The eccentricity e_i = ¦𝐞_i¦ on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc.v1
FROZEN_ABI_SHA256: b0194453d629f3233d0b241b7bf74a2620c04a7e188a990c81e14757cd15e57d
DEPS: lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerEccVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialSourceKeplerEccVector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourcePlanetAngularMomentum
KIND: definition
TITLE: spatialSourcePlanetAngularMomentum (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourcePlanetAngularMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The individual angular momentum L_i = q_i × p_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum
FROZEN_ANCHOR_ID: planetary.d59.spatialSourcePlanetAngularMomentum.v1
FROZEN_ABI_SHA256: c9ae99ca6bc813fa278608faf90c10a9b03650c5643209dd52adb4d6f6639a3f
DEPS: lpM:s1:elements#planetAngularMomentum3, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#planetAngularMomentum3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses planetAngularMomentum3
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourcePlanetAngularMomentum.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceAngularMomentum
KIND: definition
TITLE: spatialSourceAngularMomentum (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceAngularMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The total angular momentum L = Σ_i q_i × p_i on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceAngularMomentum
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceAngularMomentum.v1
FROZEN_ABI_SHA256: 7cd0696d5f64ceaaee58528d1ceb008f044ec2bc8034b1c5bb0c77cfa51c1059
DEPS: lpM:s1:elements#angularMomentum3, lpM:s1:elements#SpatialSourceCanonicalPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#angularMomentum3 | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses angularMomentum3
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceAngularMomentum (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceAngularMomentum.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceStrongAMD
KIND: definition
TITLE: spatialSourceStrongAMD (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L37
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceStrongAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: The strong AMD C = Σ_i Λ_i − ¦L¦ on the canonical carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceStrongAMD
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceStrongAMD.v1
FROZEN_ABI_SHA256: db40ab8154db4af09586f1dbea057be06d210e1746fdf2cc59d5948eb87e50be
DEPS: lpM:s1:data#spaceLength, lpM:s1:elements#spatialSourceAngularMomentum, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spaceLength
EDGE: lpM:s1:elements#spatialSourceAngularMomentum | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialSourceAngularMomentum
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the declaration uses spatialSourceKeplerAction
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceStrongAMD (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceStrongAMD.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerPeri
KIND: definition
TITLE: spatialSourceKeplerPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a (1 - e) on the canonical negative-energy carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerPeri.v1
FROZEN_ABI_SHA256: 0f954b44e61d475642b9b5755a284bd6d892d0f791c1c888ad5bb4d86a38a85e
DEPS: lpM:s1:elements#SpatialElliptic, lpM:s1:elements#spatialKeplerPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SpatialElliptic | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses SpatialElliptic
EDGE: lpM:s1:elements#spatialKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerPeri
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:elements#spatialSourceKeplerApo
KIND: definition
TITLE: spatialSourceKeplerApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L89-L91
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceKeplerApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a (1 + e) on the canonical negative-energy carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerApo
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerApo.v1
FROZEN_ABI_SHA256: 93cec71a28e2b1385b1e9368c131383f103a8a4938d79fcd7f9d9dd31435e86d
DEPS: lpM:s1:elements#SpatialElliptic, lpM:s1:elements#spatialKeplerApo
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements#SpatialElliptic | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses SpatialElliptic
EDGE: lpM:s1:elements#spatialKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L89-L89 | the declaration uses spatialKeplerApo
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceKeplerApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscParam
KIND: definition
TITLE: spatialSourceOscParam (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L525
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscParam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: k_i on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscParam
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscParam.v1
FROZEN_ABI_SHA256: 7cc4a890e34e51a19e4dcccaae46a2d6a33ddc268c8a7507be53017527f05ff0
DEPS: lpM:L16:defs#spatialOscParam, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscParam | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses spatialOscParam
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L508-L508 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscParam (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscParam.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscEnergy
KIND: definition
TITLE: spatialSourceOscEnergy (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: E_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEnergy
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEnergy.v1
FROZEN_ABI_SHA256: 78032793e3980fd9a80aa47db770fb1122a90526656d29a4f206ad8711a0b9c6
DEPS: lpM:L16:defs#spatialOscEnergy, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEnergy
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEnergy (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEnergy.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscAxis
KIND: definition
TITLE: spatialSourceOscAxis (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L528
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscAxis
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscAxis.v1
FROZEN_ABI_SHA256: 8132682794d8795bbe9d0dccb709f454e4b8339bde4202b30ffbaf93ae44d776
DEPS: lpM:L16:defs#spatialOscAxis, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscAxis | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscAxis
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscAxis (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscAxis.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscEccVector
KIND: definition
TITLE: spatialSourceOscEccVector (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: 𝐞_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEccVector
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEccVector.v1
FROZEN_ABI_SHA256: a76d9ddaef222ec0aec2eb470849d8d481a47f3dcac07dad89bd6fd7d16f015a
DEPS: lpM:L16:defs#spatialOscEccVector, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscEccVector | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEccVector
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEccVector (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEccVector.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscEcc
KIND: definition
TITLE: spatialSourceOscEcc (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L520
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscEcc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: e_i^osc on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEcc
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEcc.v1
FROZEN_ABI_SHA256: 7c2c4107f425ba9a7a8b7590b02f9811ad0ff3d84a8197d5c4ba448d967d77b9
DEPS: lpM:L16:defs#spatialOscEcc, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses spatialOscEcc
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L510-L510 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEcc (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscEcc.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscPeri
KIND: definition
TITLE: spatialSourceOscPeri (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L528
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscPeri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a^osc (1 - e^osc) on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscPeri
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscPeri.v1
FROZEN_ABI_SHA256: d0f2beb1b8b01df0732f4f00cd0c0937a69348dc3248329ced5cd939c5bd8f9d
DEPS: lpM:L16:defs#spatialOscPeri, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscPeri | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscPeri
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscPeri (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscPeri.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L16:defs#spatialSourceOscApo
KIND: definition
TITLE: spatialSourceOscApo (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L528
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: a^osc (1 + e^osc) on the valid osculating carrier. (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscApo
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscApo.v1
FROZEN_ABI_SHA256: d66fd59c0696142631e582a3970f20f5277f01aba2f2db01ea806949b960c8d8
DEPS: lpM:L16:defs#spatialOscApo, lpM:L16:defs#SpatialOscPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs#spatialOscApo | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses spatialOscApo
EDGE: lpM:L16:defs#SpatialOscPhase | docs/tracks/LP/source/MAIN.md#L16@L521-L521 | the declaration uses SpatialOscPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscApo (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceOscApo.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialSourceBarycentricPositions
KIND: definition
TITLE: spatialSourceBarycentricPositions (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceBarycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: the barycentric positions of Lemma 1's explicit inverse (L104) on their source domain ν_i > 0, μ > 0 (literal formula, definitionally the total helper spatialBarycentricPositions) (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceBarycentricPositions
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceBarycentricPositions.v1
FROZEN_ABI_SHA256: 7bc0dbad04af66325815929350cf51358ced2ce7cc9394b923cb84e82da21b32
DEPS: lpM:L1#spatialBarycentricPositions
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#spatialBarycentricPositions | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses spatialBarycentricPositions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceBarycentricPositions (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricPositions.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:L1#spatialSourceBarycentricVelocities
KIND: definition
TITLE: spatialSourceBarycentricVelocities (spatial, d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L100-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d59.spatialSourceBarycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: the barycentric velocities of Lemma 1's explicit inverse (L104) on their source domain ν_i > 0, μ > 0 (literal formula, definitionally the total helper spatialBarycentricVelocities) (MAIN, d = 3)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceBarycentricVelocities
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceBarycentricVelocities.v1
FROZEN_ABI_SHA256: 625b6a1a24052b3d6c8ff36714206c239543f7b4b3fdb85842d11fdb66ee66ab
DEPS: lpM:L1#spatialBarycentricVelocities
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#spatialBarycentricVelocities | docs/tracks/LP/source/MAIN.md#L1@L100-L100 | the declaration uses spatialBarycentricVelocities
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceBarycentricVelocities (KAM/Frozen/Planetary/Spatial/Defs/SpatialSourceBarycentricVelocities.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: spatial (d = 3) frozen realization of a d-generic MAIN definition (SPEC §5 dimension rule); DEPS read mechanically from the frozen file's direct imports (D65)

NODE: lpM:s1:model#IsHamiltonianSolutionOn
KIND: definition
TITLE: IsHamiltonianSolutionOn (reused)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: iso.IsHamiltonianSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the declaration's binders (typing data; total formula, source meaning on its carrier)
SOURCE_QUANTIFIERS: for every value of the binders
SOURCE_CONCLUSION: A genuine lifted Hamiltonian solution on an open time interval, in an action domain. The domain is part of the solution concept, not an assumed confinement estimate.
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean
FROZEN_DECL: KAM.Iso.IsHamiltonianSolutionOn
FROZEN_ANCHOR_ID: iso.IsHamiltonianSolutionOn.v1
FROZEN_ABI_SHA256: b20065362bfe0068a5eb3cfdf98a886d7ffd591bdef0464cebfbe3e171d56beb
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.IsHamiltonianSolutionOn (KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition iso.IsHamiltonianSolutionOn.v1, bound as an LP anchor node (Q6); typing data of the moving-Sun solution predicates
