NODE: lpM:L2#spatialSourceKeplerAxis_pos
KIND: lemma
TITLE: 0 < a_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L31-L33
CONTRACT_ID: planetary.d59.spatialSourceKeplerAxis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: 0 < a_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAxis_pos.v1
FROZEN_ABI_SHA256: c473fbddfb2da335b627a6e34dae5eb2013d50c912a601e2700271611738f6de
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | when E_i < 0, a_i = -1/(2E_i) > 0 by (2)
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L31-L31 | the statement uses spatialSourceKeplerAxis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAxis_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAxis_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerAction_pos
KIND: lemma
TITLE: 0 < Λ_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
CONTRACT_ID: planetary.d59.spatialSourceKeplerAction_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: 0 < Λ_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAction_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAction_pos.v1
FROZEN_ABI_SHA256: 0b19b3858aac95d3274a9b1fb596545adf71161567d87d387b316a6d16c33269
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | Λ_i = ν_i √a_i with ν_i, a_i > 0
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses spatialSourceKeplerAction
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAction_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerAction_sq
KIND: lemma
TITLE: Λ_i^2 = ν_i^2 a_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L33-L33
CONTRACT_ID: planetary.d59.spatialSourceKeplerAction_sq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: Λ_i^2 = ν_i^2 a_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerAction_sq
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerAction_sq.v1
FROZEN_ABI_SHA256: d57d7de1afd13132b9cbb2fb396ba5e23492418758b2e34a499dba10ed67c8ab
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | Λ_i = ν_i √a_i, (2)
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L33-L33 | the statement uses spatialSourceKeplerAxis
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerAction_sq (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerActionSq.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerAction_sq
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerEcc_sq
KIND: lemma
TITLE: e_i^2 = 1 - ¦L_i¦^2/Λ_i^2 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc_sq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: e_i^2 = 1 - ¦L_i¦^2/Λ_i^2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc_sq.v1
FROZEN_ABI_SHA256: 7c5b493f48a3e2ce6b74f0f11714adc2a0f3ee300381f0060aa789d5bb6c4558
DEPS: lpM:L2, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourcePlanetAngularMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11): e^2 = 1 - ¦q × v¦^2/a and ¦q × p¦ = I√(1 - e^2)
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerEcc
EDGE: lpM:s1:elements#spatialSourcePlanetAngularMomentum | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourcePlanetAngularMomentum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc_sq (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccSq.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_sq
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerEcc_nonneg
KIND: lemma
TITLE: 0 ≤ e_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L34
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L34-L34
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: 0 ≤ e_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc_nonneg.v1
FROZEN_ABI_SHA256: 26d964de20b3d56a50241c95f4b417f3d6825fe3d0e324616c2d4d941115b974
DEPS: lpM:s1:elements, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | e_i = ¦e_i¦ is a length
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#s1@L34-L34 | the statement uses spatialSourceKeplerEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc_nonneg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_nonneg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerEcc_le_one
KIND: lemma
TITLE: e_i ≤ 1 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourceKeplerEcc_le_one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: e_i ≤ 1
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerEcc_le_one.v1
FROZEN_ABI_SHA256: 43c82cd83205dbd5a55345bd116cd00b1f3e4d4a865545a6c96f02b887ffe426
DEPS: lpM:L2, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerEcc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11) gives e^2 = 1 - ¦q × v¦^2/a ≤ 1
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerEcc
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerEcc_le_one (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerEccLeOne.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerEcc_le_one
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourcePlanetAngularMomentum_length
KIND: lemma
TITLE: ¦L_i¦ = Λ_i √(1 - e_i^2) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: ¦L_i¦ = Λ_i √(1 - e_i^2)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length.v1
FROZEN_ABI_SHA256: f6e9113ab208e30a3a2469cf64d5ccf4d3d6c11e900d75ecaa1cef164ceed8fd
DEPS: lpM:L2, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourcePlanetAngularMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11): ¦q × p¦ = I √(1 - e^2)
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerEcc
EDGE: lpM:s1:elements#spatialSourcePlanetAngularMomentum | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourcePlanetAngularMomentum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourcePlanetAngularMomentum_length_le
KIND: lemma
TITLE: ¦L_i¦ ≤ Λ_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length_le
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: ¦L_i¦ ≤ Λ_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le
FROZEN_ANCHOR_ID: planetary.d59.spatialSourcePlanetAngularMomentum_length_le.v1
FROZEN_ABI_SHA256: 2d950df835a3f9ae44e6f4c05773881cd203df43080a359b47e707f7a1fe785f
DEPS: lpM:L2, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourcePlanetAngularMomentum
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | (11): ¦q × p¦ = I √(1 - e^2) ≤ I
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourcePlanetAngularMomentum | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | the statement uses spatialSourcePlanetAngularMomentum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourcePlanetAngularMomentumLengthLe.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourcePlanetAngularMomentum_length_le
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerPeri_le_length
KIND: lemma
TITLE: a_i(1 - e_i) ≤ ¦q_i¦ (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: planetary.d59.spatialSourceKeplerPeri_le_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: a_i(1 - e_i) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerPeri_le_length.v1
FROZEN_ABI_SHA256: ab638195e8eae674077c06a78ac384ef3c34d38b87ceda9bbe1ae46468fc925a
DEPS: lpM:L2, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | (12): a(1 - e) ≤ ¦q¦
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spatialSourceKeplerPeri
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerPeri_le_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerPeriLeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerPeri_le_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L2#spatialSourceKeplerApo_ge_length
KIND: lemma
TITLE: ¦q_i¦ ≤ a_i(1 + e_i) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: planetary.d59.spatialSourceKeplerApo_ge_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i(1 + e_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceKeplerApo_ge_length.v1
FROZEN_ABI_SHA256: 686e73b0b457426b316776af53db5f711e46c8b9b9c5642bad9b9480cdb8e2e6
DEPS: lpM:L2, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerApo
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | (12): ¦q¦ ≤ a(1 + e)
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spaceLength
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/source/MAIN.md#L2@L118-L118 | the statement uses spatialSourceKeplerApo
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceKeplerApo_ge_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceKeplerApoGeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceKeplerApo_ge_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L3#spatialSourceStrongAMD_nonneg
KIND: lemma
TITLE: 0 ≤ C (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: planetary.d59.spatialSourceStrongAMD_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z
SOURCE_CONCLUSION: 0 ≤ C
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceStrongAMD_nonneg.v1
FROZEN_ABI_SHA256: 6d9389729156647f75b9ad2458784dc0e7560c2158efa002c9c21f01705778fd
DEPS: lpM:L3#amd-nonneg, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#amd-nonneg | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L¦ ≤ Σ¦L_i¦ ≤ Σ I_i
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L3@L132-L132 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#L3@L132-L132 | the statement uses spatialSourceStrongAMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceStrongAMD_nonneg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceStrongAMDNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceStrongAMD_nonneg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L3#spatialSourceAction_mul_eccDeficit_le
KIND: lemma
TITLE: Σ_i Λ_i(1 - √(1 - e_i^2)) ≤ C (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: planetary.d59.spatialSourceAction_mul_eccDeficit_le
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source canonical phase z: ν_i > 0, ¦q_i¦ > 0 and E_i < 0 for every i (SpatialSourceCanonicalPhase n ν)
SOURCE_QUANTIFIERS: for every n, ν, carrier point z
SOURCE_CONCLUSION: Σ_i Λ_i(1 - √(1 - e_i^2)) ≤ C
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceAction_mul_eccDeficit_le.v1
FROZEN_ABI_SHA256: 3bcbb6495450f26b39bc3c82017a9acc587b71a13a08b259b49b0a58a3460534
DEPS: lpM:L3#deficit, lpM:L3#deficit-zero-L, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerEcc, lpM:s1:elements#spatialSourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#deficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | for L ≠ 0: the inequality of (13)
EDGE: lpM:L3#deficit-zero-L | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the case L = 0, which the frozen statement includes
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerEcc | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses spatialSourceKeplerEcc
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#L3@L133-L133 | the statement uses spatialSourceStrongAMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceActionMulEccDeficitLe.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceAction_mul_eccDeficit_le
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscParam_pos
KIND: lemma
TITLE: 0 < k_i (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L512-L512
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscParam_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 < k_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscParam_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscParam_pos.v1
FROZEN_ABI_SHA256: 6acaa4099fabe01d3477bcadec3bb8f89e454983d437d299f8bbd96abfaae3f4
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscParam, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | k_i = 1 + μν_i with μ, ν_i > 0
EDGE: lpM:L16:defs#spatialSourceOscParam | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the statement uses spatialSourceOscParam
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L512-L512 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscParam_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscParamPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscParam_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscEnergy_neg
KIND: lemma
TITLE: E_i^osc < 0 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscEnergy_neg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: E_i^osc < 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEnergy_neg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEnergy_neg.v1
FROZEN_ABI_SHA256: 2361214739322a443c11e55d2ac6581a4bd6323822478fed43ca89583698bea9
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L515-L515 | E^osc of (42), negative on the carrier
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEnergy_neg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEnergyNeg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEnergy_neg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscEcc_lt_one
KIND: lemma
TITLE: e_i^osc < 1 (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscEcc_lt_one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: e_i^osc < 1
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEcc_lt_one.v1
FROZEN_ABI_SHA256: 5c0b552b09cf9a3239d0d2e632f55a635354c80cd68ab4889dd2ef974ad11ed7
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | e^osc of (42), below one on the carrier
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEcc_lt_one (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccLtOne.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_lt_one
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscEcc_nonneg
KIND: lemma
TITLE: 0 ≤ e_i^osc (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L518-L518
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscEcc_nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 ≤ e_i^osc
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscEcc_nonneg.v1
FROZEN_ABI_SHA256: 4b620ed7bef0718a24625ea9f2c7dd0b68977e41aff8645646cc09b982741b17
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | e^osc = ¦e^osc¦ is a length
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscEcc_nonneg (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscEccNonneg.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscEcc_nonneg
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscAxis_pos
KIND: lemma
TITLE: 0 < a_i^osc (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscAxis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 < a_i^osc
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscAxis_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscAxis_pos.v1
FROZEN_ABI_SHA256: e2a68783cebe55f3388defeb40ed9632ca90c375a75edb8466da6439919823e1
DEPS: lpM:L16:defs, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | a^osc = -k_i/(2E^osc) with k_i > 0, E^osc < 0
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscAxis_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscAxis_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscPeri_pos
KIND: lemma
TITLE: 0 < a_i^osc(1 - e_i^osc) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscPeri_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: 0 < a_i^osc(1 - e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscPeri_pos
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscPeri_pos.v1
FROZEN_ABI_SHA256: a757086991b433764db2d8127482c0e8268c7764364f1090858354add5ea14df
DEPS: lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscEcc_lt_one, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#spatialSourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | a^osc > 0
EDGE: lpM:L16#spatialSourceOscEcc_lt_one | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | e^osc < 1
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscPeri_pos (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_pos
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscPeri_le_length
KIND: lemma
TITLE: a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscPeri_le_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: a_i^osc(1 - e_i^osc) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscPeri_le_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscPeri_le_length.v1
FROZEN_ABI_SHA256: bc95e8ef9395be519563edde8996304cd2a61e8738af6d0e2110b2aa3cfcd043
DEPS: lpM:L16#tangent-ellipse, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spaceLength
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscPeri_le_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscPeriLeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscPeri_le_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:L16#spatialSourceOscApo_ge_length
KIND: lemma
TITLE: ¦q_i¦ ≤ a_i^osc(1 + e_i^osc) (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.spatialSourceOscApo_ge_length
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: spatial source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SpatialSourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, carrier point z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i^osc(1 + e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatialSourceOscApo_ge_length
FROZEN_ANCHOR_ID: planetary.d59.spatialSourceOscApo_ge_length.v1
FROZEN_ABI_SHA256: bf21b051b14b444c3d627dfe57c84ded7c73481f4cb387ab34179cc1e28ce82c
DEPS: lpM:L16#tangent-ellipse, lpM:s1:model#bodyVector3, lpM:s1:data#spaceLength, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#SpatialSourceOsculatingPhase
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses bodyVector3
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spaceLength
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement uses SpatialSourceOsculatingPhase
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatialSourceOscApo_ge_length (KAM/Frozen/Planetary/Spatial/Theorems/SpatialSourceOscApoGeLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatialSourceOscApo_ge_length
NOTE: spatial characterization (d = 3), frozen with its definition as one semantic unit

NODE: lpM:T19#spatial_strongAMD_exponentialSafety
KIND: theorem
TITLE: LP2: spatial strong-AMD exponential safety (Theorem 19 with Lemma 16)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: planetary.d59.spatial_strongAMD_exponentialSafety
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; τ > n - 1; spatial (d = 3)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ spatial phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2(τ+1))}): ∃ z : ℝ → spatial phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves the spatial (1) on [-T, T] without collision and agrees with every local solution; the barycentric reconstruction solves Newton's equations with masses (1, μν_i); for every t: elliptic, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, the drift bounds A_Λ√μ, A_a√μ, nA_Λ√μ of (8), (9) with d_⋆, d_pair, star distances ≥ d_⋆, pair distances ≥ d_pair; nondegenerate osculating elements with a^osc > 0, e^osc < 1, a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ a^osc(1 + e^osc), ¦a^osc - a¦ + ¦e^osc - e¦ ≤ A_elem μ, perihelion and aphelion errors ≤ A_osc μ, osculating gaps ≥ d_⋆/2, d_pair/2 (as in LP1, spatial carriers)
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ, τ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety
FROZEN_ANCHOR_ID: planetary.d59.spatial_strongAMD_exponentialSafety.v1
FROZEN_ABI_SHA256: 9d34c2a7b12a0614bfb923fbfffc0c67809cc2097021af4eddfbcb0c5995e7a8
DEPS: lpM:T19, lpM:T19#reconstruction, lpM:T19#osculating, lpM:L16#mu0-choice, lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscPeri_le_length, lpM:L16#spatialSourceOscApo_ge_length, lpM:L16#spatialSourceOscEnergy_neg, lpM:L16#spatialSourceOscEcc_lt_one, lpM:s1:dioph#IsDiophantine, lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:model#spatialMasses, lpM:s1:model#SpatialMovingUniqueOn, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerApo, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T19 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | LP2 is Theorem 19 (the §1 conclusion in d = 3)
EDGE: lpM:T19#reconstruction | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the Newtonian reconstruction clause
EDGE: lpM:T19#osculating | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the osculating clauses, including A_elem
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#spatialSourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a^osc > 0
EDGE: lpM:L16#spatialSourceOscPeri_le_length | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a^osc(1 - e^osc) ≤ ¦q_i¦
EDGE: lpM:L16#spatialSourceOscApo_ge_length | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | ¦q_i¦ ≤ a^osc(1 + e^osc)
EDGE: lpM:L16#spatialSourceOscEnergy_neg | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | E^osc < 0
EDGE: lpM:L16#spatialSourceOscEcc_lt_one | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | e^osc < 1
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses IsDiophantine
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses bodyVector3
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses IsSpatialMovingSolutionOn
EDGE: lpM:L1#IsSpatialNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses IsSpatialNewtonSolutionOn
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialKeplerEnergy
EDGE: lpM:s1:model#spatialMasses | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialMasses
EDGE: lpM:s1:model#SpatialMovingUniqueOn | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses SpatialMovingUniqueOn
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialOscEnergy
EDGE: lpM:L1#spatialSourceBarycentricPositions | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceBarycentricPositions
EDGE: lpM:L1#spatialSourceBarycentricVelocities | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceBarycentricVelocities
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerApo
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerAxis
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerEccVector
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceKeplerPeri
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#spatialSourceOscEccVector | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscEccVector
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses SpatialSourceOsculatingPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses spatialSourceStrongAMD
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#T19@L601-L601 | the statement uses orderedStrongThreshold
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety (KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafety.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety
NOTE: Anchor LP2. Spatial instance of the §1 conclusion (Theorem 19), with Lemma 16's clauses and N10's constant relations; A_elem is the constant A of (43). AMENDED: N8, N10.

NODE: lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger
KIND: corollary
TITLE: LP2-H: LP2 at tau = n - 1/2 (exponent 1/(2n+1))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
CONTRACT_ID: planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; spatial (d = 3); τ = n - 1/2 fixed
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ spatial phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2n+1)}): ∃ z : ℝ → spatial phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves the spatial (1) on [-T, T] without collision and agrees with every local solution; the barycentric reconstruction solves Newton's equations with masses (1, μν_i); for every t: elliptic, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, the drift bounds A_Λ√μ, A_a√μ, nA_Λ√μ of (8), (9) with d_⋆, d_pair, star distances ≥ d_⋆, pair distances ≥ d_pair; nondegenerate osculating elements with a^osc > 0, e^osc < 1, a^osc(1 - e^osc) ≤ ¦q_i¦ ≤ a^osc(1 + e^osc), ¦a^osc - a¦ + ¦e^osc - e¦ ≤ A_elem μ, perihelion and aphelion errors ≤ A_osc μ, osculating gaps ≥ d_⋆/2, d_pair/2 (as in LP1, spatial carriers)
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger
FROZEN_ANCHOR_ID: planetary.d59.spatial_strongAMD_exponentialSafety_halfInteger.v1
FROZEN_ABI_SHA256: 19e891f2585d908488b799d192ba8ab04ef0bc73374739a9e998330fad54f00b
DEPS: lpM:T19#spatial_strongAMD_exponentialSafety, lpM:s1:half-integer, lpM:s1:dioph#IsDiophantine, lpM:s1:model#Phase, lpM:s1:model#bodyVector3, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:model#spatialMasses, lpM:s1:model#SpatialMovingUniqueOn, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerApo, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T19#spatial_strongAMD_exponentialSafety | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | LP2 with τ = n - 1/2
EDGE: lpM:s1:half-integer | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | τ = n - 1/2 > n - 1 and 1/(2(τ+1)) = 1/(2n+1)
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses IsDiophantine
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses Phase
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses bodyVector3
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses IsSpatialMovingSolutionOn
EDGE: lpM:L1#IsSpatialNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses IsSpatialNewtonSolutionOn
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spaceLength
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialKeplerEnergy
EDGE: lpM:s1:model#spatialMasses | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialMasses
EDGE: lpM:s1:model#SpatialMovingUniqueOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses SpatialMovingUniqueOn
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialOscEnergy
EDGE: lpM:L1#spatialSourceBarycentricPositions | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceBarycentricPositions
EDGE: lpM:L1#spatialSourceBarycentricVelocities | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceBarycentricVelocities
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses SpatialSourceCanonicalPhase
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerApo
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerAxis
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerEccVector
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceKeplerPeri
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#spatialSourceOscEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscEccVector
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses SpatialSourceOsculatingPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses spatialSourceStrongAMD
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the statement uses orderedStrongThreshold
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger (KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyHalfInteger.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_halfInteger
NOTE: Anchor LP2-H: the half-integer corollary (MAIN §1 L93) of LP2
