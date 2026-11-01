NODE: lpM:T15#planar_strongAMD_exponentialSafety_noArith
KIND: theorem
TITLE: LP3-1: planar strong-AMD exponential safety without arithmetic hypothesis
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L85-L126
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L370
CONTRACT_ID: planetary.d59.planar_strongAMD_exponentialSafety_noArith
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ > 0 (no Diophantine hypothesis, no γ, τ); planar (d = 2)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-a_n}): ∃ z, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: as LP1/LP2 (the moving solution, uniqueness, Newtonian reconstruction, ellipticity, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, (9), star and pair distances, osculating clauses and half gaps) with the drifts ‖Λ(t) - Λ(0)‖ ≤ A_Λ μ^{b_n}, ‖a(t) - a(0)‖ ≤ A_a μ^{b_n}, ¦C(t) - C(0)¦ ≤ nA_Λ μ^{b_n}; a_n = planetaryTimeExponent n, b_n = planetaryDriftExponent n
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_exponentialSafety_noArith.v1
FROZEN_ABI_SHA256: b29ff03f40dc5f47b2ba0fae11d168ed7e2b83919b143d9d51cba0f1795d16f4
DEPS: lp3:s3#first-exit, lpM:L1, lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lp3:s2.4, lpM:T15#orientation, lpM:T15#chart-cover, lpM:L8, lpM:L16#sourceOscAxis_pos, lpM:L16#sourceOscPeri_le_planeLength, lpM:L16#planeLength_le_sourceOscApo, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:model#MovingUniqueOn, lpM:s1:model#Phase, lpM:s1:data#planeLength, lp3:s1.1#planetaryDriftExponent, lp3:s1.1#planetaryTimeExponent, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:elements#sourceKeplerPeri, lpM:L16:defs#sourceOscApo, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s3#first-exit | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the stopped first exit with the LP3 drift supplier
EDGE: lpM:L1 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Newtonian reconstruction (Lemma 1)
EDGE: lpM:L16 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Lemma 16: the osculating elements on Lemma 5's compact set (m = δ/2)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#half-gaps | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the osculating half gaps
EDGE: lp3:s2.4 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L359-L359 | hstop: the planar drift supplier (§2.4)
EDGE: lpM:T15#orientation | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | the orientation reduction (reused verbatim)
EDGE: lpM:T15#chart-cover | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | the Lemma 7 charts cover; C = ¦z¦²/2 in the prograde region
EDGE: lpM:L8 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the planar analytic domain (m = n)
EDGE: lpM:L16#sourceOscAxis_pos | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc > 0
EDGE: lpM:L16#sourceOscPeri_le_planeLength | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc(1 - e^osc) ≤ ¦q_i¦
EDGE: lpM:L16#planeLength_le_sourceOscApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | ¦q_i¦ ≤ a^osc(1 + e^osc)
EDGE: lpM:s1:model#actualMasses | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses actualMasses
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L115-L119 | the retained Newtonian reconstruction explicitly uses barycentricPositions
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses barycentricVelocities
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses bodyVector
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses IsMovingSolutionOn
EDGE: lpM:L1#IsNewtonSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses IsNewtonSolutionOn
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerAction
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerAxis
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerEccVector
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses keplerEnergy
EDGE: lpM:s1:model#MovingUniqueOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses MovingUniqueOn
EDGE: lpM:s1:model#Phase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses Phase
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses planeLength
EDGE: lp3:s1.1#planetaryDriftExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses planetaryDriftExponent
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses planetaryTimeExponent
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L95-L98 | all other LP1 conclusions, including adjacent separations and osculating annuli, are retained with the same adjacent upper index
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses orderedStrongThreshold
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses oscEcc
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses oscEnergy
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses SourceCanonicalPhase
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceKeplerApo
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceKeplerPeri
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscApo
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscAxis
EDGE: lpM:L16:defs#sourceOscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscEcc
EDGE: lpM:L16:defs#sourceOscEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscEccVector
EDGE: lpM:L16:defs#sourceOscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscEnergy
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceOscPeri
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses SourceOsculatingPhase
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L85-L85 | the statement uses sourceStrongAMD
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith
NOTE: Anchor LP3-1 (D64). MAIN T15 without (5), the drift supplier Lemmas 12/13 replaced by the sealed partialConvex_nekhoroshev (LP3-PLAN §1-§3); the source is LP3-PLAN (D65 minimal model; no separate LP3 source note)

NODE: lpM:T19#spatial_strongAMD_exponentialSafety_noArith
KIND: theorem
TITLE: LP3-2: spatial strong-AMD exponential safety without arithmetic hypothesis
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L128-L134
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L370
CONTRACT_ID: planetary.d59.spatial_strongAMD_exponentialSafety_noArith
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ > 0 (no Diophantine hypothesis, no γ, τ); spatial (d = 3)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ phase z_0 with ¦q_i¦ > 0, E_i < 0, a(z_0) ∈ 𝒜, Λ(z_0) ∈ Q (typing binder) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-a_n}): ∃ z, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: as LP1/LP2 (the moving solution, uniqueness, Newtonian reconstruction, ellipticity, Λ(t) ∈ Q, C(t) ≤ B(Λ(t)) - δ/2, (9), star and pair distances, osculating clauses and half gaps) with the drifts ‖Λ(t) - Λ(0)‖ ≤ A_Λ μ^{b_n}, ‖a(t) - a(0)‖ ≤ A_a μ^{b_n}, ¦C(t) - C(0)¦ ≤ nA_Λ μ^{b_n}; a_n = planetaryTimeExponent n, b_n = planetaryDriftExponent n
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean
FROZEN_DECL: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith
FROZEN_ANCHOR_ID: planetary.d59.spatial_strongAMD_exponentialSafety_noArith.v1
FROZEN_ABI_SHA256: 387059c68796b425889eee542afbb9b3989ebf833cec9afaae08be7faa931966
DEPS: lp3:s3#first-exit, lpM:L1, lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lp3:s2.5, lpM:T19#align, lpM:L17#deficit-identity, lpM:L18#rotation-invariance, lpM:L16#spatialSourceOscAxis_pos, lpM:L16#spatialSourceOscPeri_le_length, lpM:L16#spatialSourceOscApo_ge_length, lpM:L16#spatialSourceOscEnergy_neg, lpM:L16#spatialSourceOscEcc_lt_one, lpM:s1:model#Phase, lp3:s1.1#planetaryDriftExponent, lp3:s1.1#planetaryTimeExponent, lpM:s1:model#bodyVector3, lpM:s1:model#IsSpatialMovingSolutionOn, lpM:L1#IsSpatialNewtonSolutionOn, lpM:s1:data#spaceLength, lpM:s1:elements#spatialKeplerEnergy, lpM:s1:model#spatialMasses, lpM:s1:model#SpatialMovingUniqueOn, lpM:L16:defs#spatialOscEcc, lpM:L16:defs#spatialOscEnergy, lpM:L1#spatialSourceBarycentricPositions, lpM:L1#spatialSourceBarycentricVelocities, lpM:s1:elements#SpatialSourceCanonicalPhase, lpM:s1:elements#spatialSourceKeplerAction, lpM:s1:elements#spatialSourceKeplerApo, lpM:s1:elements#spatialSourceKeplerAxis, lpM:s1:elements#spatialSourceKeplerEccVector, lpM:s1:elements#spatialSourceKeplerPeri, lpM:L16:defs#spatialSourceOscApo, lpM:L16:defs#spatialSourceOscAxis, lpM:L16:defs#spatialSourceOscEcc, lpM:L16:defs#spatialSourceOscEccVector, lpM:L16:defs#spatialSourceOscEnergy, lpM:L16:defs#spatialSourceOscPeri, lpM:L16:defs#SpatialSourceOsculatingPhase, lpM:s1:elements#spatialSourceStrongAMD, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s3#first-exit | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the stopped first exit with the LP3 drift supplier
EDGE: lpM:L1 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Newtonian reconstruction (Lemma 1)
EDGE: lpM:L16 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | Lemma 16: the osculating elements on Lemma 5's compact set (m = δ/2)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#half-gaps | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | the osculating half gaps
EDGE: lp3:s2.5 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L359-L359 | hstop: the spatial drift supplier (§2.5)
EDGE: lpM:T19#align | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | the spatial rotation reduction (reused verbatim)
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | C_{e_3} = ¦z¦²/2
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L366-L366 | back to the original frame
EDGE: lpM:L16#spatialSourceOscAxis_pos | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc > 0
EDGE: lpM:L16#spatialSourceOscPeri_le_length | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | a^osc(1 - e^osc) ≤ ¦q_i¦
EDGE: lpM:L16#spatialSourceOscApo_ge_length | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | ¦q_i¦ ≤ a^osc(1 + e^osc)
EDGE: lpM:L16#spatialSourceOscEnergy_neg | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | E^osc < 0
EDGE: lpM:L16#spatialSourceOscEcc_lt_one | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L363 | e^osc < 1
EDGE: lpM:s1:model#Phase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses Phase
EDGE: lp3:s1.1#planetaryDriftExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses planetaryDriftExponent
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses planetaryTimeExponent
EDGE: lpM:s1:model#bodyVector3 | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses bodyVector3
EDGE: lpM:s1:model#IsSpatialMovingSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses IsSpatialMovingSolutionOn
EDGE: lpM:L1#IsSpatialNewtonSolutionOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses IsSpatialNewtonSolutionOn
EDGE: lpM:s1:data#spaceLength | docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L130-L134 | the spatial LP2 statement is retained except for the arithmetic premise and time/drift exponents; its physical Euclidean lengths are unchanged
EDGE: lpM:s1:elements#spatialKeplerEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialKeplerEnergy
EDGE: lpM:s1:model#spatialMasses | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialMasses
EDGE: lpM:s1:model#SpatialMovingUniqueOn | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses SpatialMovingUniqueOn
EDGE: lpM:L16:defs#spatialOscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialOscEcc
EDGE: lpM:L16:defs#spatialOscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialOscEnergy
EDGE: lpM:L1#spatialSourceBarycentricPositions | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceBarycentricPositions
EDGE: lpM:L1#spatialSourceBarycentricVelocities | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceBarycentricVelocities
EDGE: lpM:s1:elements#SpatialSourceCanonicalPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L130-L134 | the spatial physical initial-state carrier and remaining LP2 premises are retained
EDGE: lpM:s1:elements#spatialSourceKeplerAction | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerAction
EDGE: lpM:s1:elements#spatialSourceKeplerApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerApo
EDGE: lpM:s1:elements#spatialSourceKeplerAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerAxis
EDGE: lpM:s1:elements#spatialSourceKeplerEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerEccVector
EDGE: lpM:s1:elements#spatialSourceKeplerPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceKeplerPeri
EDGE: lpM:L16:defs#spatialSourceOscApo | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscApo
EDGE: lpM:L16:defs#spatialSourceOscAxis | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscAxis
EDGE: lpM:L16:defs#spatialSourceOscEcc | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscEcc
EDGE: lpM:L16:defs#spatialSourceOscEccVector | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscEccVector
EDGE: lpM:L16:defs#spatialSourceOscEnergy | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscEnergy
EDGE: lpM:L16:defs#spatialSourceOscPeri | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceOscPeri
EDGE: lpM:L16:defs#SpatialSourceOsculatingPhase | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses SpatialSourceOsculatingPhase
EDGE: lpM:s1:elements#spatialSourceStrongAMD | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses spatialSourceStrongAMD
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses AdjIdx
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses AdjIdx.upperIdx
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses chamber
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/lp3/LP3-PLAN.md#s3@L128-L128 | the statement uses orderedStrongThreshold
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith (KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith
NOTE: Anchor LP3-2 (D64). MAIN T19 without (5), drift supplier replaced as in LP3-1 (LP3-PLAN §2.5, §3)
