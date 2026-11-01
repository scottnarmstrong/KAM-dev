NODE: lpM:T15#planar_strongAMD_exponentialSafety
KIND: theorem
TITLE: LP1: planar strong-AMD exponential safety (Theorem 15 with Lemma 16)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L502-L506
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
CONTRACT_ID: planetary.d59.planar_strongAMD_exponentialSafety
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; τ > n - 1; planar (d = 2)
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (all positive, with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ planar phase z_0 with ¦q_i¦ > 0, E_i < 0 for every i, a(z_0) ∈ 𝒜, (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (a typing binder; it follows from a(z_0) ∈ 𝒜) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2(τ+1))}): ∃ z : ℝ → phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves (1) on [-T, T] without collision (IsMovingSolutionOn) and agrees with every local solution (MovingUniqueOn); the barycentric reconstruction solves Newton's equations with masses (1, μν_i) on [-T, T]; for every t: ¦q_i¦ > 0, E_i < 0; Λ(t) ∈ Q and C(t) ≤ B(Λ(t)) - δ/2; ‖Λ(t) - Λ(0)‖ ≤ A_Λ√μ; ‖a(t) - a(0)‖ ≤ A_a√μ; ¦C(t) - C(0)¦ ≤ nA_Λ√μ; a_i(1 - e_i) ≥ d_⋆; a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair; ¦q_i¦ ≥ d_⋆; ¦q_i - q_j¦ ≥ d_pair for i ≠ j; the osculating elements are nondegenerate (E^osc < 0, e^osc < 1, a source osculating phase) with E_i^osc < 0, a_i^osc > 0, e_i^osc < 1, a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ ≤ a_i^osc(1 + e_i^osc), ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ ≤ A_elem μ; ¦a_i^osc(1 ∓ e_i^osc) - a_i(1 ∓ e_i)¦ ≤ A_osc μ; a_i^osc(1 - e_i^osc) ≥ d_⋆/2; adjacent osculating gaps ≥ d_pair/2
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ, τ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_exponentialSafety.v1
FROZEN_ABI_SHA256: a70e0b6a009377d9cb3c49a23bcec64e175853c0eb2cb59d5a456d29df729591
DEPS: lpM:T15, lpM:T15#reconstruction, lpM:T15#osculating, lpM:L16#mu0-choice, lpM:L16#sourceOscAxis_pos, lpM:L16#sourceOscPeri_le_planeLength, lpM:L16#planeLength_le_sourceOscApo, lpM:s1:dioph#IsDiophantine, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:model#MovingUniqueOn, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:elements#sourceKeplerPeri, lpM:L16:defs#sourceOscApo, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T15 | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | LP1 is Theorem 15 (the §1 conclusion in d = 2)
EDGE: lpM:T15#reconstruction | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the Newtonian reconstruction clause (Lemma 1)
EDGE: lpM:T15#osculating | docs/tracks/LP/source/MAIN.md#T15@L506-L506 | the osculating clauses, including the first estimate of (43) (A_elem)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | the stated constant relations A_osc μ_0 ≤ d_⋆/2, 2A_osc μ_0 ≤ d_pair/2 (N10)
EDGE: lpM:L16#sourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a_i^osc > 0 on the osculating carrier
EDGE: lpM:L16#sourceOscPeri_le_planeLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | a_i^osc(1 - e_i^osc) ≤ ¦q_i¦
EDGE: lpM:L16#planeLength_le_sourceOscApo | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | ¦q_i¦ ≤ a_i^osc(1 + e_i^osc)
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the Diophantine premise (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i
EDGE: lpM:s1:model#actualMasses | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the Newtonian masses (1, μν_i)
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the reconstructed barycentric positions
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the reconstructed barycentric velocities
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the positions q_i
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | z solves (1) on [-T, T] without collision
EDGE: lpM:L1#IsNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the reconstructed motion solves Newton's equations
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the actions Λ(z)
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the axes a_i
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the eccentricities e_i = ¦e_i¦
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | negative Kepler energies
EDGE: lpM:s1:model#MovingUniqueOn | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | uniqueness against every local solution
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | planar phases
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | Euclidean lengths
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the adjacent pairs of (9)
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the upper index of an adjacent pair
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | I(t) ∈ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | B(I) in (6) and (8)
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the osculating carrier condition e^osc < 1
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the osculating carrier condition E^osc < 0
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the canonical carrier
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | canonical aphelia
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | canonical perihelia
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating aphelia
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating axes
EDGE: lpM:L16:defs#sourceOscEcc | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating eccentricities
EDGE: lpM:L16:defs#sourceOscEccVector | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating eccentricity vectors
EDGE: lpM:L16:defs#sourceOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating energies
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | osculating perihelia
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | the osculating carrier
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#s1@L69-L69 | C in (6) and (8)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafety.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety
NOTE: Anchor LP1. Planar instance of the §1 conclusion (Theorem 15), with Lemma 16's elliptic, tangency and (43) clauses and N10's constant relations; A_elem is the constant A of (43) (MAIN's §1 list omits it). The premise Λ(z_0) ∈ Q is a typing binder that the source derives from a(0) ∈ 𝒜. AMENDED: N8, N10.

NODE: lpM:T15#planar_strongAMD_exponentialSafety_halfInteger
KIND: corollary
TITLE: LP1-H: LP1 at tau = n - 1/2 (exponent 1/(2n+1))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
CONTRACT_ID: planetary.d59.planar_strongAMD_exponentialSafety_halfInteger
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2; ν_i > 0, ∃ i ν_i = 1, ν_i ≤ 1; 𝒜 compact with 0 < a_i and a_i < a_j for i < j on 𝒜; δ, γ > 0; planar (d = 2); τ = n - 1/2 fixed
SOURCE_QUANTIFIERS: ∃ μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem > 0 (all positive, with A_osc μ_0 ≤ d_⋆/2 and 2A_osc μ_0 ≤ d_pair/2); then ∀ 0 < μ ≤ μ_0, ∀ planar phase z_0 with ¦q_i¦ > 0, E_i < 0 for every i, a(z_0) ∈ 𝒜, (5) with τ = n - 1/2 at ω(I^0) = (ν_i^3/Λ_i^3)_i, Λ(z_0) ∈ Q (a typing binder; it follows from a(z_0) ∈ 𝒜) and C(z_0) ≤ B(Λ(z_0)) - δ; with T = T_0 exp(cμ^{-1/(2n+1)}): ∃ z : ℝ → phases, and ∀ t ∈ [-T, T]
SOURCE_CONCLUSION: z(0) = z_0; z solves (1) on [-T, T] without collision (IsMovingSolutionOn) and agrees with every local solution (MovingUniqueOn); the barycentric reconstruction solves Newton's equations with masses (1, μν_i) on [-T, T]; for every t: ¦q_i¦ > 0, E_i < 0; Λ(t) ∈ Q and C(t) ≤ B(Λ(t)) - δ/2; ‖Λ(t) - Λ(0)‖ ≤ A_Λ√μ; ‖a(t) - a(0)‖ ≤ A_a√μ; ¦C(t) - C(0)¦ ≤ nA_Λ√μ; a_i(1 - e_i) ≥ d_⋆; a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair; ¦q_i¦ ≥ d_⋆; ¦q_i - q_j¦ ≥ d_pair for i ≠ j; the osculating elements are nondegenerate (E^osc < 0, e^osc < 1, a source osculating phase) with E_i^osc < 0, a_i^osc > 0, e_i^osc < 1, a_i^osc(1 - e_i^osc) ≤ ¦q_i¦ ≤ a_i^osc(1 + e_i^osc), ¦a_i^osc - a_i¦ + ¦e_i^osc - e_i¦ ≤ A_elem μ; ¦a_i^osc(1 ∓ e_i^osc) - a_i(1 ∓ e_i)¦ ≤ A_osc μ; a_i^osc(1 - e_i^osc) ≥ d_⋆/2; adjacent osculating gaps ≥ d_pair/2
CONSTANT_SCOPE: μ_0, c, T_0, A_Λ, A_a, d_⋆, d_pair, A_osc, A_elem depend only on (n, ν, 𝒜, δ, γ) and are chosen before μ and z_0
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger
FROZEN_ANCHOR_ID: planetary.d59.planar_strongAMD_exponentialSafety_halfInteger.v1
FROZEN_ABI_SHA256: 50df22c53395dc90c388a4d62811762b288e72721e54c799949456bb67897574
DEPS: lpM:T15#planar_strongAMD_exponentialSafety, lpM:s1:half-integer, lpM:s1:dioph#IsDiophantine, lpM:s1:model#actualMasses, lpM:L1#barycentricPositions, lpM:L1#barycentricVelocities, lpM:s1:model#bodyVector, lpM:s1:model#IsMovingSolutionOn, lpM:L1#IsNewtonSolutionOn, lpM:s1:elements#keplerAction, lpM:s1:elements#keplerAxis, lpM:s1:elements#keplerEccVector, lpM:s1:elements#keplerEnergy, lpM:s1:model#MovingUniqueOn, lpM:s1:model#Phase, lpM:s1:data#planeLength, lpM:s1:thresholds#AdjIdx, lpM:s1:thresholds#AdjIdx.upperIdx, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:L16:defs#oscEcc, lpM:L16:defs#oscEnergy, lpM:s1:elements#SourceCanonicalPhase, lpM:s1:elements#sourceKeplerApo, lpM:s1:elements#sourceKeplerPeri, lpM:L16:defs#sourceOscApo, lpM:L16:defs#sourceOscAxis, lpM:L16:defs#sourceOscEcc, lpM:L16:defs#sourceOscEccVector, lpM:L16:defs#sourceOscEnergy, lpM:L16:defs#sourceOscPeri, lpM:L16:defs#SourceOsculatingPhase, lpM:s1:elements#sourceStrongAMD
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T15#planar_strongAMD_exponentialSafety | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | LP1 with τ = n - 1/2
EDGE: lpM:s1:half-integer | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | τ = n - 1/2 > n - 1 and 1/(2(τ+1)) = 1/(2n+1)
EDGE: lpM:s1:dioph#IsDiophantine | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the Diophantine premise (5) at ω(I^0) = (ν_i^3/Λ_i^3)_i
EDGE: lpM:s1:model#actualMasses | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the Newtonian masses (1, μν_i)
EDGE: lpM:L1#barycentricPositions | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the reconstructed barycentric positions
EDGE: lpM:L1#barycentricVelocities | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the reconstructed barycentric velocities
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the positions q_i
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | z solves (1) on [-T, T] without collision
EDGE: lpM:L1#IsNewtonSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the reconstructed motion solves Newton's equations
EDGE: lpM:s1:elements#keplerAction | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the actions Λ(z)
EDGE: lpM:s1:elements#keplerAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the axes a_i
EDGE: lpM:s1:elements#keplerEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the eccentricities e_i = ¦e_i¦
EDGE: lpM:s1:elements#keplerEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | negative Kepler energies
EDGE: lpM:s1:model#MovingUniqueOn | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | uniqueness against every local solution
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | planar phases
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | Euclidean lengths
EDGE: lpM:s1:thresholds#AdjIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the adjacent pairs of (9)
EDGE: lpM:s1:thresholds#AdjIdx.upperIdx | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the upper index of an adjacent pair
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | I(t) ∈ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | B(I) in (6) and (8)
EDGE: lpM:L16:defs#oscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the osculating carrier condition e^osc < 1
EDGE: lpM:L16:defs#oscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the osculating carrier condition E^osc < 0
EDGE: lpM:s1:elements#SourceCanonicalPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the canonical carrier
EDGE: lpM:s1:elements#sourceKeplerApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | canonical aphelia
EDGE: lpM:s1:elements#sourceKeplerPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | canonical perihelia
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating aphelia
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating axes
EDGE: lpM:L16:defs#sourceOscEcc | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating eccentricities
EDGE: lpM:L16:defs#sourceOscEccVector | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating eccentricity vectors
EDGE: lpM:L16:defs#sourceOscEnergy | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating energies
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | osculating perihelia
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | the osculating carrier
EDGE: lpM:s1:elements#sourceStrongAMD | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | C in (6) and (8)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger (KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyHalfInteger.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_halfInteger
NOTE: Anchor LP1-H: the half-integer corollary (MAIN §1 L93) of LP1

NODE: lpM:L16#sourceOscAxis_pos
KIND: lemma
TITLE: a_i^osc > 0 on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.sourceOscAxis_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: 0 < a_i^osc
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscAxis_pos
FROZEN_ANCHOR_ID: planetary.d59.sourceOscAxis_pos.v1
FROZEN_ABI_SHA256: 5d18a64bd0fce6435020af9cb258359eeb057b5be6b9ee9e829ad11a3249b87c
DEPS: lpM:L16:defs, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L516-L516 | a^osc = -k_i/(2E^osc) with k_i = 1 + μν_i > 0 and E^osc < 0
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscAxis | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | a^osc occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscAxis_pos (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscAxisPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceOscAxis_pos
NOTE: -

NODE: lpM:L16#sourceOscPeri_pos
KIND: lemma
TITLE: a_i^osc(1 - e_i^osc) > 0 on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L520-L520
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.sourceOscPeri_pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: 0 < a_i^osc(1 - e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscPeri_pos
FROZEN_ANCHOR_ID: planetary.d59.sourceOscPeri_pos.v1
FROZEN_ABI_SHA256: 0c5150d43260c99afa47b998ab7a3e9f499a514e1becaf0f34eb92d66e77bf59
DEPS: lpM:L16#sourceOscAxis_pos, lpM:L16:defs, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscPeri
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#sourceOscAxis_pos | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | a^osc > 0
EDGE: lpM:L16:defs | docs/tracks/LP/source/MAIN.md#L16@L518-L518 | e^osc < 1 on the carrier
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L520-L520 | the osculating perihelion occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscPeri_pos (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriPos.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_pos
NOTE: -

NODE: lpM:L16#sourceOscPeri_le_planeLength
KIND: lemma
TITLE: a_i^osc(1 - e_i^osc) <= ¦q_i¦ on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.sourceOscPeri_le_planeLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: a_i^osc(1 - e_i^osc) ≤ ¦q_i¦
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength
FROZEN_ANCHOR_ID: planetary.d59.sourceOscPeri_le_planeLength.v1
FROZEN_ABI_SHA256: 1ce0a7aed32a3f144a29bed616e0d29c34606699a68fd2123a048048ffc3f040
DEPS: lpM:L16#tangent-ellipse, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscPeri, lpM:s1:data#planeLength, lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscPeri | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the osculating perihelion occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the position q_i occurs in the statement
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.sourceOscPeri_le_planeLength (KAM/Frozen/Planetary/StrongAMD/Theorems/SourceOscPeriLePlaneLength.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.sourceOscPeri_le_planeLength
NOTE: -

NODE: lpM:L16#planeLength_le_sourceOscApo
KIND: lemma
TITLE: ¦q_i¦ <= a_i^osc(1 + e_i^osc) on source osculating phases
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L525-L525
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
CONTRACT_ID: planetary.d59.planeLength_le_sourceOscApo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: planar source osculating phase z: ν_i > 0, μ > 0 and, for every i, ¦q_i¦ > 0, E_i^osc < 0, e_i^osc < 1 (SourceOsculatingPhase n ν μ)
SOURCE_QUANTIFIERS: for every n, ν, μ, source osculating phase z and i
SOURCE_CONCLUSION: ¦q_i¦ ≤ a_i^osc(1 + e_i^osc)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean
FROZEN_DECL: KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo
FROZEN_ANCHOR_ID: planetary.d59.planeLength_le_sourceOscApo.v1
FROZEN_ABI_SHA256: fffced58bd764c2961e056add565ae5347a7c06a8215969009b92f957225f8f3
DEPS: lpM:L16#tangent-ellipse, lpM:L16:defs#SourceOsculatingPhase, lpM:L16:defs#sourceOscApo, lpM:s1:data#planeLength, lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16#tangent-ellipse | docs/tracks/LP/source/MAIN.md#L16@L527-L527 | Lemma 2 with parameter k_i: the ellipse contains the position
EDGE: lpM:L16:defs#SourceOsculatingPhase | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the statement quantifies over source osculating phases
EDGE: lpM:L16:defs#sourceOscApo | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the osculating aphelion occurs
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | Euclidean lengths ¦·¦ occur in the statement
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L16@L525-L525 | the position q_i occurs in the statement
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StrongAMD.planeLength_le_sourceOscApo (KAM/Frozen/Planetary/StrongAMD/Theorems/PlaneLengthLeSourceOscApo.lean)
LEAN_NOTE: sealed frozen theorem (manifest SEALED, D62); proof by exact KAM.Provider.Planetary.StrongAMD.planeLength_le_sourceOscApo
NOTE: -
