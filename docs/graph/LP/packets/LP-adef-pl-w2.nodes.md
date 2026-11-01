NODE: lpM:s1:dioph#IsDiophantine
KIND: definition
TITLE: (gamma, tau)-Diophantine vector: gamma/¦k¦_1^tau <= ¦k.omega¦ for k != 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L64-L65
PROOF_SOURCE: -
CONTRACT_ID: kam.IsDiophantine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; γ, τ : ℝ; ω : Fin n → ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, γ, τ, ω
SOURCE_CONCLUSION: γ/¦k¦_1^τ ≤ ¦k·ω¦ for every 0 ≠ k ∈ ℤ^n: the condition (5) at ω = ω(I^0)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsDiophantine.lean
FROZEN_DECL: KAM.IsDiophantine
FROZEN_ANCHOR_ID: kam.IsDiophantine.v1
FROZEN_ABI_SHA256: 24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition kam.IsDiophantine.v1 (core), bound as an LP anchor node (Q6)

NODE: lpM:s1:model#actualMasses
KIND: definition
TITLE: actual masses (m_0, mu m_1, ..., mu m_n)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L17
PROOF_SOURCE: -
CONTRACT_ID: planetary.actualMasses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ (typing data)
SOURCE_QUANTIFIERS: for every n, m_0, m, μ
SOURCE_CONCLUSION: the mass vector (m_0, μm_1, ..., μm_n); with m_0 = 1 and m = ν: star mass one and planet masses μν_i (MAIN L17, L99)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/ActualMasses.lean
FROZEN_DECL: KAM.Planetary.actualMasses
FROZEN_ANCHOR_ID: planetary.actualMasses.v1
FROZEN_ABI_SHA256: 37d0c6b0a92ae0e0c839d24e591536f697c601419b11cc5c864150814a680b60
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.actualMasses.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:L1#barycentricPositions
KIND: definition
TITLE: barycentric positions x_0 = -mu sum nu_i q_i/M, x_i = x_0 + q_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L104
PROOF_SOURCE: -
CONTRACT_ID: planetary.barycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ; q (typing data)
SOURCE_QUANTIFIERS: for every n, m_0, m, μ, q
SOURCE_CONCLUSION: x_0 = -μ Σ_i m_i q_i/(m_0 + μΣ_i m_i), x_i = x_0 + q_i (Lemma 1's explicit inverse, L104, with m_0 = 1, m = ν)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.barycentricPositions
FROZEN_ANCHOR_ID: planetary.barycentricPositions.v1
FROZEN_ABI_SHA256: 222cb379298aba4da485faf152163725857fac2c6578168946b7d79fc09910d1
DEPS: lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L1@L104-L104 | planet i's coordinate vector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.barycentricPositions.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:L1#barycentricVelocities
KIND: definition
TITLE: barycentric velocities x_0' = -mu sum p_i/m_0, x_i' = p_i/m_i
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L104
PROOF_SOURCE: -
CONTRACT_ID: planetary.barycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ; p (typing data)
SOURCE_QUANTIFIERS: for every n, m_0, m, μ, p
SOURCE_CONCLUSION: ẋ_0 = -(μ/m_0) Σ_i p_i, ẋ_i = p_i/m_i (Lemma 1's explicit inverse, L104, with m_0 = 1, m = ν)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.barycentricVelocities
FROZEN_ANCHOR_ID: planetary.barycentricVelocities.v1
FROZEN_ABI_SHA256: f0bb61447643e18562ffdde5d8ddbd4bc7ed46d52985b4fabaeab4a657a15480
DEPS: lpM:s1:model#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#bodyVector | docs/tracks/LP/source/MAIN.md#L1@L104-L104 | planet i's coordinate vector
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.barycentricVelocities.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:s1:model#IsMovingSolutionOn
KIND: definition
TITLE: z solves the moving-Sun Hamiltonian (1) on J without collision
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.IsMovingSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m : Fin n → ℝ; μ : ℝ; J : Set ℝ; z : ℝ → Phase (n*2) (typing data)
SOURCE_QUANTIFIERS: for every n, m, μ, J, z
SOURCE_CONCLUSION: z is a solution on J of Hamilton's equations of (1) (frozen movingHamiltonian with star mass and G one; the differentiability-guarded ODE predicate) and every z(t), t ∈ J, is collision-free (the open domain of (1))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean
FROZEN_DECL: KAM.Planetary.IsMovingSolutionOn
FROZEN_ANCHOR_ID: planetary.d25.IsMovingSolutionOn.v1
FROZEN_ABI_SHA256: b09b6a924851b13c3ab5d708da0cd1cbeff1a2088abc7803ffaa956c257b3708
DEPS: lpM:s1:model#Phase, lpM:s1:model#NoCollision
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the phase type
EDGE: lpM:s1:model#NoCollision | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the configurations stay collision-free
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.d25.IsMovingSolutionOn.v1 (track P), bound as an LP anchor node (Q6); movingHamiltonian and KAM.Iso.IsHamiltonianSolutionOn are typing data here

NODE: lpM:s1:model#MovingUniqueOn
KIND: definition
TITLE: z agrees with every local solution from z(0) on the overlap with J
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L24-L24
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.MovingUniqueOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ; m : Fin n → ℝ; μ : ℝ; J : Set ℝ; z : ℝ → Phase (n*2) (typing data)
SOURCE_QUANTIFIERS: for every n, m, μ, J, z
SOURCE_CONCLUSION: for every open convex U ∋ 0 and every solution w of (1) on U with w(0) = z(0), w = z on U ∩ J: uniqueness of the solution of (1) ('the unique maximal solution', MAIN L74)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean
FROZEN_DECL: KAM.Planetary.MovingUniqueOn
FROZEN_ANCHOR_ID: planetary.d25.MovingUniqueOn.v1
FROZEN_ABI_SHA256: d7cd7186c2539239b187c02b6e2523a88981cb2e7c3c158ace598e407b45089e
DEPS: lpM:s1:model#Phase, lpM:s1:model#IsMovingSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model#Phase | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the phase type
EDGE: lpM:s1:model#IsMovingSolutionOn | docs/tracks/LP/source/MAIN.md#s1@L24-L24 | the competing local solutions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.d25.MovingUniqueOn.v1 (track P), bound as an LP anchor node (Q6)

NODE: lpM:L1#IsNewtonSolutionOn
KIND: definition
TITLE: finite-interval Newton equations with masses m_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L108-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.IsNewtonSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N : ℕ; masses : Fin N → ℝ; J : Set ℝ; Q, V : ℝ → Fin N → ℝ^2 (typing data)
SOURCE_QUANTIFIERS: for every N, masses, J, Q, V
SOURCE_CONCLUSION: on J: the bodies are pairwise distinct, Q̇_i = V_i and V̇_i = Σ_{j≠i} m_j (Q_j - Q_i)/¦Q_j - Q_i¦^3 (Newton's equations of Lemma 1, L108)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean
FROZEN_DECL: KAM.Planetary.IsNewtonSolutionOn
FROZEN_ANCHOR_ID: planetary.d25.IsNewtonSolutionOn.v1
FROZEN_ABI_SHA256: a03730db1e938d4da88e154ebbb322ec514de0aa287e030a2de6e8a1625e397f
DEPS: lpM:s1:data#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data#planeLength | docs/tracks/LP/source/MAIN.md#L1@L108-L108 | the Euclidean distances ¦Q_j - Q_i¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: reused frozen definition planetary.d25.IsNewtonSolutionOn.v1 (track P), bound as an LP anchor node (Q6)
