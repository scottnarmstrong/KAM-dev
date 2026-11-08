NODE: lp3:s1.1#planetaryTimeExponent
KIND: definition
TITLE: planetaryTimeExponent (reused)
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L69-L70
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planetaryTimeExponent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ (typing data)
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: a_n = 2/(6n² - 3n + 14) (Nek77 (12.4), n counts planets, not total canonical pairs.)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean
FROZEN_DECL: KAM.Planetary.planetaryTimeExponent
FROZEN_ANCHOR_ID: planetary.d25.planetaryTimeExponent.v1
FROZEN_ABI_SHA256: d50f6181d0c0f28b50322ce65b1a9831d2ecd43ad5c2c9e3941105da2d0eb152
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planetaryTimeExponent (KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.planetaryTimeExponent.v1, bound as an LP anchor node (Q6); equal to the track-N partial exponents (LP3-PLAN §1.1)

NODE: lp3:s1.1#planetaryDriftExponent
KIND: definition
TITLE: planetaryDriftExponent (reused)
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L69-L70
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planetaryDriftExponent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n : ℕ (typing data)
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: b_n = 3/(6n² - 3n + 14) (Nek77 (12.5). No optimized exponent is asserted.)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean
FROZEN_DECL: KAM.Planetary.planetaryDriftExponent
FROZEN_ANCHOR_ID: planetary.d25.planetaryDriftExponent.v1
FROZEN_ABI_SHA256: 96a0f584827900cd21aa60ad82436d7ab45e5e9ea813426b73f55a4ebc50fb97
DEPS: lp3:s1.1#planetaryTimeExponent
ROUTES: -
ROUTE_FOR: -
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L69-L69 | the declaration uses planetaryTimeExponent
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planetaryDriftExponent (KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: reused frozen definition planetary.d25.planetaryDriftExponent.v1, bound as an LP anchor node (Q6); equal to the track-N partial exponents (LP3-PLAN §1.1)
