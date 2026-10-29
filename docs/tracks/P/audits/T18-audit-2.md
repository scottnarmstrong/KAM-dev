# T18 independent package audit 2 — delta audit

**Overall: PASS WITH NOTES. Round 1 F1 is CLOSED.** `as_in`, `as_pi`, and `as_c` now contain the complete graph-node conclusions, including the formerly omitted source clauses. `as_ent` has exactly its Round 1 statement. The four local nodes pass; this infrastructure package has no frozen anchor to seal. Mass-ratio uniformity, determinant and general-axis homogeneity remain T19's work.

## Scope and pinned inputs

Independent tier-2 source correspondence/package delta audit, 2026-10-28, in `/root/code/KAM-inp-p11c-t18`. User instructions override the generic brief's MAIN-worktree destination. Only this report is a lasting edit; disposable evidence is in this worktree's `.lake/abi-scratch/` and removed after validation. No production repair, git mutation, frozen/manifest edit, or generated-root regeneration.

Audited HEAD: `8d9661151e8698898da4f393fe7715ee38d239e7`; Round 1 implementation: `0b7c10a700ade312a6c5882d5a3baa8c7b0a055a`; pre-fix report commit: `3a3bb5b0`. Fix `8d966115` changes four scoped files, **41 insertions, 8 deletions**, with no new declarations. `inp` resolved to `fd85905402ce93e14121657af8bd95cde40d35e4` at inspection. The required `git diff inp...HEAD` comparison warns of multiple merge bases and uses `a73d2767362222d4a6d0610ce6bf6be553301a4e`; inherited changes are disclosed below. The delta and all ten scoped module surfaces were inspected. Unchanged helper mathematics retains Round 1's audit disposition; all scoped exports receive fresh axiom and kernel checks.

Authority read: AGENTS.md, PLAN, DECISIONS, the package brief, T18-handoff AUDIT FOCUS, `.drafts/handoff-T18.md` Round 2 fix, Round 1 audit, Track P statement, P11C design row T18 and node table, design audit 1, graph source conclusions and blueprint Part 11b. The signature file contains no T18 node exports. Exact frozen/provider equality and prospective seal probes are **N/A**, not successful seal checks.

| Authority | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11C-LEAN-DESIGN.md` | `8693b4c33b78a6d52c251999b15e08fc68d588b9250e2e4bbe3e64b4510a6437` |
| `docs/graph/P/DEPGRAPH.md` | `dad2bca68bd1a99f5f79d4d1481f518914ca492a12593718d6e9622e9a7b2582` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7` |

### Scoped file manifest

Paths below are under `KAM/Planetary/PlanarTorsion/`.

| File | Lines | Maximum width | SHA-256 |
|---|---:|---:|---|
| `AsymptoticEntries.lean` | 33 | 98 | `58b3c16ffe84a4022600b968ab9f7a67280d32677cfb6c24c3f26d025d13658e` |
| `AsymptoticEntries/Calculus.lean` | 97 | 96 | `b9d5a807fe4f63c37a053d6781dd103853db550c06a29f05f121596f47d661c7` |
| `AsymptoticEntries/CoeffEq.lean` | 137 | 97 | `b14c15c3405d84534b16943a991fc0b6ea1096d39f47591088214ba171e3dae3` |
| `AsymptoticEntries/Coeffs.lean` | 136 | 99 | `4d070d32660cd55f150ec4508265f7b1786e4e3a08fdee752b6b2b3ead879501` |
| `AsymptoticEntries/Entries.lean` | 115 | 97 | `4b4c3dafc15a673b9abefa7294fac41e9d5bd63bc9070e3805b985799e48db09` |
| `AsymptoticEntries/EntryBounds.lean` | 149 | 99 | `57a5142aa9d3984c0d0a5eb36f778ac91c5b85610d1a0bb3d4ffa9125df43c37` |
| `AsymptoticEntries/Inputs.lean` | 218 | 100 | `ff504117597939a6a74c5bc15600577460754cd9e0cc3289b732871862e6107e` |
| `AsymptoticEntries/Leading.lean` | 121 | 96 | `d65a48a256852c728a376a415d6830fcecac889b829cb68501379f31d5b5b4c5` |
| `AsymptoticEntries/Pair.lean` | 51 | 99 | `ec8d9e3bbd0637ade79c9974f6bcac304ac58ea1d196b6a80531532f5d374164` |
| `AsymptoticEntries/Projector.lean` | 145 | 99 | `5e98c2763f9a56191e8bfe91538f7ba7cbb3bc121f9ab6372a6195a439616dbc` |

## F1 closure and source comparison

Each new source clause is appended last, preserving the old leading conjuncts. The source's multiplicative errors are expressed as subtraction of the leading monomial with an absolute Big-O remainder; this is equivalent for fixed positive physical data and nonzero leading constants. Every filter is `𝓝[>] 0 = nhdsWithin 0 (Ioi 0)`; fractional powers are real powers. Constants and thresholds are chosen after fixing `p` and before alpha. No uniformity beyond that order is claimed.

| Graph node | Export, location | Verdict | Complete conclusion checked |
|---|---|---|---|
| `stepP:p11b:as-in` | `KAM.Planetary.as_in`, Inputs:124–141 | PASS | Q00 leading −3Gm₂/(8√κ), exponent 3/2, remainder 7/2; Q11 leading −3Gm₁/(8√κ), exponent 2, remainder 4; Q01 order 11/4; Delta negative eventually (hence nonzero); Delta/Q00−1 order 1/2; **scalar a leading 3Gm₁m₂/8 at order 2, remainder 4; scalar b leading 15Gm₁m₂/32 at order 3, remainder 5**. |
| `stepP:p11b:as-pi` | `KAM.Planetary.as_pi`, Projector:76–89 | PASS | Eventual absolute-ratio bound, 0≤pi22≤Q12²/Delta², trace pi11=1−pi22; orders 5/4 and 5/2; **eventual signed identity pi12=−Q12/sqrt(Delta²+4Q12²)**. |
| `stepP:p11b:as-c` | `KAM.Planetary.as_c`, Coeffs:62–85 | PASS | Six c estimates and **all six raw combinations**, enumerated below. |
| `stepP:p11b:as-ent` | `KAM.Planetary.as_ent`, Entries:32–44 | PASS | Statement byte-identical to Round 1: beta00−8c1 and beta01−4c3 order 7/2, beta11−8c2 order 4; final leading coefficients 3m₂/(4m₀m₁), −9/(4m₀), −3m₁/(m₀m₂), remainders 3,7/2,4. Only two proof destructuring patterns gained a trailing wildcard. |

Graph authorities are DEPGRAPH.md:31313,31342,31370,31400; raw blueprint lines 240–246. For `as_in`, the scalar expressions are exactly the `A` and `B` in SpectralAdapter.lean:37–42 specialized to `![α,1]`, not newly chosen surrogates. Q's identities with these scalars and the action denominators follow directly from that existing definition. The sign statement implies the source's nonzero Delta clause. The projector's discriminant is exactly the source's R. The ratio comparison estimates remain proved in the existing projector proof; the signed formula is now in the named conclusion, not merely a helper.

With `P_i(α) := p11c_pairCoeffs α i`, the appended `as_c` clauses are:

| Source raw expression | Lean expression | Leading coefficient/order | Absolute remainder |
|---|---|---|---|
| p₁−A/4 | P₂−P₀/4 | −3/32, order 2 | O(α⁴) |
| p₂−A/4 | P₃−P₀/4 | 3/8, order 2 | O(α⁴) |
| p₃ | P₄ | 9/16, order 2 | O(α⁴) |
| p₄ | P₅ | zero | O(α⁴) |
| p₅−B/8 | P₆−P₁/8 | zero | O(α³) |
| p₆−B/8 | P₇−P₁/8 | zero | O(α³) |

The first six conjuncts retain c₁ = 3m₂/(32m₀m₁) α + O(α³), c₂ = −3m₁/(8m₀m₂) α² + O(α⁴), c₃ = −9/(16m₀) α^(3/2) + O(α^(7/2)), and c₄,c₅,c₆ of orders 7/2,9/4,11/4. Thus every scalar constant, sign and exponent agrees with blueprint:244–245 and g₀=G/κ=1/m₀.

**Mass/index check:** Setting.lean:31–41 has central mass `p.m0`, planet masses `p.m : Fin 2 → ℝ`, κ=`p.G*p.m0`, and actions `p.m i * sqrt(κ*a i)`. Therefore Lean planet indices 0,1 (including proof-local `hm0`, `hm1`) are source planets 1,2, respectively. They are not central/first-planet indices. At axes `![α,1]`, actions are Λ₁=`p.m 0*sqrt(κ α)` and Λ₂=`p.m 1*sqrt κ`. Pair indices 0..7 mean A,B,p₁,..,p₆; coefficient indices 0..5 mean c₁,..,c₆; matrix indices 0,1 mean source indices 1,2. All restored mass products and unchanged denominators follow this dictionary exactly.

**Independent refutation pass:** attempted to recover each alleged missing clause by direct projection from the actual node export, without reconstructing it from helpers. Fresh Lean examples project both scalar remainders, the signed projector identity, and each of the six raw combination estimates. All succeed. Four further examples apply the exports at their entire declared types. Mechanical old/new statement comparison finds exactly `as_in`, `as_pi`, `as_c` changed; each preserves the old initial clauses and introduces no binder. Thus F1 is closed by theorem conclusions themselves. No new finding survived this pass.

## Expanded binders and definitions

The following rows apply independently to each named export; `p` precedes `hp` (the section variable in Inputs is included in the actual declaration).

| Export | Expanded binder | Bin | Source |
|---|---|---|---|
| `as_in` | `p : PlanarData` | TYPING | fixed physical data, Setting:31–34 |
| `as_in` | `hp.1 : 0 < p.G` | STANDING | blueprint:231 |
| `as_in` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231 |
| `as_in` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, source m₁ |
| `as_in` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, source m₂ |
| `as_pi` | `p : PlanarData` | TYPING | fixed physical data, Setting:31–34 |
| `as_pi` | `hp.1 : 0 < p.G` | STANDING | blueprint:231 |
| `as_pi` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231 |
| `as_pi` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, source m₁ |
| `as_pi` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, source m₂ |
| `as_c` | `p : PlanarData` | TYPING | fixed physical data, Setting:31–34 |
| `as_c` | `hp.1 : 0 < p.G` | STANDING | blueprint:231 |
| `as_c` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231 |
| `as_c` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, source m₁ |
| `as_c` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, source m₂ |
| `as_ent` | `p : PlanarData` | TYPING | fixed physical data, Setting:31–34 |
| `as_ent` | `hp.1 : 0 < p.G` | STANDING | blueprint:231 |
| `as_ent` | `hp.2.1 : 0 < p.m0` | STANDING | blueprint:231 |
| `as_ent` | `hp.2.2 0 : 0 < p.m 0` | STANDING | blueprint:231, source m₁ |
| `as_ent` | `hp.2.2 1 : 0 < p.m 1` | STANDING | blueprint:231, source m₂ |

Per export: TYPING=1, STANDING=4, SOURCE=0 additional, RULED=0, EXCESS=0. Aggregate: 4,16,0,0,0. No instance binder or result-shaped bundled assumption. The restored raw estimates need no extra premise; `hp` is unchanged positivity only.

**Definition classification:** zero new/changed `def`, `abbrev`, `structure`, instances, or notation in T18; all 65 declarations are theorems. BODY_MATCH, PUBLIC_CARRIER, WELL_DEFINEDNESS, CHARACTERIZATION and CHOICE_INDEPENDENCE are N/A for new definitions. Existing actions/Q/projector/coefficient/beta definitions retain their original bodies. Local proof bindings do not redefine public objects. The transitive KAM import scan visits 213 modules: no provider, no frozen theorem, 58 frozen definitions, each with exactly one manifest owner and state SEALED. This is not a fresh mathematical re-audit of T4/T6/T12/T13 or all imported definitions.

## Declaration ledger

All names below are in `KAM.Planetary`; paths are within `AsymptoticEntries/`. Unchanged helper statements and proofs retain Round 1's detailed source classification; they were not silently promoted to graph-node exports. Every row has fresh clean axiom closure and is included in the module replay.

| Node served | Declaration | Location | Delta verdict |
|---|---|---|---|
| all four local nodes | `p11cAe_pos` | Calculus.lean:23 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_lt_one` | Calculus.lean:25 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_mul` | Calculus.lean:29 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_const_mul` | Calculus.lean:36 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_div` | Calculus.lean:41 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_natPow` | Calculus.lean:51 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_sqrt` | Calculus.lean:55 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_lower` | Calculus.lean:60 | PASS; unchanged statement/proof |
| as-c | `p11cAe_act0` | CoeffEq.lean:28 | PASS; unchanged statement/proof |
| as-c | `p11cAe_act1` | CoeffEq.lean:33 | PASS; unchanged statement/proof |
| as-c | `p11cAe_sqrt_rpow` | CoeffEq.lean:37 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c0_eq` | CoeffEq.lean:41 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c1_eq` | CoeffEq.lean:52 | PASS; unchanged statement/proof |
| as-c | `p11cAe_act_mul` | CoeffEq.lean:63 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c2_eq` | CoeffEq.lean:71 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c3_eq` | CoeffEq.lean:82 | PASS; unchanged statement/proof |
| as-c | `p11cAe_den` | CoeffEq.lean:93 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c_rpow` | CoeffEq.lean:107 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c4_eq` | CoeffEq.lean:117 | PASS; unchanged statement/proof |
| as-c | `p11cAe_c5_eq` | CoeffEq.lean:126 | PASS; unchanged statement/proof |
| as-c | `p11cAe_X0` | Coeffs.lean:29 | PASS; unchanged statement/proof |
| as-c | `p11cAe_X1` | Coeffs.lean:36 | PASS; unchanged statement/proof |
| as-c | `p11cAe_X3` | Coeffs.lean:41 | PASS; unchanged statement/proof |
| as-c | `p11cAe_A6` | Coeffs.lean:44 | PASS; unchanged statement/proof |
| as-c | `p11cAe_A7` | Coeffs.lean:47 | PASS; unchanged statement/proof |
| as-c | `p11cAe_A1` | Coeffs.lean:50 | PASS; unchanged statement/proof |
| as-c | `p11cAe_X4` | Coeffs.lean:53 | PASS; unchanged statement/proof |
| as-c | `p11cAe_X5` | Coeffs.lean:57 | PASS; unchanged statement/proof |
| as-c | `as_c` | Coeffs.lean:62 | PASS; full source conclusion |
| as-ent | `as_ent` | Entries.lean:32 | PASS; unchanged statement, wildcard-only proof edit |
| as-ent | `p11cAe_mono3` | EntryBounds.lean:27 | PASS; unchanged statement/proof |
| as-ent | `p11cAe_entA` | EntryBounds.lean:58 | PASS; unchanged statement/proof |
| as-ent | `p11cAe_entE` | EntryBounds.lean:85 | PASS; unchanged statement/proof |
| as-ent | `p11cAe_entB` | EntryBounds.lean:112 | PASS; unchanged statement/proof |
| as-in | `p11cAe_Q00` | Inputs.lean:29 | PASS; unchanged statement/proof |
| as-in | `p11cAe_Q11` | Inputs.lean:42 | PASS; unchanged statement/proof |
| as-in | `p11cAe_Q01` | Inputs.lean:52 | PASS; unchanged statement/proof |
| as-in | `p11cAe_id` | Inputs.lean:81 | PASS; unchanged statement/proof |
| as-in | `p11cAe_sqrt_isBigO` | Inputs.lean:84 | PASS; unchanged statement/proof |
| as-in | `p11cAe_rpow_isBigO_of_lower` | Inputs.lean:87 | PASS; unchanged statement/proof |
| as-in | `p11cAe_lead_isBigO` | Inputs.lean:96 | PASS; unchanged statement/proof |
| as-in | `p11cAe_b1_lead` | Inputs.lean:101 | PASS; unchanged statement/proof |
| as-in | `p11cAe_b2_lead` | Inputs.lean:105 | PASS; unchanged statement/proof |
| as-in | `p11cAe_lead_isBigO'` | Inputs.lean:109 | PASS; unchanged statement/proof |
| as-in | `p11cAe_congr_exp` | Inputs.lean:115 | PASS; unchanged statement/proof |
| as-in | `p11cAe_rpow_three_half` | Inputs.lean:119 | PASS; unchanged statement/proof |
| as-in | `as_in` | Inputs.lean:124 | PASS; full source conclusion |
| as-in/as-c | `p11cAe_npow_le` | Leading.lean:25 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_pair_lead` | Leading.lean:34 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_A` | Leading.lean:44 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_B` | Leading.lean:50 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_p1` | Leading.lean:57 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_p2` | Leading.lean:63 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_p3` | Leading.lean:69 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_p4` | Leading.lean:75 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_p5` | Leading.lean:81 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_p6` | Leading.lean:88 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_b1` | Leading.lean:96 | PASS; unchanged statement/proof |
| as-in/as-c | `p11cAe_b2` | Leading.lean:108 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_rpow_isBigO` | Pair.lean:26 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_pow_mul_isBigO` | Pair.lean:35 | PASS; unchanged statement/proof |
| all four local nodes | `p11cAe_pair` | Pair.lean:43 | PASS; unchanged statement/proof |
| as-pi | `p11cAe_proj_exact` | Projector.lean:26 | PASS; unchanged statement/proof |
| as-pi | `p11cAe_delta_lower` | Projector.lean:59 | PASS; unchanged statement/proof |
| as-pi | `as_pi` | Projector.lean:76 | PASS; full source conclusion |

## Verification receipts

All Lean/Lake commands ran serially with `LEAN_NUM_THREADS=1`; no overlapping build/probe/replay, cleaning, dependency fetching, heartbeat override or Mathlib source edit. Scratch probes are removed after transcription.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t18 KAM.Planetary.PlanarTorsion.AsymptoticEntries
```

Exit **0**. The gate executes `nice -n 5 lake build` internally. Exact receipt:

```text
[inp-gate] slot 1 acquired 23:49:43 for KAM.Planetary.PlanarTorsion.AsymptoticEntries
Build completed successfully (9259 jobs).
```

Warnings remain, including upstream replay warnings and unused simp arguments in Entries:64,77,89–90, plus previously recorded scoped warnings. No suppression or budget override was added; success is not a warning-free receipt.

2. Export/projection probes and axiom closure:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T18-r2-probe.lean
```

Exit **0**, no errors. Probe imports the facade, enumerates all 65 distinct public theorems with `#print axioms`, applies all four full node-export types, and checks the nine restored source clauses by direct conjunction projection. Every one of the 65 axiom lines has exactly `[propext, Classical.choice, Quot.sound]`. Main outputs:

```text
'KAM.Planetary.as_in' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.as_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.as_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.as_ent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Reproduction: extract each `^theorem` name (preserving apostrophes), import the facade and emit `#print axioms KAM.Planetary.<name>`. Full-type examples copy each theorem type and use `exact as_* p hp`. Direct projections: `as_in` scalar clauses at `.2.2.2.2.2.1` and `.2.2.2.2.2.2`; `as_pi` identity at `.2.2.2`; `as_c` raw clauses at six through eleven `.2` steps, followed by `.1` except for the last clause.

3. Kernel replay (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.AsymptoticEntries KAM.Planetary.PlanarTorsion.AsymptoticEntries.Pair KAM.Planetary.PlanarTorsion.AsymptoticEntries.Calculus KAM.Planetary.PlanarTorsion.AsymptoticEntries.Leading KAM.Planetary.PlanarTorsion.AsymptoticEntries.CoeffEq KAM.Planetary.PlanarTorsion.AsymptoticEntries.EntryBounds KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs KAM.Planetary.PlanarTorsion.AsymptoticEntries.Projector KAM.Planetary.PlanarTorsion.AsymptoticEntries.Coeffs KAM.Planetary.PlanarTorsion.AsymptoticEntries.Entries
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Calculus
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.CoeffEq
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Entries
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Coeffs
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Leading
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Pair
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Inputs
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.EntryBounds
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries.Projector
replaying KAM.Planetary.PlanarTorsion.AsymptoticEntries
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exclusively the allowed stale-generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1067 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module format, frozen-anchor guard and all 144 ABI hashes pass. The generated root was left untouched.

5. Mechanical checks: `git diff --check inp...HEAD` exits **0** (only the merge-base warning); scope has no forbidden token, `EuclideanSpace` or `set_option`; all ten files have the required module/copyright/public-import/docstring/public-section format. Maximum file length **218**, maximum line width **100 Unicode characters**. All 65 short declaration names occur exactly once in the KAM source tree; 61 helpers have the `p11cAe_` prefix. All declarations remain under `KAM.Planetary`, with no root shadowing. No new declaration was introduced by the fix.

## Notes, errata and closeout

- **N1, inherited comparison differences:** the prescribed `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is not empty: two pre-existing secular-box proof-body seals, two manifest state changes and 27 root import additions. As in Round 1, these predate T18. `git diff f67bed9b..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty, as is the corresponding four-file fix comparison. The literal whole-branch empty-diff gate is recorded as not met, not misreported as passed. No inherited seal is re-certified here.
- **N2, lint/build hygiene:** generated-root staleness is the explicitly permitted exception; build warnings are disclosed above. Neither was repaired in this report-only audit.
- **N3, constants/scope:** Big-O constants may depend on the full fixed datum `p`. Blueprint:231's “constants depending only on m₁/m₂” is the separate T19 normalization/uniformity obligation assigned at design:225,264; it is not established by these local nodes. No determinant or complete `asymptotics`/frozen theorem closure is claimed.

**Suspected source errata/deviations:** none newly found. The restored terms agree with the pinned source; no source text, premise, law, metric, normalizer or physical mass convention was changed. The accepted absolute-error notation and T18/T19 scope split are explicit above.

**Closeout:** all four local nodes classified PASS, all 65 declaration rows accounted for, Round 1 F1 closed, no unresolved delta finding. Package verdict **PASS WITH NOTES** for the inherited comparison/lint/warning and uniformity scope notes. Only this report remains as an audit edit.
