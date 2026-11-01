# Track LP dependency graph: extraction specification

Skill `build-proof-dependency-graph`, Phase 1. It follows the precedent of tracks K and W (`docs/graph/K/SPEC.md`,
`docs/graph/W/SPEC.md`) and states only what track LP needs. It was drafted before the freeze and settled after it
(package LP-GRAPH-W1, 2026-11-01): the anchors are the D62 manifest entries (§1), and the orchestrator rulings on
Q1–Q8 (root-b8) are recorded in §10. It binds the writer and the reviewers. Changes are recorded in the change log
with a date and a reason.

Track LP is built in **waves** (§9): wave 1 is the LP0 closure (§1 data, Lemmas 1–6, amendments, §7–§8 coverage),
extracted and assembled; waves 2 (LP1, LP1-H) and 3 (LP2, LP2-H) follow. LP3 (draft 8) is not frozen and not in the
graph.

## 1. Roots and anchors (binding since 2026-11-01, D62 freeze)

The LP anchors were frozen and sealed on main at `f46b94fb` (D62; `docs/tracks/LP/FREEZE.md`): **128 manifest entries**
`planetary.d59.*` (89 definitions, 34 characterization theorems, 5 headline theorems LP0, LP1, LP1-H, LP2, LP2-H),
FREEZE-PROPOSAL draft 7 revision 1. Draft 8 (LP3-1, LP3-2) is not frozen; LP3 stays outside the graph (§7, Q1).
The identity fields come from `manifest/frozen-anchors.json` (sha256 `cee8ce34…5cded8` at this freeze) and nothing
else: `packets/anchor-map.tsv` is the README's step-2 extract (128 rows) and `packets/anchor-binding.tsv`, written by
`tools/lp_depgraph_bind.py`, binds every anchor to its node, slice and wave (148 rows: the 128 entries plus 20 reused
definitions). The linter binds FROZEN_FILE, FROZEN_DECL, FROZEN_ANCHOR_ID, CONTRACT_ID/VERSION and FROZEN_ABI_SHA256
to the manifest. No graph field reads a proof body or a manifest state.

### 1.1 Node IDs of anchors (settled)

Every anchor node is `<owning MAIN node>#<Lean short name>`: definitions as in K (`bp:p0:domains#complexStrip`) and W
(`bpW:w0:ellap#WaveSpace`), and, departing from the pre-freeze proposal, theorem anchors too.

| Anchor | Lean export | Node | KIND | Wave | MAIN locus (statement / proof) |
|---|---|---|---|---|---|
| LP0 | `KAM.Planetary.StrongAMD.planar_strongAMD_barrier` | `lpM:L5#planar_strongAMD_barrier` | lemma | 1 | L5 L164 / L166–L175; N11 |
| LP1 | `…StrongAMD.planar_strongAMD_exponentialSafety` | `lpM:T15#planar_strongAMD_exponentialSafety` | theorem | 2 | T15 L502 with §1 L69–L93 |
| LP1-H | `…StrongAMD.planar_strongAMD_exponentialSafety_halfInteger` | `lpM:T15#planar_strongAMD_exponentialSafety_halfInteger` | corollary | 2 | §1 L93 and T15 |
| LP2 | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety` | `lpM:T19#spatial_strongAMD_exponentialSafety` | theorem | 3 | T19 L601 with §1 L69–L93 |
| LP2-H | `…Spatial.spatial_strongAMD_exponentialSafety_halfInteger` | `lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger` | corollary | 3 | §1 L93 and T19 |

**Why LP0 is not the node `lpM:L5` itself.** MAIN's Lemma 5 is d-generic ("negative-energy states", d ∈ {2,3}); Lemma
6 and Lemma 16 apply it in both dimensions, and the spatial chain (wave 3) must not depend on a planar declaration.
So `lpM:L5` is the ordinary d-generic lemma node and the anchor `lpM:L5#planar_strongAMD_barrier` is its planar
instance: it depends on `lpM:L5`, on the step `lpM:L5#pair-distances` (its distance clauses ¦q_i¦ ≥ d_⋆ and
¦q_i − q_j¦ ≥ d_pair are proved at L175 and restated at §1 L91), and on the frozen definitions its statement uses.
The same pattern applies to every theorem anchor; T15/T19 keep ordinary nodes `lpM:T15`/`lpM:T19` for the MAIN
theorem, decided by the wave-2/3 extractor.

### 1.2 Characterization theorems (34; roots by Q2)

Node `<owner>#<LeanName>`, the owner chosen by the docstring locus: thresholds `lpM:L4#…` (4), AMD `lpM:L3#…` (2 planar,
2 spatial), Kepler elements `lpM:L2#…` (4 planar, 9 spatial), osculating `lpM:L16#…` (4 planar, 9 spatial). Wave 1
holds the 10 planar ones whose loci lie in §1 and L2–L4; the 4 planar osculating ones join with Lemma 16 (wave 2),
the 20 spatial ones with LP-adef-sp (wave 3). Consumers depend on the characterization, never on the definition's
codomain (skill Phase 0).

### 1.3 Definition anchors

- **D62 definitions (89).** Groups (owning node): `lpM:s1:chamber` (chamber, OrderedActions), `lpM:s1:thresholds`
  (actionAxis, eccDeficit, pairFeasible, pairObjective, pairThreshold, AdjIdx, AdjIdx.upperIdx, the three ordered
  thresholds), `lpM:s1:elements` (strongAMD, keplerPeri/Apo, SourceCanonicalPhase, sourceStrongAMD,
  sourceKeplerPeri/Apo and the spatial elements), `lpM:s1:data` (spaceDot/Sq/Length), `lpM:s1:model` (spatial model,
  solution predicates, masses, bodyVector3), `lpM:L1` (barycentric maps), `lpM:L16:defs` (osculating elements). 36
  planar/dimension-free ones are wave 1 (slice LP-adef-pl), 53 spatial ones wave 3 (LP-adef-sp).
- **Reused frozen definitions (Q6: LP's own anchor nodes, bound to the existing manifest entries, never imported).**
  Exactly those that an LP frozen file imports directly: 20. Wave 1 (12): `Phase`, `bodyVector`, `NoCollision`
  (`lpM:s1:model#…`), `keplerEnergy`, `keplerAxis`, `keplerAction`, `keplerEccVector`, `planeCross`, `totalMomentum`
  (`lpM:s1:elements#…`), `planeSq`, `planeLength`, `planeDot` (`lpM:s1:data#…`). Wave 2 (7): `IsDiophantine`
  (`lpM:s1:dioph`), `actualMasses`, `IsMovingSolutionOn`, `MovingUniqueOn` (`lpM:s1:model`), `barycentricPositions`,
  `barycentricVelocities`, `IsNewtonSolutionOn` (`lpM:L1`). Wave 3 (1): `KAM.Iso.IsHamiltonianSolutionOn`. The
  transitive definition closure (e.g. `movingHamiltonian`, `hamiltonianVectorField`) is reached only through these
  and is typing data, not graph nodes.
- **Internal helpers** (`pairThreshold`, `AdjIdx`, `AdjIdx.upperIdx`) are anchor nodes of KIND definition with the
  NOTE "internal helper; source meaning only on its carrier".
- **Definition DEPS** are the frozen definitions the declaration uses (read from the frozen file), with the EDGE at
  the MAIN line it transcribes. A definition anchor has no edge to the d-generic MAIN definition node (`lpM:s1:elements`
  etc.): it realizes it in one dimension, which the statement audit of the freeze certified.
- **Convention watch:** the reused `keplerEnergy` is ν_i E_i (the Kepler term of (1)), not E_i; `keplerAxis` =
  −ν_i/(2 keplerEnergy) = −1/(2E_i).

## 2. Corpus (source pinning record)

**Corpus** (pinned in `docs/graph/LP/CORPUS.sha256`; verify with `sha256sum -c docs/graph/LP/CORPUS.sha256` from the
repository root). Both hashes were re-verified on 2026-11-01, at `inp-lp` `c2a646ac`. The last change to either file
was commit `c33ad585`.

| Path | SHA-256 | Lines | Role |
|---|---|---|---|
| `docs/tracks/LP/source/MAIN.md` | `68e9167f04e4a04689ea163c74e02ffcaea657b252726080abdbe37bdba48c1b` | 679 | the proof (T15 planar, T19 spatial); line-addressable |
| `docs/tracks/LP/source/AMENDMENTS.md` | `c887d1e27354a3db7fb8a20d8bf3e33a9ef95ff3173f925ba5ebfab192651881` | 26 | normative amendments N1–N12 |

**Amendment precedence rule** (AMENDMENTS.md L3–L6; source README L3–L5):
- N1 is fixed in place in MAIN (line 238, same line); no locator moves.
- N2–N12 **override the MAIN lines they cite**. Every graph record follows MAIN as amended.
- Locators keep pointing into MAIN, which stays line-addressable. A node whose statement or proof an amendment
  changes says so in its NOTE (`AMENDED: N<k> (AMENDMENTS.md L<row>)`). Where the amendment itself supplies the
  use, the EDGE locator points into AMENDMENTS.md.
- No source-statement field may reproduce an overridden MAIN reading. For example, a field may not list Lemma 12 and
  Lemma 13 conjunctively (N7), and may not use three different `U` sets (N2).
- Amendment rows: N1 L10, N2 L11, N3 L12, N4 L13, N5 L14, N6 L15, N7 L16, N8 L17, N9 L18, N10 L19, N11 L20,
  N12 L21. The recommended order (L23–26) is administrative.
- Rulings that settle an amendment are owner decisions, not source text. For example, N8 is settled by OD-1 (D59).
  The source fields of the anchors record the frozen convention.

**Not corpus (provenance and planning; pinned for the record only):**

| Path | SHA-256 | Lines | Why not a graph source |
|---|---|---|---|
| `docs/tracks/LP/source/README.md` | `b8b00312971dcf063c8d28a062e6aa47c1293e992ea2ed887af05540e18be5f4` | 28 | pin record; restates the precedence rule |
| `docs/tracks/LP/source/PROOF-AUDIT-1.md` | `614d3755e3bfbe931ff5e81bfabcd1c959f80d1981fe60d8c0cfe6c182bf707c` | 393 | audit report; its notes are AMENDMENTS N1–N12 |
| `docs/tracks/LP/source/LEAN-ROADMAP.md` | `bb52b50e5ba27914c81f2a65e9a207eebe1507ea92a1efdce30acb666717ca0f` | 248 | planning evidence (its §4 DAG says so, L190) |

**Candidate LP3 corpus (Q1; not in CORPUS.sha256 yet):**

| Path | SHA-256 | Lines |
|---|---|---|
| `docs/tracks/LP/lp3/LP3-PLAN.md` | `1b58b7048fb3de47e1cadfee0e904085551227a28949a564ea2dc13085ab06ba` | 506 |
| `docs/tracks/LP/lp3/LP3-PLAN-REVIEW-1.md` (provenance; PASS WITH NOTES) | `b107078df1e8e5fd6dd74d4171516718c2ab5579ff649d7853ea29060d56b7f8` | 267 |

**Imported-node sources** (pinned in `docs/graph/LP/IMPORTS.sha256`; these are exactly the pins of graphs N and P):
- `blueprint-N/parts/p0-conventions.tex`;
- `p11b-partial-nf.tex`;
- `p11c-partial-stability.tex`;
- `blueprint-P/parts/p14a-amd-expsafe.tex`.

Imports that no proof uses are pruned after extraction, together with their pins.

**Locators.** MAIN is Markdown without labels. A locator is
`docs/tracks/LP/source/MAIN.md#<unit>@L<x>-L<y>`, where `<unit>` is the MAIN unit token. The tokens are:
- `L1`–`L18`, `T15`, `T19`;
- `s1`–`s8`, for prose outside a numbered unit;
- `title`, `intro`.

Amendment locators use `N1`–`N12`. LP3-PLAN locators use its section numbers (`s2.4`, `F3`, …). The skill linter
checks only the path and the line range, so the token is a stable reader aid and never part of a node ID. Cite as
in the source README: `LP:MAIN L<k> (<lines>)`.

## 3. Standing assumptions and external inputs

- **STANDING_ASSUMPTIONS: none (settled at freeze; header `STANDING_ASSUMPTIONS: -`).** The data of MAIN §1 are not global standing assumptions:
  - n ≥ 2;
  - ν > 0 with max ν = 1;
  - 𝒜 compact and ordered;
  - δ, γ > 0;
  - τ > n − 1;
  - d ∈ {2, 3}.

  They are the hypothesis package `lpM:s1:data` (a definition node), as K treats its part-level packages. A result
  that assumes the package names it in `SOURCE_HYPOTHESES` and depends on it. Every application shows where the
  package is supplied. LP0 uses only n and ν. LP3 drops γ, τ and (5).
- **Externals.** MAIN has no labelled external list. The **closed list** is the ten candidates below (fixed at freeze; wave 1 renders the five it consumes: ftc, compact-min, heine-cantor, picard, gronwall). Any other
  unproved fact is a step node with `NOTE: SOURCE_GAP: …`, never a silent edge and never an extra external without a
  SPEC revision. The candidate list comes from MAIN's explicit appeals (coverage items `*#ext-*`, `KIND: external`,
  `LEAN_STATUS: EXTERNAL`):

  | External | Appeal in MAIN |
  |---|---|
  | `lpM:ext-ftc` | L3 L139 |
  | `lpM:ext-compact-min` (extreme value on compact sets) | L4 L149, L5 L170 |
  | `lpM:ext-heine-cantor` | L4 L154 |
  | `lpM:ext-picard` (contraction and Picard iteration) | L6 L189, L10 L340 |
  | `lpM:ext-gronwall` (uniqueness by the integral inequality) | L6 L189 |
  | `lpM:ext-holomorphic-limit` (uniform limits of holomorphic maps) | L7 L211, L8 L263 |
  | `lpM:ext-identity-theorem` | L7 L238, L8 L265, L17 L571 |
  | `lpM:ext-compact-cover` (finite subcover) | L8 L265 |
  | `lpM:ext-cauchy-estimates` (Cauchy formula and estimates, holomorphic square root) | L8 L271, L9 L302, L11 L379 |
  | `lpM:ext-fourier-contour` (Fourier coefficients of periodic holomorphic maps, contour shift) | L9 L298 |

  Extractors may propose additions only through the writer (SPEC revision).
- **Imports (cross-graph), as in the W/I/N/P precedent.** A proof that uses a result proved in another track's
  graph depends on an IMPORTED node `X:<node>`. It has `KIND external`, `LEAN_STATUS EXTERNAL`, `PROOF_SOURCE -`,
  `DEPS -`, source fields copied from `docs/graph/X/DEPGRAPH.md`, and the NOTE `IMPORTED: proved in the track-X
  graph, node <label>`. Candidates:
  - L13 cites the repository's `KAM.Nekhoroshev.nonresonant` (with `ExtNFHyp`, `nf`, `preimage`), which gives
    `N:bpN:p11:nonresonant` and possibly `N:bpN:p11:s-nf#data`. **No extractor reads the cited implementation
    files.** L13's own interface check (L433) is source text, and its Lean names are opaque tokens.
  - LP3 uses the sealed `KAM.Nekhoroshev.partialConvex_nekhoroshev`, which gives `N:bpN:p0:partial`, the root of
    graph N (D58).
  - LP3 adapts track P's Kepler data and perturbation, which gives `P:bpP:p14:h-data`, `P:bpP:p14:perturbation`,
    and possibly `P:bpP:p14:stopped` and `P:bpP:p14:lift`.

  The imports form the writer-owned slice `LP-imports`.
- **Literature** (MAIN §7: Laskar–Petit, Barbieri–Marco–Massetti, Pinzari–Liu) is provenance only. MAIN proves all
  the geometry it uses (L2–L5) and uses no external normal-form theorem.

## 4. Conventions to watch (the global reviewer checks these across slices)

- **Norms.**
  - Physical lengths |·| are Euclidean (`planeLength`, `spaceLength`).
  - Action and complex-coordinate vectors use the max norm ‖·‖_∞ (the Pi norm).
  - (24) is a weighted ℓ¹ Fourier norm of scaled vector fields.
  - Complexified real squares are bilinear (w·w), never Hermitian.
- **Angles.**
  - MAIN uses period 2π (radian frequencies ω_i = ν_i³/I_i³).
  - L13 converts to period one (θ = λ/2π, frequencies ω/2π, slow rescaling ℓ, bracket coefficient 2π/ℓ²).
  - The LP3 input `partialConvex_nekhoroshev` is radian (no conversion).
  - Track every factor 2π.
- **Normalization.**
  - G = 1, star mass 1, planet masses μν_i; max ν = 1 is kept in the anchors (OD-3).
  - The physical AMD is μC, so δ is a normalized margin.
  - The splitting (1) uses central parameter one.
  - The osculating elements use k_i = 1 + μν_i.
- **AMD.** C = ΣI − |L| is orientation-free (OD-1, N8). There is no prograde, L ≠ 0, alignment or secular premise
  in any anchor; MAIN derives each of these (L3, T15, L18).
- **Thresholds.**
  - B lives on the chamber carrier (`OrderedActions`, n ≥ 2; OD-2/OD-11), with attained-minimum characterizations.
  - C(0) ≤ B(I⁰) − δ allows equality; the conclusion is C(t) ≤ B(I(t)) − δ/2.
- **Exponents.**
  - LP1/LP2: a = 1/(2(τ+1)), τ > n − 1 free; LP1-H/LP2-H: τ = n − ½ gives 1/(2n+1).
  - LP3: a_n = 2/(6n² − 3n + 14), b_n = 3/(6n² − 3n + 14), parameter ε = B₀μ, μ₀ = ε₀/(2B₀) with the LP1/LP2
    osculating limits (LP3 review C5).
- **Drift radius.** The radius is r = √μ with improvement r/4 (L12 route), or r = D₀√μ with improvement r/2 (L13
  route, N6).
- **Shared sets (N2, N3).**
  - There is one compact U ⊂ 𝒬 containing the closed 4r_g tube about 𝓛_δ, and its modulus Ω_B serves (17), L8
    and (39).
  - r ≤ r_g and r_* ≤ 4r_g.
- **Constants.**
  - μ₀, c, T₀, A_I (A_Λ), A_a, d⋆, d_pair, A_osc, and the frozen A_elem depend only on (d, n, ν, 𝒜, δ, γ, τ). LP3's
    depend only on (n, ν, 𝒜, δ).
  - They are chosen before μ and the initial state.
  - N10/OD-9 add A_osc μ₀ ≤ d⋆/2 and 2A_osc μ₀ ≤ d_pair/2.
  - L5's d⋆, d_pair depend only on (n, ν, U, m) (N11 order).
- **Slow-pair count.** m = n (planar, L8) or m = 2n (spatial, L18). L9–L14 are generic in m and instantiated twice.
- **Canonical versus osculating.** Canonical elements use the scaled momentum p_i/ν_i; osculating elements use
  the actual velocity V_i = q̇_i (10). Records must not conflate them.

## 5. Node scheme and threshold

- **IDs** (stable, no line numbers; `ID_RE`-valid):
  - `lpM:L<k>`, `lpM:T15`, `lpM:T19` for MAIN results;
  - `lpM:s1:<slug>` for §1 definitions and claims;
  - `lpM:L9#domains`, `lpM:L9#norm`, `lpM:L16:defs` for in-lemma definitions;
  - `lpM:<unit>#<slug>` for proof steps;
  - `lpM:L14#route-L12`, `lpM:L14#route-L13` for route nodes;
  - `lpM:ext-<slug>` for externals;
  - `lp3:…` for LP3-PLAN units;
  - `N:…`, `P:…` for imports.

  Coverage items for displays are `lpM:eq<k>`, for amendments `lpA:N<k>`, for headings `lpM:h:…`.
- **Every** `### Lemma/Theorem` unit and every §1 definition group is a node, unless excluded with a reason.
- **Displays.** A numbered display (1)–(47) maps to its enclosing node. Refine it into its own node only when
  consumers use it independently and that matters for the topology. Candidates: (10), the inequality half of (13),
  (17).
- **Steps.** A further step node `<parent>#<slug>` is created only for an unmarked substantive obligation:
  - a nontrivial estimate or application;
  - a construction;
  - a case split;
  - a witness or parameter choice;
  - a quantifier closure;
  - a carrier change;
  - a reused intermediate claim.

  There are no nodes for routine algebra. The draft inventory proposes 105 proof regions; each extractor confirms,
  merges or splits them.
- **Remarks.** A remark stays a node only if a proof consumes it. Self-review, provenance, status and comparison
  prose is `EXCLUDED`.
- **Step source fields** (the W lesson, adopted from the start):
  - a step's `SOURCE_HYPOTHESES` are the premises of the enclosing statement plus local definitions;
  - results derived earlier in the proof are DEPS, never hypotheses;
  - the step's quantifiers inherit the enclosing scope.
- **Dimension rule (settled at freeze).** MAIN's §1 definitions and Lemmas 1–6 and 16 are d-generic (d ∈ {2,3});
  the frozen carriers are dimension-specific (planar `strongAMD`, `keplerAxis`, …; spatial `spatialSourceStrongAMD`,
  …). So MAIN nodes are recorded d-generically and depend on the d-generic definition nodes `lpM:s1:data`,
  `lpM:s1:model`, `lpM:s1:elements` (non-anchor), and the **dimension-specific frozen definitions attach at the
  anchors** whose statements use them (theorem anchors and definition anchors). A theorem anchor that is the
  instance of a d-generic lemma depends on that lemma node (e.g. LP0 → `lpM:L5`). This keeps every closure exact:
  LP0's closure holds the planar carriers and no spatial one.
- **Symbol uses** (the W lesson; list fixed from the anchor map at freeze). A node whose statement or proof writes a
  **dimension-free** frozen object by symbol depends on its anchor at the first use: 𝒬 (`chamber`; `OrderedActions`
  where the carrier itself is used), a_i(I) (`actionAxis`), D (`eccDeficit`), the pair feasible set and objective
  (`pairFeasible`, `pairObjective`), B_ij (`orderedPairThreshold`), B_cross (`orderedCrossThreshold`), B
  (`orderedStrongThreshold`). B_⋆ = min_i I_i has no anchor (it is inline in B). The internal helpers `pairThreshold`,
  `AdjIdx`, `AdjIdx.upperIdx` are edged only from the anchors whose declarations use them. Dimension-specific symbols
  (C, E_i, a_i, e_i, L, the osculating elements, the phase carriers, model and solution predicates) follow the
  dimension rule. Wave 2 adds `modeSize` (¦k¦₁) and the model predicates when their anchors are bound.
- **Statement splits (Q3–Q5, ruling root-b8).**
  - Q3: Lemma 3 = `lpM:L3#static` (C ≥ 0; L ≠ 0, H_i > 0, H_i ≥ m; the inequality of (13)) ∧ `lpM:L3#dynamic`
    (conservation of L; the identity of (13)) ∧ `lpM:L3#planar-orientation`; `lpM:L3` is their conjunction. Lemma 5
    consumes only `lpM:L3#static`, so LP0's closure does not reach Lemma 1.
  - Q4: `lpM:L4`'s source fields omit the radial-contact and Laskar–Petit clauses (L143) and the sharpness sentence
    (L147); items `lpM:L4#stmt-contact-lp`, `lpM:L4#stmt-sharpness`, and the prose L158 (N9) and L160 are EXCLUDED.
  - Q5 (wave 2, slice LP-m4b): Lemma 12's source fields omit (35) (N4); its items are EXCLUDED as "a remark, not a
    formal dependency (N4)". The inventory items `lpM:eq35` and the (35) proof region carry this ruling; the
    amendment item `lpA:N4` is deferred to wave 2.
- **Display refinement in wave 1:** (10) is the node `lpM:L1#velocity` (Lemma 3's recoil term and Lemma 16's V_i
  consume it apart from the reconstruction).

## 6. Edges

- Direct uses only, conjunctive, `consumer -> prerequisite`. Each edge has one `EDGE:` line at the consumer's
  use site. Write `¦` for absolute-value bars in a rationale.
- **Not edges:**
  - forward pointers (e.g. §1 L55 "Lemma 4 proves this");
  - comparisons;
  - provenance;
  - "is not used" remarks (N4, N9, L12 L427);
  - the §7 self-refutation table.
- **Alternatives.** L12 and L13 are alternative suppliers of the stopped drift (N7). Each becomes a `KIND: route`
  node, owned by the node that consumes the drift supplier, and is never a conjunction. The proposal makes `lpM:L14`
  the owner (L487 against L500). The extractor of LP-m5 confirms it or moves ownership to `lpM:T15#apply-L14` and
  `lpM:T19#apply-L14`.
- **Conditional lemmas.** L12, L13 and L14 take the L8-type domain statement as a premise. L14 also takes the chart
  identities. These premises stay in `SOURCE_HYPOTHESES`. The applications in T15 (L7, L8, m = n) and T19 (L17,
  L18, m = 2n) discharge them by edges or application nodes. LP3's §3 first exit discharges L14 with hstop from
  `lp3:s2.4`.
- **Repository citations** (L13, MAIN §7, the LP3-PLAN Lean names) are never followed into implementation files.
  Each is an IMPORT, a MAIN node, or a `SOURCE_GAP` step.

## 7. Reachability

`--require-all-reachable` joins the gate once the roots that a wave's nodes serve exist (W precedent). In wave 1 the
roots are LP0 and the 10 planar characterizations; 37 wave-1 nodes (Lemma 1, the dynamic part of Lemma 3, Lemma 6,
the osculating definitions, (4), (5), the half-integer claim, and the externals `ftc`, `picard`, `gronwall`) serve
the dynamic roots LP1/LP2 of waves 2–3 and are kept, not excluded (`reports/W1-lint.txt` lists them). From wave 3 on,
the gate includes `--require-all-reachable`; a node then outside every root closure is either linked (a missed use)
or `EXCLUDED` with the reason "outside every root closure of track LP" and the check made. Expected exclusions:
- the N9 paragraph (L158) and the Laskar–Petit identification (L160) of L4;
- the L4 statement clauses L143 (radial contact, Laskar–Petit) and L147 (sharpness), if Q4 splits them off;
- (35) (N4; see Q5);
- the L16 convention remark;
- every §7–§8 item.

If LP3 is not frozen, the LP3 slices are not extracted and LP3-PLAN stays outside the corpus.

## 8. Roles and reviewer assignments (settled: Q8, ruling root-b8)

The roles follow the skill and the repository model policy (D21: Codex GPT-6.1-Sol auditors; D24: Sol at medium
effort; D54/D57: codex-2 carries the LP audits; all of codex-1, codex-2, codex-3 are valid audit accounts).

| Role | Who (tag) | Rule |
|---|---|---|
| Writer (single) | `kam-lp` (WRITER in header.txt) | The only editor of packets, `DEPGRAPH.md` and `DEPGRAPH_COVERAGE.md`. Merges, adjudicates, applies review fragments and marks REVIEWED. Never a reviewer. |
| Extractor | `kam-lp` (EXTRACTOR of every wave-1 record). Package LP-GRAPH-W1 names its agent "the extractor, working under the writer's direction": the W low-cost precedent (option B), extracting every slice from compact specs `specs/<slice>.py` rendered by `tools/lp_depgraph_fill.py`. | Packets only; no Lean evidence, no implementation files, no proof bodies. |
| Pre-anchor inventory | `lp-preanchor-inventory` | Wrote `draft/coverage-*.md`. It may never review an LP item or node. |
| Slice reviewers | Codex GPT-6.1-Sol, medium effort, on **codex-2** (D57), one fresh session per slice, `sol-review-LP-<slice>`; the orchestrator launches them in **parallel batches** (Q8), each in its own session. | Refute-first, per `REVIEW-BRIEF.md`. Never the extractor or the writer. |
| Delta reviewers | A Sol session different from the reviewer whose replacement blocks it checks, `sol-delta<k>-LP-<slice>` | The K/W delta rule. |
| Global reviewer | A fresh Sol session, `sol-global-LP` | Distinct from the writer, every extractor and every slice or delta reviewer. |
| Opus subagents | Paper-level reviews only (e.g. the LP3 source note of Q1); never a reviewer of record for the topology (auditor policy of root-b8, 07:50). | — |

**Review batches.** R1 (wave 1, LP0): `LP-adef-pl`, `LP-athm`, `LP-ext`, `LP-m1`, `LP-m2a`, `LP-m2b`, `LP-amend`,
`LP-m78`; R2 (wave 2): `LP-m3`, `LP-m4a`, `LP-m4b`, `LP-m5`, `LP-imports`, the wave-2 additions to `LP-ext`,
`LP-adef-pl` and `LP-athm`; R3 (wave 3): `LP-adef-sp`, `LP-m6`, the wave-3 `LP-athm` additions. Then delta rounds and
the global review of all roots. Review packets: `REVIEW-BRIEF.md` and `reviews/R1-packets.md`.

## 9. Slices

Line-addressable, aligned to complete lemma units, recorded in `packets/slices.json`. A node belongs to the slice
containing the first line of its STATEMENT_SOURCE, with two overrides: every frozen anchor belongs to `LP-athm`
(theorems) or `LP-adef-pl`/`LP-adef-sp` (definitions), and the externals belong to the writer-owned `LP-ext`.
Coverage items follow their SOURCE line; an anchor slice has one item per anchor. An inventory item whose
disposition names a node of a later wave is kept in `packets/<slice>.deferred-coverage.md` (not assembled) until
that node exists. Anchor slices grow by wave (`anchor-binding.tsv`, column `wave`).

Status after wave-1 extraction (2026-11-01; all PROPOSED, extractor `kam-lp`):

| Slice | Source range | Wave | Nodes | Edges | Coverage | Deferred items |
|---|---|---|---|---|---|---|
| `LP-adef-pl` | anchors (manifest): 36 planar/dimension-free D62 definitions + 12 reused | 1 | 48 | 103 | 48 | — |
| `LP-athm` | anchors (manifest): LP0 + 10 planar characterizations | 1 | 11 | 65 | 11 | — |
| `LP-ext` | closed external list, wave-1 part (ftc, compact-min, heine-cantor, picard, gronwall) | 1 | 5 | 0 | 0 (items in the MAIN slices) | — |
| `LP-m1` | MAIN L1–93 | 1 | 6 | 8 | 19 | 6 (§1 conclusion → T15/T19 anchors) |
| `LP-m2a` | MAIN L94–160 (L1–L4) | 1 | 24 | 77 | 36 | — |
| `LP-m2b` | MAIN L161–189 (L5–L6) | 1 | 15 | 64 | 20 | — |
| `LP-amend` | AMENDMENTS L1–26 | 1 | 0 | 0 | 7 | 7 (N1, N3–N7, N10) |
| `LP-m78` | MAIN L604–679 | 1 | 0 | 0 | 12 | — |
| **wave 1** | | | **109** | **317** | **153** (26 excluded) | 13 |
| `LP-m3`, `LP-m4a`, `LP-m4b`, `LP-m5`, `LP-imports`; wave-2 parts of `LP-adef-pl` (7 reused), `LP-athm` (LP1, LP1-H, 4 osculating characterizations), `LP-ext` (5) | MAIN L190–529 | 2 | — | — | — | — |
| `LP-adef-sp` (54), `LP-m6`; wave-3 part of `LP-athm` (LP2, LP2-H, 20 spatial characterizations) | MAIN L530–603 | 3 | — | — | — | — |
| `LP3-a`, `LP3-b` | LP3-PLAN (conditional, Q1) | 4 | — | — | — | — |

## 10. Orchestrator rulings on Q1–Q8 (root-b8, 2026-11-01: all proposed defaults accepted)

- **Q1 (LP3 corpus):** option (b). A short paper-level LP3 source note is written and reviewed after the draft-8
  freeze, before LP3 extraction. Until then LP3-PLAN.md stays outside the corpus and no LP3 slice exists.
- **Q2 (characterizations):** the 34 characterization theorems are anchors **and roots** (header ROOTS).
- **Q3 (L3 split):** done in wave 1 (§5): `lpM:L3#static`, `lpM:L3#dynamic`, `lpM:L3` their conjunction.
- **Q4 (L4 clauses):** done in wave 1 (§5): the unconsumed statement clauses are excluded items.
- **Q5 ((35)):** split off and excluded; applied by the wave-2 extractor of LP-m4b (§5).
- **Q6 (reused definitions):** bound as LP anchor nodes (§1.3); exactly the 20 that LP frozen files import directly.
- **Q7 (Markdown tooling):** `tools/lp_depgraph_preextract.py` turns the draft inventory and the anchor binding into
  skeleton slice packets (dry run: `reports/W1-dryrun.txt`); `tools/lp_depgraph_fill.py` renders the writer's specs.
- **Q8 (roles):** writer tag `kam-lp`; slice and global reviews on codex-2, in parallel batches, one session per
  reviewer (§8).

## Change log

- 2026-11-01: initial pre-freeze draft (pinning, inventory, slice plan, roles). No extraction, no header, no edges.
- 2026-11-01, **post-freeze setup and wave 1** (package LP-GRAPH-W1, branch `inp-lp-graph` off inp with the D62
  freeze f46b94fb):
  - Pins re-checked: `sha256sum -c` on CORPUS.sha256 and IMPORTS.sha256, all OK; no re-pin.
  - Anchor map (128 entries; README step 2) and anchor binding (148 anchors incl. 20 reused definitions) written.
  - §1 settled: all anchor IDs are `<owner>#<LeanName>`; LP0 is `lpM:L5#planar_strongAMD_barrier`, the planar
    instance of the d-generic `lpM:L5` (deviation from the pre-freeze proposal `lpM:L5`; reason in §1.1).
  - §5: dimension rule and the fixed symbol list; Q3–Q5 splits recorded (Q3, Q4 applied; Q5 in wave 2).
  - §7: `--require-all-reachable` joins the gate when the served roots exist (wave 1 keeps 37 nodes for LP1/LP2).
  - §8, §10: rulings Q1–Q8 recorded.
  - Wave 1 extracted from specs and assembled: 109 nodes (59 anchors, 5 externals), 317 edges, 0 routes, 11 roots,
    72 nodes in the root closure, 153 coverage items (26 excluded), 13 deferred items, 1 SOURCE_GAP
    (`lpM:L3#deficit-zero-L`: the frozen deficit characterization covers L = 0, which MAIN does not argue). The
    linter (`--require-complete-coverage --require-initial-lean-status`, `--check`) exits 0; `reports/W1-lint.txt`.
- 2026-11-01, **waves 2 and 3, streamlined (D65)** (package LP-GRAPH-W2, writer and extractor `kam-lp`):
  - Owner ruling D65: a fully proved track's graph is a provenance record. No per-slice or delta reviews (the R1
    verdicts already applied stay), one extraction pass for waves 2-3 (and 4 when the LP3 anchors are on main), LEAN_STATUS
    set mechanically from LEAN_REFs that resolve on main, structural lint (coverage, edges, cycles, reachability)
    without `--require-reviewed`, then ONE independent global review. The header CORPUS line says so. §8's per-slice
    review batches R2/R3 are cancelled.
  - Packets: the wave additions to the reviewed wave-1 slices are separate packets `LP-athm-w2`, `LP-athm-w3`,
    `LP-adef-pl-w2`, `LP-ext-w2`, and the formerly deferred coverage items are `LP-m1-w2`, `LP-amend-w2` (the
    `*.deferred-coverage.md` files are superseded and not assembled). Assembly order: `packets/slices-assembled.txt`.
  - §6 routes: the drift suppliers are route nodes `lpM:L14#route-L12` and `lpM:L14#route-L13`, owned by
    `lpM:L14#improvement` (the step consuming the drift at L487/L500), a refinement of the proposal "lpM:L14 owns
    them". Lemma 14 is d-generic and conditional; T15/T19 discharge its chart premises (`#apply-L14`).
  - Q5 applied: (35) and its proof region excluded, `lpA:N4` excluded. The Cauchy bounds on DΦ (L379) are excluded as
    unconsumed ("not used to infer invertibility").
  - New SOURCE_GAP steps: `lpM:L10#lie-flow-identification`, `lpM:L10#flow-existence` (N5: sketched; route L12 only)
    and `lpM:L14#maximal-solution` (the unique maximal solution from Lemma 6's local existence; §1 L78).
  - Externals: the remaining five of the closed list rendered (`LP-ext-w2`). Imports: only `N:bpN:p11:nonresonant`
    (Lemma 13); `N:bpN:p0:partial` and the P imports serve LP3 only and stay unrendered; IMPORTS.sha256 unchanged.
  - Wave 3 anchors are bound mechanically (`specs/_lp_anchor_util.py`): a definition's DEPS (and a theorem's
    statement-symbol edges) are the bound frozen definitions its file imports and names in its declaration.
  - Three frozen carrier definitions have no consumer in any root statement or source proof and are not graph
    nodes: `sourceOscVelocity`, `sourceOscParam`, `spatialSourceOscVelocity` (items EXCLUDED, "outside every root
    closure"; removed from FROZEN_ANCHORS by `tools/lp_depgraph_header.py`). `lpM:L3` is consumed whole by
    `lpM:L18#alignment`.
  - Result: 292 nodes, 1040 edges, 39 roots, 145 anchors, 11 externals (10 closed-list + 1 import), 2 routes,
    4 SOURCE_GAP, 394 coverage items (40 excluded), every node in a root closure; lint exit 0
    (`reports/W2-lint.txt`); LEAN_STATUS applied (`LEAN_STATUS.md`): 145 PROVED, 11 EXTERNAL, 136 NOT_STARTED.
- 2026-11-01, **wave 4 (LP3, D64 landed at main 61c6d5a7), streamlined (D65)**: `inp` (b5f029f5, with D64) merged into
  `inp-lp-graph` (no conflict). LP3-PLAN.md is pinned in CORPUS.sha256 (hash = the §2 candidate pin) and is the LP3
  source; the Q1 source note is not written (D65 minimal model, orchestrator ruling). Anchors bound mechanically from
  the manifest (binding rows, wave 4): LP3-1 `lpM:T15#planar_strongAMD_exponentialSafety_noArith`, LP3-2
  `lpM:T19#spatial_strongAMD_exponentialSafety_noArith` (roots), and the reused exponent definitions
  `lp3:s1.1#planetaryTimeExponent`, `lp3:s1.1#planetaryDriftExponent` (Q6). Import `N:bpN:p0:partial`
  (partialConvex_nekhoroshev). Four LP3 step nodes: `lp3:s2.3` (fixed data and premise discharge, §2.2-§2.3),
  `lp3:s2.4` (planar drift supplier in the hstop shape, §2.4 with §3's sharp sublevel), `lp3:s2.5` (spatial),
  `lp3:s3#first-exit` (Lemma 14's route-independent steps with the LP3 supplier; LP3 drops (5), so it does not use
  `lpM:L14` or `lpM:T15#apply-L14`). The 40 LP3-PLAN inventory items are coverage (packets LP3-a, LP3-b). Result:
  301 nodes, 1161 edges, 41 roots, 149 anchors, 12 externals, 438 coverage items (47 excluded); lint exit 0;
  LEAN_STATUS PROVED 153, BYPASSED 136, EXTERNAL 12.
- 2026-11-01, **global review incorporated (D65)**: the one global review `maud-lp-gglob-1`
  (`reviews/GLOBAL-review-1.md`, audited ef3c63d0) is PASS WITH NOTES and confirms the D27 BYPASS of all 136 nodes.
  Its 11 exact evidence-record refinements (report lines 161-189: EDGE locators of LP1 (4), LP2-H (1), LP3-1 (2),
  LP3-2 (2) and the spatial characterizations spatialSourceKeplerApo_ge_length, spatialSourceKeplerPeri_le_length
  (1 each)) are applied to the packets; no DEPS, ROUTES, status or identity field changed. Header GLOBAL_REVIEWER / GLOBAL_REVIEW_REF are
  set. TOPOLOGY_STATUS stays PROPOSED outside the 72 R1-reviewed wave-1 records: under D65 the global review replaces
  slice review, and the structural gate runs without `--require-reviewed` (the W graph's REVIEWED markers came from
  its slice reviews, which D65 cancels). Lint exit 0; LEAN_STATUS sync re-applied with no change (PROVED 153,
  BYPASSED 136, EXTERNAL 12). Retained SOURCE_GAP steps: `lpM:L3#deficit-zero-L`, `lpM:L10#flow-existence`,
  `lpM:L10#lie-flow-identification`, `lpM:L14#maximal-solution`.
