# Track LP dependency graph: extraction specification (PRE-FREEZE DRAFT)

Skill `build-proof-dependency-graph`, Phase 1, written **before the LP anchors are frozen**. It follows the
precedent of tracks K and W (`docs/graph/K/SPEC.md`, `docs/graph/W/SPEC.md`) and states only what track LP needs.
Sections marked **AFTER FREEZE** are proposals: they become binding only when the orchestrator confirms them after
the owner approves the exact anchor text and the anchors enter `manifest/frozen-anchors.json`. Every other section
binds the writer and the reviewers from the moment extraction starts. Changes are recorded in the change log with a
date and a reason.

No extraction has started. No dependency edge, node block, `header.txt` or `DEPGRAPH*.md` exists yet. The skill
forbids them before the frozen manifest exists ("Only then create the graph header").

## 1. Roots and anchors (AFTER FREEZE; proposal)

The LP anchors are not frozen. The proposal is FREEZE-PROPOSAL **draft 7** (`/root/code/KAM-inp-lp-freeze7`,
branch `inp-lp-freeze7`, commit `b5f8d503`, `docs/tracks/LP/FREEZE-PROPOSAL.md` sha256 `429830d2…dc3a6d5`). That draft
is in revision (LP-FREEZE7R: audit-1 findings F1 spatial barycentric maps, F2 helper roles). LP3 is the separate
**draft 8** delta (`/root/code/KAM-inp-lp-freeze8`, in progress; tentative names `…_noArith`). At freeze, every name,
path, count and ABI hash below is re-read from the manifest. Nothing here may be copied into a graph field before
then.

### 1.1 Theorem anchors and proposed node IDs

The proposal binds each anchor to the MAIN unit whose statement it is, as K and W do (source labels as node IDs).

| Anchor | Draft-7/8 Lean name | Proposed node | KIND | MAIN locus (statement / proof) |
|---|---|---|---|---|
| LP0 | `KAM.Planetary.StrongAMD.planar_strongAMD_barrier` | `lpM:L5` | lemma | L5 (162–175), with L2–L4 (110–160); N11 |
| LP1 | `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety` | `lpM:T15` | theorem | T15 (502–506) with §1 (69–93) and L16 (508–529); N8, N10 |
| LP1-H | `…planar_strongAMD_exponentialSafety_halfInteger` | `lpM:T15#tau-half` | corollary | §1 (93) and T15 |
| LP2 | `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety` | `lpM:T19` | theorem | T19 (599–603) with §1 (69–93), L16, d = 3 |
| LP2-H | `…spatial_strongAMD_exponentialSafety_halfInteger` | `lpM:T19#tau-half` | corollary | §1 (93) and T19 |
| LP3-1 | draft 8, tentative `…planar_strongAMD_exponentialSafety_noArith` | `lp3:LP3-1` | theorem | LP3-PLAN §1.2 (85–126); proof §2.2–§2.4, §3 |
| LP3-2 | draft 8, tentative `…spatial_strongAMD_exponentialSafety_noArith` | `lp3:LP3-2` | theorem | LP3-PLAN §1.3 (128–134); proof §2.5, §3 |

- The corollary anchors depend on their parent anchor node and on `lpM:s1:half-integer` (τ = n − ½ is admissible;
  2((n − ½) + 1) = 2n + 1).
- LP3-1 and LP3-2 enter only if draft 8 is frozen (LP3-PLAN O-3) and Q1 below is settled.

### 1.2 Characterization theorems (34 in draft 7)

These are frozen theorems with `DRAFT_SORRY` bodies. The proposal (Q2) makes each one an anchor node **and a root**.
The node ID is `<owning MAIN node>#<LeanName>`. Consumers depend on the characterization theorem, not on the
definition's codomain (skill Phase 0). Proposed loci:

| Characterizations | MAIN locus |
|---|---|
| `orderedPairThreshold_isLeast`, `orderedPairThreshold_existsUnique_value`, `orderedCrossThreshold_isLeast`, `orderedStrongThreshold_isLeast` | (3) (45–55), L4 (141–156) |
| `sourceStrongAMD_nonneg`, `sum_action_mul_eccDeficit_le_sourceStrongAMD`; `spatialSourceStrongAMD_nonneg`, `spatialSourceAction_mul_eccDeficit_le` | L3 (130–139), (13) |
| `sourceKepler_axis_pos`; `spatialSourceKeplerAxis_pos`, `spatialSourceKeplerAction_pos`, `spatialSourceKeplerAction_sq` | (2) (31–35) |
| `sourceKepler_ecc_le_one`, `sourceKeplerPeri_le_planeLength`, `planeLength_le_sourceKeplerApo`; `spatialSourceKeplerEcc_{sq,nonneg,le_one}`, `spatialSourcePlanetAngularMomentum_length{,_le}`, `spatialSourceKeplerPeri_le_length`, `spatialSourceKeplerApo_ge_length` | L2 (110–128), (11)–(12) |
| `sourceOscAxis_pos`, `sourceOscPeri_pos`, `sourceOscPeri_le_planeLength`, `planeLength_le_sourceOscApo`; `spatialSourceOsc{Param_pos,Energy_neg,Ecc_lt_one,Ecc_nonneg,Axis_pos,Peri_pos,Peri_le_length,Apo_ge_length}` | L16 (508–529), (42)–(43), and L2 with parameter k_i |

### 1.3 Definition anchors

- **New definitions (88 in draft 7).** Node ID `<definition node>#<LeanName>`, as in `bp:p0:domains#complexStrip`
  (K) or `bpW:w0:ellap#WaveSpace` (W). The definition nodes are:
  - `lpM:s1:chamber`, `lpM:s1:thresholds` (thresholds, carriers, `AdjIdx`, `modeSize` through (5));
  - `lpM:s1:elements` (the strong AMD, canonical elements, source carriers, planar and spatial vectors);
  - `lpM:s1:model` (the spatial model and Newtonian maps);
  - `lpM:L16:defs` (osculating elements).

  The exact mapping is made at freeze from the frozen docstrings, which carry `LP:MAIN` loci.
- **Reused frozen definitions.** 19 are referenced directly and 21 are in the closure, including `movingHamiltonian`
  and `hamiltonianVectorField`. Following the I/P/W precedent (W SPEC, ruling kam-d4), a definition that MAIN §1
  transcribes becomes **LP's own anchor node**, bound to the existing manifest entry, and is never imported. Examples
  are `keplerAxis` (2) and `IsMovingSolutionOn` (1). A reused definition that MAIN does not transcribe gets a
  writer decision, recorded here: anchor node or `EXCLUDED` typing data. Example: `Phase`.
- **Internal helpers** ("internal" role, draft 7 §4.2/§4.4) are frozen definitions, so each is an anchor node of
  `KIND: definition`. Its source fields say "internal helper; source meaning only on its carrier". It has no
  separate MAIN statement.
- LP3 adds no definition, if draft 8 confirms an empty closure delta. The exponents `planetaryTimeExponent` and
  `planetaryDriftExponent` are already frozen (track P). They bind to `lp3:s1.1#exponents` under the same reuse rule.

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

- **STANDING_ASSUMPTIONS: none (proposal).** The data of MAIN §1 are not global standing assumptions:
  - n ≥ 2;
  - ν > 0 with max ν = 1;
  - 𝒜 compact and ordered;
  - δ, γ > 0;
  - τ > n − 1;
  - d ∈ {2, 3}.

  They are the hypothesis package `lpM:s1:data` (a definition node), as K treats its part-level packages. A result
  that assumes the package names it in `SOURCE_HYPOTHESES` and depends on it. Every application shows where the
  package is supplied. LP0 uses only n and ν. LP3 drops γ, τ and (5).
- **Externals.** MAIN has no labelled external list. The writer fixes a **closed list** before extraction. Any other
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
- **Symbol uses** (the W lesson). A node whose statement or proof writes a frozen object by symbol depends on its
  anchor at the first use. The symbols are B, B_ij, 𝒬, C (strong AMD), the canonical and osculating elements and
  their source carriers, `modeSize` (|k|₁), and the model and solution predicates. This list is fixed from the
  anchor map at freeze.

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

`--require-all-reachable` is part of the gate from the first assembled draft. A node outside every root closure is
either linked (a missed use) or `EXCLUDED` with the reason "outside every root closure of track LP" and the check
made. Expected exclusions:
- the N9 paragraph (L158) and the Laskar–Petit identification (L160) of L4;
- the L4 statement clauses L143 (radial contact, Laskar–Petit) and L147 (sharpness), if Q4 splits them off;
- (35) (N4; see Q5);
- the L16 convention remark;
- every §7–§8 item.

If LP3 is not frozen, the LP3 slices are not extracted and LP3-PLAN stays outside the corpus.

## 8. Roles and reviewer assignments

The roles follow the skill and the repository model policy:
- D21: Sonnet workers, Codex GPT-6.1-Sol auditors;
- D24: Sol at medium effort;
- D54: codex-1 for every track;
- D57: codex-2 carries the LP and W audits, one audit at a time machine-wide, LP first;
- D60: parallel W audits; this is W-specific.

All of codex-1, codex-2 and codex-3 are valid audit accounts. Items marked **[CONFIRM]** need the orchestrator.

| Role | Who (tag) | Rule |
|---|---|---|
| Writer (single) | `claude-suborch-LP` (kam-lp sub-orchestrator, Opus 5.5; D56) **[CONFIRM tag]** | The only editor of packets, `DEPGRAPH.md` and `DEPGRAPH_COVERAGE.md`. Merges, adjudicates, and marks REVIEWED. Never a reviewer. |
| Pre-anchor inventory | `lp-preanchor-inventory` (this preparation) | Wrote `draft/coverage-*.md`, all PROPOSED. It may never review an LP coverage item or node. |
| Extractors | **Option A (recommended):** Sonnet subagents at low effort, one per slice, `sonnet-extract-LP-<slice>` (skill default; K precedent; D21). **Option B:** the writer extracts every slice from compact specs (the W "low-cost policy" precedent), `EXTRACTOR: claude-suborch-LP`. **[CONFIRM A or B]** | Packets only. No Lean evidence, no implementation files. Each extractor edits only its own `packets/<slice>.{nodes,coverage}.md`. |
| Slice reviewers | Codex GPT-6.1-Sol, medium effort, default tier, on **codex-2** (D57), fallback codex-1 (D54) or codex-3. One fresh session per review batch, `sol-review-LP-<slice>`. **[CONFIRM account]** | Refute-first (REVIEW-BRIEF, to be written from the K/W template). Never the extractor of the slice. |
| Delta reviewers | A Sol session different from the reviewer whose replacement blocks it checks, `sol-delta<k>-LP-<slice>` | The K/W delta rule. |
| Global reviewer | A fresh Sol session, `sol-global-LP` | Distinct from the writer, every extractor and every slice or delta reviewer (the linter enforces writer and extractor; the writer enforces reviewer). |
| Opus subagents | **Paper-level only [CONFIRM]**: e.g. a refute-first review of a new LP3 source note (Q1 (b)), as PROOF-AUDIT-1 and LP3-PLAN-REVIEW-1 were. | No D-number authorizes Opus as the recorded slice or global topology reviewer. D21 and D57 place audits on Codex, and OD-10 option (b) was not taken. Opus would serve as a reviewer of record only by an explicit orchestrator ruling recorded here. |

**Batching.** D57 allows one audit at a time machine-wide, so reviews run in four batches, in order. Each batch is
one fresh Sol session with one review file per slice, as in W's batched review. Running batches in parallel needs a
ruling like D60 for LP **[CONFIRM]**.

| Batch | Slices | Closure it completes |
|---|---|---|
| R1 | `LP-adef-pl`, `LP-athm`, `LP-m1`, `LP-m2a`, `LP-m2b`, `LP-amend`, `LP-m78` | LP0 |
| R2 | `LP-m3`, `LP-m4a`, `LP-m4b`, `LP-m5`, `LP-imports`, `LP-ext` | LP1, LP1-H |
| R3 | `LP-adef-sp`, `LP-m6` | LP2, LP2-H |
| R4 | `LP3-a`, `LP3-b` | LP3-1, LP3-2 (conditional) |

After that come delta rounds, then the global review of all roots.

## 9. Slices

These are the planned slices; `packets/slices.json` records them. They are line-addressable and aligned to complete
lemma units. A node belongs to the slice containing the first line of its STATEMENT_SOURCE, with one override: every
frozen anchor node belongs to `LP-athm` or `LP-adef-*`, as K's anchors belong to K-p0. Coverage items follow their
SOURCE line. Node and item counts are estimates from the draft inventory.

| Slice | Source range | Units | Est. nodes | Est. items | Anchors served | Wave |
|---|---|---|---|---|---|---|
| `LP-adef-pl` | anchors (manifest) | new planar/dimension-free definitions 1–37 and reused frozen definitions | ≈ 56 | ≈ 56 | all | 1 |
| `LP-adef-sp` | anchors (manifest) | new spatial definitions 38–88 | ≈ 51 | ≈ 51 | LP2, LP2-H, LP3-2 | 3 |
| `LP-athm` | anchors (manifest) | 5 (+2) theorem anchors, 34 characterizations: identity and source fields; DEPS into MAIN nodes | ≈ 41 | ≈ 41 | all | 1 |
| `LP-m1` | MAIN L1–93 | §1 data, (1)–(9), conclusion, line 93 | 8 | 25 | all | 1 |
| `LP-m2a` | MAIN L94–160 | L1–L4 | 20 | 33 | all (L1: dynamic anchors) | 1 |
| `LP-m2b` | MAIN L161–189 | L5–L6 | 15 | 20 | LP0 (L5); dynamic (L6) | 1 |
| `LP-amend` | AMENDMENTS L1–26 | N1–N12, precedence, order | 0 | 14 | per amendment | 1 |
| `LP-m78` | MAIN L604–679 | §7–§8, all excluded | 0 | 12 | none | 1 |
| `LP-m3` | MAIN L190–271 | L7–L8 | 16 | 27 | dynamic | 2 |
| `LP-m4a` | MAIN L272–379 | L9–L11 | 21 | 35 | LP1/LP2, route-L12 | 2 |
| `LP-m4b` | MAIN L380–464 | L12–L13 | 12 | 21 | LP1/LP2, both routes | 2 |
| `LP-m5` | MAIN L465–529 | L14, T15, L16 | 25 | 32 | LP1, LP1-H; dynamic | 2 |
| `LP-imports` | graphs N, P | imported nodes (writer-owned) | ≤ 5 | — | LP1/LP2 (route-L13), LP3 | 2 |
| `LP-ext` | — | the closed external list (writer-owned) | 10 | — | per use | 2 |
| `LP-m6` | MAIN L530–603 | L17, L18, T19 | 17 | 23 | LP2, LP2-H, LP3-2 | 3 |
| `LP3-a` | LP3-PLAN L1–258 | targets, the frozen interface, fixed data F1–F7, premises | 17 | 22 | LP3-1, LP3-2 | 4 |
| `LP3-b` | LP3-PLAN L259–506 | the hstop supplier, spatial version, sublevel, first exit, assembly; §4–§7 excluded | 14 | 18 | LP3-1, LP3-2 | 4 |

The MAIN slices hold 134 planned nodes and 242 coverage items (MAIN 228 and AMENDMENTS 14), plus 10 externals, ≤ 5
imports and the anchor slices. The largest MAIN slice is `LP-m4a`, 107 lines. Each wave ends with the linter run
`--require-complete-coverage --require-initial-lean-status` on the assembled draft.

## 10. Open questions for the orchestrator

- **Q1 (LP3 corpus).** LP3-PLAN.md is a plan ("not a proof certificate", L4), and most of its steps cite LP or
  track-P implementation lemmas by name, marked [REUSED] or [ADAPTED]. Options:
  - (a) Pin LP3-PLAN.md (and REVIEW-1 as provenance) as the LP3 corpus. Map every Lean-name citation to a MAIN node,
    a graph-N/P import, or a `SOURCE_GAP` step. Expect several gaps (cell Kepler data, the Hamiltonian identity on
    V_j, time reversal).
  - (b) First write a short paper-level LP3 source note: MAIN-style, line-addressable, with the [REUSED] steps
    restated against MAIN lemmas and the N/P blueprints. Give it a refute-first review, then pin it.

  Recommendation: (b), if the LP3 anchors are frozen. Otherwise defer.
- **Q2 (characterizations).** Make all 34 characterization theorems (and any draft-8 additions) anchors **and
  roots**? There is no precedent graph with characterization anchors. Recommendation: yes. They are `DRAFT_SORRY`
  frozen theorems that need a source-traced closure, and `--require-all-reachable` otherwise forces the
  unconsumed ones out, e.g. `spatialSourceOscParam_pos`.
- **Q3 (L3 split).** LP0 uses only L3's static parts: C ≥ 0, L ≠ 0, H_i ≥ m and the inequality half of (13). If L3
  stays one node, LP0's closure includes L3#conservation and hence L1. Options:
  - expose the static claims as separately consumed steps, so that L5 depends on `lpM:L3#deficit` etc., as W
    allows step dependencies;
  - accept the larger closure.

  Recommendation: steps.
- **Q4 (L4 unconsumed clauses).** The L4 statement asserts radial contact, the Laskar–Petit identification (L143)
  and sharpness (L147). No proof uses them (N9). Either keep them in L4's SOURCE_CONCLUSION, which drags the L158/L160
  arguments into every closure, or record L4's statement without them in a reviewed split with a NOTE.
  Recommendation: split, with `lpM:L4#sharpness` EXCLUDED.
- **Q5 ((35)).** (35) belongs to L12's statement but has no consumer (N4). The question is the same as Q4: keep it
  in the statement, or split it off and exclude it. Recommendation: split it off and exclude it.
- **Q6 (reused frozen definitions).** Bind the 19–21 reused P/I definitions as LP anchor nodes (I/P/W precedent),
  or import them from graph P? Recommendation: anchors, for those that MAIN §1 transcribes.
- **Q7 (Markdown tooling).** The shared `inp_depgraph_preextract.py` reads LaTeX labels only. Either the writer
  converts `draft/coverage-*.md` into slice packets with a small `docs/graph/LP/tools/lp_depgraph_preextract.py`
  (Markdown, locator tokens from §2), or the extractors start from the draft coverage directly. The slice check,
  assemble and review tools work unchanged, because they check paths and line ranges only.
- **Q8 (roles).** The [CONFIRM] items of §8: writer tag, extractor option, Codex account, Opus scope, batch
  parallelism.

## Change log

- 2026-11-01: initial pre-freeze draft (pinning, inventory, slice plan, roles). No extraction, no header, no edges.
