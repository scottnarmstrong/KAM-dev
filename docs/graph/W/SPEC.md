# Track W dependency graph: extraction specification

Fixed before extraction (skill `build-proof-dependency-graph`, Phase 1). It follows track I's specification
(`docs/graph/I/SPEC.md`) and states only what track W needs. It binds the writer and the reviewers. Changes are
recorded at the end with a date and a reason.

Track W is built in **waves**. Wave 1 (this specification) covers the accepted parts W0–W3 and the headline. Parts
W4–W8 are still being written. Each later part becomes one or more new slices (`W-w4`, `W-w5`, …). The root's proof
(the W8 assembly) is added in the wave that brings W8.

## Roots and anchors
- **Root:** the frozen theorem `KAM.Wave.nlw2` (manifest `wave.nlw2.v1`), node `bpW:wh:nlw2` (statement:
  `blueprint-W/parts/w-headline.tex` L41–L65). Its proof is milestone W8, which is not yet in the corpus. Until W8
  exists, the root's DEPS lists only the definitions that its statement uses.
- **Anchors (13).** These are the twelve frozen W declarations (`KAM/Frozen/Wave/{Defs,Theorems}/`, manifest IDs
  `wave.*.v1`), plus the track-K definition `KAM.IsDiophantine`. The frozen `nlw2` uses that definition, and the
  headline transcribes it (`bpW:wh:dioph`). This follows the track-I and track-P precedent: when a part transcribes a
  K definition, it becomes the track's own anchor node, bound to K's manifest entry (`kam.IsDiophantine.v1`), and is
  never imported. Definition anchors have the ID `<label>#<LeanName>`.

### Anchor mapping (Part 0 labels → frozen declarations)
Blueprint-W carries no `\frozen{…}` tags. The writer binds the anchors with `w_depgraph_preextract.py --anchor-map`,
using the docstrings of the frozen files, which name their blueprint labels.

| Blueprint label (file) | Node | Lean export | Manifest anchor |
|---|---|---|---|
| `bpW:w0:nlw` (w0-conventions L29–35) | `bpW:w0:nlw#IsClassicalSolution` | `KAM.Wave.IsClassicalSolution` | `wave.IsClassicalSolution.v1` |
| `bpW:w0:basis` (L39–42) | `bpW:w0:basis#lam` | `KAM.Wave.lam` | `wave.lam.v1` |
| `bpW:w0:basis` | `bpW:w0:basis#sineMode` | `KAM.Wave.sineMode` | `wave.sineMode.v1` |
| `bpW:w0:ellap` (L51–57) + Convention `bpW:w0:weights` | `bpW:w0:ellap#ellWeight` | `KAM.Wave.ellWeight` | `wave.ellWeight.v1` |
| `bpW:w0:ellap` + `bpW:w0:weights` | `bpW:w0:ellap#WaveSpace` | `KAM.Wave.WaveSpace` | `wave.WaveSpace.v1` |
| `bpW:w0:ellap` + `bpW:w0:weights` | `bpW:w0:ellap#coeff` | `KAM.Wave.coeff` | `wave.coeff.v1` |
| `bpW:w0:reconstruction` (L75–81) | `bpW:w0:reconstruction#reconU` | `KAM.Wave.reconU` | `wave.reconU.v1` |
| `bpW:w0:reconstruction` | `bpW:w0:reconstruction#reconV` | `KAM.Wave.reconV` | `wave.reconV.v1` |
| `bpW:w0:Gq` (L96–101) | `bpW:w0:Gq#cubicGrad` | `KAM.Wave.cubicGrad` | `wave.cubicGrad.v1` |
| Convention `bpW:w0:periodone` (L136–144) = `bpW:wh:lintorus` | `bpW:w0:periodone#linearTorus` | `KAM.Wave.linearTorus` | `wave.linearTorus.v1` |
| `bpW:wh:embedding` (w-headline L22–27) | `bpW:wh:embedding#IsAnalyticTorusEmbedding` | `KAM.Wave.IsAnalyticTorusEmbedding` | `wave.IsAnalyticTorusEmbedding.v1` |
| `bpW:wh:dioph` (L33–37) | `bpW:wh:dioph#IsDiophantine` | `KAM.IsDiophantine` (track K) | `kam.IsDiophantine.v1` |
| `bpW:wh:nlw2` (L41–65) | `bpW:wh:nlw2` | `KAM.Wave.nlw2` | `wave.nlw2.v1` |

**The mapping is not one-to-one, unlike track I's `bpI:p0:*`.**
- *Three labels carry more than one anchor:* `bpW:w0:basis` (2), `bpW:w0:ellap` (3), `bpW:w0:reconstruction` (2).
- *Two anchors live outside Part 0 proper:* `bpW:wh:embedding` and `bpW:wh:dioph` are in w-headline. The frozen
  linear torus is bound to the Convention `bpW:w0:periodone`, where its formula is. `bpW:wh:lintorus` only points to
  that Convention, so it is not a node; its coverage item maps to `bpW:w0:periodone#linearTorus`.
- *Convention `bpW:w0:weights`* (a = p = 1) has no anchor of its own. It is realized by `WaveSpace`, `coeff` and
  `ellWeight 1 1`, and its coverage item maps there.
- *Part 0 labels with no frozen counterpart* stay ordinary nodes:
  - `bpW:w0:mass` is the standing assumption (below);
  - `bpW:w0:twosided`, `bpW:w0:H`, `bpW:w0:eqmotion`, `bpW:w0:z` and `bpW:w0:actions` are `definition` nodes;
  - Remark `bpW:w0:harmless` is excluded.
- `bpW:wh:Dnu` (D_ν K = DK ν) is notation that the frozen statement inlines (a `HasDerivAt` along t ↦ θ + tν at
  t = 0). Its coverage item maps to `bpW:wh:nlw2`.

Anchor identity (file, export, anchor ID, contract ID/version, ABI hash) is copied from `manifest/frozen-anchors.json`
and bound by the linter. It is never edited in the graph. Anchors belong to slices `W-w0c` and `W-wh`.

## Corpus
- The accepted parts `blueprint-W/parts/{w0-conventions,w0-normalization,w1-sequences,w2-reconstruction,
  w3-birkhoff,w-headline}.tex`, pinned in `docs/graph/W/CORPUS.sha256` (branch `inp`, fa002b43, 2026-10-30).
- Their acceptance records:
  - W0: `docs/tracks/W/audits/W-BP0-audit-{1,2}.md`;
  - W1: `blueprint-W/reviews/w1-review-{1,2}.md`;
  - W2: `w2-review-1.md`;
  - W3: `w3-review-{1,2}.md`.
- Any later change to a pinned file is recorded below with the new hashes. Locators are then remapped mechanically
  with a W copy of `inp_depgraph_remap_locators.py`, whose path regex must accept `blueprint-W`, and the affected
  slices are re-checked.
- The pinned papers (P96-W, P96-K, KP96) are provenance only. The blueprint proves everything it uses except the
  external inputs below.

## Standing assumption and carriers
**STANDING_ASSUMPTIONS: `bpW:w0:mass`** (m > 0 fixed). This is `KIND: assumption`, `LEAN_STATUS: ASSUMED`. It is
the only global standing assumption. In Lean it is the carrier `hm : 0 < m`, which `lam`, `reconU`, `reconV`,
`cubicGrad`, `IsClassicalSolution` and `nlw2` take as an argument.

**Carrier rule (to keep the edges direct and few).** m enters almost every statement through λ_j = √(j²+m)
(`bpW:w0:basis#lam`), and `lam` depends on `bpW:w0:mass`.
- A node that uses λ depends on `bpW:w0:basis#lam`, not on `bpW:w0:mass` directly.
- A direct edge to `bpW:w0:mass` is required where m > 0 itself (not merely λ) is used, for example:
  - the equation u_tt = u_xx − mu − u³;
  - the strict convexity of √(s²+m);
  - j < λ_j;
  - (1+m) or √m bounds.

  Such uses usually go through `bpW:w0:basis#lambda-facts`.
- The part openings "Standing assumption `bpW:w0:mass` and the conventions of §`bpW:w0` are in force" are coverage
  prose. They are mapped to the consumers or excluded as a pointer.

**Positive carriers.** `hI : ∀ i, 0 < I i` in `linearTorus` and `nlw2` (I ∈ (0,∞)²). Record it in the source fields
wherever a statement has it.

**Hypothesis packages.**
- The weights (a, p) and 𝕂 ∈ {ℝ, ℂ} of a W1/W3 lemma are typing data. They go in SOURCE_HYPOTHESES and are never
  nodes.
- W2 and W3 open with "Standing data" paragraphs (W2 L25–33, W3 L23–27) that fix notation (κ, ω, a, p ≥ 1/2, J).
  If such a paragraph states a fact that a proof consumes, it becomes a `definition` node `<section label>#data`
  (I-SPEC rule). Otherwise it is mapped to its consumers or excluded as notation.

## External inputs and imports (EXTERNAL_POLICY)
- **Track-W externals.** These are the labelled items of the parts' external-fact lists, `KIND: external`,
  `LEAN_STATUS: EXTERNAL`, all Mathlib-level:
  - `bpW:w1:ext-{lp,series,analytic,onevar,unifderiv,integral,ode,fourier}`;
  - `bpW:w2:ext-{deriv,an,sums,trig}`;
  - `bpW:w3:ext-{multilinear,series,tsum,mvt,integral,neumann}`.

  Remark `bpW:w3:ext-flows` is not an external: it states what Mathlib lacks.
- **Unlabelled W0 externals.** The W0 ledger (w0-normalization L422–423) lists "external standard facts" without
  labels:
  - completeness of (φ_l) in L²(0,π) is the W1 lemma `bpW:w1:sine-completeness`, proved there from
    `bpW:w1:ext-fourier`, so the W0 consumer depends on that lemma;
  - analyticity of continuous multilinear maps is `bpW:w1:ext-analytic`;
  - Young's inequality is the W1 lemma `bpW:w1:young`;
  - ζ(3) < ∞ is `bpW:w1:ext-series`;
  - the classical Lindstedt frequency shift (used only by `bpW:w0n:duffing`) becomes the external node
    `bpW:w0n:ledger#ext-lindstedt`.

  These are the only externals not taken from an ext-list.
- **Alias rule.** An ext-list item that only restates another external is EXCLUDED as "alias of …", and its
  consumers depend on the cited node. Items that cite a track-K external by `\texttt{bp:p1:ext-…}` *inside* their
  own text (e.g. W1-E4 "Cauchy integral formula (`bp:p1:ext-cauchy`)") are W's own externals. The K label is
  provenance, not an import.
- **Track-K results (import policy).** Blueprint-W has no `\Kref`. It cites track K only by `\texttt{bp:p1:…}` in W1
  §`bpW:w1:analytic`–§`bpW:w1:kam` (`holomorphic-analytic`, `fourier-basic`, `strip-identity`, `decay`,
  `summation`).
  - Where a W proof *uses* such a result, the target is an IMPORTED node `K:<K graph node>`, with:
    - `KIND external`, `LEAN_STATUS EXTERNAL`, `PROOF_SOURCE -`, `DEPS -`;
    - STATEMENT_SOURCE at its locator in `blueprint/parts/`;
    - source fields copied from `docs/graph/K/DEPGRAPH.md`;
    - NOTE `IMPORTED: proved in the track-K graph, node <label>; shared Lean provider`.
  - The imported nodes form the writer-owned slice `W-imports`, with the K blueprint files pinned in
    `docs/graph/W/IMPORTS.sha256`.
  - A mention that W re-proves the result (e.g. "the proof of K's Lemma … carries over") is *not* an import. The W
    node then owns the argument, and the K label is provenance.
  - Track-K externals `K:bp:p1:ext-*` are imported only when a W proof uses one that no W ext item restates.
- **Other gaps.** A proof that uses a fact which is neither proved in the corpus, nor a W external, nor an imported
  result gets a step node with `NOTE: SOURCE_GAP: …`. Never a silent edge, and never an additional external without
  a SPEC revision.
  - The `\sourcegap` notes (w0-normalization L159; w1-sequences L906, L1105; w3-birkhoff L366, L750) record defects
    *in the pinned papers* that the blueprint repairs. Map each one to the node(s) that supply the repair. If the
    blueprint leaves a gap open, model a SOURCE_GAP node.
  - The writer reports every such note in the handoff.

## Conventions to watch (the global reviewer checks these across slices)
- **Weighted coordinates.**
  - The frozen phase space `WaveSpace` = ℓ²(ℕ₊;ℝ) × ℓ²(ℕ₊;ℝ) holds *weighted* coordinates y.
  - The Fourier–sine coefficients are q_j = `coeff y j` = y_j / (j e^j) (κ_{1,1}).
  - W1 transports every ℓ^{a,p} to ℓ² by τ_{a,p}, κ_{a,p}.
  - A record must say whether it speaks of coefficients (q) or of weighted coordinates (y). For example, G^w(y)_l =
    ω_{1,2}(l)·`cubicGrad m hm y l`, and X^w has the coordinates of X_H times ω_{1,0}(j) = e^j.
- **ℕ₊ indexing.**
  - Modes are j ∈ ℕ₊ (`PNat`), j ≥ 1.
  - The tangential `i : Fin 2` is mode j = i + 1 (`(i : ℕ).succPNat`).
  - Normal modes are j ≥ 3, with the entries j = 1, 2 set to zero in Lean.
  - P96-K indexes the normal modes from 1, a shift of 2.
- **Period-one angles.**
  - Torus angles θ have period one, φ_j = 2πθ_j, and the campaign frequency is ν = ω/(2π).
  - (θ, Y = 2πI) is canonical.
  - Small divisors are 2π k·ν + l·Ω.
  - The linear flow rotates *clockwise*: ż_j = −iλ_j z_j, φ increases. P96-W is time-reversed.
  - Track every factor 2π.
- **Max norm on WaveSpace.**
  - ‖(q,p)‖_E = max(‖q‖, ‖p‖), which is Mathlib's product norm.
  - Factors √2 appear where the source uses a Hilbert product norm: W1 `diag`(iv) ‖L_t‖ ≤ √2, and the pairing J in
    W1 `twosided`(iii).
- **Two-sided spaces.** The weight is ⟨l⟩^{2s} e^{2a|l|} with ⟨l⟩ = max(1, |l|). The constant is
  K_s = 2^s (1+2ζ(2s))^{1/2}; C_* = K_{p+1/2}²/π; C_m = 8(1+2ζ(3))/π, independent of m.
- **Corrected normal-form coefficients (E-PDE-W-1/2).**
  - A_ii = 9/(8πλ_i²), A_12 = A_21 = 3/(2πλ_1λ_2), B_ji = 3/(2πλ_jλ_i). These are 1/16 of P96-W's printed
    Ḡ_ij = (6/π)(4−δ_ij)/(λ_iλ_j).
  - The quartic prefactor is 1/16 in z.
  - The action is I_j = |z_j|² = (q_j²+p_j²)/2.
  - The recovery is q = √2 Re z.
  - The other corrections are: the √2 in the majorant (N-1), the sign of λ_j² q_j (N-4) and KP96 p. 13 (N-5).
  - A record that copies a printed P96-W constant, action or sign fails.
- **Positive carriers.** hm : 0 < m and hI : ∀ i, 0 < I i are carriers of frozen declarations, not proof steps.
- **Headline constants.**
  - r₀, C, τ, η, Γ, ν, K are chosen after m and before I, θ₀; γ_I is chosen per I.
  - C is common to (3) and (5).
  - τ > 1.
  - Γ is Borel, with density one at 0 in the sup-norm ball B_h.
  - No uniformity in m is claimed.
- **Constants elsewhere.** Record every constant's dependence list exactly as stated, e.g. "independent of m"
  (C_m), "depending on m, a, p" (W3 §`bpW:w3:constants`).
- **Real versus complex.** 𝕂 ∈ {ℝ, ℂ}. Holomorphic (complex Fréchet differentiable, W1 `bpW:w1:holomorphic`) is
  not the same as analytic. Analyticity is claimed only on finite-dimensional domains or for polynomial maps (W1
  Route, W3 `ext-flows`).

## Node threshold
As in tracks K and I:
- every labelled result environment (theorem, proposition, lemma, corollary, definition, convention, assumption),
  every `\proofstep` and every labelled external item is a node, unless it is excluded with a reason;
- a further step node, ID `<parent>#<slug>`, is added only for an unmarked substantive obligation:
  - a nontrivial estimate or application;
  - a construction;
  - a case split;
  - a witness or parameter choice;
  - a quantifier closure;
  - a carrier change;
  - a reused intermediate claim;
- no nodes for routine algebra.

**Remarks.** Administrative remarks are `EXCLUDED`: deviations, errata, comparisons with printed constants,
provenance, Lean-totality notes, "requests to W1", "what W3 supplies", status summaries. A remark stays a node
(`KIND claim`) only if a proof consumes a fact it states.

**Labels inside a result.** Equation and item labels map to their enclosing node in the coverage:
- `bpW:w0:eq`, `bpW:w0:coeffsys`;
- `bpW:w0n:g-signed`, `bpW:w0n:force`, `bpW:w0n:Gz`, `bpW:w0n:avgG`;
- `bpW:w2:C1`–`C2`, `bpW:w2:inv`, ….

Refine one into its own node only if consumers use it independently and that matters for the topology.

## Reachability (wave 1)
Every graph node must eventually feed the root. In wave 1 the root has no proof, so nearly all W0n–W3 nodes are
unreachable. They are **not** excluded: they are kept and listed as "awaiting W4–W8".
- The linter runs without `--require-all-reachable` until W8 is in the corpus.
- A labelled result is excluded as "outside every root closure of track W" only after W8 has been extracted.

## Edges
- Direct uses only, conjunctive, `consumer -> prerequisite`. Every edge has one `EDGE:` line locating the use in the
  consumer. Use `¦` for absolute-value bars inside an EDGE rationale.
- **Not edges:**
  - forward pointers (e.g. "by Lemma `bpW:w0n:gradient`, G_q(q)_l = ∂G/∂q_l" inside Definition `bpW:w0:Gq`, which
    would otherwise close a cycle);
  - comparisons with the source;
  - provenance (`\source{…}`; "This lemma is the W1 node …");
  - "is not used" / "does not use" mentions (e.g. W3 `ext-flows` and Lemma `bpW:w1:flow`);
  - mentions of a hypothesis being checked.
- **Cross-part uses are ordinary edges.** For example:
  - W1's `bpW:w1:algebra` *is* `bpW:w0n:algebra` (its proof says so);
  - W0n's force step uses W1's sine completeness;
  - W2 uses W1's `trifrozen` step.

  A step node of another part may be a dependency when the text cites the step (e.g. "Step `stepW:w1:trifrozen`").
- **Alternatives** ("either … or …", "equivalently, by …") become `KIND: route` nodes, but only when the text
  presents each as sufficient.

## Roles
- **Writer and extractor:** `claude-suborch-W` (the track-W sub-orchestrator's writer, Opus 5.5). It is the single
  writer of all packets, under the low-cost policy of 2026-10-30. It extracts every slice itself, from the compact
  specs in `docs/graph/W/specs/<slice>.py`, rendered by `tools/w_depgraph_fill.py`. Every node and coverage item it
  wrote has `EXTRACTOR: claude-suborch-W`.
- **Slice reviewers:** GPT-6.1-Sol (Codex, `codex-3`), one fresh session per slice, tagged `sol-review-W-<slice>`,
  distinct from the writer. A node that a reviewer rewrites gets a *different* reviewer (delta review). Reviewers end
  with a whole line `READY <marker>`.
- **Global reviewer:** a fresh GPT-6.1-Sol session, `sol-global-W`, after the slice reviews of a wave.

## Tools
- The shared tools in `/mnt/HC_Volume_106379410/orchestrator-tools/` accept track W, with these exceptions, which
  have W copies in `docs/graph/W/tools/`:
  - `inp_depgraph_preextract.py`: `convention` environments, a list of anchor parts, `--anchor-map`;
  - `inp_depgraph_split.py`: draft globs for `w*` part files.
- Used unchanged:
  - `inp_depgraph_slice_check.py`, `inp_depgraph_assemble.py`;
  - `inp_depgraph_apply_review.py`, `inp_depgraph_mark_reviewed.py`, `inp_depgraph_route_edges.py`;
  - `inp_depgraph_imports.py` (K imports only: its import regex `[KINP]` covers `K:`).
- `tools/w_depgraph_fill.py` renders the writer's specs.

## Slices
Line-addressable, aligned to statement/proof units, and recorded in `docs/graph/W/packets/slices.json`. Each part is
one slice. W1 (128 draft nodes) is split at its §"The sine system" (L591). New parts W4–W8 become new slices.

| Slice | Source range | Draft nodes | Final nodes | Coverage items |
|---|---|---|---|---|
| `W-w0c` | w0-conventions.tex, all (11 of the 13 anchors) | 18 | see handoff | 39 |
| `W-w0n` | w0-normalization.tex, all | 38 | | 62 |
| `W-w1a` | w1-sequences.tex L1–590 (transport, externals, weighted spaces, two-sided, cubic field) | 64 | | 95 |
| `W-w1b` | w1-sequences.tex L591–end (sines, analytic toolkit, KAM support, ledger) | 64 | | 91 |
| `W-w2` | w2-reconstruction.tex, all | 36 | | 60 |
| `W-w3` | w3-birkhoff.tex, all | 84 | | 134 |
| `W-wh` | w-headline.tex, all (2 anchors and the root) | 7 | | 14 |
| `W-imports` | imported track-K nodes (writer-owned, if any) | – | | |

A node belongs to the slice containing the first line of its STATEMENT_SOURCE, and coverage items follow their
SOURCE line.

## Change log
- 2026-10-30: initial specification (wave 1: W0–W3 and the headline).

## Sub-orchestrator rulings
- **2026-10-30 (kam-d4):** `KAM.IsDiophantine` (`kam.IsDiophantine.v1`) is kept as the 13th anchor
  `bpW:wh:dioph#IsDiophantine`, following the I/P precedent. It is an existing frozen manifest anchor that the frozen
  `nlw2` imports, so nothing new is frozen.
