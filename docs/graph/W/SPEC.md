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

## Reachability
- **Wave 1.** The root had no proof, so nearly all W0n–W3 nodes were unreachable. They were kept, not excluded, and
  the linter ran without `--require-all-reachable`.
- **Wave 2 (from 2026-10-30).** W8 is in the corpus and the root's PROOF_SOURCE is the proof of
  `bpW:w8:nlw2-proof`. `--require-all-reachable` is part of the gate. A node outside the closure is linked (a missed
  use) or EXCLUDED with the reason "outside every root closure of track W" plus the check made.

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

Status after delta 6 and the W4–W6 gap repair (2026-10-30):

| Slice | Source range | Nodes (REVIEWED/total) | Edges | Coverage (REVIEWED/total) |
|---|---|---|---|---|
| `W-w0c` | w0-conventions.tex, all (10 of the 13 anchors) | 18/18 | 43 | 41/41 |
| `W-w0n` | w0-normalization.tex, all | 31/31 | 117 | 62/62 |
| `W-w1a` | w1-sequences.tex L1–590 | 66/66 | 188 | 96/96 |
| `W-w1b` | w1-sequences.tex L591–end | 67/67 | 176 | 96/96 |
| `W-w2` | w2-reconstruction.tex, all | 33/33 | 189 | 60/60 |
| `W-w3` | w3-birkhoff.tex, all | 89/90 | 339 | 141/141 |
| `W-w4` | w4-homological.tex, all | 55/58 | 167 | 102/103 |
| `W-w5a` | w5-kamstep.tex L1–466 | 41/53 | 181 | 74/77 |
| `W-w5b` | w5-kamstep.tex L467–end | 28/32 | 122 | 48/48 |
| `W-w6` | w6-iteration.tex, all | 41/47 | 176 | 70/70 |
| `W-w7a` | w7-measure.tex L1–459 | 50/51 | 154 | 79/79 |
| `W-w7b` | w7-measure.tex L460–end | 41/41 | 122 | 62/63 |
| `W-w8a` | w8-assembly.tex L1–410 | 55/56 | 208 | 79/79 |
| `W-w8b` | w8-assembly.tex L411–end | 43/46 | 200 | 61/61 |
| `W-wh` | w-headline.tex, all (3 anchors: embedding, IsDiophantine, the root nlw2) | 3/3 | 12 | 14/14 |
| `W-imports` | imported track-K nodes (writer-owned) | 4/4 | 0 | 4/4 |

A node belongs to the slice containing the first line of its STATEMENT_SOURCE, and coverage items follow their
SOURCE line.

## Change log
- 2026-10-30: initial specification (wave 1: W0–W3 and the headline).

## Sub-orchestrator rulings
- **2026-10-30 (kam-d4):** `KAM.IsDiophantine` (`kam.IsDiophantine.v1`) is kept as the 13th anchor
  `bpW:wh:dioph#IsDiophantine`, following the I/P precedent. It is an existing frozen manifest anchor that the frozen
  `nlw2` imports, so nothing new is frozen.

## Change log (continued)
- **2026-10-30, after slice review round 1** (W-w0c FAIL, W-w0n FAIL, W-wh PASS). The fragments were applied with
  `inp_depgraph_apply_review.py`; the PASS records were marked with `inp_depgraph_mark_reviewed.py`.
  - From now on the *packets* of W-w0c, W-w0n and W-wh are the source of truth. `w_depgraph_fill.py` refuses to
    re-render a packet that holds reviewed or reviewer-written records.
  - The reviewers' two general lessons are adopted for every slice. The W-w1a, W-w1b, W-w2 and W-w3 specs were
    re-rendered with both.
    - **Step source fields.** A step's `SOURCE_HYPOTHESES` are the premises of the enclosing statement (its proof
      context) plus local definitions. Results derived earlier in the proof are DEPS, never hypotheses. The step's
      `SOURCE_QUANTIFIERS` inherit the enclosing statement's scope. Rendered by `STEP_CONTEXT = True`.
    - **Direct symbol uses.** Every node whose statement or proof text uses a frozen object by symbol depends on its
      anchor, at the first line of use. The symbols are:
      - λ (`lam`), φ_j (`sineMode`);
      - U_m / D^0 (`reconU`), V_m (`reconV`);
      - G_q, 𝒢 (`cubicGrad`);
      - `coeff`, `WaveSpace`;
      - K^0_I (`linearTorus`);
      - `IsClassicalSolution`, `IsAnalyticTorusEmbedding`.

      Rendered by `SYMBOL_EDGES = True` with the rationale "… occurs directly here". This tightens the carrier rule
      above: a node that writes λ_j depends on `lam` even when it also depends on `lambda-facts`.
  - Reviewer-added nodes in W-w0c: `bpW:w0:ellap#spaces` (the general ℓ^{a,p}, ℓ^{a,p}_ℂ, E_{a,p} of L52–56) and
    `bpW:w0:reconstruction#rescaling` (L78–80). They also added the display items `bpW:w0:eq` and `bpW:w0:coeffsys`
    (KIND corrected from `equation` to `display` by the writer).
- **2026-10-30, imports.** W-w1b uses five track-K results. They are imported in the writer-owned slice `W-imports`,
  with source fields copied from `docs/graph/K/DEPGRAPH.md` and `blueprint/parts/p1-analysis.tex` pinned in
  `IMPORTS.sha256`:
  - `K:bp:p1:holomorphic-analytic`, used by `stepW:w1:hacoef`. The step uses K's proof with W replaced by a complete
    F, a carrier change argued at L821–823.
  - `K:step:p1:dec-shift`, used by `stepW:w1:shift`. The text cites the shift as "`bp:p1:fourier-basic`", a
    suspected misreference reported as an erratum; it is applied with an arbitrary shift η.
  - `K:bp:p1:fourier-basic` and `K:bp:p1:strip-identity`, used by `stepW:w1:fsum`.
  - `K:bp:p1:decay`, used by `stepW:w1:fbdecay`.
- **2026-10-30, after the batched review** (codex-1): W-w0c and W-w0n deltas (review-2); W-w1a, W-w1b, W-w2, W-w3
  and W-imports (review-1). Every slice verdict was FAIL, with replacement blocks and no unresolved rows.
  - Applied with `inp_depgraph_apply_review.py` and marked with `inp_depgraph_mark_reviewed.py`.
  - The reviews state "all other coverage items PASS". The items they pass this way, without an explicit row, are
    marked by the new `tools/w_depgraph_mark_coverage_rest.py`. W-wh round 1 was processed the same way.
  - Writer adjudications:
    - the two route nodes `stepW:w3:XG#via-w0-gradient` and `#via-w1-gradient`, added by the reviewer, got their
      missing EDGE lines (`inp_depgraph_route_edges.py`, locator L301) and their coverage mapping;
    - the reviewer's edge `bpW:w2:ext-trig -> bpW:w0:basis#lam` was dropped, because an external must be a leaf (the
      linter rejects it); the consumers already depend on `lam`.
  - Reviewers exposed four SOURCE_GAP notes:
    - `stepW:w1:shift`: the contour shift is cited as `bp:p1:fourier-basic`, and the arbitrary-η generalization of
      `K:step:p1:dec-shift` is not given;
    - `stepW:w3:XG` and its two routes: the a = 0 case is not covered by the cited gradient results, which assume
      a > 0.
- **2026-10-30, delta review 2 and corpus re-pin.**
  - Delta review 2 (codex-1; review-3 for W-w0c and W-w0n, review-2 for the others) was applied and marked. Its
    replacements left 5 nodes PROPOSED: `stepW:w1:flowlim`, `stepW:w3:gradtrans`, `stepW:w3:majY`, `stepW:w3:majps`,
    `stepW:w3:conj`.
  - inp was merged into inp-wgraph (the blueprint cleanup 99afc128), and the wave-1 corpus was re-pinned in
    `CORPUS.sha256`. W4 and W7 are in inp but not in the corpus (wave 2).
  - Every locator was remapped mechanically from fa002b43 with `tools/w_depgraph_remap_locators.py`, a W copy whose
    path regex accepts `blueprint-W`.
  - Writer revisions r2 (`EXTRACTOR ... +claude-suborch-W-r2`, all PROPOSED):
    - **Restated statements:** `bpW:w0:twosided` (convolution for s >= 0), `bpW:w0:H` (G on l^{a,p}, a > 0; edge to
      recon-bounded), `bpW:w0:Gq#cubicGrad` (domain l^{a,p}; the frozen cubicGrad is the l^{1,1} case; edges to
      recon-bounded and ellap#spaces), `bpW:w0n:gradient`, `bpW:w0n:cubic-bound`.
    - **Re-worded steps:** `stepW:w1:ext`, `stepW:w1:restr`.
    - **New nodes:** the external `bpW:w1:ext-rect`; the lemma `bpW:w1:fourier-shift` with its steps `fshift-one`,
      `fshift-iter`, `fshift-end`.
    - **Resolved SOURCE_GAPs:** `stepW:w1:shift` now uses fourier-shift, and the import `K:step:p1:dec-shift` is
      pruned; `stepW:w3:XG` now covers every a >= 0, and its two route nodes are deleted, because the a > 0
      citations are now consistency remarks.
    - **Coverage:** two headline prose items have new exclusion reasons.
  - The specs (`specs/`) and `draft/` are wave-1 historical inputs; the packets are the source of truth.
- **2026-10-30, delta review 3** (codex-1: W-w0c-review-4, W-w0n-review-4, W-w1a-review-3, W-w1b-review-3,
  W-w3-review-3, W-wh-review-2). Applied and marked.
  - The residual FAIL rows all came with replacement blocks: a missing `lam` edge (`stepW:w3:XG`, L303), a missing
    `flowlip` edge (`stepW:w1:flowlim`, L903-L904), and stale in-text preamble line numbers (`stepW:w3:majY`,
    `majps`, `conj`). These 5 nodes are PROPOSED for delta 4.
  - The writer then remapped *in-text* line references (`(proof preamble L…)`, `L…` in SOURCE_*/NOTE/EDGE
    rationales) from fa002b43 to the re-pinned corpus, with the same line map as the locators. This is a mechanical
    remap like the locator remap, so statuses are unchanged. It touched 33 records, e.g. the W3 preambles now cite
    L336-L338, L632 and L708-L709.

- **2026-10-30, wave 2 extraction** (writer tag `claude-suborch-W-w2`; inp merged, all eleven parts re-pinned, wave-1
  locators and in-text line numbers remapped).
  - New slices W-w4, W-w5a/b, W-w6, W-w7a/b, W-w8a/b (380 nodes) from specs `specs/W-w4.py` … `W-w8b.py`.
  - W5–W8 symbol policy: a bare `\lambda` there is P96-K's weight parameter, so `bpW:w0:basis#lam` matches only
    `\lambda_{1,2,j,J,i,n}` and `\Lean{lam`. In W7/W8 `\phi` is a phase, so `sineMode` matches only
    `\Lean{sineMode`. `linearTorus` matches `K^0_` and `\Lean{linearTorus`.
  - Unlabelled prose that fixes data is a `<section>#data` definition node (`bpW:w7#data`, `bpW:w7:basic#data`,
    `bpW:w8#data`, …).
  - W-w3 gains `bpW:w3:transport-tori-weak` and its steps `wk-lin`, `wk-reg`, `wk-transport`.
  - Root: PROOF_SOURCE = `w8-assembly.tex#bpW:w8:nlw2-proof@L552-L599`, plus one edge to `bpW:w8:nlw2-proof`. The
    frozen fields are unchanged and the record is PROPOSED.
  - Cycle repair: Definition `bpW:w7:constdef` (C3) uses σ_X, c_X of Lemma `bpW:w7:Xzones`, whose proof uses
    (C4). The definitional part is the separate node `bpW:w7:Xzones#consts` (L422–L426), and constdef depends on it.
  - All-reachable check: these nodes are EXCLUDED as "outside every root closure of track W", each with the check:
    `bpW:w0:reconstruction#rescaling`; `bpW:w0n:pde-equiv` with steps `time`, `ident`, `converse` (W2 uses only
    step `stepW:w0n:force`, which stays); `bpW:w0n:formal-birkhoff` (W3 re-derives it and cites it only in source
    notes); `bpW:w0n:duffing` and the ledger fact `bpW:w0n:ledger#ext-lindstedt`; `bpW:w4:k0` with steps `k0one`,
    `k0diff` (the k = 0 conditions downstream come from W7 Lemma `bpW:w7:sep`).
  - Excluded remarks re-checked against W4–W8: `w1:kam-conventions`, `w3:interface`, `w3:class-remark`,
    `wh:weakenings` and `w0n:kappa` are cited only in prose, source notes or excluded remarks, except W6 step
    `t-an`, which cites `w3:class-remark`; that edge goes to `bpW:w3:flow`. They stay EXCLUDED with updated reasons.
    `operator-fourier`, `w2:hyp`, `w2:constants`, `w2:hidden` and `wh:reading` have no W4–W8 citations.
  - The linter passes with `--require-complete-coverage --require-initial-lean-status --require-all-reachable`:
    690 nodes, 2260 edges, all in the root closure.

- **2026-10-30, wave-2 review 1 and delta 5** (codex-1; tags `sol-review-W-W-<slice>` for W-w4–W-w6, as written in
  those files, and `sol-review-W-<slice>` for W-w7a–W-w8b; `sol-delta5-W-<slice>`). Applied with
  `inp_depgraph_apply_review.py`, marked with `inp_depgraph_mark_reviewed.py` and `tools/w_depgraph_mark_coverage_rest.py`.
  - W-wh, W-w0n and W-w0c delta 5 passed: the root edge and all reachability exclusions are confirmed.
  - Rule 11 restored two remarks as claim nodes: `bpW:w3:class-remark` (cited in W6 step `t-an`, L374) and
    `bpW:w1:kam-conventions` (cited in the statement of Convention `bpW:w4:index`, L87). The delta reviewers'
    cross-slice blocks for `stepW:w6:t-an` and `bpW:w4:index` were merged into the owning packets (W-w6, W-w4) as one
    added edge each; the tool had appended them to W-w3 and W-w1b. Both restored claims get PROOF_SOURCE = their
    statement locator, as for the other kept remarks.
  - Reviewers exposed 10 SOURCE_GAP nodes: `stepW:w4:schurrep`, `stepW:w5:t-comp`, `c-skew`, `n-exp`, `p-inv`,
    `a-hol`, `bpW:w6:prep-step`, `stepW:w6:p-lipp`, `bpW:w6:freq-lip`, `stepW:w6:fl-borel`. The writer reset
    `stepW:w5:n-exp`'s LEAN_NOTE to `-` (initial-Lean gate); the gap stays in its NOTE.
  - The linter passes with `--require-all-reachable`.

- **2026-10-30, delta 6 and the W4–W6 blueprint gap repair** (writer tag `claude-suborch-W-gapfix`).
  - Delta 6 (tags `sol-delta6-W-W-<slice>`, as written in the files) was applied, marked and coverage-rested. It
    passed W-w1b, W-w5b and W-w7b; the other slices' FAIL rows came with replacement blocks.
  - The blueprint repair (blueprint-W/reviews/gapfix-review-1.md) was merged from inp-wbp 565c9040 (the one
    allowed merge; inp did not have it yet). w4, w5 and w6 were re-pinned (CORPUS.sha256; header CORPUS line).
    Locators were remapped with `tools/w_depgraph_remap_locators.py 9b5d2603` and in-text line numbers with the
    in-text pass. The W5 slice boundary moves from L450 to L467 (`slices.json`).
  - New external leaves: `bpW:w4:ext-riesz`, `bpW:w5:ext-symm`, `bpW:w5:ext-sqrt`, `bpW:w5:ext-triangle`, with
    coverage items.
  - All 10 SOURCE_GAP nodes are closed and their NOTEs removed. The changed records go to PROPOSED:
    - `stepW:w4:schurrep`: Riesz construction; edges `ext-riesz`, `w1:ext-lp`, `w1:schur`, `w4:index`.
    - `stepW:w5:t-comp`, `c-skew`: `ext-symm`.
    - `stepW:w5:s-out`: the lie edge now cites (iv) under the guard (G).
    - `stepW:w5:n-exp`: `ext-triangle`.
    - `stepW:w5:p-inv`, `p-ass`: difference bounds carry |ξ−ζ|.
    - `stepW:w5:a-hol`: `ext-sqrt`.
    - `bpW:w6:prep-step`, `stepW:w6:p-div`: the divisor bound comes directly from Definition `bpW:w7:zones`(i);
      the edge to `bpW:w7:melnikov` is dropped.
    - `stepW:w6:p-lipp`: sup bound via `stepW:w5:f-flow`.
    - `bpW:w6:freq-lip`: wording; θ is fixed before α.
    - `stepW:w6:fl-borel`: direct Borel argument; the edge to `bpW:w7:measurable` is dropped.
  - `bpW:w7:melnikov` then lay outside the root closure. It is EXCLUDED: its only consumer was prep-step(i), and the
    remaining citations are in excluded remarks.
  - The linter passes with `--require-all-reachable`: 696 nodes, 2394 edges, 0 SOURCE_GAP, review queue 31.
  - `GLOBAL-BRIEF.md` was written for the global reviewer `sol-global-W`.

- **2026-10-31, delta 7** (tags `sol-delta7-W-<slice>`; track W resumed by owner ruling D53).
  - Applied, marked and coverage-rested. PASS: W-w4, W-w5b, W-w7a, W-w7b, W-w8a, W-w8b.
  - The FAIL rows came with replacement blocks, which were applied: `bpW:w3:class-remark` (stale in-text line L374 ->
    L383), `stepW:w5:t-comp` (edge to the class definition), `bpW:w6:prep-step` (conclusion records the zones(i) bound
    and the onto property, plus a wave(ii) edge) and `stepW:w6:p-lipp` (omega edge). These 4 nodes are PROPOSED for
    delta 8.
  - The corpus on inp (9c6d9128) matches the pins (CORPUS.sha256 and IMPORTS.sha256 all OK), so nothing was re-pinned.
  - The linter passes with `--require-all-reachable`: 696 nodes, 2397 edges, 0 SOURCE_GAP, review queue 4.

- **2026-10-31, delta 8** (tags `sol-delta8-W-W-<slice>`, as written in the files): W-w3, W-w5a and W-w6 PASS and are
  marked. All 696 nodes and 1094 coverage items are REVIEWED; 0 SOURCE_GAP. The gate with `--require-reviewed` now fails
  only on the placeholders `GLOBAL_REVIEWER` and `GLOBAL_REVIEW_REF`, which await the global review `sol-global-W`
  (GLOBAL-BRIEF.md).

## Wave-2 plan (proposed 2026-10-30; extraction starts on the sub-orchestrator's go)
- **Corpus.**
  - Once W4–W8 are accepted and on inp, merge inp again.
  - Re-pin all eleven parts.
  - Remap the wave-1 locators (text and locators) with `tools/w_depgraph_remap_locators.py` and the in-text pass.
  - The W3 revision adds `bpW:w3:transport-tori-weak` (a new node in W-w3); W7 carries the accepted β = 1/4
    revision.
- **Slices.** One per part; the large parts are split at subsection boundaries. Approximate unit counts are from
  inp-wbp 2f92d968.

  | Slice | Range | ~units |
  |---|---|---|
  | `W-w4` | w4-homological.tex, all | 64 |
  | `W-w5a` | w5-kamstep.tex L1–449 (externals, setting, W4 generalization, Taylor, step data, flow) | 50 |
  | `W-w5b` | w5-kamstep.tex L450–end (new Hamiltonian, pull-back, commutators, one KAM step, action–angle, initial perturbation) | 32 |
  | `W-w6` | w6-iteration.tex, all | 46 |
  | `W-w7a` | w7-measure.tex L1–459 (externals, indices, frequencies, constants, interface, slicing and zone lemmas) | 50 |
  | `W-w7b` | w7-measure.tex L460–end (preparatory/iteration zones, measure theorem, density, Diophantine, frequency limit) | 43 |
  | `W-w8a` | w8-assembly.tex L1–410 (externals, shell data, shell iteration, shell tori) | 60 |
  | `W-w8b` | w8-assembly.tex L411–end (patching, family injectivity, the proof of W-NLW2) | 43 |
- **Pre-extraction.**
  - Run `tools/w_depgraph_preextract.py` on all eleven parts, so that `\ref`s into W0–W3 resolve, with the same
    anchor map and `--proved-in bpW:wh:nlw2=w8-assembly`. W8's references to the headline state what it proves; they
    are not uses.
  - Split into a scratch directory and copy only the new slices' packets (`w_depgraph_split.py` refuses to overwrite
    the reviewed wave-1 packets).
  - Wave-2 externals are the ext-lists of W4 (4), W5 (2), W7 (7) and W8 (8).
  - The `\sourcegap` notes (W4: 1, W5: 2) are handled as in wave 1.
- **Root.** `bpW:wh:nlw2` gets PROOF_SOURCE = the proof environment of `bpW:w8:nlw2-proof` (w8-assembly.tex, from
  L552), replacing the provisional statement locator, and a DEPS edge to `bpW:w8:nlw2-proof` ("this result proves
  the frozen anchor", as for track I's `bpI:p2:g1`). Its frozen identity fields are unchanged. The record goes back to
  PROPOSED for a delta reviewer.
- **Reachability.**
  - The root closure then runs through W8's 17 proof steps into W2 (`bpW:w2:clause5`), W3, W5–W7 and the W1/W0
    support.
  - `--require-all-reachable` becomes part of the gate.
  - Every wave-1 or wave-2 node outside the closure is then checked against the text, and is either linked (a missed
    use) or EXCLUDED with "outside every root closure of track W" plus the check made.
  - Likely candidates are the consistency checks `bpW:w0n:duffing` and `bpW:w0n:ledger#ext-lindstedt`, and parts of
    W0n/W1 that W4–W8 do not consume (e.g. `bpW:w0n:formal-birkhoff`, `bpW:w1:flow`).
  - Excluded remarks (`kam-conventions`, `operator-fourier`, `w2:hyp`, `w3:interface`) are re-examined against W4–W8
    citations.
- **Review.** As in wave 1: writer extraction from specs, then one batched GPT-6.1-Sol review of the new slices plus
  delta reviews of the re-opened wave-1 records (root, W-w3 additions, re-linked nodes), then the global review
  (`sol-global-W`) once the whole graph is reachable.
