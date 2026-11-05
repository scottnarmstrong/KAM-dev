# Track LP source dependency graph: pre-freeze preparation

Status, 2026-11-01. This directory prepares the track-LP source dependency graph with the skill
`build-proof-dependency-graph`. It contains **only the work the skill allows before the anchors are frozen**. The LP
anchors are not frozen: FREEZE-PROPOSAL draft 7 is in revision (LP-FREEZE7R), and the LP3 delta, draft 8, is in
progress. The owner approves the exact text later. Extraction starts right after the freeze.

The layout follows the precedent graphs `docs/graph/{K,I,N,P,W}/`. In particular `docs/graph/W/` gives `SPEC.md`,
`CORPUS.sha256`, `IMPORTS.sha256`, `draft/`, `packets/slices.json` and `tools/`, and `docs/graph/K/SPEC.md` gives the
roles and slice conventions. Nothing here was committed (the orchestrator commits). No Lean or Lake was run, no Lean
file was read, and nothing under `KAM/` or `manifest/` was touched.


## Post-freeze status (2026-11-01, package LP-GRAPH-W1, writer `kam-lp`)

The anchors are frozen and sealed (D62, main `f46b94fb`). README steps 1–3 are done (pins OK; `packets/anchor-map.tsv`,
`packets/anchor-binding.tsv`; SPEC §1/§8/§10 settled; `header.txt`). Q7's pre-extractor is
`tools/lp_depgraph_preextract.py` (dry run `reports/W1-dryrun.txt`). **Wave 1 (the LP0 closure)** is extracted from
`specs/*.py` (`tools/lp_depgraph_fill.py`) and assembled: 109 nodes, 317 edges, 11 roots (LP0 + 10 characterizations),
59 anchors, 1 SOURCE_GAP, 153 coverage items; lint exit 0 (`reports/W1-lint.txt`). All records are PROPOSED and wait
for review batch R1 (`REVIEW-BRIEF.md`, `reviews/R1-packets.md`). The wave's LEAN_STATUS against the sealed anchors is
`LEAN_STATUS-W1.md` (sync tool `tools/lp_depgraph_lean_sync.py`, applied after publication). The text below is the
pre-freeze preparation record.

## Status after wave 4 (2026-11-01, D64 landed; D65)

The full graph (LP0-LP3: 41 roots) is assembled: 301 nodes, 1161 edges, 149 anchors, 12 externals (2 imports from
track N), 2 routes, 4 SOURCE_GAP steps, 438 coverage items (47 excluded); structural lint exit 0. LEAN_STATUS
(mechanical, D65/D27): PROVED 153 (149 anchors + 4 ordinary nodes by docstring match), BYPASSED 136, EXTERNAL 12,
NOT_STARTED 0 (`LEAN_STATUS.md`, `reports/lean-ref-map.txt`). The ONE global review `maud-lp-gglob-1`
(`reviews/GLOBAL-review-1.md`) is PASS WITH NOTES and is incorporated (header GLOBAL_REVIEWER/GLOBAL_REVIEW_REF; its 11
locator refinements applied); the graph is ready to land.

## Status after LP-GRAPH-W2 (2026-11-01, streamlined under D65)

Waves 1-3 (LP0, LP1, LP1-H, LP2, LP2-H and the 34 characterizations) are extracted and assembled: 292 nodes, 1040
edges, 39 roots, 145 anchors, 2 routes (L12/L13 at `lpM:L14#improvement`), 4 SOURCE_GAP steps, 394 coverage items.
The skill linter passes on structure (`--require-complete-coverage --require-all-reachable`, `reports/W2-lint.txt`);
`--require-reviewed` is dropped by D65, which replaces per-slice reviews by ONE global review (pending). LEAN_STATUS is
applied mechanically (`LEAN_STATUS.md`, `tools/lp_depgraph_lean_sync.py`). LP3 (wave 4) is pending until the D64
anchors are on main. Assembly order: `packets/slices-assembled.txt`. SPEC change log has the details.

## What is done

| File | Content |
|---|---|
| `SPEC.md` | Phase-1 extraction specification, as a pre-freeze draft. It covers: anchor proposal and node IDs (AFTER FREEZE); the source pinning record and the amendment precedence rule; the external and import policy; conventions to watch; the node and edge scheme; reachability; roles and reviewer assignments; slices; open questions Q1–Q8. |
| `CORPUS.sha256` | Pins of the corpus `MAIN.md` (679 lines) and `AMENDMENTS.md` (26 lines). Both sha256 values were verified against the brief: `68e9167f…48c1b` and `c887d1e2…51881`. |
| `IMPORTS.sha256` | Pins of the four candidate import sources: blueprint-N p0, p11b, p11c and blueprint-P p14a. They are identical to graphs N and P. |
| `draft/coverage-main.md` | Coverage inventory of MAIN.md: 228 items. |
| `draft/coverage-amendments.md` | Coverage inventory of AMENDMENTS.md: 14 items (precedence rule, N1–N12, recommended order). |
| `draft/coverage-lp3plan.md` | Coverage inventory of LP3-PLAN.md: 40 items. This is a **candidate** corpus, pending SPEC Q1 and the draft-8 freeze. |
| `packets/slices.json` | The slice plan: 17 planned slices with ranges and estimated sizes. |
| `tools/lp_depgraph_inventory.py` | Regenerates `draft/` and `slices.json` from one table. Use it before extraction only; after that the packets are the source of truth. |

The inventory files use the skill's coverage schema: `ITEM`, `KIND`, `SOURCE`, `DISPOSITION`, `REASON`,
`COVERAGE_STATUS`, `EXTRACTOR`, `REVIEWER`.
- Every item is `PROPOSED`, with extractor `lp-preanchor-inventory` and no reviewer.
- The anchors each item supports are listed in `REASON` as `ANCHORS: …`, because the schema has no field for them.
- The planned slice is listed in `REASON` as `SLICE: …`.

All 282 items pass the linter's own manifest parser and locator check: no parse errors, every path exists, and every
range is within its file.

### Inventory counts

| File | Items | Mapped | Excluded |
|---|---|---|---|
| MAIN.md | 228 | 201 | 27 |
| AMENDMENTS.md | 14 | 10 | 4 |
| LP3-PLAN.md (candidate) | 40 | 33 | 7 |
| **Total** | **282** | **244** | **38** |

MAIN items by kind:
- 2 theorems (T15, T19) and 17 lemmas (L1–L14, L16–L18);
- 11 definitions (§1 groups, D_ρ, the norm (24), the osculating definitions (42));
- all 47 numbered displays (1)–(47);
- 105 proof regions (candidate step nodes) and 15 claims;
- 22 citations: 15 appeals to the 10 candidate externals, the repository citation of L13, and 6 literature and hash
  records;
- 9 headings.

The MAIN exclusions:
- the title and introduction;
- the section headings;
- the N9 paragraph and the Laskar–Petit identification in L4;
- L12's closing remark and the L16 convention remark;
- all of §7–§8 (literature pins, repository baseline, self-refutation table, status, input hashes).

Anchor mapping of the 201 mapped MAIN items (`REASON`):

| Anchors served | Items | Main content |
|---|---|---|
| all seven anchors (LP0 … LP3-2) | 40 | §1 data, elements, chamber, thresholds; L2–L5 |
| the six dynamic anchors (LP1, LP1-H, LP2, LP2-H, LP3-1, LP3-2) | 73 | model, fast part, L1, L6–L8, L14, L16, the conclusion displays |
| LP1, LP1-H, LP2, LP2-H only | 3 | Diophantine (5) and its display, horizon (7) |
| route-L12 only (LP1/LP2) | 43 | L9–L12 |
| route-L13 only (LP1/LP2, the Lean route) | 10 | L13 |
| planar (LP1, LP1-H, LP3-1) | 6 | T15 and its steps, L3's orientation clause |
| LP1, LP1-H only | 1 | `lpM:T15#apply-L14` |
| spatial (LP2, LP2-H, LP3-2) | 21 | L17, L18, T19 |
| LP2, LP2-H only | 1 | `lpM:T19#apply-L14` |
| LP1-H, LP2-H only | 1 | τ = n − ½ (line 93) |
| no anchor, but mapped to a node | 2 | (35) and its step (N4); see SPEC Q5 |

Closure per anchor (proposal):

| Anchor | MAIN items in its closure |
|---|---|
| LP0 | §1 data, elements, chamber, thresholds; L2–L5. L1 joins only through L3's conservation step (Q3). |
| LP1 | L1–L14 (L12 and L13 as alternative routes; L9–L11 only on route-L12), T15, L16 |
| LP2 | L1–L8 (L7, L8 through L17, L18), L9–L14 (routes), L16–L18, T19 |
| LP3 | L1–L8, L14, L16 (+ L17, L18 spatially), the LP3-PLAN steps, imports from N and P; no L9–L13, no (5) |

## The slice plan (details in SPEC §9 and `packets/slices.json`)

The plan has 17 slices:
- 3 anchor slices: `LP-adef-pl`, `LP-adef-sp`, `LP-athm`;
- 9 MAIN slices, aligned to complete lemma units: `LP-m1`, `LP-m2a`, `LP-m2b`, `LP-m3`, `LP-m4a`, `LP-m4b`, `LP-m5`,
  `LP-m6`, `LP-m78` (the last is coverage only);
- `LP-amend`;
- 2 writer-owned slices: `LP-imports`, `LP-ext`;
- 2 conditional LP3 slices: `LP3-a`, `LP3-b`.

The MAIN slices hold about 134 planned nodes. The largest MAIN slice covers 107 source lines.

The order follows the anchor closures:

| Wave | Slices | Closure |
|---|---|---|
| 1 | anchors, §1, L1–L6, amendments, §7–§8 | LP0 |
| 2 | L7–L16, imports, externals | LP1 |
| 3 | spatial definitions, L17–T19 | LP2 |
| 4 | LP3 | LP3 |

Reviews run in batches R1–R4 on Codex Sol (codex-2 per D57; one at a time unless the orchestrator rules otherwise).
Then come the delta rounds, then the global review `sol-global-LP`.

## What waits for the freeze (skill: requires frozen anchors)

1. The frozen manifest entries for the LP anchors. The graph header `header.txt` (with `ROOTS`, `FROZEN_ANCHORS`
   and `FROZEN_MANIFEST`) can be written only after them.
2. The anchor identity binding: the exact node ↔ manifest mapping, the reused-definition decision (Q6), and whether
   the characterizations are roots (Q2).
3. The root check: each frozen theorem's statement against its MAIN locus, with all four source fields
   reconstructed before any proof is read (skill Phase 1).
4. The extraction, review and global briefs (`EXTRACT-BRIEF.md`, `REVIEW-BRIEF.md`, `GLOBAL-BRIEF.md`, from the K/W
   templates), which name the frozen anchor files.
5. All node blocks, `DEPS`, `EDGE` and route records, and `DEPGRAPH.md` / `DEPGRAPH_COVERAGE.md`.
6. LP3: the draft-8 freeze and Q1 (corpus) before `LP3-a` and `LP3-b` start.

## First commands after the freeze

Run from the repository root of the graph worktree, which branches from `inp-lp` after the freeze commit.

```bash
# 1. Pins still valid (re-pin and record in SPEC's change log if not)
sha256sum -c docs/graph/LP/CORPUS.sha256 docs/graph/LP/IMPORTS.sha256

# 2. Anchor map from the frozen manifest (identity fields only; never read Lean bodies)
python3 -I -c "import json; m=json.load(open('manifest/frozen-anchors.json')); [print(a['id'], a['kind'], a['path'], a['export'], a['abi_sha256'], sep='\t') for a in m['anchors'] if a['id'].startswith(('planetary.d59.', 'fourier.d59.'))]" > docs/graph/LP/packets/anchor-map.tsv
wc -l docs/graph/LP/packets/anchor-map.tsv   # draft 7: 127 entries (+2 with draft 8); reconcile with SPEC §1

# 3. Settle Q1-Q8, then fill SPEC §1/§8 and the change log. Write header.txt from the K/W pattern:
#    ROOTS, FROZEN_ANCHORS, and FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:auto

# 4. Packets per slice from draft/coverage-*.md (Markdown pre-extractor, SPEC Q7), then the dry run
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-m2a --root . --structural

# 5. After each merge wave: assemble and lint
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_assemble.py --graph-dir docs/graph/LP \
  --slice-dir docs/graph/LP/packets --header docs/graph/LP/header.txt \
  --slices LP-adef-pl,LP-athm,LP-m1,LP-m2a,LP-m2b,LP-amend,LP-m78 --title "Proof dependency database - track LP"
python3 /root/.claude/skills/build-proof-dependency-graph/scripts/proof_depgraph.py \
  --db docs/graph/LP/DEPGRAPH.md --manifest docs/graph/LP/DEPGRAPH_COVERAGE.md --source-root . \
  --require-complete-coverage --require-initial-lean-status --report
```

The publish gate is the skill's Phase-7 pair of commands with `--require-reviewed --require-complete-coverage
--require-initial-lean-status --require-all-reachable`, first with `--write-dashboard` and then with `--check`.

## Errata and deviations noticed while inventorying (for the orchestrator's ledger)

- **No new source defect found** beyond PROOF-AUDIT-1's N1–N12. MAIN L13 (L433, L616) cites implementation paths
  in `/root/code/KAM` at commit `f5625f19` as its interface evidence. This is not a defect, but the graph must
  consume it through graph-N imports, never through the implementation files (SPEC §3, §6).
- LP3-PLAN L22–L23 (review note C4) says that occurrences of `ν` meaning `B₀μ` "mean `ε`". §2.3–§2.4 still write
  `ν₀`, `ν^{b_n}` for that scalar (e.g. L249, L276). Extractors must read these as `ε`. This is a notation hazard,
  not a mathematical error.
- Deviation of this preparation from the skill: the inventory was written before the anchors are frozen, with
  planned node IDs. The skill orders "anchors → graph" and allows the source inventory as Phase 2 work. No edge, node
  block or header exists. Every planned ID is a proposal that the anchor map can change.

## Orchestrator rulings (root-b8, 2026-11-01)

All proposed defaults for Q1–Q8 are accepted:
- Q1: a short paper-level LP3 source note is written and reviewed after the freeze, before LP3 extraction.
- Q2: the 34 characterization theorems are anchors and roots.
- Q3–Q5: the statement splits are made as proposed.
- Q6: the reused frozen definitions are bound as LP anchor nodes.
- Q7: a small Markdown converter is written for MAIN.md.
- Q8: the writer tag is `kam-lp`. Slice and global reviews run on codex-2 in parallel batches, each reviewer in its
  own session.

## Standing rule after publication (owner, 2026-11-01)

Every LP landing that adds Lean under `KAM/Planetary/StrongAMD` or `KAM/Planetary/Spatial` gets its LEAN_STATUS sync
on main within the same hour. The HQ flags the lag (`scripts/hq-status.py` `graph_sync_lag`).
