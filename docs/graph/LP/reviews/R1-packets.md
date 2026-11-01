# Review batch R1 (wave 1, the LP0 closure): one packet per reviewer session

Launched by the orchestrator: codex-2 (D57), GPT-6.1-Sol at medium effort, one fresh session per slice, the eight
sessions in a parallel batch (Q8). Each reviewer gets exactly its packet below as the prompt. The extractor and the
writer (`kam-lp`) do not review. Records are all PROPOSED; nothing is marked REVIEWED before the writer applies the
reviews.

After the batch, the writer runs, per slice `<s>` with reviewer tag `<t>`:
```
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_apply_review.py docs/graph/LP/packets <s> docs/graph/LP/reviews/<s>-review-1.md <t>
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_mark_reviewed.py docs/graph/LP/packets <s> docs/graph/LP/reviews/<s>-review-1.md <t>
```
then re-assembles and lints (SPEC §9 command; `reports/W1-lint.txt`), and opens delta reviews (`sol-delta1-LP-<s>`,
a different session) for every record a reviewer rewrote.

Common prompt prefix for every packet:

> Work in `/root/code/KAM-inp-lp-graph` (branch `inp-lp-graph`). Read `docs/graph/LP/REVIEW-BRIEF.md` in full and
> follow it exactly. You are an independent refute-first topology reviewer; edit nothing but your review file; run no
> Lean, Lake, build or state-changing git. Lean hard rules (verbatim): 1. Never use `set_option maxHeartbeats` (or any
> heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the
> proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it
> as a design signal. 2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into
> focused modules, preserving public import paths as cheap facades.

| # | Slice | Reviewer tag | Output | Records | Raw source to re-read | Focus |
|---|---|---|---|---|---|---|
| 1 | `LP-adef-pl` | `sol-review-LP-LP-adef-pl` | `reviews/LP-adef-pl-review-1.md` | 48 nodes, 103 edges, 48 items | MAIN §1 L11–L93, L16 L508–L525; the 48 frozen definition files (FROZEN_FILE) | identity fields vs manifest; DEPS vs the declarations' actual uses; source fields vs MAIN loci; the reused-definition binding (Q6) and the `keplerEnergy` = ν_iE_i convention |
| 2 | `LP-athm` | `sol-review-LP-LP-athm` | `reviews/LP-athm-review-1.md` | 11 nodes, 65 edges, 11 items | MAIN §1 L41–L55, L2–L5 (L110–L175); the 11 frozen theorem statements (up to `:=`) | LP0's separate anchor over the d-generic `lpM:L5` (SPEC §1.1); its quantifier and constant order; the characterizations' carriers (no positive-mass premise in the L4 ones); the SOURCE_GAP modelling of the deficit characterization |
| 3 | `LP-ext` | `sol-review-LP-LP-ext` | `reviews/LP-ext-review-1.md` | 5 nodes | MAIN L139, L149, L154, L170, L189 | each external is Mathlib-level, stated at the strength its consumers use, and on the closed list (SPEC §3) |
| 4 | `LP-m1` | `sol-review-LP-LP-m1` | `reviews/LP-m1-review-1.md` | 6 nodes, 8 edges, 19 items + 6 deferred | MAIN L1–L93 | data package (not a standing assumption); d-generic `lpM:s1:elements`; the chamber/threshold items mapped to anchors; the six deferred conclusion items |
| 5 | `LP-m2a` | `sol-review-LP-LP-m2a` | `reviews/LP-m2a-review-1.md` | 24 nodes, 77 edges, 36 items | MAIN L94–L160 | Q3 split of Lemma 3 (static/dynamic/orientation) and the gap step `deficit-zero-L`; Q4 split of Lemma 4; (10) as `lpM:L1#velocity`; L4 proof steps and the externals |
| 6 | `LP-m2b` | `sol-review-LP-LP-m2b` | `reviews/LP-m2b-review-1.md` | 15 nodes, 64 edges, 20 items | MAIN L161–L189, AMENDMENTS N2, N11 | Lemma 5's steps and N11 order; conditional-premise discharge (L3 static in L5, L5 in L6 via (17)); Lemma 6 and N2's shared U |
| 7 | `LP-amend` | `sol-review-LP-LP-amend` | `reviews/LP-amend-review-1.md` | 7 items + 7 deferred | AMENDMENTS L1–L26 and the MAIN lines each note cites | dispositions of N2, N8, N9, N11, N12, precedence, order; justification of the seven deferrals |
| 8 | `LP-m78` | `sol-review-LP-LP-m78` | `reviews/LP-m78-review-1.md` | 12 items | MAIN L604–L679 | every exclusion; no row of the self-refutation table adds an obligation that a Lemma 1–6 node lacks |

Per-packet prompt: the common prefix, then
"Your slice is `<Slice>`; your reviewer tag is `<Reviewer tag>`; write `docs/graph/LP/<Output>`. Focus (in addition to
the full checklist): <Focus>. When done print `READY sol-review-LP-<Slice>`."

If the orchestrator prefers fewer sessions, the coverage-only packets 7 and 8 and the 5-node packet 3 may share one
session (tag `sol-review-LP-R1-small`, three output files); every node and item still gets a reviewer different from
`kam-lp`.
