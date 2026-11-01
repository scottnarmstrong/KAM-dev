# Slice topology review brief (track LP dependency graph)

You are an independent, refute-first reviewer of one slice of the source dependency graph of track LP (strong AMD
and exponential safety of planetary systems) of the KAM formalization. Work in the worktree
`/root/code/KAM-inp-lp-graph` (branch `inp-lp-graph`). The extractor `kam-lp` wrote these records under the writer
`kam-lp`. You did not. Your slice and your reviewer tag (`sol-review-LP-<slice>`) are named in your prompt
(`docs/graph/LP/reviews/R1-packets.md`).

## Read
- `docs/graph/LP/SPEC.md`. It is binding and fixes:
  - §1: the anchors and their node IDs (`<owner>#<LeanName>`; LP0 = `lpM:L5#planar_strongAMD_barrier`, the planar
    instance of the d-generic `lpM:L5`), the reused frozen definitions (Q6);
  - §2: the corpus and the **amendment precedence rule** (N2–N12 override the MAIN lines they cite);
  - §3: no standing assumption; the closed external list; the import policy;
  - §4: the conventions to watch;
  - §5: the node threshold, the **dimension rule**, the **fixed symbol list**, the **statement splits Q3–Q5**;
  - §6: the edge policy; §7: wave reachability; §9: the slices and the deferred-coverage rule.
- The raw source of your slice: `docs/tracks/LP/source/MAIN.md` at the slice's line range (SPEC §9), and
  `docs/tracks/LP/source/AMENDMENTS.md` in full (26 lines). Whenever an edge points into another slice, read the
  cited text there.
- Your slice's records: `docs/graph/LP/packets/<slice>.nodes.md` and `<slice>.coverage.md`, and, if present,
  `<slice>.deferred-coverage.md` (items held back until their later-wave nodes exist; check that each deferral is
  justified, i.e. that no wave-1 node is the right target).
  - `docs/graph/LP/specs/<slice>.py` is only the writer's input format. Review the rendered packets, not the spec.
  - Do not read the `*.draft-*.md` files (mechanical pre-extraction skeletons).
- The other slices' node files, read-only, when you check a cross-slice edge.
- The frozen-anchor manifest `manifest/frozen-anchors.json`, **identity fields only** (id, path, export, contract,
  abi_sha256, source.range), and `docs/graph/LP/packets/anchor-binding.tsv`.
- For anchors (slices `LP-adef-pl` and `LP-athm` only), the frozen declaration files named in FROZEN_FILE: the
  docstring and the declaration's statement (for a theorem, up to `:=`; for a definition, its body).
- **Read nothing else in Lean:**
  - no implementation modules (`KAM/Planetary/**` outside `KAM/Frozen/`);
  - no `KAM/Provider/` files;
  - no proof bodies, `sorry` or proof status;
  - no manifest `state` fields, no `LEAN_STATUS-W1.md`.

## Try to refute
1. **Completeness.**
   - Look for statements, displays, definitions and substantive proof steps of the slice that have no node and are
     not excluded with a valid reason: an estimate, a construction, a case split, a parameter or witness choice, a
     quantifier closure, a carrier change, a reused intermediate claim hidden in an unlabelled proof paragraph.
   - Look for facts used without proof that are neither a node, nor an external of the closed list (SPEC §3), nor a
     `SOURCE_GAP` step. The wave-1 externals are `lpM:ext-ftc`, `ext-compact-min`, `ext-heine-cantor`,
     `ext-picard`, `ext-gronwall`; proposing another external needs a SPEC revision (say so in the review).
2. **Edges.**
   - For every node, re-read its statement and proof. Every DEPS entry must be a direct use, located at the
     consumer by its EDGE line (not at the prerequisite's own proof).
   - Look for missing direct uses (including uses without a lemma number: "by (11)", "by Lemma 4", "uniform
     continuity", "the deficit bound"); forward pointers kept as edges (e.g. §1 L55 "Lemma 4 proves this"); "is not
     used" mentions kept as edges (N4, N9); reversed, merely transitive or unnecessary edges.
   - **Symbol rule (SPEC §5).** Dimension-free frozen symbols used directly need the anchor edge: 𝒬 (`chamber`),
     a_i(I) (`actionAxis`), D (`eccDeficit`), the feasible set and objective, B_ij, B_cross, B. Dimension-specific
     symbols (C, E_i, a_i, e_i, L, the phase carriers) are **not** edged from d-generic MAIN nodes: they go through
     `lpM:s1:elements`/`lpM:s1:model`, and the frozen carriers attach at the anchors (dimension rule). Fail a missing
     dimension-free edge; do not demand planar-carrier edges on d-generic nodes.
   - **Conditional premises.** Wherever a node applies a conditional result, check that an edge or the applying
     node shows where each premise is supplied. Wave-1 examples: Lemma 3's (13) inequality needs C < B_⋆ (supplied in
     Lemma 5 by C ≤ B − m < B ≤ B_⋆); Lemma 5 inside Lemma 6 needs C ≤ B(I) − δ/2 (supplied by (17)); Lemma 4's
     continuity inside Lemma 5's K_m and Lemma 6's modulus.
   - Look for alternatives modelled as a conjunction (no routes exist in wave 1; L12/L13 are wave 2), and for cycles
     between a definition and its consequences.
3. **Source-statement fields.** Reconstruct `SOURCE_HYPOTHESES`, `SOURCE_QUANTIFIERS`, `SOURCE_CONCLUSION` and
   `CONSTANT_SCOPE` independently from the raw statement (as amended). For steps, use the proof context: a step's
   hypotheses are the enclosing statement's premises plus local data, results derived earlier are DEPS, and its
   quantifiers inherit the enclosing scope. Fail any record that adds a proof ingredient as a hypothesis, drops a
   premise (e.g. n ≥ 2, ν > 0, U ⊂ 𝒬 compact, m > 0, E_i < 0), reorders quantifiers, weakens or strengthens the
   conclusion, or lets a constant depend on more or less than stated (L5: d_⋆, d_pair only on (n, ν, U, m), N11).
   Watch SPEC §4: Euclidean ¦·¦ vs the max norm; the orientation-free C (N8/OD-1); the chamber carrier; the frozen
   `keplerEnergy` = ν_i E_i; canonical (p_i/ν_i) vs actual velocity V_i (10).
4. **Statement splits.** Check that Q3 (Lemma 3 static/dynamic) and Q4 (Lemma 4 without the L143 contact/LP and L147
   sharpness clauses) are faithful: the split records together say exactly what MAIN says, consumers use the right
   part (Lemma 5 only the static part), and the excluded clauses really have no consumer.
5. **Locators.** STATEMENT_SOURCE and PROOF_SOURCE ranges must match the text. EDGE locators must point at the use
   in the consumer. Amended nodes carry `AMENDED: N<k>` in NOTE.
6. **Coverage.** Every inventory item needs a correct disposition; every exclusion a valid reason (administrative,
   provenance, comparison, heading, unconsumed by ruling Q4/N9). Wave 1 never excludes a result as "outside every
   root closure" (SPEC §7): 37 wave-1 nodes serve the wave-2/3 roots and are kept.
7. **Anchors (`LP-adef-pl`, `LP-athm`).**
   - Compare the four source fields with the MAIN transcription **and** with the frozen declaration: binders,
     carriers, quantifier order, constant scope (LP0: d_⋆, d_pair, then K, before I, e, z).
   - Check that FROZEN_*, CONTRACT_ID and CONTRACT_VERSION equal the manifest entry exactly.
   - Check each definition anchor's DEPS against the frozen definitions its declaration actually uses.
   - Check the binding (SPEC §1, `anchor-binding.tsv`): owner node, slice, wave; LP0's separate anchor node over the
     d-generic `lpM:L5` (SPEC §1.1).
   - `lpM:L3#sum_action_mul_eccDeficit_le_sourceStrongAMD` relies on the SOURCE_GAP step `lpM:L3#deficit-zero-L`
     (the frozen statement covers L = 0, which MAIN does not argue). Confirm or refute that modelling.

Topology status is not proof status. A faithfully exposed `SOURCE_GAP` node passes. Do not supply missing mathematics
yourself.

You may run, from `/root/code/KAM-inp-lp-graph`:
```
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets <slice> --root .
```

## Output
Write `docs/graph/LP/reviews/<slice>-review-1.md`, containing:
- **A verdict for the slice:** PASS or FAIL.
- **A node table,** one row per node, in exactly this form, which `inp_depgraph_apply_review.py` parses:
  `| <node id> | PASS | <source spans re-read> |` or `| <node id> | FAIL | <reason> |`.
- **A coverage table, one row per coverage item** (PASS or FAIL, same form), so that every passed item can be marked
  by `inp_depgraph_mark_reviewed.py`. Also one row per deferred item (`DEFER-OK` or `FAIL`).
- **Replacement fragments.** For every FAIL, give the corrected *complete* node block (all fields, EDGE lines
  included) or coverage item, in the database format, inside a fenced block. `inp_depgraph_apply_review.py` replaces
  whole blocks by ID. To delete a node, say so in its row and give the replacement coverage item. For a new node,
  give a complete block with `TOPOLOGY_STATUS: PROPOSED`, `REVIEWER: -` and `LEAN_STATUS: NOT_STARTED` (`EXTERNAL`
  for an external); never edit FROZEN_* or anchor CONTRACT_* fields.
- **Suspected defects of the source,** in a separate section: location, quoted text, and why it is wrong.

Edit nothing except your review file. Run no state-changing git. Run no Lean, lake or builds.

The repository's Lean hard rules, for awareness (verbatim):
1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof
   will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.

Keep working in the same turn until your slice is reviewed. Then print `READY <your marker>` on a line of its own.
