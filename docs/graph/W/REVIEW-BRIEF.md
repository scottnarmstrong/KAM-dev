# Slice topology review brief (track W dependency graph)

You are an independent, refute-first reviewer of one slice of the source dependency graph of track W (PDE KAM,
nonlinear wave) of the KAM formalization. Work in the worktree `/root/code/KAM-inp-wgraph`, branch `inp-wgraph`.
The writer `claude-suborch-W` extracted these records. You did not. Your slice and your reviewer tag
(`sol-review-W-<slice>`) are named in your prompt.

## Read
- `docs/graph/W/SPEC.md`. It is binding and fixes:
  - the root and the 13 anchors, with the mapping of the Part 0 labels;
  - the standing assumption `bpW:w0:mass` and the carrier rule;
  - the external and import policy;
  - the conventions to watch;
  - the node threshold, the reachability rule of wave 1, the edge policy and the slices.
- The raw source of your slice: `blueprint-W/parts/<part>.tex`, at the line range in SPEC.md's slice table.
  - Whenever an edge points into another part, read the cited result there.
  - For an imported node `K:…`, read its statement at its STATEMENT_SOURCE in `blueprint/parts/`.
- Your slice's records: `docs/graph/W/packets/<slice>.nodes.md` and `<slice>.coverage.md`.
  - `docs/graph/W/specs/<slice>.py` is only the writer's input format. Review the rendered packets, not the spec.
  - Do not read the `*.draft-*.md` files: they are the mechanical pre-extraction.
- The other slices' node files, read-only, when you check a cross-slice edge.
- The frozen-anchor manifest `manifest/frozen-anchors.json`, identity fields only.
- For anchors (slices `W-w0c` and `W-wh` only), the frozen declaration files:
  - `KAM/Frozen/Wave/Defs/*.lean`;
  - `KAM/Frozen/Wave/Theorems/Nlw2.lean`, its statement only;
  - `KAM/Frozen/Defs/IsDiophantine.lean`.
- **Read nothing else in Lean:**
  - no implementation modules;
  - no `KAM/Provider/` files;
  - no proof bodies, `sorry` or proof status;
  - no manifest state fields.

## Try to refute
1. **Completeness.**
   - Look for statements, displays, definitions and substantive proof steps of the slice that have no node and are
     not excluded with a valid reason. That includes parts of a long unlabelled proof that hide a plausible Lean
     lemma: an estimate, a construction, a case split, a parameter choice, a carrier change.
   - Look for facts the text uses without proof that are neither a W external, nor a proved node, nor an imported K
     node, nor a `SOURCE_GAP` node.
   - Check every `prose-L…` disposition. A paragraph that fixes data or states a fact later consumed needs a node
     (`#data`, `#lambda-facts`, …) or a mapping to its consumers.
   - Check every `sourcegap-L…` disposition (SPEC §External inputs, "Other gaps").
2. **Edges.**
   - For every node, re-read its statement and proof. Every DEPS entry must be a direct use, located at the consumer
     by its EDGE line.
   - Look for:
     - missing direct uses, including uses without `\ref`: "by Cauchy–Schwarz", "termwise", "by symmetry of g",
       "λ_j > j", a definition used through its symbol (U_m, G_q, κ, T, 𝒯, X^w, …);
     - forward pointers kept as edges;
     - provenance edges from `\source`;
     - "is not used" mentions kept as edges;
     - reversed, merely transitive or unnecessary edges.
   - **Externals.** A proof that cites `\ref{bpW:w1:ext-…}`, `bpW:w2:ext-…` or `bpW:w3:ext-…` needs that edge. So
     does a proof that uses such a fact without citing it (e.g. Mathlib-level analyticity of a multilinear map).
   - **Carrier rule.** Uses of λ go to `bpW:w0:basis#lam`. A use of m > 0 itself goes to `bpW:w0:mass` or to
     `bpW:w0:basis#lambda-facts` (SPEC). Do not demand edges to `bpW:w0:mass` from nodes that use only λ.
   - **Frozen definitions used by symbol.** `coeff`, `reconU`, `reconV`, `cubicGrad`, `lam`, `sineMode`, `ellWeight`,
     `WaveSpace`, `linearTorus`, `IsClassicalSolution` and `IsAnalyticTorusEmbedding` are anchors. A node whose
     statement or proof speaks of the frozen object needs the edge to the anchor node.
   - Look for alternatives modelled as a conjunction.
   - Look for circularity between a definition and its consequences, and between a remark and the result it
     comments on.
3. **Source-statement fields.** Reconstruct `SOURCE_HYPOTHESES`, `SOURCE_QUANTIFIERS`, `SOURCE_CONCLUSION` and
   `CONSTANT_SCOPE` independently from the raw statement. For steps, use the proof context. Fail any record that:
   - adds a proof ingredient as a hypothesis;
   - drops a stated premise, such as a range of a, p, s or 𝕂;
   - reorders quantifiers;
   - weakens or strengthens the conclusion;
   - lets a constant depend on more or less than stated.

   Watch SPEC's conventions:
   - weighted coordinates (y) versus coefficients (q = κ y);
   - ℕ₊ indexing and the Fin 2 ↦ j = i + 1 shift;
   - period-one angles and the factors 2π;
   - the max norm on WaveSpace and the √2 factors it causes;
   - the corrected normal-form coefficients (E-PDE-W-1/2: A_ii = 9/(8πλ_i²), A_12 = B_ji = 3/(2πλλ), the 1/16
     prefactor, I_j = |z_j|², ż = −iλz);
   - the positive carriers hm and hI;
   - the constants K_s, C_*, C_m (independent of m) and the W3 constants (m, a, p).
4. **Conditional premises.** Wherever a node applies a conditional result, check that the applying node or an edge
   shows where each premise is supplied. For example:
   - Lemma `bpW:w1:selection` with its bound on c_ijkl;
   - Theorem `bpW:w0n:cubic-bound` with p ≥ 1/2;
   - `bpW:w0n:algebra` with s ≥ 1;
   - the W2 theorem applied to the frozen conclusions (3)–(4);
   - W3's divisor bound inside the generating Hamiltonian.

   A missing premise discharge is a FAIL.
5. **Locators.** STATEMENT_SOURCE and PROOF_SOURCE ranges must match the text. EDGE locators must point at the use
   in the consumer, not at the prerequisite.
6. **Coverage.** Every inventory item needs a correct disposition. Every exclusion needs a valid reason:
   - alias;
   - administrative;
   - pointer or provenance;
   - notation only;
   - layout.

   Wave 1 never excludes a result as "outside every root closure" (SPEC §Reachability).
7. **Anchors (`W-w0c`, `W-wh`).**
   - Compare the four source fields with the blueprint transcription and with the frozen declaration's statement:
     binders, carriers, quantifier order, constant scope.
   - Check that the FROZEN_* fields and the anchor CONTRACT_* fields equal the manifest entry exactly.
   - Check the anchor mapping table in SPEC.md against the frozen files' docstrings.

Topology status is not proof status. A faithfully exposed `SOURCE_GAP` node passes. Do not supply missing mathematics
yourself.

**Wave-1 reachability is expected to fail.** Nearly every node of W0n–W3 is unreachable from the root until W8
exists. Do not fail a node for that.

You may run, from `/root/code/KAM-inp-wgraph`:
```
python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/W/packets <slice>
```

## Output
Write `docs/graph/W/reviews/<slice>-review-1.md`, containing:
- **A verdict for the slice:** PASS or FAIL.
- **A node table,** one row per node, in exactly this form, which `inp_depgraph_apply_review.py` parses:
  `| <node id> | PASS | <source spans re-read> |` or `| <node id> | FAIL | <reason> |`.
- **A coverage table.** Give one row per coverage item that FAILS, in the same form. Then say "all other coverage
  items PASS" explicitly. If you prefer, list a PASS row for every item instead.
- **Replacement fragments.** For every FAIL, give the corrected *complete* node block (all fields, EDGE lines
  included), EDGE line or coverage item, in the database format, inside a fenced block. `inp_depgraph_apply_review.py`
  reads the fenced blocks and replaces whole blocks by ID.
  - To delete a node, say so in its table row and give the replacement coverage item.
  - For a new node, give a complete block, with `TOPOLOGY_STATUS: PROPOSED` and `LEAN_STATUS: NOT_STARTED`
    (`EXTERNAL` for an external).
- **Suspected defects of the blueprint,** in a separate section: location, quoted text, and why it is wrong.

Edit nothing except your review file. Run no state-changing git. Run no Lean, lake or builds.

The repository's Lean hard rules, for awareness (verbatim):
1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof
   will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.

Keep working in the same turn until your slice is reviewed. Then print `READY <your marker>` on a line of its own.
