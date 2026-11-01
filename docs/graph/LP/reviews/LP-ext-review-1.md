Audited HEAD: `3ee7b4480fb27797643d618460bbc206225c40b5`
Branch: `inp-lp-graph`
Reviewer: `sol-review-LP-R1-small`

Independent refute-first source-topology review under REVIEW-BRIEF.md and SPEC.md. Read AGENTS.md,
docs/PLAN.md, docs/DECISIONS.md, the full brief, SPEC, and AMENDMENTS L1–L26. Corpus hash checks both returned
`OK`. No Lean, Lake, builds, lint, implementation files, provider files, proof bodies, or state-changing git.
Manifest inspection was restricted to identity data; anchor-binding.tsv was read. No anchor declaration audit is
claimed for these slices. Only this session's three requested review files are written.

Lean hard rules (verbatim):
1. Never use set_option maxHeartbeats (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.

Slice: `LP-ext`
Verdict: FAIL

| Node ID | Verdict | Source spans re-read / reason |
|---|---|---|
| lpM:ext-ftc | FAIL | The alternative “or with integrable derivative” does not imply constancy; restrict the contract to zero derivative, as MAIN L139 uses. |
| lpM:ext-compact-min | PASS | MAIN L149–L156, L168–L175; LP-m2a feasible-compact/continuity and LP-m2b Km-compact/perihelion consumer blocks. |
| lpM:ext-heine-cantor | PASS | MAIN L154–L156, L179–L189; continuity and shared-U consumer blocks. |
| lpM:ext-picard | PASS | MAIN L189; local-existence and continuation consumer blocks; L340 read for the later-wave appeal. |
| lpM:ext-gronwall | PASS | MAIN L189; local-existence consumer block and the stated integral-inequality uniqueness argument. |

Coverage table: no rows (the packet's coverage file is empty). No deferred items.

The five nodes are exactly the wave-1 closed list in SPEC §3. They are ordinary calculus, compactness,
contraction, and ODE uniqueness inputs, not planetary or normal-form theorems. Their empty DEPS/ROUTES,
PROOF_SOURCE `-`, external classification and locators are appropriate. No standing assumption or new external
is introduced. Dimension-specific symbols and anchor edges are inapplicable to these abstract inputs.

For compact-min, MAIN supplies continuity and nonemptiness at L149. L170 explicitly splits the empty K_m case
before taking extrema, and n ≥ 2 supplies a nonempty finite family of adjacent gaps. Positivity is deduced by
the consumer from attainment and pointwise positivity; the external does not silently assume it. For
Heine–Cantor the consumers use continuous real objectives on compact metric sets. For Picard, the consumer
has a finite-dimensional physical phase space, a closed ball in a neighborhood of the compact nonsingular set,
and bounded field and derivative. Its two strict time bounds give a self-map and contraction on the complete
continuous-path space. Gronwall supplies uniqueness for the two solutions with the same initial data on their
common time interval. These uses need no stronger external. The backward-time step negates the vector field.

FTC finding: f(t)=t on [0,1] has an integrable derivative and is not constant. The parentheses therefore admit
a false instance of the printed conclusion. MAIN L139 already proves derivative zero; the narrow replacement
below exactly supplies scalar planar or vector spatial constancy, with no generalized integral identity needed.
This is a packet defect, not a defect in MAIN's argument.

Replacement fragment (complete node; no EDGE lines because DEPS is empty):

```text
NODE: lpM:ext-ftc
KIND: external
TITLE: fundamental theorem of calculus (zero derivative on an interval)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-ftc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J a real interval; f : J → V continuous on J and differentiable on its interior, with derivative zero there; V is a finite-dimensional real normed vector space (including ℝ)
SOURCE_QUANTIFIERS: for every such J, V and f, and every s, t ∈ J
SOURCE_CONCLUSION: f(t) = f(s); thus f is constant on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level
```

Suspected defects of the source: none identified in the assigned appeals. No source mathematics supplied or
frozen contract changed; the replacement corrects only the external's transcription.

Checks: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-ext --root .`
returned exit 0: `LP-ext: 5 nodes, 0 edges, 0 coverage items, 0 problems`. This checks the original packet's
structure, not the mathematical validity of its FTC alternative. No proof-status or axiom certification claimed.

Final artifact verification: every required ID occurs exactly once in a verdict row (LP-ext: 5; LP-amend:
7 current + 7 deferred; LP-m78: 12). Replacement node blocks retain PROPOSED/REVIEWER - and have one EDGE
per dependency. HEAD advanced from 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2 to the audited HEAD printed above
during concurrent work. A read-only commit comparison listed only docs/tracks/LP/packages/LP-GRAPH-W2.md;
none of this review's inputs changed. `git diff --name-only` was empty. Other reviewers' untracked files
were present and were left untouched. The checks above were run against the original packets, not applied
replacement fragments.
