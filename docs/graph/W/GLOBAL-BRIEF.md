# Global root-closure review brief (track W dependency graph)

You are the global reviewer (`sol-global-W`) of the source dependency graph for track W of the KAM formalization
(PDE KAM for the nonlinear wave equation; worktree `/root/code/KAM-inp-wgraph`, branch `inp-wgraph`). You are
fresh and independent: you did not extract, review or repair any slice. Your tag must differ from every tag
already used:
- `claude-suborch-W*`
- `sol-review-W-*` and `sol-review-W-W-*`
- `sol-delta*-W-*`

Your job is to find a global modelling error.

## Read
- `docs/graph/W/SPEC.md`. It is binding. It covers:
  - the root and the 13 anchors;
  - the standing assumption `bpW:w0:mass`;
  - the external policy and imports;
  - "Conventions to watch";
  - the node threshold, reachability and edges;
  - the change log, including the sub-orchestrator ruling on `bpW:wh:dioph#IsDiophantine`.
- `docs/graph/W/REVIEW-BRIEF.md`, rules 1–11. They are binding here too, in particular rules 8 and 11 on step
  hypotheses, symbol edges, the W5–W8 λ/φ policy and cited remarks.
- The assembled graph `docs/graph/W/DEPGRAPH.md` and the coverage manifest `docs/graph/W/DEPGRAPH_COVERAGE.md`.
- The full corpus, pinned in `docs/graph/W/CORPUS.sha256` (check it with `sha256sum -c`):
  - `blueprint-W/parts/w0-conventions.tex`, `w0-normalization.tex`, `w1-sequences.tex`, `w2-reconstruction.tex`,
    `w3-birkhoff.tex`, `w4-homological.tex`, `w5-kamstep.tex`, `w6-iteration.tex`, `w7-measure.tex`,
    `w8-assembly.tex`, `w-headline.tex`.
- The imported track-K nodes (`K:bp:p1:*`), at their locators in `blueprint/parts/p1-analysis.tex`, pinned in
  `docs/graph/W/IMPORTS.sha256`. The reviewed `docs/graph/K/DEPGRAPH.md` is background for them.
- The manifest `manifest/frozen-anchors.json`, identity fields only. Do not use its state fields.
- The frozen declaration files:
  - `KAM/Frozen/Wave/Defs/*.lean`
  - `KAM/Frozen/Wave/Theorems/Nlw2.lean`
  - `KAM/Frozen/Defs/IsDiophantine.lean`
- **Read nothing else in Lean.** That means no implementation modules, providers, proof bodies or status.
- The slice reviews in `docs/graph/W/reviews/` are background only. Do not take their verdicts on trust.

## Do
1. **The root `bpW:wh:nlw2`** (`KAM.Wave.nlw2`, `wave.nlw2.v1`).
   - Reconstruct `SOURCE_HYPOTHESES`, `SOURCE_QUANTIFIERS`, `SOURCE_CONCLUSION` and `CONSTANT_SCOPE` directly
     from the headline (`w-headline.tex`) and from `Nlw2.lean`. Compare all four with the node.
   - Check that the anchor identity fields match the manifest.
   - PROOF_SOURCE is the proof of `bpW:w8:nlw2-proof` (w8 L552–L599). Check that the one edge to that theorem, and
     its 17 conjunct steps plus the assembly step, cover every conjunct of the frozen statement, in the frozen order.
   - Then trace the root backward through its whole closure.
   - **W-NLW2 checks:**
     - The witnesses r₀, C, τ, η, Γ, ν, K are chosen after m and before I, θ, θ₀.
     - γ_I is chosen per I.
     - C is common to clauses (3) and (5).
     - There is no uniformity in m.
     - η ≥ 0 on (0, r₀) and η → 0 along `nhdsWithin 0 (Ioi 0)`.
     - Clause (1) is the density statement in [0, ∞].
     - Clause (3) closeness is to `linearTorus I hI` at the *same* θ, with the o(r) rate η(r(I)) r(I).
     - Clause (4) is the coordinatewise `HasDerivAt` form with `cubicGrad`.
     - Clause (5): `IsClassicalSolution`, u_x as `derivWithin` on [0, π], the time derivative via `reconV`.
     - Clause (6) is injectivity of the family.
2. **Global consistency across slice boundaries.** Check:
   - statement strength and quantifier order;
   - carriers: `Fin 2 → ℝ` actions, period-one angles, `WaveSpace = ℓ² × ℓ²` with weighted coordinates (coefficients
     q = coeff y);
   - the conventions SPEC lists to watch:
     - max norm versus Hilbert norm, and the √2 factors;
     - N₊ (PNat) mode indexing; the tangential `i : Fin 2` is mode i+1; normal modes j ≥ 3, with P96-K's index
       j′ = j − 2;
     - φ = 2πθ and ν = ω/(2π);
     - P96-K's z is the conjugate of W0's z;
     - the corrected normal-form coefficients E-PDE-W-1/2;
     - the weights ⟨l⟩ and Dirichlet weights; β = 1/4 and loss 1/2;
     - K_s and C_m;
   - the constant order of W6 (s, σ_P, γ, γ₁, M, θ before α), W7 ((C1)–(C6)) and W8 (E₁…E₇, t₀, shells);
   - that every constant depends on m only where SPEC says so;
   - the external boundary:
     - the labelled ext-items of W1–W5, W7 and W8, including the new gap-repair items `bpW:w4:ext-riesz`,
       `bpW:w5:ext-symm`, `bpW:w5:ext-sqrt` and `bpW:w5:ext-triangle`;
     - the imported K nodes;
     - nothing else. Each external must be a leaf, and no alias may duplicate another external.
   - The graph has no SOURCE_GAP nodes. Look for any gap that a step hides, in particular in W4–W6, where the blueprint
     repair of 2026-10-30 closed ten exposed gaps.
   - every route node.
3. **Conditional premises at every application.**
   - Each premise must be supplied by an edge or a step at the consumer. Check the following applications:
     - W3's normal form and Birkhoff map in W5 (`bpW:w5:action-angle`) and W8 (`bpW:w8:Kshell`, `shell-close`,
       `shell-inv`, `injective`);
     - `bpW:w3:transport-tori-weak` in W8;
     - W4's homological lemmas in W5 (weight guard (G), the modified divisors, `bpW:w5:w4-general`/`w4-modified`);
     - W5's KAM step in W6 (`prep-step` in the modified case, `wave-iteration`);
     - W6's results in W8 through `bpW:w8:w6-general`. They are stated for every ε₀ in the admissible interval;
       Remark `bpW:w6:to-w8` is the interface.
     - W7's measure, density, Diophantine and limit results in W8 (shells with q = 1/2, α_n, Π_n);
     - W2's `bpW:w2:clause5` and `bpW:w2:orbit` in W8;
     - W1's analytic toolkit wherever it is applied.
   - **Section data.** Every node that uses section data (`<section>#data`) must depend on that data node.
   - **Circularity.** W7 constdef (C3)/(C4) is split through `bpW:w7:Xzones#consts`. Check that this introduces no
     circularity and no strengthening.
4. **Cross-part edges.**
   - Check, in particular:
     - W2–W3 on W1;
     - W4 on W1/W3;
     - W5 on W3/W4;
     - W6 on W5/W7;
     - W8 on W2/W3/W5/W6/W7;
     - every edge into a frozen definition (symbol edges at first use; λ only for λ_{1,2,j,J,i,n} and `\Lean{lam}`
       in W5–W8);
     - every edge into an imported node.
   - Look for missing, reversed, merely transitive or pointer-only edges, and for EDGE locators that do not point at
     the consumer's use.
5. **Imports.**
   - Run `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_imports.py docs/graph/W/packets --slice
     W-imports --root . --owner K=blueprint --owner-graph K=docs/graph/K --self-track W`.
   - Every imported node must be referenced, and must be a node of `docs/graph/K/DEPGRAPH.md`.
   - Compare each import's source fields with its statement in `blueprint/parts/p1-analysis.tex`.
6. **Coverage.**
   - Every proof paragraph that contributes a substantive obligation must appear in the graph or be excluded with a
     valid reason. This includes the unlabelled prose and the section-data paragraphs.
   - The results excluded as "outside every root closure of track W" must really be unused by the root's proof:
     - `bpW:w0:reconstruction#rescaling`;
     - `bpW:w0n:pde-equiv` with steps `time`, `ident`, `converse`;
     - `bpW:w0n:formal-birkhoff`;
     - `bpW:w0n:duffing` and the Lindstedt ledger fact;
     - `bpW:w4:k0` with its steps;
     - `bpW:w7:melnikov`.
   - Remarks cited inside a statement or proof step must be nodes (rule 11). Check the excluded remarks' reasons.
7. **Anchors.** Check that the root and the 12 definition anchors are author-frozen. Every non-anchor, including
   every imported node, must have `FROZEN_*: -`.

Linter, from the worktree root:
```
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md \
  --source-root . --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable
```
Every node and coverage item is REVIEWED. The only expected failures of this command are the two header lines
`GLOBAL_REVIEWER` and `GLOBAL_REVIEW_REF`, which the orchestrator fills in after your review; any other failure is a
finding.

## Output
Write `docs/graph/W/reviews/GLOBAL-review.md` with:
- the root verdict (PASS or FAIL), with the four reconstructed source fields;
- the global findings. Give each a severity (blocking, major or minor) and evidence (file and line). Where a record
  must change, include a complete replacement node block or EDGE line in a fenced block, saying which slice owns it;
- an unreachable-node or coverage finding list (or "none");
- suspected blueprint defects (location, quoted text, why);
- the final list of unresolved questions (or "none").

Edit nothing else. Run no state-changing git, no lake and no Lean, and read no implementation Lean or provider files.
Keep working in the same turn until done, then print `READY graph-global-W` on a line of its own.

Hard rules for any Lean work (verbatim):
1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
