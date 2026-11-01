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

Slice: `LP-m78`
Verdict: PASS

Node table: no rows (zero nodes). No deferred items.

| Coverage ID | Verdict | Source spans re-read / exclusion reason |
|---|---|---|
| lpM:h:s7 | PASS | MAIN L604–L606; section heading. |
| lpM:s7#intro | PASS | MAIN L607–L610; literature-check/process introduction, not an analytic supplier. |
| lpM:s7#cite-lp-aa | PASS | MAIN L611; interpretation/provenance; geometry has its own L2–L5 proof. |
| lpM:s7#cite-lp-arxiv | PASS | MAIN L612; version/page provenance and published-fetch limitation. |
| lpM:s7#cite-bmm | PASS | MAIN L613; explicit non-supplier, no slow-pair specialization imported. |
| lpM:s7#cite-pinzari-liu | PASS | MAIN L614; comparison only, no zero-frequency specialization asserted. |
| lpM:s7#repository-baseline | PASS | MAIN L616; reuse/comparison boundary, not a supplier in the LP0 closure. |
| lpM:s7#research-notes | PASS | MAIN L618; research provenance; analytic obligations are assigned to numbered lemmas. |
| lpM:s7#self-refutation | PASS | MAIN L620–L644; all nineteen rows traced below; no new wave-1 obligation. |
| lpM:h:s8 | PASS | MAIN L646; section heading. |
| lpM:s8#status | PASS | MAIN L648–L661; paper status assertions, not proof-status evidence for this graph. |
| lpM:s8#input-hashes | PASS | MAIN L663–L679; historical input/process record, not graph source pinning or a theorem. |

All twelve dispositions are valid exclusions under SPEC §§5–7. There are no source-statement fields, edges,
route nodes, constants, or frozen identities in this slice to change. No result is excluded because its root is
not yet assembled. The empty node packet is correct: neither literature comparisons, historical repository
inspection, self-review, nor status claims are direct proof inputs. Repository Lean names at L616/L618 were
treated as opaque tokens; no implementation was followed. Literature URLs are provenance in this slice;
this review does not independently certify their bibliographic or mathematical contents.

Self-refutation table: the following accounts for every row. MAIN L94–L189 and the relevant LP-m2a/LP-m2b
records were read for the wave-1 claims. Later-wave references explain the scope of the remarks; they do not
certify unassembled later-wave topology.

| MAIN row | Obligation already represented / boundary |
|---|---|
| L624 | Star protection is (16): lpM:L5#perihelion and pair-distances; B includes B_⋆. No pair-only strengthening is inferred. |
| L625 | Closed feasible square and continuity are lpM:L4#feasible-compact, contact-param and continuity. Interior realization is the deliberately unconsumed Q4/N9 clause at L158, not a new consumed obligation. Radial endpoints are included in L2. |
| L626 | C ≥ 0 is lpM:L3#amd-nonneg. Restricting centers and building the δ/4 collar is Lemma 8 L246–L261 and Lemma 14 L472; it is not an extra assumption min_U B > δ for L5/L6. |
| L627 | lpM:L3#L-nonzero, projections and static already give nonzero L and positive projections, with m=δ initially. No retrograde/alignment hypothesis is added. |
| L628 | Regular chart construction and symplectic extension belong to Lemmas 7/17; no L1–L6 chart obligation is implied. |
| L629 | Complex bilinear denominator control is Lemma 8 L267–L271; it is distinct from the real distance estimates of L5, not silently attributed to them. |
| L630 | Entire slow ball/global chart is the later Lemma 8/Lemma 14 domain assertion, not an assumed secular trajectory or a strengthened L5. |
| L631 | Fixed-plane deficit on the full spatial ball is Lemma 18 L588–L597. The wave-1 L3 projection bound and L5 list formulation already supply its real static geometry. |
| L632 | Fixed-frequency inversion and optional (35) are Lemma 12 L400–L427, subject to N4/Q5. This row creates no wave-1 all-orders arithmetic premise or edge to (35). |
| L633 | One-derivative commutators and the iteration condition belong to Lemmas 9–11; no obligation is assigned to L1–L6. |
| L634 | The fixed strip and weighted Fourier bounds are the later Lemma 9 and Lemma 12 L405 mechanism; no extra wave-1 estimate. |
| L635 | Exact cancellation in the Lie remainder is Lemma 10 L342–L349; no additional smallness assumption on X_h0. |
| L636 | Slow-coordinate commutator/flow scaling belongs to Lemmas 9–10. The original physical-time normalization is already lpM:L1#reduction/reconstruction. |
| L637 | Negative-time flow inverses are Lemma 11 and their two errors are used at Lemma 12 L414–L418; no inverse-chart statement is added to L1–L6. |
| L638 | Moving threshold (17) is lpM:L6#moving-threshold using dynamic (13); (39) is the later Lemma 14 choice. The N2 source-field defect is reported in LP-amend, not repaired by this remark. |
| L639 | First exit/strict improvement is Lemma 14 L478–L489. Compact endpoint continuation already has lpM:L6#local-existence, continuation and backward with the δ/2 premise supplied by (17). |
| L640 | Conservation of the total vector is lpM:L3#conservation/dynamic; choosing its fixed spatial direction belongs to Lemma 18 L597. No secular-divergence premise is added. |
| L641 | Actual versus canonical velocity is lpM:L1#velocity (10). Osculating-element comparisons and the two endpoint errors are Lemma 16 (42)–(43), N10, L527–L528; no missing static L5 obligation. |
| L642 | L5 constants are already restricted to (n,ν,U,m), including the empty case; L6 chooses U uniformly. Real/complex collar and iteration choices belong to Lemmas 8/12/14. No μ-dependent geometric cutoff is introduced by this row. |

In particular, L625's interior-minimizer sentence does not reinstate the excluded L4 sharpness/realization
nodes: SPEC §6 explicitly forbids edges from the self-review table, and N9 confirms no downstream proof uses
that paragraph. Its appearance in a non-supplier self-review does not violate that exclusion. Conversely the
consumed contact reduction/parameterization for continuity remains present in LP-m2a. L638 and L639 do not
remove the actual premises needed for (17) or the L5 application with margin δ/2. The dimension rule and
static/dynamic split are preserved throughout this reading.

Replacement fragments: none (no failed items).

Suspected defects of the source: none requiring a new consumed mathematical obligation in this slice.
MAIN L661's “None” is a historical paper-status claim, not an endorsement of proof closure or a cancellation of
SOURCE_GAP nodes. No claim is made that all later-wave self-review resolutions have passed independent review.
No source repair, frozen change, or other deviation is proposed.

Checks: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-m78 --root .`
returned exit 0: `LP-m78: 0 nodes, 0 edges, 12 coverage items, 0 problems`. Source topology and exclusions only;
no Lean theorem proof or axiom certification claimed.

Final artifact verification: every required ID occurs exactly once in a verdict row (LP-ext: 5; LP-amend:
7 current + 7 deferred; LP-m78: 12). Replacement node blocks retain PROPOSED/REVIEWER - and have one EDGE
per dependency. HEAD advanced from 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2 to the audited HEAD printed above
during concurrent work. A read-only commit comparison listed only docs/tracks/LP/packages/LP-GRAPH-W2.md;
none of this review's inputs changed. `git diff --name-only` was empty. Other reviewers' untracked files
were present and were left untouched. The checks above were run against the original packets, not applied
replacement fragments.
