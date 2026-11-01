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

Slice: `LP-amend`
Verdict: FAIL

Node table: no rows (the slice has zero nodes). The N2 finding concerns the source fields of its named
cross-slice targets, not the correctness of the two target IDs. Full corrective blocks are supplied below.

| Coverage ID | Verdict | Source spans re-read / reason |
|---|---|---|
| lpA:precedence | PASS | AMENDMENTS L1–L6; SPEC §2: N1 in place, N2–N12 override the cited MAIN text. Administrative exclusion. |
| lpA:N2 | FAIL | Correct target IDs, but lpM:L6 and shared-U source fields retain the unamended neighborhood/radius statement; the shared closed 4r_g tube and r ≤ r_g occur only in NOTE. |
| lpA:N8 | PASS | AMENDMENTS L17; MAIN L26–L39 and L506; orientation-free elements and strongAMD targets, with the reflection bridge in wave 2. |
| lpA:N9 | PASS | AMENDMENTS L18; MAIN L143–L160; unconsumed realization/sharpness is excluded under Q4/N9. |
| lpA:N11 | PASS | AMENDMENTS L20; MAIN L164–L175; perihelion defines d_⋆ first and bounds consumes it. |
| lpA:N12 | PASS | AMENDMENTS L21; roadmap typing note has no MAIN obligation or wave-1 target. |
| lpA:order | PASS | AMENDMENTS L23–L26; recommended work order is administrative, not a proof edge. |

| Deferred coverage ID | Verdict | Source spans re-read / justification |
|---|---|---|
| lpA:N1 | DEFER-OK | AMENDMENTS L10; MAIN L232–L238. Corrected planar one-form identity is in Lemma 7, wave 2; no L1–L6 node proves chart symplecticity. |
| lpA:N3 | DEFER-OK | AMENDMENTS L12; MAIN L246–L271. Complex widths and K′ projection belong to Lemma 8, wave 2; shared-U does not supply the complex chart widths. |
| lpA:N4 | DEFER-OK | AMENDMENTS L13; MAIN L400–L427. The (35) remark belongs to Lemma 12, wave 2; Q5 requires its eventual exclusion, not a wave-1 supplier or arithmetic dependency. |
| lpA:N5 | DEFER-OK | AMENDMENTS L14; MAIN L323–L349. The specified Lie-flow, existence and remainder steps belong to Lemma 10, wave 2; Lemma 6 local ODE existence does not supply these analytic identities. |
| lpA:N6 | DEFER-OK | AMENDMENTS L15; MAIN L431–L464 and L487–L500. Adapter widths and r/2 drift are Lemma 13 and its Lemma 14 alternative route, wave 2. |
| lpA:N7 | DEFER-OK | AMENDMENTS L16; MAIN L487, L500, L506. Alternative drift suppliers belong at Lemma 14's route nodes, wave 2; neither is replaced by Lemma 6 continuation. |
| lpA:N10 | DEFER-OK | AMENDMENTS L19; MAIN L91, L520–L528. Final osculating μ₀ constraints belong to Lemma 16, wave 2; L5's static constants require no μ₀. |

N2 is not deferrable: wave 1 already constructs U and the modulus and exports (17). Its two current targets
say AMENDED in NOTE, but their four source fields fail to require the shared tube. In particular the shared-U
step quantifies over a solution and r using an already supplied U before concluding that U exists. The replacement
puts the construction before its applications and records the source's N2 specialization explicitly. This is
source transcription of AMENDMENTS L11 and MAIN L257, not a new proof or an extra external. Existing direct
uses of L4 continuity, Heine–Cantor, chamber and B remain unchanged. No new edge to a later-wave node is needed.
The later Lemma 8 and Lemma 14 uses remain wave-2 work.

N8's source definition uses the absolute value of angular momentum, including zero; it does not assume
prograde motion. OD-1 fixes the convention in SPEC §4. The consumer at MAIN L506 handles reversal by a
simultaneous orthogonal change; that bridge belongs to T15, not an extra premise in the definition.
N11's named steps have AMENDED notes and a direct bounds → perihelion edge, and d_⋆ depends only on
(n, ν, U, m). N9 is not an edge or a hidden source theorem: Q4 also excludes the related statement clauses.
No amendment is interpreted conjunctively as two analytic proof routes. No exclusion uses wave-1 nonreachability.

Replacement fragments: complete coverage item, followed by the complete two target node blocks in LP-m2b.
These are proposed corrections only; no packet is edited and no anchor identity/contract field is changed.

```text
ITEM: lpA:N2
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N2@L11-L11
DISPOSITION: NODE lpM:L6#shared-U, lpM:L6
REASON: N2 is implemented in the source fields of lpM:L6#shared-U and lpM:L6: one shared compact U contains the closed 4r_g sup-norm tube about 𝓛_δ; its modulus serves (17), Lemma 8 and (39), with Ω_B(4r_g) ≤ δ/16 for Lemma 8 and r ≤ r_g; Lemma 8 and Lemma 14 targets join in wave 2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

NODE: lpM:L6
KIND: lemma
TITLE: Lemma 6: the moving threshold (17) and continuation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n, ν, d, μ > 0); 𝓛 ⊂ Q compact; δ > 0
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q and δ > 0: choose one shared compact neighborhood U ⊂ Q and r_g > 0, with the modulus Ω_B; then for every 0 < r ≤ r_g and every solution with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ, whose actions stay within r of I^0 with that tube in U, and every t
SOURCE_CONCLUSION: U is a compact neighborhood of 𝓛 containing the closed 4r_g sup-norm tube about 𝓛_δ = {I ∈ 𝓛 : B(I) ≥ δ}; this same U and its modulus are used in Lemmas 6, 8 and 14, with Ω_B(4r_g) ≤ δ/16 for the Lemma 8 choice; Ω_B(r) = sup{¦B(I) - B(J)¦ : I, J ∈ U, ‖I - J‖_∞ ≤ r} → 0 as r ↓ 0; C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17); if nr + Ω_B(r) ≤ δ/2, the solution cannot terminate at a finite time while those action and ellipticity conditions hold; the same holds backwards in time
CONSTANT_SCOPE: U, r_g and Ω_B depend only on 𝓛, δ and the fixed data, chosen before r and the solution and shared with Lemmas 8 and 14
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L6#moving-threshold, lpM:L6#continuation, lpM:L6#backward, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/AMENDMENTS.md#N2@L11-L11 | N2 requires the same U and modulus in (17), Lemma 8 and (39), the closed 4r_g tube, and r ≤ r_g
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17)
EDGE: lpM:L6#continuation | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | no finite-time termination
EDGE: lpM:L6#backward | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the backward assertion
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L179-L179 | 𝓛, U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L181-L181 | B and Ω_B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): U is the one compact set shared with Lemmas 8 and 14; it contains the closed 4r_g sup-norm tube about 𝓛_δ, its modulus Ω_B serves (17), Lemma 8 and (39), and r ≤ r_g (the consumers in wave 2 record where these requirements are used)

NODE: lpM:L6#shared-U
KIND: step
TITLE: compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L182
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#shared-U
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n, ν, d, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local definition 𝓛_δ = {I ∈ 𝓛 : B(I) ≥ δ}
SOURCE_QUANTIFIERS: for every compact 𝓛 ⊂ Q and δ > 0, choose U and r_g > 0 before the solution and before 0 < r ≤ r_g
SOURCE_CONCLUSION: choose one compact neighborhood U ⊂ Q of 𝓛 and r_g > 0 such that U contains the closed 4r_g sup-norm tube about 𝓛_δ; Ω_B(r) = sup{¦B(I) - B(J)¦ : I,J ∈ U, ‖I - J‖_∞ ≤ r} tends to zero as r ↓ 0; choose r_g small enough that Ω_B(4r_g) ≤ δ/16; the same U and Ω_B serve (17), Lemma 8 and (39), with applications restricted to r ≤ r_g
CONSTANT_SCOPE: U, r_g and Ω_B depend only on 𝓛, δ and the fixed data, before the solution and application radius r
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4, lpM:ext-heine-cantor, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | B is continuous on Q
EDGE: lpM:ext-heine-cantor | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | uniform continuity on the compact U
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | U lies in the open chamber Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the modulus of B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): the closed neighborhood is the one shared compact U containing the closed 4r_g-tube about 𝓛_δ
```

Suspected defects of the source: none identified. N2's requirements are explicit in the normative amendment;
the defect is their incomplete transcription into the target fields. No deviation from MAIN as amended is proposed.

Checks: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-amend --root .`
returned exit 0: `LP-amend: 0 nodes, 0 edges, 7 coverage items, 0 problems`. The seven deferred items were read
separately; they are not assembled and this structural result does not validate their later-wave targets.
No theorem proof or axiom certification claimed.

Final artifact verification: every required ID occurs exactly once in a verdict row (LP-ext: 5; LP-amend:
7 current + 7 deferred; LP-m78: 12). Replacement node blocks retain PROPOSED/REVIEWER - and have one EDGE
per dependency. HEAD advanced from 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2 to the audited HEAD printed above
during concurrent work. A read-only commit comparison listed only docs/tracks/LP/packages/LP-GRAPH-W2.md;
none of this review's inputs changed. `git diff --name-only` was empty. Other reviewers' untracked files
were present and were left untouched. The checks above were run against the original packets, not applied
replacement fragments.
