# Proposed core improvement: majorize Lie remainders on merged polynomials (FOR OWNER)

Status: proposal only (2026-11-03, kam-b1; recorded at root-b8's request). Nothing has been started.

## Problem (design signal from B3-CERT)

`checkOscChain` (`KAM/EffectiveStability/OscillatorChainCheck.lean`) evaluates the Lie identity
`cartEqCheck (cartLieSum χ Q L) out` and the remainder majorant `cartSupBound (cartAdPow …)` on **unmerged**
monomial lists. For the Hénon–Heiles certificate those lists reach about 1.3·10⁵ monomials.

- One `decide +kernel` call fails with `(kernel) deep recursion`. The cause is `foldr`, `List.sum` and
  `cartWidth`, whose recursion is as deep as the list; failures start at about 5·10³ monomials.
- Kernel memory grows with the total work in one process. Per-chunk calls ran out of memory at the 4 GB scope
  when many chunks shared one module.

B3-CERT worked around this without editing core and without option overrides:
- It split the check into 34 shards, each a separate `decide +kernel` theorem.
- Untrusted intermediate accumulators enter as literals, and proved merge lemmas
  (`HenonHeiles/ChunkMerge.lean`, `BracketChunk.lean`) join the shards.
- Cost: about 27 CPU-min, peak RSS 3.4 GB.
- Details are in the handoff summary of the B3-CERT landing (main 95387f9b0) and in
  `docs/tracks/B/freeze/SEAL-AUDIT-HH-1.md`.

## Proposal

Change the checker so that every polynomial it reasons about is **normalized (merged) before** it is
majorized or compared. Two variants:

1. **Merged Lie remainder.** Compute `ad_χ^L Q` by iterated bracket followed by `cartNormalize` at each power. Bound
   the remainder with `cartSupBound` of the merged polynomial, which has hundreds of monomials, not 10⁵.
   - Soundness: `cartEval (cartNormalize P) = cartEval P` is already proved.
   - The majorant of a merged polynomial is at most that of the unmerged list (triangle inequality per merged
     coefficient). This needs one new lemma.
2. **Bound as certificate data.** The certificate carries the merged `ad^L` polynomial as a literal. The checker
   verifies `cartEqCheck (bracket χ (prev)) next` step by step and bounds only the literal.

Either variant keeps kernel lists at the size of the certificate's own polynomials.

## Expected effect

The HH check would drop from about 27 CPU-min and 34 shards to seconds, in a single module. That makes larger
instances realistic: higher Lie orders, more steps, and the plan's later LG00 / torus-route literals.

## Scope and cost

- About 0.3–0.6k Lean lines in `KAM/EffectiveStability/Poly/Lie.lean`, `OscillatorChain/*` and
  `OscillatorChainCheck.lean`, generic over `CertCoeff K`.
- The existing theorems stay as they are, or become corollaries.
- One audited package; about 2–4 prover-hours.
- The landed HH certificate keeps its current, valid proof. It could be re-checked with the new checker as a
  regression, after which the shard modules could retire.
- The sealed anchors do not change.

## Decision requested

Whether to schedule this, and with what priority: before B6–B8 / a torus-route literal instance, or only if a larger
certificate is chosen.
