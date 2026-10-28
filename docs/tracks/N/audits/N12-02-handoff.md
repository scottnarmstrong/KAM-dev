# N12-02 prover handoff (branch inp-n1202, f20c8eb; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/CompactMaximum.lean` (~45 lines). Committed on inp-n1202.
**Node:** `bpN:p12:ext-markov#compact-max` -> `KAM.Nekhoroshev.compact_max`, signature verbatim from N12Signatures.lean.
**Approach:** restrict to the subtype `Icc 0 T` (compact), build the jointly continuous `G x t = g t x` via
`ContinuousOn.comp_continuous`, apply Mathlib `IsCompact.continuous_sSup`, identify the images.
Imports: `Mathlib.Topology.Order.Compact`, `Mathlib.Topology.Instances.Real.Lemmas`.
**Corollaries:** the design table mentions "local and variable-time corollaries", but the signature file declares only
`compact_max`; none added (consumers can reparametrise u = v*t themselves). Say if they are wanted as extra lemmas.
**Checks:**
- gate build `KAM.Nekhoroshev.Averaging.CompactMaximum`: success, no sorry. One linter warning: `hT` unused (kept: signature
  must not change; for T<0 the image is empty and the sSup is the constant 0, so the hypothesis is not needed).
- `#print axioms KAM.Nekhoroshev.compact_max`: propext, Classical.choice, Quot.sound.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI hashes OK; prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: KAM.lean not edited by me; orchestrator regenerates).
**Uncertainties / errata / deviations:** none. No design signals (compiles in ~5 s at default heartbeats).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-02 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design signatures (compact_max and its local and variable-time corollaries via time reparameterization); (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the N12-02 module (CompactMaximum).

## Round 2 (after audit 1 FAIL F1)
Prover fix on branch inp-n1202 at 9fbf91b: the local (domain/subtype), image/supremum and variable-time corollaries. Prover notes: /root/code/KAM-inp-n1202/.drafts/handoff-N12-02b.md.

AUDIT FOCUS round 2: verify finding F1 of docs/tracks/N/audits/N12-02-audit-1.md is fully resolved (each corollary requested by the design row present, correctly stated for its downstream consumers, no extra premise, sound proof); compact_max unchanged; hygiene (lint incl. 100-char lines). Audit ONLY KAM/Nekhoroshev/Averaging/CompactMaximum.lean.
