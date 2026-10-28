# N89-G5 prover handoff (branch inp-n89g5, 6a01089; contains inp-n89g4 (N89-G1..G4, audited); offloaded package run by the main orchestrator; prover on claude-12)

Files: KAM/Nekhoroshev/ResonanceGeometry/Blocks.lean (new, ~60 lines; imports only ResonanceGeometry.Maximal).
Nodes: bpN:p8:blocks -> zone, zoneStratum, blocks (verbatim from signatures); bpN:p8:blocks-cover (+ stepN:p8:bc-finite, bc-top) -> blocks_cover (verbatim statement).
Approach: finiteness = subset of klattice_finite. Cover: D = {d | w ∈ zoneStratum d}; if empty, Λ=⊥ (maximalK_bot, zone ⊥ = univ by simp, not in stratum (latticeDim ⊥+1) since D empty); else d = sSup D (bounded by n), take its witness Λ; w ∉ stratum (d+1) by maximality.
Checks: inp_lake_build.sh KAM.Nekhoroshev.ResonanceGeometry.Blocks: success; only unused-variable warnings for hK, hlam (signature-mandated; the statement is true without them). lint_sources.sh: PASS except "KAM.lean is out of date" (generated; not edited per brief). Frozen guard OK, ABI OK.
#print axioms blocks_cover: propext, Classical.choice, Quot.sound.
Uncertainties: none. Errata/deviations: none. Design signals: none (default heartbeats, no overrides).

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-G5 and proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean): (1) statements/definitions = design signatures (zones, strata, blocks, finite blocks_cover); (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY ResonanceGeometry/Blocks*.lean (compare with branch inp-n89g4).
