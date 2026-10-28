# N12-08 prover handoff (branch inp-n1208, 4225b26; contains inp-n1207 (N12-07, N12-01; audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- NEW `KAM/Nekhoroshev/Averaging/SlabBox.lean` (145 lines): generic one-box estimate `AvgSlab.section_dist_le`, `AvgSlab.volume_box_le` (`sl-box`: MVT on line sections + Fubini via `volume_preserving_piFinSuccAbove`).
- NEW `KAM/Nekhoroshev/Averaging/Slab.lean` (320 lines): `slab`, `AvgSlabBound` (signatures verbatim, in signature-file order), plus helpers `AvgSlab.{lineFun,gradFun,unif_M,hasDerivAt_line,exists_coord,slab_freq}` and extra `exists_avgSlabBound` (∃ C₁, AvgSlabBound h R C₁; distinct name, convenience for N12-09 `shells`).
- `KAM/Nekhoroshev/Averaging/Coefficients.lean`: checked out UNCHANGED from branch inp-n1204 (N12-04, audited PASS WITH NOTES) because the `slab` and `AvgSlabBound` signatures mention `avgQ`, which lives there. Identical content, so landing is conflict-free.

## Design deviation / note
The design's import edge is `Slab → Rank`, but `avgQ` is defined in N12-04 `Coefficients`; Slab therefore also imports `Coefficients` (so `Slab → Rank, Coefficients`; still acyclic). Please add this edge to the design DAG / land inp-n1204 before inp-n1208.

## Approach
Compactness-free in `e`: ∂ⱼ(e·ω) = (Mᵀe)ⱼ is linear in e, so uniform continuity of M on closedBall 0 (7R/8) gives a radius r independent of e; finitely many sup-norm cubes closedBall x r (x in G) cover G (finite_cover_balls_of_compact). For v ≤ λ/2, a cube meeting G∩{|e·ω|≤v} has, from `lambda`, a coordinate j with |(Mᵀe)ⱼ| ≥ 2cc (cc=λ/(4√n)), hence ≥ cc on the whole cube; sections along j have diameter ≤ 2v/cc, Fubini gives vol ≤ (2r)^{n-1}·2v/cc. Sum over cubes; v>λ/2 uses vol G. C₁ = max 1 (max (p(2r)^{n-1}2/cc) (2 vol G/λ)). Integer modes: e = k/|k|₂.
This does not follow the blueprint's open cubes Q_m × open sets U_m cover of K₀ literally; it is the same argument with uniform continuity replacing the (I,e) cover (equivalent, simpler).

## Checks
- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh <wt> KAM.Nekhoroshev.Averaging.Slab`: Build completed successfully (3188 jobs), no warnings in my files.
- `sh scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated, not edited); check_lean_modules PASS; frozen guard OK; ABI hashes OK.
- `#print axioms KAM.Nekhoroshev.slab` and `exists_avgSlabBound`: [propext, Classical.choice, Quot.sound].
- No sorry/maxHeartbeats; all lines ≤ 100 chars; files ≤ 320 lines.

## Uncertainties / errata / design signals
None. No heartbeat issues. No statement changes. No source errata found (blueprint step sl-box's "constant sign" is not needed: the MVT only needs the modulus bound).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-08 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (slab, numerical AvgSlabBound; finite coordinate boxes uniform in e); (2) proofs sound (Fubini/MVT used correctly); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the Slab module(s) (compare with branch inp-n1207).
