# N89-G7 prover handoff (branch inp-n89g7, 448b5d3; contains inp-n89g6 (G1..G6) and inp-n89p1 (audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/ResonanceGeometry/Covering.lean` (no other file touched).

**Nodes proved:** `bpN:p8:covering` -> `KAM.Nekhoroshev.covering`; `bpN:p8:cutoffs` -> `KAM.Nekhoroshev.cutoffs`;
definitions `CoverParams.lam/radius/alpha/delta`, `actionBlock` copied verbatim from N89Signatures.lean.
Statements of `covering`/`cutoffs` are verbatim; no hypotheses added, no signature changed.

**Approach:** Valid gives A>1, A*K>=1, lam d>0, lam(d+1)/lam d = A*K; apply `geometric` and `blocks_cover`.
delta = lam d/V by ring; alpha = (pM/(bm))*K*(lam d/V) by field_simp; radius bounds from `maximal`
(1<=V<=K^d, dim=n -> Lambda=top), V(bot)=V(top)=1, dim top = n. Rank-zero case: alpha(bot) <= lam 1 since
pM/(bm) <= A. `cutoffs`: applies `covering` with P = univ, freqR = id; zBall/eBall inclusions from
`modeSize_euclid_compare`; zero-rank closeness via lattice bot = ⊥ and `projection_zero`.
Helper lemmas (public, in this file): `CoverParams.Valid.{hE,hA1,hq1,hqpos,lam_pos,alpha_eq,radius_nonneg,
radius_bounds,alpha_bot_le}`, `CoverParams.{delta_eq,radius_bot,radius_top}`, `latticeDim_top`.

**Checks:** gate build `KAM.Nekhoroshev.ResonanceGeometry.Covering`: "Built ... Build completed successfully", no
warnings in Covering. `scripts/lint_sources.sh`: only "KAM.lean is out of date" (expected; KAM.lean not edited),
module check PASS, frozen guard OK, ABI hashes OK. 
`#print axioms covering` / `cutoffs`: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat issues; no overrides. File 249 lines.
`latticeDim_top` is a new public name in `KAM.Nekhoroshev` (check no collision on integration).

AUDIT FOCUS (design docs/tracks/N/design/N89-LEAN-DESIGN.md row N89-G7 and proof plan; audits DESIGN-N89-design-audit-{1,2}.md; signatures .drafts/design/N89Signatures.lean): (1) statements = design signatures (CoverParams.lam/radius/alpha/delta, actionBlock, covering, cutoffs); exact zBall and norm comparisons; (2) proofs sound; no added premises; (3) hygiene. Audit ONLY ResonanceGeometry/Covering*.lean (compare with branch inp-n89g6).
