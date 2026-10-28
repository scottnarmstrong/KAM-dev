# P4-CO prover handoff (branch inp-p4co, 85e9096; contains inp-p4s (P4-S, P45-S; audited); offloaded package run by the main orchestrator; prover on claude-12)


Files: new `KAM/Planetary/PGMeasure/Collar.lean` (~270 lines; imports Mathlib, KAM.Planetary.PG.Setting). KAM.lean untouched (lint reports it out of date, as expected).

Declarations (signatures verbatim from P45Signatures.lean): `ext_conn`, `realNbhd_joinedActions`, `domain_collar_helper`, `collar`
(order in file: ext_conn first). Helpers: `blockSplitEquiv`, `blockSplitEquiv_apply`, `measurePreserving_blockSplitEquiv`, `volume_joinedActions`.
The hboundary hypothesis enters `collar` exactly as the signature's `hc` (A, d explicit); no PGData use.

Approach: ext_conn proved directly (this Mathlib has no `inter_frontier_nonempty`) via the preconnected cover by interior V and (closure V)ᶜ.
collar: innerCore = closure V ∩ ⋂ closed distance sets (compact, bounded by V); (c) by segment + ext_conn; (b),(d) by monotonicity against hc and V ⊆ core ∪ (V \ core).
Product neighbourhood via dist_pi_lt_iff and Fin.append; volume of joinedActions via a measure-preserving block split (piCongrLeft ∘ sumPiEquivProdPi) and Measure.prod_prod.
domain_collar_helper: N \ J ⊆ (X'\X)×B ∪ X×(B\Y), B the (l-s,u+s)^b box.

Checks: gate build `KAM.Planetary.PGMeasure.Collar`: "Build completed successfully (9062 jobs)", no sorry. lint_sources.sh: PASS except KAM.lean out-of-date note (generated; not edited) and one >100-char line (113) that is the verbatim signature line of domain_collar_helper.
Axioms of all four main results: [propext, Classical.choice, Quot.sound].
Warnings: unused hypotheses hX, hl, hsl, hXfinite in domain_collar_helper (mandated by the frozen-style signature; they are not needed for the proof).

Uncertainties/errata/deviations: none. No heartbeat problems.

AUDIT FOCUS (design docs/tracks/P/design/P45-LEAN-DESIGN.md row P4-CO and its proof plan; audits DESIGN-P45-design-audit-{1,2,3}.md; signatures .drafts/design/P45Signatures.lean): (1) statements = design signatures (ext_conn first, collar, realNbhd_joinedActions, domain_collar_helper), the hboundary hypothesis exactly as designed (no extra premise); (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY KAM/Planetary/PGMeasure/Collar*.lean (compare with branch inp-p4s).
