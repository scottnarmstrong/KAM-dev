# P23-07 prover handoff (branch inp-p2307, 42ff000; off inp; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/TwoScale/Lipschitz.lean` (~105 lines). No other file touched.

**Node:** `bpP:p3:lip-sup` -> `KAM.Planetary.lip_sup` (signature as in P23Signatures.lean; only line-wrapped
for the 100-column lint). Local steps `ls-close`/`ls-far` are inlined; private helper `isOpen_actionNbhd_aux`.

**Approach:** N = 0: domain subsingleton, difference 0. N >= 1, near pair (`‖x-y‖ < r/2`): on the complex ball
`B(ι x, r/2)` every closed `r/2`-ball lies in `B(ι x, r) ⊆ actionNbhd S r`, so `KAM.norm_fderiv_le_of_closedBall`
gives `‖Dδ‖ ≤ 2A/r`; convex mean-value (`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`) gives
`2A/r‖x-y‖ ≤ 4NA/r‖x-y‖`. Far pair: triangle inequality, `2A ≤ 4NA‖x-y‖/r`. (Constant 2NA/r in fact; N only enters as N >= 1.)
No premises added; no source gap hit.

**Checks:**
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-p2307 KAM.Planetary.TwoScale.Lipschitz`: Built, no warnings.
- `scripts/lint_sources.sh`: line-length OK, check_lean_modules PASS, frozen guard OK, ABI hashes OK. Only message:
  "KAM.lean is out of date" (expected; KAM.lean is generated, not edited by me).
- `#print axioms KAM.Planetary.lip_sup`: propext, Classical.choice, Quot.sound.

**Uncertainties:** none. **Errata/deviations:** none. No heartbeat issues; no overrides.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-07 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (lip_sup (near/far pairs, zero-dimensional case); Weighted.general_cauchy consumed); (2) proofs sound; no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the P23-07 module(s) (KAM/Planetary/TwoScale/Lipschitz*).
