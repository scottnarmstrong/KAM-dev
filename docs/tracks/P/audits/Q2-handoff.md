# Q2 prover handoff (branch inp-p11c-q2, 9d0803d0; offloaded package run by the main orchestrator)


## Files (new)
- KAM/Planetary/Quantitative/BudgetPositivity.lean (208 lines): helper positivity lemmas (all `qbc_*`).
- KAM/Planetary/Quantitative/BudgetCompare.lean (~360 lines): `BudgetOrder` (verbatim from signatures; no earlier
  module defines it), `qb_comp`, `qb_mono` (verbatim signatures), helpers `qbcLam`, `qbcOld*`, `qbc_*`.

## Approach
Positivity of everything for NumericalValid data: cutoff constant (mollifier mass 0 = 1, cutoffDerivative 0 = 1,
sSup over finite image), diameter > 0 (volume K > 0 forces non-subsingleton), cDio, gamma, tbar >= 1, tflat, xibar,
thetaMax, lambdaFlat, thresholds. lambdaFlat and the old threshold share one shape `qbcLam`; one monotonicity lemma
`qbcLam_mono` serves both theorems. Monotone pieces: cDio antitone, gamma, tbar antitone, tflat, xibar antitone
(uses s*tbar antitone on (0,1] via log x >= 1 - 1/x, since 16N/pi > 1), thetaMax. qb_comp: old T <= tbar, tflat <= t,
t <= 1, X <= xibar, C1 >= 1.

## Checks
- Gate: `inp_lake_build.sh ... KAM.Planetary.Quantitative.BudgetCompare` -> Build completed successfully (9088 jobs).
- `#print axioms qb_comp`, `qb_mono`: [propext, Classical.choice, Quot.sound].
- No sorry/maxHeartbeats; lines <= 100.
- scripts/lint_sources.sh: check_lean_modules PASS, frozen guard OK, ABI hashes OK; exit 1 only with
  "KAM.lean is out of date" (new modules not in generated root; I must not edit KAM.lean — orchestrator regenerates).

## Uncertainties / errata / deviations
None. No signature changed. Statements true as given (N>=1 etc. come from NumericalValid).
Note: the old threshold uses A0 without abs and T = max 1 (...), both <= new tbar, as the design expects.
No heartbeat problems.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q2 (qb_comp, qb_mono; Q1, adm_params numerical equality) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/Quantitative/BudgetCompare.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
