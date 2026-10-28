# T4 prover handoff (branch inp-p11c-t4, 98de073f; contains inp-p11c-t3 (on inp) and, merged by the orchestrator (98de073f), inp-p11c-t2 (T2 OrbitJet, in audit), which provides p11c_JetEq; offloaded P11C package run by the main orchestrator)


## Files (all committed)
- KAM/Planetary/PlanarTorsion/PairCoefficients.lean (≈230 lines): `p11c_pairCoeffs`, `p11c_pairSeriesJet` (verbatim, only line-wrapped), `pair_series`, `pair_quadratic_consistency`, helper tables p11cN0/N1/Dn/Ord/Quot.
- .../PairCoefficients/Vanish.lean: `p11cVanishes`, iterated-derivative vanishing, Pi-valued jet lemma.
- .../PairCoefficients/Series.lean: `p11cSeries`, `P11cGood` (analytic on (-1,1), head/tail split).
- .../PairCoefficients/Laplace.lean: `p11c_laplace_neg` (parity), `p11cHalf` identification of `p11c_laplace (1/2) k` with the Part-8 series on all of (-1,1), head/tail with a^8 remainder.

## Approach
b_k = head_k + a^8 tail_k with tail_k analytic (coefficients halfCoef from U8a, bound ≤1). Each component of pairCoeffs − jet equals a^m·(analytic), with the exact polynomial identity N0·head0+N1·head1−Dn·jet = a^m·q (q explicit, closed by `ring`; sympy used only to produce q). m=8 for components 0–5, 7 for 6,7 (the true a^7 coefficient of comps 6,7 is nonzero, so the stated jets to order 6 are sharp); component 1 has m=8 giving JetEq 7. Consistency: from T3 `laplace_up` at s=1/2 plus field_simp.

## Checks
- Gate builds (inp_lake_build.sh) of Vanish, Series, Laplace, PairCoefficients: success, no sorry/errors.
- `#print axioms` pair_series, pair_quadratic_consistency: propext, Classical.choice, Quot.sound.
- scripts/lint_sources.sh: all checks pass except "KAM.lean is out of date" (generated file; orchestrator regenerates). No line >100 chars.
- sympy cross-check: all stated jets verified (diff vanishes through a^7; comp 1 through a^8).

## IMPORTANT dependency / deviation
`p11c_JetEq` is defined by T2 in KAM/Planetary/PlanarTorsion/OrbitJet/Analytic.lean, not on this branch. PairCoefficients.lean imports `KAM.Planetary.PlanarTorsion.OrbitJet.Analytic`. To build, I copied that file from branch inp-p11c-t2 (commit 44a87596) into the worktree UNTRACKED and did not commit it. **Merge T2 before T4** (or the branch will not build). Vanish/Series/Laplace are independent of T2.

## Uncertainties / errata
No source defects found; signatures unchanged. No heartbeat issues, no set_option. Names p11cN0 etc. grepped unused.

ORCHESTRATOR NOTE: the prover had built against an untracked copy of T2's OrbitJet/Analytic.lean; the orchestrator removed it and merged branch inp-p11c-t2 instead (identical file), then rebuilt PairCoefficients successfully.

AUDIT FOCUS (design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T4 and its proof plan; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean): (1) p11c_pairCoeffs, p11c_pairSeriesJet, pair_series, pair_quadratic_consistency = signature file EXACTLY, and the T4 slice COMPLETE (read the design row and proof plan line by line); (2) proof soundness: the head/tail split b_k = head_k + a^8 tail_k, the analyticity of the tails on (-1,1), the identification p11cHalf of p11c_laplace (1/2) k with the Part-8 series on all of (-1,1), the explicit polynomial identity closed by ring (sympy only produced q), the vanishing orders; no added premises; (3) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM: note helpers p11cN0/N1/Dn/Ord/Quot; no root shadow). Audit ONLY the KAM/Planetary/PlanarTorsion/PairCoefficients*.lean files (OrbitJet is T2's, audited separately).
