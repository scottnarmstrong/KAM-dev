# S8-4 prover handoff (branch inp-s84, f581afcd; offloaded package run by the main orchestrator; Scaling* files written by a delegated agent of the prover)


## Files (all new, KAM/Planetary/SecularForm/)
Quartic.lean (facade; contains `quartic`), Quartic/{Defs, PairScaling, PairAverage, PairDecomp, PairAnalytic,
Orthogonal, Invariant, PairSymmetry, PairJet, Coefficients, Jet, Taylor, Swap, Diagonal,
ScalingReal, ScalingComplex, ScalingTube, ScalingEmb, Scaling}.lean. Last five written by a delegated agent.

## Signed declarations (verbatim)
Defs: quarticMonomials, radialR1, unitPosition, separatedDomain, dimensionlessPair (radialPhi/radialH reused from
LaplaceIdentities). Theorems: `quartic_pair_scaling` (PairScaling), `quartic` (Quartic.lean), `quartic_scaling` (Scaling).
The "six coefficients" are the explicit analytic `quarticCoeff D i j` (Coefficients.lean).

## Approach
- pair decomposition of secular D false on the perturbation_analytic polydisc (PairDecomp; `avg_pair` Fubini lemma
  for two coordinates of the cell average);
- joint analyticity of pairSlowSecular via the two-planet system `pairData` + `perturbation_analytic` (PairAnalytic);
- O(2)-invariance of the 4-jet via `evenness` (rotation, reflection, `orth_cases`) + polynomial representation of the
  4th derivative + S8-W `quartic_invariant` (Invariant, PairSymmetry, PairJet);
- six coefficients = explicit linear functionals of the 4-jet at six test vectors, hence analytic (Coefficients);
- assembly over pairs (Jet); diagonal values c0,c1 from `pairSlowSecular_diag_jet` + Taylor uniqueness
  (Taylor) + exchange of the two planets (Swap, Diagonal);
- quartic_scaling: change of variables to eccentric longitude, explicit complexified integrand, e_param, descent to
  real analyticity (Scaling*).

## Checks
Gate build `KAM.Planetary.SecularForm.Quartic`: success (9175 jobs). lint_sources.sh: all PASS except
"KAM.lean is out of date" (generated; not edited). `#print axioms` of quartic, quartic_scaling,
quartic_pair_scaling: only propext, Classical.choice, Quot.sound. No sorry, no heartbeat overrides.

## Uncertainties / notes
- Signature-forced unused hypotheses (hn, hij, hI, hSep) give unused-variable warnings only.
- Mixed coefficients c3..c6 are defined but not computed (Part 11b), as designed.
- `radialR1` is only a definition here (no theorem in the signature file about it).
- Design signals: none (one whnf timeout in the delegated work fixed by restating a composition).
## Errata / deviations: none found.

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-4 and its proof plan; P810 design audits; signatures /root/code/KAM-inp/.drafts/design/P810Signatures.lean): (1) quarticMonomials, radialR1, unitPosition, separatedDomain, dimensionlessPair, quartic_pair_scaling, quartic, quartic_scaling = signature file EXACTLY, and the S8-4 slice COMPLETE: read the design row and proof plan line by line, and check every graph proof cut the row assigns (sibling S8-Q failed because an assigned proof cut, qf-diag2, was not exported); also check that the internal helpers S8-D/S8-X are consumed as the 13:08 OVERNIGHT ruling says; (2) the handoff's approach line 'pair decomposition of secular D false on the perturbation_analytic polydisc' is garbled: determine what PairDecomp actually proves and whether anything is false; (3) proof soundness (avg_pair Fubini, joint analyticity via pairData, O(2) invariance of the 4-jet, the six coefficients as linear functionals, Taylor uniqueness and planet exchange, the quartic_scaling change of variables and descent to real analyticity); signature-forced unused hypotheses hn, hij, hI, hSep are signature premises (confirm), no added premises; (4) hygiene (no EuclideanSpace; no public short name already used elsewhere in KAM; no root shadow). Audit ONLY the KAM/Planetary/SecularForm/Quartic*.lean files.
