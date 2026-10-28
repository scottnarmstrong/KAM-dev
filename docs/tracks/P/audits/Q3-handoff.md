# Q3 prover handoff (branch inp-p11c-q3, ec1afcb8; offloaded package run by the main orchestrator)


## Files (branch inp-p11c-q3, all committed)
- KAM/Planetary/Quantitative/BudgetPower.lean (464 lines, facade + signed decls): `BudgetRates`,
  `BudgetRates.Valid`, `BudgetRates.exponent`, `RateBounds`, `qb_poly` (copied verbatim from
  P11CSignatures.lean, checked by whitespace-normalised textual comparison), plus public helpers
  `BudgetRates.rateD/rateG/rateL/rateJ/rateX/rateH` (named D,G,L,J,X,H; `exponent_eq : exponent = 2*rateH + C1` by rfl),
  `qbPoly_collar`, `qbPoly_xibar_upper`, `qbPoly_second_lower`, `qbPoly_lambda_lower`.
- BudgetPower/Positivity.lean: `qbPoly_cutoffConstant_pos`, `qbPoly_diameter_pos` (+ bump/mollifier lemmas).
- BudgetPower/Rates.lean: power-rate algebra on (0,1].
- BudgetPower/Gamma.lean: `qbPoly_gap_pos`, `qbPoly_cDio_bound`, `qbPoly_gamma_lower` (ab_gamma).
- BudgetPower/Collar.lean: `qbPoly_tbar_bound` (ab_T0, both cases a_s=0 / a_s>0), `qbPoly_thetaMax_lower`.
Nodes: qb-poly / bu-poly -> `qb_poly`; fragments ab_gamma, ab_T0, ab_t0, ab_lam proved locally under the
`qbPoly_*` names (adm_budget NOT used; no dependency signal).

## Approach
c' = k^2 c/(2N) where k is the constant of `qbPoly_lambda_lower` (lambdaFlat >= k u^H), built from
constants of tbar<=Ct u^-L, gamma>=k2 u^G, tflat>=kt u^J, xibar<=Cx u^-X, thetaMax>=c^2/2^(mu+3) u^(a_beta+a_0),
cutoff constant > 0; all constants depend only on (N,mu,rho,tau,c,a_s). Constants are existentially chosen before a,d,u.

## Checks
- `scripts/lint_sources.sh`: exit 0 ("ABI HASHES OK (144 frozen declarations)").
- Gate build `KAM.Planetary.Quantitative.BudgetPower`: "Build completed successfully (9091 jobs)", no sorry;
  only 3 unused-variable linter warnings (hrho in Collar, hv/hu1 in BudgetPower).
- `#print axioms KAM.Planetary.qb_poly`: [propext, Classical.choice, Quot.sound].
- No set_option anywhere; all lines <= 100 cols; largest file 464 lines. No heartbeat issue in the final files
  (an earlier nlinarith in cDio_bound timed out and was replaced by an explicit calc).

## Uncertainties / notes for orchestrator
- Q2 (qb_comp: 0 < thresholds d) will need the same facts `p11c_cutoffConstant > 0` and `diameter > 0`:
  reuse `qbPoly_cutoffConstant_pos` / `qbPoly_diameter_pos` (import BudgetPower.Positivity) rather than re-proving;
  Q2 ran in parallel and could not see them. Watch for duplicate-helper clashes when merging.
- Both are genuinely needed: with diam = 0 (N>=2) or an unbounded cutoff sSup the Lean thresholds would be 0.
  They hold for NumericalValid data (epsLoss>0 and volume K > ofReal epsLoss force positive diameter).
- Positive note: qb_poly's hypotheses sufficed verbatim; no extra hypothesis was needed.

## Suspected errata / deviations
None found. Blueprint T0 uses |A0| inside tbar in the Lean def (Q1), consistent with the proof.

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q3 (qb_poly and the exact rates/exponent; Q1, U11a3 adm_budget proof fragments) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. The handoff says the fragments were proved locally (qbPoly_* helpers) without adm_budget (P11B B20 does not exist yet): check that the local fragments are exactly what the design allows Q3 to prove and that nothing is assumed. Audit ONLY KAM/Planetary/Quantitative/BudgetPower.lean and BudgetPower/*.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
