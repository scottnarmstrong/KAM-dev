# S8-I prover handoff (branch inp-s8i, 9dd80da; contains inp-s8l (audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- New: `KAM/Planetary/SecularForm/LaplaceIdentities.lean` (~310 lines). Imports Basic and Laplace.

## Declarations (design signatures, verbatim)
- `SecularForm.identities` (`bpP:p8:identities`), both identities; statement unchanged.
- `SecularForm.radialPhi`, `SecularForm.radialH` (definitions, verbatim).
- Helpers: `hasDerivAt_tsum_pow` (termwise differentiation of `∑ a_q z^(e_q)` on |z|<1 with polynomially bounded
  coefficients), `halfCoef`, `pcoef_half_le_one`, `half_deriv1`, `half_deriv2`, `poch_succ'`, `poch_three_halves`,
  `pow_aux1/2`, `term_comb1/2`, `coef1`, `coef2`, `hasSum_shift_unique`.

## Approach
`b_{1/2}^{(k)}` equals its binomial power series `∑ c_{q+k}c_q α^(2q+k)` on (0,1) (S8-L `hasSum_laplaceTerm`);
`hasDerivAt_tsum_of_isPreconnected` twice gives the series of `deriv` and `iteratedDeriv 2`. Each identity's LHS is
a `HasSum` whose q=0 term vanishes; shifting by one, the termwise coefficient identity is the rational recurrence
`poch(3/2) q = 2 poch(1/2)(q+1)` plus `field_simp; ring`; `HasSum.unique` closes.

## Checks
- Gate build `KAM.Planetary.SecularForm.LaplaceIdentities`: Build completed successfully.
- `scripts/lint_sources.sh`: only "KAM.lean is out of date" (not edited per rules); modules/frozen/ABI PASS.
- `#print axioms identities`: [propext, Classical.choice, Quot.sound].
- No `sorry`, no heartbeat overrides, file well under 1500 lines.

## Uncertainties / errata / deviations
None. Statements true as given. KAM.lean needs regeneration for the new module (orchestrator).

AUDIT FOCUS (design docs/tracks/P/design/P810-LEAN-DESIGN.md row S8-I and its proof plan; audits DESIGN-P810-design-audit-{1,2}.md; signatures .drafts/design/P810Signatures.lean): (1) statements/definitions = design signatures (the identities, radialPhi/radialH); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY SecularForm/LaplaceIdentities*.lean (compare with branch inp-s8l).
