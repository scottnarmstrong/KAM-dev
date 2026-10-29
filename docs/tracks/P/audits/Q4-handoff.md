# Q4 prover handoff (branch inp-p11c-q4, ec61ba29; offloaded package run by the main orchestrator)


**Files:** new `KAM/Planetary/Quantitative/Budget.lean` (99 lines). No other file touched.

**Declarations (signed, verbatim statements):** `p11c_G0`, `p11c_B0`, `qb_beta` (`stepP:p11a:qb-beta`),
`budget` (`bpP:p11a:budget`, K5: `qb_comp ∧ qb_mono ∧ qb_beta`), `displacement_power_flat` (K6).
Unsigned helpers (all `qbBeta*`, short names unused elsewhere in KAM): `qbBetaRates`, `qbBetaRates_valid`,
`qbBeta_rateG`, `qbBeta_exponent`, `qbBetaC`, `qbBetaC_pos`, `qbBeta_rateBounds`, `qbBeta_valid`.

**Approach:** `qb_beta` is `qb_poly` (Q3) at u = b with the rates `a_beta = 1`, all others 0; the exponent
`BudgetRates.exponent` reduces exactly to `p11c_B0` (`G = G0 = (mu+1)/rho`). The constant `c0` is the min of
`1, vartheta, s, epsLoss, M⁻¹, M0⁻¹, C1⁻¹, diameter⁻¹`. `displacement_power_flat` uses `qbPoly_gamma_lower` (Q3) for
`gamma ≥ k b^{G0}` and `min .. ≤ cDelta sqrt eps / gamma`, `cD = cDelta / k`. `budget` assembles Q2's
`qb_comp`, `qb_mono` with `qb_beta`. Note: `displacement_power_flat` needs only `NumericalValid` (uses `hd.1`).
The brief names U11a1 `gamma_inverse`; it is not imported: the gamma lower bound comes from Q3's local
`qbPoly_gamma_lower`. No `gamma_inverse` identifier exists in KAM.

**Checks:**
- `inp_lake_build.sh <wt> KAM.Planetary.Quantitative.Budget`: Build completed successfully, no warnings in Budget.lean.
- `#print axioms` of `qb_beta`, `budget`, `displacement_power_flat`: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK; its only complaint is
  "KAM.lean is out of date" (new module; generated file, not edited by me; orchestrator regenerates).
- Longest line 99 columns. No maxHeartbeats, no sorry/axiom.

**Uncertainties / errata / deviations:** none. Design signals: none (default heartbeats).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row Q4 (qb_beta, budget, displacement_power_flat; Q2/Q3, U11a1 gamma_inverse) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. Audit ONLY KAM/Planetary/Quantitative/Budget.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
