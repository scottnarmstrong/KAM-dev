# N12-06 prover handoff (branch inp-n1206, 77f0e5a; contains inp-n1205 (N12-04, N12-05; audited); offloaded package run by the main orchestrator; prover on claude-12)


## Files
- NEW `KAM/Nekhoroshev/Averaging/CorrectorRegular.lean` (~760 lines; under the 1500 cap). Nothing else changed. KAM.lean NOT edited
  (lint reports "KAM.lean is out of date; run scripts/gen_root_imports.py" because the new module is not yet registered: orchestrator to regenerate).

## Nodes proved
- `bpN:p12:wreg` (+ steps wr-smooth, wr-ac, wr-b, wr-d), `bpN:p12:ext-tsum` (used locally): `KAM.Nekhoroshev.wreg`
  (signature verbatim from N12Signatures.lean, incl. full-domain directional derivative HasSum for every z ∈ avgDomain, v real/complex-phase direction).
- `envelope_regular`: `KAM.Nekhoroshev.envelope_regular` (verbatim; only line-wrapping of the statement changed to satisfy the 100-col lint).

## Approach
- Summand `gk k y := (-χ_k(ι y.1)) • avgU k y.2`; `avgW = fun y => ∑' k, gk k y` (tsum_neg).
- `avgU k = aScal k • kvec k`, `aScal = coeff(ι I) * ψ(Q_k I)`; real derivative of aScal via product/chain rule, with Cauchy bound `2/s β_k` (coef part 3),
  `|dQ_k v| ≤ modeSize k * M₂ * ‖v‖` (from hM) and `corrector` bounds → `‖fderiv avgU‖ ≤ avgBterm` and the stated `avgBterm` bound.
- Termwise differentiation by `hasFDerivAt_tsum_of_isPreconnected` on the open convex set `avgDomain n R = univ ×ˢ ball 0 R` with a GLOBAL
  dominating series `domC * (1+|k|₁)^3 β_k` (valid on the whole domain because the coef bounds hold uniformly on `actionBall`; no local nbhd needed).
- C¹: each `gk k` is C¹ on avgDomain (coefficients holomorphic ⇒ `KAM.contDiffOn_infty_of_differentiableOn_pi`; ω is C²), so `fderiv gk k` continuous;
  `continuousOn_tsum` gives continuity of `fderiv avgW`; `contDiffOn_succ_iff_fderiv_of_isOpen`.
- Directional HasSum: evaluate the CLM-valued HasSum at v.
- Periodicity: `character_add`, integer shift has character 1 (`exp_int_mul_two_pi_mul_I`).
- Residual series: coef part 5 minus the θ-direction derivative series; `1 - yψ(y) = κ²/(y²+κ²)` from `corrector`. Norm bounds via
  `HasSum.norm_le_of_bounded` and `ENNReal.ofReal_tsum_of_nonneg`.
- Envelope measurability: `measurable_fderiv_apply_const` (frequency map measurable with no regularity), `Measurable.ennreal_tsum`; finiteness from summable majorants.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-n1206 KAM.Nekhoroshev.Averaging.CorrectorRegular`: "Build completed successfully (3181 jobs)"; only warnings are
  4 deprecation warnings (`Measurable.ennreal_tsum` → `Measurable.tsum`; left since replacement lives in a heavier import).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only complaint: "KAM.lean is out of date" (see above). No lines >100 cols.
- `#print axioms KAM.Nekhoroshev.wreg` and `…envelope_regular`: [propext, Classical.choice, Quot.sound].
- No sorry/axiom/maxHeartbeats/override; no heartbeat design signals (every declaration elaborates at default heartbeats).
- Signature check: normalised-whitespace comparison of both statements against N12Signatures.lean: identical.

## Uncertainties / deviations
- None in statements. The avgG guard is not needed: all bounds hold on all of `avgDomain` (avgG ⊆ actionBall); they are proved under the guard only
  because the statement asks for that. `hM` is used only at points of `closedBall 0 R`; `0 ≤ M₂` is derived from `hM` and `1 ≤ n` (d.hn).
- Private duplicate: `contDiffOn_freq'` copies the private `contDiffOn_freq` of Setting.lean (not exported there).

## Suspected errata
- None.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-06 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design (wreg incl. the full-domain directional derivative HasSum, envelope_regular, exact residual series, both partial derivative series); (2) proofs sound (SmoothSeries used with hypotheses discharged); no added premises; (3) hygiene (lint incl. 100-char lines). Audit ONLY the CorrectorRegular module(s) (compare with branch inp-n1205).
