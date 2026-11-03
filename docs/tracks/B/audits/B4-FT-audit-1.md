# B4-FT independent audit 1

Audit date: 2026-11-03 UTC. Audited HEAD `6a059ea09c3f00de6a62c0d9dfc0b8a8b9750bfa`, comparison ref `inp` = `58e886b1ecac99539862e5aa3ab98b19184c985b`. Initial working tree clean.

## Verdict

**PASS WITH NOTES for B4-FT items 1–6.** No frozen anchor or provider is supplied by this package; “seal-ready” and provider/frozen-type equality probes are inapplicable. This is an ordinary infrastructure package under `KAM.EffectiveStability`, not closure of a track I/N/P anchor or the forthcoming torus checker. No proof or statement defect found in the reviewed FT code.

The user's explicit report destination overrides the generic audit brief's main-worktree destination. The Track B AUDIT FOCUS and B4-FT/common briefs supply the applicable statement contract in place of unrelated I/N/P blueprint nodes. Read AGENTS, PLAN, DECISIONS, SPEC, FREEZE-PROPOSAL, OWNER-DECISIONS, the handoff, both B briefs and common prover brief; compared all five Lean modules with `git diff inp...HEAD`; checked plan §3.2, the Cartesian analogue, canonical setting and `Torus.lean:35–52`. The local DECISIONS snapshot ends at D70; D71 is the packet's recorded overnight status, not evidence of an approved freeze.

## Findings and consumer scope

1. **Normalizer and equality checker: PASS.** `Basic.lean:327–420` trims both lists, negates the frequency and sine coefficient together, removes the zero-frequency sine contribution, merges only equal `(k, α, e)` keys, and drops only terms with both rational coefficients zero. Evaluation preservation is proved for the generic trigonometric laws and instantiated without assumptions for ℝ/ℂ. `ftEqCheck` tests whether the normalized *difference* is empty; it does not depend on an ordering of normalized lists. Soundness is global, including polynomials that do not fit the chosen dimension. Completeness is neither claimed nor needed.
2. **Products and derivatives: PASS.** The sum-frequency coefficients are `(cc'−ss')/2`, `(cs'+sc')/2`; difference-frequency coefficients are `(cc'+ss')/2`, `(sc'−cs')/2`. Tags add. Angle differentiation increments `e` exactly once and maps coefficients to `(k_i s, −k_i c)`. Action differentiation uses the exponent multiplier and predecessor only in the nonzero-exponent branch. Generic calculus hypotheses express actual derivative/regularity laws for arbitrary `cf,sf`; the unconditional real/complex instances discharge them. No hard analytic result is hidden in a public FT premise.
3. **Brackets and Lie sums: PASS.** `Bracket.lean:52–63,141–224` uses `{P,Q}=DφP·DJQ−DJP·DφQ`, agreeing with `Canonical.Setting:37–45` and the frozen real field `(DJQ,−DφQ)`. Summing only to `ftWidth P` is valid: omitted derivatives of P vanish, and terms outside `Fin n` vanish under `FTFits n P`. Q need not fit for a single bracket correctness theorem; this is stronger than requiring both. Iteration preserves fits, recurs as `{ad^k P,χ}`, and the Lie sum is exactly `j < L` with rational `1/j!`, including L=0. No infinite Lie series or exact flow is asserted.
4. **Majorants and strip units: PASS.** `Bound.lean:35–268` proves π ≤ 31416/10000 from Mathlib's π bound. The action and frequency sums match the list semantics, with fits needed to equate list products/sums and `Fin n` products/sums. On a nonempty action box the pointwise radius premises supply nonnegativity for the relevant radii; no extra global radius hypothesis is necessary. The phase estimate is `|Im(2π k·φ)| ≤ |k|₁ log lam`; exponentiation gives `lam^|k|₁`. Thus the geometric width is `log lam/(2π)`, consistent with plan §3.2's `exp(2πσ|k|₁)`. For `0 < lam < 1` the strip is empty when n>0, since its proposed width is negative. When n=0, fits forces all frequency entries zero, giving exponent zero and bound factor 1. The broader positive-lam theorem is sound; it does not certify a negative-width strip with points.
5. **B1-T interface: PASS, prospective use.** `abs_fderiv_ftEvalR_le` concludes the literal `|fderiv ℝ R w (Pi.single j 1,0)| ≤ η j` after setting R to `ftEvalR P`, b to the cast rational radius list, and η to the cast `ftAngleDriftBound`. `ftSupBound_dφ` identifies the formula exactly. A fresh application probe checks this quantified drift premise with πub=`ftPiUB`. Periodicity holds for every integer shift, globally, with no fits premise; regularity is supplied at every requested order, including smoothness and analyticity. These discharge the FT remainder's local interface; other B1-T premises and a complete torus step checker are outside this package.
6. **Kernel smoke tests: PASS.** Nine examples in `Bound.lean:273–295` use `decide +kernel`, including both bracket signs, product identities, sign normalization, a Leibniz example, two-mode bracket, typing, and a negative equality check. Additional audit examples cover zero-frequency sine removal, padded mixed-sign canonicalization, distinct π tags, conservative fits checking, and the small-lam edge cases.

Notes: `ftFitsCheck` checks list lengths, so it can reject `ftCosMode [1,0]` at n=1 even though `FTFits 1` holds; it is a sufficient checker, not a complete decision procedure for fits. `ftNormalize` need not sort keys or eliminate all trigonometric identities; only soundness is promised. The supplied real/complex cos/sin-mode evaluation formulas live in the generic `ftEvalG_cosMode/sinMode` API rather than separately named R/C wrappers; their specializations are definitional. Handoff line counts undercount Basic, Deriv and Bound by one (actual 570/347/299); harmless metadata discrepancy. The four implementation modules total 1442 lines, plus a 21-line facade, below the brief's approximate 1500-line package staging threshold.

## Declaration review

One row per explicit public declaration; namespace `KAM.EffectiveStability` throughout. Structure fields and derived equality are representation/propositional support, not independent analytic premises. Each definition row classifies the whole-carrier object; no fallback substitutes a hard theorem. Missing list entries default to zero by the specified representation. Bounds are total rational expressions and are asserted as bounds only under their stated pointwise premises.

| Node | Lean declaration (file:line) | Verdict | Classification / reason |
|---|---|---|---|
| B4-1 | `FTMono` (Basic.lean:34) | PASS | Exact rational trigonometric monomial data with explicit π-power tag. |
| B4-1 | `FTPoly` (Basic.lean:48) | PASS | Finite list carrier; evaluation sums all terms. |
| B4-1 | `ftAddPadZ` (Basic.lean:51) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftGetD_addPadZ` (Basic.lean:56) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-1 | `ftGetD_neg` (Basic.lean:68) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-1 | `ftTrimZ` (Basic.lean:77) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftGetD_trimZ` (Basic.lean:81) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-1 | `ftFirstNeg` (Basic.lean:97) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftGetD_zero_of_length_le` (Basic.lean:101) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-1 | `FTTrig` (Basic.lean:106) | PASS | Prop bundle of generic trigonometric laws; actual R/C instances proved. |
| B4-1 | `ftTrig_real` (Basic.lean:120) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftTrig_complex` (Basic.lean:123) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftPhase` (Basic.lean:132) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-1 | `ftJProd` (Basic.lean:135) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-1 | `ftMonoEvalG` (Basic.lean:138) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-1 | `ftEvalG` (Basic.lean:143) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-1 | `ftEvalG_nil` (Basic.lean:149) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_cons` (Basic.lean:153) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_append` (Basic.lean:158) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftAdd` (Basic.lean:163) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftNeg` (Basic.lean:166) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftSub` (Basic.lean:169) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftSmul` (Basic.lean:172) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftConst` (Basic.lean:175) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftJVar` (Basic.lean:178) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftCosMode` (Basic.lean:181) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftSinMode` (Basic.lean:184) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftEvalG_add` (Basic.lean:187) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_neg` (Basic.lean:192) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_sub` (Basic.lean:201) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_smul` (Basic.lean:205) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftJProd_nil` (Basic.lean:214) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftPhase_nil` (Basic.lean:217) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_const` (Basic.lean:220) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftJProd_unit` (Basic.lean:225) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_jVar` (Basic.lean:236) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_cosMode` (Basic.lean:241) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_sinMode` (Basic.lean:246) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftPhase_congr` (Basic.lean:253) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftJProd_congr` (Basic.lean:258) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftPhase_add` (Basic.lean:263) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftPhase_neg` (Basic.lean:270) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftJProd_add` (Basic.lean:277) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftMonoMul` (Basic.lean:284) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftMul` (Basic.lean:291) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-1 | `ftMonoEvalG_mul` (Basic.lean:293) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_mulMono` (Basic.lean:306) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_mul` (Basic.lean:315) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftMonoCanon` (Basic.lean:327) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftJProd_trim` (Basic.lean:334) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftMonoEvalG_canon` (Basic.lean:338) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftInsertMono` (Basic.lean:352) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftEvalG_insertMono` (Basic.lean:359) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftMerge` (Basic.lean:372) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftEvalG_merge` (Basic.lean:374) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_canonmap` (Basic.lean:383) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalG_filter` (Basic.lean:390) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftNormalize` (Basic.lean:403) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftEvalG_normalize` (Basic.lean:406) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEqCheck` (Basic.lean:411) | PASS | Exact canonicalization/checking algorithm; preservation/soundness proved. |
| B4-1 | `ftEvalG_eq_of_eqCheck` (Basic.lean:413) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR` (Basic.lean:427) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-1 | `ftEvalC` (Basic.lean:431) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-1 | `ftEvalC_ofReal` (Basic.lean:434) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_add` (Basic.lean:445) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_add` (Basic.lean:448) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_neg` (Basic.lean:451) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_neg` (Basic.lean:454) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_sub` (Basic.lean:457) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_sub` (Basic.lean:460) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_smul` (Basic.lean:463) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_smul` (Basic.lean:466) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_mul` (Basic.lean:469) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_mul` (Basic.lean:472) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_const` (Basic.lean:475) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_const` (Basic.lean:478) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_jVar` (Basic.lean:481) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_jVar` (Basic.lean:484) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_normalize` (Basic.lean:487) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_normalize` (Basic.lean:490) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalR_eq_of_eqCheck` (Basic.lean:494) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `ftEvalC_eq_of_eqCheck` (Basic.lean:499) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-1 | `FTFits` (Basic.lean:506) | PASS | Support typing / conservative Boolean length test, with soundness. |
| B4-1 | `ftFitsCheck` (Basic.lean:510) | PASS | Support typing / conservative Boolean length test, with soundness. |
| B4-1 | `ftFits_of_check` (Basic.lean:513) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_nil` (Basic.lean:519) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_add` (Basic.lean:521) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_neg` (Basic.lean:526) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_sub` (Basic.lean:531) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_smul` (Basic.lean:534) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_mul` (Basic.lean:539) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_const` (Basic.lean:549) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_jVar` (Basic.lean:554) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_cosMode` (Basic.lean:560) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-1 | `ftFits_sinMode` (Basic.lean:565) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-2–3 | `ftMonoDφ` (Deriv.lean:33) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-2–3 | `ftMonoDJ` (Deriv.lean:37) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-2–3 | `ftDφ` (Deriv.lean:43) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-2–3 | `ftDJ` (Deriv.lean:46) | PASS | Exact padded-list algebra or formal derivative; corresponding evaluation/typing laws proved. |
| B4-2–3 | `ftDφ_nil` (Deriv.lean:48) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `ftDJ_nil` (Deriv.lean:49) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `ftDφ_cons` (Deriv.lean:50) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `ftDJ_cons` (Deriv.lean:52) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `ftJDeriv` (Deriv.lean:60) | PASS | Literal phase, monomial, evaluation or formal product derivative; correct on stated carrier. |
| B4-2–3 | `ftEvalG_dJ_mono` (Deriv.lean:63) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `ftMonoEvalG_dφ` (Deriv.lean:84) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `ftPhase_lin` (Deriv.lean:93) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-2–3 | `hasDerivAt_ftJProd` (Deriv.lean:107) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `hasDerivAt_ftMonoEvalG` (Deriv.lean:129) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `hasDerivAt_ftEvalG` (Deriv.lean:175) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `contDiff_ftMonoEvalG` (Deriv.lean:193) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `contDiff_ftEvalG` (Deriv.lean:208) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `fderiv_ftEvalG_apply` (Deriv.lean:221) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `fderiv_ftEvalG_dφ` (Deriv.lean:239) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `fderiv_ftEvalG_dJ` (Deriv.lean:249) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftPhase_add_int` (Deriv.lean:268) | PASS | Period-one lattice identity; generic periodicity discharged for R/C. |
| B4-2–3 | `ftEvalG_add_period` (Deriv.lean:278) | PASS | Period-one lattice identity; generic periodicity discharged for R/C. |
| B4-2–3 | `ftEvalR_contDiff` (Deriv.lean:299) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalC_contDiff` (Deriv.lean:303) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalC_differentiable` (Deriv.lean:307) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalR_fderiv_dφ` (Deriv.lean:311) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalR_fderiv_dJ` (Deriv.lean:317) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalC_fderiv_dφ` (Deriv.lean:323) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalC_fderiv_dJ` (Deriv.lean:329) | PASS | Actual calculus identity/regularity; generic laws discharged for R/C. |
| B4-2–3 | `ftEvalR_add_period` (Deriv.lean:335) | PASS | Period-one lattice identity; generic periodicity discharged for R/C. |
| B4-2–3 | `ftEvalC_add_period` (Deriv.lean:341) | PASS | Period-one lattice identity; generic periodicity discharged for R/C. |
| B4-4 | `ftWidth` (Bracket.lean:31) | PASS | Finite support width / bracket / iteration / factorial-weighted sum; exact evaluation proved. |
| B4-4 | `ftLength_le_width` (Bracket.lean:35) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-4 | `ftGetD_zero_of_width` (Bracket.lean:46) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-4 | `ftBracket` (Bracket.lean:52) | PASS | Finite support width / bracket / iteration / factorial-weighted sum; exact evaluation proved. |
| B4-4 | `ftAdPow` (Bracket.lean:57) | PASS | Finite support width / bracket / iteration / factorial-weighted sum; exact evaluation proved. |
| B4-4 | `ftLieSum` (Bracket.lean:62) | PASS | Finite support width / bracket / iteration / factorial-weighted sum; exact evaluation proved. |
| B4-4 | `ftFits_flatMap` (Bracket.lean:67) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-4 | `ftFits_dφ` (Bracket.lean:75) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-4 | `ftFits_dJ` (Bracket.lean:80) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-4 | `ftFits_bracket` (Bracket.lean:91) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-4 | `ftFits_adPow` (Bracket.lean:97) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-4 | `ftFits_lieSum` (Bracket.lean:103) | PASS | Typing preservation or sufficient-check soundness; no analytic premise. |
| B4-4 | `ftDJ_eq_nil_of_getD` (Bracket.lean:107) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-4 | `ftEvalG_flatMap` (Bracket.lean:123) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-4 | `ftEvalG_dφ_zero` (Bracket.lean:131) | PASS | Literal algebra/evaluation/trigonometric/support identity; matches B4 item 1 or its structural helpers. |
| B4-4 | `ftEvalG_bracket` (Bracket.lean:141) | PASS | Exact canonical bracket / ad orientation / finite Lie-sum semantics. |
| B4-4 | `ftEvalC_bracket_complex` (Bracket.lean:169) | PASS | Exact canonical bracket / ad orientation / finite Lie-sum semantics. |
| B4-4 | `ftEvalR_bracket_real` (Bracket.lean:178) | PASS | Exact canonical bracket / ad orientation / finite Lie-sum semantics. |
| B4-4 | `ftEvalC_adPow_complex` (Bracket.lean:192) | PASS | Exact canonical bracket / ad orientation / finite Lie-sum semantics. |
| B4-4 | `ftEvalG_lieSum` (Bracket.lean:202) | PASS | Exact canonical bracket / ad orientation / finite Lie-sum semantics. |
| B4-4 | `ftEvalC_lieSum_complex` (Bracket.lean:216) | PASS | Exact canonical bracket / ad orientation / finite Lie-sum semantics. |
| B4-5 | `ftPiUB` (Bound.lean:35) | PASS | Total exact rational/natural formula; bound theorem supplies validity domain. |
| B4-5 | `pi_le_ftPiUB` (Bound.lean:37) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `ftL1` (Bound.lean:44) | PASS | Total exact rational/natural formula; bound theorem supplies validity domain. |
| B4-5 | `ftBPow` (Bound.lean:47) | PASS | Total exact rational/natural formula; bound theorem supplies validity domain. |
| B4-5 | `ftMonoBound` (Bound.lean:51) | PASS | Total exact rational/natural formula; bound theorem supplies validity domain. |
| B4-5 | `ftSupBound` (Bound.lean:55) | PASS | Total exact rational/natural formula; bound theorem supplies validity domain. |
| B4-5 | `ftAngleDriftBound` (Bound.lean:59) | PASS | Total exact rational/natural formula; bound theorem supplies validity domain. |
| B4-5 | `norm_cos_le_exp_im` (Bound.lean:65) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `norm_sin_le_exp_im` (Bound.lean:77) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `ftNorm_jProd_le` (Bound.lean:95) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `norm_ftMonoEvalG_le` (Bound.lean:117) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `ftSupBound_cons` (Bound.lean:150) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `norm_ftEvalG_le_supBound` (Bound.lean:154) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `ftSum_range_eq_fin` (Bound.lean:177) | PASS | List/support/finite-sum helper with explicit structural premises. |
| B4-5 | `abs_im_phase_le` (Bound.lean:182) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `norm_ftEvalC_le_supBound` (Bound.lean:215) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `abs_ftEvalR_le_supBound` (Bound.lean:237) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `ftSupBound_dφ` (Bound.lean:251) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |
| B4-5 | `abs_fderiv_ftEvalR_le` (Bound.lean:261) | PASS | Exact majorant or supporting inequality; premises match intended pointwise domain. |

## Verification receipts

All Lean/Lake commands are serialized and run under this prefix (including the lint subprocess's Lean ABI check):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

The build driver adds `nice -n 5` around its targeted `lake build`. No resource-budget overrides, dependency mutation, full rebuild, production-source edits, or state-changing git were used.

