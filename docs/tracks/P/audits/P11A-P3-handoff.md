# P11A-P3 prover handoff (branch inp-p11ap3, 6fd4eed; off inp (P11A-C0 audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Preparation/RectangularBracket.lean` (252 lines). KAM.lean NOT edited (lint reports it out of date: orchestrator must run `scripts/gen_root_imports.py`).

**Declarations (signatures verbatim from P11ASignatures.lean):** `p11Box`, `p11WBound`, `aniso_field` (bpP:p11:aniso-bracket, field clause), `aniso_bracket` (bpP:p11:aniso-bracket). `ab_der` / `ab_prod` are the private lemma `polyNbhd_box_subset` and the slack/limit argument inside `aniso_bracket`.

**Approach:** reduce to the isotropic Weighted estimates (`cauchy_loss`, `wbound_bracket`, `sup_le_wbound`, `inClass_fderiv_apply`). Base set V = inner box; with m = min rho1 rho2, polyNbhd V m lies in the outer box (likewise radius d = min(r01-r1+rho1, r02-r2+rho2) in the r0 box). Since V is the base set, losses are applied with radius m-δ (δ>0 slack) and δ→0 is taken (`le_of_small`, ge_of_tendsto). Bracket: bound (1/e)(1/(dσ)+1/((s0-s+σ)m))UW, algebraically equal to the stated form. Field: pointwise ∂θ ≤ M/(eσ), ∂I ≤ M/m, then max of the three scaled norms (e>1 absorbs the angle part).

**Checks:** gate build `KAM.Planetary.Preparation.RectangularBracket`: "Build completed successfully", no warnings. `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (only "KAM.lean is out of date", generated file untouched per rules).
`#print axioms KAM.Planetary.aniso_field` and `aniso_bracket`: [propext, Classical.choice, Quot.sound].

**Uncertainties / deviations:** none on statements. `hr1`,`hr2` unused in both theorems (kept for signature); `set_option linter.unusedVariables false in` on those two theorems only (same convention as Weighted/Cauchy). No heartbeat options. No errata found. No design signals.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-P3 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements = design signatures exactly (p11Box, p11WBound, aniso_field, aniso_bracket); (2) proofs sound (Weighted coefficient Cauchy estimates and algebra); no added premises; (3) hygiene. Audit ONLY KAM/Planetary/Preparation/RectangularBracket.lean.
