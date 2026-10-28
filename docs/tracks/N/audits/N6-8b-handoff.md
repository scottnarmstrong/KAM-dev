# N6-8b prover handoff (branch inp-n68b, 8d552de; base inp-n68a; offloaded package run by the main orchestrator; prover on claude-12)


Branch `inp-n68b`, worktree `/root/code/KAM-inp-n68b`. All committed.

## Files (new; each < 180 lines; no maxHeartbeats, sorry, axiom)
- `KAM/Nekhoroshev/NormalForm/NormalFormAux.lean` (175): `chain_translate`, `chain_real` (integer translations / reality
  along `chain Φ m`), `coeff_homRes` (coeffs of `P_Λ T_K u` = `1_{Λ∩Z_K} û_k`, via `projections` twice), `coeff_sum_eq_zero`,
  `nf_coeff_g` (`ĝ_k = 0`, `k ∉ Λ ∩ Z_K`, for `g_N`), `inClass_mono_nf`, `wbound_zero_nf`.
- `NormalFormCaseA.lean` (144): `nfSteps` (verbatim from signature), `NFConcl` (= the conclusion of `normal_form`, verbatim),
  `fstSeminorm`/`sndSeminorm`, `nfConcl_caseA` (Case A, all `N ≥ 0`: `Ψ = chain nfPhi N`, `g = nfG (N+1)`, `fs = nfF (N+1)`;
  telescope on `Uᵢ = Dom rᵢ sᵢ`, displacement via the two seminorms and `nf_disp_sums`; exact-correction clause from
  `nf_final_g_zero`, the `iterU < exp` branch contradicting Case A).
- `NormalForm.lean` (155): `nfConcl_caseB` (single step, losses `(r/4, s/3)`, `g = homRes K Λ f`), `normal_form`
  (signature verbatim; `by_cases` on `exp(-κ/6) ≤ iterU α p ε (r/8) (s/6)`), `nonresonant_case` (signature verbatim).
- Arith*/Steps* untouched (no interface gap). `nfSteps` lives in `NormalFormCaseA` (imported by `NormalForm`), same declaration/namespace.

## Checks
- Gate: `inp_lake_build.sh /root/code/KAM-inp-n68b KAM.Nekhoroshev.NormalForm.NormalForm`: `Build completed successfully (3241 jobs)`, no warnings.
- `scripts/lint_sources.sh`: PASS except expected `KAM.lean is out of date` (generated; not edited, rule 10); no >100-char lines.
- `#print axioms` of `normal_form`, `nonresonant_case`, `nfConcl_caseA`, `nfConcl_caseB`: all `[propext, Classical.choice, Quot.sound]`.

## Notes
- `nonresonant_case`: `ε ≥ 0` is derived from `WBound` at a point `I ∈ polyNbhd D r` (the claim is vacuous when `polyNbhd` is empty); no extra hypothesis.
- Audit note F2 honored: both equality cases (`N = 0`, Case B) proved; the "Case B" test is the carried-bound `iterU α p ε (r/8) (s/6)` literally.
- No errata, no deviations, no design signals.

AUDIT FOCUS (design docs/tracks/N/design/PART67-LEAN-DESIGN.md v2 row N6-8 and the N6-8 proof plan; audits DESIGN-N67-design-audit-{1,2}.md; signatures .drafts/design/NPart67Signatures.lean; blueprint-N p6 normal-form, #data, nonresonant-case): (1) statements = design signatures and blueprint EXACTLY (normal_form, nonresonant_case and #data); consume the audited session-1 Arith/Steps interface with no added premise; (2) proofs sound; (3) hygiene (lint incl. 100-char lines). Audit ONLY the NormalForm module(s) added on top of inp-n68a.
