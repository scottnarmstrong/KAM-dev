# T7 prover handoff (branch inp-p11c-t7, a7c0963c; offloaded package run by the main orchestrator)


## Files (new)
KAM/Planetary/PlanarTorsion/Characters.lean (facade) and Characters/{Defs,Trig,Factor,Basic,Poly,Average,CharPoly,Bracket}.lean (all < 400 lines).
- Defs: p11c_monomial, QuarticFamily(.eval), p11c_rotation, p11c_character, p11c_average, p11c_NR4, p11c_n0, p11c_bracket (verbatim from P11CSignatures.lean).
- Basic: `char` (all four clauses). CharPoly: `character_polynomial`. Average: `average_action_polynomial`. Bracket: `character_bracket`.
- Graph steps ch-mon / ch-bra: proved as local lemmas (charG_expand, charFc_eq, charFc_rot, character_eq_sum, character_covariance; bracket via rotation_hasDerivAt). bpP:p11b:char and sec-bnf#data (QuarticFamily, NR4, n0, bracket, rotation) are all in T7. Nothing assigned to another package was left undone; p11c_NR4/p11c_n0/p11c_bracket are defined here only (design lists them T1/T7; Setting.lean lacks them).

## Approach
Per plane, the rotated monomial (cosθx+sinθy)^p(−sinθx+cosθy)^q equals e^{-idθ}·Q(e^{iθ}) with Q an explicit polynomial (coefficients in ℂ[x,y], total degree ≤ d); Fourier coefficients are Q's coefficients. The box integral factors over the two planes (restrict_pi_pi + integral_fintype_prod_eq_prod); covariance by periodic shift; reconstruction by evaluating at θ=0; reality by integral_conj; bracket by chain rule along the rotation curve (characters are polynomials, hence differentiable). Average: zero mode is rotation-invariant and homogeneous, so K·(x²+y²)^m (0 in odd degree); the quartic family A is built explicitly (charQcoef).

## Checks
- `inp_lake_build.sh ... KAM.Planetary.PlanarTorsion.Characters`: success (9118 jobs), no sorry warnings.
- `#print axioms` of char, character_bracket, character_polynomial, average_action_polynomial: [propext, Classical.choice, Quot.sound] each.
- scripts/lint_sources.sh: see final line appended below.
- No heartbeat overrides, no EuclideanSpace; helper names are in namespace KAM.Planetary.PlanarCharacters (charG, charFc, charQ, ...) or prefixed char*/charAvg*; public KAM.Planetary extras: charIdx_sum, sum_piFinset_two, character_support, character_covariance, character_eq_sum is in PlanarCharacters, charLam, charAvgA/B/C, average_formula, charIdx_single, charQcoef, quartic_of_actions, character_mv, character_homog, mv_eval_differentiable, character_differentiable, n0_fderiv_apply, hamiltonian_n0, rotation_hasDerivAt (grepped before use; no clashes found at build time).

## Uncertainties / errata / deviations
None: no statement changed, no extra hypotheses. No suspected source errata. Design signals: none (all elaborates at default heartbeats).
- lint_sources.sh: check_lean_modules PASS (830 files); FROZEN-ANCHOR GUARD OK; ABI HASHES OK (144 frozen declarations).

AUDIT FOCUS: design docs/tracks/P/design/P11C-LEAN-DESIGN.md row T7 (QuarticFamily, characters, polynomial/covariance/bracket clauses; exact finite monomial algebra) and its node table; P11C design audits; signatures /root/code/KAM-inp/.drafts/design/P11CSignatures.lean. The orchestrator ran a whitespace-only lint round (31 long lines wrapped) after the prover: check it changed no token. Audit ONLY KAM/Planetary/PlanarTorsion/Characters.lean and Characters/*.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
