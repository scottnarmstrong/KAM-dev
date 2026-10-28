# S8-4 audit 3 — delta audit

**PASS WITH NOTES. F2 CLOSED; F1 remains closed.** All three signed exports pass; q4-a now reaches the literal physical pair fourth jet with its prefactor and no assumed expansion. This infrastructure package seals no frozen anchor. Notes: permitted stale generated root, inherited whitespace, and the existing historical-ruling/Part 11b scope boundaries below.

Snapshot: HEAD `470d1de23e092f9c75c972fdcd26e59c85600c80`; inp `eff45716c45678ce9fbb21a346ab5821d70a823b`; Round 2 baseline `7fe32f2c38cb0bf0e64b39154c88f80623bf419a`. `git diff inp...HEAD` selects merge base `9400863e51e5f140a497a3774d3dff7b479e0d04` with a multiple-base warning. Its inventory includes inherited DiagonalJet and reports; mathematical scope is only Quartic*.lean. Fresh proof review covers aab2fce3 and both rename commits; unchanged proofs retain the explicitly scoped audit-1/2 baseline. No production edits, git mutations, providers, or anchor-sealing claims.
Authority: supplied brief, AGENTS/PLAN/DECISIONS, both handoffs, audits 1/2, track-P statement conventions, P810 design row/proof cuts and exact signatures, blueprint p8:216–234. Applied lean-statement-audit/manuscript-audit as a focused tier-2 delta audit; the user already authorized report/scratch writes and targeted checks. The exact user destination overrides the generic brief. Acceptance: unchanged signed bytes; unrestricted constant term; literal pair/prefactor attachment; internally discharged expansion; pure renames; width ≤100; serial hygiene gates.
Pinned SHA256: signatures `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`; blueprint p8 `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc`; design `f555e21a468123ce906f6818359cb8faaffc5d0435ea0f70c65967cec38722c4`. All equal prior snapshots. Package digest `bc1e60ebab11d6eafc66efffa718ec465bb91e37c6162f5a682e2a3b30d66847`: SHA256 of concatenated `path:sha256(bytes)\n`, facade first, then sorted Quartic/*.lean paths (24 files).

F2 refutation/closure: p8:221 says “if ... is the quadratic part and ... the quartic part” and explicitly “times the appropriate prefactor”; p8:232 says “The conversion is the expansion”. Conversion:443–459 retains arbitrary W0 and pref and the exact negative A/4, A′/4, B/8 corrections. Its remainder premise is a Taylor-data helper premise, not by itself an unconditional theorem for arbitrary W with odd terms. Expansion:133–186 proves that premise, including W(0), from local analyticity/O(2) invariance and identifies orders 2/4 as derivatives divided by 2/24. Thus the source's standing setting pays the helper's premise; no claim that arbitrary functions with merely named quadratic/quartic parts have no odd terms.
PairChart:160–249 assumes only positive ordered axes/actions and i<j. At :179–186, quartic_scaling supplies analyticity of the actual dimensionlessPair; qpc_W_invariant transports pair_matW_invariant using the explicit local chart inverse and cancels a proved nonzero physical prefactor. At :186–189, taylor_parts_of_invariant produces hexp and passes it to conversion_const. At :196–204, the literal pair's fourth derivative/24 is identified with the existing quarticCoeff polynomial by pairQuartic_eq. At :211–249, eventual full-function equality from quartic_pair_scaling and homogeneous-ray uniqueness identify the fourth coefficient. No derivative of an O-term is taken; all chart/separation guards are established near zero. The resulting equality holds for every w, not merely near zero.
Adversarial checks: W≡1 now instantiates the general helper with W0=1 (fresh Lean probe); pref=0 is permitted in that helper and physical prefactor cancellation is independently justified from positive masses/G/outer axis. The inverse law is used only with L>0 and planeSq(v)<1. A quartic coefficient cannot hide in the O(s⁵) remainder: ChartAlgebra:124 proves this by evaluating at s and 2s, eliminating the quadratic coefficient. No surviving mathematical blocker or new source defect.

| Node / declaration (namespace KAM.Planetary.SecularForm) | Verdict | Evidence |
|---|---|---|
| quartic | PASS | Exact signed header and unchanged proof; no frozen seal. |
| quartic_pair_scaling | PASS | Exact signed header and unchanged proof; literal full-function prefactor. |
| quartic_scaling | PASS | Exact signed header and unchanged proof; separated-domain analyticity. |
| q4-a / quartic_sqrt_chart_conversion_const | PASS, Taylor-data helper | Arbitrary constant and prefactor; source formula with correct signs/denominators. |
| q4-a / exists_poly_of_multilinear_two | PASS | Bilinear diagonal expanded in the finite coordinate basis. |
| q4-a / quadratic_form_of_invariant | PASS | Consumes Weyl.quadratic_invariant; invariance is an appropriate generic-helper premise. |
| q4-a / taylor_parts_of_invariant | PASS | Produces quadratic/quartic Taylor data and centered remainder, kills odd jets with −1. |
| q4-a / sqrtChart | PASS | Literal exact square-root formula. |
| q4-a / sqrtChartInv | PASS | Literal inverse formula, inverse identity locally guarded. |
| q4-a / planeSq_smul_vec | PASS | Homogeneous quadratic identity. |
| q4-a / planeDot_smul_vec | PASS | Bilinear scalar-product identity. |
| q4-a / quarticMonomials_smul_vec | PASS | Six exact degree-four identities. |
| q4-a / poincareV_pair | PASS | Exact original Poincaré chart, positive action. |
| q4-a / continuous_planeSq_vec | PASS | Polynomial continuity. |
| q4-a / continuous_sqrtChart | PASS | Continuity of total real square root and constant scalar division. |
| q4-a / sqrtChart_zero | PASS | Exact zero value. |
| q4-a / continuous_sqrtChartInv | PASS | Denominator strictly positive on its entire carrier. |
| q4-a / sqrtChartInv_zero | PASS | Exact zero value. |
| q4-a / planeSq_mulVec | PASS | Orthogonal invariance from RᵀR=1. |
| q4-a / sqrtChartInv_mulVec | PASS | Orthogonal equivariance. |
| q4-a / sqrtChart_sqrtChartInv | PASS | Local inverse for L>0, planeSq<1. |
| q4-a / quartic_coeff_eq_zero_of_isBigO | PASS | Ray uniqueness; no smoothness assumed. |
| q4-a / quartic_pair_chart_conversion | PASS | Literal physical fourth jet, expansion produced inside proof. |
| q4-str / q4_action_axis | PASS | Pure rename in e4b37745. |
| q4-str / q4_analyticAt_pairSlowSecular | PASS | Pure rename in e4b37745. |
| q4-str / q4_avg_finset_sum | PASS | Pure rename in e4b37745. |
| q4-str / q4_pairData | PASS | Pure rename in 470d1de2; same physical data body. |
| q4-str / q4_pairSlowSecular_pairData | PASS | Pure rename in 470d1de2. |
| q4-b / q4_pairSlowSecular_swap | PASS | Pure rename in 470d1de2. |
| q4-str / q4_secular_eq_avg | PASS | Pure rename in 470d1de2. |
| q4-str / q4-b / q4-c unchanged cuts | PASS, baseline scope | Structure/diagonal derivative interfaces unchanged; mixed coefficients and repaired CP11 certificate stay Part 11b. |

Binder audit (S=SOURCE, ST=STANDING, T=TYPING; EXCESS=0, RULED=0). Repeated scalar/vector data are separately listed; source references are p8:221/232 and its standing physical/O(2) conventions. Generic helper premises are discharged at the literal application as detailed above.
| Surface | Binder | Bin / source meaning |
|---|---|---|
| conversion_const | Λ₁ | T: first action scalar |
| conversion_const | Λ₂ | T: second action scalar |
| conversion_const | h₁ | S: Λ₁>0 |
| conversion_const | h₂ | S: Λ₂>0 |
| conversion_const | A | T: quadratic coefficient |
| conversion_const | A′ | T: quadratic coefficient |
| conversion_const | B | T: quadratic coefficient |
| conversion_const | W0 | T: arbitrary constant Taylor datum |
| conversion_const | pref | T: arbitrary scalar prefactor |
| conversion_const | c | T: six quartic coefficients |
| conversion_const | W | T: scalar function of two planar vectors |
| conversion_const | hW | S: centered even Taylor data, produced by Expansion in the standing source setting |
| taylor_parts | F | T: function on PairW |
| taylor_parts | hF | S: real analyticity at zero |
| taylor_parts | hinv | ST: local simultaneous O(2) invariance |
| pair_conversion | n | T: dimension |
| pair_conversion | D | T: original Data n (expanded below) |
| pair_conversion | i | T: first index |
| pair_conversion | j | T: second index |
| pair_conversion | I0 | T: first action |
| pair_conversion | J0 | T: second action |
| pair_conversion / D | G | T: gravitational scalar |
| pair_conversion / D | m0 | T: central mass |
| pair_conversion / D | m | T: original mass vector |
| pair_conversion / D | hG | ST: G>0 |
| pair_conversion / D | hm0 | ST: m0>0 |
| pair_conversion / D | hm | ST: each mass>0 |
| pair_conversion / D | hn | ST: positive planet count |
| pair_conversion | hij | S: ordered pair i<j |
| pair_conversion | hI | S: positive first action |
| pair_conversion | hJ | S: positive second action |
| pair_conversion | hab | S: first axis strictly below second |
Counts: conversion T=9/S=3; Taylor-parts T=1/S=1/ST=1; pair top-level T=6/S=4, Data expands additionally T=3/ST=4. No analytic result, expansion, coefficient identity, or derivative bound is smuggled into Data.
Definition classification: the two new public defs sqrtChart/sqrtChartInv are literal formulas (BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS/CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; PASS). Total sqrt/division semantics are explicit; inverse behavior is claimed only on its valid locus, and no fallback is exploited. Private qexSend is the literal linear coordinate projection; private qpcW is exactly dimensionlessPair at fixed α. q4_pairData is byte-identical after renaming. No new abbrev/structure; unchanged definitions retain the prior audit classification.

Mechanical checks: all five signed definition commands and all three theorem headers match the pinned signature bytes, including binder order; Defs is entirely unchanged from Round 2. Fresh renamed copies of the signed theorem declarations elaborate by direct exact applications (no draft signature import). Each rename commit was checked file-by-file: new bytes equal old bytes with only the specified whole-word substitutions; e4b37745: 4 files, 470d1de2: 7 files. All 139 public package declarations have distinct names; these names have zero external public leaf-name collisions in this checkout and zero against the 15 S8-Q files on current inp. No root shadow, forbidden escapes/options, EuclideanSpace, or provider/frozen-theorem import occurs in the package files. All 24 package files satisfy module headers; maximum length 463 lines, maximum Unicode line width 100, including the new files (Expansion 190, ChartAlgebra 175, PairChart 254).
Validation commands use LEAN_NUM_THREADS=1 and nice -n 5, strictly sequential for this audit; no clean/update/cache/full rebuild. `LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s84 KAM.Planetary.SecularForm.Quartic` exited 0: `[inp-gate] slot 1 acquired 20:49:24 for KAM.Planetary.SecularForm.Quartic`; `Build completed successfully (9180 jobs).` Warnings are unused-variable/tactic-linter suggestions, not errors or budget overrides.
`LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-s84-3-probe.lean` exited 0. It checks three copied literal signed types, W≡1 with nonzero constant, and #print axioms for all 103 public package theorems: every output is exactly `[propext, Classical.choice, Quot.sound]`, including quartic, quartic_pair_scaling, quartic_scaling, conversion_const, taylor_parts_of_invariant and quartic_pair_chart_conversion.
`LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Quartic KAM.Planetary.SecularForm.Quartic.Defs KAM.Planetary.SecularForm.Quartic.PairScaling KAM.Planetary.SecularForm.Quartic.PairAverage KAM.Planetary.SecularForm.Quartic.PairDecomp KAM.Planetary.SecularForm.Quartic.PairAnalytic KAM.Planetary.SecularForm.Quartic.Orthogonal KAM.Planetary.SecularForm.Quartic.Invariant KAM.Planetary.SecularForm.Quartic.PairSymmetry KAM.Planetary.SecularForm.Quartic.PairJet KAM.Planetary.SecularForm.Quartic.Coefficients KAM.Planetary.SecularForm.Quartic.Jet KAM.Planetary.SecularForm.Quartic.Taylor KAM.Planetary.SecularForm.Quartic.Swap KAM.Planetary.SecularForm.Quartic.Diagonal KAM.Planetary.SecularForm.Quartic.ScalingReal KAM.Planetary.SecularForm.Quartic.ScalingComplex KAM.Planetary.SecularForm.Quartic.ScalingTube KAM.Planetary.SecularForm.Quartic.ScalingEmb KAM.Planetary.SecularForm.Quartic.Scaling KAM.Planetary.SecularForm.Quartic.Conversion KAM.Planetary.SecularForm.Quartic.Expansion KAM.Planetary.SecularForm.Quartic.ChartAlgebra KAM.Planetary.SecularForm.Quartic.PairChart` exited **0**. Output: 24 `replaying KAM.Planetary.SecularForm.Quartic[.<module>]` lines, one for each listed module; includes Conversion, Expansion, ChartAlgebra, PairChart and facade; no errors.
`LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` exited **1 solely for the brief-permitted generated-root exception**. Complete output: `KAM.lean is out of date; run scripts/gen_root_imports.py`; `check_lean_modules: PASS (746 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. No substantive lint failure; generated files left untouched.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff 7fe32f2c HEAD --check` exits 0. Full `git diff inp...HEAD --check` exits 2 solely for Conversion:93 trailing whitespace, already present byte-for-byte at Round 2; no repair in this report-only audit. Final working-tree diff check and cleanup recorded below.
Scope/errata: no new pinned-source/blueprint defect. Carry existing E-P-CP11-2: printed “37 alpha^4 beta_4^(9)” needs alpha power three; no repaired-polynomial certificate or torsion determinant is certified here. Audit-1/2 N1 remains a provenance note: the exact historical “13:08 OVERNIGHT” ruling was not recovered; current design assigns S8-D to S8-4 (consumed through pairSlowSecular_diag_jet), S8-X to S8-Q. The garbled handoff's `secular D false` means the fixed model, whose pair-sum equality is proved; no false proposition. No mathematical deviation introduced. Memory was used only for audit workflow; package conclusions were freshly verified.
Closeout: all requested delta criteria pass, with the stated notes; no open F2 obligation. HEAD and the package digest were rechecked unchanged; inp advanced concurrently to `eedc66febf1e2749337a502351ab1515c1779c15`, with the same selected merge base and still-empty protected-path comparison. Auditor scratch/probe/log files removed. Final `git diff --check` exits 0; `git status --short` contains only `?? docs/tracks/P/audits/S8-4-audit-3.md`. Report: 92 lines; exact requested absolute destination. No source or manifest edited.
