# Handoff LOCK-SQRT (track SO part 3, D45): the trusted primitive `HamExpr.sqrt`

Branch `inp-locksqrt`, base `13160166` (inp with BALLDY + BALLFIX). Design: SO-LOCK-DESIGN.md §4 (audit 3 PASS WITH NOTES).

## Files
New:
- `KAM/Certificate/Expr/Sqrt.lean` (168): `sqrtE` (total, `0` on the closed nonpositive real axis), `sqrtE_eq_exp`,
  `contDiffAt_sqrtE`, `differentiableAt_sqrtE`, `sqrtE_sq`, `sqrtE_ne_zero`, `sqrtE_re_nonneg`, `sqrtE_ofReal`,
  `hasDerivAt_sqrtE_of_mem`, `hasDerivAt_sqrtE`, `sqrtE_model_error`, `sqrtE_ball`.
- `KAM/Certificate/Expr/BallSqrt.lean` (106): `sqrtNewton`, `sqrtAnchor`, `ballSqrt`, `ballSqrt_lt_re`, `re_pos_of_ball`,
  `re_pos_of_mem_ballSqrt`, `ballSqrt_sound`.
- `KAM/Certificate/Expr/DiffCalculusSqrt.lean` (128): `JetSmoothOn.sqrtE`, `jetDeriv_sqrtE`, `jetDeriv2_sqrtE`, `jetDeriv3_sqrtE` (+ inverse helpers).
- `KAM/Certificate/Expr/DiffNodeSqrt.lean` (180): `slpSqrtNode` (emits `sqrt`, `inv`, w², w³, w⁵), `slpSqrtNode_sound`, `slpSqrtNode_emit_prefix`.
- `KAM/Certificate/Model/SqrtWitness.lean` (180): `SqrtWitness`, `sqrtWitnessRadius`, `sqrtWitness_sound`.
- `KAM/Certificate/Tests/Sqrt.lean` (181): tests (below).
Changed (landed): `Expr/Basic.lean` (constructor `sqrt` last; `eval`/`NonvanishingOn` arms; cases of `contDiffOn_eval`,
`eval_add_int`, `exists_real_eval`), `Expr/Slp.lean` (`SlpOp.sqrt`, step arm), `Expr/Ball.lean` (ball arm + soundness
case, `ballStep_sqrt_lt`, `ballsSpec/ballsAux_prefix_sqrt`, `SlpSqrtGood`, `Slp.sqrtGood_of_balls`, **the helper
exception** `nonvanishingOn_of_inv_good` → `nonvanishingOn_of_program_good`, proof edit of `nonvanishingOn_of_balls`),
`Expr/Diff.lean` (compiler arm, `nonvanishingOn_empty` and `slpCompile_sound` cases), `Expr/Compose.lean`
(`Witnesses.sqrtWit` field, `sqrt` arm and soundness case), `CertificateSharp/Ham/BallsTrig.lean` (`stepT_sound`
case, `ballsAuxT_prefix_sqrt`, `sqrtGood_of_ballsTrig`, proof edit of `nonvanishingOn_of_ballsTrig`),
`CertificateSharp/Kernel/Prune.lean` (`opDeps (.sqrt a) = [a]`, `sqrtWit` passed through `prune`).
Test literals (4th `Witnesses` field `[]`): Certificate/Tests/{Compose,Defs,Negative,RatData,Torsion,Toy2Data,Toy2dData,Toy3Data}.lean,
SpinOrbit/Tests/GraphCert.lean. Emitters: `scripts/spin_orbit/toy_lean_cert.py`, `scripts/sjs/kernel_probe_gen.py`
(mirror of Prune: opDeps arm, 4-field literal). DiffNode/DiffBuild/DiffCalculus/DiffCalculus3/ComposeModels/Sound/Ham untouched.
All files ≤ 778 lines.

## Approach
- §4.1/4.2 as designed. `exists_real_eval` gets one case via `sqrtE_ofReal`; `eval_real` unchanged.
- §4.3 `ballSqrt`: fails unless `r < re c`; anchor `s` = 9 rounded rational Newton steps (P bits); `R = |re c − s²| + |im c| + r`;
  checks `0 < s ∧ R < s²`; returns `ballRound P (s, R/s)`. Soundness from `sqrtE_ball`. Safety extraction: success ⇒ `r < re c`.
- §4.4 jets: node emits `V = sqrt x`, `w = V⁻¹`, `w²`, `w³`, `w⁵`; tables `½w x_i`, `½w x_ij − ¼w³x_i x_j`,
  `⅜w⁵x_ix_jx_k − ¼w³(cross) + ½w x_ijk`; the rules are proved from `hasDerivAt_sqrtE` and the existing inverse rules.
- §4.5 witness: checks `0 ≤ d < s`, `supBound(W − s) ≤ d`, `supBound(g − s²) < s²`, returns `supBound(g − W²)·(1/(s−d))↑`.
  `W·W` at product key `[3]` (config `forWitness 3 slot`), `−1·(W²)` by the scalar route.

## Contract / ABI check
**Revised after package audit 1 (F1).** The first receipt compared single-line abbreviated pretty-prints and missed four
test statements. Redone with `pp.all true`, `pp.oneline false`, `pp.fullNames true`: full elaborated types of every declaration
of the 16 touched modules (7 checker + 9 test), branch `a12b69cb` against `inp` (`/root/code/KAM-inp` build; `inp` has no change
under `KAM/Certificate`, `KAM/CertificateSharp`, `KAM/SpinOrbit/Tests` since base `13160166`). Result: 29 changed types, 1 removed declaration and
27 new declarations. The scratch files were deleted. The full list of changed or removed types:
- **`HamExpr.nonvanishingOn_of_inv_good`**: removed and replaced by `HamExpr.nonvanishingOn_of_program_good` (the sanctioned exception, with the exact designed statement).
- **Test statements, authorized by kam-inp-24, test-only migration:** `composeTest_noChar`, `composeTest_noExp`, `composeTest_noInv`, `composeTest_n2`
  (`KAM/Certificate/Tests/Compose.lean`). Each states a composition result for a `Witnesses` literal, which now carries the 4th field `[]` (`Witnesses.mk` arity).
  These are sqrt-free and their meaning is unchanged.
- Auto-generated only (from the new constructors / arms / field): `HamExpr.{rec,recOn,casesOn}`, `HamExpr.eval.{match_1,eq_def}`,
  `HamExpr.NonvanishingOn.{match_1,eq_def,eq_8}` (the eq lemmas were materialized in Tests.Torsion), `SlpOp.{rec,recOn,casesOn}`, `SlpOp.step.match_1`,
  `ballStepG.match_5`, `slpCompile.match_1`, `composeStep.match_7`, `opDeps.{match_1,eq_5}` (wildcard equation gains the `sqrt` exclusion),
  `Witnesses.{mk,mk.inj,mk.injEq,mk.noConfusion,mk.sizeOf_spec,rec,recOn,casesOn}`.
Apart from the four test theorems above, no hand-written theorem or definition changed type: `exists_real_eval`, `eval_real`, `contDiffOn_eval`, `nonvanishingOn_of_balls`, `nonvanishingOn_of_ballsTrig`,
`invGood_of_ballsTrig`, `slpCompile_sound`, `jet_*`, `Slp.compose_sound`, `composePruned_sound`, `ComposeState.slotsEnclose_nil` etc. are identical.
`checkHamBounds_sound`, `ham_structural`, V2 engine (Sound/Ham, V2/*) are untouched files and rebuild green.
Caller grep: `nonvanishingOn_of_inv_good` has no remaining reference in KAM/ (only historical audit docs).

## Checks
- Gate builds (one at a time): Sqrt, Slp/Basic, DiffCalculusSqrt, DiffNodeSqrt, Diff, Ball, SqrtWitness, Compose, Prune, BallsTrig, Tests.Sqrt.
- Downstream closure (91 modules depending on Basic/Slp or the edited tests), via its 18 leaves in one gate call:
  `Build completed successfully (3586 jobs).` (Tests.{Ball,Compose,Defs,Gram,Negative,Rat,Sqrt,Torsion}, CertificateSharp.Tests.{BallsTrig,Frame,Shared},
  V2.{BaseCorner,BaseTrig}, V2.Tests.{Refined,RefinedR1,TrigCombined}, SpinOrbit.LunarAssemblySharpGen, SpinOrbit.Tests.GraphCert). After that, one
  docstring line-wrap in Ball.lean; Ball rebuilt green (downstream oleans are stale only by that docstring).
  No warnings in new files; preexisting warnings only (Basic.lean:93 unused `hS` in `contDiffOn_eval`, which predates this change; PiHigh simp arg).
- `scripts/lint_sources.sh`: all checks pass (modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK (158 frozen)) except
  `KAM.lean is out of date; run scripts/gen_root_imports.py` — the 6 new modules need the generated root; rule 10 forbids me to edit it (orchestrator: regenerate).
- Tests (`decide +kernel`, all pass): `sqrtTest_ball` (centre within 1e-6 of 2, radius ≤ 1/100), `sqrtTest_ball_mem`, `_left_fails`, `_axis_fails`,
  `sqrtTest_anchor_small`; witness pass / opposite root `W = −2` rejected (audit F2 counterexample) / negative anchor rejected / `sqrtTest_witness_encloses` via `sqrtWitness_sound`;
  `sqrtTest_compose` (slot-keyed witness) and `_missing_witness` (none); `checkHamBounds` passes for `√I` with M = 2, fails with M = 1/4, and `½√(I⁴)` passes with M = 1000;
  `sqrtTest_nonvanishing` (NonvanishingOn derived through `nonvanishingOn_of_balls`, exercising the sqrt extraction); `√I` on a disc containing 0 fails closed.

## Axioms
`checkTorusCertificateV2_sound`, `nonvanishingOn_of_program_good`, `Slp.sqrtGood_of_balls`, `sqrtGood_of_ballsTrig`, `nonvanishingOn_of_ballsTrig`,
`nonvanishingOn_of_balls`, `ballSqrt_sound`, `sqrtE_ball`, `sqrtE_model_error`, `sqrtWitness_sound`, `slpSqrtNode_sound`, `slpCompile_sound`,
`exists_real_eval`, `Slp.compose_sound`, `Slp.composePruned_sound`, `checkHamBounds_sound`: all `[propext, Classical.choice, Quot.sound]`.

## Deviations from the design (please record)
1. **Sqrt witnesses keyed by slot number** (`sqrtWit : List (ℕ × SqrtWitness α) := []`, first match on `st.len`) instead of a counter.
   A counter field in `ComposeState` would change the landed statement `ComposeState.slotsEnclose_nil` (it mentions the state literal). Consequence:
   Prune needs no witness pruning (slots are never renumbered; dead witnesses are simply unread) — “aligned sqrt-witness pruning” is satisfied trivially.
2. **`Witnesses` arity**: the defaulted field does not help anonymous constructors (`⟨a, b, c⟩` errors), so every existing literal needs `, []`
   (9 in-repo Lean files and 2 Python emitters edited). Any out-of-repo generated data using 3-field `⟨…⟩` must add `, []`.
3. Jet: emits `inv` of the root and `w³`, `w⁵` slots rather than literally `.div f′ (.mul 2 (.sqrt f))`; mathematically the same rule, reuses the inv soundness.
   The `inv` operand is the root slot, whose ball (s, R/s) with R/s < s passes the inv test except in near-degenerate cases.
4. `ballSqrt` adds the explicit guard `r < re c` (design step 1) used for the safety extraction; `hasDerivAt_sqrtE_of_mem` (slit-plane version) added.
5. Witness product site `3` / key `[3]` chosen (not specified in the design); without advice for `[3]` the crude product enclosure is used (sound, loose) unless W is constant.

## Uncertainties / design signals
- Ball arithmetic of high-order sqrt derivatives is loose: for `½√(I⁴)` (exact third derivative 0) the bounds need M ≈ 10³ on |I − 1| < 1/10.
  LOCK-GEN should expect inflation of `D³` bounds when a sqrt operand is a long product; compile `√I` directly where possible.
- No heartbeat problems; no `set_option`.
- No lunar work done (COORDS-C separate). Python untrusted mirrors (`sofx_model.py`) do not yet know `sqrt`.

## Suspected errata
None in pinned sources. Design §4.1 wording "one new proof case each" for `eval_real` is (as audit 3 noted) inaccurate: `eval_real` needed no change — confirmed.

## Sub-orchestrator note (namespace)
The signatures file wraps all declarations in `namespace KAM.SpinOrbit.Lock`; the sqrt primitive and its lemmas
(`sqrtE`, `hasDerivAt_sqrtE`, `sqrtE_model_error`, `sqrtE_ball`, …) live in `KAM.Certificate` as checker
declarations (design §4.6 places them in checker files). Ruling (kam-inp-24): accepted as a namespace deviation; the
statements must otherwise match the signatures verbatim (auditor: check).

## Sqrt-free behaviour (requested by root-b8 for SO-DATA3)
Claim to verify in audit: for sqrt-free programs and certificates every checker function returns exactly the same
values as before (same Bool results, same slot balls), so the Python mirror stays bit-exact and existing data need
no value re-emission; only 3-field anonymous `Witnesses` literals need `, []` (named-field syntax works on both sides).
