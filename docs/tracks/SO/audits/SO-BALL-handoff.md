# SO-BALL prover handoff (branch inp-soball, c0e606b1; track SO package run by the main orchestrator)


## Files
- NEW `KAM/Certificate/Expr/Ball.lean` (~530 lines): `cexpHalvings`, `certCExpReduced_cexpHalvings_isSome`,
  `Slp.balls`, `Slp.val_mem_ball`, `HamExpr.nonvanishingOn_of_balls` (all with the signed types/names), plus helpers
  (`ballStep`, `ballsAux`, `BallRel`, `constBall`, `ballPiLo/Hi`, `inv_ball_bound`, `SlpInvGood`,
  `Slp.invGood_of_balls`, `slpInvNode_emit_prefix`, `HamExpr.nonvanishingOn_of_inv_good`).
- NEW `KAM/Certificate/Tests/ComplexExp.lean`: the five `cexpTest_*` (by `decide +kernel`).
- NEW `KAM/Certificate/Tests/Ball.lean`: ball test 11 (`ballTest_*`: exp 2, exp of cosine mode (radius > 1),
  cos of large action ball, div ok / div fails closed, `ballTest_weight`, and `ballTest_exp_const_mem` pairing a success with
  `Slp.val_mem_ball`).
- Branch note: `inp-soball` was off `inp-soexprb` and lacked SO-CEXP/SO-RAT; I merged `inp` into it (merge commit) first.

## Approach
- `Slp.balls` = left fold `ballsAux` mirroring `Slp.vals`, step `ballStep` in exact ℚ ball arithmetic via the generic
  `CertBall.plus/times` (so soundness reuses `mem_plus/mem_times`). Constants: `times` of the exact `(re,im)` ball and a ball of `(2π)^deg`
  from `piLoQ/piUpQ` (`ballPiLo/Hi`; `deg = 0` is exact). Action j: `(centre_j, radius_j)` for `j < n` else zero ball. Char k: `(0, w^{Σ|k_i|})`
  (via `norm_character_le_weight`, `one_le_w`, `sum_natAbs_certKeyFun_le`). exp: `certCExpReduced c r (cexpHalvings c r) taylorN`
  (`none` propagates). inv: needs `r < max |re| |im|`; centre `conj c/|c|²`, radius `r/((m-r)m)` (`inv_ball_bound`).
- `val_mem_ball`: invariant `BallRel` (slot values in balls) through the fold.
- `nonvanishingOn_of_balls`: success gives `SlpInvGood` on D (every `inv` operand slot nonzero on D, from the ball test + `val_mem_ball`);
  then induction on `e` through `slpCompile` (each `div` emits `.inv B.v` at slot `|rb|`, `slpInvNode_emit_prefix`), using `slpCompile_sound` on
  D for the denominator. No change to SO-EXPR files.
- Completeness: `2^s > 2(|re|+|im|+r)` from `Nat.lt_log2_self`; the exact-ℚ reduced ball has `normUp+radius = x/2^s ≤ 1`.

## Checks (exact output)
- `inp_lake_build.sh /root/code/KAM-inp-soball KAM.Certificate.Expr.Ball KAM.Certificate.Tests.ComplexExp KAM.Certificate.Tests.Ball`
  -> `Build completed successfully (2951 jobs).` No warnings in my files.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS (1311 Lean files)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144)`;
  only complaint `KAM.lean is out of date; run scripts/gen_root_imports.py` (generated; I did not touch it; orchestrator regenerates).
- No `sorry`/axiom/`native_decide`/`maxHeartbeats`/`EuclideanSpace`; lines ≤ 100.
- `#print axioms` of `certCExpReduced_cexpHalvings_isSome`, `Slp.val_mem_ball`, `HamExpr.nonvanishingOn_of_balls`,
  all `ballTest_*`/`cexpTest_*` checked: `[propext, Classical.choice, Quot.sound]` only.
- Kernel times (`set_option profiler`, type checking): each `cexpTest_*` and `ballTest_*` 150–280 ms; whole Tests/Ball and Tests/ComplexExp
  files elaborate in ~3.5 s / ~4.4 s including import loading.

## Uncertainties / notes
- `Slp.val_mem_ball` takes `hi : i < bs.length` as signed but does not need it (out-of-range slots hold the zero ball); kept for signature fidelity.
- Hypothesis `hW` (checkWeight) is used only for character slots.
- `inv` check requires strict `r < max |re| |im|` exactly as designed; ball radius inflates by the generic `times` bound (valid, not tight).
- Public short names introduced are all unique in KAM and Mathlib (grep'd); `testWeight` is in Tests/Ball.

## Suspected errata / deviations
- None in sources. Deviation: Ball tests live in their own module `Tests/Ball.lean` (not `Tests/ComplexExp`) so that `Tests/ComplexExp` depends only on Arith.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4, which repaired design audit 3 finding F10); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean section D (cexpHalvings, Slp.balls, Slp.val_mem_ball, HamExpr.nonvanishingOn_of_balls) and section J 'Range-reduction tests'. Check: every exp slot and compiled sin/cos goes through certCExpReduced and FAILS CLOSED on none (no caller-side size hypothesis anywhere); the ball soundness Slp.val_mem_ball holds on the whole certified domain; nonvanishingOn_of_balls proves NonvanishingOn for every divisor from the checked balls; the tests reduce by decide +kernel with false controls. Orchestrator rename: BallRel.nil/snoc -> BallRel.ballRel_nil/ballRel_snoc. The branch is stacked on inp-soexprb (landed) and merged inp.

AUDIT FOCUS: signed declarations match verbatim; soundness with no added premise; the slice complete. Audit ONLY KAM/Certificate/Expr/Ball.lean, KAM/Certificate/Tests/Ball.lean, KAM/Certificate/Tests/ComplexExp.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.

## Round 2 (prover repair, commit 527aead5)

Repair of audit F1 (docs/tracks/SO/audits/SO-BALL-audit-1.md): all signed tests unchanged; added soundness pairings.
- Tests/ComplexExp.lean: `cexpTest_zero_small_mem`, `cexpTest_two_reduced_mem`, `cexpTest_large_pin_mem` (via `certCExpReduced_sound`).
- Tests/Ball.lean: `ballTest_exp_cos_mode_mem`, `ballTest_cos_large_action_mem` (via `Slp.val_mem_ball`, as `ballTest_exp_const_mem`).
- Module docstrings updated. Short-name check: OK. Build of both modules through inp_lake_build.sh: success. lint_sources: only the known stale KAM.lean.
- `#print axioms` of all five new theorems: [propext, Classical.choice, Quot.sound].
- No errata, no deviations.
ROUND 2 FOCUS: is F1 closed (each of the three successful complex-exponential tests and the two remaining ball
scenarios now has a containment corollary of the exact value, through certCExpReduced_sound / Slp.val_mem_ball)? Are the
signed tests unchanged? Any new issue? Verdict.
