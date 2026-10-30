# SO-BALLFIX handoff: SO-BALLDY's ball pass made compatible with sharp-v2 (owner ruling D39)

Branch `inp-soballfix`, base `7ffcd528` (inp with main's sharp-v2 `86089b36`) plus SO-BALLDY's three cherry-picked
commits (`5943a651`, `d22b9964`, `22f20b9c`, audit 1 PASS WITH NOTES). This package is one commit on top of
`22f20b9c`.

## 1. Root cause

Merged with main, the landing build failed in sharp-v2's `KAM/CertificateSharp/Ham/BallsTrig.lean` (SHARP-C3,
`ec06e801`). Two *proofs* there unfolded the body of the old `ballStep`. SO-BALLDY changed that body to
`ballForce (ballStepG slpBallPrec … (fun a => acc.getD a ballZero) op)`.

- `BallsTrig.lean:223` (`stepT_sound`, the `char` case): `plain (⟨0, 0⟩, WH.w ^ …) (by simp [ballStep])`.
  `simp [ballStep]` now leaves `ballForce (ballStepG … (.char k)) = some …`, because `ballStepG` and `ballForce`
  are not unfolded and `ballForce` carries the denominator test. The result was unsolved goals.
- `BallsTrig.lean:366` (`ballsAuxT_prefix_inv`, the `inv` case): `simp only [ballStep] at hr; split_ifs at hr with hlt`.
  The `if r < m` now sits inside `ballStepG`, under `ballForce` and a `match` on the operand ball, so `split_ifs`
  found no `if`.

Nothing else in sharp-v2 unfolds Ball.lean internals. BallsTrig does use the public `ballStep` (as a function),
`ballStep_sound`, `ballZero`, `BallRel`, `BallRel.ballRel_nil`, `BallRel.ballRel_snoc`, `toC_zero_rat`,
`inv_ball_bound`, `SlpInvGood` and `HamExpr.nonvanishingOn_of_inv_good`. All of these keep their audited
statements, and `ballsAux`'s shape is not used anywhere in sharp-v2. SplitBounds (`:209-210`) and HamClaim (`:61-63`)
reach `Slp.balls` only through `HamExpr.nonvanishingOn_of_balls` and `Slp.norm_val_le_slotMagQ`, whose
statements are unchanged, and they built without modification.

## 2. The delta against BALLDY's audited state (`git diff 22f20b9c`, Lean part)

### New helper lemmas in `KAM/Certificate/Expr/Ball.lean` (added after `ballForce_eq_some`; nothing else changed)

```lean
/-- Forcing a computed ball returns it. -/
theorem ballForce_some (b : CC ℚ × ℚ) : ballForce (some b) = some b := by
  have := b.2.den_pos
  simp only [ballForce]
  split_ifs with h
  · rfl
  · omega

/-- The ball of a character: `(0, w_H^{|k|₁})`. -/
theorem ballStep_char {n : ℕ} {WH : CertWeight} {centre radius : List ℚ} {taylorN : ℕ}
    (acc : List (CC ℚ × ℚ)) (k : CertKey) :
    ballStep n WH centre radius taylorN acc (.char k) =
      some (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum) := by
  simp only [ballStep, ballStepG]
  exact ballForce_some _
```

`ballStep_char` is the exact characterization the old proof obtained by `simp [ballStep]`. Characters are not
rounded, so the value is the old exact one. The `inv` case needs no new lemma: BALLDY's audited
`ballStep_inv_lt` (`Ball.lean:496`) states exactly the fact the old `split_ifs` extracted, in the
`(acc.map Prod.fst).getD a ballZero` shape BallsTrig uses.

### Proof-only changes in `KAM/CertificateSharp/Ham/BallsTrig.lean` (the whole diff against main)

```diff
-    · have := plain (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum) (by simp [ballStep])
+    · have := plain (⟨0, 0⟩, WH.w ^ (k.map Int.natAbs).sum) (ballStep_char _ k)
 …
-      simp only [ballStep] at hr
-      split_ifs at hr with hlt
+      have hlt := ballStep_inv_lt hr
```

### Header identity

- `git diff main -- KAM/CertificateSharp/Ham/BallsTrig.lean` is exactly the 3-line proof diff above: every
  declaration header, definition body and docstring of BallsTrig is byte-identical to main. No other sharp-v2
  file changed (`git diff --stat main -- KAM/CertificateSharp` lists only BallsTrig.lean).
- `git diff 22f20b9c -- KAM/Certificate/Expr/Ball.lean` is purely additive: 16 added lines, the two lemmas above,
  and no removed or modified line. Every BALLDY-audited header in Ball.lean is unchanged. BallRound.lean is
  untouched.
- No sharp-v2 *statement* asserts old exact values that the rounded evaluator breaks. One test,
  `toyCert2_trig_eq`/`toyCert3_trig_eq` (`CertificateSharp/Tests/BallsTrig.lean:34-44`), compares `ballsTrig`
  with `Slp.balls` by `decide +kernel`. Both go through the same rounded `ballStep`, and the test still passes
  (§4).

## 3. Item 3: which evaluator the sharp-v2 Hamiltonian checks use

| check | file:line | evaluator | BALLDY's rounding | BALLDY's reverse-cons pass |
|---|---|---|---|---|
| `checkHamBounds` (landed; `landedBase` in V2/Engine.lean:101) | Certificate/Defs.lean:238 | `Slp.balls` | yes | yes |
| `checkHamClaim` (route A refined, V2/RouteARefinedEngine.lean:35) | CertificateSharp/V2/HamClaim.lean:42 | `Slp.balls` | yes | yes |
| `checkHamBoundsSplit` | CertificateSharp/Ham/SplitBounds.lean:178 | `Slp.balls` | yes | yes |
| `checkHamBoundsTrig` (TrigCertifier.lean:29, V2/BaseTrig.lean:25) | CertificateSharp/Ham/SplitBounds.lean:164 | `ballsTrig` | ball part only | **no** |
| `checkHamBoundsTrigSplit` (V2/HamTrig.lean:29) | CertificateSharp/Ham/SplitBounds.lean:171 | `ballsTrig` | ball part only | **no** |

`TrigBound.lean` has no evaluator. It supplies only the scalar bounds `trigRad`, `expLoTrigQ` and `expNegUpQ`
and their lemmas.

`ballsTrig` (BallsTrig.lean:100-102) is its own pass, `ballsAuxT` (BallsTrig.lean:91-96). It is not an exact-ℚ
evaluator for the balls themselves: every non-trig slot ball comes from `stepT` (BallsTrig.lean:64-88). `stepT`
calls the rounded, forced `ballStep` (Ball.lean:206-209) on `acc.map Prod.fst`. So products, reciprocals and
exponentials are rounded to `slpBallPrec` bits there too. However, `ballsAuxT` keeps the structure that BALLDY
removed from `Slp.balls`, and it adds unrounded data:

1. **In-order `acc ++ [b]`** at every step (BallsTrig.lean:96): `O(L)` copying per op, `O(L²)` overall. BALLDY
   replaced this in `ballsAux` with `ballsRev` (cons plus one final reverse).
2. **`acc.map Prod.fst` rebuilt at every step** (BallsTrig.lean:71, 77, 82, 85, 88). This is a second `O(L)`
   list per op, and up to two `getD` walks per operand read (`stepT`'s shape reads plus `ballStep`'s `getD`).
3. **Unrounded, unforced shape scalars.** `mulShape` (BallsTrig.lean:42-46) stores `u * tbMag y`, and the `add`
   case stores `u + v` (BallsTrig.lean:78). These rationals are never rounded or forced. Along a chain of
   products of a character with other slots, their sizes grow like the exact-ℚ products did before BALLDY, and
   they are lazy thunks under kernel evaluation. The `trigRad` ball (BallsTrig.lean:80) is computed from them
   unrounded. The `char` slot (BallsTrig.lean:65) is not forced, but it is a single small rational.

**Conclusion:** the cosh-pass checks (`checkHamBoundsTrig`, `checkHamBoundsTrigSplit`) get BALLDY's rounding on
their slot balls but not its memory structure. They are exposed to the quadratic list copying and to the growth of
the shape scalars. I have not measured them on the lunar program (out of scope; their evaluators were not changed
here). If the lunar route uses the cosh pass, a follow-up package should give `ballsAuxT` the reverse-cons form
and round (outward, upwards for these magnitudes) and force the shape scalars. The route-A refined claim
(`checkHamClaim`) and the landed `checkHamBounds` are fully on BALLDY's evaluator.

## 3a. Python mirror evidence (correction to SO-BALLDY's handoff)

SO-BALLDY's handoff (`docs/tracks/SO/audits/SO-BALLDY-handoff.md`) claimed that the Python mirror matches the
Lean bit for bit. That claim was **stale**: it rested on the dump `.drafts/bd/xc/XL.out`, which matches the first
"round every slot" version of the pass and not the final rule (products, reciprocals and exponentials rounded;
constants, actions, characters and sums exact). SO-DATA3 step 1 found this. The current evidence is a fresh
`#eval` of the final `Slp.balls`. It matches the aligned mirror on all 887 lunar slots and on all 7 toy programs:
see `/mnt/HC_Volume_106379410/kam-data/so-data3/step1-xc/` (`XL2.lean`, `XL2.out`, `XC.out`, `mine.py`) and
branch `inp-sodata3` at `26d9b34c` (`scripts/spin_orbit/toy_arith.py`, "align the ball-pass mirror to SO-BALLDY's
rounded Slp.balls"). This package does not change the rounding rule. It changes no definition at all, so the
mirror evidence carries over unchanged.

## 4. Checks

All builds went through `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh`, one module at a time.
There were no errors and no `sorry` in any log. After the `if_pos` deprecation in the first draft of
`ballForce_some` was fixed, the logs show no warnings in Ball.lean or BallsTrig.lean.

```
KAM.Certificate.Expr.BallRound rc=0 Build completed successfully (2845 jobs).
KAM.Certificate.Expr.Ball rc=0 Build completed successfully (2951 jobs).
KAM.CertificateSharp.Ham.BallsTrig rc=0 Build completed successfully (3255 jobs).
KAM.CertificateSharp.Ham.SplitBounds	rc=0 Build completed successfully (3256 jobs).
KAM.CertificateSharp.Ham.TrigCertifier	rc=0 Build completed successfully (3324 jobs).
KAM.CertificateSharp.V2.BaseTrig	rc=0 Build completed successfully (3368 jobs).
KAM.CertificateSharp.V2.HamTrig	rc=0 Build completed successfully (3401 jobs).
KAM.CertificateSharp.V2.HamClaim	rc=0 Build completed successfully (3398 jobs).
KAM.CertificateSharp.V2.RouteARefinedEngine	rc=0 Build completed successfully (3506 jobs).
KAM.CertificateSharp.V2.Engine	rc=0 Build completed successfully (3364 jobs).
KAM.CertificateSharp.Tests.BallsTrig	rc=0 Build completed successfully (3335 jobs).
KAM.CertificateSharp.Tests.Corner	rc=0 Build completed successfully (3379 jobs).
KAM.CertificateSharp.Tests.Frame	rc=0 Build completed successfully (3381 jobs).
KAM.CertificateSharp.Tests.FreqTests	rc=0 Build completed successfully (3175 jobs).
KAM.CertificateSharp.Tests.Margin	rc=0 Build completed successfully (3348 jobs).
KAM.CertificateSharp.Tests.Shared	rc=0 Build completed successfully (3335 jobs).
KAM.CertificateSharp.Tests.Step0Coh	rc=0 Build completed successfully (3277 jobs).
KAM.CertificateSharp.V2.Tests.FrameFacts	rc=0 Build completed successfully (3515 jobs).
KAM.CertificateSharp.V2.Tests.Frozen	rc=0 Build completed successfully (3426 jobs).
KAM.CertificateSharp.V2.Tests.Refined	rc=0 Build completed successfully (3510 jobs).
KAM.CertificateSharp.V2.Tests.RefinedR1	rc=0 Build completed successfully (3505 jobs).
KAM.CertificateSharp.V2.Tests.TrigCombined	rc=0 Build completed successfully (3516 jobs).
KAM.CertificateSharp.V2.Tests.TrigFacts	rc=0 Build completed successfully (3409 jobs).
KAM.Certificate.Tests.Ball	rc=0 Build completed successfully (2952 jobs).
KAM.Certificate.Tests.ComplexExp	rc=0 Build completed successfully (2845 jobs).
KAM.Certificate.Tests.Compose	rc=0 Build completed successfully (2962 jobs).
KAM.Certificate.Tests.Defs	rc=0 Build completed successfully (3252 jobs).
KAM.Certificate.Tests.Gram	rc=0 Build completed successfully (2963 jobs).
KAM.Certificate.Tests.Model	rc=0 Build completed successfully (2916 jobs).
KAM.Certificate.Tests.Negative	rc=0 Build completed successfully (3252 jobs).
KAM.Certificate.Tests.Packed	rc=0 Build completed successfully (2915 jobs).
KAM.Certificate.Tests.Positivity	rc=0 Build completed successfully (2917 jobs).
KAM.Certificate.Tests.RatData	rc=0 Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Rat	rc=0 Build completed successfully (3254 jobs).
KAM.Certificate.Tests.Torsion	rc=0 Build completed successfully (2985 jobs).
KAM.Certificate.Tests.Toy2Data	rc=0 Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Toy2dData	rc=0 Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Toy2d	rc=0 Build completed successfully (3328 jobs).
KAM.Certificate.Tests.Toy2	rc=0 Build completed successfully (3326 jobs).
KAM.Certificate.Tests.Toy3Data	rc=0 Build completed successfully (3253 jobs).
KAM.Certificate.Tests.Toy3	rc=0 Build completed successfully (3323 jobs).
KAM.Certificate.Tests.ToyLit	rc=0 Build completed successfully (3252 jobs).
KAM.Certificate.Tests.Witness	rc=0 Build completed successfully (2920 jobs).
KAM.Certificate.Soundness	rc=0 Build completed successfully (3319 jobs).
KAM.CertificateSharp.Sound	rc=0 Build completed successfully (3363 jobs).
```

The modules that import BallsTrig, transitively (from a grep of the import graph): Ham.SplitBounds,
Ham.TrigCertifier, V2.BaseTrig, V2.HamTrig, Tests.BallsTrig, V2.Tests.FrameFacts, V2.Tests.TrigCombined and
V2.Tests.TrigFacts. All of them are in the list above, along with V2.HamClaim, V2.RouteARefinedEngine,
V2.Engine, every V2/Tests, CertificateSharp/Tests and Certificate/Tests module (the toys and Tests/Ball's
negative test included), Certificate.Soundness and CertificateSharp.Sound.

**Kernel replay** (`leanchecker --verbose`, toolchain v4.35.0, project LEAN_PATH, `ulimit -v` 40 GB):

```
leanchecker --verbose KAM.Certificate.Expr.BallRound KAM.Certificate.Expr.Ball \
  KAM.CertificateSharp.Ham.BallsTrig KAM.CertificateSharp.V2.Engine KAM.CertificateSharp.V2.RouteARefinedEngine
replaying KAM.CertificateSharp.V2.RouteARefinedEngine
replaying KAM.CertificateSharp.V2.Engine
replaying KAM.CertificateSharp.Ham.BallsTrig
replaying KAM.Certificate.Expr.Ball
replaying KAM.Certificate.Expr.BallRound
wall 80.22 s, peak 11127232 KB
rc=0
```

**Axioms** (`lake env lean` on a scratch file):

```
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.checkTorusCertificateSharp_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.checkTorusCertificateV2_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballForce_some' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.ballStep_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.mulShape_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.TRel.nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.TRel.length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.tb_fst_getD' depends on axioms: [propext, Quot.sound]
'KAM.CertificateSharp.getD_append_lt' depends on axioms: [propext]
'KAM.CertificateSharp.getD_append_ge' depends on axioms: [propext]
'KAM.CertificateSharp.TRel.snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.trig_add_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.stepT_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.val_mem_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.norm_val_le_slotMagQ_trig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.invGood_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.nonvanishingOn_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`getD_append_lt`/`getD_append_ge` (only `propext`), `tb_fst_getD` and `ballForce_some` (`propext`,
`Quot.sound`) are subsets of the standard three.

**Lint** (`sh scripts/lint_sources.sh`): rc=1. The only failure is `KAM.lean is out of date; run
scripts/gen_root_imports.py (KAM/Root/Certificate.lean)`, which predates this package (BallRound.lean from
BALLDY is not in the root). `check_lean_modules: PASS (1628 Lean files)`, `FROZEN-ANCHOR GUARD OK`,
`ABI HASHES OK (158 frozen declarations)`. No line over 100 columns. Ball.lean has 674 lines,
BallsTrig.lean 408.

**Short names** (`main_shortname_check.py` on Ball and BallsTrig): exit 7. The only hits are the existing
sharp-v2 names `TRel.length`, `TRel.nil` and `TRel.snoc` (see §5). The new names are clean.

## 5. Uncertainties and notes

- `main_shortname_check.py` on `KAM.Certificate.Expr.Ball` and `KAM.CertificateSharp.Ham.BallsTrig` reports
  `TRel.length`, `TRel.nil` and `TRel.snoc` in BallsTrig (their last components collide with Mathlib short
  names). These are sharp-v2's existing public names from main, and the brief forbids changing them. The two new
  names (`ballForce_some`, `ballStep_char`) are clean.
- `KAM.lean` is out of date: BallRound.lean (from BALLDY) is missing from `KAM/Root/Certificate.lean`. BALLDY
  already reported this, rule 10 bars me from editing it, and it should be regenerated with
  `scripts/gen_root_imports.py` on landing. It is the only failure of `scripts/lint_sources.sh`.
- No suspected errata in pinned sources. Deviations: none (proof-only changes plus two additive helper lemmas).

## 6. Audit focus

(1) The BallsTrig diff against main is proof-only (3 lines). No public header, body or docstring of any sharp-v2
file changed. (2) The Ball.lean diff against `22f20b9c` is purely additive (`ballForce_some`, `ballStep_char`),
so every BALLDY-audited header is unchanged. (3) `ballStep_char` states the unrounded character ball, which is
the value `ballStepG` gives. (4) The item-3 finding: the cosh pass `ballsTrig` keeps the `acc ++ [b]` /
`acc.map Prod.fst` structure and has unrounded shape scalars. (5) The mirror evidence is now SO-DATA3 step 1
(§3a), not BALLDY's stale `XL.out`.
