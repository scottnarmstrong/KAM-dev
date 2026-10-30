# SO-BALLDY handoff: rounded, forced, reverse-cons Hamiltonian ball pass (owner ruling D39)

Branch `inp-soballdy`:
- `1b72cf90`: the checker change. These are the only two Lean files touched, and this is the commit to cherry-pick.
- `440fed52`: the probes, logs and Python reference (`.drafts/bd/`).

Branch `inp-soballdy-oninp` (`df1db930`) is the same checker commit cherry-picked onto current `inp` (`3860bc48`).
It applied cleanly, because `Ball.lean`, `Sound/Ham.lean`, `Defs.lean` and `Arith/*` are identical on both bases.
It was used for the `CertificateSharp` checks (§5).

**Result.** `decide +kernel` of `checkHamBounds base` on the lower R1 torus now passes at the data's expOrder 30:
91 s, 8.98 GB peak. It also passes at expOrder 20 (91 s, 8.99 GB). Before, it ran out of memory at 10 GB at every
expOrder tried. All Certificate tests pass, and every signed statement is unchanged.

## 1. Files
- **new** `KAM/Certificate/Expr/BallRound.lean` (188 lines): dyadic outward rounding and the rounded exponential.
  - `slpBallPrec`, `ilog2Q`, `dyScale`, `dyDown`, `dyUp`, `ballRound`, `ballRound_mem(_aux)`.
  - The ℚ ball sum and product `plusQ`, `timesQ`, with `plusQ_eq` and `timesQ_eq`.
  - `ballSqIter`, `ballSqIter_mem`, `ballExp`, `ballExp_sound`.
- **changed** `KAM/Certificate/Expr/Ball.lean` (658 lines):
  - New bodies: `ballStep`, `ballsAux`, `Slp.balls` (its body is unchanged, `ballsAux … [] p.ops`).
  - New helpers: `ballStepG`, `ballForce`, `revGet`, `ballsRev`, `ballsSpec`.
  - New lemmas: `revGet_reverse`, `ballsRev_eq`, `ballsAux_eq_spec`, `ballForce_eq_some`, `ballStepG_sound`,
    `ballsSpec_sound`, `ballStep_inv_lt`, `ballsSpec_prefix_inv`.
  - Re-proved, with statements unchanged: `ballStep_sound`, `ballsAux_sound`, `ballsAux_prefix_inv`.
  - Untouched: `Slp.val_mem_ball`, `Slp.invGood_of_balls`, `HamExpr.nonvanishingOn_of_balls` (and everything after
    them), `cexpHalvings`, `certCExpReduced_cexpHalvings_isSome`, `constBall`, `BallRel`, …
- Not touched: `Defs.lean` (`checkHamBounds`, `hamBoundsOk`), `Sound/Ham.lean` (`checkHamBounds_sound` still
  consumes `ballsAux_sound … [] [] bs BallRel.ballRel_nil h` verbatim), `Arith/*`, Poly/Model files, the
  certificate format.
- `KAM.lean` is out of date and needs `public import KAM.Certificate.Expr.BallRound`. It was already out of date on
  this branch before my change (`Poly.Sparse` and the unlanded data modules), and rule 10 bars me from editing it.
  Please regenerate it with `scripts/gen_root_imports.py` on landing.

## 2. Approach, with value-preserving versus value-changing for each change

This section answers the mirror FYI from the main orchestrator.

| change | kind | justification |
|---|---|---|
| (a) slots kept in reverse order: `b :: racc` plus one final `List.reverse`; operand read with `revGet racc k a = if a < k then racc.getD (k-1-a) ballZero else ballZero` | **value-preserving** | `revGet_reverse : revGet acc.reverse acc.length = fun a => acc.getD a ballZero`, `ballsRev_eq`, `ballsAux_eq_spec : ballsAux … acc ops = ballsSpec … acc ops` (the in-order `acc ++ [b]` form) |
| (b) every operand ball read once (`match get a₁, get a₂ with \| (c₁, r₁), (c₂, r₂) => …`) | **value-preserving** | same rationals by definition |
| (c) `plusQ`/`timesQ` in place of `CertBall.plus`/`times` over ℚ (the backend error terms are identically 0 there) | **value-preserving** | `plusQ_eq`, `timesQ_eq` (equality in ℚ). This is exactly the formula of `toy_arith.b_plus`/`b_times`. |
| (d) `ballForce`: the step's ball is kept only if `0 < r.den + re.den + im.den` (always true) | **value-preserving** | `ballForce_eq_some`. It only makes the lazy kernel evaluate each slot when it is created. |
| (e) outward rounding of `mul` and `inv` balls, and inside `exp` (`ballExp`) | **value-changing** | rule below; soundness in §3 |

**Rounding rule (exact, for the mirror).** `P = slpBallPrec = 320`.
For a ball `((re, im), r)` with normalized rationals:

```
m   = |re| + |im| + r                                   (exact)
e   = log2(|m.num|) - log2(m.den)     with Nat.log2 (log2 0 = 0), so e = 0 when m = 0
k   = P - e                           (an integer, may be negative)
S   = 2^k                             (the rational 1 / 2^(-k) when k < 0)
re' = floor(re * S) / S
im' = floor(im * S) / S
r'  = ceil((r + (re - re') + (im - im')) * S) / S
ballRound((re, im), r) = ((re', im'), r')
```

Where the rounding is applied, per op:
- **Not rounded:** `const` (`constBall`), `action`, `char`, `add` (`plusQ`).
- **`mul`:** `ballRound(timesQ(a, b))`.
- **`inv`:** the old test and formula, then `ballRound`. The test is `r < max(|re|,|im|)`, done on the stored operand
  ball as before. The formula is `((re/d, -im/d), r/((m-r)m))` with `d = re² + im²`.
- **`exp`** (`ballExp`):
  1. `red = timesQ((z, r), ofRat(1/2^s))` with `s = cexpHalvings(z, r)` as before, and `certCExpSmall(red)` tested
     as before.
  2. `out = ballRound(certCExp(red.c, red.r, N))`, where `certCExp` is unchanged and exact.
  3. Repeat `s` times: `out = ballRound(timesQ(out, out))`.
  4. Return `out`. It is not rounded a second time.

A sum of rounded balls stays on the finer of the two grids, so its size grows by at most a bit plus the spread of
the exponents.

**Python reference.** `.drafts/bd/xc/ballround_ref.py` is the rule above on top of `toy_arith`; it is untrusted
tooling. It reproduces Lean's `Slp.balls` **bit for bit** on:
- T2d (156 ops, with `inv`);
- `exp (const 2)`, `exp (cosMode [1])`, `cos (action 0)` at `[20] [1/10]`, `sin (3·action 0)`;
- `div` (ok), and `div` with a denominator ball containing 0 (both give `none`);
- the lunar 887-op program (`.drafts/bd/xc/xc.py`, `xl.py`).

The mirror (`toy_arith.slp_balls`, used by `sofx_check.checkHamBounds`) must switch to it.

**Effect on the lunar bounds** (exact versus rounded, `xl.py`):

| bound | value | relative change | margin to M = 2.03 |
|---|---|---|---|
| ΣD H | 1.97995 | 1.2e-96 | 0.050 |
| \|∂H\| | 1.896 | 4.7e-97 | 0.134 |
| DX_H | 1.896 | 4.7e-97 | 0.134 |
| D²X_H | 1.56489 | 2.7e-96 | 0.465 |
| D²H | 2.02053 | 6.1e-97 | 0.0095 |

Largest number size on the lunar program: 854 bits exact, 349 bits rounded.

**Why the rounding is relative, not on a fixed grid.** A first version used a fixed absolute grid of `2^-320`. It
broke toy T2d: `checkHamBounds toyCert2d` became false, with D²X_H at 2.4e10 against M = 2.97. The slot
`x⁻⁴ ≈ 2^-398` (with `x = 10^30 + cos 2πq`) falls below that grid, and later products amplify the error by
`2^253 · 2^99`. Rounding to P significant bits of the ball's own magnitude fixes this: T2d's bounds equal the exact
ones to all printed digits.

**Why only `mul`, `inv` and `exp` are rounded.** Rounding every slot cost 9.67 GB on the lunar check; rounding only
these costs 8.98 GB.

## 3. Soundness of the value-changing part
- `ballRound_mem_aux`: for any `S > 0`, if `‖w − (re + i·im)‖ ≤ r` then `‖w − (re' + i·im')‖ ≤ r'`. The proof:
  - `re' ≤ re` and `im' ≤ im` (floor), so `|re − re'| + |im − im'| = (re − re') + (im − im')`.
  - The triangle inequality and `‖x + iy‖ ≤ |x| + |y|` give the bound before rounding the radius.
  - `ceil` rounds `r'` up.
- `dyScale_pos` gives `S > 0` for every `k : ℤ`. So containment holds whatever exponent `ilog2Q` returns, and
  `ilog2Q` only affects tightness.
- `ballSqIter_mem` and `ballExp_sound` follow `mem_certBallSquareIter` and `certCExpReduced_sound`, with
  `ballRound_mem` after each rounding and `timesQ_eq` rewriting to `CertBall.mem_times`.
- `ballStepG_sound`: `mul` and `inv` end with `ballRound_mem`. The `inv` exclusion test is unchanged and runs on the
  stored operand ball, so `ballStep_inv_lt`, `ballsSpec_prefix_inv`, `ballsAux_prefix_inv` and
  `Slp.invGood_of_balls` keep their meaning. A denominator ball containing 0 still fails closed (`ballTest_div_fails_closed`).
- **No new hypotheses:** the signed statements of `ballStep_sound`, `ballsAux_sound`, `ballsAux_prefix_inv`,
  `Slp.val_mem_ball`, `HamExpr.nonvanishingOn_of_balls` and `checkHamBounds_sound` are textually unchanged.

**Choice of P = 320.** The brief allowed "the certificate's precision field or a constant ≥ 200 bits". `Slp.balls`
has no precision argument and its signature is fixed, so P is a constant. 320 is the precision of the certificates'
fixed-point backend (`soPrecision = 320`). The relative error is about 1e-96 per rounded slot, against bound margins
of at least 1e-2 here (and thresholds around 1e-40 elsewhere in the certificate). The cost is insensitive to P: the
kernel's cost is per term, not per bit.

## 4. Kernel recursion depth
- `ballsRev` is tail recursive in the ops.
- `revGet` is `List.getD` (`get?Internal`, tail recursive).
- `ballForce` forces each slot as it is created, so evaluating a later slot forces at most its operands, which are
  already cached. There is no O(ops)-deep thunk chain.
- The slot counter `k + 1` is forced at the next `revGet` (`a < k`).
- No `foldr`, `map` or `++` over the slot list. `List.reverse` is tail recursive.
- No deep-recursion error was seen on the 887-op program.

## 5. Checks (exact commands and output)

**Kernel probes.** All run with `.drafts/bd/run.sh FILE`, which is `flock …/.kernel-probe.lock systemd-run --user
--scope -p MemoryMax=10G -p MemorySwapMax=0 /usr/bin/time … nice -n 5 lake env lean FILE`, one at a time.
"Peak" is the cgroup's anon memory, sampled each second.

| probe | what | result | wall | peak |
|---|---|---|---:|---:|
| `HB30.lean` | `checkHamBounds base = true` by `decide +kernel` (expOrder 30, the data's) | **pass** | 91 s | **8.98 GB** |
| `HB20.lean` | `checkHamBounds base20` (`{ base with expOrder := 20 }` as a def) | **pass** | 91 s | **8.99 GB** |
| before (SO-DATA-2, SO-EMITFIX `H12`, `H6`; old exact pass) | expOrder 30 / 12 / 6 | OOM | – | ≥ 10 / 10.0 / 10.1 GB |

Breakdown of where the memory goes:

| probe | what | wall | peak |
|---|---|---:|---:|
| `K0.lean` | spine of `base.ham.jet.prog.ops` only (length 887) | 54 s | 3.9 GB |
| `J0.lean` | every op of the compiled program forced (indices, constants), no balls | 59 s | **6.9 GB** |
| `Lk.lean` | J0 plus the reverse-list lookups (`revGet`) | 65 s | 7.46 GB |
| `X30.lean` | exact variant (same list and forcing, no rounding), full `hamBoundsOk` | 82 s | 8.2 GB |
| `B30.lean`, `HB30` (first version, rounding every slot) | – | 95 s | 9.39 GB, 9.67 GB |

Other notes:
- The lunar program is 887 ops: 204 const, 3 action, 14 char, 180 add, 486 mul, 0 exp, 0 inv (`P0.lean`). So
  `expOrder` does not affect this check, which is why 30 and 20 cost the same and 12 and 6 were not rerun.
- `decide +kernel` on `checkHamBounds { base with expOrder := 30 }` written inline fails in the *elaborator*
  ("deterministic timeout at isDefEq", the post-failure diagnostic). The kernel itself accepts that proposition via
  `addDecl` (`KH30.lean`: "kernel accepted", 93 s, 9.67 GB, first version). The certificate-as-a-def form `HB20`
  passes.

**Tests.** Each run separately through `inp_lake_build.sh` on the final code, all rc=0
(`.drafts/bd/tests2.log`): `KAM.Certificate.Tests.{Ball, ComplexExp, Compose, Defs, Gram, Model, Negative, Packed,
Positivity, Rat, Torsion, Witness, ToyLit, Toy2, Toy2d, Toy3}`.
- This includes `ballTest_div_fails_closed` (the denominator ball contains 0, so the balls are `none`) and the
  Negative toys.
- `Toy2d` failed with the absolute grid (§2) and passes with the relative rule.

**Sharp checks** (branch `inp-soballdy-oninp`, current `inp` plus the checker commit):
- `inp_lake_build.sh … KAM.CertificateSharp.Sound KAM.CertificateSharp.Tests.Margin KAM.Certificate.Soundness
  KAM.Certificate.Tests.Ball KAM.Certificate.Tests.Negative`: rc=0 (211 s). `CertificateSharp/Tests/Margin.lean`
  is the only file under `CertificateSharp/Tests`.
- `… KAM.Certificate.Tests.Toy2d KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Toy2`: success.
- `sh scripts/lint_sources.sh` there, after building the frozen anchors so the ABI step can load them:
  - `check_lean_modules: PASS (1465 Lean files)`; FROZEN-ANCHOR GUARD OK; ABI HASHES OK (146 frozen declarations);
  - "KAM.lean is out of date": the only diff against `gen_root_imports.py` is
    `+ public import KAM.Certificate.Expr.BallRound`.

**Builds.** `inp_lake_build.sh … KAM.Certificate.Expr.BallRound KAM.Certificate.Expr.Ball KAM.Certificate.Soundness
KAM.Certificate.Sound.Ham KAM.SpinOrbit.Data.Lower.Cert`: success, with no warnings in my files.

**Lint.** `sh scripts/lint_sources.sh`:
- frozen-anchor guard OK; ABI hashes OK (144 frozen declarations);
- `check_lean_modules: FAIL` only for "KAM.lean is out of date" (see §1);
- 21 "not a module" lines, all scratch probes under `.drafts/` (`.drafts/s1`, `.drafts/ef`, and my `.drafts/bd`
  probes, which are plain scripts as in SO-EMITFIX).

**Other.**
- Every line is at most 100 columns.
- `main_shortname_check.py /root/code/KAM-inp-soballdy KAM.Certificate.Expr.BallRound KAM.Certificate.Expr.Ball`:
  "short-name check OK (no reused public short name)".
- No `maxHeartbeats` and no `maxRecDepth` anywhere.

## 6. `#print axioms`
On `inp-soballdy` (`.drafts/bd/AX.lean`), each of the following depends on `[propext, Classical.choice,
Quot.sound]`:
- `checkHamBounds_sound`
- `checkTorusCertificate_sound`
- `HamExpr.nonvanishingOn_of_balls`
- `ballsAux_sound`
- `Slp.val_mem_ball`

On `inp-soballdy-oninp`, each of the following depends on `[propext, Classical.choice, Quot.sound]`:
- `KAM.CertificateSharp.checkTorusCertificateSharp_sound`
- `checkHamBounds_sound`
- `checkTorusCertificate_sound`

## 7. Uncertainties and design signals
- **The jet program dominates the memory, not the balls.**
  - Forcing the compiled 887-op program (`HamExpr.jet` via `slpCompile` and the Diff* compilers) costs 6.9 GB and
    59 s of the 8.98 GB.
  - The ball pass itself now adds about 2.1 GB, of which about 0.56 GB is the O(slot) list lookups.
  - The margin under the 10 GB cap is about 1 GB.
  - If the N = 65 data keep the same Hamiltonian, the program is the same. The Hamiltonian program does not depend
    on N, so I expect the same cost.
  - Further headroom would come from the jet compiler's kernel evaluation (not my files, SO-KDEPTH's area) or from
    a log-depth slot store in place of the list (a possible follow-up of about 0.5 GB).
- The `{ c with … }`-inline elaborator failure (§5) is a quirk worth knowing for the assembly: state each
  sub-check on a named def.
- I did not measure the old pass at expOrder 20; the "before" column is SO-EMITFIX's and SO-DATA-2's.

## 8. Errata and deviations
- No suspected errata in pinned sources.
- Deviations:
  1. The rounding is relative (P significant bits), not the brief's fixed grid `2^-P`. A fixed grid is sound but
     broke toy T2d (§2).
  2. Constants, actions, characters and sums are not rounded. This keeps the containment contract and lowers the
     kernel cost; the brief said "every slot ball".
  3. Both are value-changing for the Python mirror; the exact rule is in §2.

Landing branch note (orchestrator): this worktree is branch inp-soballdy-oninp (the checker commit 1b72cf90 cherry-picked onto inp as df1db930, then inp merged in); it contains only KAM/Certificate/Expr/{Ball,BallRound}.lean changes against inp. Measurements were taken on inp-soballdy with the R1 data.

AUDIT FOCUS (owner ruling D39: implementation change, statements unchanged): (1) no signed statement changed: every public declaration of Expr/Ball.lean present on inp keeps its exact header (in particular Slp.balls, ballStep_sound, ballsAux_sound, ballsAux_prefix_inv, Slp.val_mem_ball, Slp.invGood_of_balls, HamExpr.nonvanishingOn_of_balls), and checkHamBounds_sound in Sound/Ham.lean still compiles unchanged; (2) SOUNDNESS of the value-changing outward rounding: ballRound_mem (the exact value stays inside the rounded ball for every input, including negative k, m = 0, huge or tiny balls), ballExp_sound, and the inv test still guarding division; (3) the value-preserving changes really preserve values (revGet_reverse, ballsRev_eq, plusQ_eq, timesQ_eq, ballForce_eq_some); (4) kernel friendliness: no O(length)-deep recursion introduced; (5) the documented rounding rule in the handoff matches the Lean exactly (the mirror will be built from it); (6) tests (Tests/*, the toys, CertificateSharp), kernel replay, axioms of checkHamBounds_sound, checkTorusCertificate_sound, checkTorusCertificateSharp_sound.
