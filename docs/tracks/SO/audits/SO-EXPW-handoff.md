# SO-EXPW prover handoff (branch inp-soexpw, 472c97b8; track SO package run by the main orchestrator)


Branch `inp-soexpw`, which is off `inp-somalg` at b0ac8009. Commits 55f83ae1..472c97b8. Every edit is committed. `KAM.lean` is not
touched: it is generated and the orchestrator regenerates it.

## Files (all new; 1301 lines in total, every file under 500 lines)

- `KAM/Certificate/Model/ExpBounds.lean` (330 lines): scalar tools.
  - `CertBall.sumPairs/sumRounds/foldSum/listSum` are balanced ball sums (64 pairwise rounds, then a fold).
  - `CertPoly.coeffSumBall` with `CertPoly.mem_coeffSumBall`: the ball encloses `P(0) = Σ c_k`.
  - `CC.negC`, `CC.toC_negC`, `CertPoly.negP`, `CertPoly.eval_negP`, `CertModel.mul_deg`.
  - `expm1Up s N x`: a backend upper bound of `exp x − 1`. `expSeriesUp`, `expm1SqIter` and
    `expm1Up_sound` support it.
- `KAM/Certificate/Model/Exp.lean` (487 lines):
  - signed: `ExpWitness`, `expPinBall`, `expPinBall_sound`, `expWitnessRadius`, `expWitnessRadius_pin`,
    `expWitness_sound`;
  - helpers: `expPinErr`, `expResidualProduct`, `expResidualUp`, `expWitnessRadiusOf`, `norm_sub_le_expPinErr`,
    `CertPoly.fderiv_eval_single`, `norm_errTermsEval_add_le`, `norm_le_expResidualUp`, `norm_clm_le_sum_single`,
    `norm_exp_sub_one_le_exp_norm`, `exists_int_translate`, `norm_exp_sub_witness_le` (the analytic core) and
    `expWitnessRadiusOf_sound`.
- `KAM/Certificate/Model/Inv.lean` (300 lines):
  - signed: `invWitnessRadius`, `invWitness_sound`;
  - helpers: `isZeroKey`, `oneSubSupUp`, `recipBoundAux`, `recipOneSubUp`, `certKeyFun_eq_zero_of_isZeroKey`,
    `CertPoly.eval_filter_add`, `CertPoly.eval_zeroKeys`, `norm_one_sub_le_oneSubSupUp`, `recipBoundAux_ge` and
    `recipOneSubUp_ge`.
- `KAM/Certificate/Tests/Witness.lean` (184 lines): `decide +kernel` tests and contract instances. They are listed
  under Checks.

## Signed declarations (statements verbatim; SOSignatures.lean §C, lines ~574–618)

- `ExpWitness`, `expPinBall`, `expPinBall_sound`, `expWitnessRadius`, `expWitnessRadius_pin`, `expWitness_sound`,
  `invWitnessRadius` and `invWitness_sound` are all proved or defined.
- Verbatim check: a scratch file pasted each signed statement from SOSignatures.lean under the name `sigcheck_<name>`.
  - Theorems are closed by `apply <name> <;> assumption`.
  - Defs are `:= <name> args`, which checks their types.
  - Everything elaborated with no error.
- No bodies use `sorry` or well-founded recursion. Every recursion is structural (`List`/`ℕ`).

## Approach

**Exp witness.**
- `g = (deg 0) g₀ + T` with `|T| ≤ η`.
- `B := |g₀|_w`, the balanced weighted norm `supNormUp`.
- The analytic core is `norm_exp_sub_witness_le`, with `F = E·exp(−g₀)`:
  - `F` is periodic (`eval_add_int`);
  - `∂_j F = exp(−g₀)(∂_j E − (∂_j g₀)E)`, and the operator norm is at most `Σ_j |∂_j F|` (`norm_clm_le_sum_single`);
  - every strip point is an integer translate of a point with `‖θ'‖ ≤ 1/2 + ρ` (`round`, `exists_int_translate`);
  - the mean value inequality on the convex strip (`convex_complexStrip`) then gives
    `|F − 1| ≤ e^B(ε₀ + (1/2+ρ)Σ r_j)`;
  - since `exp g₀ − E = exp(g₀)(1 − F)`, this yields `|exp g₀ − E| ≤ e^{2B}(ε₀ + (1/2+ρ)Σ r_j)`.
- The other half is `|exp g − exp g₀| ≤ e^B(e^η − 1)`, using Mathlib's `norm_exp_sub_sum_le_exp_norm_sub_sum` with
  `n = 1` and `Complex.norm_exp_le_exp_norm`.
- Radius: `upAdd (upMul (eB·eB) (upAdd ε₀ (upMul (1/2+ρ)↑ Σr_j))) (upMul eB mη)`, where `eB = 1 + expm1Up(B)` and
  `mη = expm1Up(η)`.

**Pin (F10).**
- `out := certCExpReduced (expPinBall g) E.pinHalvings E.pinOrder`; `none` ⇒ `none`.
- `ε₀ := upAdd (|D.c|↑) D.r` with `D := CertBall.plus (coeffSumBall E) (−out)`. This is `|E(0) − out.1|↑ + out.2`
  plus the rounding of `E(0)` and of the subtraction.
- `expWitnessRadius_pin` follows from `certCExpReduced_sound` and `expPinBall_sound`.
- Nothing assumes `g₀(0)` is small. The tests include a pin of `exp 3` that fails with 0 halvings and passes with 2.

**Residual, fused (`expResidualUp`).**
- The terms of `∂_jE/2π` (`derivItem`) are merged (`mergeErrTerms`) with the product terms of `(∂_j g₀/2π)·(−E)`.
  The product comes from `CertModel.polyProduct` at key `[1, j]`; the direct product is used if the advice is
  missing or fails.
- The merged list is bounded in ONE weighted pass `Σ (|c|+e) w^{|k|}`. The bound adds the product error and
  `errRadius(∂_j g₀ items)·|E|_w`, and is multiplied by `2·piUpQ ≥ 2π`.
- `|E|_w` is computed once for all directions.

**Reciprocal witness.**
- `u := CertModel.mul W cfg [2] ⟨0,Q,0⟩ ⟨0,b.poly,b.rad⟩`, which encloses `Q·(b/(2π)^d)`.
- `δ := oneSubSupUp W u` is the sum of:
  - `|1 − Σ zero-key coefficients|↑` (ball sum);
  - the weighted norm of the other terms;
  - `u.rad`.
  It does not depend on how the keys are represented.
- If `blt δ 1` passes, `t ≥ 1/(1−δ)` comes from `recipOneSubUp`. The interface has no division, so it uses
  `1/(1−δ) = Π_{i<k}(1+δ^{2^i})/(1−δ^{2^k})`; once `2x ≤ 1`, the last factor is bounded by `1 + 2x`. For a tiny `δ` this
  is one step with `t = 1 + 2δ`.
- Radius: `|Q|_w·δ·t`.
- Soundness: `|1 − u| ≤ δ < 1` ⇒ `u ≠ 0` ⇒ `b ≠ 0`, and `1/b − (2π)^{−d}Q = (2π)^{−d}·Q(1−u)/u`.

## Checks (exact output)

- **Gate build:** `inp_lake_build.sh /root/code/KAM-inp-soexpw KAM.Certificate.Model.ExpBounds KAM.Certificate.Model.Exp KAM.Certificate.Model.Inv KAM.Certificate.Tests.Witness`
  ```
  ✔ [2916/2919] Built KAM.Certificate.Model.ExpBounds (2.2s)
  ✔ [2917/2919] Built KAM.Certificate.Model.Inv (2.7s)
  ✔ [2918/2919] Built KAM.Certificate.Model.Exp (3.2s)
  ✔ [2919/2919] Built KAM.Certificate.Tests.Witness (5.1s)
  Build completed successfully (2919 jobs).
  ```
  My files produce no warnings. The only warning in the log is the pre-existing one at `Arith/PiHigh.lean:218`.
- **Lint:** `sh scripts/lint_sources.sh`
  ```
  KAM.lean is out of date; run scripts/gen_root_imports.py
  check_lean_modules: PASS (1350 Lean files, 0 comparator configurations)
  FROZEN-ANCHOR GUARD OK
  ABI HASHES OK (144 frozen declarations)
  ```
  The only failure is the generated root, which needs four new modules. I may not edit it, so the orchestrator
  regenerates it.
- **Short-name check:** `main_shortname_check.py … ExpBounds Exp Inv Tests.Witness` → `short-name check OK (no reused
  public short name)`.
  - The first run flagged `CertBall.pairRounds` (renamed to `sumRounds`) and `norm_exp_le_exp_norm` (now Mathlib's).
- **Line widths:** every line is at most 100 characters.
- **Forbidden tokens:** no `sorry`, `native_decide`, `ofReduceBool`, `maxHeartbeats` or `EuclideanSpace`.
  - One linter option is used: `set_option linter.unusedVariables false in` on `invWitnessRadius`. The signed
    argument `n` is unused because the reciprocal check does not depend on the dimension.
- **`#print axioms`:** `expPinBall_sound`, `expWitnessRadius_pin`, `expWitness_sound`, `invWitness_sound`,
  `expm1Up_sound`, `recipOneSubUp_ge` and `witnessTest_exp_fixed` all give `[propext, Classical.choice, Quot.sound]`.
- **Tests (`Tests/Witness.lean`, every check `decide +kernel`):**
  - Scalar bounds:
    - `expm1Up 3 8 1 ∈ [1.718281828, 1.718281829]`;
    - `expm1Up 0 8 2 = none`;
    - `recipOneSubUp 0.9 ≥ 10`;
    - `recipOneSubUp 1 = none`.
  - Exp witness, ℚ, n = 1, Bessel witness of `exp(0.2 cos)`:
    - radius ≤ 1e-4 (measured 8.3e-6);
    - the witness `E = 1` gives radius > 0.1;
    - the pin `exp 3` gives `none` with `pinHalvings = 0`, and radius ≤ 1e-6 with `pinHalvings = 2` and order 20;
    - `cfg.halvings = 0` with `B = 3` gives `none`.
  - Reciprocal witness, `1/(2 + 0.5 cos)`:
    - radius ≤ 1e-4 (measured 1.15e-5);
    - an exact constant reciprocal gives `some 0`;
    - `Q = 0` gives `none`.
  - Fixed point (`CertFixed 128`, n = 2, 289-term witness; the kernel computes the coefficients): radius ≤ 2^-38. The
    radius lies between 2^-44 and 2^-38, and the residual is truncation-dominated, as expected.
  - Contract instances: `witnessTest_exp_encloses` and `witnessTest_inv_encloses`.

## Kernel timings (single thread, `lake env lean` on scratch files, import baseline subtracted)

| Case | Kernel time |
|---|---|
| ℚ exp toy (n = 1, 9 terms) | 0.32 s |
| ℚ reciprocal toy | 0.47 s |
| `expm1Up 40 20` on `CertFixed 320` (40 halvings, order 20) | 0.47 s |
| `CertFixed 128`, n = 2, 289-term `E`: full `expWitnessRadius` | ≈ 3.2 s |
| same, one direction of `expResidualUp` | ≈ 1.6 s |
| same, `|E|_w` (289 weights) | ≈ 0.9 s |
| same, pin and real bounds | ≈ 0.1 s |

- The 1.6 s per direction is about 5 ms per term.
- The first version (residual via `CertModel.add/mul` and `supUp`) took ≈ 7 s (≈ 3.5 s per direction), because about
  1,470 weight evaluations at ≈ 2.4 ms each dominated it. The fused pass removed about two thirds of them.
- `Tests/Witness` builds in 5.1 s in total.

## Deviations (implementation choices; no signed statement changed)

1. **The real factors `exp(B)`, `exp(2B)` and `exp(η) − 1` use the backend upward bound `expm1Up`, not `ratExpUp`.**
   - Design §1.7 / F10 says the factors "stay on `ratExpUp`". But `B = |g₀|_w` and `η = g.rad` are backend values,
     `ratExpUp` is ℚ → ℚ, and `CertArith` has no law-free α → ℚ conversion. Feeding it would mean trusting data or
     searching by comparisons.
   - `ratExpUp`'s ℚ squarings would also blow up denominators on 318-bit inputs.
   - `expm1Up` uses the same parameters (`cfg.halvings`, `cfg.taylorN`) and the same Taylor bound (`Real.exp_bound'`).
     It squares with `z ↦ z(2+z)`, so there is no cancellation in `e^η − 1 ≈ η`.
   - It **fails closed** (`none`) when the halved argument is above `1` or `N = 0`, instead of falling back to
     `3^⌈q⌉`. Generators must choose `cfg.halvings ≥ log₂ max(B, η)`.
   - `exp(2B) := exp(B)²`.
2. **Residual.**
   - The residual is the fused bound described above, not a `CertModel.add/mul` pipeline.
   - It applies no cutoff: a sup bound needs no truncation.
   - On missing or failed advice it uses the direct product, which is sound but costly, instead of the crude
     enclosure. A certificate that supplies the advice never reaches it.
   - The advice operands are the same as in the design reading: the polynomial of `∂_j g₀` items
     (`itemsPoly (g₀.terms.filterMap (derivItem j))`) times `E.negP`.
3. **Product keys.**
   - Exp residual of direction `j`: `[1, j]`. Reciprocal product: `[2]`.
   - The signed functions take no witness index, so keys of different witnesses on the same `cfg.advice` would
     collide. **SO-EMB must give each witness its own `ModelConfig`/advice book**, or the design must add an index.
     This is flagged for SO-EMB and SO-DATA.
4. **`recipOneSubUp` runs at most 64 squarings.**
   - The design says `none` only when `δ < 1` fails. Here the check also returns `none` when `δ` is so close to `1`
     that `δ^{2^64}` (rounded upward) stays above `1/2`, that is `δ ≳ 1 − 2^{−64}`.
   - Production `δ` is tiny.
5. **`ε₀` contains the rounding of the ball sum of `E(0)`.** The design wording is "rounded difference plus its
   rounding"; the content is the same.

## Uncertainties and design signals

- No heartbeat problems. Every proof elaborates at the default settings, and every file builds in at most 5 s.
- The kernel cost per witness term is ≈ 5 ms per direction on `CertFixed 128`. Weights dominate it (SO-MALG design
  signal 1).
  - For a full 8.5k-term `E` with n = 2, the estimate is ≈ 110 s of kernel per exp witness (2 × 8.5k × 5 ms, plus ≈ 25 s for `|E|_w`).
  - SO-MALG's lever (b), a weight table by degree, would cut this directly. It lives in `Model/Terms`, not here.
- Several bounds in the scalar tools, the residual and the reciprocal reuse let-shared backend values (`eB`, `|E|_w`,
  the squaring iterates). They rely on the kernel's whnf cache for shared subterms.
  - Measured: 40 squarings on `CertFixed 320` cost 0.47 s, so there is no exponential re-evaluation.
- Generators: `cfg.cutoff` does not affect the exp residual, but it still truncates the reciprocal product `u`
  (SO-MALG signal 3: `cutoff = 0` keeps only the constant term).

## Suspected errata

None in the pinned sources. The signed statements were provable as stated, with no extra hypotheses.

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §7 row SO-EXPW and Revision 4 (design audit 3 F10: every exponential pin goes through certCExpReduced and fails closed; the halving count is certificate data; the epsilon_0 budget includes reduction, rounding and squaring errors); signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean lines ~576-620 (ExpWitness, expWitnessRadius, expWitnessRadius_pin, expWitness_sound, invWitnessRadius, invWitness_sound). Built on SO-MALG (landed) and SO-CEXP (landed).

AUDIT FOCUS: (1) signed declarations verbatim; (2) expWitness_sound and invWitness_sound hold for EVERY certificate-supplied witness (no trust in the data) with no added premise; the pin path fails closed when certCExpReduced returns none; every error contribution is paid; (3) the one 'set_option linter.unusedVariables false in' on invWitnessRadius is a linter option only (no resource override) and is justified by the signed unused argument; (4) tests reduce by decide +kernel with false controls; (5) hygiene. Audit ONLY KAM/Certificate/Model/{Exp,ExpBounds,Inv}.lean and KAM/Certificate/Tests/Witness.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
