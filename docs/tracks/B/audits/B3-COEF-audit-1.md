# B3-COEF audit 1 (refute-first, independent)

- Package: B3-COEF (track B, OD-B17): coefficient-generic Cartesian polynomial layer (`CertCoeff K`, instances
  `ℚ` and `QSqrt2`).
- Branch `inp-b3coef`, audited commit `bb1a23077` (code commit `b96786d6b`); merge base with `inp`
  `2a104f734`; `inp` tip at audit time `ab5d5aed4`.
- Prover handoff: `docs/tracks/B/audits/B3-COEF-handoff.md`. Brief: `inp-audit-package.md` + the handoff's AUDIT FOCUS.
- The package proves **no frozen anchor** and adds no provider, so the provider = frozen-type check (brief item 1)
  does not apply. The relevant check is preservation of the ℚ API that the downstream track-B stack consumes.

## Verdict: **PASS WITH NOTES**

There are no blocking findings. The notes (N1–N5 below) cover source-level API surface and documentation only. None
changes a statement's meaning.

## 1. ℚ API preservation (focus 1)

**Names.** I extracted every top-level `theorem/def/abbrev/structure/instance` from the five `inp` versions of
`Poly/{Basic,Deriv,Bracket,Bound,Lie}.lean` (135 declarations). All 135 exist on HEAD. The monomial-level ones
moved from namespace `CartMono` to `CartMonoK` (see N1).

**Statements.** I wrote an untracked probe, `.lake/abi-scratch/AbiOld.lean`, that restates **all 97 old theorems**
verbatim from the `inp` text. The restatement keeps the old `variable` lines (`[Algebra ℚ R]`, `[RCLike 𝕜]`, …) and
the `omit … in`/`variable … in` prefixes, with `CartPoly`/`CartMono` as the types. I made two mechanical rewrites:
`CartMono.x` → `CartMonoK.x`, and `X.cartEval` → `cartEval X` (see N2). Each restatement is proved only by
`exact @new ..` or `apply new <;> assumption`. Those tactics close a goal only when the new lemma at `K = ℚ`
unifies with the old statement, including the old `[Algebra ℚ R]` instance binders.

```
LEAN_NUM_THREADS=1 systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 \
  lake env lean .lake/abi-scratch/AbiOld.lean      → 0 errors, exit 0 (97/97 theorems)
```

So at `K = ℚ` every old statement is definitionally the new one, under Mathlib's own `Algebra ℚ R`.

**Downstream.** `git diff inp...HEAD` touches only `KAM/EffectiveStability/Poly{.lean,/*}` and the handoff. No
downstream module was edited. 38 modules depend on Poly. I built their 7 leaves (`OscillatorChain.Smoke`,
`OscillatorChainCheck`, `OscillatorChainPhysicalSmoke`, `OscillatorPhysicalSmoke`, `TorusChainCheck`,
`TorusChainPhysicalSmoke`, `TorusPhysicalSmoke`) through the compile gate: `Build completed successfully (3023 jobs)`.

**Sealed track-B anchors on `inp`.** Track B was frozen and sealed (D72) on `inp` after the merge base. The sealed
anchors are `torus_confinement` and `oscillator_confinement`, and their providers import `TorusProof` and
`OscillatorProof`. Neither proof module imports Poly, and the frozen statements do not mention `CartPoly`. The two
branches change disjoint files, and `git merge-tree --write-tree inp HEAD` merges cleanly. The package therefore
does not touch any sealed proof.

## 2. Declaration table

| Node / item | Lean declaration | Verdict | Note |
|---|---|---|---|
| OD-B17 class | `CertCoeff K` | PASS | All fields are proved data (no hard step bundled as an assumption). `toReal`/`toComplex` are ring homs, `toComplex_eq` and `toReal_ofRat` are compatibility laws, and `abs_toReal_le` is the majorant property. |
| decidability | `certCoeffDecEq` (prio 900) | PASS | At ℚ it is `with_reducible_and_instances rfl` to Mathlib's `DecidableEq ℚ` (probe). |
| norm class | `CertNormLe K 𝕜` | PASS | A Prop class tied to the given `Algebra K 𝕜`, so no wrong algebra can pair with a bound. |
| ℚ instance | `instCertCoeffRat` (`@[default_instance]`) | PASS (N3) | `toCommRing` is `with_reducible_and_instances rfl` to `Rat.commRing`; `absUB = |·|`. |
| ℚ norm | `instCertNormLeRat`, `norm_algebraMap_rat'` | PASS (N5) | Holds for every `RCLike 𝕜`. |
| QSqrt2 ring | `QSqrt2`, its `CommRing` | PASS | `mul = ⟨ac + 2bd, ad + bc⟩` is exactly `(a+b√2)(c+d√2)`. All ring axioms are proved by `ext; simp; ring`. |
| QSqrt2 → ℝ | `QSqrt2.qsqrt2RealHom`, `realVal` | PASS | `a + b√2`; `map_mul` uses `√2·√2 = 2`. `algebraMap_qsqrt2_real` is `rfl`. |
| majorant | `QSqrt2.absUB`, `sqrt_two_le`, `abs_realVal_le` | PASS | `√2 ≤ 141422/100000` via `Real.sqrt_le_left` and `norm_num` (kernel-checked). It is genuine: the probe proves `¬ √2 ≤ 141421/100000`. The bound is `|a| + |b|·1.41422`. |
| ℂ semantics | `instAlgebraQSqrt2Complex`, `IsScalarTower QSqrt2 ℝ ℂ`, `CertNormLe QSqrt2 ℂ` | PASS | `algebraMap QSqrt2 ℂ x = ↑(algebraMap QSqrt2 ℝ x)` is `rfl` (probe). |
| B2 layer | all of `Poly/{Basic,Deriv,Bracket,Bound,Lie}` | PASS | Generic in `K`; ℚ specialization = old statements (§1). |
| sup bound | `cartMonoBound`, `cartSupBound`, `norm_eval_le_supBound`, `abs_eval_le_supBound`, `abs_actionBracket_le_supBound` | PASS | The proof uses only `CertNormLe.norm_le` and `mul_le_mul`. The result type is still `ℚ`. |
| checker | `cartEqCheck`, `cartEval_eq_of_eqCheck` | PASS | Generic soundness. Zero filtering uses `decide (m.c ≠ 0)` in `K` with the class's `DecidableEq`. |
| scalars | `cartAction`, `cartLieSum`, `two_half`, `algebraMap_ratCoeff`, `ratCoeff_half_mul_two` | PASS | `ratCoeff q = ofRat q`. `algebraMap_ratCoeff` holds for any `Algebra K 𝕜` (`eq_ratCast` on the composite hom), so `1/2` and `1/j!` mean what they say under any algebra structure. |
| real/complex lemmas | `cartEval_action`, `cartEval_ofReal`, `cartEval_bracket_{real,complex}`, `cartEval_adPow_complex`, `cartEval_lieSum_complex`, `cartEval_actSubst_real` | PASS | The extra `[Algebra K ℝ]`/`[Algebra K ℂ]` (`[IsScalarTower K ℝ ℂ]`) binders are typing data (instance-level). At ℚ they are Mathlib's, and the statements hold for any such structure. |
| smoke | `hhQuadSmoke`, `hhCubicSmoke`, 7 `decide +kernel` examples, `hhQuadSmoke_eval` | PASS (N4) | See §5. |

## 3. Definition classification

All new definitions are the intended objects on their whole carrier. None has junk values or fallbacks:

- `CartMonoK K`, `CartPolyK K` are plain data. `CartMono := CartMonoK ℚ` and `CartPoly := CartPolyK ℚ` are abbrevs.
- `ratCoeff` is the ring hom `ofRat`.
- `QSqrt2` and its operations are exact `ℚ(√2)` arithmetic. `realVal` is the standard embedding.
- `absUB` is a total, sound majorant. `cartMonoBound` uses `absUB m.c`, which at ℚ is `|m.c|` by `rfl` (`absUB_rat`).
- `instAlgebraQSqrt2Real/Complex` are `RingHom.toAlgebra` of the semantic homs.
- `hhQuadSmoke`/`hhCubicSmoke` are test data.

## 4. Diamonds and `@[default_instance]` (focus 4)

I ran a meta probe over the 307 non-internal declarations in the 7 modules:

- **No mixed specialization.** No declaration whose type is generic in `CertCoeff` mentions `instCertCoeffRat`. So
  no generic lemma silently pinned a sub-term to ℚ through the default instance.
- **ℚ-only declarations** (mention `instCertCoeffRat` without being generic): only `absUB_rat`, `ratCoeff_rat` and
  `instCertNormLeRat`, all intended.
- **No ℚ diamonds** (`with_reducible_and_instances rfl` / `rfl`):
  - `CertCoeff.toCommRing = Rat.commRing`
  - `certCoeffDecEq ℚ = inferInstance`
  - `toCommRing (QSqrt2) = QSqrt2.instCommRing`
  - `cartEval` at ℚ uses `DivisionRing.toRatAlgebra`
- **Default instance.**
  - An expression whose `K` is determined by context, such as `cartEqCheck (cartAction 0) hhQuadSmoke`, resolves to
    `QSqrt2` (checked by `rfl` against the explicit `(K := QSqrt2)` form).
  - A bare `cartAction 0` defaults to `CartPolyK ℚ`, as designed.
  - Residual risk, for future data files: a `QSqrt2` term written without any `QSqrt2` information defaults to ℚ
    and fails to type-check against a `QSqrt2` target. It cannot silently change the meaning of a `QSqrt2`
    statement. Recorded as N3.

## 5. Smoke tests (focus 5)

- Every check is `decide +kernel`. There is no `native_decide`, `implemented_by` or `extern` (grep).
- I re-checked the semantics by hand against the convention `cartBracket P Q = Σ ∂_qP ∂_pQ − ∂_pP ∂_qQ`:
  - `{I₀ − (√2/2)I₁, q₁} = (√2/2)p₁` ✓
  - `{·, p₁} = −(√2/2)q₁` ✓
  - `{I₀, q₀} = −p₀` ✓
  - the negative check uses `√2/3` ✓
  - antisymmetry of the cubic `q₀²q₁ − q₁³/3` with the quadratic part ✓
  - `cartSupBound hhQuad [1,1] [1,1] = 1 + 2·(1/4)·1.41422 ≈ 1.707 ≤ 2` ✓
- `hhQuadSmoke_eval` proves the intended real semantics `I₀ − (√2/2) I₁` through `toReal`.

## 6. Hygiene (exact commands and output)

All Lean runs used `LEAN_NUM_THREADS=1 systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 …`,
one process at a time.

- Build: `inp_lake_build.sh <wt> KAM.EffectiveStability.Poly KAM.EffectiveStability.Poly.QSqrt2Smoke` →
  `Build completed successfully (2892 jobs).`
- Axioms: a probe ran `Lean.collectAxioms` on all 307 declarations of the 7 modules → `axioms used: [Quot.sound,
  Classical.choice, propext]; bad: []`.
- Kernel replay, one invocation per module, sequentially: `lake env leanchecker --verbose
  KAM.EffectiveStability.Poly.{Coeff,Basic,Deriv,Bracket,Bound,Lie,QSqrt2Smoke}` and `KAM.EffectiveStability.Poly`
  → **exit 0** for all 8.
- `sh scripts/lint_sources.sh` → exit 1. The only failing line is the expected `KAM.lean is out of date; run
  scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)`, because the new modules `Poly.Coeff` and
  `Poly.QSqrt2Smoke` need the orchestrator's regeneration. All other checks pass: `check_lean_modules: PASS`, 25
  tests OK, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`.
- Forbidden tokens: `grep -nE 'sorry|admit|axiom|unsafe|opaque|set_option|native_decide|implemented_by|extern'`
  over `Poly/*.lean` and `Poly.lean` → no hits.
- File sizes: the largest is `Poly/Basic.lean` at 442 lines (cap 1500). Every file is a module (copyright, `module`,
  `public import`, docstring, `public section`).
- `git diff inp...HEAD --stat -- KAM/Frozen manifest KAM.lean KAM/Root README.md lakefile.lean` → empty.
- Probe files in `.lake/abi-scratch/` were deleted afterwards.

## 7. Notes (non-blocking)

- **N1 (API surface, namespace).**
  - The fully-qualified names `KAM.EffectiveStability.CartMono.{powProd, cartMonoEval, cartMonoMul, cartMonoTrim,
    cartMonoDq, cartMonoDp, powProd_congr, powProd_addPad, cartMonoEval_mul, cartMonoEval_trim}` became
    `CartMonoK.*`.
  - Dot notation `m.cartMonoEval` still works.
  - No `.lean` file in the repo references `CartMono.` explicitly, so nothing breaks. Out-of-tree or future code
    using the explicit `CartMono.` prefix would need `CartMonoK.`.
  - The handoff says "names unchanged". Strictly, the short names are unchanged and the namespace is not. This is
    a deviation to record.
- **N2 (API surface, dot notation).**
  - For `P : CartPoly`, the old notation `P.cartEval z` no longer elaborates ("Function `cartEval` does not have a
    usable parameter of type `CartPoly`"), because `cartEval` now takes `CartPolyK K`. The same applies to
    `P.cartDq`, etc.
  - 18 old theorem statements were written with `P.cartEval`. In the probe I rewrote them to `cartEval P` and they
    are then definitionally equal.
  - Statement meaning is unaffected and no in-repo code uses the dot form. This is a source-compatibility deviation
    the handoff does not mention.
- **N3 (default instance).** `@[default_instance] instCertCoeffRat` is a global elaboration default for `CertCoeff`.
  It is safe for meaning (§4). Future generic statements should keep writing `(K := K)` where `K` is not
  determined by an argument, as the prover did.
- **N4 (docstrings).**
  - A textual rewrite garbled several docstrings, for example `Poly/Bracket.lean` module doc: "`KAM.Canonical.poissonBracket
    P.cartEval cartEval Q z`" and "`fderiv ℝ cartEval P z (KAM.hamiltonianVectorField cartEval Q z)`"; `Poly/Deriv.lean`:
    "`fderiv 𝕜 cartEval P z v`". The correct form is `(cartEval P) …` / `(fun z => cartEval P z)`.
  - The `QSqrt2Smoke` module doc uses 1-based `I₁ − (√2/2) I₂ … q₂`, while the code and declaration docs are
    0-based (`I₀ − (√2/2) I₁`, `q₁`).
  - Cosmetic only.
- **N5 (duplication).** `norm_algebraMap_rat'` (Coeff) duplicates the retained `norm_algebraMap_rat` (Bound).
  Harmless.
- **N6 (computability, as disclosed by the prover).** `instCertCoeffRat`/`instCertCoeffQSqrt2` are
  `noncomputable`. Data must stay in `noncomputable section` (it already does). Kernel `decide` is unaffected.

## 8. Suspected blueprint / source defects

None. The package only generalizes the B2 polynomial layer. It relies on no fact that contradicts the blueprint and
reveals no false frozen statement.

READY B3-COEF-AUDIT
