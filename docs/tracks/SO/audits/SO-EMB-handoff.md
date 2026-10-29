# SO-EMB prover handoff (branch inp-soemb, 59fc468f; track SO package run by the main orchestrator)


Branch `inp-soemb` (off `inp-soexpw`), worktree `/root/code/KAM-inp-soemb`. Last commit `59fc468f`. Every edit
is committed. No `sorry`, axiom, `native_decide` or heartbeat or recursion overrides. No frozen, shared,
`README.md` or `KAM.lean` edits.

## Files (all new; 1228 lines in total, the largest is 469)

- `KAM/Certificate/Embedding.lean` (162 lines)
  - Signed, verbatim: `CertEmbedding`, `CertEmbedding.eval`, `CertEmbedding.differentiable_eval`,
    `CertEmbedding.isPrimaryOnStrip`, `CertEmbedding.isRealOnReals`. All are law-free, with only `[CertArith α]`.
  - Helpers:
    - `realComp`, the optional component `(2π)^d (P or 0)`;
    - `CertEmbedding.angleAt`, `actionAt`, `eval_fst`, `eval_snd`;
    - `realComp_add_int`, `realComp_real`, `differentiable_realComp`;
    - `character_conj`, `CertRealPoly.eval_conj`, `realComp_conj`, `CertEmbedding.angleAt_conj`,
      `differentiable_angleAt`.
- `KAM/Certificate/Expr/ComposeModels.lean` (431 lines): the slot models and their enclosure contracts.
  - `zeroModel`, `ratErrUp`, `constModel`, `padKey`.
  - `CertRealPoly.toSortedPoly`, `realCompModel`, `imulItems`, `phaseTermModel`, `charPhaseModel`.
  - `CertRealPoly.isZeroData`, `CertEmbedding.angleIsZero`, `CertEmbedding.normKey`.
  - `CertPoly.reflectSorted`, `shiftModel`, `findKeyIdx`, `subAdvice`, `ModelConfig.forWitness`, `charExpFun`.
  - Lemmas: `*_encloses`, `charExpFun_normKey`, `charExpFun_reflectSorted`, `exp_I_modePhase_eval`,
    `CertRealPoly.eval_toSortedPoly`, `toDeg_deg`, and others.
- `KAM/Certificate/Expr/Compose.lean` (469 lines)
  - Signed, verbatim: `Witnesses`, `Slp.compose`, `Slp.compose_sound`.
  - Internals:
    - `CertModel.mulN` and `CertModel.mulN_supNormUp`;
    - `ComposeState`, `slotEntry`, `ComposeState.slot`, `ComposeState.pushSlot`;
    - `charResolve`, `charEntry`, `charSlot`, `composeStep`, `composeOps`;
    - `CacheValid`, `ComposeState.SlotsEnclose`;
    - the `*_sound` lemmas.
- `KAM/Certificate/Tests/Compose.lean` (166 lines): `decide +kernel` tests and a contract instance, all in `ℚ`.
- Not committed, because `.drafts` is ignored: `.drafts/SO-EMB-lunar-probe.lean` is the CertFixed timing probe
  described below.

## Approach

**Embedding.** `K.eval` is the signed formula. A missing component goes through `Option.getD 0`.

- `differentiable_eval` uses `Differentiable.prodMk` and `differentiable_pi`.
- Primary: `CertRealPoly.eval_add_int`.
- Real on reals: `CertRealPoly.eval_real`. The `(2π)^d` factor is real.
- `angleAt_conj`, that is `U(θ̄) = conj U(θ)`, is law-free. The reflected character witnesses use it.

**Composition.** `Slp.compose` does one structural `List.foldl` over `p.ops`, with an `Option ComposeState`
state. A failed check makes it `none` from then on (fail closed). Each slot stores `(model, |poly|_w)`.

| Op | Slot model |
|---|---|
| `const re im deg` | `constModel n`: one term at the zero key of length `n`, centre `ofRatUp`, radius `≥ ofRatUp q − q` for each part. Exact in `ℚ` and for dyadic constants. |
| `action j` | `j < n`: `realCompModel n dA_j A_j` (exact, `toSortedPoly`). Otherwise `zeroModel`. |
| `char k` | `χ_k∘K = χ_k · exp(i·2π k·(2π)^{dU}U)` (`exp_I_modePhase_eval`). The witness is found under `kk = K.normKey n k`. If `kk` has none, the witness of `−kk` is used, reflected by `reflectSorted` (`conjReflect` with the order reversed). The slot is `shiftModel` by `padKey n k`: exact shift, radius `w^{\|k\|₁}·r`. |
| `add a b` | `CertModel.add W m_a (toDeg W pe m_a.deg m_b)` (mixed degrees). |
| `mul a b` | `CertModel.mulN W cfg [0, slot] m_a |m_a|_w m_b |m_b|_w`, which is `CertModel.mul` with the cached norms (`mulN_supNormUp` is `rfl`). |
| `exp a` | The next `expWit` (slot order): `expWitnessRadius n W (cfg.forWitness 1 i) (toDeg W pe 0 m_a) E`, giving `⟨0, E.poly, r⟩`. |
| `inv a` | The next `invWit`: `invWitnessRadius n W (cfg.forWitness 2 i) m_a Q`, giving `⟨−deg, Q, r⟩`. |

A slot off the program, or an operand that is not an earlier slot, is `zeroModel`. This matches `Slp.vals`,
where such a value reads `0`.

**Character witnesses.**
- Each table witness is checked once by `expWitnessRadius` against `charPhaseModel n K W pe kk`. This model is
  `Σ_{j<n, kk_j≠0} toDeg 0 (i·kk_j·(2π)^{dU_j+1}·U_j)`.
- The pin `exp(2πi k·U(0))` therefore goes through SO-EXPW's `certCExpReduced`. A failed reduction gives
  `none`.
- Certified witnesses and their reflections are cached under their normalized key, so each one is computed once.
  Lunar case: the 14 keys ±(2, 2−m) give two cache entries, (2,0) and (−2,0), from one table entry.
- `CacheValid` is part of the invariant.

**Soundness.** The invariant `ComposeState.SlotsEnclose` after `ops` has three parts:
- `len = ops.length`;
- every `slot i` encloses `θ ↦ (Slp.vals n (K θ) ops).getD i 0` on `T_ρ`, and its stored norm is
  `supNormUp`;
- the cache is valid.

`composeStep_sound` is proved by cases on the op. Old slots use `Slp.val_append`, the new slot uses
`Slp.val_snoc_self`, and `composeOps_sound` follows by `List.reverseRecOn`. `Slp.compose_sound` holds on success
with no domain hypothesis: reciprocal witnesses certify their own nonvanishing (`invWitness_sound`).

## Brief requirements (volume and kernel)

- **Scalars are not products (SO-ADVCOUNT lever 1).** Constants are models whose keys are all zero.
  `CertModel.polyProduct` therefore takes its scalar route for any `mul` with a constant operand. The test
  `composeTest_scalar` checks this: the product `(1/2)·A` is exact, with radius `0` and 3 terms.
- **Cached weighted norms (SO-MALG signal 1(c)).** Each slot stores `|P|_w`, computed at most once. The kernel is
  lazy, so it is computed only if a product reads it. Products use `CertModel.mulN`.
- **No forced accumulators and no per-term zero tests.**
  - The only tests are per coordinate (`kk_j = 0` in `charPhaseModel`) and per key (cache/table lookup).
  - **Slots are stored newest first.** A push is one cons, and the slot count is an explicit field.
  - The first version appended (`slots ++ [e]`). That built unevaluated append chains that every operand lookup
    re-walked: 48 s of kernel on the lunar probe, against 14 s now.
- **Per-witness advice books (SO-EXPW handoff, item 3).** `ModelConfig.forWitness s i` keeps the advice entries
  `s :: i :: rest` and re-keys them to `s :: rest`. Advice is untrusted, so every contract holds for any book.

  | Witness | Generator emits | Seen by the witness as |
  |---|---|---|
  | exp witness `i` (slot order) | `[1, i, j]` | `[1, j]` |
  | character table entry `c` | `[1, expWit.length + c, j]` | `[1, j]` |
  | reciprocal witness `i` | `[2, i]` | `[2]` |
  | compose product at slot `s` | `[0, s]` | (not re-keyed) |

  SO-DATA and the generator must emit these keys.
- **Canonical key order (my addition, efficiency only).** `CertRealPoly.toPoly` (landed) emits the zero term at
  key `[]` and interleaves `k`/`−k`. The model algebra's sorted merges (`mergeErrTerms`) then cannot combine
  equal keys.
  - Effect: with `toPoly`, the toy reciprocal check `Q·A` gave `δ ≈ 0.15` and a radius of 0.16 (duplicate keys
    pay separately). With the canonical order the radius is about 1e-9.
  - Fix: compose uses `CertRealPoly.toSortedPoly n` instead. It emits the reversed conjugates, then the zero key
    of length `n`, then `half`, and is proved equal in value to `eval` under the laws.
  - It is ascending when the `half` keys have length `n`, are lexicographically positive and are ascending. **The
    generator should emit `half` that way**, and keys of length `n` throughout: character witness keys, the
    witnesses' polynomials, and so on. Any order remains sound.

## Checks and their exact output

- `inp_lake_build.sh … KAM.Certificate.Embedding KAM.Certificate.Expr.ComposeModels KAM.Certificate.Expr.Compose
  KAM.Certificate.Tests.Compose`:
  ```
  ✔ [2959/2961] Built KAM.Certificate.Expr.ComposeModels (3.4s)
  ✔ [2960/2961] Built KAM.Certificate.Expr.Compose (3.6s)
  ✔ [2961/2961] Built KAM.Certificate.Tests.Compose (8.0s)
  Build completed successfully (2961 jobs).
  ```
  Embedding had been built earlier in 2.6 s. None of my files emits a warning.
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS (1354 Lean files…)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (144 frozen declarations)`. Its only failure is `KAM.lean is out of date; run
  scripts/gen_root_imports.py`.
  - This was already failing at the branch base, before any SO-EMB change.
  - `KAM.lean` is generated and rule 10 forbids editing it. The orchestrator should regenerate it so that it
    picks up the four new modules.
  - No line in my files is over 100 characters.
- `main_shortname_check.py … (four modules)`: `short-name check OK (no reused public short name)`.
  `ComposeState.push`, `Valid` and `valid_nil` collided with Mathlib short names and were renamed `pushSlot`,
  `SlotsEnclose` and `slotsEnclose_nil`.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
  `CertEmbedding.differentiable_eval`, `CertEmbedding.isPrimaryOnStrip`, `CertEmbedding.isRealOnReals`,
  `Slp.compose_sound`, `composeTest_all`, `composeTest_n2`, `composeTest_sound`.

**Tests** (`Tests/Compose`, `ℚ`, `decide +kernel`; the whole file elaborates in about 8 s). Setup: `n = 1`,
`U = 0.1 cos`, `A = 1 + 0.1 cos`, `dU = −1`, and an 11-slot program.

| Test | What it checks |
|---|---|
| `composeTest_all` | All 11 slots: action, constant, scalar product, `χ_1`, `χ_{−1}` through reflection, a sum, a model product, `exp(1/2)`, `1/A`, the degree `−1` constant `i/2π`, and a mixed-degree sum. Every radius is in `[0, 10⁻⁶]`. |
| `composeTest_scalar` | The scalar route is exact. |
| `composeTest_conj` | The reflected radius equals the direct one, and is `> 0`. |
| `composeTest_noChar`, `_noExp`, `_noInv` | A missing witness gives `none`. |
| `composeTest_pinFail` | `U(0) = 3.1` with `pinHalvings = 0` gives `none`. |
| `composeTest_offProgram` | A slot off the program is the zero model. |
| `composeTest_normKey`, `composeTest_n2` | `n = 2`, `U₂` syntactically zero: keys (1,0), (1,3) and (−1,2) share the one witness under (1,0). |
| `composeTest_sound` | Contract instance. |

## Kernel timings

The probe is `.drafts/SO-EMB-lunar-probe.lean`, run with the profiler; it uses `CertFixed 128`.

- **Program:** the real lunar jet `(soRotHamExprScaled (237/125)).jet`, which has 887 slots and 14 `char` ops. It
  is pasted as a literal, generated by `#eval`.
- **Embedding:** `U₀ = 0.05 cos`, `U₁ = 0`, `p = 1 + 0.05 cos`, `J = 0`.
- **Witness:** one 25-term character witness `exp(2iU₀)` under (2, 0).

| Check | Kernel |
|---|---|
| `composeOps … .isSome` (all witness and cache control flow) | 0.51 s |
| the four `d1` models, all radii `≤ 2⁻²⁸` (wanted = `jet.d1`) | 14.2 s (48.2 s before the newest-first fix) |
| one witness check, `expWitnessRadius` of the character, alone | 0.05 s |

## Design signals and uncertainties

1. **The jet compiler is expensive in the kernel.**
   - `(soRotHamExprScaled c).jet.prog.ops.length = 887` by `decide +kernel` costs **60.7 s of kernel**. This is
     SO-EXPR's `HamExpr.jet`, not SO-EMB. An end-to-end check that computes the jet inside each `decide` pays
     this again every time.
   - Suggestion for SO-DATA: state `(soRotHamExprScaled c).jet = <literal>` once, or `prog`/`d1`/`v0` separately,
     then rewrite before the decides.
2. **The model algebra dominates compose cost.**
   - It is about 16 ms per slot even with tiny models: 870 slots in 14 s, from weights, `errRadius` and merges
     in `CertFixed`.
   - With production models (250 to 8.5k terms) the per-term costs of SO-MALG signal 1 scale this directly.
   - The levers are in `Model/Terms`, not in SO-EMB: (a) one weight per operation, (b) a weight table by degree.
   - **SO-DATA should measure the real stage before choosing.** I could not build valid production-size witnesses
     here.
3. **Unmerged duplicate keys cost precision as well as time.** See the canonical-order point above. The
   SO-EXPW reciprocal check is complete only for merged products: `oneSubSupUp` pays each duplicate key
   separately. The packed advice path returns dense, merged output, but the `direct` path merges only if its
   inputs are sorted.
4. **Character lookup falls back on failure.** If the witness under `kk` exists but its check fails,
   `charEntry` falls back to the witness of `−kk` before failing. This is sound, since each route is checked, and
   it only costs time in a failing case.
5. **Key equality is list equality.** Table and cache keys are compared as lists: `decide (key = kk)`, where `kk`
   has length `n`. A table key with another length, such as `[2]` for (2, 0), is never found, and the composition
   fails closed.
6. **No unused-witness check.** Unused witnesses, extra exp/inv witnesses or extra table entries are ignored.
   Soundness does not need such a check.
7. **No heartbeat problem.**
   - Every proof elaborates at default settings, and each file builds in at most 8 s.
   - During development, two elaboration timeouts came from lazy-delta `rfl` checks that unfolded `supNormUp` (its
     `pairRounds 64`). They were fixed structurally, by `unfold` plus `pair_snd`, explicit `cases`, and
     `simp only` on projections. No budget was raised.

## Suspected errata and deviations

- No pinned-source errata. Every signed statement was proved exactly as signed, with no added hypotheses.
- Deviations, all implementation choices inside unsigned bodies:
  - the advice re-keying convention above;
  - the canonical key order (`toSortedPoly`, a zero key of length `n` for constants, `reflectSorted`);
  - the fallback to `−kk` after a failed `kk` check.

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §7 row SO-EMB; signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean lines ~653-700 (CertEmbedding and its eval, differentiable_eval, isPrimaryOnStrip, isRealOnReals; Witnesses; Slp.compose, Slp.compose_sound). Built on SO-EXPW, SO-MALG, SO-EXPR, SO-BALL (landed). Design audit 3 F10 / Revision 4: character and exponential witnesses go through the pins and fail closed.

AUDIT FOCUS: (1) signed declarations verbatim; (2) Slp.compose_sound: the composed models enclose the EXACT composition of the expression program with the embedding on the stated strip, for every certificate-supplied embedding and witness, with no added premise; failure paths fail closed; the constant-operand scalar route and the cached weighted norms are sound; (3) CertEmbedding.isPrimaryOnStrip / isRealOnReals / differentiable_eval are the properties IG1Body needs, stated on the whole stated domain; (4) tests reduce by decide +kernel; (5) hygiene. Audit ONLY KAM/Certificate/{Embedding,Expr/Compose,Expr/ComposeModels}.lean and KAM/Certificate/Tests/Compose.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
