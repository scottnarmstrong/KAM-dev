# SO-MALG prover handoff (branch inp-somalg, 78ddce05; track SO package run by the main orchestrator)


Branch `inp-somalg`, worktree `/root/code/KAM-inp-somalg`. Base `b339e88f` (SO-POLY-B audit request). Six commits
on top, HEAD `78ddce05`. Everything
is committed.

Every signed SO-MALG declaration of `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` (§C, `ModelConfig` through
`CertModel.Encloses.average`) is proved or defined with its signed type, verbatim. That is 12 declarations, docstrings
included. The bodies reduce in the kernel (`decide +kernel` tests below).

Hygiene: no `sorry`, no axiom, no `native_decide`, no heartbeat, recursion-depth or synthesis override. No well-founded
recursion; every recursion is structural over `List` or `ℕ`. No file is over 700 lines.

## Files (all new)

| File | Lines | Content |
|---|---|---|
| `KAM/Certificate/Model/Terms.lean` | 539 | The kernel toolkit (details below). |
| `KAM/Certificate/Model/Ops.lean` | 698 | The signed SO-MALG layer and its supporting lemmas (details below). |
| `KAM/Certificate/Tests/Model.lean` | 211 | `decide +kernel` tests and one contract instance. |

**`Model/Terms.lean`** contains:
- error terms `ErrTerm α = (key, coefficient, error bound)` with their denotation `errTermsEval` / `errTermsErr`;
- `keyDeg`, and `keyCmp` (lexicographic) with `keyCmp_eq_eq`;
- the backend complex operations with error bounds: `CC.addC/addErrC`, `CC.mulC/mulErrC`, `CC.scaleC/scaleErrC`;
- balanced upward sums: `sumPairsUp`, `pairRounds`, `sumUp`, `sumUp_ge`;
- `weightTermUp` (`|e|·w^{|k|₁}`), `errRadius` and `CertPoly.supNormUp` (the strip sup bound), with their lemmas;
- the structural sorted merge `mergeErrTerms` with `mergeErrTerms_spec`;
- the direct product `directItems` with `directItems_spec`;
- the cutoff truncation `truncKeep`, `truncErr`, `truncPoly` with `truncPoly_spec`.

**`Model/Ops.lean`** contains the signed declarations and their supporting lemmas:
- **Signed:** `ModelConfig`; `CertModel.add/mul/trim/toDeg/ofDeriv`; `CertModel.Encloses.{add, mul, trim, toDeg,
  ofDeriv, average}`.
- **Helpers:** `adviceLookup`, `CertPoly.isConst`, `CertModel.polyProduct` with `CertModel.polyProduct_sound`,
  `crossUp`, `trimDrop`.
- **Powers of 2π:** the Machin bounds `piLowPos/piUpMin/twoPiZpowLo/twoPiZpowHi` with `twoPiZpow_mem`.
- **Lemmas:** `scaleItems`, `derivItem`, `CertModel.Encloses.rad_nonneg`, `norm_mul_sub_le_core`,
  `norm_toDeg_sub_le_core`, `hasFDerivAt_termSum`, `CertPoly.torusAverage_eval`.

Imports: `Model/Ops` → `Model/Terms` (→ the `Poly/Ops` facade only), `Arith/PiEnclosure`, `Strip/Averages` (for
`torusAverage`). `KAM.lean` was not edited (rule 10). `gen_root_imports.py` would add exactly my three modules
plus SO-POLY-B's six. I checked this and restored the file.

## Approach (what each operation computes)

**`add` (same degree).** The two polynomials are combined by a structural sorted merge.
- Equal keys add their coefficients.
- Each merged entry carries `upAdd(e₁ + e₂, addErr re + addErr im)`.
- The radius is `r_a + r_b + Σ_entries |e|·w^{|k|₁}`.
- The merge is sound for any input order and complete for lexicographically sorted keys. All landed producers are
  sorted: the generator, the packed `targetTerms` and the merges themselves.
- On both production backends the errors are zero (`addErr = 0`).

**`mul`.** The route is chosen in this order:
1. **Scalar route.** A constant factor (every key zero, the zero polynomial included) gives a scalar
   multiplication: `directItems` with one row. If the constant is the right factor it is commuted.
   - This happens before any advice lookup, so the packed route is never used (SO-ADVCOUNT lever 1).
   - The test shows it holds even with bogus advice registered under the key.
2. **Advice route.** Otherwise `adviceLookup cfg.advice key` decides:
   - `packed P rr ii ri ir` calls SO-POLY-B's `CertPoly.mulPacked cfg.toMant W P …`. Its all-zero real or imaginary
     parts cost nothing; that is SO-POLY-B's `packedRealProduct` (lever 2).
   - `direct` calls `directItems`: rows merged one after another, keys `packAddZ`, coefficient errors from
     `CertBall.mulRe/ImErr`.
3. **Crude fallback.** A missing key or a failed packed check gives `⟨deg_a + deg_b, 0, (|P_a|_w + r_a)(|P_b|_w + r_b)⟩`.

On every non-crude route:
- Product terms with `|k|₁ > cfg.cutoff` move into the error at size `normUp(c)·w^{|k|₁}` (`truncErr`).
- The radius is `remainder + errRadius + crossUp(|P_a|_w, r_b) + crossUp(|P_b|_w, r_a) + r_a r_b`.
- `crossUp n r` is `0` when `beq r 0`, and then never evaluates `n`. An exact factor therefore does not pay for the
  other factor's weighted norm.

`Encloses.mul` is unconditional. It rests on `norm_mul_sub_le_core`:
`XY − CDQ = CD(AB − Q) + CAv + DBu + uv`.

**`trim`.** It drops the terms with `weightTermUp(normUp c) ≤ eps`. Their weighted sizes are added to the radius
through `supNormUp` of the dropped part.

**`toDeg`.** The degree changes by `e = deg − d`.
- `(2π)^e` is enclosed in `[lo, hi]` from the Machin bounds at `pe`'s `(machinK, machinJ)`. Each bound is the better
  of the Machin bound and the landed `piLoQ`/`piUpQ`, so a degenerate parameter pair cannot give a nonpositive lower
  bound.
- The centre is `c = ofRatUp hi`, and `r ≥ c − ofRatDown lo` is computed in the backend.
- The new polynomial is `scaleC c P`.
- The radius is `c·rad + r·|P|_w + Σ scale errors·w^{|k|}`.
- The same degree returns the model unchanged.

**`ofDeriv`.** Each coefficient becomes `i k_j c = ⟨−(c.im·k_j), c.re·k_j⟩` (backend `mul`, errors in the radius) at
degree `d + 1`. Terms with `k_j = 0` are dropped.
- `hasFDerivAt_termSum` gives `fderiv ℂ (P.eval n) θ (e_j) = 2π Σ i k_j c χ_k`, by induction with
  `fderiv_character_single`.

**`average`.** `CertPoly.torusAverage_eval` shows the average of `P` over the real torus is `P.coeff n 0`. It uses
`torusAverage_character` and linearity of the integral on continuous integrands. Then `norm_torusAverage_le` bounds
the remainder. Continuity of `f` on the strip gives integrability.

## Checks (exact)

- **Gate build.** `inp_lake_build.sh /root/code/KAM-inp-somalg KAM.Certificate.Model.Terms KAM.Certificate.Model.Ops
  KAM.Certificate.Tests.Model` printed `Build completed successfully (2915 jobs).`
  - There is no warning in my files. The only warning shown is the existing one in `Arith/PiHigh.lean:218`.
- **Lint.** `sh scripts/lint_sources.sh` printed:
  - `KAM.lean is out of date; run scripts/gen_root_imports.py`. This is expected (the generated root, rule 10).
  - `check_lean_modules: PASS (1346 Lean files, 0 comparator configurations)`
  - `FROZEN-ANCHOR GUARD OK`
  - `ABI HASHES OK (144 frozen declarations)`
  - Every line is at most 100 columns.
- **Short names.** `main_shortname_check.py /root/code/KAM-inp-somalg KAM.Certificate.Model.Terms
  KAM.Certificate.Model.Ops KAM.Certificate.Tests.Model` printed `short-name check OK (no reused public short name)`.
  An earlier `pairUp` clashed with Mathlib and was renamed `sumPairsUp`.
- **Signature check.** The script is `.drafts/SO-MALG/sigcheck.py`. It compares the 12 signed declarations
  whitespace-normalized: statements up to `:=` (docstrings included), and the full text of `ModelConfig`. It printed
  `checked 12 bad 0`.
- **`#print axioms`.** Every one of the following gives `[propext, Classical.choice, Quot.sound]`:
  - `CertModel.Encloses.{add, mul, trim, toDeg, ofDeriv, average}`;
  - `CertModel.polyProduct_sound`, `mergeErrTerms_spec`, `directItems_spec`, `truncPoly_spec`;
  - the tests `modelTest_mul_packed`, `_scalar`, `_toDeg`, `_mul_encloses`.

## Tests (`Tests/Model`, all `decide +kernel`; whole file 2.6 s in the gate build)

The data are restated from `Tests/Packed`. Bodies of non-`@[expose]` definitions of another module are not exported,
so the kernel cannot unfold `packedTest*` from here.

| Test | What it shows |
|---|---|
| `modelTest_mul_packed` | The packed route returns exactly `mulPacked`'s polynomial (non-empty). |
| `modelTest_mul_missing`, `_failing` | A missing key, and advice with one slot off by `+2`, both give the crude model (empty polynomial). |
| `modelTest_mul_scalar`, `_scalar_coeff` | A constant factor is a scalar multiplication, with no advice and with bogus advice under the key, on either side. The keys are the other factor's; the coefficients are floored products. |
| `modelTest_mul_zero` | The zero model times anything gives empty polynomial and radius `0`. |
| `modelTest_mul_encloses` | `Encloses.mul` instantiated on the packed route. |
| `modelTest_mul_direct` (ℚ) | `(1 + 2χ₁)(χ₋₁ + 1) = χ₋₁ + 3 + 2χ₁`, merged and sorted. |
| `modelTest_add` (ℚ) | Merge with keys sorted; radius `1/10 + 1/5`. |
| `modelTest_trim` (ℚ) | `χ₅/1000` is dropped; radius `= 1.1⁵/1000`. |
| `modelTest_ofDeriv` (ℚ) | `∂₀(3χ_{(2,1)} + χ_{(0,4)})` gives `6i χ_{(2,1)}` at degree 1, radius 0. |
| `modelTest_pi`, `modelTest_toDeg` (ℚ) | `checkPiEnclosure` holds. Degree 1 → 0: the coefficient is within `[2π, 2π + 10⁻⁶]` and the radius is `≤ 10⁻⁶`; the same degree is the identity. |

## Kernel timings at lunar size

**Setup.** Scratch only, generators in `.drafts/SO-MALG/timing/`, not committed.
- Data: `CertFixed 320`, 8544 terms, box 96 × 89 (2-D, sorted), mantissas about 2^312, `w = 1095/1000`.
- Runs: one Lean process, `LEAN_NUM_THREADS=1`, `ulimit -v 16 GB`.
- The machine was shared (load 5–8), so allow ±30 %.
- Times are the "type checking" (kernel) time; the base import cost of about 4.5 s is excluded.

| Operation | Kernel | Max RSS |
|---|---|---|
| `CertPoly.supNormUp` (8544 terms) | 19.1 s | 4.5 GB |
| `mul`, scalar route, constant with radius ≠ 0 (both `|P|_w` needed) | 33.1 s | 6.0 GB |
| `mul`, scalar route, exact constant (`crossUp` skips `|P_b|_w`) | 15.7 s | 4.9 GB |
| `add` of two 8544-term models (complete merge, 8544 out) | 17.0 s | 5.0 GB |
| `ofDeriv` (8448 out) | 13.1 s | 4.6 GB |
| `trim` | 19.8 s | 4.4 GB |
| `toDeg` (Machin `(50, 15)` included) | 26.8 s | 5.3 GB |

All of these scale linearly. The scalar route took 6.6 s at 1920 terms and 13.1 s at 3840 (before `crossUp`). The
weighted norm took 4.7 s at 3200 terms.

## Design signals and uncertainties

1. **Kernel cost per term, about 1.5–4 ms.** It is dominated by the per-term weight `ofRatUp(w^{|k|₁})` and the
   `upMul` around it.
   - SO-ADVCOUNT counts 478 scalar × model slots in the jet. If many of them act on full 8.5k-term models, the
     scalar route alone is hours of kernel per torus. Most are cfgLow models of about 250 terms, about 1 s each.
   - Levers (no signature change):
     - (a) Bound rounding radii by `(Σ e)·w^{K_max}`, one weight per operation. This loses at most `w^{K_max − |k|}`
       per term, about 7e-84 per full operation at 318 bits, against budgets of about 1e-80.
     - (b) A weight table by degree.
     - (c) Cache `|P|_w` of each slot model in `Slp.compose` (SO-EMB) instead of recomputing it in every product.
   - SO-DATA/SO-EMB should measure this on the real stage before choosing.
2. **Two kernel pitfalls I measured and removed.** Both are worth knowing for the other SO packages.
   - (i) A forced accumulator `cond (beq acc acc) …` is quadratic in the kernel (13 → 65 s from 1.6k to 3.2k terms).
     It is replaced by balanced pairwise sums (`pairRounds 64`, depth about `log₂ N`, no deep recursion).
   - (ii) A per-term zero test `ble e (ofInt 0)` on `CertFixed` cost about 15 ms per term. It is removed.
   - Generally, kernel `Int` arithmetic through negative intermediates (`Int.ediv` of a negative numerator,
     `Int.decLe` with a negative difference) measured 5–10× slower than the positive path in isolation. `CertFixed`'s
     `cdiv x d = −((−x)/d)` goes through that path on every upward rounding. A SO-ABK lever (no interface change)
     would be a positive-only `cdiv`: `(x + d − 1)/d` for `x ≥ 0`.
3. **`cutoff` is literal.** Products keep `|k|₁ ≤ cutoff`, so `cutoff = 0` keeps only the constant term.
   - SO-TOYGEN's table lists "cutoffs 0 / 0" for T1, T3 and TR. Its Python mirror uses `cutoff is None` for "no
     truncation".
   - If a generator emits `0` meaning "none", the Lean model drops every nonconstant product term into the radius.
     This is sound, but the margins fail. The generators must emit a real bound (for example 10⁶) instead.
4. **`toDeg` reads `pe`'s Machin parameters, not its backend centre/radius.**
   - The `hpe` premise is not needed for soundness: the Machin bounds hold unconditionally.
   - The result is at least as tight as the Python mirror's `pe.centre ± pe.rad` ball, which `checkPiEnclosure`
     makes contain the Machin interval.
   - The kernel recomputes `piLowRat/piUpRat` per call. It is included in the 26.8 s above; most of that is the 8544
     scaled terms.
   - The radius formula differs slightly from the mirror: the centre is the upper bound `hi`, plus the
     scaling-rounding term.
5. **Merging requires sorted keys for completeness only.**
   - Unsorted inputs stay sound but may keep duplicate keys, so later products grow.
   - The direct route merges row by row (`O(|a|·|result|)`, intended for the ℚ toys).
6. **The crude fallback** keeps `deg_a + deg_b` and uses `(|P_a|_w + r_a)(|P_b|_w + r_b)`. This is the design's
   "sup|a|·sup|b|" without the `(2π)^deg` factors, which stay symbolic.

No suspected errata in the pinned sources. No signed statement was false or underspecified.

**Deviations.** These are implementation choices, not statement changes:
- `trim`'s threshold uses `weightTermUp`, the same rounding as the radius.
- The constant test is "all keys zero".
- `crossUp` short-circuits on an exactly-zero radius.

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §7 row SO-MALG; signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean §C (ModelConfig through CertModel.Encloses.average). Built on SO-POLY-B (landed: advice-checked packed products, CertPoly.mulPacked).

AUDIT FOCUS: (1) every signed declaration verbatim; (2) each Encloses lemma (add, mul, trim, toDeg, ofDeriv, average) is sound for every input model and every ModelConfig, with no added premise: in particular mul's soundness when the advice is wrong or missing (the fallback), when an operand is constant (the scalar route), and at cutoff 0; trim's radius accounting; toDeg's use of the Machin bounds; (3) the kernel tests reduce and the bodies have no well-founded recursion; (4) hygiene. Audit ONLY KAM/Certificate/Model/{Terms,Ops}.lean and KAM/Certificate/Tests/Model.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
