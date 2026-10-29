# SO-POS prover handoff (branch inp-sopos, c86ea057; track SO package run by the main orchestrator)


Both signed declarations (`checkRealLowerBound`, `checkRealLowerBound_sound`, §F of SOSignatures.lean) are
proved/defined with the signed text verbatim (whitespace-normalized comparison of the statements: both `True`).
No sorry, axiom, native_decide, heartbeat override, `EuclideanSpace`, or well-founded recursion.

## Files
- `KAM/Certificate/Positivity.lean` (177 lines): the signed pair plus helpers.
- `KAM/Certificate/Tests/Positivity.lean`: `decide +kernel` tests on the `ℚ` backend.
`KAM.lean` not edited.

## Approach
`checkRealLowerBound W cfg f m₀ m g = decide (f.deg = 0) && ble (supBound W h) (ofRatDown (2 (m₀ - m)))` where `h`
(`CertModel.realLowerModel`) is the model of `(f + f*) - 2 g g* - 2 m₀`, built from `CertModel.add/mul`:
`f* = CertModel.starModel f` (conjSorted polynomial, same degree and radius), `g g*` by `CertModel.mul` at the SOS
site key `[7]` (cfg advice first, direct product as fallback appended to the book), scaled by the exact constant `-2`
(scalar route), plus the constant model of `-2 m₀` (centre `ofRatUp`, radius `ofRatUp + neg ofRatDown`, so rational
rounding is paid).
Soundness: on real `x`, `f*(x) = conj f(x)`, `g g*(x) = |g(x)|²`, so `Re` of the model function is
`2 Re f - 2|g|² - 2 m₀`; `norm_le_supBound` at the real point (in the strip by `ofReal_mem_complexStrip`) gives
`2 Re f ≥ 2 m₀ - 2(m₀-m) = 2m`. No added premise beyond the signed ones.
Helpers: `CertPoly.conjSorted` (reflection with reversed terms: negating keys reverses lexicographic order, so
sorted input stays sorted; without it `mergeErrTerms` is incomplete and the constants do not cancel — found by test),
`CertPoly.keyLen`, `CertModel.ofConst` (constant under the zero key of the polynomial's key length; keys `[]` would not
merge with `[0,…,0]`), `CertModel.mul_deg`, `Encloses.{starModel, ofConst, ofPoly}`, `certKeyFun_replicate`,
`CertPoly.eval_conjSorted`.

## Checks (exact)
- Gate: `inp_lake_build.sh /root/code/KAM-inp-sopos KAM.Certificate.Positivity KAM.Certificate.Tests.Positivity` →
  `Build completed successfully (2916 jobs).` No warning in my files (only the existing `Arith/PiHigh.lean:218`).
- `lint_sources.sh`: `KAM.lean is out of date` (expected, rule 10); `check_lean_modules: PASS`; FROZEN-ANCHOR GUARD OK;
  ABI HASHES OK; no line over 100 columns.
- `main_shortname_check.py`: `short-name check OK (no reused public short name)` (renamed `conj`→`reflect`→`starModel`).
- `#print axioms KAM.Certificate.checkRealLowerBound_sound`: `[propext, Classical.choice, Quot.sound]`.
- Tests (`decide +kernel`, ℚ, `w = 11/10`, whole file ~2 s): pass at `m ≤ m₀ - 11/10`; reject at slack `m = 2`;
  SOS term `g = χ₁` shifted by constant 4; degree `≠ 0` rejected.

## Kernel timings
Not measured at lunar size. Cost is 3 `add`s on `|f|`-sized models plus one `supBound` (weighted norm) over the
sum, plus the `g g*` product (direct, `|g|²` items; `g` is a small SOS polynomial) and exact scalar routes.
Extrapolating SO-MALG's numbers (add 17 s, supNormUp 19 s at 8.5k terms) expect roughly 1–1.5 min per full-size `f`.

## Uncertainties / design signals
1. **Degree.** `toDeg` needs a `PiEnclosure`, which the signed `checkRealLowerBound` does not take, so models with
   `f.deg ≠ 0` are REJECTED (`false`, sound but incomplete). Callers must pass `deg = 0` models (or convert with
   `toDeg` first). If degree-`d` inputs are wanted, the signature needs a `pe`.
2. Key `[7]` is the SOS site of the §7 key table; any advice there is used, else direct.
3. The check is sharp only for sorted keys of uniform length (the producers' invariant); otherwise it is sound but
   cruder. `f` with an empty polynomial uses `g`'s key length.
No errata found in pinned sources; deviations: none from the signature.

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §7 row SO-POS; signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean §F: checkRealLowerBound, checkRealLowerBound_sound. Built on SO-MALG (landed).

AUDIT FOCUS: checkRealLowerBound_sound holds for every model and every certificate datum with no added premise (the real part of the enclosed function is bounded below on the whole stated domain); the rejection of nonzero-degree models is sound (fails closed) and documented; the tests reduce by decide +kernel with false controls; hygiene. Audit ONLY KAM/Certificate/Positivity.lean and KAM/Certificate/Tests/Positivity.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
