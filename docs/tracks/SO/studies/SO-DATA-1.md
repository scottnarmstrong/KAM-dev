# SO-DATA-1: lunar certificates against the landed checker (STOPPED: design signal)

Branch `inp-sodata1`. Python and Markdown only. No Lean file was touched, and nothing was built: the worktree has no
`.lake`.

## Verdict: STOP. `checkHamBounds` fails for package R1 on both tori

The brief says to stop and report when a sub-check fails. One does.

The landed `checkHamBounds` (Defs.lean:233, `hamBoundsOk` :151) bounds `‖D²H‖` by
`Σ_a Σ_b |∂_a ∂_b H|`, summed over all four phase indices. Both off-diagonal angle entries are therefore counted. For
`ham = soRotHamExprScaled (237/125)`, the jet's ℚ balls give these bounds:

| bound (lower; upper equal to 1e-5) | value | `M = 1987/1000` |
|---|---:|---|
| `Σ_a |∂_a H|` (`DH`) | 1.9800 | ok (margin 7e-3) |
| `max_a |∂_a H|` (`X_H`) | 1.8960 (= c) | ok |
| `max_a Σ_b |∂_a∂_b H|` (`DX_H`) | 1.8960 | ok |
| `max_a Σ_{b,c} |∂_a∂_b∂_c H|` (`D²X_H`) | 1.5649 | ok |
| **`Σ_{a,b} |∂_a∂_b H|` (`D²H`)** | **2.0205** | **FAILS by 0.0335** |

**An independent closed form agrees.** The bound is
`c·(1 + Σ_m ε|A_m|(2π)²(2+|2−m|)² e^{2πρ_H(2+|2−m|)})`. At ρ_H = 257/10000 this is 2.020530.

**No choice of domain rescues R1.** As ρ_H falls, the bound decreases only to about 2.00 at ρ_H = 0.015 and 1.99 at ρ_H → 0.
In any case `checkEmbedding` needs `ρ_H ≥ ρ + ι + μ ≈ 0.025793`, so ρ_H is already at its floor.

**Cause.** SO-GEN2's majorant `M₁ = 1.047601` (`c·M₁ = 1.98625`) does not equal the landed form. With a max-row
count it would be `c·1.05528 = 2.0008`. With the full double sum it is `c·1.06568 = 2.0205`. In both cases it is
above 1.987, so the R1 package (`M = 𝔪 = 1987/1000`, LunarParams.lean) is not certifiable by the landed checker.
This is a **suspected erratum in the SO-GEN2 enclosure and in package R1**, not in a pinned source.

**Owner options.**
- **(a) Raise `M`** to at least 2.021 (for example 203/100) in `lunarR1`. Smallness stays far from binding:
  - `C₁e/(γ⁴ρ⁴)` becomes 0.0042 (lower) and 0.0081 (upper), against 0.0019 and 0.0037 now;
  - the `C₂` ratio becomes 7.0e-4.
  - The only parameter that changes is `M`. Since `𝔪 = max(M, σK, σB, σT)`, the margins against the threshold
    (532× and 273×) shrink by about the ratio of the `C₁` values.
- **(b) Lower the time scale `c`.** This is not recommended: it moves every other margin, and `c` is pinned in
  LunarParams.
- **(c) Change `hamBoundsOk`** to a row-max form for `D²H`. This would need a different NormBridge; it is a design
  change.

## What exists now (for the restart after the ruling)

### The mirror: `scripts/spin_orbit/sofx_*.py`

This is a backend-generic transcription of the landed checker for `CertFixed P` and `ℚ`. It replaces the
structure-only ℚ toy mirror for production data.

| file | transcribes |
|---|---|
| `sofx_arith.py` | Arith/{Interface, Rat, Fixed (floor `mul`, ceiling `upMul`, `mulErr = 1 ulp`), PiHigh, PiEnclosure, Roots, ComplexExp, Mantissa} |
| `sofx_model.py` | Model/{Basic, Terms, Ops, ExpBounds, Exp, Inv}, Expr/{ComposeModels, Compose}, Poly/{Basic, Ops} |
| `sofx_check.py` | Gram, Torsion/{Frame, Models, Average}, Positivity, Defs (all eight sub-checks), SpinOrbit/Graph/Cert (`checkSoGraph`) |
| `sofx_packed.py` | the **landed** Poly/{Packed, Layout, Advice, MulPacked} bodies, plus the advice generator (box, `outLog`, `scale` against the exact landed `remainderBound`) |
| `sofx_lunar.py` | the R1 certificate objects from `<which>_rot.json`, with params `lunarR1 err disp` and box `lunarR1Box` |

### Run status

| sub-check | lower | upper | note |
|---|---|---|---|
| `checkStatic` | PASS | PASS | ray margin 8.96e-7. With weight `w` = `ratExpUp` rounded up at 1e-30, the weight margins are 6.4e-31 and 5.3e-31. |
| `checkHamBounds` | **FAIL** | **FAIL** | see above |
| `checkEmbedding` | PASS | PASS | `DK` margin 0.6204 / 0.6203; ι margin 1.64e-5 / 1.53e-5; action margin 2.99e-5 / 3.44e-5 |
| `checkSmallness` | PASS | PASS | `C₁` ratio 0.0019 / 0.0037; `C₂` ratio 4.8e-4 at `disp = 10⁻³⁹` |
| `checkInvariance`, `checkEnergy`, `checkGram`, `checkTorsion`, `checkSoGraph` | not run | not run | stopped at the failure, per the brief |

### Findings from transcribing the landed checker (inputs for SO-DATA-2 and the owner)

1. **The cfgLow factors are full precision.**
   - Gram and torsion multiply the `dkModels` straight from the embedding (`ofDeriv`, no `trim`, no truncation).
     These are about 8.5k terms with 320-bit mantissas, so `toMants` needs `P = 320` for every product.
   - SO-GEN2, SO-ADVCOUNT and SO-DATA-PY modelled cfgLow as 72-bit trimmed factors of 212–466 terms, so their
     125-product volume and kernel estimates do not apply.
   - Expect about 50–60 products with one 8.5k-term factor (Gram `DKᵀDK`, `N`, `DG`, `DN`), each about as costly in
     the kernel as the three full products. The `cutoff` truncates only the outputs.
   - The advice volume is probably still below the 50 MB cap, because tails round to zero under a ~1e-6 cfgLow
     budget: the Gram margin needs δ ≲ 4e-4. The kernel time is roughly 1–3 CPU-h per torus.
   - This needs measuring once the run proceeds.
2. **`mulPacked` returns `tRR ++ tII ++ tRI ++ tIR` unmerged.** By parity only one part is nonzero, and its target
   terms are in ascending key order, so downstream merges stay complete.
3. **Zero real parts are free.** `packedRealProduct` returns `([], 0)` before reading the advice, so the generator
   emits a placeholder for them (SO-DATA-PY's "×4 shards" concern is gone).
4. **The landed `shardFits` bounds only the first `s+1` blocks,** and `inBox` is a digit test. `sofx_packed.py`
   follows the landed bodies.
5. **Keys `[5, a, l]` and `[4, 10, …]` are never looked up.** `freqModel` is constant and takes the scalar route.
   This confirms the SO-TEST-B audit (N1). The mirror records lookups only on the genuine route.
6. **The `π` enclosure** is Machin `(k, j) = (72, 21)`. Its width is about 1e-100, so every `toDeg` gap is far
   below `err`. The centre is `ofRatDown` of the midpoint, and the radius is the half-width plus 4 ulp.
7. **`certBallSquareIter` evaluates `certBallSquareIter b s` twice per level** (exponential in `s` without
   sharing). This is harmless at `pinHalvings = 0`, but a kernel hazard for larger `s`.

## Deviations and errata

- **Suspected erratum, not in a pinned source:** SO-GEN2's `‖D²H‖` majorant 1.047601
  (`lower_rot.json` `enclosures.norms.H`). It is below the landed `Σ_{a,b}` form (1.06568 at c = 1), so package R1's
  `M = 1987/1000` cannot be certified.
- **Data convention:** `lower_rot.json`'s `J_cos` is at scale `scale_bits` (318), not `J0_scale_bits` (319). See
  rot_emit.py:122. The builder uses 318.
- **Unverified inputs:**
  - The jet comes from `adv_jet.py`, the Python mirror of the compiler. Diff* has no changes since `074bd0c5`, but
    the jet was not extracted from Lean.
  - The Gram witness parity (B12 is i·odd) is inferred from symmetry.
