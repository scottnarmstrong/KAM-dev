# SHARP2-C8DFIX: the hybrid producer and mirror aligned with the Lean checker

Branch `sharp-c8dfix` from `sharp-v2` at d13b5a17 (main with the hybrid certifier). Python first; three small Lean probes,
each under 4 GB. No kernel test was built.

## Outcome

- **The mirror is now a port of `checkHybrid`, cross-checked against Lean.** `hybrid_xlang.py` evaluates 45 cases (the
  two accepted files and 43 mutations) with the mirror and with `#eval` of the Lean definitions. **All 45 agree, group by
  group.**
  - 108 exact intermediate values agree as strings.
  - Boundary pairs pass both ways: a claim at its exact Lean value is accepted, and 10⁻⁴⁰ below it is rejected. This holds
    for all seven step bounds, `dE0`, `σT`, `bT`, and each weight at 10⁻⁴⁰.
  - On T2 the complete Lean `checkHybrid` agrees on every case.
- **F1 fixed.**
  - Weights are now checked as Lean checks them: `ratExpUp (2·piUpQ·ρ) s N ≤ w`, with `0 < ρ` and the strip checks of
    `hybWeightsOk`.
  - The producer's weights pass at `(8, 24)` and at `(12, 30)`.
  - T2's weights are now exactly those of the Lean test `Hybrid/Tests/T2.lean`.
- **F2 fixed.** The real-torus torsion uses `d1R`, `d1tR`, and λ₁ uses the invariance error. AUDIT-C8C-1's counterexample
  gives `tA = 503/100000` in both languages.
- **New finding, fixed: R1 failed `hybCauchyOk`.**
  - The checker's Cauchy bound is `dE0 ≥ n·err/(ρ − ρT) = 3.63·10⁻³`. The v1 file supplied the measured
    ‖DE‖ × 1.10 = 1.97·10⁻⁴; AUDIT-C8C-1 did not run this check on R1.
  - The producer now writes the bound itself. It enters the torsion (m·t_A^ext rises from 0.001 to 0.007) and costs
    0.001 decades.
- **R1-L8 hybrid margin from the aligned mirror: +0.471.** The restarted error is e₁ = 5.191·10⁻¹², against
  e₁* = 1.535·10⁻¹¹. The v1 mirror reported +0.472; the plain run's margin is still −5.444.
  - R1 passes every ported check at the declared settings, at SO's `(12, 30)` with Machin `(72, 21)`, and at the
    worst-case Machin `(0, 0)`.
  - T2 passes at +35.770, unchanged.
- **H0–H4 on R1 confirmed in the kernel.** `r1HybA_transfer` (`transferOk`, by `decide +kernel`) takes 3.5 s at 1.87 GB.
- **Also in the kernel: the step bounds on R1's nonzero step.** `r1HybA_poly` (`hybPolyOk` on `r1HybStep`) takes 17 s at
  3.37 GB. This is the first kernel run of the step machinery on a nonzero step, which C8c had listed as untested.

## Files

| File | Change |
|---|---|
| `scripts/apost_sharp/hybrid_mirror.py` | rewritten (546 lines): the port of `checkHybrid` in the rational backend (below) |
| `scripts/apost_sharp/hybrid_numq.py` | exactness: Lean's totalized division (`qdiv`, x/0 = 0) in `CB`, `caS`, `budgetOk`, `c2Q`, `c3Q`, and natural-number exponents (`nsub`) as in `RouteAQ.lean` |
| `scripts/apost_sharp/hybrid_producer.py` | format v2: Lean weights, Lean step bounds, the Cauchy `dE0`, the ported transfer, `base.cert`, a mirror check before writing; the Lean data module also gets `r1HybBaseParams`, `r1HybBaseClaim`, `r1HybW1`, `r1HybWinf`, `r1HybWT` |
| `scripts/apost_sharp/hybrid_xlang.py` | new (512 lines): the cross-language regression |
| `docs/campaign/design/hybrid/format.md` | v2 (owned by C8d): changes list, `base.cert`, §5 organised as `checkHybrid`, kernel-only list, §8 regression |
| `docs/campaign/design/hybrid/hybrid-T2.json`, `hybrid-R1-L8.json` | regenerated (v2) |
| `docs/campaign/design/hybrid/xlang-lean.json` | new: the recorded Lean results of the regression (verdicts, values, probe costs) |
| `kernel-tests/CertificateSharp/V2/HybridR1L8Data.lean` | regenerated (547 lines, ≤ 100 characters) |
| `kernel-tests/CertificateSharp/V2/HybridR1L8Aligned.lean` | new, unbuilt (90 lines): `r1HybA_transfer` and `r1HybA_poly`, every number read from the data module |

## Approach

**1. The port.** Each Lean definition is transcribed one for one, in the rational backend (`instCertArithRat`: every
rounding error is 0, and `ofRatUp`, `ofRatDown` are the identity).

| Lean | Mirror |
|---|---|
| `piLoQ`, `piUpQ`, `atanS`, `piLowRat`, `piUpRat`, `piLowPos`, `piUpMin`, `twoPiZpowLo/Hi`, `degFactorUp` | same names |
| `ratExpUp q s N`, `checkWeight` | `rat_exp_up`, `check_weight` (below) |
| `toSortedPoly`, `weightedNormUp` (= `supNormUp`), `supBound`, `realCompModel`, `ofDeriv`, `toDeg`, `compDerivModel`, `stepModel`, `dstepModel`, `sumsOk` | `sorted_terms`, …, `sums_ok` |
| `hybWeightsOk`, `hybPolyOk`, `hybCauchyOk`, the d_ω check | `hyb_weights_ok`, `hyb_poly_ok`, `hyb_cauchy_ok`; one named entry per conjunct |
| `FrameQ`, `dABQ`, `StepNumQ.{e1, frS, frR, wB, lam0, lam1, t1, tA, sK1, sB1}`, `IsoNumQ.{e1, tAext}`, `HybWit.{kq, qq, δ1, ρT, tAx, t1, mT}` | `hyb_numbers` |
| `transferOk` | `transfer_ok`: the 35 conjuncts, named as the fields of `TransferFacts` |
| `refinedCoreR` | `hybrid_numq.py`, plus `classicalOk` (`zetaUp`, `shellUp`, `epsUp`, `radUp`) |

- **`ratExpUp`.** The squarings reach about 74 000 digits at `(8, 24)` and 1.7 million at `(12, 30)`. The Taylor sum is
  reduced once; its 2^s-th power is then automatically reduced, so no gcd of the large powers is taken. Comparisons are
  by cross-multiplication.
- **Sites.** With `"reuse-base"`, the restarted run's `sitesOk` equals the base run's when n, τ, kp, ρ, ρ∞, c, c̄, J, κ,
  γ and the box agree; the mirror checks these equalities exactly. The base run's sites are certified in Lean (T2's test;
  R1's `r1R_sites` in kernel-tests).
- **Kernel-only.** `hybOmegaOk` (`o0`, `o0R`, `o1`, `o1R`) and `hybCompOk` (`lE`, `lH`) need the base certificate's
  composition machinery. The mirror reports them as kernel-only rather than assuming them.

**2. The producer.**
- **Weights.** w = the larger of `ratExpUp` at the declared settings and at `(12, 30)`, rounded up: to an integer if
  w ≥ 100 (T2, as the Lean test does), else to 10⁻¹⁵.
- **Polynomial claims.** The Lean bounds computed at Machin `(0, 0)`, the loosest `twoPiZpowHi/Lo`, so they pass for any
  π enclosure; rounded up to 13 significant digits.
- **`dE0 = dE0R`.** `rup(n·err/(ρ − ρT))`.
- **Restart numbers.** From `hyb_numbers`.
- **Self-check.** The file is checked by the mirror before it is written.

**3. The regression** (`hybrid_xlang.py`).
- **Cases.** 15 T2 mutations aimed at single checks (weights, strips, Cauchy, ν, disp, sK, bT, err, s₁, d₀ < 0, X⋆ = 0,
  μ₁) and 28 R1 mutations (boundary pairs, C8d's old weights, the WT radius).
- **Lean side.** It generates two probes (`.drafts/c8dfix/xlang/`). They `#eval` `transferOk`, `hybWeightsOk`,
  `hybPolyOk`, `hybCauchyOk`, the d_ω check, the six conjuncts of `refinedCoreR` other than `sitesOk`, and for T2 the
  complete `checkHybrid`.
- **R1 stub.** R1 uses `{ toyCert2H with params, freqBox, weight, expHalvings, expOrder, piEnc }`. These sub-checks read
  only those fields.
- **Values.** The transfer numbers, step sup bounds, derivative matrices and `ratExpUp` to 10⁻⁶⁰ are compared as strings
  on the accepted files. So are synthetic fixtures: every transfer field distinct and nonzero; a polynomial step with
  complex coefficients, degrees −1, 0, 2 and a missing component, at Machin (2, 1), (4, 4), (0, 0); and the audit's
  counterexample.
- **Modes.** `--lean` runs Lean; `--record` rewrites `xlang-lean.json`. Without `--lean` it compares the mirror with the
  recorded results.

## Decisions (overnight, conservative, recorded)

- **D1. R1's `base.cert` is assumed.** I used the toy's `expHalvings = 8`, `expOrder = 24` and Machin `(4, 4)`, as
  AUDIT-C8C-1 and C8c checked; R1's base certificate is not in Lean. The data do not depend on this choice: the weights
  also pass at SO's `(12, 30)`, and the polynomial claims pass at any Machin parameters.
- **D2. Format bumped to v2.** The meaning of the weights changed, so the version changed. The `real` weight was dropped
  (Lean's `realWeight` is built in). `step.rho1` and `step.mu1` are informational, because the checker reads `params1`.
- **D3. C8c's `HybridR1L8Transfer.lean` was not edited** (another package's tracked file; additive rule).
  - It hard-codes the v1 base `disp` and weights. With the regenerated data, its `transferOk` fails at `disp` only
    (requirement 1.61435·10⁻⁷ against the hard-coded 1.6107·10⁻⁷; the base `err` and base claim are unchanged, checked).
  - `HybridR1L8Aligned.lean` replaces it, and reads every number from the data module.
  - For the orchestrator: retire `HybridR1L8Transfer.lean`, or point its `r1BaseParams` and weights at `r1HybBaseParams`
    and `r1HybW1`, `r1HybWinf`, `r1HybWT`.
- **D4. C8d's `HybridR1L8.lean` and `HybridR1L8Core.lean` were not edited.** Every statement in them still holds on the
  new data (checked exactly):
  - `wfOk`, `okR`, `budgetOk`, `finalOkA`, the tail;
  - the margin pair (passes at 1.5·10⁻¹¹, fails at 1.55·10⁻¹¹ on the smallness, with three times `disp`);
  - the sites congruence (c, c̄, kp, J, κ, box equal to `r1RefinedWitR`'s).

  One docstring figure is stale: `X⋆ = 19934881/125` in `HybridR1L8.lean`, now `31783537/200`.
- **D5. Kernel-only claims stay floating × 1.10:** `lE`, `lH`, `o0`, `o0R`, `o1`, `o1R`.

## Checks (exact commands and output)

1. `cd scripts/apost_sharp && python3 -I hybrid_numq.py` → `validate: PASS` (the four kernel facts, after the
   exactness changes).
2. Producer, then a byte comparison of a second full run with the committed files:
   ```
     wrote …/hybrid-T2.json (4308 bytes)
     R1-L8: v^ 23, J^ 73, DK^ [125, 60, 149, 191] terms; e 3.927e-06 (analytic 3.927e-06); E_lin~ 4.713e-12, E1 sup 2.365e-12 (4s)
     wrote …/hybrid-R1-L8.json (74336 bytes)
     wrote …/HybridR1L8Data.lean (547 lines)
   same hybrid-T2.json
   same hybrid-R1-L8.json
   same HybridR1L8Data.lean
   ```
3. `python3 -I scripts/apost_sharp/hybrid_mirror.py docs/campaign/design/hybrid/hybrid-T2.json docs/campaign/design/hybrid/hybrid-R1-L8.json`
   ```
   == T2: PASSES the ported checks (expHalvings 8, expOrder 24, Machin (4, 4))
      groups: transferOk ok, hybWeightsOk ok, hybPolyOk ok, hybOmegaOk kernel-only, hybCauchyOk ok, hybCompOk kernel-only, dw ok, refinedCoreR ok
      plain run:  e = 3.207e-43, e* = 1.89e-07, margin +35.770
      restarted:  e1 = 3.207e-43, e1* = 1.89e-07, hybrid margin +35.770
   == R1-L8: PASSES the ported checks (expHalvings 8, expOrder 24, Machin (4, 4))
      groups: transferOk ok, hybWeightsOk ok, hybPolyOk ok, hybOmegaOk kernel-only, hybCauchyOk ok, hybCompOk kernel-only, dw ok, refinedCoreR ok
      plain run:  e = 4.319e-06, e* = 1.554e-11, margin -5.444
      restarted:  e1 = 5.191e-12, e1* = 1.535e-11, hybrid margin +0.471
      slacks: d0+mu1<=mu 0.00188, d1+mu1/2<=mu/2 1.6e-10, m tAx<1 0.993, sT 9.84e-14, bT 2.17e-13, params1.err 0, outer disp 2.48e-13
      exact step bounds (Lean's): d0 1.15438e-07, dinf 5.69204e-08, d0R 5.68815e-08, d1 5.92288e-06, d1t 4.42347e-06, d1R 2.72152e-06, d1tR 1.81021e-06
   ```
   With `--settings 12,30,72,21` and `--settings 8,24,0,0`, R1 also `PASSES the ported checks`.
4. On the v1 files (before the fix), the new mirror reproduces AUDIT-C8C-1: `checkWeight W1`, `Winf`, `WT` fail for T2
   and R1. It also finds `cauchy dE0` and `cauchy dE0R` failing for R1.
5. `python3 -I scripts/apost_sharp/hybrid_xlang.py --lean` (excerpt; every case line reads `agree`):
   ```
   lean probe XlangT2.lean: 12.8 s, peak RSS 3.76 GB
   lean probe XlangR1.lean: 12.8 s, peak RSS 3.78 GB
   lean: 45 cases, 108 values
     t2-ok                  mirror accept lean accept agree; full checkHybrid True (omega True, comp True, sites True)
     r1-ok                  mirror accept lean accept agree
     t2-w1-audit            mirror reject lean reject agree; full checkHybrid False (…)  [hybWeightsOk/rho1 <= W1.rho]
     r1-d1tR-exact          mirror accept lean accept agree
     r1-d1tR-below          mirror reject lean reject agree  [hybPolyOk/dstepOk d1tR]
     r1-weights-c8d         mirror reject lean reject agree  [hybWeightsOk/checkWeight W1; …Winf; …WT]
     r1-rho1-w-ceil40       mirror accept lean accept agree
     r1-rho1-w-floor40      mirror reject lean reject agree  [hybWeightsOk/checkWeight W1]
   values: 108 compared, 0 mismatches (accepted files: transfer numbers, step bounds, ratExpUp to 10^-60; synthetic fixtures)
   aud.tA (AUDIT-C8C-1 counterexample; Lean's value 503/100000): mirror 503/100000
   XLANG PASS (45 cases)
   ```
   Without `--lean` (against `xlang-lean.json`): `XLANG PASS (45 cases)`, exit 0.
6. Kernel probes. Each is a copy of `HybridR1L8Aligned.lean` with the data module inlined and one theorem, run as
   `nice -n 5 lake env lean`, one process at a time, under a watchdog that kills its own `lean` above 4 GB:
   - `.drafts/c8dfix/R1Transfer.lean` (`r1HybA_transfer`): exit 0, 3.53 s, peak 1.87 GB;
   - `.drafts/c8dfix/R1Poly.lean` (`r1HybA_poly`): exit 0, 16.96 s, peak 3.37 GB.
7. `sh scripts/lint_sources.sh` (exit 1, from the ABI step only, AUDIT-C8C-1 F3):
   ```
   check_lean_modules: PASS (1847 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   …/.lake/abi-scratch/tmp….lean:1:0: error: object file '…/KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean' of module KAM.Frozen.Planetary.Theo… does not exist
   ```
8. Names: `r1HybClA`, `r1HybStepA`, `r1HybWitA`, `r1HybA_transfer`, `r1HybPi`, `r1HybA_poly`, `r1HybBaseParams`,
   `r1HybBaseClaim`, `r1HybW1`, `r1HybWinf`, `r1HybWT` appear nowhere else in `KAM/` or `kernel-tests/`.

## `#print axioms` (probes)

```
'KAM.CertificateSharp.HybridR1Test.r1HybA_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.r1HybA_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Memory

- **The `#eval` probes' 3.76–3.78 GB is the import.** A bare `import KAM.CertificateSharp.Hybrid.Tests.T2` peaks at
  3.58 GB in this worktree; `Hybrid.Claims` + `RestartQ` + `Toy2Data` peak at 3.50 GB. Splitting the regression into two
  probes did not lower the peak.
- **The kernel probes import less.** They import `Hybrid.Claims`, `Hybrid.RestartQ` and `V2.Tests.Frozen`, and stayed at
  1.87 GB and 3.37 GB.

## Proposed rows for `kernel-tests/README.md` (for the orchestrator)

```
| `CertificateSharp/V2/HybridR1L8Aligned.lean` | the hybrid on R1's L = 8 candidate with the v2 data: `transferOk` (H0–H4) and `hybPolyOk` on the nonzero step (SHARP2-C8DFIX; imports `HybridR1L8Data` by module path) | 1.87 GB / 3.37 GB (inlined copies) | 3.5 s / 17 s |
| `CertificateSharp/V2/HybridR1L8Transfer.lean` | stale since format v2 (hard-coded v1 base `disp`): retire, or point it at `r1HybBaseParams` and the generated weights | — | — |
```

## Uncertainties

- **R1's base certificate is not in Lean.** Its settings are assumed (D1). `hybWeightsOk`, `hybCauchyOk` and the d_ω
  check on R1 are confirmed only by `#eval` on a certificate stub. `hybOmegaOk`, `hybCompOk` and the base checks wait for
  the certificate (format §7).
- **Kernel-only claims** are floating × 1.10. The restart tolerates e₁ up to about × 2.9 (the margin pair), and `lE`
  dominates e₁.
- **Rational backend only.** A rounded backend adds radii the mirror does not model (format §6).
- **R1's sites** are checked by reuse: exact equalities plus the base run's Lean certificate `r1R_sites`, which is in
  kernel-tests at 19.2 GB.

## Errata

None found in pinned sources. Deviations: D1–D5 above.
