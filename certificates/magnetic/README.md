# Magnetic field-line barrier at ε = 3/2500: certificate package for the packed-gate run

This package contains the certificate data for the analytic torus behind the frozen theorem
`KAM.Magnetic.magnetic_barrier`. The theorem is DRAFT_SORRY, frozen under D68 (main 1ec9073d). The
model is plan-magnetic-barrier §1.1 at ε = 3/2500. The data was generated on branch `mag-pilot` and
is untrusted: only the kernel decides. No Lean data chain has been emitted or built.

## Route

**v2 route A, refined branch, classical small-divisor sites.** The witness is
`Sum.inr (Sum.inr refinedWit)` of `checkTorusCertificateV2 routeAV2`. The A.L8′ variant and certified
sites are not used.

| Quantity | Value |
|---|---|
| `err` | 73/10²³ (7.3·10⁻²²) |
| `disp` | 511/10¹⁵ (5.11·10⁻¹³) |
| Threshold of the exact mirror at this package | 10^-19.19 (`mag_witness.json`, `log10_thr`) |
| Margin | err/threshold = 10^-1.94, so 1.94 decades |
| X* | 47/200000 |

**Refined claim** R (exact mirror values, rounded up):

| `dh` | `dx` | `d2x` | `d2h` | `bL` | `bN` | `bNt` | `bT` |
|---|---|---|---|---|---|---|---|
| 222/125 | 2123/1000 | 8301/100 | 4421/1000 | 469/200 | 1667/1000 | 339/125 | 1829/500 |

## Hamiltonian, parameters, frequency, strip

**Hamiltonian:** `KAM.Magnetic.magHamExpr` (`KAM/Magnetic/HamExpr.lean`, core). It uses only
`const`, `action`, `cosMode`, `add`, `mul` and `pow`; compiled, that is const/add/mul/char ops only.

  `H((q, φ), (p, J)) = J + h(p) + ε (cos a + cos b) + (1427/3200) ε² ((32000/2777) cos a − (96000/7669) cos b)²`,
  with `a = 2π(2q − φ)`, `b = 2π(3q − 2φ)`, `h(p) = p − ¾p² + ⅓p³ − p⁴/16` and `ε = 3/2500`.

**Backend:** `MagBackend = CertFixed 128` (`KAM/Magnetic/Params.lean`).

**Parameters:** `magParams err disp`:

| Parameter | Value |
|---|---|
| τ | 1 |
| ρ | 3/1000 |
| ρ∞ | 3/1000000 |
| M | 85 |
| σK | 9/5 |
| σB | 27/10 |
| σT | 11/5 |
| μ | 1/500 |
| γ = γbar | κ/10 |
| σω | 2 |
| νRay | 10⁻⁶ |
| s | s₀ = 500001/500000 |
| κ | 1/s₀ |
| E0 | 0 |

**Frequency:** `ω* = (α, 1)/s₀` with `α = (7913 − √5)/13618 = [0; 1, 1, 2, 1, 1, 2, 3, 1̄]`.
- `freqBox` is in `mag_cert.json`: coordinate 0 comes from a √5 enclosure at 10⁻¹¹⁰; coordinate 1 is exactly `(κ, 0)`, so the clock holds.
- `checkAlgBox` coefficients: `magCoeffs = [[7913κ/13618, −κ/13618], [κ]]`.

**Domain and strips:**
- The certificate strip is ρ = 3/1000. The Hamiltonian strip is `weightH.rho = 363/50000`.
- Action ball: centre (223/625, −2753/10000), radii (124/3125, 613/25000).
- The frozen theorem's strip is `complexStrip 2 (3/1000000)` (ρ∞).

**Embedding:** `K(θ) = (θ₁ + u, θ₂, p, J)`, with `u` odd (a sine series) and `p`, `J` even (cosine
series).
- `angleDeg = actionDeg = [0, 0]`.
- Character witnesses `E_m = exp(2πi m u)` under the normalized keys (2, 0) and (3, 0), pin order 70.
- Gram inverse witness with 48-bit mantissas.

## Fourier box sizes and support

| Series | Support | `|k|`, `|l|` |
|---|---|---|
| `u` (sin) | 749 half-keys | ≤ 140, ≤ 82 |
| `p` | 836 half-keys | ≤ 140, ≤ 82 |
| `J` | 822 half-keys | ≤ 140, ≤ 82 |
| `E₂`, `E₃` | ~1650 full keys each | |
| `B₁₁`, `B₁₂`, `B₂₂` | 1019 / 1017 / 1019 full keys | |
| SOS witnesses (pLo, pHi) | 447 / 429 terms | |

All series are truncated at weighted modulus `|c_k| e^{2πρ|k|₁} > 10⁻²⁶`.
- Configurations: `cfgFull` (cut-off 100000, Taylor 30, halvings 12, packed budget 10⁻²⁷) and `cfgLow` (cut-off 600, packed budget 10⁻⁸).
- Advice books: 99 `cfgFull` and 224 `cfgLow` keys.
- Key coverage: `cfgFull` emitted = looked up. `cfgLow` looked up one key more than it emitted, with no misses; this is the same pattern as the lunar data.

## Graph data (`checkSoGraph`)

- `mono = 0.5689913` (mean form, no SOS). `pLo = 0.3261223`, `pHi = 0.3876199`; both lie inside the frozen bounds 8/25 ≤ P ≤ 39/100.
- Strict margin: `disp = 5.11·10⁻¹³ < mono·ρ∞ = 1.7·10⁻⁶`.

## Mirror verdicts

These come from the bit-exact Python mirror of the landed checker (`scripts/spin_orbit/sofx_*`). `mag_report.json` has the full detail.

| Check | Value | Result |
|---|---|---|
| checkStatic | | ✓ |
| checkHamBounds | D²X 83.0 ≤ M = 85 | ✓ |
| checkEmbedding | | ✓ |
| checkInvariance | rows 1.24·10⁻²³, 0, 7.29·10⁻²², 4.61·10⁻²² ≤ err | ✓ |
| checkEnergy | 3.3·10⁻²³ | ✓ |
| checkGram | margin 0.22 | ✓ |
| checkTorsion | margin 0.23 | ✓ |
| checkSoGraph | | ✓ |
| hamClaim | | ✓ |
| frameMajorants (L, N, T, Ω) | | ✓ |
| refinedCore (Xs, wf, okB, tail, final) | | ✓ |
| checkSmallness (v1 only; replaced in v2 by the refined route) | | FAILS |

Cost: GENERATE + CHECK took 3 h 19 min wall and 1.06 GB RSS (single thread, nice 10); the witness took 30 min.

## Files

| File | Contents |
|---|---|
| `mag_cert.json` | The certificate in sofx JSON (mantissas m denote m/2¹²⁸): params, ham, weights, box, embedding, witnesses, gramInv, torsInv, cfgs, π enclosure, graph |
| `mag_advice.json` | The packed-product advice books `cfgFull`, `cfgLow` (run-length windows) |
| `mag_witness.json` | The routeARefined witness (R, Xs, caps, sites, c, cbar, …) and the exact claim values |
| `mag_report.json` | The mirror report: every check, the product table, key coverage |
| `mag_rot.json` | The truncated Fourier data the certificate was built from (`scripts/magnetic/mag_cert.py`, from the 256-bit solution) |
| `design_thresholds.json` | Phase-1 sampled route thresholds (design evidence only) |
| `SHA256SUMS` | Checksums of the JSON files |

## Reproduction

The producer and the mirror client live on mag-pilot.
- Producer: `scripts/magnetic/{mag_producer, mag_cert, sofx_mag, mag_witness}.py`.
- Mirror: `scripts/magnetic/run_mirror.sh` (`SO_CLIENT=sofx_mag SO_PREC=128 SO_BUDGET_FULL=27 SO_CUT_LOW=600 SO_DISP_COEF=7e8 sofx_gen.py mag`).
- Witness: `scripts/magnetic/run_witness.sh`.

## Notes for the packed route (lemma.farm lessons, root-b8)

- State the consumers at the jet literal, not `c.ham.jet`.
- Reuse the built jet bridge and the Hamiltonian-bounds modules.
- Cap segments at 13 nodes for Full and 40 for Low.
- The jet program is the compile of `magHamExpr` (`adv_jet.jet(2, sofx_mag.mag_ham_expr())`). It has four
  character ops that resolve witnesses or reflections: keys (2, 0) and (3, 0), plus their reflections
  through the cache. The products of `pow` and of A² are packed.
