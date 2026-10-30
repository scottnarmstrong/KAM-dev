# SO-GEN3: lunar tori for a band below 3 % under the sharp certifier

Branch `inp-sogen3`. Python, data and Markdown only; no Lean file touched or built.

## Interim answer (30 October 2026; quick study, numbers to be replaced by the full study below)

**Yes: a band below 2.9 % looks certifiable.** All tori up to N = 65 exist on the full seven-term model, their
Fourier decay barely changes, and the sharp threshold sits about 25.5 orders below 1, so each torus needs only about
38–40 digits and roughly 1–2k terms. With the old certifier, R1 needed 88 digits and 8.5k terms.

| N | converged | lower torus p range | upper torus p range | **band max\|p−1\|** | gap between tori | k-decay (digits/mode) | width ρ_ψ | log10 thr/c (sharp, ρ = 1/70) | L (digits) | v half / E terms (proj.) |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---|
| 40 (R1) | ref. | 0.9676–0.9821 | 1.0179–1.0324 | 3.24 % | 0.0358 | 0.61 | 0.18 | −25.11 | ~38 | 704 / 1406 (measured, 440-bit data) |
| 50 | yes | 0.97099–0.98774 | 1.01227–1.02901 | **2.901 %** | 0.0245 | 0.52 | 0.19 | −25.48 | ~38 | ~820 / ~1650 |
| 55 | yes | 0.97185–0.98993 | 1.01008–1.02814 | **2.815 %** | 0.0202 | 0.48 | 0.18 | −25.64 | ~38–39 | ~890 / ~1770 |
| 60 | yes | 0.97245–0.99173 | 1.00828–1.02754 | **2.755 %** | 0.0166 | 0.45 | 0.17 | −25.79 | ~39 | ~960 / ~1910 |
| 65 | yes | 0.97287–0.99322 | 1.00678–1.02713 | **2.713 %** | 0.0136 | 0.42 | 0.16 | −25.92 | ~39–40 | ~1020 / ~2040 |

**How each column was obtained.**
- **(a) Convergence.** Double continuation in ε (40 steps) plus Newton–GMRES on a 256×64 grid
  (`g3_double.py`; `model.py` now reads `SO_N`). Every run converged, with final projected residual 3–8e-14 and
  4–7 min per torus. ν± = 1 ± 1/(N+g) = 1 ± (2N−1−√5)/D, D = ((2N−1)²−5)/2.
- **(b) The band.** It is the max of |p − 1| on the grid of the numerical torus. disp is about 1e-14 relative
  (see (d)), so it is negligible. The two tori are symmetric to 1e-5. The separatrix floor is 2.62 %.
  - The N = 50 band of 2.901 % only touches 2.9 %.
  - **Below 2.9 % needs N ≥ 51 or so. N = 55 gives 2.82 %, N = 60 gives 2.76 %, N = 65 gives 2.71 %.**
- **(c) Width and decay.** I fitted max_l |b_{k,l}| against |k|.
  - The ψ-decay slows only mildly, from 0.61 digits per mode (N = 40) to 0.42 (N = 65).
  - So the width in ψ is about 0.16–0.19 in every case. The φ-decay is unchanged at about 2 digits per mode.
  - The certificate strip ρ = 1/70 ≈ 0.014 is far inside the width for every N. Analyticity is not the
    constraint.
- **(d) Threshold.** This is an exact transcription of the landed `sharpTest` (`sharp_q.py`, from
  `ConstantsQ.lean`; at the landed R1 it gives 10^−27.89) at an R2-like package (`g3_package.py`):
  - M = c × 1.0657 (the landed D²H sum per unit c);
  - σK, σB, σT from SO-GEN2's measured ‖DK‖ = 1.3604, ‖G⁻¹‖ = 1.9799, ‖avg⁻¹‖ = 1.0225/c, each plus μ;
  - μ = 1/160, ρ∞ = ρ/1000, ν = 1e-6;
  - γ = γ̄ = c/((N+1)s). The binding mode is k = (1, 0), with γ((ν−1, 1)) = 1/(N+g) > 1/(N+1); R1's 1/42 is the
    N = 40 case.

  The quantity that matters is threshold/c, because err ≈ c·η. It is flat for c ≥ 4, with active branch E. The
  displacement coefficient is about 10^12, so disp ≈ 1e-14 at err = 1e-26.
- **Digits and terms.** On R1, SO-GEN2 measured c·η ≈ 10^(−L+10.3) at truncation 10^−L. With 2 orders of headroom
  that gives L ≈ 38 (N = 50) to 40 (N = 65), and about 3.33L + 24 ≈ 150–160 bits. The term counts are N = 40's
  measured counts at L = 38, scaled by the ratio of ψ-decay rates.

**Plausibility.** Every number in (d) depends on majorants measured on the N = 40 tori. The D²H, DK and Gram
values should change little, because the tori differ by less than 1 % in p and the decay is similar, but they still
have to be re-enclosed.

Against R1 under the old certifier (88 digits, 4.2k / 8.3k terms, about 70M product pairs), N = 55–65 needs:
- about 40 digits;
- about 1–2k terms;
- about 3–4M pairs, roughly 20× fewer.

Even at N = 65, the certificate should be **much cheaper than the R1 certificate the SO track already sized**.

**Caveats (interim).**
- All counts are projections, not measured truncations.
- The width uses a 256×64 double grid with a noise floor of about 1e-17.
- The η–L offset of 10.3 may grow by about 1 digit at N = 65, because the cutoff shell sits at larger |k|.
- The package uses N = 40 majorants.
- Each new N needs its own Diophantine lemma (γ = 1/(N+1) in the rotated frame).

**Interim recommendation.** Primary **N = 55 (2.82 %)**; stretch N = 60 (2.76 %). N = 50 gives 2.90 % and does

## Interim 2: beyond N = 65 (30 October 2026)

**N = 80 and N = 100 converge, but the gain in band is small and the cost grows fast.** The band approaches the
separatrix floor (2.62 %), while the gap between the tori, which is the initial window the theorem covers,
collapses.

| N | converged | lower p range | upper p range | **band** | gap (window) | ψ-decay (digits/mode) | width ρ_ψ | ‖DK‖ | ‖G⁻¹‖ (ℓ¹) | log10 thr/c | L | bits | v half (proj.) |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 65 | yes | 0.97287–0.99322 | 1.00678–1.02713 | 2.713 % | 0.0136 | 0.42 | 0.16 | 1.865 | 5.36 | −32.17 | 40 | 158 | 1180 (measured) |
| 80 | yes | 0.97348–0.99632 | 1.00369–1.02651 | **2.652 %** | 0.0074 | 0.35 | 0.13 | 2.275 | **12.06** | −36.32 | ~44 | ~171 | ~1740 |
| 100 | yes | 0.97370–0.99841 | 1.00160–1.02630 | **2.630 %** | 0.0032 | 0.28 | 0.10 | 2.874 | **40.55** | −42.10 | ~50 | ~191 | ~2820 |

**How each column was obtained.**
- **Method.** Same method as the interim table (256×64 double continuation, residual 1e-13), then a 360-bit
  Newton stage on 256×64, then `rot_emit` at ρ = 1/140.
- **Majorants.** ‖DK‖ and ‖G⁻¹‖ are enclosed on the actual N = 80 and N = 100 lower tori (L = 32 and 26).
- **Threshold.** It is the landed `sharpTest` mirror at c = 2, ρ = 1/140, γ = κ/(N+2) (SO-DION), σT = 13/25.
- **Digits.** L = −log10(thr/c) + (the η offset measured at each N: 5.6, 5.3, 5.2) + 2 orders of headroom.
- **Terms.** Each count is the measured count at the emitted L, plus the measured growth per digit scaled by the
  decay rate.

**Findings.**
- **The Gram inverse is the cost driver.** ‖G⁻¹‖ goes 1.98 → 2.89 → 3.59 → 4.55 → 5.85 → 12.1 → 40.5 for
  N = 40, 50, 55, 60, 65, 80, 100: roughly ×1.27 per 5 in N. Because the sharp constants are high powers of σB, the
  threshold falls 4 orders from N = 65 to N = 80 and 10 orders to N = 100.
- **Still feasible in size.** About 44 and 50 digits and 1.7k and 2.8k v half-terms. That is below R1's 88 digits
  and 4.2k half-terms, but well above N = 65 (40 digits, 1.2k).
- **The data need a finer grid.** The 256×64 stage aliases at 1e-37 (N = 80) and 1e-29 (N = 100), which is short
  of L = 44 and 50.
  - The 512×128 chord stage stalled (GMRES) at N = 65, so it needs a fix first, for example a stronger
    preconditioner or a 384×96 grid.
  - This is a tooling issue, not non-convergence.
- **Largest converging N.** At least 100; I did not search further. Every tested N converges in double precision
  with residual ≤ 1.5e-13.
- **Gain against cost.** N = 65 → 80 gains 0.06 points (2.71 → 2.65 %), and N = 100 another 0.02. Meanwhile the
  confined window (the gap) shrinks from 0.0136 to 0.0074 and 0.0032.

**Recommendation.** N = 65 is a good stopping point. N = 80 is possible as a stretch, at about 4 more digits,
1.5× the terms and a fixed grid stage. N = 100 is not worth it: 0.02 points for 10 orders of threshold.
not clear "below 2.9 %".

## Full study: N = 65 (decision D38), with N = 60 as the fallback

**Verdict.** Both N = 65 tori pass **all seven unchanged sub-checks of `checkTorusCertificateSharp`, `sharpTest`
and `checkSoGraph`**. They were run in the fixed-point mirror of the landed checker (`sofx_gen.py`, `CertFixed 160`,
GENERATE and then a fresh CHECK pass with the emitted books). The sub-checks are `checkStatic`, `checkHamBounds`,
`checkEmbedding`, `checkInvariance`, `checkEnergy`, `checkGram` and `checkTorsion`.

- **Certified band: max |p − 1| = 2.755 %.**
- **Headroom:** err/threshold = 10^−2.34 (lower torus) and 10^−2.26 (upper torus).
- **No final certificate data generated**, as instructed. The mirror's GENERATE output stays in scratch and is not
  committed.

### Package R2 (exact; `scripts/spin_orbit/g3_r2.py`)

| field | value | justification (landed form, sofx mirror on the actual tori) |
|---|---|---|
| time scale c | 2 | threshold/c is flat for c ≥ 2 (±0.03 orders) |
| ρ, ρ∞ | 1/140, 1/140000 | ρ = 1/140 beats 1/70 by 0.85 orders (threshold −0.6, η +1.5 orders) and 1/100 by 0.2 |
| M | 54/25 = 2.16 | `checkHamBounds` max 2.1191 (the D²H sum); margin 0.041 |
| σK | 1873/1000 | DK rows 1.86485 + μ; `dk_margin` 0.0019 |
| σB | 2689/500 = 5.378 | `checkGram` β = 5.36057 (ℓ¹); margin 0.0112 |
| σT | 13/25 | `checkTorsion` ‖S‖ = 0.50406, δ_T = 2.7e-5; margin 0.0097 |
| μ, ν, s, σω | 1/160, 1e-6, 1 + 1e-6, 2 | as R1 |
| γ = γ̄ | κ/67, κ = c/s | SO-DION: IsDiophantine (κ/(N+2)) 1 |
| domain | ρ_H = 979/50000; P₁ disc 24619/25000 ± 49/2500 (lower); P₂ disc 49981/100000 ± 159/25000 | `rot_norms`; `checkEmbedding` room 0.0062 |
| cfgFull / cfgLow | cutoff 100000 / **160**, Taylor 30, halvings 12; packed budgets 1e-36 / 1e-8 | at cfgLow cutoff 30–80 `checkTorsion` FAILS (see below) |
| **threshold** | **10^−31.827**, active branch E; disp ≥ 10^15.583 · err | `g3_r2.threshold` → `sharp_q.sharp` (ConstantsQ.lean transcription) |

**Re-running for a new certifier.** `threshold(p)` in `g3_r2.py` is the only threshold function. It calls
`sharp_q.sharp`, so a new constant set means editing `sharp_q.consts` / `sharp` and re-running
`python3 g3_r2.py 6.8e-35 8.17e-35`. The majorants above are certifier-independent.

### Measured truncation (L = 40, both tori; S = 158 bits, checker precision 160 bits)

| | lower | upper |
|---|---:|---:|
| v terms half / full | 1180 / 2360 | 1165 / 2330 |
| E terms | 2336 | 2328 |
| p half, J half | 1180, 1233 | 1165, 1219 |
| invariance rows (checker) | Q1 9.2e-43, P1 **6.79e-35**, P2 2.03e-35 | 9.9e-43, **8.16e-35**, 2.09e-35 |
| energy | 1.2e-36 | 9.9e-37 |
| err (rows × 1.001, 3 digits) | **6.8e-35** | **8.17e-35** |
| disp | 2.61e-19 | 3.13e-19 |
| err / threshold | 10^−2.34 | 10^−2.26 |
| packed products / shards / nonzero advice | 129 / 1230 / 61,767 | 129 / 1229 / 62,960 |
| slot width w (max) | 337 bits | 337 |
| mirror wall time (GENERATE + CHECK), peak RSS | 21.8 min, 0.50 GB | 21.8 min, 0.50 GB |

- **Truncation scan.** I scanned L = 32–42 at ρ = 1/70 (`so-gen3-data/N65_scan_rho70_*.jsonl`). η falls about 0.9
  orders per digit. At ρ = 1/140 the offset is η ≈ 10^(−L+5.5).
- **Minimum feasible L.** About 38 with no headroom. L = 40 follows SO-GEN2's two-order rule.
- **Against R1 under the old certifier** (L = 88, 318 bits, 4.2k/8.3k terms, 70M v×E pairs), R2 needs:
  - 40 digits;
  - 158 bits;
  - 1.2k/2.3k terms;
  - 5.5M pairs (13× fewer).

### Product families (per torus; blockRows 32)

| family | n | factor terms | blocks | shards |
|---|---:|---|---|---:|
| cfgFull `[0,10]` p̃·p̃ | 2 | 2361 × 2361 | 8 × 8 | 30 |
| cfgFull/cfgLow `[1,0,j]` witness | 4 | 2252–2322 × 2336 | 8 × 8 | 60 |
| cfgLow `[3,0]` Gram DKᵀDK | 9 | 2252–2322 × 2252–2322 | 8 × 8 | 135 |
| cfgLow `[4,1]`, `[4,2]` (DL × DK, torsion) | 24 | 2252 × 2252–2322 | 8 × 8 | 360 |
| cfgLow `[4,0]`, `[4,5]`, `[4,6]`, `[4,7]`, `[4,9]` (big × small) | 50 | 2252–3677 × 190–401 | 8 × 2–3 | 481 |
| cfgLow small × small (`[3,1]`, `[4,3]`, `[4,4]`, `[4,8]`) | 40 | 183–401 | 2–3 × 2–3 | 164 |
| **total** | **129** | | | **1230** |

**Shard pairs and the heavy count.**
- The 8 × 8 products give 15 shards each, with at most 8 block pairs per shard (R1: 12 × 12, 23 shards, 12 pairs).
- 39 products are DK-sized on both sides, against R1's 63 with an 8.5k-term factor.
- The cfgLow cutoff of 160 is what makes the `[4,1]`/`[4,2]` torsion products full-size.

### Kernel-cost projection (from SO-PACKFIX: one 32-row shard of 12 block pairs at 320 bits ≈ 45 s, 4.6 GB)

**Packed shards.**
- Our shards carry at most 8 pairs, at w ≈ 337 bits against about 659.
- Scaling linearly in pairs, and between linearly and quadratically in width, gives **≈ 8–15 s and ≲ 2.5 GB per
  shard**.
- For 1230 shards per torus that is **≈ 3–5 CPU-h per torus, about 6–10 CPU-h for both**. The upper bound at
  45 s per shard is 15 CPU-h per torus.
- Per-declaration overhead for about 1230 shard theorems per torus comes on top.

**Model evaluation (`Slp.compose`, SO-DATA-1's main memory risk).**
- The live models are 2.3k terms at 160 bits, against 8.5k at 320.
- That is about 7× less term data than R1.
- This is a projection, not a measurement.

### Certified graph bands (`checkSoGraph`, both pass)

| torus | mono | pLo | pHi | disp | [pLo − disp, pHi + disp] | max \|p − 1\| |
|---|---|---|---|---|---|---:|
| lower ν₋ = 1 − 1/(65+g) | 0.1353683 | 0.9724531 | 0.9935293 | 2.6e-19 | [0.9724531, 0.9935293] | 2.7547 % |
| upper ν₊ = 1 + 1/(65+g) | 0.1353116 | 1.0064780 | 1.0275440 | 3.1e-19 | [1.0064780, 1.0275440] | 2.7544 % |

- **Certified band: |p − 1| ≤ 2.755 %.** The numerical torus extremes give 2.713 %. The 0.04-point gap is the
  graph-certificate slack: `sofx_gen` asks the SOS lower-bound witness for a 3e-4 margin.
  - Tightening that slack, for example to 3e-5 with more SOS terms, would bring the certified band to about
    2.72 %. This is a lever, not done.
- **Barrier separation (the confined window):** (0.9935293, 1.0064780), width 0.0129. The tori are separated.
- **mono.** It is 0.135, against 0.64 at N = 40, so the graph map ψ ↦ ψ + v/2π is much less uniform near the
  separatrix. It is still positive, with margin 3.6e-7 over the residual bound.

### Fallback N = 60 (ρ = 1/70, L = 39, c = 2, M 54/25, σK 1833/1000, σB 1141/250, σT 1, γ = κ/62)

- **Lower torus.** It passes everything at cfgLow cutoff 70: err 1.17e-32, threshold 10^−30.39, headroom
  10^−1.54.
  - That run used γ = κ/61. At κ/62, its disp 8.26e-18 is just below the new minimum: disp must be recomputed as
    10^14.86 · err ≈ 8.5e-18.
  - That is a one-line change with no effect on the bands.
- **Upper torus.** It passes everything at cutoff 160 with γ = κ/62: err 1.42e-32, disp 1.04e-17.
- **Bands.** Lower [0.97185, …], upper […, 1.02784]: about 2.82 % certified.
- **Not done.** A re-optimization at ρ = 1/140 with σT = 13/25, which would add about 1 order of headroom.

### What the landed checker would reject (found and fixed in the data/tooling, all mirror-verified)

1. **`checkTorsion` at the R1 cfgLow cutoff of 30**, and also at 40–80 for N = 65.
   - The truncation mass of the DL·DK products (`[4,1]`, `[4,3]`) is the cause. ψ-decay is slow near the
     separatrix: 0.42 digits per mode.
   - It gives a radius of r ≈ 21 and δ_T ≈ 11. **Cutoff 160 is required** (r = 5.4e-5).
2. **`checkEnergy` with a cfgFull packed budget below the fixed-point resolution.**
   - At 1e-42 with 146–160 bits, the advice builder cannot meet the budget and the crude fallback gives energy
     ≈ 1.96.
   - **Use a budget of 1e-36.**
3. **Gram witness parity.** For N = 55, rot_norms' approximate inverse B had parity-broken rounding coefficients.
   - `sofx_lunar.build_gram_inv` now projects onto the dominant parity. B is untrusted, and `checkGram` verifies
     whatever is sent.
4. **`checkSmallness` (the old certifier) fails at R2**, as expected: C₁ ratio about 1e62. Only the sharp
   certifier accepts R2.

### Tooling issues (not certificate defects)

- **The 512×128 chord stage of `run_hp.py` stalls (GMRES) at N = 65.**
  - The 256×64 stage (`SO_HP_STAGE1_ONLY=1`, residual 1e-105 projected and an alias floor of 1e-46) is ample for
    L = 40.
  - N = 80 and above needs a fix.
- **New scripts.** `sharp_q.py`, `g3_r2.py`, `g3_package.py`, `g3_double.py`, `g3_analyze.py`, `g3_torsion.py`.
- **Environment overrides** (defaults reproduce R1/N = 40 byte for byte):
  - barrier and data: `SO_N`, `SO_DATA_DIR`, `SO_RHO`;
  - precision: `SO_HP_BITS`, `SO_PBITS`, `SO_PREC`;
  - package and checks: `SO_PKG`, `SO_SHARP`, `SO_BUDGET_FULL`, `SO_CUT_LOW`, `SO_HP_STAGE1_ONLY`.
- **Data.** Reports, scans, the package and the driver shell scripts are in `docs/tracks/SO/studies/so-gen3-data/`
  (284 KB).
- **Reproduce N = 65.** Run the shell drivers in so-gen3-data:
  1. `hp1.sh 65`;
  2. `RHO=1/140 emit.sh 65 lower|upper 40`;
  3. `CUT_LOW=160 sofx.sh 65 lower|upper 160 pkgR2.json OUT`.
