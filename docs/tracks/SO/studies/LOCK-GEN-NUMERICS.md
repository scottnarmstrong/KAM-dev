# LOCK-GEN numerics (D45, phase 1): periodic orbit and the N = 65 librational torus in polar coordinates

**Status:** 30 October 2026. Untrusted Python tooling (`scripts/spin_orbit/lock_po.py`, `lock_hp.py`). These are
design numbers, not certificates. The model is the exact seven-term model of `model.py` / `KAM/SpinOrbit/Model.lean`
(ε = 69/200000, e = 549/10000). Data: `/mnt/HC_Volume_106379410/kam-data/so-lock/`.

## 1. Synchronous periodic orbit ψ*(φ)

ψ* is odd and 1-periodic: ψ* = Σ_l ψ_l sin 2πlφ (turns). It is solved by mpmath Newton–Galerkin (K_PO sine modes,
M = 256 collocation points). Every run converges quadratically.

- ψ_1 = −1.1999·10⁻⁵, ψ_2 = −3.50·10⁻⁷, ψ_3 = −1.77·10⁻⁸. Decay ≈ 1.6 decades per harmonic, in steps of five
  (forcing harmonics). |ψ_64| ≈ 10⁻¹⁰⁶, max |ψ*| = 1.1989·10⁻⁵ turns. The 64 coefficients are stored to 64 digits in
  `po_K64*.json`.
- **Radii polynomial** in two-sided weighted ℓ¹ (weight e^{2πν|l|}). A = J_K⁻¹ ⊕ (−1/l²). The Z₁ and Z₂ bounds are
  crude (formulas in the `lock_po.py` docstring). r_max = 0.01 in V = 2πψ units.

| K_PO | bits | ν | Y₀ | Z₀ | Z₁ | Z₂ | r interval (ψ, turns) |
|---:|---:|---:|---|---|---|---|---|
| 40 | 400 | 1/5 | 1.5e-58 | 9e-128 | 1.43e-3 | 3.19e-3 | [2.3e-59, 1.6e-3] |
| 64 | 640 | 1/5 | 1.8e-91 | 7e-200 | 1.43e-3 | 3.19e-3 | [2.8e-92, 1.6e-3] |
| 64 | 640 | 1/10 | 3.2e-109 | 6e-200 | 9.8e-4 | 2.13e-3 | [5.0e-110, 1.6e-3] |

  The bound closes with a large margin (1 − Z₀ − Z₁ ≈ 0.9986). Caveat: the Y₀ tail is summed only up to l = M/2 − 1
  = 127. A certificate needs an analytic bound for the tail beyond that.
- **Rational centre** c(φ) = Σ c_l sin 2πlφ (turns). ‖·‖_ν uses ν = 1/5.

| harmonics | c_l | ‖ψ* − c‖_ν | sup \|ψ* − c\| | sup \|ψ*′ − c′\| |
|---|---|---|---|---|
| 1 | −3/250000 | 5.3e-6 | 3.7e-7 | 4.8e-6 |
| 2 | −3/250000, −7/20000000 | 9.8e-7 | 2.4e-8 | 3.9e-7 |
| 3 (used) | −3/250000, −699/2000000000, −883/50000000000 | 2.1e-7 | 5.5e-9 | 5.6e-8 |

## 2. The N = 65 librational torus, ω = 1/(65 + g) = 0.015239712914462636…

**Method.**
- V = 2πψ on 𝕋², odd. Galerkin on the half diamond |k|/160 + |l|/40 ≤ 1 (6440 sine modes).
- Double bordered continuation in the amplitude from the periodic orbit, then a fixed-ω Newton (residual 1.6e-19).
- Chord iteration in 192-bit fixed point on a 512 × 128 grid, using the double LU of the Galerkin Jacobian. Rate
  ≈ 10⁻¹⁵ per step: max |R̂| over all grid modes 10^−14.6 → −29.6 → −45.0 → −51.4.
- Exact polar map around c with Ω = 8/65:
  X = ψ − c, Y = p − 1 − c′, I = π(ΩX² + Y²/Ω), α = atan2(√Ω X, Y/√Ω)/2π.
  Then K(θ) = (θ₁ + U, P), and its Fourier data are computed in mp on the grid.

**Ω.** Ω = 8/65 = 0.1231. The double scan minimises (max P − min P)/mean P; the optimum is 0.1230 with spread 0.204,
so the torus is an ellipse only to about ±10 %. The small-amplitude value would be 2πω₀ = 0.164.

**Results** (`lock_N65_K160_L40.json`):

- Libration amplitude 73.82°. max |p − 1 − c′| = 0.02513.
- **P range [I_min, I_max] = [0.013238, 0.016258].** Sqrt-domain annulus, e.g. I ∈ [1/80, 1/60].
- **Decay** (max over U and P): about 0.29 decades per θ₁-harmonic (10^−25.3 at k = 80, 10^−40.0 at k = 130), and
  1.45 decades per θ₂-harmonic (10^−42.3 at l = 28). The floor is 10^−57.5 (192 bits).
- **Support.** The rectangle |k| ≤ 129, |l| ≤ 27 drops a tail of Σ|coef| = 4.1e-40. It holds 14243 nonzero complex
  coefficients (U ∪ P), about 7.1k real half-terms per function. A diamond support would cut that roughly in half.
- **Residual of the truncated polar embedding** (sup on the 512 × 128 grid, in turns/period and action/period):
  E_α = 4.7e-39, E_I = 5.2e-42. This beats the 1e-35 target.
- **Twist.** dω/d⟨P⟩ ≈ −1.24, from coarse tori at N = 64 and N = 66. It is monotone and nondegenerate.
- **Projected thresholds.**
  - `sharp_q.py` with the R1 constants and γ = κ/67 gives 10^−28.7 (10^−27.9 at κ/42; the design doc quotes about
    10^−25).
  - The v2 refined route is quoted at 10^−11.3 to −12.1 for R1. With the γ⁴ scaling (42/67)⁴ that becomes about
    10^−12.1 to −12.9.
  - Achieved: 10^−38.3. The margin is ≥ 9.6 decades even against the landed sharp route. For v2 refined, support can
    be cut to about K ≈ 50, L ≈ 10 (decay 10^−14 at k ≈ 45, l ≈ 9). These projections reuse R1's M and σ constants;
    they are not lock-package constants.

## Reproduction and timings (4 threads, nice 10, loaded machine)

    cd scripts/spin_orbit; D=/mnt/HC_Volume_106379410/kam-data/so-lock
    python3 lock_po.py $D/po_K40.json 40 256 400 1/5          # 9 s
    python3 lock_po.py $D/po_K64_nu1_5.json 64 256 640 1/5    # 31 s
    OMP_NUM_THREADS=4 SO_HP_BITS=192 python3 lock_hp.py $D 65 160 40 512 128 10   # 149 s (64 s stage A)

Stage A caches `A_N65_K160_L40.npy`; stage B pickles the fixed-point sine coefficients to `B_N65_K160_L40.pkl`.

## Part 2 (LOCK-GEN-2): the N = 65 certificate under v2 (`routeAV2`, refined route A)

**Status:** 30 October 2026, branch `inp-lockgen2`. Untrusted Python tooling: `lock_ham.py` (the proposed
`lockHamExpr` body), `lock_jet.py` (jet-compiler mirror for exp, inv, sqrt, sin, cos, div, pi), `lock_balls.py`
(disc-pass mirror), `lock_v2.py` (frame majorants, Ham claims, thresholds), `lock_trunc.py`, `lock_emit.py`.
Every threshold pass/fail decision is exact (the `v2_q.py` mirror). My wrapper reproduces R2's −14.264 on R2's
inputs. Data: `/mnt/HC_Volume_106379410/kam-data/so-lock/gen2/`.

### P2.1 The Hamiltonian as compiled (proposal for LOCK-COORDS-C)

- **Tree** (`lock_ham.lock_ham_expr`, form "design"): `J̃ + ½Y² − ½c′² + X c″ + V − ½`, with
  X = √((1/Ω)·I/π) sin 2πα and Y = √(Ω·I/π) cos 2πα.
- **V.** `−cos A · Σ εA_m cos 2π(2−m)φ + sin A · Σ εA_m sin 2π(2−m)φ`, with A = 4π(c + X). Angles enter only
  through modes, so the φ-phase is split off by the addition formula.
- **Compiled jet** (`lock_jet`, which agrees with `adv_jet` on the lunar subset): 3158 operations, 4 `sqrt`,
  8 `inv` (4 of them `inv π`, whose witness is exactly 2 at 2π-degree −1) and 4 `exp`. The lunar R2 jet has
  887 operations and none of these.
- **No sharing.** `slpCompile` does not share equal subtrees, so X compiles three times (Xc″, cos A, sin A) and Y
  once. That is where the 4 square roots come from.
- **Witnesses on the torus.** A∘K = 4πψ = 2V, so all four exp witnesses are SO's E = exp(2iV) and its reflection.
  The character witness is (1, 0) ↦ exp(2πiU). The sqrt and inverse witnesses are √(P/(πΩ)), √(PΩ/π) and their
  reciprocals.
- **"Lean" form** (owner item 1): ½Y² = (Ω/2π) I cos² 2πα, with no second root. It saves 1 sqrt, 1 inv and 20 of
  the 128 heavy torsion-compose products. The Ham claims change by only 2 %. `lockHamExpr_eval` would then hold
  only off the nonpositive real I axis.

### P2.2 Lock-package constants (ρ = 1/100, μ = 1/1000, κ = 1)

**Frame** (sampled at the corners Im θ = ±ρ, × 1.01): bL 1.484, bN 2.136, bNt 2.171, bT 6.18.

| package entry | value | how it is set |
|---|---|---|
| σK | 1.445 | ‖DK‖ 1.43 + μ |
| σB | 4.529 | ‖G⁻¹‖ 4.48 + μ |
| σT | 1.022 | bordered torsion inverse 1.01/κ + μ; ⟨T⟩₁₁ = −1.537 κ |

**Domain.** ρ_H = ρ + sup Im U + μ = 0.01523. I ∈ c₁ ± r₁ = 0.01480 ± 0.00261, J̃ ∈ 0.49986 ± 0.00109.

**Ham claims: certified disc pass against true sup.**

| | dh | dx | d2x | d2h | M |
|---|---:|---:|---:|---:|---:|
| `Slp.balls` mirror (× 1.01): what the kernel can certify | 1.93 | 140 | 3.5·10⁴ | 166 | 3.5·10⁴ |
| sampled true sup on the domain boundary (ρ = 1/140) | 1.03 | 1.73 | 102 | 1.82 | — |

**Design signal.** The disc pass overestimates by 70–300×. It treats sin 2πα as a disc of radius cosh around 0,
so exp(±iA) gets a ball of radius e^{4π·0.2} ≈ 13. Each I-derivative of the root then costs about 6× more. Two
consequences:
- the threshold is linear in d2x, so a sharper Ham pass (angle-cell subdivision, or BallsTrig-style shapes through
  `exp`) would buy about 2.5 decades (−18.40 → −15.94 at ρ = 1/140);
- M (3.5·10⁴) only feeds `checkHamBounds`; it has no effect on the threshold in the refined route.

### P2.3 Thresholds (refined route A, configuration d01b, kp = 3, ϑ = 1/8, J = 20, binding J2)

`lock_v2.py scan`. The lock frequency (ω, 1) equals the upper rotational frequency (ν₊ − 1, 1) at N = 65. The
landed Diophantine fact (γ = κ/67), the box and the small-divisor sites are therefore the upper torus's.

**κ drops out.** thr/κ does not depend on κ, and the error scales with κ too, so κ = 1.

log₁₀ e* (κ = 1):

| ρ \ μ | 1/4000 | 1/2000 | 1/1000 | 1/500 |
|---|---:|---:|---:|---:|
| 1/280 | −19.18 | −19.23 | −19.33 | −19.56 |
| 1/140 | −18.24 | −18.29 | −18.40 | −18.62 |
| **1/100** | **−17.87** | −17.93 | **−18.03** | −18.27 |
| 1/70 | −18.70 | −18.75 | −18.86 | −19.09 |
| 1/50 | the frame fails (the torus is not analytic enough there) | | | |

**Optimum: ρ = 1/100.** Beyond it the claims grow faster than ρ⁴. μ = 1/1000 is chosen over 1/4000: it costs
0.16 decades and leaves room in `checkEmbedding`.

The design §7 projection (10^−12.1 to −12.9) reused R1's constants. The real lock constants lose about 5 decades,
almost all of it in d2x and dx.

### P2.4 Truncation (κ = 1)

`lock_trunc.py`: weighted residual norm of the truncated embedding, max over the rows α, I, J̃. The α row binds;
the energy error is about 10⁴× smaller.

| support | half-terms (U) | ρ = 1/280 | 1/140 | **1/100** | 1/70 |
|---|---:|---:|---:|---:|---:|
| diamond 56 × 12 | 676 | | 1.5e-13 | | |
| diamond 70 × 14 | 994 | 2.0e-16 | 4.3e-16 | 8.2e-16 | 2.2e-15 |
| diamond 84 × 17 | 1429 | 1.6e-19 | 4.2e-19 | 9.3e-19 | 3.2e-18 |
| **diamond 90 × 18** | **1636** | | | **5.1e-20** | |
| diamond 98 × 20 | 1962 | 9.0e-23 | 2.8e-22 | 7.2e-22 | 3.2e-21 |
| rectangle 64 × 13 | 1731 | 2.6e-19 | 6.5e-19 | 1.6e-18 | 8.0e-18 |
| rectangle 76 × 16 | 2312 | 3.5e-23 | 1.7e-22 | 6.4e-22 | 5.3e-21 |

- **Diamond, not rectangle.** The diamond (Ks/Ls ≈ 5, which matches the decay ratio 0.29 : 1.45) needs 15–25 %
  fewer terms at equal error.
- **The cut.** err ≤ e*/10 = 9.2·10⁻²⁰ at ρ = 1/100, μ = 1/1000 gives **diamond 90 × 18**: residual 5.1·10⁻²⁰, and
  1636 / 1576 / 1509 half-terms for U / P / J̃. The factor-1.8 margin is for the witness and rounding radii. If
  LOCK-DATA's mirror finds it short, use 92 × 18.

### P2.5 Recommended package and witness (exact check, `lock_v2.final_check`)

| item | value |
|---|---|
| ρ, ρ∞ | 1/100, 1/100000 |
| μ, ν | 1/1000, 10⁻⁶ |
| s, σω | 1 + 10⁻⁶, 2 |
| κ (time scale c = κs) | 1 |
| γ | κ/67 |
| M | 35150 |
| σK, σB, σT | 289/200, 4529/1000, 511/500 |
| refined claim | the P2.2 disc-pass row |
| err | 9·10⁻²⁰ |
| X* | 59/125 (2× room) |
| disp | 169/5·10¹⁵ = 3.4·10⁻¹⁴ |
| threshold | 10^−18.03 |
| err/e* | 10^−1.0 |

- `refinedCore` holds (Xs, wf, okB, tail, final), and the test fails at err = 5·10⁻¹⁹ as it should.
- Certified site constants: δ₀ 0.00194, δ₁ 0.00189, b₀ 0.00501, b₁ 0.00283, b₂ 0.00207 (float c_freq × 1.01, to
  be re-derived with the balanced checker). δ₂ is classical.
- The displacement coefficient is 10^5.58.
- Backend CertFixed 112; data scale S = 101 bits (23 digits).

### P2.6 Counts and kernel cost (relative to R2-v2: 129 packed products, 667–718 shards, factors ≈ 490 terms, w = 208)

**Heavy compose products** (both factors torus-dependent, `lock_jet.heavy_products`):

| check | lock | R2 |
|---|---:|---:|
| energy | 5 | 1 |
| invariance (cfgFull) | 24 | 0 |
| torsion / Gram (cfgLow) | 128 | 0 |

**Witness checks:** 1 character, 4 exp, 4 sqrt (each W² plus a residual), and 4 non-constant inv. The four
`inv π` checks are scalar.

**Products and sizes.**
- Products: about 106 (torsion models) + 17 (Gram) + 157 (compose) + about 20 (witnesses) ≈ **300**, which is 2.3×
  R2.
- Factor sizes: about 3.2k full-lattice terms for the data; witnesses are 1.6k (W) to 3.3k (1/√), all cut at
  10⁻²³ unweighted. That is about 6.5× R2's.

**Projection** (cost per product ∝ size^{1.5…2} × width^{1…2}, width ≈ 240 bits):
- per product ≈ 17–48× R2;
- packed part ≈ 40–110× R2's 0.3–0.9 CPU-h, i.e. **≈ 12–100 CPU-h for the one torus**, against 1.4–3.6 CPU-h for
  R2's pair.

**Not included** in that projection:
- the advice-book generation;
- the per-declaration literal baseline;
- the two Ham passes. The program is 3.6× R2's, so 2 × about 5.5 min. The 10 GB cap is at risk: R2's pass
  already peaked at 9.0 GB.

**Levers:**

| lever | effect |
|---|---|
| sharper Ham pass | threshold −15.9 → diamond about 75 × 15, about 1.15k half-terms → cost ÷ 2–3 |
| "lean" form | −16 % of the torsion compose products |
| pruned composition | needed: the landed `Slp.compose` in `Certificate/Defs` runs the whole program, 1026 heavy-or-not MM products; `KAM/CertificateSharp/Kernel/Prune.lean` brings that down to the counts above |

### P2.7 Emitter (`lock_emit.py`)

- Fixed-point 192-bit grid (512 × 128) from the part-1 stage-B pickle, then the FFT, the support, rounding to
  2^-S, the residual of the truncated embedding, and the certificate JSON.
- **Certificate contents.**
  - params: the full package plus the exact v2 check;
  - ham: the tree, its Lean text, and the exp/inv/sqrt slot lists;
  - emb: U (angle 0, degree 0), angle 1 = 0, P, J̃;
  - wit:
    - charWit (1, 0);
    - expWit, mapped to W± by evaluating the program;
    - invWit: π ↦ 2, the rest ↦ 1/√;
    - sqrtWit, keyed by slot 17 / 433 / 787 / 1983, with anchor and margin from the weighted spread × 1.5.
  - advice books: **empty**. Missing keys fall back to the direct product; the packed advice needs the sofx
    mirror's new sqrt arm.
- **Not emitted yet:**
  - `gramInv` and `torsInv`: listed in the docstring, but they need the model-level mirror. LOCK-DATA computes them
    with `sofx_gen` once the mirror is extended.
  - freqBox: described in words only; it is `lunarBox` upper, scaled by κ.
- The sqrt witness encoding lives in `sqrt_witness` only.
- Sample Lean rendering: `gen2/lockN65_sample.lean`. It is not in KAM/.

### Reproduction (4 threads, nice 10, machine load 15–20)

    cd scripts/spin_orbit; D=/mnt/HC_Volume_106379410/kam-data/so-lock/gen2
    OMP_NUM_THREADS=4 python3 lock_v2.py scan $D/scan1.json                       # ≈ 12 min
    SO_HP_BITS=192 python3 lock_emit.py $D/test_K56_L12.json --Ks 56 --Ls 12      # 503 s (322 s grid, then cached)
    SO_HP_BITS=192 python3 lock_trunc.py $D/trunc1.json diamond:70:14 diamond:84:17 diamond:98:20 rect:64:13 rect:76:16   # ≈ 2 min each
    SO_HP_BITS=192 python3 lock_emit.py $D/lockN65_D90x18_rho100.json --Ks 90 --Ls 18 --rho 1/100 --prec 112 \
        --digits 23 --pkg $D/pkg_rho100_mu1000.json --lean $D/lockN65_sample.lean  # 140 s

## Part 3: resync to the landed `lockHamExpr` (inp 7e8f8c02)

**Finding.** The SO-LOCK-COST gate (§12, commit f8af9c30) compiled the landed `lockHamExpr (8/65) cs` and got 3116
ops, against the 3158 in P2.1. Neither the tree nor the compiler mirror was wrong:
- `lock_ham.lock_ham_expr(…, "design")` is the landed tree node for node (LOCK-COORDS-C already checked this in Lean).
  Its `lock_jet` program equals the gate's literal `lockJetLit` (`G1lit.lean`) **op for op, 3116 ops**, and v0,
  d1, d2, d3 are equal too: `python3 lock_jet.py check-lit $G/G1lit.lean`.
- The 42 ops are the time scale. P2.1 counted the certificate's `ham = .mul (.const κ) (lockHamExpr Ω cs)`
  (`lock_ham_scaled`). That compiles to the κ constant (slot 1, which shifts the tree by one), the tree, and one
  product κ·e for each of the 41 nonzero jet entries (v0, 4 d1, 9 d2, 27 d3): 3116 + 1 + 41 = 3158.
- The wrapper is not optional at κ = 1. The landed consumer `lockBarrier_of_exact_torus`
  (`Lock/Graph.lean:85`) states invariance for `HamExpr.mul (.const κ) (lockHamExpr Ω cs)` for every κ. So the
  certificate's program has 3158 ops, and the gate's bridge and ball-pass probes measure the bare tree, which is
  a 41-product, one-constant subset of it.
- Every count in P2.1–P2.6 is unchanged. In the bare tree, the exp, inv and sqrt slots move down by one (exp 887,
  1127, 2083, 2323; sqrt 16, 432, 786, 1982).

**Gate G2 boundaries.** The gate's generator placed the tail segments at s = 3158 − L. On the bare 3116-op program,
`take L` therefore cut them to 758 and 358 ops. `lock_gate.py` (no Lean run) did four things:
- Reprinted the gate's `opLit` / `chunked` text and checked it byte for byte against `G1lit.lean` and all eight
  existing `G2_*` files. All match.
- Rewrote `gate/G0_emit.lean`, keeping the original as `G0_emit.lean.orig-3158`. The changes:
  - `g1lit` now checks length 3116;
  - the tails go at `lockJ.prog.ops.length − L`, that is s = 2716 (L = 400) and s = 2316 (L = 800), guarded by
    `lockN = 3116`.
- Wrote `gate/G2_segments.json`: ranges, op census and the sha256 of each `segLit` text the regenerated G0 will
  print.
- Moved the four stale tail probes to `gate/stale-3158/`. The s = 0 probes are unchanged and still valid.

The tail probe files themselves (with accIn and accOut) need the exact Lean ball pass, so the next
`run_gate.sh emit` writes them.

**Emitter.** `lockN65_D90x18_rho100.json` and `lockN65_sample.lean` were regenerated (version lock-gen2-0.2). The
residual, supports, witnesses and package are unchanged. `ham` now records both `program_length` 3158 (certificate)
and `lockHamExpr_length` 3116 (landed tree).
