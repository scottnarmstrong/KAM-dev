# SJS-X1: the Fourier support of FH25's torus, measured to 22 digits

2 November 2026, branch `zohar/sjs-planar-x1`. Gate **X1** of [sjs-plan](sjs-plan.md) §5.2, the first step of milestone M3
(the planar Sun–Jupiter–Saturn torus) that needs no owner decision. Numerics only, in double-double arithmetic (about 32
significant digits). **No certificate, no Lean, and no change to any landed, frozen or SO-owned file.** Every number comes
from `scripts/sjs/x1/` (§7) and is labelled *measured* or *model*.

## Verdict

X1 asked for the Fourier support S(L) of FH25's torus at certificate accuracy. This was the plan's largest uncertainty: a
factor of 3 in cost, extrapolated from L ≤ 10. Here it is measured to L = 22. The definition is the plan's (1.3): the strip
0.02, the regular-chart components, each component relative to its own largest nonconstant coefficient.

- **The support grows at the plan's low rate (measured).**
  - S^(1/3) gains 3.46 per digit at L = 12 and 3.74 at L = 20.
  - It stays at 3.74–3.77 through L = 24.
  - The plan's range was 3.7 (low) to 5.3 (high, the cross-polytope envelope).
- **Extrapolated to L = 45 (model).**
  - S(45) = **4.0–4.1·10⁶** if the slope stays flat, as it was over the last five measured digits.
  - S(45) = 4.9·10⁶ if the slope resumed the rise it had between L = 10 and 20.
  - The plan had 4.3·10⁶–1.3·10⁷.
- **The adapted frame stays compact (measured).** In the best unimodular frame, box/S (99.5 % per axis) is 2.23–2.30 for
  every L from 12 to 24. The plan measured 2.5–2.6 at L ≤ 8 and used 3.
- **The cost range narrows by about 3× from its top.** These are the plan's own cost model (§3.4) with the measured S and
  β = 2.3 (model):

  | Quantity | Here (flat slope … rising slope) | sjs-plan |
  |---|---:|---:|
  | Box | 0.91–1.12·10⁷ | 1.3–3.8·10⁷ |
  | Operand F | 0.95–1.17 GB | 1.3–4 GB |
  | Packed, one `Nat` per model | 10–43 CPU-h | 14–143 CPU-h |
  | Packed, 8 GB shards | 20–94 CPU-h | 29–950 CPU-h |
  | Packed, default kernel limit | 107–590 CPU-h | 210–6,700 CPU-h |

- **Input literals (model, on rates measured by V2-PACKED, landed 1 November).**
  - The six components of K on the box at 174 bits are 0.95–1.16·10¹⁰ bits.
  - Ingested in 288-bit chunks, that is 340–550 GB of charged kernel memory, spread over declarations of at most 4 GB, plus
    2.4–4.2 CPU-h of elaboration.
  - With long-line chunks (V2-PACKED's owner question Q1) it is 57–70 GB.
  - So literal input is comparable to the arithmetic, not dominant.
- **A structural finding (measured).** The torus has one isolated near-resonant spike, at the θ-mode k₀ = (27, −67, 31),
  where 27ω₁ − 67ω₂ + 31ω₃ = 7.7·10⁻⁷.
  - Its coefficient is 5.8·10⁻¹⁵, which is 2.6·10¹⁴ times the median coefficient at its order |k|₁ = 125.
  - Its satellites lie along the great-inequality direction (2, −5, 2), at 8.9·10⁻¹⁶ for n = ±1.
  - It lies outside the 99.5 % box for L = 15–17 and inside it from L = 18. In the box extrapolated to L = 45 (8.7·10⁶ modes),
    k₀ is the only mode with |k·ω| < 10⁻⁶ and no mode has |k·ω| < 10⁻⁷.
- **A lesson for the data generator (E1 SJS-GEN, measured).** Near-resonant modes have double small divisors in the Newton
  step: 1/(k·ω)² ≈ 10¹² at k₀.
  - In double precision they therefore carry noise: 3–8·10⁻¹⁰ at k₀ in every double torus computed here.
  - A double-double refinement on a grid whose band cuts k₀'s satellites diverges.
  - On an adequate grid it converges to the double-double floor in five iterations.

**Checked independently of the solver (measured).**
- The energy is constant on the torus to 3.8·10⁻³⁰ over 2.5·10⁶ grid points (|H| = 0.106).
- ⟨Ĝ⟩ = 2.17657418883872689348514735… agrees with FH25's printed 2.176574188839 to all its digits.
- Two grids of different shapes give identical S(L) for every L ≤ 22, and agree within 0.02 % at L = 23–25.
- The plan's coarse torus and its S(L) table are reproduced.

**Not done.**
- No enclosure of anything.
- Only K's support was measured; the plan priced intermediate models at 0.3–2.2× K, and that was not re-measured.
- Nothing is measured beyond L ≈ 23.
- L = 45 needs about 48 digits, beyond double-double (§6).

## 1. Setting

- **Torus.** FH25's torus of the reduced planar three-body problem, as SJS-PLAN computed it (`sjs_torus.py`: FH25 (2.1)–(2.2),
  masses (0.9546, 0.2856), μ = 10⁻³, FH's frequency ω and angular momentum). The chart is SJS-PLAN's synodic regular chart
  (`sjs_chart.H_syn`):
  - angles (b₁, b₂, b₃) = (a₁ − a₂, a₂, a₂ + a₃);
  - actions (Λ₁, I₅, I₆), with Λ₂ eliminated through the angular momentum;
  - normal modes w = Qᵀz, with Q the rotation by φ = −1.0908308.
- **The Hamiltonian, recoded (`hsyn.py`).** The Hamiltonian is coded anew with regular Kepler variables, as the plan's
  operation count does: k + ih = ε z̄, the eccentric longitude F, and no e = 0 singularity or arctangent.
  - At 200 bits it equals SJS-PLAN's Delaunay route to 7.8·10⁻⁶².
  - Its double-double gradient agrees with an mpmath finite difference to 7.7·10⁻³².
  - SJS-PLAN's own double-precision evaluation (`sjs_chart.tensors`) is 3·10⁻¹² away in the gradient. Since the formulas
    agree, that gap is rounding in its double evaluation.
- **Constants.** The model's constants are FH25's printed decimals, exactly rounded in each number type.
- **Parametrization.** The torus is K(p) = (A p + q(p), act(p)) on a grid in the adapted frame:
  - k′ = G k with G = ((−1, 0, 1), (−1, −1, 0), (−2, −1, 0)), the plan's best frame at L = 8;
  - θ = Gᵀp are the angles of SJS-PLAN's torus;
  - A = F_s Gᵀ is the chart's winding;
  - the frequency is ω′ = G⁻ᵀω.
- **Arithmetic (`dd.py`).** Double-double on numpy arrays:
  - Knuth's two-sum and Dekker's two-product;
  - sine and cosine by a 1,024-entry table and a Taylor series;
  - a mixed-radix (2, 3) FFT with twiddles exact to double-double.
  - Against mpmath it is accurate to 1.9·10⁻³² relative (arithmetic), 8.7·10⁻³² (sine, cosine) and 2·10⁻³¹ (FFT).

## 2. Method

1. **Start.** SJS-PLAN's coarse torus (E4: continuation from μ = 0 on 96³, then refinement) is re-run and reproduced to every
   printed digit: residual 1.797·10⁻⁷, ⟨Ĝ⟩ = 2.176574188855, |⟨T⟩⁻¹| = 354.077. It is moved to the synodic chart
   (`sjs_chart.periodic_data`) and re-indexed into the p grid (`x1_torus.py init`).
2. **Double precision.** FH25's quasi-Newton step at fixed frequency is applied in the synodic chart (`x1_torus.py newton`, the
   algebra of `sjs_torus.newton`). From 3·10⁻⁸ it reaches 7.5·10⁻¹⁴ in one step. On 48×192×144 it stops at a floor of
   7.5·10⁻¹⁵; |⟨T⟩⁻¹| = 390.953 in this chart.
3. **Double-double defect correction (`x1_dd.py`).**
   - The state is the double-double Fourier coefficients, exactly zero outside a box band and exactly Hermitian.
   - The residual E = X_H(K) − DK·ω′ is evaluated in double-double: inverse FFT, gradient of H, FFT.
   - The Newton correction is computed in double from the in-band part of E and added in double-double.
   - The out-of-band part of E is the grid's truncation residual. It cannot be corrected, and it measures the grid.
4. **Grids.** The iteration first ran on 48×192×144 (1.3·10⁶ points). The production run was then on **72×144×243**
   (2.5·10⁶ points, band |k′ᵢ| ≤ 0.45 Nᵢ). The check grid is 64×162×243, regridded from the production state and re-converged.

| Run | Grid | In-band residual (sup), by iteration | Truncation (out-of-band ℓ¹) | Peak RSS |
|---|---|---|---:|---:|
| production | 72×144×243 | 1.0·10⁻¹⁷ → 1.1·10⁻²⁵ → 4.4·10⁻²⁸ → 3.2·10⁻³¹ → 6.5·10⁻³² → 7.5·10⁻³² | 2.3·10⁻²⁶ | 3.06 GB |
| check | 64×162×243 | 1.1·10⁻²⁶ → 6.6·10⁻³² → 5.9·10⁻³² → 5.9·10⁻³² → 5.6·10⁻³² | 5.8·10⁻²⁵ | 3.25 GB |

Each production iteration took about 2.5 minutes on one thread, at a machine load of about 100 on 18 cores. The whole gate,
from the E4 continuation to the last check, took about 1.5 CPU-h.

**What went wrong first.** On 48×96×144 the double-double iteration diverged: 5.8·10⁻¹⁵, then 1.2·10⁻¹³, then 2·10⁻¹¹.
- Debugging showed no sign error: the double and double-double residuals agree to the double floor.
- The cause is k₀ (§4). The correction there is amplified by 1/(k₀·ω)², and k₀'s satellites n = ±2 were cut by that grid's
  band edge.
- Doubling the grid along the resonant axis cured it.
- A second harmonic 2k₀ at |k·ω| = 1.5·10⁻⁶ then sat on that grid's band edge. It decayed slowly, about 5× per iteration,
  from a spurious 2.6·10⁻¹².
- It is outside the band of both final grids. Its true size was not measured; an estimate puts it below 10⁻²⁰.

## 3. The support

S(L) on the production torus. The strip is 0.02 and the components are the regular chart's, as in the plan's table 1.3. The
check grid gives the same counts to L = 22.

| L | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 | 24 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| S(L) | 1,162 | 4,626 | 12,544 | 27,078 | 50,472 | 85,058 | 133,612 | 200,194 | 287,328 | 397,070 | 531,768 |
| SJS-PLAN | 1,162 | 4,626 | 12,576 | 28,202 | | | | | | | |
| S^(1/3) per digit | 2.80 | 3.11 | 3.34 | 3.38 | 3.46 | 3.51 | 3.59 | 3.70 | 3.74 | 3.77 | 3.76 |
| β (best frame, 99.5 %) | | | 2.44 | | 2.30 | | 2.29 | | 2.28 | | 2.23 |

- **Agreement with the plan.** It agrees with the plan's table to 0.3 % for L ≤ 8. The plan's L = 9 and 10 are 1.4 % and
  4 % high, because its torus had a residual of 1.7·10⁻⁹.
- **The last column.** At L = 24 the support reaches the band edge along p-axis 1 (row (−1, −1, 0)). The noise floor in the
  outer band shell is 3.7·10⁻²⁶. So L = 23–24 are marginal, and L ≥ 25 is not measured.
- **Without the strip** (ρ = 0) the counts are 41,276 at L = 12, 108,244 at 16, 231,160 at 20 and 319,816 at 22.
- **Frames.** The best frame switches between ((−1, 0, 1), (−2, −1, 1), (−2, −1, 0)) for L ≤ 16 and the plan's frame from
  L = 20, with nearly equal β.
- **Extents** (99.5 % per axis, frame G, full widths):
  - L = 8: 16×33×57 (the plan: 17×33×57);
  - L = 16: 35×71×123;
  - L = 24: 53×117×191;
  - that is 2.5, 5.0 and 8.5 lattice points per digit.
- **Coefficient agreement between the two grids.**
  - Coefficients between 10⁻²² and 10⁻²⁰ agree to a median of 7·10⁻¹⁴ relative (99th percentile 7·10⁻¹¹).
  - Between 10⁻²⁴ and 10⁻²² they agree to 7·10⁻¹² (99th percentile 8·10⁻⁸).
  - The check grid started from the production state, so this tests the grid, not the start.

## 4. The near-resonance at (27, −67, 31)

- **The mode.** k₀ = (27, −67, 31) in the θ lattice, |k₀|₁ = 125, with |k₀·ω| = 7.70·10⁻⁷. In the p frame it is
  k′ = (4, 40, 13).
- **Its cluster** k₀ + n(2, −5, 2), in units of each component's largest nonconstant coefficient:

  | n | −2 | −1 | 0 | +1 | +2 | +3 | +4 |
  |---|---:|---:|---:|---:|---:|---:|---:|
  | coefficient | 8.5·10⁻¹⁷ | 8.9·10⁻¹⁶ | 5.8·10⁻¹⁵ | 8.9·10⁻¹⁶ | 6.5·10⁻¹⁷ | 3.3·10⁻¹⁸ | 1.5·10⁻¹⁹ |

- **Against the smooth envelope.** The median coefficient at |k|₁ = 125 is 2.2·10⁻²⁹.
- **In double precision** the same mode came out at 7.7·10⁻¹⁰ on 48×96×144 and 3.4·10⁻¹⁰ on 48×192×144. That is noise of
  ~10⁻²⁰ per mode, amplified by the double small divisor, and it is why the double Newton corrections never fell below
  10⁻¹⁰.
- **Is it alone?** In the box extrapolated to L = 45 (half-widths 53, 111, 185 in the p frame), k₀ is the only mode with
  |k·ω| < 10⁻⁶. None has |k·ω| < 10⁻⁷.
- **Consequences for the certificate.**
  - At L = 45 the spike and its cluster lie inside the box, so no sparse overflow is needed for them.
  - The Diophantine side is unaffected. The plan's explicit cubic frequency has certified γ = 2.8·10⁻⁷ at τ = 2, and
    γ/|k₀|₁² = 1.8·10⁻¹¹ ≪ 7.7·10⁻⁷.
- **For the generator.** Its Newton solves must keep a residual well below (k₀·ω)²/|T| at k₀ before that mode can be
  trusted.

## 5. What changed since sjs-plan

- **Decision 1 (the packed layer) is partly built.** V2-PACKED's GMP-resident packed models landed on `main` on 1 November
  (`KAM/CertificateSharp/Packed/`, 54 files). LG00's tori are proved by that route: 1.75–2.7 CPU-h each against run18's
  29.9 CPU-h.
  - At SJS size the operands are F ≈ 1 GB, about 75× above the kernel's default `Nat` limit of 2²⁷ bytes.
  - So blocks or the `LEAN_NAT_MAX_SIZE` override (decision 3) are still needed.
  - V2-PACKED's handoff names literal I/O as SJS's binding cost. §0 above prices it with the measured S.
- **Decision 7 (sequence).** LG00 is at 97 % (`docs/campaign/side/lg00-status.json`). The packed gate X2 can now use this
  torus's real coefficients.
- **Literature.** No completed computer-assisted proof of FH25's torus was found (searched 2 November 2026).
  - FH25 ([arXiv:2403.10152](https://arxiv.org/abs/2403.10152), J. Nonlinear Sci. 2024) is a numerical verification.
  - Its reference [19] and the CRM's 2025 article describe the proof as in progress.
  - Novelty must be re-checked before any claim.
- **The other decisions (2–6, 8) are unchanged.**

## 6. Next gates

None of these needs an owner decision except where stated.

1. **X2, the packed gate.** A real 3-D reversible product in blocks, on this torus's coefficients at S ≈ 10⁵–4·10⁵. It
   measures layout, β with sparse overflow, and the V2-PACKED literal path at SJS width.
2. **X3.** A ball-arithmetic mirror of the synodic H on the box: enclosed against sampled majorants.
3. **E1 SJS-GEN.** L = 45 needs about 48 digits.
   - Triple-double (about 48 digits) or quad-double versions of `dd.py` would carry this pipeline there.
   - So would the plan's native packed Newton.
   - The near-resonance (§4) sets the generator's residual target at k₀.
4. **X6.** Route-B budgets at L_low = 3–6 for frames and torsion.

## 7. Reproduction

From the repository root, with numpy, scipy and mpmath. `OUT` is any scratch directory; torus files (0.3–0.5 GB) are not
committed. One process at a time; the peak is 3.3 GB. Logs and JSON receipts are in `scripts/sjs/x1/results/`.

```
python3 scripts/sjs/x1/dd.py && python3 scripts/sjs/x1/hsyn.py                                    # self-tests
python3 scripts/sjs/plan/sjs_torus.py --grid 96 96 96 --steps 20 --newton 3 --refine 6 --save OUT/t96.npz   # E4, 19 min
python3 scripts/sjs/x1/x1_torus.py init OUT/t96.npz --grid 48 96 144 --out OUT/s1.npz
python3 scripts/sjs/x1/x1_torus.py newton OUT/s1.npz --iters 8 --out OUT/s1n.npz
python3 scripts/sjs/x1/x1_torus.py newton OUT/s1n.npz --grid 48 192 144 --iters 6 --out OUT/s2n.npz
python3 scripts/sjs/x1/x1_dd.py OUT/s2n.npz --iters 4 --out OUT/s2dd.npz
python3 scripts/sjs/x1/x1_regrid.py OUT/s2dd.npz --grid 72 144 243 --out OUT/s3.npz
python3 scripts/sjs/x1/x1_dd.py OUT/s3.npz --iters 6 --out OUT/s3dd.npz                            # production
python3 scripts/sjs/x1/x1_regrid.py OUT/s3dd.npz --grid 64 162 243 --out OUT/s4.npz
python3 scripts/sjs/x1/x1_dd.py OUT/s4.npz --iters 5 --out OUT/s4dd.npz                            # check grid
python3 scripts/sjs/x1/x1_spectrum.py OUT/s3dd.npz --Lmax 30 --frames 8,12,16,20,24 --json scripts/sjs/x1/results/x1_spec_s3dd.json
python3 scripts/sjs/x1/x1_spectrum.py OUT/s4dd.npz --Lmax 30 --frames "" --json scripts/sjs/x1/results/x1_spec_s4dd.json
python3 scripts/sjs/x1/x1_compare.py OUT/s3dd.npz OUT/s4dd.npz scripts/sjs/x1/results/x1_spec_s3dd.json \
    scripts/sjs/x1/results/x1_spec_s4dd.json --json scripts/sjs/x1/results/x1_compare.json
python3 scripts/sjs/x1/x1_check.py OUT/s3dd.npz --json scripts/sjs/x1/results/x1_check_s3dd.json
python3 scripts/sjs/x1/x1_resonance.py OUT/s3dd.npz --json scripts/sjs/x1/results/x1_resonance_s3dd.json
python3 scripts/sjs/x1/x1_cost.py scripts/sjs/x1/results/x1_spec_s3dd.json --Lfit 22 --beta 2.3 --json scripts/sjs/x1/results/x1_cost.json
```

The double-double iterations of 48×192×144 were run as 2 + 1 + 1 in the receipts, not as one run of 4, which is equivalent.
Scripts of SJS-PLAN (`scripts/sjs/plan/`) are imported read-only.
