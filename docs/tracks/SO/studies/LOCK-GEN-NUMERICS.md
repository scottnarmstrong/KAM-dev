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
