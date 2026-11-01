# V2-3FREQ: sharp small-divisor sites for three frequencies

Date: 1 November 2026. Branch `v2-3freq` from `origin/main` at `f80bdf6e`. Improvement #4 of
[CERTIFIER-V2-IMPROVEMENTS](CERTIFIER-V2-IMPROVEMENTS.md). Additive only: no existing file under
`KAM/CertificateSharp/**`, `KAM/Sharp2/**`, `KAM/Strip/**` changes.

## 0. Starting point

The v2 sharp site [`siteOk`](../../../KAM/CertificateSharp/V2/SmallDivQ.lean) (lines 59–61) accepts
`n = 2`, `τ = 1` and an exact last coordinate `κ`. Everything else falls back to the classical
`c♮(n, τ, b)`. Three facts shape the extension:

1. The real analysis is already general. `KAM.smallDivisorSum_snoc_le_fiber`
   (`KAM/Strip/CohomologicalSumFiber.lean`) is the fibered bound for `ω = (ω', 1) ∈ ℝ^{m+1}` at any
   `m` and any real `τ ≥ 0`. `KAM.sdTail_le` bounds the tail `T_N` for any `τ`.
   `sdSum_ray_le`, `isDiophantine_ray` and `sdConst_of_sdSum` (`KAM/Sharp2/SmallDiv/*`) hold for
   every `n`, `τ`.
2. Only the rational layer is specialised. `SdsData.tailBound` and `sds_tail_le` hard-code `τ = 1`.
   `fiberCheck` is stated with a `decide (∀ k ∈ modeBox m N, …)` that the kernel cannot run at
   `m = 2`. `sdConst_two_of_sdSum` and `siteOk` hard-code `n = 2`.
3. **`τ = 1` is empty in dimension three.** By Dirichlet, every `ω ∈ ℝ³` has infinitely many `k` with
   `|k·ω| ≤ C |k|₁^{-2}`. So `IsDiophantine γ 1 ω` is false for every `γ > 0` and `ω ∈ ℝ³`, and
   `sdsFiberBound_sound` at `m = 2` has an unsatisfiable premise. Three frequencies need `τ ≥ 2`.
   The natural witnesses are cubic: `(1, θ, θ²)` with `θ` a cubic irrational is `(γ, 2)`-Diophantine.

## 1. Mathematics of the new site

Let `ω* ∈ ℝ³` lie in the certificate's box. The last coordinate is enclosed in `[κc - κr, κc + κr]`,
with `κlo = κc - κr > 0` and `κhi = κc + κr`. Write `ω* = ω*₂ · (ω', 1)` with `ω'_i = ω*_i / ω*₂`.

**Fiber box (interval division).** If `|ω*_i - c_i| ≤ r_i` and `|ω*₂ - κc| ≤ κr`, then
`|ω'_i - c_i/κc| ≤ (r_i κc + |c_i| κr) / (κlo κc)`. For an exact clock (`κr = 0`) this is `r_i/κc`,
which is the lunar `fiberBox`.

**Diophantine transfer.** `IsDiophantine γ τ ω*` gives `IsDiophantine (γ/ω*₂) τ (ω', 1)`, hence
`IsDiophantine (γ/κhi) τ (ω', 1)` by monotonicity in `γ`.

**Scaling.** `S(ω*, b) = (ω*₂)⁻² S((ω', 1), b) ≤ κlo⁻² S((ω', 1), b)`
(`smallDivisorSum_smul`, with `S(ω, b) = smallDivisorSum ω (2b)`).

**Finite part.** `smallDivisorSum_snoc_le_fiber` at `m = 2`, `δ = 2b` and `E_j = E₁^j` with
`E₁ ≥ e^{-2πδ}` gives

  `S((ω',1), δ) ≤ E₁ π²/3 + Σ_{k' ∈ modeBox 2 N} t(k') + T_N(γ/κhi, τ, δ)`.

Here `t(k') = E₁^{|k'|+|p|} L⁻² + E₁^{|k'|} ([p ≠ 0] (|p| - ½)⁻² + E₁ C₀)`. The per-mode data are
those of the n = 2 checker (`fiberP`, `fiberLb`), now for `k' = (a, b) ∈ ℤ²`:

- `x = a c'₀ + b c'₁`, `p = ⌊-x + ½⌋`, `rad = |a| r'₀ + |b| r'₁`;
- the check `|x + p| + rad ≤ ½` and `L = |x + p| - rad > 0`.

There are `2N(N+1)` modes. The kernel walks them on the diamond `|a| + |b| ≤ N`: rows
`a = i - N`, `i < 2^l`; columns `b = j - (N - |a|)`, `j < 2^l`; `2N + 1 ≤ 2^l`. Both levels use
balanced bisection, so the recursion depth is `2l`. One pass both checks a mode and returns its
rounded term (`Option ℕ`; `none` = a failed mode).

**Outward fixed point.** Each `t(k')` is replaced by the natural number `⌈t(k') 2^P⌉`, so the sum
is a sum of naturals. Exact rational accumulation (the n = 2 `balBound`) would grow the
denominator as the lcm of all `L²` numerators: harmless for `2N ≈ 10³` terms, prohibitive for
`2N² ≈ 10⁵`. The rounding cost is at most `#modes · 2^{-P}`, checked in the claimed bound. Upper
rounding is the only direction ever used.

**Tail, any `τ ∈ ℕ`.** `KAM.sdTail_le` with `E' = E₁^{N+1}` gives the rational

  `T̂ = 2 (1 + 2^τ) γ'^{-2} (6.3 δ) (N+1)^{2τ} E₁^{N+1} (1 + c_lo⁻¹)`,
  `c_lo = 6.28 δ - 2τ/(N+1) > 0`.

`c_lo > 0` gives the side condition `2τ < 2πδ(N+1)`. At `τ = 1` this is `SdsData.tailBound`.
The tail is the proved infinite part: no truncation is assumed beyond `N`.

**Constant on the ray.** `S(s ω*, b) ≤ S(ω*, b)` for `s ≥ 1`. `sdConst_of_sdSum` then needs
`(2π)⁻¹ 2^{n/2} √S ≤ c γ⁻¹ b^{-τ}`. The rational test, squared, with `π > 3.1415`, is

  `2^n · B κlo⁻² · (γ b^τ)² ≤ (2 · 3.1415 · c)²`,

where `B` is the claimed bound of `S((ω',1), δ)`. At `n = 2`, `τ = 1`, `κr = 0` this is `biteOk`'s
test.

## 2. Diophantine witnesses for real 3-vectors

Let `P = t³ + p₂t² + p₁t + p₀ ∈ ℤ[t]` have no rational root, and let `θ ∈ ℝ` satisfy `P(θ) = 0`.
For `u ∈ ℤ³` put `β(u) = u₀ + u₁θ + u₂θ²`.

- *Independence.* For rational `v ≠ 0`, `v₀ + v₁θ + v₂θ² ≠ 0`. Elementary: reduce `θ² = sθ + t`.
  Then `P(θ) = 0` is linear in `θ`, and either `θ` is rational or `P` has the rational factor
  `t + s + p₂`. No minimal-polynomial theory is needed.
- *Norm and cofactor.* `M_u` is the integer matrix of multiplication by `β(u)` on `(1, θ, θ²)`.
  `N(u) = det M_u ∈ ℤ`, and `Y(u) = y₀ + y₁θ + y₂θ²` with `y = adj(M_u) e₀` (integer quadratic
  forms). Then `β(u) Y(u) = N(u)`; this is a polynomial identity modulo `P`, checked by
  `linear_combination` with the explicit quotient computed by sympy.
- *`N(u) ≠ 0` for `u ≠ 0`.* If `det M_u = 0`, some rational `v ≠ 0` has `M_u v = 0`
  (`Matrix.exists_mulVec_eq_zero_iff`). Then `β(u) β(v) = 0` with both factors nonzero by
  independence, a contradiction.
- *Quadratic bound.* `Y(u) = uᵀ H(θ) u`, with `H` symmetric and entries in `½ℤ[θ]`. For
  `ω = D⁻¹ A (1, θ, θ²)` with an integer matrix `A`, `det A ≠ 0` and `D > 0`, we have
  `k·ω = D⁻¹ β(Aᵀk)` and `Y(Aᵀk) = kᵀ W k` with `W = A H Aᵀ`. So
  `|k·ω| ≥ 1/(D · max_{ij} |W_ij(θ)| · |k|₁²)`.
  Each `W_ij = w₀ + w₁θ + w₂θ²` is computed exactly over `ℚ`. It is bounded on `|θ - θc| ≤ θr` by
  `|W_ij(θc)| + θr (|w₁| + |w₂| (2|θc| + θr))`.

The checker `cubicDioOk` verifies: no integer root in `[-|p₀|, |p₀|]` (with `p₀ ≠ 0`, the rational
root theorem for monic `P`), `det A ≠ 0`, and `γ D W̄ ≤ 1` for the computed bound `W̄`. Its soundness
theorem gives `IsDiophantine γ 2 ω`.

This is the conjugate bound of the SJS plan (§5.3), `γ = 1/(D m₁ m₂)`, without complex conjugates.
It is never worse, since `|W_ij| ≤ m₁ m₂`. Transferring through the norm of `A` would lose a
further factor `‖A‖²`, so it is avoided. A lossy general transfer (integer matrix, any `n`, `τ`)
and the `τ`-general scaling lemma are included for other uses.

On the landed example `(∛2/2, ∛4/2, 1/2)`, `W̄ = 2∛2 ≈ 2.52` gives `γ = 0.198`, against the landed
`1/12` (`cubicFreq_isDiophantine`). The numerical infimum of `|k|₁² |k·ω|` (`|k|₁ ≤ 40`) is `0.43`.

## 3. Lean interfaces (new modules only)

| Module | Content |
|---|---|
| `KAM.CertificateSharp.V2.Fiber.TailTau` | `SdsData.cLoT`, `SdsData.tailBoundT` (rational `T̂`, any `τ : ℕ`), `sds_tail_leT`; `fiberTermM`; `smallDivisorSum_snoc_le_fiberT` (any `m`, `τ`, with the mode facts as hypotheses) |
| `KAM.CertificateSharp.V2.Fiber.Enum2` | `balFold` (balanced `Option ℕ` sum), `cell2`, `fib2Sum` (diamond walk), `modeBox_two_le` (coverage), `smallDivisorSum_snoc2_le` |
| `KAM.CertificateSharp.V2.Fiber.Site3` | `FibWit`, `clockFiberBox`, `fiberSiteOk`, `sdConst_ray_of_fiberSiteOk`; `SiteWitG` (`classical`, `bite`, `fiber`), `siteOkG`, `sdConst_of_siteOkG` |
| `KAM.CertificateSharp.V2.Fiber.RouteAG` | `RefinedWitG`, `sitesOkG`, `refinedCoreG`, `refinedCoreG_sound`, `routeARefinedG : EngineV2` |
| `KAM.CertificateSharp.Freq.CubicNorm` | independence, norm/cofactor identity, `cubicDioOk`, `isDiophantine_of_cubicDioOk`; `isDiophantine_smulT`, `isDiophantine_intMat` |
| `KAM.CertificateSharp.V2.Tests.Fiber3Toy` | T3 (`toyCert3`, `n = 3`, `τ = 2`) through `routeARefinedG` with fiber sites; Diophantine premise from `cubicDioOk` |
| `KAM.CertificateSharp.V2.Tests.Fiber3XLang` | Exact equalities produced by the Python mirror, checked by `decide +kernel` |

**Site checker.**

```
structure FibWit where N l J P : ℕ; E1 B : ℚ
def fiberSiteOk (n τ : ℕ) (box : FreqBox) (γ b c : ℚ) (w : FibWit) : Bool
theorem sdConst_ray_of_fiberSiteOk (hτ : 1 ≤ τ) (hγ : 0 < γ) (h : fiberSiteOk n τ box γ b c w)
    (hω : FreqEncloses n box ωstar) (hdio : IsDiophantine γ τ ωstar) :
    SDConst n τ γ b c (ray ωstar)
inductive SiteWitG | classical | bite (w : BiteWit) | fiber (w : FibWit)
def siteOkG (n τ J : ℕ) (box : FreqBox) (κ γ b c : ℚ) : SiteWitG → Bool
theorem sdConst_of_siteOkG … : SDConst n τ γ b c (ray ωstar)   -- same shape as sdConst_of_siteOk
```

**Plug-in.** The v2 theorems consume the site constants only through `NumQ.cert_ray` (route A) and
`NumBQ.cert_ray` (route B). Their hypotheses are `SDConst Q.n Q.τ γ (Q.δ s) (c_s) (ray ωstar)`
per site. `sdConst_of_siteOkG` produces exactly that, so the engine variant changes only the site
step. `refinedCoreG_sound` copies `refinedCore_sound` (`V2/RouteARefined.lean`) with `sitesOkG`.
`routeARefinedG` copies `routeARefined`'s test and soundness. `siteOkG` contains `siteOk`
(`.bite w` ↦ `siteOk … (some w)`, `.classical` ↦ `siteOk … none`), so every existing route-A
refined witness has an image. The route-B variant (`NumBQ.sitesOk`, three sites per stage) is the
same substitution. It is left for a follow-up, because route B's engine file is shared with
running work (§7).

## 4. Cost model

- **Modes:** `2N(N+1)` fibres at `m = 2`, against `#{0 < |k|₁ ≤ N} ≈ 4N³/3` for the full box. The
  walk visits at most `(2N+1) 2^l ≤ 2(2N+1)²` cells; an empty cell is one comparison.
- **Cut-off:** `c_lo > 0` needs `N + 1 > τ/(3.14 δ) = τ/(6.28 b)`. In practice `T̂` must also be
  small next to `S`. That takes `2πδ(N+1)` of about `2τ ln(N+1) + ln(γ'^{-2}/S) + O(1)`, so
  `N ≈ (25–40)/(2πδ)` for the bites below.
- **Arithmetic per mode:** a floor of a rational of the box's denominator size, two squares, one
  `E₁^j` with `j ≤ N(1 + |ω'|) + 1`, and one ceiling at `2^P`. `E₁` is a short rational (10–30
  digits), so `E₁^j` has `≈ 10 j` digits. The accumulator is a natural below `2^{P + log₂ B + 20}`.
- **Bites of the example (T3, `ρ = 9`):** `b ∈ {1, ½}`; `N = 8–12`, `l = 5`, about 200 fibres per
  site. The default build carries it.
- **SJS (sjs-plan §1.2, §5.3):** `δ = 2.65·10⁻³` and `5.3·10⁻⁴` give about `9·10³` and `2.3·10⁵`
  fibres per site (plan's count, rechecked in §6 of the handoff). That is a heavy kernel check,
  opt-in under `kernel-tests/`, priced by the measured per-mode cost.

## 5. Python mirror

`scripts/certifier/fiber3.py`: an exact `Fraction` transcription of `fiberSiteOk` (same names,
same rounding, same enumeration order), a producer (choose `N`, `l`, `J`, `E₁`, `P`, `B`, `c`), and
`cubic_dio` (the checker `cubicDioOk` and the bound `W̄`). The cross-language test
`scripts/certifier/fiber3_xlang.py` writes and compares the expected naturals and booleans of
`Tests/Fiber3XLang.lean`. The kernel decides the same equalities.

## 6. Out of scope

General `n ≥ 4` enumeration (the fiber theorem is general; only the walk is `m = 2`);
higher-degree number fields; the route-B variant (§3); producer-side route selection
(improvement #3).
