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

**Integer fixed point (as built).** The walk runs on naturals only. The witness gives a dyadic box
`DBox2` (`ω'_i ∈ [C_i ± R_i]/2^q`), checked once to contain the interval-divided certificate box
(`dboxOk`). With it, `X = a C₀ + b C₁`, `p = ⌊(2^q - 2X)/2^{q+1}⌋`, `Y = |X + p 2^q|` and
`Rd = |a| R₀ + |b| R₁` are integers, and the mode test is `Rd < Y`, `2(Y + Rd) ≤ 2^q`. The weights
are `E_j = powUp(e, j)/2^P ≥ (e/2^P)^j ≥ e^{-2πδj}`, by binary powering with each product rounded
up. `e ≥ 2^P/expLow` is checked once. Each of the three quotients of a mode term is rounded up
(`ceilDiv`). Nothing about `p` is assumed: soundness uses only the checked inequalities.

Exact rational accumulation (the n = 2 `balBound`) would grow the denominator as the lcm of all `L²`
numerators. Measured on the T3 box, it costs 6.5 ms and 0.8 MB of kernel cache per fibre.

The kernel evaluates `mode3K`/`powUpK`, which use core operations (`Nat.shiftLeft` for `2^P`,
`Nat.blt`, `cond`, `Int.mul`). They are proved equal to the readable `mode3`/`powUp` by `rfl` plus
`simp`. Mathlib's `Monoid.npow` path for `2 ^ P` alone costs 0.2 ms per occurrence in the kernel.

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
| `KAM.CertificateSharp.V2.Fiber.TailTau` | `expLowQ`, `cLoQ`, `tailQ` (rational `T̂`, any `τ : ℕ`, any `E' ≥ e^{-2πδ(N+1)}`), `sdTail_le_tailQ` |
| `KAM.CertificateSharp.V2.Fiber.Enum2` | `balFold`, `cell2`, `row2`, `walk2` (diamond walk, generic in the mode function), `walk2_sound` (injection of `modeBox 2 N`); `pow2`, `ceilDiv`, `mulUp`, `powUp`, `powUp_ge`; `DBox2`, `mode3`, `mode3_spec`; kernel forms `mode3K`, `powUpK` with `mode3K_eq`, `powUpK_eq`; `smallDivisorSum_snoc2_le_walk` |
| `KAM.CertificateSharp.V2.Fiber.Site3` | `sdConst_ray_of_sdSum_le` (any `n`, `τ`); `abs_div_sub_div_le`; `FibWit`, `clockBox2`, `dboxOk`, `fibBound`, `fiberSiteOk`, `clock_reduce`, `sdConst_ray_of_fiberSiteOk`; `SiteWitG` (`classical`, `bite`, `fiber`), `siteOkG`, `sdConst_of_siteOkG` |
| `KAM.CertificateSharp.V2.Fiber.RouteAG` | `RefinedWitG`, `sitesOkG`, `refinedCoreG`, `refinedCoreG_sound`, `routeARefinedG`, `routeAV2G`; `RefinedWitG.ofRefined`, `refinedCoreG_ofRefined` (never worse) |
| `KAM.CertificateSharp.V2.Fiber.RouteBG` | `NumBQ.sitesOkG`, `NumBQ.cert_rayG`, `RefinedBWitG`, `refinedBCoreG`, `refinedBCoreG_sound`, `routeBRefinedG`, `routeV2G`; `refinedBCoreG_ofRefined` |
| `KAM.CertificateSharp.V2.Fiber.Shard` | `balFold_succ_of`, `row2_of_le`, `fiberPreOk`, `fiberSiteOk_of` (a site from a walk proved by shards) |
| `KAM.CertificateSharp.Freq.CubicNorm` | `noIntRootIn`, `noRatRoot_of`, `cubic_indep`, `cubN`, `cubY`, `beta_mul_cof`, `cubN_ne_zero`, `cubicH`, `cubicW`, `polyAbsUp`, `cubicDioOk`, `isDiophantine_of_cubicDioOk`; `isDiophantine_smulT`, `isDiophantine_mono` |
| `KAM.CertificateSharp.V2.Tests.Fiber3RouteB` | Toy B (route B, `n = 2`) through `routeBRefinedG` via `ofRefined` |
| `KAM.CertificateSharp.V2.Tests.Fiber3Toy` | T3 (`toyCert3`, `n = 3`, `τ = 2`) through `routeARefinedG` with fiber sites; Diophantine premise from `cubicDioOk` |
| `KAM.CertificateSharp.V2.Tests.Fiber3XLang` | Exact equalities produced by the Python mirror, checked by `decide +kernel` |

**Site checker.**

```
structure FibWit where N l J P e : ℕ; D : DBox2; B : ℚ
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
(`.bite w` ↦ `siteOk … (some w)`, `.classical` ↦ `siteOk … none`), so every existing refined
witness has an image with the same verdict (`refinedCoreG_ofRefined`, `refinedBCoreG_ofRefined`).
The route-B variant (`NumBQ.sitesOk`, three sites per stage) is the same substitution, in a new
module.

## 4. Cost model

- **Modes:** `2N(N+1)` fibres at `m = 2`, against `#{0 < |k|₁ ≤ N} ≈ 4N³/3` for the full box. The
  walk visits at most `(2N+1) 2^l ≤ 2(2N+1)²` cells; an empty cell is one comparison.
- **Cut-off:** `c_lo > 0` needs `N + 1 > τ/(3.14 δ) = τ/(6.28 b)`. In practice `T̂` must also be
  small next to `S`. That takes `2πδ(N+1)` of about `2τ ln(N+1) + ln(γ'^{-2}/S) + O(1)`, so
  `N ≈ (25–40)/(2πδ)` for the bites below.
- **Arithmetic per mode:** integers of `q + log₂ N` bits (`q = 64` on T3), two binary powers of
  `O(log j)` products of `P`-bit naturals (`P = 64`), three rounded quotients. The accumulator is a
  natural below `2^{P + log₂ S + 25}`.
- **Measured (kernel, `walk2 (mode3K …)`, T3 box, import base 3.39 GB):** 420 fibres 0.49 s,
  1,012 fibres 1.13 s, 1,860 fibres 2.50 s. That is about **1.2 ms and 215 KB of kernel cache per
  fibre** within one declaration, so about 2,500 fibres per declaration under the 4 GB cap and
  about 30,000 under the 10 GB guard. Larger walks are sharded (`Fiber/Shard.lean`).
- **Bites of the example (T3, `ρ = 9`):** `b ∈ {1, ½}`; `N = 2, 3`; 12 and 24 fibres; 0.04 s and
  0.07 s per site. The default build carries it.
- **SJS:** see the handoff. At the first-stage bite `b = 2.65·10⁻³` the proved tail needs
  `N ≈ 1,200–1,300`, i.e. `3·10⁶` fibres, about 1 h of kernel CPU in about 1,400 shards (4 GB cap).
  At `b = 6.6·10⁻⁴` it needs `N ≈ 5,000`, about `5·10⁷` fibres and 16–20 h. These are opt-in
  application builds, never in the default build.
- **Correction (1 November 2026, V2-BULK).** The 3.39 GB base above was measured on a non-module
  scratch file. As a `lake build` module the base is about 1.5–1.6 GB, so about 11,000 fibres fit per
  4 GB shard. The SJS shard counts become about 307, 1,275 and 5,278, not about 1,400 at the first
  bite (handoff V2-BULK, suspected errata; §7).

## 5. Python mirror

`scripts/certifier/fiber3.py`: an exact `Fraction` transcription of `fiberSiteOk` (same names,
same rounding, same enumeration order), a producer (choose `N`, `l`, `J`, `E₁`, `P`, `B`, `c`), and
`cubic_dio` (the checker `cubicDioOk` and the bound `W̄`). The cross-language test
`scripts/certifier/fiber3_xlang.py` writes and compares the expected naturals and booleans of
`Tests/Fiber3XLang.lean`. The kernel decides the same equalities.

## 6. Out of scope

General `n ≥ 4` enumeration (the fiber theorem is general; only the walk is `m = 2`);
higher-degree number fields; a positive three-frequency example for route B (route B needs
`ρ ≤ 1`, and T3 has `ρ = 9`); producer-side route selection (improvement #3); a bulk bound
for far-from-resonance fibres, which would cut the SJS walks by orders of magnitude (§4).

## 7. V2-BULK: a bulk bound for the fibres far from resonance

Date: 1 November 2026. Branch `v2-bulk` from `origin/main` at `01d36418` (owner question 2 of the
V2-3FREQ handoff, approved). Additive: new modules only. `SmallDivQ.lean` and the landed `Fiber/*`
modules stay byte-identical.

**Problem.** `walk2` evaluates every fibre `k' = (a, b)` with `0 < |a| + |b| ≤ N`, which is
`2N(N + 1)` fibres. For the SJS frequencies (§4) that is `3·10⁶–6·10⁷` fibres. Yet at the first
bite, only `6.9·10³` fibres have `|x + p| < 10⁻³`, and the others carry `1.8 %` of `S`
(mirror sweep, `ω' = (0.40288, −2.2037·10⁻⁴)`, `δ = 5.3·10⁻³`, `N = 1310`).

**Structure used.** Along a row `a` (fixed), `x_b = aω'₀ + bω'₁` is an arithmetic progression of
step `ω'₁`. The application orders coordinates so that `|ω'₁|` is small (for SJS it is the secular
frequency over the fast clock). A run of consecutive `b` on which `p` is constant and `x_b + p` keeps
one sign has `|x_b + p|` affine in `b`. The weights `e^{-2πδ(|a|+|b|)}` are geometric in `|b|`.
Both facts make a whole run summable from its two endpoints.

**The bound (any run, no Diophantine input).** Take a run `b = σ(lo + i)`, `i₀ ≤ i ≤ i₁`, with
`σ = ±1` and `|b| = lo + i`. Put `p = nearP(X(i₀))`, `Z(i) = X(i) + p·2^q` and
`Rd(i) = |a|R₀ + (lo + i)R₁`, all integers. Let `s` be the sign of `Z(i₀)`, `F = sZ − Rd` and
`G = sZ + Rd`. Both are affine in `i`. The check `F(i₀), F(i₁) > 0` and `2G(i₀), 2G(i₁) ≤ 2^q`
then gives, for every `i` in the run:

  `Λ/2^q ≤ |x_b + p| ≤ 1/2`, where `Λ = min(F(i₀), F(i₁))`.

This holds because an affine function on an interval lies above the smaller endpoint value. With
`x = e/2^P ≥ e^{-2πδ}` and `Σ_{j<2^t} x^j ≤ G_t/2^P` (a checked table, `G_{t+1} ≥ G_t(1 + x^{2^t})`),
the run's terms sum to at most

  `x^{|a|+lo+i₀}·(x^{|p|}·Λ⁻²·2^{2q} + [p ≠ 0](|p| − ½)⁻² + x·C₀)·G_t/2^P`.

That is one `mode3`-shaped rounded value with the weights replaced by `mulUp(powUp(j₀), G_t)`. A
single fibre is the case `i₀ = i₁`, `t = 0`, which is exactly `mode3`. Nothing about `p` or the
choice of runs is assumed: soundness uses only the checked endpoint inequalities.

**The walk.** Row `a = i − N` (bisection over `i < 2^l`, as in `walk2`) is split into two half-rows,
`b = lo + i ≥ 0` (`lo = 1` when `a = 0`) and `b = −(1 + i)`. Each half-row is bisected over
`i < 2^l`. A node `[i₀, i₀ + 2^t)` (clipped at `N − |a|`) is accepted as a run if the check passes
and either
- `rd·max(G(i₀), G(i₁)) ≤ rn·Λ`, so `|x + p|` varies by at most `rn/rd` and the loss is at most
  `(rn/rd)²`; or
- the run's value is at most `tol`.

Otherwise the node splits. A leaf (`t = 0`) must pass the check. The acceptance rule only affects cost
and tightness, never soundness. Near a crossing of an integer (a near-resonance) the walk ends
in single fibres, evaluated as by `mode3`. Elsewhere it takes long runs.

**Soundness glue.** `BCov S v` says that some per-fibre choice `(p_k, L_k)` on the finite mode set `S`
satisfies the fibered theorem's hypotheses, with summands summing to at most `v` (base `x`). It is
closed under disjoint unions (choices glued with `if k ∈ S`), subsets (terms are nonnegative) and
finite disjoint unions. The walk gives `BCov (modeBox 2 N) (s/2^P)`, and
`smallDivisorSum_snoc_le_fiber` with `E_j = x^j` finishes, as in `smallDivisorSum_snoc2_le_walk`.
The output has the same form: `E₁·3.3075 + s/2^P + tailQ`.

**Counts (exact mirror) and kernel projections (as built).**
- The node counts are from the exact mirror `scripts/certifier/fiber3_bulk.py` (node by node,
  `rn/rd = 5/4`, `tol = 10⁻⁹ S`, `P = 128`).
- No SJS walk, bulk or plain, was run in the kernel. Both kernel columns (minutes and 4 GB shards)
  are **projections** from the per-node law below (bulk) and the per-fibre law (plain walk).
- "Bulk minus plain-walk sum" is relative to a **floating-point** evaluation of the fibered sum
  (`sd_sum_fiber_np`: no rounding, no tail, true exponential), not to the exact landed walk. It also
  contains the fixed-point bias `e/2^P ≥ e^{−6.28δ}` that the landed walk shares.

| SJS bite (cubic γ) | `N` | plain-walk fibres | bulk nodes (values) | bulk minus float sum | kernel (projected): bulk / plain walk | 4 GB shards (projected): bulk / plain walk |
|---|---:|---:|---:|---:|---:|---:|
| `2.65·10⁻³` | 1,298 | `3.4·10⁶` | 44,568 (28,212) | +0.46 % | 1.0 min / 1.1 h | 4 / 307 |
| `1.33·10⁻³` | 2,647 | `1.4·10⁷` | 168,464 (94,579) | +0.22 % | 3.9 min / 4.7 h | 13 / 1,275 |
| `6.6·10⁻⁴` | 5,387 | `5.8·10⁷` | 653,691 (345,363) | +0.31 % | 15 min / 19 h | 51 / 5,278 |

Kernel laws, from `lake build` of shard modules importing `Fiber/BulkSite`:

- The base is 1.6 GB.
- The bulk walk costs 1.4 ms and about 180 KB of kernel cache per node. The 8,033-node probe took
  13 s and 3.05 GB.
- The plain walk costs 1.2 ms and 215 KB per fibre (V2-3FREQ).

**Interfaces (as built, new modules).**

| Module | Content |
|---|---|
| `Fiber/Bulk.lean` | `termX`, `BCov`, `BCov.union`/`subset`/`biUnion`; `gTabOk`, `gTabOk0`, `gTabOk0_spec`; `run_point`; `minN`, `maxN`, `sameSign`, `colX`/`colZ`/`colR`, `blkValK`, `blkK`, `blkValK_ge`, `blkK_spec`; `accOk`, `hrow`, `loP`, `rowB`, `walkB`, `hrSet`, `rowSet`, `hrow_spec`, `rowB_spec`, `walkB_sound`; `smallDivisorSum_snoc2_le_bulk` |
| `Fiber/BulkSite.lean` | `BulkWit`, `bulkSumOk`, `bulkSiteOk`, `sdConst_ray_of_snocBound`, `sdConst_ray_of_bulkSiteOk`; `bulkPreOk`, `bulkSiteOk_of` (shards); `SiteWitH` (`g`, `bulk`), `siteOkH`, `sdConst_of_siteOkH`, `siteOkH_g`, `siteOkH_bulk_of` |
| `Fiber/RouteH.lean` | `routeARefinedH`, `routeBRefinedH`; `RefinedWitH.ofG`, `RefinedBWitH.ofG` (same verdict); `routeV2H = routeV2G.orElse (routeARefinedH.orElse routeBRefinedH)` |
| `Tests/BulkToy.lean` | `bkFreq = (θ − 1, 3θ² + 24θ − 35, 1)`, `θ = ∛2`; premise, enclosure, one bulk site (452 nodes for 8,580 fibres), also from two shards |
| `Tests/BulkRouteB.lean` | `toyB3` through `routeBRefinedH` with two `.bulk` sites; `CertifiedTorus toyB3 cubicFreq` |
| `Tests/BulkXLang.lean` | 28 values of the mirror decided by the kernel (generated by `fiber3_bulk_xlang.py`) |

**Out of scope.** These are recorded in the handoff as owner questions:

- *A run across a half-integer crossing* (`p` changes inside the run). The float model puts its saving
  at a third of the nodes.
- *A one-sided integral bound for the run next to an integer crossing* (`Σ_j (F₀ + j d)⁻² ≤ F₀⁻² +
  1/(d(F₀ + d/2))`). It would make each crossing `O(1)` nodes instead of `O(log_{rn/rd})`, which is
  the route to about `10⁴` nodes at the first SJS bite.

The clock choice (owner question 3) stays with the application.

## 8. V2-BULK-RUNS: tent runs, crossing runs and a computed crossing cut

Date: 1 November 2026, on top of V2-BULK (orchestrator decision 1, owner question 1 of the V2-BULK
handoff). New modules only; the V2-BULK modules are unchanged.

**Why.** At the first SJS bite, `walkB` spends its 44,568 nodes on two kinds of half-rows:
- 738 half-rows with an integer crossing, at 28.5 nodes each. Isolating a crossing by bisection costs
  `O(log M)` nodes, and the ratio runs around it cost `O(log_{5/4})` more.
- 745 half-rows with a half-integer crossing, at 21.4 nodes each. A plain run cannot contain a
  change of `p`.

The 3,709 half-rows with no crossing cost 2.0 nodes each.

The mass map (float) shows how much each part matters:
- the ±3 fibres around integer crossings carry 86.9 % of `S`;
- no-crossing half-rows carry 12.5 %;
- the receding sides of crossings carry 0.24 % and the approaching sides 0.44 %;
- half-integer half-rows carry 0.001 %.

**Run types (`Fiber/BulkRuns.lean`).**
- *Tent run* (`tentK`), across a half-integer, with `p₀ = −⌊X(i₀)/2^q⌋`.
  - The certified distance is `min(Z − Rd, 2^q − Z − Rd)` with `Z = X + p₀2^q`. It is the minimum
    of two affine functions, so its four endpoint values bound it below.
  - Each fibre takes the nearer of `p₀` and `p₀ − 1`.
  - The weight uses `min(|p₀|, |p₀−1|)`, and the term `j = 0` uses `max(·, 1)`.
- *Crossing run* (`apK`): `p` constant and one sign, as `blkK`. The certified distance
  `F(i) = sZ − Rd` has the exact integer slope `d = sσC₁ − R₁`, and every fibre keeps its own lower
  bound `F(i)/2^q`.
  - Receding (`d ≥ 0`): `Σ_{j<n} x^j (F₀+jd)⁻² ≤ (1/u − x^n/(u+nd))/(d+(1−x)u)`, with
    `u = F₀ − d/2 > 0`. This is telescoping, and `x^n` is bounded below by `powDownK`, a
    floor-rounded binary power.
  - Approaching (`d < 0`): the weights are at most the largest, and
    `Σ_{k<n} (F₁+ke')⁻² ≤ n/((F₁−e'/2)(F₁+(n−½)e'))`.
  - Acceptance: the near end must be at least `s|d|` from the crossing; when approaching, the
    weights must also vary by at most `rn/rd`. A value at most `tol` is accepted too.
- *Weights at any length*: `gsumK n = ⌈2^P(2^P − powDownK n)/(2^P − e)⌉ ≥ 2^P Σ_{j<n} x^j`. This
  needs no table and needs `e < 2^P`. `blkK_spec_gen` is `blkK_spec` at the run's own length.

**Walk (`Fiber/Bulk2.lean`, `walkB2`).** A node `[i₀, i₀+n)` is handled by the first of these that
applies:
1. a single fibre;
2. a plain run, a tent run or a crossing run;
3. if the centre line crosses an integer (`crossCut`, one division), two options:
   - the crossing fibre alone plus one crossing run on each side;
   - otherwise the cut `[i₀, i_c−s)`, the single fibres `[i_c−s, i_c+s]` and `(i_c+s, i₀+n)`,
     each recursed;
4. otherwise its two halves.

Fuel bounds the recursion. Soundness is independent of every cut point and acceptance rule. Each
branch partitions the index interval (`runSet_split`), and each leaf is a run check with its own
theorem (`hnode_spec`, `walkB2_sound`, `smallDivisorSum_snoc2_le_bulk2`).

**Site and engine.** `Fiber/Bulk2Site.lean`: `bulk2SiteOk`, `bulk2SiteOk_of` (shards) and
`SiteWitK` (`h` = every `SiteWitH`, plus `bulk2`). `Fiber/RouteBK.lean`: route B with `SiteWitK`
sites, copied by script from `RouteBG`, with `ofH` (same verdict). Route A is not copied, because
the combined engine of applications is V2-CONSOL's.

**Measured (exact mirror `scripts/certifier/fiber3_bulk2.py`; `rn/rd = 5/4`, `tol = 10⁻⁹ S`,
`s = 2`, `P = 128`).** "Over float sum" is relative to a floating-point evaluation of the fibered
sum, as in §7.

| SJS bite (cubic γ) | fibres | `walkB` nodes / values | `walkB2` nodes / values | `walkB2` over float sum | certified `c` (`walkB2` / `walkB`) |
|---|---:|---:|---:|---:|---|
| `2.65·10⁻³` | `3.4·10⁶` | 44,568 / 28,212 | **13,719** / 20,425 | +0.40 % | `2.357·10⁻⁷` / `2.358·10⁻⁷` |
| `1.33·10⁻³` | `1.4·10⁷` | 168,464 / 94,579 | **38,028** / 56,265 | +0.22 % | |
| `6.6·10⁻⁴` | `5.8·10⁷` | 653,691 / 345,363 | **122,921** / 164,699 | +0.31 % | |

**Kernel cost tracks value computations, not nodes.** A value costs about three binary powers of
`P`-bit numbers. `walkB2` evaluates more values per node than `walkB` does, because a node that ends
up split may compute plain, tent and crossing values for their tolerance tests. Kernel probes at the
first bite (temporary shard modules, not committed; base about 1.5 GB):

| 512-row block | `walkB2` nodes, values | build, peak | `walkB` nodes, build, peak |
|---|---|---|---|
| typical | 1,860, 2,259 | 11 s, 2.0 GB | 8,033, 13 s, 3.05 GB |
| densest | 7,311, 12,942 | 19 s, 3.8 GB | 21,249, over 4 GB (killed) |

At the first bite, the estimate for the whole `walkB2` walk is about 50 s of kernel time in 4–5
shards. That is a modest gain over `walkB` (about 1 min projected, 4 shards). At the third bite the
values drop 2.1× (`walkB2` 164,699 against `walkB` 345,363). Possible further savings are listed in
the handoff.
