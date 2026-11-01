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

**Measured on SJS (float model of the walk, `rn/rd = 5/4`, `tol = 10⁻⁹ S`).** First bite: the bound
is `1.0027 ×` the full walk's sum. It takes `2.2·10³` single fibres plus `2.1·10⁴` runs, `4.2·10⁴`
visited nodes in all, against `3.4·10⁶` fibres. The exact mirror's counts, the other bites and a
kernel timing are in the handoff.

**Interfaces (new modules).**

| Module | Content |
|---|---|
| `Fiber/Bulk.lean` | `termX`, `BCov` and its union/subset lemmas; `gTabOk` (geometric table); `blk`/`blkK` (run check and value), `blk_spec`; `hrow`, `rowB`, `walkB` and the kernel forms; `walkB_sound`; `smallDivisorSum_snoc2_le_bulk` |
| `Fiber/BulkSite.lean` | `BulkWit`, `bulkSiteOk`, `sdConst_ray_of_bulkSiteOk`; `SiteWitH` (`g` = every landed site, `bulk`), `siteOkH`, `sdConst_of_siteOkH` |
| `Fiber/RouteH.lean` | route A and route B with `siteOkH` sites (`routeARefinedH`, `routeBRefinedH`), and embeddings of the `G` witnesses with the same verdict |
| `Tests/BulkToy.lean` | a cubic three-frequency vector with a slow coordinate; one bulk site decided by the kernel, with `SDConst` from `cubicDioOk` |
| `scripts/certifier/fiber3_bulk.py` | exact mirror of `walkB` (same rounding, same order), producer, SJS counts |

**Out of scope.** A run across a half-integer crossing, where `p` changes inside the run. It would
cut the visited nodes by a further third on SJS (float model: `2.8·10⁴` instead of `4.2·10⁴`); it is
left as an optional extension. Clock choice (owner question 3) stays with the application.
