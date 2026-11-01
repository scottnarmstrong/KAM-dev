# V2-ENERGY-ROW: the isoenergetic energy-row bound

Date: 1 November 2026. Step 1 of the V2-ENERGY brief; gate of
[improvement 2](../design/CERTIFIER-V2-IMPROVEMENTS.md). Mirror measurements only.

Reproduce (several minutes, one process; reads the T′ dry run through `KAM_LG00_TP`):

```sh
nice -n 10 python3 -B -I scripts/apost_sharp/energy_row.py --json OUT.json
```

## Result

**The gain is real but only on route B, and it changes no route selection.**

- **Route A refined has no slack.** Its checker already sets `HY := R.dh * sN` (`RouteARefined.lean:53`), and its
  theorems already take a free `Mh1`. So route A needs no change and no new engine.
- **Route B on LG00 T′ gains +1.62 decades (42×)**, from `y₀ = 6568` to `y₀ = 105`. Its margin at L = 20 with classical
  sites goes from 0.135× (fails) to 5.66×.
- **Route A still wins on T′:** 99× at L = 20 with classical sites, 17.5 times route B's new margin.
- **Lunar N = 65 gains nothing:** `M = 2.16` and `dh = 2.08`, and the energy row is not the binding branch.
- **It buys no L or kernel cost on either application.** The cheapest route stays route A. Route B moves from
  L = 23 to L = 21 at a 10× margin, still two digits behind route A's L = 19.
- **The certified `dh` is more than enough.** A sharper gradient bound adds exactly nothing on either route.

This qualifies the #1 study's "about 15 times more on LG00": that figure is right for route B, but route A has had this
gain all along.

## Where the slack is

The energy row is `Y = DH(K) N`, and every route needs a bound `y₀` of its row sum. It enters through the constant

```text
C_0 = s_T max(λ + t c_avg, λ_ω + y₀ c_avg)
```

| Route | Checker's `y₀` | Theorem |
|---|---|---|
| A refined | `R.dh * sN` | `hHY : N.HY = Mh1 * N.sN`, `Mh1` free |
| A frozen | `p.M * sN` | same theorem, at `Mh1 = M` |
| B refined | `p.M * sN` | `hy0 : N.y0 = M * N.sN`, `M` the standing one-size bound |
| B frozen | `p.M * sN` | same |

Once `y₀ < t`, the first branch of the `max` is the larger, so `y₀` stops mattering. That is why the table below stops
improving at `dh`.

## Candidates

| Data | `M` | certified `dh` | claim | sampled sup on `D` | `|s ω*|₁` | `y₀ = M s_N` | `y₀ = dh s_N` | `t` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| lunar N = 65 | 2.16 | 2.0777 | 2.078 | 2.0749 | 2.0305 | 5.06 | 4.87 | 24.3 |
| LG00 T′ L = 20 | 5170 | 82.544 | 82.7 | 71.80 | 64.79 | 6568 | 105.1 | 963 |

- **`dh`** is the disc-pass gradient sum, already checked by `checkHamClaim` (`HamFacts.dh`).
- **Sampled** is a floor for any pass over `D`, not a bound.
- **`|s ω*|₁`** is the value of the row on an exact torus (`Y = ωᵀ - (η^L)ᵀ`), a floor for `y₀` itself.

`M` is so large on LG00 because it is one number bounding five objects, and `‖D²X_H‖ ≈ 5156` sets it.

## Thresholds

`log10 e*`, changing only the gradient bound (`c_Th = 2 M₁`, `c_DTh = 2 M₂`). The two lunar tori agree to three decimals.

| Data | Route, sites | `M` | `dh` | sampled | `|s ω*|₁` | gain at `dh` |
|---|---|---:|---:|---:|---:|---:|
| lunar N = 65 | B classical | -18.271 | -18.271 | -18.271 | -18.271 | +0.000 |
| lunar N = 65 | B frequency | -15.125 | -15.125 | -15.125 | -15.125 | +0.000 |
| lunar N = 65 | A classical | -18.702 | -18.702 | -18.702 | -18.702 | +0.000 |
| lunar N = 65 | A frequency | -14.120 | -14.120 | -14.120 | -14.120 | +0.000 |
| LG00 T′ | B classical | -17.962 | -16.341 | -16.341 | -16.341 | +1.621 |
| LG00 T′ | B frequency | -16.382 | -14.820 | -14.820 | -14.820 | +1.562 |
| LG00 T′ | A classical | -18.437 | **-15.098** | -15.098 | -15.098 | already applied |
| LG00 T′ | A frequency | -16.489 | **-13.143** | -13.143 | -13.143 | already applied |

The route-A `M` entries are a what-if, to show what `dh` is already worth there (+3.34 decades). The bold figures are route
A as it stands. -15.098 reproduces the T′ figure in the LG00-T2 handoff.

Binding fields at `10^0.02 X⋆`:

- **LG00, route B at `dh`:** `J2` and `J3 cap0`.
- **Lunar, route B:** `J2` and `J3 cap5`, for every candidate.

`J3 cap0` is only co-binding on LG00: raising `μ` to `10⁻⁴` or `10⁻³` removes it from the list and moves the threshold by
at most 0.005 decades, on route A and route B alike.

## Margins and L

Margin is `e*/err`. T′ has `err = 8.06·10⁻¹⁸` at L = 20. For the other L, `err` is taken from the LG00 dry runs (L = 12,
18, 20, 21), interpolated at L = 19 and extrapolated above L = 21, at about 0.93 decades per digit. Rows marked † cannot be
certified on LG00 today (see below).

| Route on T′ | `log10 e*` | Margin at L = 20 | Least L with margin ≥ 10× |
|---|---:|---:|---:|
| A refined, classical (current) | -15.098 | 99× | **19** |
| B refined, classical, today | -17.962 | 0.135× | 23 |
| B refined, classical, with #2 | -16.341 | 5.66× | 21 |
| B refined, classical, with #2 and #1 | -16.048 | 11.1× | 20 |
| B refined, frequency, today † | -16.382 | 5.14× | 21 |
| B refined, frequency, with #2 † | -14.820 | 188× | 19 |
| A refined, frequency † | -13.143 | 8920× | 17 |

**Cost.** LG00's records give support ×1.24 and kernel calls ×1.3 from L = 18 to L = 20, about 14 % of calls per digit, and
30.1 CPU-h at L = 20. So #2 saves a route-B certificate about 2 digits (roughly a quarter of its calls), but route B with
#2 still costs about 2 digits more than route A. Dropping `FrameT` (F2) saves only 0.26 %, which does not close that gap.

On the lunar data nothing changes, and SO-2 and SO-3 use route A anyway.

## A finding outside the brief

**Route A with frequency sites would reach about 8900× on T′**, against 99× with classical sites. That would allow L = 17,
three digits below route A's L = 19 at a 10× margin. It is the largest lever seen for LG00, but it is not available today:

- `clockOk` (`SmallDivQ.lean`) needs an exact **positive** last coordinate, and LG00's box has `-41.48`, so the enhanced
  `siteOk` rejects it. This is presumably why `lg00RW` uses classical sites.
- These are float `c_freq × 1.01` design values, not certified sites, and the kernel cost of certifying them on LG00 was
  not measured.

Passing this to LG00-T2's route table seems worthwhile: a sign change of the frequency, or a check accepting a negative
clock, might be cheap.

## Consequence for the rest of the task

- **Route A:** no new engine, as the brief makes that conditional on a gain.
- **`Mh1`:** the checked claim is the existing `R.dh`. No sharper pass is justified, since nothing below `dh` moves any
  threshold.
- **Route B:** the additive theorems and engine proceed as the brief directs. They help any future application with
  `M ≫ dh` that selects route B; they do not change a current one.

## Scope and caveats

- **Thresholds, not certificates.** These are exact-constant mirrors with a double-precision bisection, and the same free
  design caps as [V2-STRUCTURED-B](V2-STRUCTURED-B.md).
- **Sites differ between routes.** Route B uses `kp = 5` and route A `kp = 3`. Treat differences under about 0.2 decades as
  ties. No conclusion above is that close.
- **T′ only.** T″ was still being computed when this ran.
- **The L column is an estimate** from the dry-run `err` values, not from new dry runs at those L.
- **Read only.** `lg00-cert` and the LG00-T2 scratch data were not modified.
