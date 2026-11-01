# V2-STRUCTURED-B: structured bounds of `hamComm` in route B

Date: 1 November 2026. Item 5 of the V2-FIXES brief; gate of
[improvement 1](../design/CERTIFIER-V2-IMPROVEMENTS.md). Report only: no Lean was written and no certificate changed.

Reproduce (several minutes, one process):

```sh
nice -n 10 python3 -B -I scripts/apost_sharp/structured_b.py --json OUT.json
```

## Verdict: do not implement

The bounds are rigorously smaller and `c_Th` does bind, but no acceptance changes on either application:

- **Lunar N = 65:** `c_Th` falls from 4 to 2.10, which raises route B's threshold by **0.44–0.48 decades**. Route A with
  frequency sites stays 0.56 decades ahead.
- **LG00 L = 20:** `c_Th` falls from 498 to 397, a gain of **0.11 decades**. Route A stays far ahead, and improvement 2
  is worth about 15 times more here.
- **`c_DTh` never matters:** halving it on the lunar data changes the threshold by 0.000.

If an application ever selects route B, implement `c_Th` only, and on LG00-like data do improvement 2 first.

## Method

With `S` the Hessian of `H` in `(θ, I)` and `Ω₀ = [[0, -1], [1, 0]]`, the Lean definition `hamComm = A Ω₀ - Ω₀ A`,
`A = DX_H`, is

```text
[[ S_II - S_θθ,  -(S_Iθ + S_θI) ],
 [ -(S_Iθ + S_θI),  S_θθ - S_II ]]
```

The script checks this sign table against the matrices on random Hessians. Each entry is `±(S_{a'b'} ∓ S_{ab})`, where
`a'` is the conjugate index.

- **Bound.** The checker's own slot balls (`Slp.balls`, mirrored by `toy_arith.slp_balls`) are combined entrywise before
  taking magnitudes, then summed by rows, as the matrix norm reads them. `c_DTh` is the same sum over third derivatives,
  which bounds the segment Lipschitz constant in the sup norm of `z`. Both hold on all of `D` for the reason the
  checker's own sums do: `ballsAux_sound` puts each slot value in its ball.
- **Sampling check.** The commutator is also evaluated directly at 4000 points of `D`. This confirms the bounds from below
  and shows how much a sharper rigorous method could still gain. Sampled values are not bounds.
- **Threshold.** Each certificate runs through the exact mirror of `routeBOk` in the form `RunBWit.num` gives it (iso,
  `y₀ = M s_N`, `Θ = σ_ω |box|`), changing only `c_Th` and `c_DTh`. The stage constants are exact; the bisection runs in
  double precision.

## The bounds

| Data | `2 M₁` | structured `c_Th` | sampled | `2 M₂` | structured `c_DTh` | sampled |
|---|---:|---:|---:|---:|---:|---:|
| lunar N = 65, lower | 4 | 2.1003 | 2.0746 | 2.994 | 1.4968 | 1.0906 |
| lunar N = 65, upper | 4 | 2.1004 | 2.0746 | 2.996 | 1.4970 | 1.0906 |
| LG00 L = 20 | 498 | 396.51 | 163.44 | 10340 | 9713.2 | 2821.0 |

- **Lunar:** the row sum is dominated by the constant `H_{I₁I₁} = 2`. The commutator counts it once and `2 M₁` counts it
  twice, which is the cancellation improvement 1 predicted. The structured `c_Th` is within 1.3 % of the sampled sup.
- **LG00:** the slot balls limit the gain, not the commutator. The sampled Hessian row sum is 135.7 against the checker's
  248.6, so the ball pass overestimates by up to a factor of 1.8 before any cancellation is applied. The sampled `c_Th` shows
  what a sharper pass could reach; that would be a different and larger piece of work.

## What binds

`c_Th` enters route B in two places: the torsion cap `t = c_Th s_Nt s_N + t_s`, which feeds `Q` through `C_gL`, and the
rate `sCab` of cap 5 (`Tab`). `c_DTh` enters only `sCab`, with a factor `δ`.

`log10 e*` by case:

| Data | Sites | checker | `c_Th` only | `c_DTh` only | both | gain | sampled | `c_Th = c_DTh = 0` |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| lunar N = 65 | classical | -18.271 | -17.790 | -18.271 | -17.790 | +0.481 | -17.781 | -16.762 |
| lunar N = 65 | frequency | -15.125 | -14.683 | -15.125 | -14.683 | +0.441 | -14.678 | -14.349 |
| LG00 L = 20 | classical | -17.962 | -17.854 | -17.962 | -17.854 | +0.108 | -17.482 | -16.766 |
| LG00 L = 20 | frequency | -16.382 | -16.275 | -16.382 | -16.275 | +0.108 | -15.903 | -15.188 |

The two lunar tori agree to three decimals. The binding fields are those failing at `10^0.02 X⋆`:

- **Lunar, checker bounds:** `J2` (tail decay) and `J3 cap5` (`Tab`).
- **Lunar, structured `c_Th`:** `J2` alone.
- **LG00:** `J2` alone in every case.

So the `c_Th` inequality does bind: directly through cap 5 on the lunar data, and through `t` inside `Q` in `J2`
everywhere. On the lunar data `e*` scales about as `t^-1.6` to `t^-1.7`. On LG00 the exponent is about 1.1, because `y₀ = M s_N ≈ 6600`
exceeds `t ≈ 960` in the energy row and absorbs most of the gain.

A grid over `kp ∈ {3, 4, 5}`, `t_s ∈ {1/10, 1, 10, 100}` and `θ ∈ {1/16, 1/8}` selects the same defaults (`kp = 5`,
`t_s = 1/10`, `θ = 1/16`) in every case, checker and structured alike, so the gains are not an artefact of those defaults.

## Acceptance

`log10 e*`, against the landed `err`:

| Data | `log10 err` | A classical | A frequency | B checker (cl / fr) | B structured (cl / fr) |
|---|---:|---:|---:|---:|---:|
| lunar lower | -15.80 | -18.70 | -14.12 | -18.27 / -15.13 | -17.79 / -14.68 |
| lunar upper | -15.74 | -18.70 | -14.12 | -18.27 / -15.13 | -17.79 / -14.68 |
| LG00 L = 20 | -17.09 | -15.10 | not evaluated | -17.96 / -16.38 | -17.85 / -16.28 |

- **No case flips.** Every B entry that passes `err` at the checker's bounds passes at the structured ones, and every one
  that fails still fails.
- **Lunar:** the frequency route B margin grows from 0.67 to 1.11 decades (lower torus), still short of route A's 1.68.
- **LG00:** route A's margin is 2.0 decades with classical sites. Route B fails `err` at classical sites either way.

## Interaction with improvement 2

Replacing `y₀ = M s_N` by `y₀ = dh s_N` was evaluated as a what-if. It is a theorem-interface change that does not exist
today.

| Data | Sites | `y₀` alone | `y₀` and structured | B after both | Route A classical |
|---|---|---:|---:|---:|---:|
| lunar N = 65 | either | +0.000 | as structured alone | -17.79 / -14.68 | -18.70 |
| LG00 L = 20 | classical | +1.621 | +1.914 | -16.05 | -15.10 |
| LG00 L = 20 | frequency | +1.562 | +1.820 | -14.56 | -15.10 |

On LG00, where `M = 5170` and `dh = 82.7`, improvement 2 is about 15 times the gain of improvement 1. On the lunar data
`M = 2.16` and `dh = 2.08`, so it does nothing. After both, `J3 cap0` (the `|DK|` cap) starts to bind on LG00.

## Cost, if it were built

- **Checking:** negligible. In Python the structured sums take 0.5 ms (lunar) and 6 ms (LG00), on top of ball passes of
  11 ms and 80 ms.
- **Kernel, measured analogue:** LG00's ledger gives 6.8 s for the `d2` row module and 6.4–6.6 s for each `d3` row module.
  A `c_Th` check has the shape of one more `d2` pass. A `c_DTh` check would cost four more `d3` passes and buy nothing.
- **Lean, estimated and not attempted:** an additive `RunBWit.num` with a free `c_Th`, the entry identity for `hamComm` in
  jet slots, and ball membership from `ballsAux_sound`. `lip` can stay at `2 M₂` through `norm_hamComm_sub_le_of`.

## When to reopen

Reopen for `c_Th` only, when all of these hold:

1. An application selects route B because route A fails or costs too much.
2. Its Hessian is dominated by a block that the commutator counts once, as for a mechanical `p²/2` term.
3. Its slot balls are close to the true sup, so the cancellation is not lost in the ball pass.

If `M ≫ dh`, improvement 2 comes first.

## Scope and caveats

- **Thresholds, not certificates.** No kernel run and no `refinedBCore` witness stand behind these numbers. The caps are
  the free design caps (+5 %) and the stage-0 weights are the least `Fits` allows.
- **Sites differ between routes.** Route B's frequency sites are float `c_freq` values with `kp = 5`. Route A's lunar
  frequency sites are `site_constants` (×1.01) with `kp = 3`. Treat cross-route differences under about 0.2 decades as ties.
- **Scope of "lunar".** The two N = 65 band tori only. The lock's librational torus was not evaluated.
- **Reconstructed inputs.** SO's generated state and LG00's `gen_L20/state.pkl` are on a volume not mounted here. Domains
  and claims come from the landed Lean literals, jets from the mirrors, and the LG00 chart from
  `lg00_hptorus_sqrt_N512h.pkl` in the `lg00-prep` worktree. Two checks validate this:
  - the recomputed sums match the landed claims and LG00's measured values (`248.639`, `5156.47`, `558.117`, `82.5444`);
  - the route-A figure reproduces LG00's reported threshold, `7.9·10⁻¹⁶`.
- **Read only.** `git status` of `lg00-cert` is clean after the runs.
