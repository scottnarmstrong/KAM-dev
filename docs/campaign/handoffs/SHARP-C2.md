# Handoff SHARP-C2: certified frequency data (checker side)

30 October 2026, branch `sharp-c2` (merged `sharp-v2` for the fibered theorem of SHARP-L2B). Additive only; all
new files under `KAM/CertificateSharp/Freq/` and `Tests/`.

## Files
| File | Lines | Content |
|---|---:|---|
| `Freq/QuadraticCore.lean` | 157 | `quad_norm_eq`, `quad_tail_core`: the real norm tail |
| `Freq/QuadraticExact.lean` | 229 | `QuadData`, `quadFiniteOk(_sound)`, `QuadData.check`, **`isDiophantine_of_quadCheck`** |
| `Freq/QuadraticLunar.lean` | 226 | `isDiophantine_smul`; four lunar instances by `decide +kernel` |
| `Freq/SmallDivisorSum.lean` | 277 | box checker `SdsData`, **`sdsBound_sound`**, `sds_tail_le`, stage list `sdsStagesOk_sound` |
| `Freq/SmallDivisorFiber.lean` | 148 | fibered checker, **`sdsFiberBound_sound`** (data of `smallDivisorSum_snoc_le_fiber`) |
| `Tests/FreqTests.lean` | 55 | kernel tests on toy models, `#print axioms` |
| `scripts/certifier/c2_fiber_measure.lean.txt` | | the `#eval` measurement below |

## Approach
- **Quadratic γ\*.** For ω=(α,1), α a root of Ax²+Bx+C (Vieta form, α, α' irrational, rational enclosures):
  the test enumerates |k₁|<K₀, |k₂|≤M₂ with interval lower bounds, and checks the closed tail condition
  γ(1+Aγ) ≤ K₀²(1+a₀−AγD) (monotone in |k₁|², so no limit argument). The tail uses the norm N(k)∈ℤ∖0.
  Lunar results (K₀=2): θ frame γ=4923/100000 (infimum 0.049239; landed 1/21), rotated frame γ=2461/100000
  (infimum 0.024620; landed 1/42 by transfer), for both ν±. Gain +0.058 orders on γ⁴. `isDiophantine_smul`
  scales a constant to c•ω. Cubic part (`CubicDirection`) **not done** (optional, last).
- **S(ω,δ).** Per the orchestrator note the primary checker is the **fibered** one: for ω=(ω',1) it
  produces p_{k'}=⌊−k'·c+½⌋, L, L₀=|p|−½, E_j=E₁^j, from the frequency box of ω' only, with entries
  #{0<|k'|₁≤N} (2N for n=2). The box checker (`sdsBound`, all modes of ω, ≈4N² terms) is kept as the
  general-n fallback and as the reference for tests. Both bound π by 3.14<π<3.15 and e^{-b} by the degree-J
  Taylor polynomial of e^{6.28δ} (E₁ supplied short and checked `1 ≤ E₁·expLow`); the tail is `sdTail_le`
  at τ=1. Stage list: `SdsStage`/`sdsStagesOk` (any δ_s, `stageDelta δ₀ s = δ₀/2^s`).
- Refactor inside my files only: `sds_tail_le`, `dot_sub_boxDot_le` shared by both checkers.

## Checks
- `lake build KAM.CertificateSharp.Tests.FreqTests`: success, default heartbeats, no overrides.
- `scripts/lint_sources.sh`: line-length/module/anchor checks pass; its final ABI-scratch step errors
  because `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean` is absent from this worktree's
  snapshot (environmental, not from my files).
- `python3 -I scripts/gen_root_imports.py` run; `KAM.lean` committed.
- `#print axioms` of `isDiophantine_of_quadCheck`, the four `lunarNu*_exact` theorems, `sdsBound_sound`,
  `sdsStagesOk_sound`, `sdsFiberBound_sound`: all `[propext, Classical.choice, Quot.sound]`.
- Kernel tests (`decide +kernel`) only on the toy (0.618,1) and on the four lunar quadratic instances (tiny
  data, K₀=2); no lunar-scale S evaluation in the kernel.

## Measured comparison
Quadratic constant (landed → mine): θ 1/21=0.047619 → 0.04923; rotated 1/42=0.023810 → 0.02461.
Small-divisor sum, rotated lower torus ω'=ν₋−1, γ=1/42, δ₀=0.0023786, N=1157, J=12 (`#eval` of
`fiberBound`, ~1 min interpreted, exact ℚ): fiberCheck=true, data entries 2314 (box checker: 2,679,612
modes), bound **104832.6** (tail 501.4); with N=2000 bound **104331.3** (tail 0.005). The L2B enclosure of
S is [103570, 103768], so the loss is 0.5–0.7 %, as in SHARP-L2B. With γ*=0.02461 the tail at N=1157 falls to
469.3. The Rüssmann constant it replaces is 107× larger (design §2.6). The box checker was not run at
lunar scale (a 4N² evaluation exceeded 10 minutes interpreted, as expected).

## Uncertainties / not done
- Cubic Diophantine direction bound: not attempted.
- Fibered checker is for n=2 clients in the sense of m=1 data lists, but is stated for any m
  (cost 2N(N+1) entries for n=3).
- No kernel timing for the fibered checker at lunar scale (2314 entries, ℚ with ~14-digit denominators): expected
  modest, unmeasured; `E₁` should be passed with few digits (done in the `#eval`).
- The consumer (δ-dependent constant in the sharp theorem) is SHARP-PLUS's job.
- One `decide +kernel` comparison of the fibered and box bounds on the toy got stuck (`Rat` `≤` against a
  product); dropped, both side-condition tests pass.

## Errata / deviations
None found in pinned sources. Deviation: `Fin.snoc ω' 1` formulation requires the caller to bring the last
frequency to 1 (`smallDivisorSum_smul` in SHARP-L2B).
