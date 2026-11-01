# LP3-DESIGN handoff

Package LP3-DESIGN ([brief](../packages/LP3-DESIGN.md)), 2026-11-01. Deliverable: [`LP3-PLAN.md`](LP3-PLAN.md).
Docs only: no Lean or Lake run, no code changed.

## Summary

LP3 (the sharp strong Laskar–Petit threshold with no arithmetic hypothesis) needs **one new drift supplier**. All
other parts of LP1/LP2 are reused unchanged:

* the barrier (L2–L6);
* the charts (L7, L17);
* the whole-sublevel domains (L8, L18; LP-DOM/DOMX, LP-SP-DOM/DOMX);
* the chart lift (LP-LIFT);
* the conditional first exit (LP-CONF `strongFirstExit_of_stopped_drift` and its spatial twin);
* osculating elements (L16) and reconstruction.

The sealed `KAM.Nekhoroshev.partialConvex_nekhoroshev` gives the drift `ν^{b_n}/2` on a stopped interval. With
`r := (B₀μ)^{b_n}` this is exactly the `hstop` shape "drift `≤ r/2` on the stopped `r`-tube" that LP-CONF consumes.
Results:

* time `T₀ exp(c μ^{−a_n})`;
* drift `O(μ^{b_n})`;
* `a_n = 2/(6n²−3n+14)`, `b_n = 3/(6n²−3n+14)` (`planetary*Exponent n`, fast dimension `n`, in both the planar and
  the spatial case).

## Key decisions

1. **Finite cover, per-cell sharp levels.** The frozen `μ₀` depends on `(G, G′, D)`, so the plan covers `𝓛_δ` by
   finitely many balls `G_j = ball(c_j, η)` with centres `c_j ∈ 𝓛_δ`. Each cell has
   `D_j = slowBall(B(c_j) − 5δ/16)`, so the levels are local and sharp; one common level would be the `AMDBox`
   problem again. The thresholds are minimized over the finite cover.
2. **One normalized perturbation.** `P = fc/B₀`, with `fc` from `exists_strongTube`, satisfies
   `IsPartialPerturbation` on every cell via `strongCore_containment`. `ν = B₀μ`.
3. **Sharpened stopped slow bound.** `C < B(c_j) − 3δ/8` uses `Ω_B(4r_g) ≤ δ/16` twice. It reserves a `δ/16` AMD
   collar below `D_j` for `innerCore D_j (ν^{b_n})`. The LP1 bound `C ≤ B(I⁰) − δ/4` is insufficient.
4. **No sign adapter; time-reversal adapter only for `t < 0`.** `HasDefiniteFastPart` allows `σ = −1`. Negative
   times use `(−h, −P)` on the reversed curve, as track P does.
5. **No period or time conversion.** Radian angles (`fastShift`) and physical time match the LP chart lift exactly.
6. **Import policy.** Following the root-b8 ruling of 2026-11-01, LP modules may import the sealed anchor (track P's
   `Stopped.lean:9` is the precedent), and never the provider. The common prover brief still forbids importing frozen
   theorem anchors, so every LP3 Lean brief must quote the ruling.

## Packages (about 2,300 lines in 12 files)

LP3-KEP, LP3-COVER, LP3-PERT, LP3-ONE (an early one-cell test of the frozen interface), LP3-DRIFT, LP3-PS, then the
spatial LP3-SP-COVER, LP3-SP-DRIFT and LP3-SP-SAFE after LP-SP-SAFE lands. Optionally, a generic-in-`k` cellwise
lemma would share the drift between the planar and spatial cases.

## Open risks

Detailed in LP3-PLAN §6:

* the finite-cover uniformity of `μ₀` (R1);
* erosion versus collar, resting on the sharpened bound (R2);
* the safe-state predicates hard-code `√μ` (R11);
* the brief conflict on importing frozen theorems (R12);
* the dependency on unlanded LP2 spatial modules (R13).

Candidate owner decisions O-1 (exponent names), O-2 (generalize the predicates or add parallel ones) and O-3
(anchor status of LP3) are open.
