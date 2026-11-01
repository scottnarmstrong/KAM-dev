**PASS WITH NOTES — MAG-SA-2, commit `716251f5`.** No blocking or major statement defect found.

1. **NOTE — Make the embedding consequence explicit.** [MagneticBarrier:37–44](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/mag/draft/MagneticBarrier.lean.txt:37) uses [IsPrimaryOnStrip:25–27](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/KAM/Frozen/Defs/IsPrimaryOnStrip.lean:25), which asserts equivariance alone. However, the combined conjuncts imply embedding: writing `Q = Re K.q`, invariance and the graph link give
   \[
   (\alpha\partial_0+\partial_1)Q=h'(P(Q,\theta_1)).
   \]
   A zero of `∂₀Q` propagates along the dense irrational flow, forcing it identically zero, contradicting degree one. Thus `∂₀Q>0`; the exact clock then supplies the quotient embedding required by [plan:97–100](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/plan-magnetic-barrier.md:97). **Fix:** document and prove this corollary, or expose monotonicity explicitly.

2. **NOTE — The state-type exception remains pending.** [MagField:23](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/mag/draft/MagField.lean.txt:23) correctly orders the product as `(q,p,φ)`, but differs from the plan and ambient-type rule, as acknowledged in [Decision 4:99–101](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/mag/FREEZE-PROPOSAL.md:99). **Fix:** record the explicit owner exception before freezing, or use `Fin 3 → ℝ`.

3. **MINOR — The elaboration-warning report is inaccurate.** [Proposal:79–80](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/mag/FREEZE-PROPOSAL.md:79) claims only a `sorry` warning. [MagEps:8](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/mag/draft/MagEps.lean.txt:8) and [MagH0:8](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/mag/draft/MagH0.lean.txt:8) additionally trigger the deprecated `Mathlib.Data.Real.Sqrt` import warning. **Fix:** use `Mathlib.Analysis.Real.Sqrt` and update the receipt.

The substantive checks passed:

- Exact arithmetic confirms `magAlpha = (43+18φ_g)/(74+31φ_g)`, both derivatives at `7/20`, the control sign/coefficient, every cosine coefficient, and the fallback scaling `4/25`.
- `magHamC` agrees exactly with `J + magH0 + magV` on reals. Its vector field is `((h′,1),(-V_q,-V_φ))`, correctly projecting to `magField`. Clock index `1`, frequency `![magAlpha,1]`, and all `2π` factors agree. Retaining the constant is compatible with energy zero through `J=-h(p)-V`.
- The positive open strip prevents derivative-default-zero loopholes. Reality makes the `.re` graph link faithful. Analyticity, both periods, quantifier order, local uniqueness, both time directions, and all three sign implications match the plan. No structural inconsistency or vacuous premise was found.
- Flux slacks are exactly **0.00798 below** and **0.00434 above**, consistent with the reported range. These numerical checks do not certify the graph bounds. Owner Decisions 1–3 and 5–6 are otherwise consistent with the stated scope.

Selective stdin elaboration **passed at default heartbeats**. Differentiability and real-agreement checks use `[propext, Classical.choice, Quot.sound]`; the draft theorem additionally uses `sorryAx`. The per-file module chain was not built. No files were edited; full lint was skipped because its fixture/ABI stages write files.

No new source erratum was established. The four [§8 candidates](/mnt/HC_Volume_106379410/kam-mag/KAM-mag/docs/explorations/plan-magnetic-barrier.md:545) remain carried forward; their original PDF claims were not independently rechecked.

