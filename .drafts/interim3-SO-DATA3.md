# SO-DATA3 interim note 3: step 4 STOPPED — families that cannot be split under 10 GB

Every run was alone under the kernel-probe lock with MemoryMax=10G and MemorySwapMax=0 (`scripts/spin_orbit/sodata3_kbuild.sh`). Logs are in `kam-data/so-data3/kpass/`, the
journal shows each OOM kill. Lower torus only; the upper torus was not started.

## Results: whole wall time and peak RSS (`/usr/bin/time -v`)

### Passes

| family | result | wall | peak |
|---|---|---:|---:|
| Core (refinedCore without bites, `|ω*|`, the algebraic box) | pass | 6.5 s | 1.5 GB |
| checkStatic | pass | 7.3 s | 1.6 GB |
| checkHamBounds | pass | 1:44 | 9.75 GB |
| checkHamClaim | pass | 1:41 | 10.24 GB RSS (9.76 GiB; under the 10 GiB cgroup cap) |
| checkEmbedding (whole) | pass | 0:35 | 3.2 GB |
| bite δ₁, l = 12 (earlier probe) | pass | 2:03 | 8.36 GB |

### OOM-killed at the cap

| family | result | wall / CPU | anonymous RSS at kill |
|---|---|---|---|
| checkGram (whole) | killed | ≈ 3 min CPU | 10.23 GB |
| Gram defect row 0 alone (`GramSplit`) | killed | 2:55 | ≈ 9.3 GB at the kill |
| Gram defect row 1 alone | killed | — | — |
| checkEnergy | killed | 2:17 CPU | 10.23 GB |
| checkInvariance | killed | — | 10.24 GB |

### Not run

These were stopped once the blockers were clear: Torsion, FrameT, FrameN (both need gramCheck; FrameT also needs
compose), FrameL, Graph, and bites b₀, b₁, b₂, δ₀.

## Diagnosis (design signal)
- **Energy, invariance and torsion (and FrameT) are each one `Slp.compose`.**
  - The kernel holds the 887-op fold of the Hamiltonian over the embedding models (`composeOps`, `ComposeState`)
    in one evaluation.
  - The landed checker has no entry point for an intermediate compose state given as data.
  - The state is every slot's model, so emitting it as literals is not feasible.
  - These checks cannot be split from the data side.
- **Gram** cannot be split below one defect row. Every row needs the whole Gram model matrix
  (`gramModels`: products of the DK models at cut-off 160). The row-literal split (`Data/GramSplit.lean`) is
  correct, but the row itself exceeds the cap.
- **What would fix it is a checker change**, outside this package: the compose and Gram checks verified against
  supplied intermediate models, one slot or one entry per theorem. For example:
  - a "compose with advice" whose per-step check `slot_k = op(slot_a, slot_b)` (within rounding) runs as its own
    kernel computation on literal slot models;
  - a cheaper kernel representation of the models.
- Other levers, not tried, each a package decision:
  - fewer terms per model: a lower cutoff for cfgLow (Gram), or a coarser truncation;
  - a smaller precision.
- Not mine to decide; reported per the brief.

## State
- Committed on `inp-sodata3`:
  - the generators `sodata3_passes.py` and `sodata3_kbuild.sh`;
  - the pass modules `Data/{Lower,Upper}/Pass/*` and `Passes.lean`;
  - `Data/GramSplit.lean` (gate-built; its lemmas are general and sound);
  - `LunarFinalR2V2.lean` (step 5), written but NOT built: it needs the passes.
- inp-sokdepth-oninp and inp-locksqrt are merged and rebuilt. After LOCK-SQRT, a fresh `#eval` of `Slp.balls` on the
  887-op program is byte-identical to before.
- Nothing is frozen, and no READY marker was created.

## Round 2: the levers already landed in sharp-v2 (lower torus, each run alone, capped)

| probe | live slots (products) | result |
|---|---|---|
| (a) `checkInvEnShared base`: pruned, shared invariance + energy | 215 of 887 (100 of 486) | OOM-killed at the cap (18:51, 10.27 GB anonymous) |
| energy alone: `Slp.composePruned` of `[v0]` (probe `EN.lean`) | 86 (26 products, 14 characters) | OOM-killed in about 1.5 min (18:53) |
| (b) `checkTorsion` | 887 unpruned, plus `gramCheck` | not run. It starts with the `gramCheck` whose single defect row already exceeds the cap, so it cannot fit. A pruned torsion would need 401 slots. |

**Live sets per output:**

| output | slots | products |
|---|---:|---:|
| v0 | 86 | 26 |
| d1 row 0 | 99 | 36 |
| d1 row 1 | 85 | 31 |
| d1 row 2 | 16 | 7 |
| d1 row 3 | 3 | 1 |

Even the smallest heavy piece (energy, 86 slots) exceeds 10 GB. Per-output pruning therefore cannot close the gap,
and no further split along the program is available.
