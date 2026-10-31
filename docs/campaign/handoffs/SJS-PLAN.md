# SJS-PLAN handoff: a costed plan to certify a KAM torus of the Sun–Jupiter–Saturn system

Brief: `/home/scott/kam-tools/briefs/SJS-PLAN.md` (Opus). Branch `sjs-plan`. LOCAL-COMMON and the AGENTS.md hard rules apply. The deliverable is
`docs/explorations/sjs-plan.md`, with its decision table first.

## Answer

The big target is feasible: about 15–300 CPU-h of kernel per torus, 80–560 GB of ledger, 1–20 h wall on a rented 48-core machine, under USD 200 of
compute, and 8–15k Lean lines. It needs a packed big-integer layer and a new chart. It does not need the hybrid or new theorem work.

| Item | Result |
|---|---|
| Theorem | Route B, isoenergetic, in a new synodic regular chart: T_raw = 10⁻³⁸·⁰ with a certified γ (10⁻³⁴·³ numerical). L = 45, 174 bits, S = 4.3·10⁶–1.3·10⁷ full lattice, β ≈ 3 |
| Torus | FH25's, reproduced in Python; moved to an explicit cubic frequency within 10⁻⁸ of ω_FH, γ = 2.8·10⁻⁷, τ = 2 |
| Numerics | lemma.farm can do it within 32 GB: 60–200 CPU-h. Needs a data volume |
| Kernel | (a) today's checker 7·10⁴–5·10⁵ CPU-h; (b) packed 14–143 (one `Nat`), 29–950 (8 GB shards), 210–6700 (default limit); (c) hybrid (b) × 1–1.4, **no kernel gain** |
| Hardware | lemma.farm has only 43 GB of free disk. Rent 48 cores, 256–768 GB, 1–2 TB NVMe for about a week |

## Read first

1. **The chart is new.** Delaunay's polydisc contains e = 0, so the landed ball arithmetic cannot work on it. The synodic chart needs a new `HamExpr` node for the regular Kepler
   equation: a trusted extension, on an SO-owned path. That needs a ruling.
2. **New kernel limits.** `Nat` ≤ 2²⁷ bytes unless `LEAN_NAT_MAX_SIZE` is set (a clean error). `Nat.shiftLeft` with exponent ≥ 2³² **panics** and kills the process. `Nat.pow` exponent ≤ 2²⁴.
   The SO track may want to know the first two.
3. **Several SJS-FEAS numbers are superseded** (`sjs-plan.md` §8), notably "hybrid + packed: 6–19 CPU-h". I did not edit SJS-FEAS (additive rule). The orchestrator may annotate it.
4. **The largest uncertainty is S(L):** measured to L ≈ 10, used at L = 45, a factor 3. Experiment X1 removes it and should run first, with the packed gate X2.

## Files

- `docs/explorations/sjs-plan.md`: the plan.
- `docs/campaign/handoffs/SJS-PLAN.md`: this file.
- `scripts/sjs/plan/`:

| File | Content |
|---|---|
| `sjs_torus.py`, `sjs_torus_diag.py` | FH25's translated-torus continuation and refinement; the diagnostic |
| `sjs_spectrum.py` | S(L, ρ) per chart, the regular chart, robust frame search |
| `sjs_chart.py` | Truncated Taylor algebra, majorants on tube and box, frames, torsion, bordered torsion |
| `sjs_plan_thresholds.py`, `sjs_plan_iso.py`, `sjs_plan_sens.py` | Mirrors on measured data, iso form, enclosure sensitivity |
| `sjs_hybrid.py` | The hybrid constant A on truncations |
| `sjs_intermediates.py` | Support of the checker's intermediates |
| `sjs_ops.py` | Operation counts on a hash-consed program, forward and reverse |
| `sjs_dioph.py` | Cubic frequencies and the norm-form γ |
| `packed_probe_gen.py`, `packed_probe_run.py`, `literal_probe_gen.py` | Kernel probes (E1, E2) |
| `sjs_plan_cost.py` | The cost model |
| `results/` | JSON and logs, about 400 kB. Torus files are not committed |

No Lean file was added or changed; `.drafts/` probes were deleted. The E2 writer (`lean --run`, `Lean.addDecl`, `writeModule`) was transient and is described in §3.1; the committed `literal_probe_gen.py` has the `run_cmd` form.

## Checks run and their output

- **Reproduction of FH25** (`results/torus_128.log`): |⟨T⟩⁻¹| 354.077 (FH 354.07743243); ⟨Ĝ⟩ 2.176574188839 (FH 2.17657418883872…); residual 1.67·10⁻⁹ at 128²×144 (FH 5.3·10⁻¹⁰ at 128³);
  sampled c_Xh 0.089 (FH 0.09), c_DXh 134 (FH 129).
- **Derivatives:** `sjs_chart.py` checks the third-order algebra against the exact gradient and Hessian of `sjs_torus.py`.
- **Threshold wrapper:** on FH's data, route B −48.49 against SJS-FEAS's −48.5; route A′ −64.5, which SJS-FEAS only estimated at −65…−70.
- **Lunar calibration:** the cost constants give 2.5 CPU-h for the real L = 20 torus; the gates measured 1.6–2.5.
- **Reversibility:** angle parts odd and action parts even to 3·10⁻¹² and 10⁻¹⁵ in both charts.
- **Kernel probes:** `results/packed_probes.jsonl`. Each theorem was checked by `decide +kernel` in its own process, one at a time, `nice -n 5`, with no overrides. The override was set only in E2's probes, none of which enters any tracked file.
- **`#print axioms`:** not applicable; no Lean theorem was added.
- **`scripts/lint_sources.sh`:** exits 1, with nothing from this package (no Lean file was added or changed):
  `check_lean_modules: PASS (1802 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; the ABI step then fails on a missing `.olean` in `.lake/build`, the known worktree
  failure LG00-PREP also reports (a whole-library build is forbidden here).

## Uncertainties

- S(45) from S(≤ 10): ×3. Largest intermediates: up to ×2, not included in the cost table.
- Majorants are sampled (8 000 points), not enclosed. ×20 costs 2.7 digits.
- Route B is the design mirror, 0.26 orders from Lean on R1. Stage constants use a fit of S(ω, δ), and the frame's effect on |k|₁ is neglected.
- Delaunay rows use box samples of a box that contains e = 0, so they flatter it.
- GMP timings: single runs at load 20–30, ±30 %. The one-`Nat` row extrapolates 12–35× in F; the default-limit row is inside the measured range.
- Op counts are for my draft program. Kepler's jet counts and the witness costs follow the landed pattern but no such node exists.
- The Lean line counts are estimates from landed analogues, and the calendar (4–6 weeks) is a guess at the campaign's pace, ×2 either way.
- I did not check whether FH's computer-assisted proof has since appeared. The novelty claim depends on it.

## Suspected errata and deviations

- **Pinned sources:** none suspected. FH25's data were reproduced. (Remarks in `sjs-plan.md` §8.)
- **Toolchain:** the `Nat.shiftLeft` panic above (Lean 4.35).
- **Deviation:** one probe, `t_full` at 10⁶ digits, peaked at **4.47 GB**, over the brief's "~4 GB". No process was killed, and it was not repeated. Python runs stayed under 4.4 GB.
- **Own correction during the study:** a first run of the torus failed from aliasing at a 0.45·N cut; the 2/3 rule cured it. An early claim that the secular slow decay is a polar-chart artefact was not supported by per-axis rates and was dropped.
- **SJS-FEAS** itself is listed in §8 of the plan.

## What remains

X1 and X2 first (the plan's §5.2), then the packages of §6.2. All of §6.3 needs the owner.
