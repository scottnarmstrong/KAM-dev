# LP-W5A: combined audit handoff for LP3-KEP + LP3-COVERPERT + LP3-CELL + LP3-DRIFT (LP3, planar drift supplier with no arithmetic hypothesis)

Branch `inp-lp-w5a` (worktree `/root/code/KAM-inp-lp-w5a`) = `inp-lp-lp3drift` + `inp-lp` (through W4D). The four
packages were proved in sequence on one line of branches: KEP 50aaa4e0, COVERPERT bc848662, CELL 4d6256d1, DRIFT
92d0a5fe. Nothing in track LP is frozen.

**Package diff:** `git diff inp-lp HEAD -- KAM` (7 files, about 1,450 lines). Six new modules under
`KAM/Planetary/StrongAMD/Nek/` (`Kepler`, `Cover`, `Perturbation`, `Cells`, `Drift/Stopped`, `Drift`) plus the
regenerated root.

**Prover handoffs:** `docs/tracks/LP/audits/LP3-{KEP,COVERPERT,CELL,DRIFT}-handoff.md`. **Briefs:**
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP3-{KEP,COVERPERT,CELL,DRIFT}.md`.

**Plan:** `docs/tracks/LP/lp3/LP3-PLAN.md`, especially §1.1 and §2.1–§2.4. It passed an independent Opus plan review
with notes (`lp3/LP3-PLAN-REVIEW-1.md`); review changes C1–C5 are applied. The plan replaces MAIN's Diophantine drift
supplier (L12/L13, condition (5)) by the sealed frozen `partialConvex_nekhoroshev`, applied cellwise on a finite cover
of the sharp level set. The exponents are `a_n = 2/(6n² − 3n + 14)` and `b_n = 3/(6n² − 3n + 14)`.

**Import ruling (D58 in docs/DECISIONS.md):** LP modules may import the **sealed** frozen anchor
`KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the frozen definitions, never a provider. These
modules reach it directly (`Cells`) and through track P's `Exponential/Stopped`. Verify that no `KAM/Provider/*` module
is imported.

## Orchestrator checks (kam-lp)

- `lp_build.sh` of the 6 modules: built. `lp_lint.sh`: exit 0. Short-name check: OK.
- `#print axioms` of the main declarations of each package (in the prover handoffs): `[propext, Classical.choice,
  Quot.sound]`. In particular, the sealed anchor contributes no `sorryAx`.
- Every module docstring carries the SPEC §4 sentence.

## REPORT FORMAT

Four sections (LP3-KEP, LP3-COVERPERT, LP3-CELL, LP3-DRIFT), each with a verdict, then a combined verdict.

## AUDIT FOCUS

**Frozen interface fidelity (all four packages):**
- Every application of `partialConvex_nekhoroshev` must match its exact binder list and quantifier order
  (`PartialConvexNekhoroshev.lean:48–77`): `μ₀` after the domains and `h`, before `P`, `C`, the orbit; strict
  `μ < μ₀`.
- The sealed definitions must be used as defined: `HasDefiniteFastPart` (either sign), `IsPartialPerturbation`,
  `innerCore` (closed max-norm erosion), `IsSolutionOn`.

**LP3-KEP:**
- `h = planetaryKeplerC ν` and `−h` against `HasDefiniteFastPart` with `σ = ∓1`.
- The collar `ρ₀ = Imin/4`, with margin `Re z_i ≥ Imin/2`.
- `g` and `m` use `Ibar = Imax + Imin/2`.
- `hn : 1 ≤ n`.
- `lp3_kepler_data` constants depend only on `(ν, U)`.

**LP3-COVERPERT:**
- Widths: `rs = min(4rg, R/4)`, `η = rs/4`, `ρ = rs/8`.
- Collar, containment `partialComplexDomain G'_j D_j ρ ⊆ complexTube(core, R/2)`, slow gap.
- `P = fc/B₀`, cut to 0 off the tube; `IsPartialPerturbation` of `±P` for every centre in `𝓛_δ`.
- The `V_j` identity `degenerateHamiltonian (realPart h) (Re P ∘ cx) (B₀ μ) = liftChartHam ν μ`, with no time
  rescaling. This deviates from the brief's "divided by B₀"; it follows the plan.

**LP3-CELL:**
- `PartialConvexConclusion` must be a verbatim transcription of the frozen conclusion.
- `cell_threshold_uniform`: the minimum of `μ₀` over `ι × {±}`.
- `isSolutionOn_reverse_neg` (time reversal; sign conventions of `degenerateHamiltonian` and `hamiltonianVectorField`).
- `cell_drift_two_sided` (hypotheses are exactly the orbit premises on `uIcc 0 t`) and `kepler_cell_drift`.
- These are conditional helpers with distinct names, not source results.

**LP3-DRIFT:**
- The order of choices: `ρ₀(ν, 𝓛_δ)`, then `rg := min rg₀ (ρ₀/2)` (`isSharedTube_of_le`), then `R, B₀, P`, then the
  cover. There must be no cycle.
- Threshold bookkeeping: `μ₀ = ε₀/(2B₀)`, so `B₀μ < ε₀` strictly. The horizon is `exp(ε^{−a}) ≤ ε⁻¹ exp(ε^{−a})`.
- The sharp slow bound `C < B(c_j) − 3δ/8` (plan §2.4 step 4).
- `nek_stopped_drift_core`'s `hfield` and `hcell` are discharged in `Drift.lean`; the lemma is internal.
- **`lp_stopped_drift_nek_hstop`'s last hypothesis must be literally the `hstop` antecedent of
  `strongFirstExit_of_stopped_drift` (`Confinement.lean:177–182`), with `r := (B₀μ)^{b_n}`**, so that the assembly
  (LP3-PS, next) matches it by `exact`.
- The typing datum `actionVector ν z₀ ∈ strongLevelSet ν L δ`.
- No drift, AMD or confinement premise anywhere.
- Exponent bridges from `planetary*` to `partial*`.

## Source defects, deviations, design signals

No MAIN defect reported. Deviations:
- the generated root;
- COVERPERT bundles the cell statements for every centre in `𝓛_δ`, not only the finite cover (stronger);
- the `V_j` identity has no division by `B₀` (follows the plan, not the brief);
- KEP's collar is `Imin/4`, not `Imin/2`.

No design signals: every file is at most 329 lines and builds in under 15 s under the 4 GB cap.

**Tooling note:** `lp_lean.sh` previously ran with `autoImplicit` on (fixed 09:0x). All checks here used
`lp_build.sh`, which always used the lakefile options.
