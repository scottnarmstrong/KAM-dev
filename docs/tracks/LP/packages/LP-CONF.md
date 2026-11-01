# Package LP-CONF: sharp first exit (MAIN Lemma 14), as a conditional confinement helper

Wave 3. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
Base: `inp-lp` (wave 1 landed: THR, MOM, GEOMOD, DICT). Handoffs: `docs/tracks/LP/audits/`.

This package proves the topological first-exit argument of MAIN L14 with the stopped drift as an explicit
hypothesis (`hstop`), exactly the roadmap's internal helper. It is NOT the public theorem. Package LP-PS
discharges `hstop` from LP-NRR (Lemma 13) through the chart lift (package LP-LIFT). Give the helper a distinct
name and a docstring that says so.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 14, lines 468–500, with `source/AMENDMENTS.md`:
- **N2:** the shared `U`.
- **N6:** with the Lemma-13 route the stopped radius is `r` and the improvement is to `r/2` (not `r/4`).
  (39) still gives `C ≤ B(I(t)) − δ + nr/2 + Ω_B(r/2) ≤ B(I(t)) − 3δ/4`.

Roadmap §3 row 14 and the "representative new sharp confinement interface" in §3.

## Reuse

- `KAM/Planetary/AMD/ConfinementExit.lean` (`amd_exit_forward`, `amd_exit_backward`: the generic first-exit
  architecture).
- `KAM/Planetary/AMD/MovingODE.lean` (`moving_ode`), `KAM/ODE/{Maximal,Continuation,Uniqueness}.lean`.
- LP:
  - `Geometry.lean` (`BarrierState`, `strongBarrier_physical`, `exists_barrierCompact`);
  - `Modulus.lean` (`strongThresholdModulus`, monotonicity, `abs_strongThreshold_sub_le_modulus`);
  - `Continuation.lean` (`strongAMD_le_of_tube` (17), `maximal_global_of_barrier`, `maximal_global_of_tube`);
  - `Momentum.lean` (`strongAMD_sub_eq_sum`, `totalMomentum_const`).
- The frozen `MovingUniqueOn` and `IsMovingSolutionOn` definitions.
- Track P's `KAM/Planetary/AMD/Confinement.lean` (`amd`) as a template; do not use its `AMDBox` statements.

## Owned files

`KAM/Planetary/StrongAMD/Confinement.lean` (split with a facade if needed). Nothing else.

## Statement (the helper; expand all abbreviations into literal inequalities)

Data: `hν`, `2 ≤ n`, compact `U ⊆ chamber ν`, `0 < δ`, `0 < r`, `0 < T`, `0 ≤ μ` (or `0 < μ`, whichever the
field lemmas need; report).

Premises:
- `hbudget : n * r + strongThresholdModulus ν U r ≤ δ / 4`;
- an initial point `z₀` that is a physical state, with `I⁰ := Λ z₀` such that the closed `r`-ball (sup norm)
  about `I⁰` lies in `U`, and `strongAMD ν z₀ ≤ strongThreshold ν I⁰ − δ`;
- `hstop`: for every `OrdConnected J ∋ 0`, every `z` with `IsMovingSolutionOn ν μ J z` and `z 0 = z₀`, every
  `t ∈ J` with `|t| ≤ T`: if every `u ∈ uIcc 0 t` satisfies
  - `IsPhysicalState ν (z u)`,
  - `‖Λ(z u) − I⁰‖ ≤ r`,
  - `strongAMD ν (z u) ≤ strongThreshold ν (Λ(z u)) − δ/2`,

  then `‖Λ(z t) − I⁰‖ ≤ r/2`. These are MAIN's stopped conditions (40) in closed form. If the exit argument
  needs the strict form, use it and report.

Conclusion: `∃ z : ℝ → Phase (n*2)` with
- `z 0 = z₀`, `IsMovingSolutionOn ν μ (Icc (−T) T) z`, `MovingUniqueOn ν μ (Icc (−T) T) z`;
- for every `t ∈ Icc (−T) T`:
  - `IsPhysicalState ν (z t)`;
  - `‖Λ(z t) − I⁰‖ ≤ r/2`;
  - `strongAMD ν (z t) ≤ strongThreshold ν (Λ(z t)) − δ/2` (MAIN (8));
  - `BarrierState ν U (δ/2) (z t)`, so GEOMOD's constants give (9) and all pair separations.

Route: the maximal solution of the moving field on `collisionFreeDomain n` (`moving_ode`). Run a forward and a
backward first exit on the closed stopped set:
- inside it, `hstop` improves the drift to `r/2`;
- (17) with `hbudget` improves the AMD margin to `3δ/4`;
- GEOMOD makes the set compact and collision free;
- `maximal_global_of_barrier` rules out a finite maximal endpoint.

Uniqueness: from the ODE uniqueness on the open domain (`KAM/ODE/Uniqueness.lean`), in the frozen
`MovingUniqueOn` form.

Out of scope: discharging `hstop` (LP-PS via LP-NRR and LP-LIFT), the chart, the Newtonian reconstruction, and
the osculating clauses.

## Checks and stop condition

- `lp_build.sh` on each module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of the helper and its main lemmas.

Stop when done or blocked: report, never add a hypothesis silently. Expected size 600–1,500 lines.

## Handoff

`docs/tracks/LP/audits/LP-CONF-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-CONF.md`, then
`touch .drafts/READY-LP-CONF`.
