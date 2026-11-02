# Handoff B1-CORE

Branch `inp-b1core`. New files (all in `KAM/EffectiveStability/`): `Domains.lean` (160 lines), `StoppedDrift.lean` (31), `FirstExit.lean` (165), `ChartFlow.lean` (148). Import order: Domains, StoppedDrift, FirstExit, ChartFlow (ChartFlow imports Domains, FirstExit and `KAM.ODE.Continuation`). No other file is touched.

## Lemmas (all with the requested signatures, no changes)
- Domains: defs `cyl cylClosed actionBox actionBoxClosed osc oscClosed oscAct` (as requested); `oscAct_apply`, `oscillatorAction_nonneg (p q) (j)`, `isOpen_cyl`, `isOpen_actionBox`, `isOpen_osc`, `continuous_oscAct`, `cyl_eq_prod`, `actionBoxClosed_eq_pi`, `isCompact_actionBoxClosed`, `isCompact_oscClosed`, `actionBoxClosed_subset_actionBox`, `cylClosed_subset_cyl`, `oscClosed_subset_osc` (all `{ε} (hε : 0 < ε) : X b ⊆ X (fun j => b j + ε)`), `add_angleShift_mem_cyl (hw : w ∈ cyl c) (k)`, `contDiff_oscAct : ContDiff ℝ ⊤ oscAct`, helper `oscActDeriv`, `hasFDerivAt_oscAct`, `fderiv_oscAct (w v) : fderiv ℝ oscAct w v = fun j => w.1 j * v.1 j + w.2 j * v.2 j`.
- StoppedDrift: `abs_sub_le_of_deriv_bound` (proved by the convex mean value inequality on `uIcc 0 s`, so no reflection is needed).
- FirstExit: helper `firstExit_box_nonneg` (forward time, sSup argument with the strict margin), `firstExit_box` (negative times by reflection), `firstExit_box_of_deriv`.
- ChartFlow: helper `exists_confined_aux` (shared abstract step: given the maximal solution, the stopped drift bound and the two continuation implications, produces real `T₁ > T` with `Ioo (-T₁) T₁ ⊆ eIoo Tm Tp`), `exists_confined_solution_compact`, `exists_confined_solution_periodic`.

## Checks
- `b_build.sh` of Domains, StoppedDrift, FirstExit, ChartFlow: all succeed, no warnings from these files.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, 25 tests OK, FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- `#print axioms` of `exists_confined_solution_compact`, `exists_confined_solution_periodic`, `firstExit_box`, `firstExit_box_of_deriv`, `abs_sub_le_of_deriv_bound`, `fderiv_oscAct`, `isCompact_oscClosed`: only `propext, Classical.choice, Quot.sound`.

## Notes
- `oscillatorAction_nonneg` takes `(p q : Fin n → ℝ) (j)`.
- The import path of the frozen def is `KAM.Frozen.Planetary.Defs.OscillatorAction`.
- T = 0 and η = 0 are covered (no case split needed).
- Design signals: none (all modules build in ~2 s). Errata: none.

## AUDIT FOCUS (kam-b1)
Track B (program B, overnight D71; nothing frozen). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B1-CORE.md (requested
signatures) and /root/code/KAM-inp-b1/.drafts/B/brief-B1-common.md; conventions docs/tracks/B/SPEC.md; consumer: the
B1-T / B1-E headlines in docs/tracks/B/FREEZE-PROPOSAL.md (statement audit freeze/STATEMENT-REVIEW-1.md).
Check: (1) each lemma's statement against the brief and that it is true as stated; (2) plan §7 Brief 2 reviewer duty:
TRACE the first-exit argument (FirstExit.lean) and the continuation step (ChartFlow.lean `exists_confined_aux`) and
confirm neither assumes the requested existence interval or the confinement conclusion; `hstop` must be a genuine
stopped bound (confinement assumed only on uIcc 0 t); the strict margin must be what excludes an exit; (3) edge cases
T = 0, η = 0, backward time, zero oscillator actions; (4) domain lemmas (compactness of oscClosed, cyl = univ ×ˢ
actionBox, fderiv_oscAct); (5) module hygiene (AGENTS rules 3, 4, 7), names; (6) axioms. Memory rule: every lean/lake
call wrapped in `systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
