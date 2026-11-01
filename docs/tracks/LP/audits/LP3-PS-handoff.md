# LP3-PS handoff (planar theorem LP3-1: strong-AMD exponential safety, NO arithmetic hypothesis)

Branch `inp-lp-lp3ps`, track LP, non-frozen. No `sorry`/axiom/`maxHeartbeats`; no existing file edited
(only the generated `KAM/Root/Planetary.lean`, via `scripts/gen_root_imports.py`). No ingredient interface
mismatched. Imports the sealed anchor only through LP3-DRIFT (`Nek/Drift`); no provider.

## Files (510 lines, largest 190)
- `KAM/Planetary/StrongAMD/Nek/PlanarSafety.lean` (facade)
- `Nek/PlanarSafety/Orientation.lean` (110): `nekPlanarState`, `nekPlanarSol` (LP1's `PlanarSafeState/Sol`
  with the drift scale `√μ` replaced by a parameter `s`), `nekPlanarState.of_reflectPhase`,
  `nekPlanarSol.of_reflectPhase` (reuses the LP1 invariance lemmas by import).
- `Nek/PlanarSafety/Prograde.lean` (190): `nek_planar_safety_of_prograde` (`0 < totalMomentum` internal).
- `Nek/PlanarSafety/Main.lean` (187): `lp3_planar_strongAMD_safety`, `lp3_planar_strongAMD_safety_normalized`.

## Approach
LP1's `planar_safety_of_prograde` with one ingredient changed: `lp_stopped_drift_nek_hstop` (gives `rg, B0, c,
T₀, μs`) replaces `lp_stopped_drift`; the shared tube, barrier and osculating constants are taken for
`(sharedTube rg, δ/2)`. `r = (B0 μ)^{b_n}`; the supplier's `r ≤ 4 rg` is exactly the tube radius (`sharedTube`
is `cthickening (4 rg)`), so no extra threshold is needed; its budget conjunct feeds `LiftData`.
`hstop := hdr z₀ hI0 hd` by `exact` match. Constants: `AΛ = B0^b/2`, `Aa = B0^b (max C 0+1)(S+1)`,
`μ₀ = min (min μs μ2) (min (dS1/(2Aosc)) (dP1/(4Aosc)))`; `(B0 μ)^b = B0^b μ^b` (`mul_rpow`).
Orientation via `reflectPhase` as in LP1 (`L ≠ 0` from `totalMomentum_ne_zero_of_strongAMD_lt`).

## Statement
`lp3_planar_strongAMD_safety`: full elaborated signature printed by `#check` in `.drafts/ax_ps3.out`.
Token-level diff against `lp1_planar_strongAMD_safety` (`PlanarSafety/Main.lean:44–91`), exactly:
1. name; removed binder tokens `γ τ`, `(hγ : 0 < γ) (hτ : (n:ℝ) - 1 < τ)`, and the Diophantine premise
   `(∀ k ≠ 0, γ * modeSize k ^ (-τ) ≤ |∑ …|) →`;
2. `T`: `(-(1 / (2 * (τ + 1))))` ⟶ `(-planetaryTimeExponent n)`;
3. `Real.sqrt μ` ⟶ `μ ^ planetaryDriftExponent n` in the three lines (action, axis, AMD).
Nothing else differs (premises, 13 clauses, constant order, N10 inequalities, `hch`, `let T`). No prograde or
arithmetic premise. The normalized form adds the unused `_hνmax _hνle`, as LP1.

## Checks
- `lp_build.sh … Nek.PlanarSafety.Orientation`, `…Prograde`, `…Main`, `…PlanarSafety`: all built,
  `Build completed successfully`; no warning in my files (`lp_lean.sh` on each: empty).
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK). An earlier lint run
  flagged four lines over 100 characters in `Main.lean`; fixed, rerun clean.
- `main_shortname_check.py` on the four modules: `short-name check OK`, exit 0.
- `#print axioms` (`.drafts/ax_ps3.lean` via `lp_lean.sh`): `lp3_planar_strongAMD_safety`,
  `…_normalized`, `nek_planar_safety_of_prograde`: each exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- Statement text vs LP1 (token diff above); `T` as `let`; constant order (all constants before `μ`, `z₀`,
  depending on `(n, ν, A, δ)` only: `rg, B0, c, T₀, μs` come from the supplier for `L = strongLSet ν A`).
- `hstop` by `exact` from the supplier; `LiftData` fields (budget from supplier, `ball` from `r ≤ 4 rg`,
  `orient` is `0 < totalMomentum`, internal only).
- Drift-line constants: `AΛ = B0^b/2` vs `r/2`; `Aa`, AMD line `n * AΛ * μ^b`.
- `nekPlanarSol.of_reflectPhase` (`MovingUniqueOn`, osculating clauses): copy of the LP1 proof with `s` generic.
- Premise `actionVector ν z₀ ∈ strongLevelSet` of the supplier is derived from `A` and the AMD margin
  (`mem_strongLSet_actionVector`, `hlevel`), as in LP1.

## Not done / errata / deviations / design signals
Nothing omitted. No errata. Deviation: `nekPlanarState/Sol` parallel definitions (drift scale generic), per the
brief. No heartbeat or size problems (all files < 200 lines).
