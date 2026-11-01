# LP-PS audit handoff: the planar theorem LP1 (MAIN Theorem 15 with Lemma 16) and LP0 (Lemma 5)

Branch `inp-lp-psaud` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp-ps` (74ebebb1) + `inp-lp` (every other planar
package: landed or audited and landing). The package diff is `git diff inp-lp...HEAD -- KAM`: the `PlanarSafety`
facade and its parts (Orientation, Constants, Prograde, Main), plus the regenerated root, about 780 lines. Every
ingredient is already audited (LP-BAR1, W1B, W2A, OSC, W3B, W3C) and is NOT in scope. Nothing in track LP is
frozen.

Prover handoff: `docs/tracks/LP/audits/LP-PS-handoff.md`. Brief:
`/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-PS.md`.

Target statements: `docs/tracks/LP/FREEZE-PROPOSAL.md` draft 2, §2 (LP0) and §3 (LP1), reviewed twice
(`docs/tracks/LP/freeze/STATEMENT-REVIEW-{1,2}.md`; review 2 PASS for the theorem types). The orchestrator's
verification file `docs/tracks/LP/freeze/verification-draft-2.lean.txt` states the draft-2 LP0 and LP1 verbatim
and closes them by `lp0_planar_barrier` and `lp1_planar_strongAMD_safety_normalized`. Capped `lp_lean`, exit 0,
axioms `[propext, Classical.choice, Quot.sound]`. Please re-run that check, capped.

Source: `docs/tracks/LP/source/MAIN.md` Theorem 15 (502–506), Lemma 14 (468–500), Lemma 16 (508–529), Lemma 5
(162–175), §1 (6)–(9), with `docs/tracks/LP/source/AMENDMENTS.md` (N2, N6, N7, N10).

## REPORT FORMAT

One verdict for the package, with a section per main theorem: `lp1_planar_strongAMD_safety` (general),
`…_normalized` (the draft-2 text), `…_halfInteger`, `lp0_planar_barrier`, and `planar_safety_of_prograde`
(internal).

## AUDIT FOCUS

- **Statement fidelity:**
  - `lp1_planar_strongAMD_safety_normalized` IS the draft-2 LP1 text (re-run the verification).
  - The general theorem differs only by dropping `hνmax` and `hνle`; it is a pure generalization of the
    equation, with μ read as a mass scale (review 1, F5).
- **No conclusion-shaped premise anywhere in the public theorems.** `0 < totalMomentum` appears only in the
  internal `planar_safety_of_prograde`, and is discharged by the reflection.
- **Constant order:** every constant, including `Aelem` and the N10 inequalities, is chosen before `μ` and
  `z₀`, and depends only on `(n, ν, A, δ, γ, τ)`.
- **Discharge of `hstop`:**
  - `StoppedOn` is CONF's antecedent by `rfl`;
  - both time directions use `uIcc 0 t`;
  - the time bound matches NRR's;
  - `lpStoppedBlock` is `lpBlock` by `rfl`;
  - NRR's widths are used consistently.
- **Orientation reduction:** `PlanarSafeSol.of_reflectPhase`, in particular `MovingUniqueOn` and the
  osculating clauses (`oscVelocity` of a reflected state).
- **LP0:** the compact `K := K_barrier ∩ {E_i ≤ −c}` (closedness, negative energies).

---

# Prover handoff (LP-PS, as delivered)

# LP-PS handoff (planar theorem LP1, MAIN Theorem 15 with Lemmas 14, 16; track LP, non-frozen)

Branch `inp-lp-ps`. No `sorry`/axiom/`maxHeartbeats`; no existing file edited (only the generated
`KAM/Root/Planetary.lean`, via `scripts/gen_root_imports.py`). Statement = draft 1 of
`FREEZE-PROPOSAL.md` §3 **plus the TARGET DELTA** (statement review F2: constant `Aelem`, N10
inequalities, osculating validity clause) and LP0 in the review's source-complete F1 text.
Premises: exactly those of LP1 minus `hνmax`, `hνle`. No ingredient interface mismatched.

## Files (779 lines in total, largest 298)
- `KAM/Planetary/StrongAMD/PlanarSafety.lean` (facade)
- `PlanarSafety/Orientation.lean` (173): `PlanarSafeState`, `PlanarSafeSol`, reflection transport
  (`PlanarSafeState.of_reflectPhase`, `PlanarSafeSol.of_reflectPhase`), invariance of `oscVelocity`,
  `oscEccVector`, `oscPeri`, `oscApo`, `keplerPeri`, `keplerApo`, `actionVector`; `MovingUniqueOn` transported.
- `PlanarSafety/Constants.lean` (107): `exists_budget_radius` (n r + Ω_B(r) ≤ δ/4 for small r),
  `keplerAxis_eq_action_sq`, `norm_axis_sub_le` (MAIN line 497), `mem_strongLSet_actionVector`.
- `PlanarSafety/Prograde.lean` (201): `planar_safety_of_prograde` (L > 0 case; constants, `hstop` discharge, CONF).
- `PlanarSafety/Main.lean` (298): `lp1_planar_strongAMD_safety`, `…_normalized` (with `hνmax`, `hνle`, unused),
  `…_halfInteger` (τ = n − 1/2, exponent `1/(2n+1)` via `scaleExponent_planar`), `lp0_planar_barrier` (F1 text).
- `KAM/Root/Planetary.lean` regenerated (+ `PlanarSafety` imports).

## Statements
`lp1_planar_strongAMD_safety`: the elaborated signature is the text of the target (copy from
`Main.lean:36–89`; `#check` output in `.drafts/axioms_ps.txt`):
`∃ μ₀ c T₀ AΛ Aa dStar dPair Aosc Aelem, 0<… (nine) ∧ Aosc*μ₀ ≤ dStar/2 ∧ 2*(Aosc*μ₀) ≤ dPair/2 ∧ ∀ μ ∈ (0,μ₀], ∀ z₀, …
let T := T₀ exp(c μ^{-(1/(2(τ+1)))}); ∃ z, z 0 = z₀ ∧ IsMovingSolutionOn ∧ MovingUniqueOn ∧ IsNewtonSolutionOn ∧ ∀ t ∈ Icc (-T) T, (13 clauses)`.
Clauses per time: physical; `∃ hcht` AMD ≤ B − δ/2; Λ drift ≤ AΛ√μ; axis drift ≤ Aa√μ; AMD drift ≤ nAΛ√μ; perihelia;
adjacent gaps; star distances; pair distances; **osculating validity** (`oscEnergy<0`, `0<oscAxis`, `oscEcc<1`,
`oscPeri ≤ |q| ≤ oscApo`, `|Δa|+|Δe⃗| ≤ Aelem μ`); peri/apo errors `≤ Aosc μ`; `dStar/2 ≤ oscPeri`; half gaps.
The statement is written with `planeLength (keplerEccVector …)` literally in place of the proposal's `ecc` abbrev.
`lp0_planar_barrier`: F1 text (deficit-list barrier, compact `K` with `NoCollision` and negative energy, `z ∈ K`,
`m ≤ |L_i|`, `0 < L_i · L`), exactly as in `STATEMENT-REVIEW-1.md` F1 up to the same `ecc` unfolding.

## Approach
Constants (before μ, z₀): `L = strongLSet ν A`; shared tube `U` (`exists_isSharedTube`); `lp_stopped_drift` with
`D₀ = 1` (`μ₁, c, T₀, w`); `strongBarrier_physical` and `osculating_barrier` for `(U, δ/2)`; budget radius `r₁`;
`r₂ = min r₁ r_g`; `dStar = min dS₁ dS₂`, `dPair = min dP₁ dP₂`; `AΛ = 1/2`; `Aa = (max C 0 + 1)(Σ ν⁻² + 1)`
(C a sup-norm bound of `U`); `Aelem = A`, `Aosc` from OSC; `μ₀ = min(μ₁, μ₂, r₂², dS₁/(2Aosc), dP₁/(4Aosc))`
(N10 for both pairs of constants). With `r = 1·√μ`: `LiftData` (physical, ball ⊆ U via `cthickening_mono`, budget,
`amd` from `hC0`, `orient`), `hstop` from `lpChartLift_premises` (block `lpStoppedBlock` = `lpBlock` by `rfl`) and
`lp_stopped_drift` with `J = uIcc 0 t`, `t₁ = t`; then `strongFirstExit_of_stopped_drift`; conclusions from CONF,
`strongBarrier_physical`, `osculating_barrier`, `strongAMD_sub_eq_sum`, `norm_axis_sub_le`,
`isNewtonSolutionOn_of_isMovingSolutionOn`. Orientation: `totalMomentum_ne_zero_of_strongAMD_lt` (with
`strongThreshold_le_action`) gives `L ≠ 0`; `L < 0` is handled by `reflectPhase z₀` and transport.
Mass normalization is not used.

## Checks
- Stale modules rebuilt in import order through `lp_build.sh` (NonresonantScale, NonresonantReuse.*, Osculating,
  ChartLift, Confinement, Reflection, …), then `PlanarSafety.{Orientation,Constants,Prograde,Main}` and the facade:
  all `Build completed successfully`, no warning in my files.
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
- `main_shortname_check.py` on the five modules: `short-name check OK`, exit 0 (first run flagged `.reflect`; renamed `.of_reflectPhase`).
- grep for `sorry|maxHeartbeats|axiom|admit|unsafe|opaque` in the new files: empty.
- `#print axioms` (`.drafts/ax_ps.lean` via `lp_lean.sh`): `lp1_planar_strongAMD_safety`, `…_normalized`,
  `…_halfInteger`, `lp0_planar_barrier`, `planar_safety_of_prograde`: each exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS
- Statement text against the delta (F2) and F1; the 13-clause order; `T` as a `let`.
- Constant order: `Aelem` and the N10 inequalities depend on `(ν, A, δ, γ, τ)` only; `μ₀` includes the extra
  `dS₁/(2Aosc)`, `dP₁/(4Aosc)` so that the inequalities hold for the *min* constants.
- `hstop` discharge: strict stopped set (`StoppedOn` by `rfl`); both time directions use `uIcc 0 t`;
  `|t| ≤ T` matches the drift time `T₀ exp(c μ^{-scaleExponent τ})` (`scaleExponent τ = 1/(2(τ+1))` by `rfl`).
- Orientation reduction: `PlanarSafeSol.of_reflectPhase`, in particular `MovingUniqueOn` and the osculating clauses.
- LP0 F1: compact `K` is `K_barrier ∩ {E_i ≤ −c}` (closed by continuity of the energy on the collision-free set).
- `hch` is typing data; the `0 < totalMomentum` premise exists only in the internal `planar_safety_of_prograde`.

## Not done / source defects / deviations / design signals
- Nothing in the brief omitted. No errata found. Deviations: `ecc` unfolded literally; `PlanarSafeState/Sol`
  helper definitions (unfold to the statement clauses). No heartbeat, OOM or size problems (every file < 300 lines).
