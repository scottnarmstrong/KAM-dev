# Package LP-LIFT: the chart lift on a stopped interval and the D1 premises (MAIN Lemma 14, chart part)

Wave 3. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
Base: `inp-lp` (landed wave 1; LP-DOM and LP-NRS audited, landing). Handoffs: `docs/tracks/LP/audits/`.

## Goal

MAIN L14 (lines 477–483): on the stopped interval, "every such physical point lies in `𝒟₁`, using the whole
ball (21)", and the chart is valid there. This package turns the stopped conditions of LP-CONF's `hstop`
(strict form) into exactly the premises of LP-DICT's conditional `nonresonant_drift_of_chartData` (audit note
D1, PROGRESS "Carried requirements"):
- (i) a chart lift `w` of the physical solution (in `chartSafe`, projecting to `z`, solving the chart ODE);
- (ii) `lpRescale ℓ (w u) ∈ b.realDom b.rB` (outer localization);
- (iii) the stopped slow membership in `secularBall ν δ I⁰`.

All three must be derived; none may be assumed.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 14 (lines 468–500), Theorem 15 (lines 502–506: orientation, the product
chart covers every initial state, `C = ΣΓ_i`), with `source/AMENDMENTS.md` N2 and N6.

## Reuse

- Track P's `KAM/Planetary/Exponential/Lift.lean` is the template: maximal chart ODE solution through the
  initial chart point, projection to a physical solution (`liftPhysicalDeriv`, `chart_orbit`), equality with
  `z` by uniqueness, and continuation over a compact zero-angle set via `UniformData`. Also reuse `liftChartHam`,
  `chartSafe`, `isOpen_chartSafe`, `contDiffOn_liftField`, `liftField_periodic`. Do NOT use its `AMDBox`
  statements, and never import `Exponential/Stopped.lean`.
- LP: `PlanarDictionary.lean` (`lpChart_strongAMD`, `lpChart_image`, `lpChart_action`), `Momentum.lean`
  (`cross_sign_and_margin`, `totalMomentum_const`), `Geometry.lean`, `Modulus.lean`,
  `AnalyticDomain/Core.lean` (`secularBall`), `NonresonantAdapter*.lean` (`lpRescale`, `lpRealDom_isOpen`; the
  exact premise shapes of `nonresonant_drift_of_chartData`).
- LP-CONF's strict stopped conditions, in the form of its `hstop` antecedent: for `u ∈ uIcc 0 t`,
  `IsPhysicalState ν (z u) ∧ ‖Λ(z u) − Λ z₀‖ < r ∧ strongAMD ν (z u) < B(Λ(z u)) − δ/2`. The CONF branch is
  `inp-lp-conf` (d62be160); copy that antecedent literally, without importing it.

## Owned files

`KAM/Planetary/StrongAMD/ChartLift.lean` (split with a facade if needed). Nothing else.

## Statements

Data: `hν`, `2 ≤ n`, compact `U ⊆ chamber ν`, `0 < δ`, `0 < r` with the budget
`n r + strongThresholdModulus ν U r ≤ δ/4`, `μ`, a physical `z₀` with `I⁰ := Λ z₀`, the closed `r`-ball about
`I⁰` inside `U`, `strongAMD ν z₀ ≤ B(I⁰) − δ`, and **`0 < totalMomentum z₀`** (orientation; LP-PS reflects
otherwise).

1. **Prograde along the stopped interval.** For a moving solution `z` on `OrdConnected J ∋ 0` with `z 0 = z₀`,
   and `t ∈ J` with the strict stopped conditions on `uIcc 0 t`: every `z u` (`u ∈ uIcc 0 t`) is
   `ProgradeElliptic ν` (conservation of `L`, `cross_sign_and_margin` with `m = δ/2`), and is a
   `BarrierState ν U (δ/2)`.
2. **Whole-ball membership (MAIN line 480).** On the same interval,
   `strongAMD ν (z u) ≤ B(I⁰) − δ/4`. Indeed `C(z u) < B(Λ(z u)) − δ/2 ≤ B(I⁰) + Ω(r) − δ/2`, and the budget
   gives `Ω(r) ≤ δ/4`.
3. **Chart lift.** `∃ w : ℝ → Phase (n+n)` and an open interval containing `uIcc 0 t` on which:
   - `HasDerivAt w (KAM.hamiltonianVectorField (liftChartHam ν μ) (w u)) u`;
   - `w u ∈ chartSafe ν` and `poincareProd ν 1 (w u) = z u` on `uIcc 0 t`;
   - `fast (w 0).2 = I⁰`.
   Follow `Lift.lean`: the compact set for continuation is the chart preimage, with angles in one cell, of the
   stopped states. It is compact by GEOMOD and DOM-style arguments, because actions lie within `r` of `I⁰` and
   `chartAMD ≤ B(I⁰) − δ/4`.
4. **D1 premises.** For the block `b := ⟨I⁰, secularBall ν δ I⁰, r, wₛ⟩` (any `0 < wₛ`, `ℓ = b.lam = wₛ/r`) and
   every `u ∈ uIcc 0 t`:
   - (ii) `lpRescale b.lam (w u) ∈ b.realDom b.rB`: real angles, `‖fast − I⁰‖ < r`, slow point in the base;
   - (iii) `(slow (w u).1, slow (w u).2) ∈ b.S`, from item 2 via `lpChart_strongAMD`
     (`chartAMD = strongAMD`);
   - `fastAction (lpRescale b.lam (w 0)) = b.Ic`.
   State them in exactly the shape `nonresonant_drift_of_chartData` consumes. If that helper's premise is "on
   `J`", note that LP-PS applies it with `J := uIcc 0 t` restricted. Check that restriction of
   `IsMovingSolutionOn` and of the lift's ODE to `uIcc 0 t` is legitimate (two-sided derivatives inside a larger
   open interval), and prove the restriction lemma if needed.

Out of scope: discharging `hstop` itself (LP-PS combines NRR's drift with these premises), the reflection to
`L > 0` (LP-PS, with MOM's `isMovingSolutionOn_reflectPhase_iff`), and the analytic data.

## Checks and stop condition

- `lp_build.sh` on each module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–4.

Stop when done or blocked: report, never add a hypothesis silently. Expected size 600–1,500 lines.

## Handoff

`docs/tracks/LP/audits/LP-LIFT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-LIFT.md`, then
`touch .drafts/READY-LP-LIFT`.
