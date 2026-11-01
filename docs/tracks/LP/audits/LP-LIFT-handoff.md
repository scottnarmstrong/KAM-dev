# LP-LIFT handoff (MAIN Lemma 14, chart part; track LP, non-frozen)

Branch `inp-lp-lift`. Base: `inp-lp` waves 1–2 plus the LP-LIFT brief. No `sorry`, no `maxHeartbeats`;
all files far below 1500 lines.

## Files

| file | lines | content |
|---|---|---|
| `KAM/Planetary/StrongAMD/ChartLift/Stopped.lean` | 129 | `LiftData`, `StoppedOn`, items 1–2 |
| `KAM/Planetary/StrongAMD/ChartLift/Lift.lean` | 229 | restriction lemma, compact `liftQ` box, `mem_chartSafe_of_liftQ`, item 3 |
| `KAM/Planetary/StrongAMD/ChartLift/Premises.lean` | 134 | `lpStoppedBlock`, `lpRescale_mem_realDom`, item 4, conditional composition with the adapter |
| `KAM/Planetary/StrongAMD/ChartLift.lean` | 18 | facade |
| `KAM/Root/Planetary.lean` | +4 | output of `scripts/gen_root_imports.py` (needed for `lp_lint.sh` to exit 0) |

## Statements (elaborated signatures)

Data (all source premises / typing data; no drift or confinement conclusion):

```
structure LiftData (ν : Fin n → ℝ) (U : Set (Fin n → ℝ)) (z₀ : Phase (n * 2)) (δ r : ℝ) : Prop
  pos_mass : ∀ i, 0 < ν i      two_le : 2 ≤ n      compact : IsCompact U     subset_chamber : U ⊆ chamber ν
  delta_pos : 0 < δ            r_pos : 0 < r
  budget : n * r + strongThresholdModulus ν U r ≤ δ / 4
  physical : IsPhysicalState ν z₀
  ball : ∀ I, ‖I - actionVector ν z₀‖ ≤ r → I ∈ U
  amd : strongAMD ν z₀ ≤ strongThreshold ν (actionVector ν z₀) - δ
  orient : 0 < totalMomentum z₀

def StoppedOn ν z₀ δ r z t : Prop := ∀ u ∈ uIcc 0 t, IsPhysicalState ν (z u) ∧
    ‖actionVector ν (z u) - actionVector ν z₀‖ < r ∧
    strongAMD ν (z u) < strongThreshold ν (actionVector ν (z u)) - δ / 2
```
`StoppedOn` is, by `rfl`, the antecedent of LP-CONF's `hstop` (copied literally from `d62be160`).

1. `LiftData.prograde_of_stopped (hd) (hJ : J.OrdConnected) (h0 : 0 ∈ J) (hz : IsMovingSolutionOn ν μ J z)
   (hz0 : z 0 = z₀) (ht : t ∈ J) (hs : StoppedOn ν z₀ δ r z t) :
   ∀ u ∈ uIcc 0 t, ProgradeElliptic ν (z u) ∧ BarrierState ν U (δ / 2) (z u)`
   (conservation of `L` via `totalMomentum_const`, `cross_sign_and_margin` with `m = δ/2`).
2. `LiftData.strongAMD_le_of_stopped (hd) (hs) (hu : u ∈ uIcc 0 t) :
   strongAMD ν (z u) ≤ strongThreshold ν (actionVector ν z₀) - δ / 4`
   (from `abs_strongThreshold_sub_le_modulus` and the budget; the unused slack `n r` is kept as
   `LiftData.threshold_ball_le : B(I⁰) - δ/4 ≤ B(I) - n r` on the closed ball).
3. `LiftData.lpChartLift_of_stopped (hd) hJ h0 hz hz0 ht hs :
   ∃ w I, IsOpen I ∧ I.OrdConnected ∧ uIcc 0 t ⊆ I ∧
     (∀ u ∈ I, w u ∈ chartSafe ν ∧ HasDerivAt w (hamiltonianVectorField (liftChartHam ν μ) (w u)) u) ∧
     (∀ u ∈ uIcc 0 t, poincareProd ν 1 (w u) = z u) ∧ fast (w 0).2 = actionVector ν z₀`
4. `lpChartLift_premises (hd) {wS} hJ h0 hz hz0 ht hs : ∃ w,`
   `(∀ u ∈ uIcc 0 t, w u ∈ chartSafe ν ∧ Ψ (w u) = z u ∧ HasDerivAt w (X_{liftChartHam ν μ} (w u)) u) ∧`
   `(∀ u ∈ uIcc 0 t, lpRescale b.lam (w u) ∈ b.realDom b.rB) ∧`
   `fastAction (lpRescale b.lam (w 0)) = b.Ic ∧ (∀ u ∈ uIcc 0 t, (slow (w u).1, slow (w u).2) ∈ b.S)`
   with `b = lpStoppedBlock ν δ (actionVector ν z₀) r wS = ⟨I⁰, secularBall ν δ I⁰, r, wS⟩`, any `wS`
   (positivity is only needed by the adapter, which gets it from `ExtNFHyp.slow_width_pos`).
   The first conjunct is literally `hlift` of `nonresonant_drift_of_chartData` with `J := uIcc 0 t`.
   Supporting: `lpRescale_mem_realDom` (general block form of (ii)), `lpMovingSolutionOn_mono`.
5. Extra (shape check, **conditional on the L8 analytic data; not a source result, not `hstop`**):
   `lpStopped_drift_of_chartData` composes item 4 with `nonresonant_drift_of_chartData` on
   `J' := uIcc 0 t` and yields `‖Λ(z u) - I⁰‖ ≤ r/2` on `uIcc 0 t` for `|t|` within the engine time.
   It compiles with `hh, hsmall, htr, hstop-antecedent` exactly as the adapter states them.

## Approach

Template `KAM.Planetary.lift`: maximal solution of the pulled-back field through a chart preimage of
`z 0` (`lpChart_inverse`; collision-freeness from `hz.2`), `liftPhysicalDeriv`, uniqueness
(`gen_uniqueness_inter`), then `uniform_data` + `gen_continuation` over the compact zero-angle set
`liftQ ⟨box [I⁰ - r, I⁰ + r], outerAMD := B(I⁰) - δ/4⟩` (an `AMDBox` used only as data; `liftQ_isCompact`
needs no admissibility). `hQW` (zero-angle point in `liftQ` ⇒ `w ∈ chartSafe`): action in the closed ball
⇒ in `U ⊆ 𝒬`; `Γ_i ≤ ΣΓ ≤ B(Λ) - n r < Λ_i` gives the chart domain; `Ψ w` is a barrier state with margin
`n r > 0`, hence in the collision-free compact of `exists_barrierCompact`. The stopped conditions give
membership of the lift in the continuation set (item 2 + `lpChart_strongAMD` + `lpChart_action`).

## Checks

* `lp_build.sh` on `…ChartLift.Stopped`, `…ChartLift.Lift`, `…ChartLift.Premises`, `…ChartLift` (and the
  stale `…AnalyticDomain.Core`, `…Containment`, `…NonresonantAdapter`): all `Build completed successfully`.
* `lp_lint.sh`: exit 0 after `python3 scripts/gen_root_imports.py` (before it: "KAM.lean is out of date";
  this adds 4 import lines to `KAM/Root/Planetary.lean`).
* `main_shortname_check.py /root/code/KAM-inp-lp-lift <4 modules>`: "short-name check OK", exit 0.
* `#print axioms` (via `lp_lean.sh` on `.drafts/axioms_lift*.lean`): `prograde_of_stopped`,
  `strongAMD_le_of_stopped`, `lpChartLift_of_stopped`, `lpChartLift_premises`, `lpRescale_mem_realDom`,
  `lpStopped_drift_of_chartData`, `lpMovingSolutionOn_mono`: each only `[propext, Classical.choice, Quot.sound]`.

## Not done / out of scope

`hstop` itself, the reflection to `L > 0` (LP-PS), analytic data (trace identity, `ExtNFHyp`).

## AUDIT FOCUS

* `StoppedOn` vs LP-CONF's `hstop` antecedent (strict `< r`, strict `< B - δ/2`; `uIcc 0 t`).
* `LiftData`: only source premises; `orient : 0 < totalMomentum z₀` is the orientation of Thm 15; `budget` is
  the N6 form `n r + Ω_B(r) ≤ δ/4`; `ball` is the closed `r`-ball in `U`.
* Item 3's open interval is the maximal chart interval `eIoo Tm Tp`; derivatives are two-sided
  (`HasDerivAt`), so restriction to `uIcc 0 t` (item 4 / the adapter's `J`) is legitimate. `z` is only used on
  `uIcc 0 t ⊆ J` (restriction `lpMovingSolutionOn_mono`; `z`'s ODE on the closed interval suffices for
  uniqueness since `gen_uniqueness_inter` needs only `OrdConnected`).
* `lpRescale_mem_realDom`: strictness `‖Λ - I⁰‖ < rB` comes from the strict stopped condition; real angles
  lie in the unit complex strip; slow coordinates match the block base exactly (difference `0`).
* The continuation set is the zero-angle `liftQ` (angles zeroed), not "angles in one cell"; equivalent via
  `uniform_data`, as in track P.

## Source defects / deviations / design signals

* No errata found. MAIN line 480 states `−7δ/16` using `Ω_B ≤ δ/16` (39); with N6's budget `n r + Ω ≤ δ/4`
  the bound proved is `B(I⁰) − δ/4` (task item 2), which is all item 4 (iii) needs (`secularBall` uses `δ/4`).
* Deviations: `LiftData`/`StoppedOn` bundle the premises as a structure/def (unfold literally to the
  hypotheses); `KAM/Root/Planetary.lean` regenerated (+4 lines). No heartbeat or size problems (files ≤ 229
  lines, each elaborates in seconds).
