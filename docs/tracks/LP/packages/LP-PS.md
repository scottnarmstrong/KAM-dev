# Package LP-PS: the planar theorem LP1 (MAIN Theorem 15 with Lemma 16), assembly

Wave 3, the planar milestone. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules,
capped wrappers, handoff). Base: `inp-lp-ps`, which holds every planar package:
- landed: THR, MOM, GEOMOD, DICT, DOM, NRS;
- audited: OSC;
- in audit: CONF and NRR (LP-W3B);
- proved: LIFT.

Read every handoff in `docs/tracks/LP/audits/`.

## Target

Prove, as an ordinary (non-frozen) theorem, the exact statement LP1 of `docs/tracks/LP/FREEZE-PROPOSAL.md`
(draft 1, §3; elaborated text in `docs/tracks/LP/freeze/elaboration-draft-1.lean.txt`), with two changes:
- **name** `lp1_planar_strongAMD_safety` (namespace `KAM.Planetary.StrongAMD`, a distinct name, so the future
  frozen anchor does not clash);
- **without** the premises `hνmax` and `hνle` (OD-3 recommendation: a strictly more general theorem).

Also prove the corollary with `hνmax` and `hνle`, as one line. Also prove `lp0_planar_barrier`, LP0 of §2, as a
restatement of `strongBarrier_physical`.

The statement review of the proposal (root-b8's request) may change the text. If it does, the orchestrator
sends you the delta; otherwise prove draft 1 exactly.

## Source

`docs/tracks/LP/source/MAIN.md` Theorem 15 (lines 502–506), Lemma 14 (468–500), Lemma 16 (508–529) and §1
(6)–(9), with `source/AMENDMENTS.md`:
- **N6:** stopped radius `r = D₀√μ`, improvement `r/2`, margin `3δ/4`;
- **N7:** Lemma 13 is the drift supplier;
- **N10:** the `μ₀` ordering;
- **N2:** the shared `U`.

## Assembly plan (all ingredients exist)

1. **Constants, chosen before `μ` and `z₀`.**
   - `L := strongLSet ν A` (D0: compact, ⊆ chamber); `𝓛_δ`.
   - The shared tube `U`, `r_g` (`exists_isSharedTube`).
   - DOM's tube (`exists_strongTube`).
   - NRR's constants (`lp_stopped_drift`; take `D₀ := 1` or any fixed value); NRS's exponent `scaleExponent τ`.
   - GEOMOD's barrier constants for `(U, δ/2)` (`strongBarrier_physical`), and OSC's `osculating_barrier` for
     `(U, δ/2)`.
   - Then shrink `μ₀` so that, for `r = D₀√μ`: `r ≤ r_g` (so the closed `r`-ball about `I⁰ ∈ 𝓛_δ` lies in `U`),
     and the budget `n r + strongThresholdModulus ν U r ≤ δ/4` holds (`tendsto_strongThresholdModulus`), and
     OSC's `μ₀` applies.
   - `T₀, c` from NRR; `A_Λ := D₀/2`.
   - `A_a` from the Lipschitz bound of `I ↦ (I_i/ν_i)²` on `U` (MAIN line 497).
2. **Initial data.** Axes in `A` ⇒ `Λ z₀ ∈ L`. `strongAMD ≥ 0` (MOM) and `C₀ ≤ B − δ` ⇒ `I⁰ ∈ 𝓛_δ`.
   `C₀ < Λ_k` ⇒ `totalMomentum z₀ ≠ 0` (MOM).
3. **Orientation (MAIN Theorem 15).** If `totalMomentum z₀ < 0`, apply the argument to `reflectPhase z₀` and
   transport back with MOM's reflection lemmas (`isMovingSolutionOn_reflectPhase_iff`, the invariance of
   energy, axis, action, `e`, lengths, `strongAMD`, and `MovingUniqueOn` by the involution).
   - Prove any missing invariance, e.g. of `oscPeri`/`oscApo` (`oscVelocity` of the reflected state is the
     reflected velocity) and of the Diophantine premise (actions are invariant).
   - Keep these in a focused `Reflection`-style part.
4. **Confinement.** Apply `strongFirstExit_of_stopped_drift` (CONF) with `T := T₀ exp(c μ^{-a})`. Discharge
   `hstop` by LIFT's `lpChartLift_premises` with NRR's `lp_stopped_drift` (equivalently
   `lpStopped_drift_of_chartData` fed with NRR's `ExtNFHyp`, trace identity and `hsmall` at the centre `I⁰`).
   The block is `lpStoppedBlock ν δ I⁰ r wS` with NRR's width `wS`, and `J := uIcc 0 t`. Check that the time
   bound and every width match NRR's fixed choices.
5. **Conclusions.**
   - CONF gives existence, `MovingUniqueOn`, the physical state, drift `≤ r/2`, `C ≤ B − δ/2`, and
     `BarrierState ν U (δ/2)`.
   - GEOMOD gives perihelia, adjacent gaps, star and all-pair distances.
   - `strongAMD_sub_eq_sum` gives `|C(t) − C(0)| ≤ n A_Λ √μ`.
   - Membership `Λ(z t) ∈ U ⊆ chamber` gives the existential `hcht` with `orderedStrongThreshold_eq`.
   - OSC's `osculating_barrier` gives the osculating clauses.
   - The Newtonian reconstruction is track P's `isNewtonSolutionOn_of_isMovingSolutionOn`
     (`KAM/Planetary/Newtonian/Reconstruction.lean`) on the collision-free solution.
6. **Corollary** `τ = n − 1/2` (`scaleExponent_planar`): the exponent `1/(2n+1)`.

## Owned files

`KAM/Planetary/StrongAMD/PlanarSafety.lean` (facade) and parts `KAM/Planetary/StrongAMD/PlanarSafety/*.lean`
(e.g. `Constants`, `Orientation`, `Confine`, `Main`). Nothing else.

## Checks and stop condition

- `lp_build.sh` on each module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of `lp1_planar_strongAMD_safety`, its normalized corollary, `lp0_planar_barrier` and the
  `τ = n − 1/2` corollary. They must be exactly `[propext, Classical.choice, Quot.sound]`.

**This is the end-to-end check of the planar campaign.** Stop when done or blocked. If an ingredient's
interface does not fit (a width, time or quantifier mismatch), STOP and report the exact mismatch; do not add a
hypothesis to the main theorem. Expected size 800–1,800 lines.

## Handoff

`docs/tracks/LP/audits/LP-PS-handoff.md` (committed, with AUDIT FOCUS and the full elaborated signature) and
`.drafts/handoff-LP-PS.md`, then `touch .drafts/READY-LP-PS`.
