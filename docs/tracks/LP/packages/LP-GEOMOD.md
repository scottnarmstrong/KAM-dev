# Package LP-GEOMOD: the uniform strong barrier (MAIN L5) and the moving threshold and continuation (MAIN L6)

Wave 1. One prover, two package ids in `packages.json` (LP-GEO: `Geometry.lean`; LP-MOD: `Modulus.lean`,
`Continuation.lean`). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers,
handoff). Base: branch `inp-lp-bar1` (LP-THR + LP-MOM, under audit). Their APIs are in
`docs/tracks/LP/audits/LP-THR-handoff.md` and `LP-MOM-handoff.md`. If the audit changes a name, the orchestrator
tells you.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 5 (lines 162–175) and Lemma 6 (lines 177–189), with
`source/AMENDMENTS.md`, which is binding here:
- **N2:** one shared compact `U ⊂ 𝒬`. Lemmas 6, 8 and 14 use the same `U` and its modulus `Ω_B`, so state
  everything for an arbitrary compact `U ⊆ chamber ν` given as data, and separately prove that suitable `U`
  exist (item M2).
- **N11:** define `d_⋆ := a_min m² / (2 I_max²)` before using it in the momentum bound.

Reuse: `KAM/Planetary/AMD/Geometry.lean` (`amd_compact`: the compactness pattern; do not use the `AMDBox`
statements themselves), `KAM/ODE/Continuation.lean` (`gen_continuation_compact`), `KAM/ODE/Maximal.lean`,
`KAM/Planetary/AMD/MovingODE.lean` (`moving_ode`: the moving field is C¹ on the open `collisionFreeDomain n`,
and `IsMovingSolutionOn ↔ IsSolutionIn`), and `KAM/Planetary/AMD/ConfinementExit.lean`.

## Owned files

`KAM/Planetary/StrongAMD/Geometry.lean`, `KAM/Planetary/StrongAMD/Modulus.lean`,
`KAM/Planetary/StrongAMD/Continuation.lean` (split with facades if needed). Nothing else.

Standing premises: `hν : ∀ i, 0 < ν i`, `hn : 2 ≤ n`, `U ⊆ chamber ν` compact, `0 < m`. Write
`Λ z := fun i => keplerAction ν z i`, `e_i := planeLength (keplerEccVector ν z i)`, `C := strongAMD ν z`,
`B := strongThreshold ν`. "Physical state" means `∀ i, 0 < planeLength (bodyVector z.1 i) ∧ keplerEnergy ν z i < 0`.

## LP-GEO (MAIN Lemma 5)

- G0 Bridge: on physical states, `actionAxis ν (Λ z) i = keplerAxis ν z i`.
- G1 Deficit form (MAIN line 164, second sentence). `∃ dS dP > 0` (depending only on `ν, U, m`) such that for
  every `I ∈ U` and `e : Fin n → ℝ` with `e i ∈ [0,1]` and `∑ i, I i * eccDeficit (e i) ≤ B I − m`:
  - `∀ i, dS ≤ actionAxis ν I i * (1 − e i)`;
  - for every adjacent pair `a`,
    `dP ≤ actionAxis ν I a.upperIdx * (1 − e a.upperIdx) − actionAxis ν I a.1 * (1 + e a.1)`
    (`AdjIdx.upperIdx` is THR's successor index).

  Proof route: the compact set `K_m` of MAIN line 167 (closed by THR continuity; mind the empty case), and THR's
  `pairThreshold_le_of_feasible` for strict positivity.
- G2 Physical form (MAIN line 164, first sentence, and lines 169–171). With the same `dS, dP` and explicit
  `R, P, c > 0`: every physical state with `Λ z ∈ U` and `C ≤ B (Λ z) − m` satisfies:
  - perihelion `keplerAxis·(1 − e_i) ≥ dS`, and the adjacent annulus gaps are `≥ dP`;
  - `planeLength q_i ≥ dS`;
  - `planeLength (q_i − q_j) ≥ dP` for every `i ≠ j` (not only adjacent pairs);
  - `planeLength q_i ≤ R`, `planeLength p_i ≤ P`, `keplerEnergy ν z i ≤ −c`;
  - the MOM projection conclusion (`m ≤ |L_i|`, every `L_i` with the sign of `totalMomentum z`).

  Use MOM's `orbital_identities` and `sum_action_mul_eccDeficit_le_strongAMD`, with `eccDeficit` joined to the
  literal deficit by `rfl`/`simp`.
- G3 Compactness: `∃ K, IsCompact K ∧ K ⊆ collisionFreeDomain n ∧` every state of G2 lies in `K`.

## LP-MOD (MAIN Lemma 6)

- M1 Modulus. Define `strongThresholdModulus ν U r := sSup {|B I − B J| | I ∈ U, J ∈ U, ‖I − J‖ ≤ r}` (sup norm;
  name per SPEC §2). For compact `U ⊆ chamber ν`, prove:
  - it is nonnegative, monotone in `r`, and bounded above (the set is bounded);
  - `|B I − B J| ≤ strongThresholdModulus ν U r` whenever `I, J ∈ U`, `‖I − J‖ ≤ r`;
  - `Tendsto (strongThresholdModulus ν U) (𝓝[>] 0) (𝓝 0)` (uniform continuity of `B` on `U`; THR's
    `continuousOn_strongThreshold`).
- M2 Shared `U` (N2). For compact `L ⊆ chamber ν`: `∃ ρ > 0` such that `Metric.cthickening ρ L` is compact and
  contained in `chamber ν` (so later packages take `U := cthickening (4 r_g) L` with `4 r_g ≤ ρ`).
- M3 (17). For a moving solution `z` on an `OrdConnected` `J ∋ 0` with physical states along `J`, if
  `Λ (z 0) ∈ L` (any set), `C(z 0) ≤ B (Λ (z 0)) − δ`, `t ∈ J`, `‖Λ (z t) − Λ (z 0)‖ ≤ r`, and
  `Λ (z 0), Λ (z t) ∈ U`, then `C(z t) ≤ B (Λ (z t)) − δ + n * r + strongThresholdModulus ν U r`.

  Use MOM's `strongAMD_sub_eq_sum` and the sup-norm bound `|∑ i, (Λ_i(t) − Λ_i(0))| ≤ n r`.
- M4 Continuation (MAIN lines 181 and 187). For the maximal solution `z` of the moving field on
  `collisionFreeDomain n` from `z₀` (`KAM.ODE.IsMaximalSolution`, interval `(Tm, Tp)`):
  - if for some `0 ≤ t_* < Tp` every `z t` with `t_* ≤ t < Tp` is a physical state with `Λ (z t) ∈ U` and
    `C ≤ B (Λ (z t)) − m`, then `Tp = ⊤`;
  - the mirror statement backwards gives `Tm = ⊥`.

  This is G3 with `gen_continuation_compact`. Also give the MAIN-shaped corollary: under M3's hypotheses with
  `n r + Ω(r) ≤ δ/2` (so `m = δ/2`), the solution cannot terminate while the action-tube and physical conditions
  hold.

Out of scope: the first-exit assembly (MAIN L14) and any analytic estimate.

## Checks and stop condition

- `lp_build.sh` on each module (import order).
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` on your modules exits 0.
- `#print axioms` of G0–G3, M1–M4.

Stop when done or blocked; report, and never add a hypothesis silently. Expected size 800–1,800 lines.

## Handoff

`docs/tracks/LP/audits/LP-GEOMOD-handoff.md` (committed, with an AUDIT FOCUS section) and
`.drafts/handoff-LP-GEOMOD.md`, then `touch .drafts/READY-LP-GEOMOD`.
