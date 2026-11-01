# Package LP3-PS: the planar theorem LP3-1 (strong-AMD safety with NO arithmetic hypothesis), assembly

LP3, planar. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3ps` = `inp-lp-lp3drift` (LP3-KEP, COVERPERT, CELL,
DRIFT on `inp-lp`; the planar LP1 assembly is landed on main).

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the
frozen definitions. Never import any `KAM/Provider/*` module.

## Template

The landed LP1 assembly `KAM/Planetary/StrongAMD/PlanarSafety/*.lean` (`Constants`, `Prograde`, `Main`, …; handoff
`docs/tracks/LP/audits/LP-PS-handoff.md`, audit LP-PS-1), with exactly one change of ingredient. Its `hstop`
discharge, `lp_stopped_drift` with the Diophantine `(γ, τ)`, is replaced by LP3-DRIFT's `lp_stopped_drift_nek_hstop`
(handoff `LP3-DRIFT-handoff.md`; it matches `hstop` of `strongFirstExit_of_stopped_drift` by `exact`, with
`AΛ := B0^b_n/2`). Reuse the LP1 modules wherever they are stated for a general drift scale `r` and time `T`
(orientation/reflection, confinement, conclusions). Where an LP1 lemma hard-codes `√μ` or the Diophantine time, write
a drift-scale-generic version in your own files (the plan's "drift-scale generalization of the safe-state
predicates, or a parallel pair"); never edit the LP1 files.

## Target statements (plan `docs/tracks/LP/lp3/LP3-PLAN.md` §1.1, §1.2, §1.4: the exact displayed text)

`lp3_planar_strongAMD_safety` and `lp3_planar_strongAMD_safety_normalized`. Take the LP1 text
(`PlanarSafety/Main.lean:44–91` and `:137–185`; FREEZE-PROPOSAL §3) with exactly three changes:
1. **Removed:** the data `γ τ`, the premises `hγ hτ` and the Diophantine premise.
2. **Time:** `T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))`.
3. **Drift:** `AΛ * μ ^ planetaryDriftExponent n` in the action line, `Aa * μ ^ planetaryDriftExponent n` in the
   axis line, and `n * AΛ * μ ^ planetaryDriftExponent n` in the AMD line, instead of `√μ`.

Everything else is identical, character for character. That covers all other premises, all other conclusions
(existence and uniqueness on `[−T, T]`, Newtonian reconstruction, ellipticity, margin `δ/2`, separations,
osculating elements with the F2 clauses), the constant order (all constants before `μ` and `z₀`; they depend on
`(n, ν, 𝒜, δ)` only), and the N10 inequalities. Nothing is added: **no** prograde or arithmetic premise. The
orientation is handled by the reflection, as in LP1.

## Owned files

`KAM/Planetary/StrongAMD/Nek/PlanarSafety.lean` (facade) and parts `KAM/Planetary/StrongAMD/Nek/PlanarSafety/*.lean`
(for example `Orientation`, `Prograde`, `Main`). New files only (the generated `KAM/Root/Planetary.lean` excepted).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of both LP3-1 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- A token-level diff of the LP3-1 type against the LP1 type (`Main.lean:44`) in the handoff, showing only the three
  changes.

If an ingredient interface does not fit, STOP and report the exact mismatch. Never add a hypothesis to LP3-1.
Expected size 400–800 lines.

## Handoff

`docs/tracks/LP/audits/LP3-PS-handoff.md` (committed, with AUDIT FOCUS, the full elaborated signatures and the token
diff) and `.drafts/handoff-LP3-PS.md`, then `touch .drafts/READY-LP3-PS`.
