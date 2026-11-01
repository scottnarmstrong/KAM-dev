# Package LP3-SP-SAFE: the spatial theorem LP3-2 (strong-AMD safety with NO arithmetic hypothesis), assembly

LP3, spatial. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-lp3spsafe` = `inp-lp-lp3spdrift`, which holds every
spatial LP package (LP2 proved, under audit as W4E), LP3-SP-COVER, LP3-SP-DRIFT and the planar LP3 pieces.

## Import ruling (D58 in docs/DECISIONS.md, main 56e4a2c4)

LP modules MAY import the **sealed** frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` and the
frozen definitions. Never import any `KAM/Provider/*` module.

## Template

The LP2 assembly `KAM/Planetary/Spatial/SpatialSafety/{Constants,Orientation,Bridge,Aligned,Main}.lean` (handoff
`docs/tracks/LP/audits/LP-SP-SAFE-handoff.md`), with exactly one change of ingredient. Its `hstop` discharge (SP-NRR's
Diophantine `spatial_stopped_drift`) is replaced by LP3-SP-DRIFT's `spatial_stopped_drift_nek` (handoff
`LP3-SP-DRIFT-handoff.md`). Reuse the LP2 modules wherever they are stated for a general drift scale `r` and time
`T` (`Orientation`, `Bridge`, the confinement and conclusion lemmas). Where an LP2 lemma hard-codes `√μ` or the
Diophantine time, write a drift-scale-generic version in your own files; never edit the LP2 files.

## Target statements (plan `docs/tracks/LP/lp3/LP3-PLAN.md` §1.1–§1.4)

`lp3_spatial_strongAMD_safety` and `lp3_spatial_strongAMD_safety_normalized`. Take the LP2 text
(`SpatialSafety/Main.lean:43` and `:153`; FREEZE-PROPOSAL §3c) with exactly three changes:
1. **Removed:** the data `γ τ`, the premises `hγ hτ` and the Diophantine premise.
2. **Time:** `T := T₀ * Real.exp (c * μ ^ (-planetaryTimeExponent n))`.
3. **Drift:** `AΛ * μ ^ planetaryDriftExponent n` in the action line, `Aa * μ ^ planetaryDriftExponent n` in the
   axis line, and `n * AΛ * μ ^ planetaryDriftExponent n` in the AMD line, instead of `√μ`.

Everything else is identical, character for character. That covers all other premises (physical initial state,
`a(0) ∈ 𝒜`, chamber membership, `spatialStrongAMD ν z₀ ≤ orderedStrongThreshold − δ`), every other conclusion, the
constant order (all constants before `μ` and `z₀`; they now depend on `(n, ν, 𝒜, δ)` only), and the N10
inequalities. Same premises otherwise, nothing added: **no** prograde, small-inclination, nonzero total angular
momentum, secular-confinement, alignment or arithmetic premise.

**Exponents.** Use the `planetary*` names, as the plan recommends (O-1). They equal the frozen `partial*` by the
bridges in `Exponential/Stopped.lean`.

**Constants.** LP3-SP-DRIFT's scale is `r = (B₀ μ)^{b_n} = B₀^{b_n} μ^{b_n}`, so `AΛ` absorbs `B₀^{b_n}`. Its time
is `exp((B₀μ)^{−a_n})`; express it as `T₀ exp(c μ^{−a_n})` with `c = B₀^{−a_n}` and `T₀ = 1` (or as the confinement
lemma needs).

## Owned files

`KAM/Planetary/Spatial/Nek/SpatialSafety.lean` (facade) and parts `KAM/Planetary/Spatial/Nek/SpatialSafety/*.lean`
(for example `Constants`, `Aligned`, `Main`). New files only (the generated `KAM/Root/Planetary.lean` excepted).

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of both LP3-2 theorems: exactly `[propext, Classical.choice, Quot.sound]`.
- A token-level diff of the LP3-2 type against the LP2 type (`Main.lean:43`) in the handoff, showing only the three
  changes.

If an ingredient interface does not fit, STOP and report the exact mismatch. Never add a hypothesis to LP3-2.
Expected size 500–900 lines.

## Handoff

`docs/tracks/LP/audits/LP3-SP-SAFE-handoff.md` (committed, with AUDIT FOCUS, the full elaborated signatures and the
token diff) and `.drafts/handoff-LP3-SP-SAFE.md`, then `touch .drafts/READY-LP3-SP-SAFE`.
