# Package LP-SP-OSC: actual-velocity osculating ellipses in dimension three (MAIN Lemma 16, d = 3)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
Base: `inp-lp-sposc` = `inp-lp` + LP-SP-MODEL + LP-SP-GEO (handoffs in `docs/tracks/LP/audits/`).

## Template

The planar LP-OSC (landed: `KAM/Planetary/StrongAMD/Osculating*.lean`; audit `LP-OSC-audit-1.md`, PASS WITH NOTES)
is the template. MAIN L16 holds "in dimensions two and three". Re-prove its estimates with `Fin 3` vectors
(`spaceDot`, `spaceSq`, `spaceLength`, `spaceCross` from LP-SP-MODEL). Where a planar lemma is dimension-free in
substance (the scalar `spec*` algebra in `Osculating/Estimates.lean`), reuse it, or state a `Fin 3` twin with the
same proof. Keep the audit note: the energy bound is on the **specific** scale (`−(c/ν_i)/2`).

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 16 (508–529), (10), (42), (43), with `source/AMENDMENTS.md` N10 and statement
review F2 (`docs/tracks/LP/freeze/STATEMENT-REVIEW-1.md`): export the summed element estimate and ellipse validity
explicitly.

## Owned files

`KAM/Planetary/Spatial/Osculating.lean` (and parts). Do not edit other files.

## Statements (spatial twins of LP-OSC)

1. **Definitions (MAIN (42), d = 3).**
   - `spatialOscVelocity ν μ z i := (1/ν_i) • p_i + μ • Σ_j p_j`, `spatialOscParam`, `spatialOscEnergy`,
     `spatialOscAxis`, `spatialOscEccVector`, `spatialOscEcc`, `spatialOscPeri`, `spatialOscApo`.
   - `spatialKeplerPeri`, `spatialKeplerApo`.
   - Per OD-11 (b), also a carrier subtype version (valid osculating states) with defining equations.
2. **Velocity.** `spatialOscVelocity` equals the `q`-block of the spatial moving field (SP-MODEL's
   `hamiltonianVectorField_spatial`).
3. **(43), uniform.** On a set of physical spatial states with uniform bounds `dS ≤ |q_i| ≤ R`, `|p_i| ≤ P`,
   `E_i ≤ −c`, `e_i ≤ e_* < 1`: there are `μ₀ A A_osc > 0` such that every state satisfies
   - specific osculating energy `≤ −(c/ν_i)/2`;
   - `0 < axis`, `oscEcc < 1`;
   - radial incidence `oscPeri ≤ |q_i| ≤ oscApo`;
   - `|Δa| + |Δ𝐞| ≤ A μ`, and endpoint errors `≤ A_osc μ`.
4. **Bridge and half-gaps (N10).** From SP-GEO's `SpatialBarrierState` (`spatialStrongBarrier_physical`): the
   bounds of item 3, and, after shrinking `μ₀` with `A_osc μ₀ ≤ dS/2` and `2 A_osc μ₀ ≤ dP/2`, every barrier
   state has `oscPeri ≥ dS/2` and adjacent osculating gaps `≥ dP/2`.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–4.

Expected size 600–1,200 lines. Stop when done or blocked.

## Handoff

`docs/tracks/LP/audits/LP-SP-OSC-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-OSC.md`, then
`touch .drafts/READY-LP-SP-OSC`.
