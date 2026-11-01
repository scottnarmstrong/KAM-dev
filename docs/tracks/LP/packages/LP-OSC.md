# Package LP-OSC: actual-velocity osculating ellipses (MAIN Lemma 16), planar

Wave 3 (independent of the analytic packages). Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md`
(hard rules, capped wrappers, handoff). Base: `inp-lp` with THR, MOM, GEOMOD and DICT. GEOMOD supplies the safe
compact physical set (`BarrierState`, `strongBarrier_physical`, `exists_barrierCompact`); its handoff is
`docs/tracks/LP/audits/LP-GEOMOD-handoff.md`.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 16, lines 508–529, with `source/AMENDMENTS.md` **N10**: the final `μ₀`
also satisfies `A_osc μ₀ ≤ d_⋆/2` and `2 A_osc μ₀ ≤ d_pair/2`. Roadmap §2 (the conclusion's osculating clauses)
and §3 row 16.

## Owned files

`KAM/Planetary/StrongAMD/Osculating.lean` (split with a facade if needed). Nothing else.

## Definitions (planar, literal MAIN (42), namespace `KAM.Planetary.StrongAMD`)

For `z : Phase (n * 2)`, write `q_i = bodyVector z.1 i` and `p_i = bodyVector z.2 i`.
- `oscVelocity ν μ z i := (1 / ν i) • p_i + μ • ∑ j, p_j` (`V_i = q̇_i`, MAIN (10)). Prove it equals the
  `q_i`-block of the moving Hamiltonian field, i.e. the actual heliocentric velocity, via
  `KAM/Planetary/Newtonian/HamiltonNodes.lean` (`movingField_blocks` / `hamilton_eqs_moving`).
- `oscParam ν μ i := 1 + μ * ν i` (`k_i`).
- `oscEnergy`, `oscAxis`, `oscEccVector`, `oscEcc` exactly as (42), with `planeSq`, `planeDot`, `planeLength`.
- `oscPeri ν μ z i := oscAxis * (1 − oscEcc)`, `oscApo ν μ z i := oscAxis * (1 + oscEcc)`, and the canonical
  `peri`/`apo` from `keplerAxis` and `planeLength (keplerEccVector …)`.

## Theorems

Data: a set `K` of physical states (`IsPhysicalState`) with explicit uniform bounds:
- `dS ≤ planeLength q_i ≤ R`;
- `planeLength p_i ≤ P`;
- `keplerEnergy ν z i ≤ −c`;
- `planeLength (keplerEccVector ν z i) ≤ e_*` with `e_* < 1`.

GEOMOD's barrier states satisfy all of these, with `e_*` from its deficit bound; prove that bridge too.

1. **(43), uniform.** `∃ μ₀ A A_osc > 0` (depending only on `ν`, `n` and the bounds) such that for
   `0 < μ ≤ μ₀` and every `z ∈ K` and `i`:
   - `oscEnergy ≤ −(c/ν_i)/2` (specific energy; the input bound `keplerEnergy ≤ −c` is total energy, audit LP-OSC-1 note), so the elements are nondegenerate elliptic;
   - `oscEcc < 1`;
   - `|oscAxis − keplerAxis| + planeLength (oscEccVector − keplerEccVector) ≤ A μ`;
   - `|oscPeri − peri| ≤ A_osc μ` and `|oscApo − apo| ≤ A_osc μ`.

   Mass normalization: `keplerEnergy ν z i = ν_i E_i` (MAIN's specific energy times `ν_i`) and
   `keplerEccVector` is MAIN's `𝐞_i`. The osculating quantities in (42) are specific (unit-mass) with parameter
   `k_i`. Compare like with like and state the comparison exactly as (43).
2. **Tangency.** The osculating ellipse passes through `q_i` and is tangent to `V_i`. Prove it in the form of
   Lemma 2 with parameter `k_i`: `oscAxis(1 − oscEcc) ≤ |q_i| ≤ oscAxis(1 + oscEcc)`. Reuse MOM's
   `orbital_identities` pattern; a `k`-scaled version of the algebra is fine as a new helper.
3. **Half-gaps (N10).** With `d_⋆ = dS` and `d_pair = dP` from GEOMOD's barrier, after shrinking `μ₀` so that
   `A_osc μ₀ ≤ d_⋆/2` and `2 A_osc μ₀ ≤ d_pair/2`, every barrier state satisfies:
   - `d_⋆/2 ≤ oscPeri i`;
   - for each adjacent pair, `d_pair/2 ≤ oscPeri (i+1) − oscApo i`.

Out of scope: spatial (d = 3) versions (wave 4), and any dynamics beyond identifying `V_i` with the field's
`q`-block.

## Checks and stop condition

- `lp_build.sh` on the module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–3.

Stop when done or blocked: report, never add a hypothesis silently. Expected size 500–1,000 lines. Avoid big
`nlinarith` calls; split the expansions into focused lemmas.

## Handoff

`docs/tracks/LP/audits/LP-OSC-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-OSC.md`, then
`touch .drafts/READY-LP-OSC`.
