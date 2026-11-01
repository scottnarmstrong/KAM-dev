# Package LP-SP-ADAPT: the Lemma-13 adapter for unequal fast/slow blocks (spatial infrastructure)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp` (LP-DICT landed: `KAM/Planetary/StrongAMD/NonresonantAdapter*.lean`).

## Why

LP-DICT Part B (audited, LP-W1B-1) proved the period-one rescaling and field conversion from the planar chart
`Phase (n+n)` to the engine's `ER n n` (`lpRescale`, `lpUnrescale`, `lpRescaleHam`, `lpRescale_field`,
`lpRescale_hasDerivAt`, `lpRealDom_isOpen`, `lpIndicator_field`, `lpOrbit_hasDerivAt`). The spatial product chart
(LP-SP-PROD, in progress) uses `Phase (n + (n + n))`: `n` fast pairs and `m = n + n` slow pairs, with slow
positions `(ξ, v)` in `w.1` and slow momenta `(η, u)` in `w.2`. The engine is `KAM.Nekhoroshev.ER n m` / `EC n m`
with `PartialBlock n m`. This package re-types Part B for general `m`. The planar case is `m = n`; prove that the
new maps agree with the planar ones there.

## Owned files

`KAM/Planetary/Spatial/NonresonantAdapter.lean` (and parts). Do not edit LP-DICT's files.

## Statements (generic `n m`)

1. `lpRescaleNM ℓ : Phase (n + m) →L[ℝ] ER n m`, mapping:
   - angles to `/(2π)`;
   - fast actions unchanged;
   - slow positions and momenta to `/ℓ`, into `slowPair` in the engine's slot order.

   Also `lpUnrescaleNM`, inverse lemmas, `fastAction_lpRescaleNM`, and `slowPair_lpRescaleNM`.
2. `lpRescaleHamNM ℓ G := (1/(2π)) * G ∘ lpUnrescaleNM ℓ`. The field conversion `lpRescaleNM_hasDerivAt`: a
   Hamiltonian solution of `G` (repository convention `hamiltonianVectorField`) maps to a solution of
   `realWfield (2π/ℓ²) (lpRescaleHamNM ℓ G)`. Check the slot and sign convention exactly as LP-DICT did. If it
   does not match for `m ≠ n` (for example, the `(v, u)` pair orientation), STOP and report.
3. `lpRealDomNM_isOpen`, `lpIndicatorNM_field` (the indicator Hamiltonian on `b.realDom` for `PartialBlock n m`),
   and `lpOrbitNM_hasDerivAt`, the generic versions of LP-DICT items 7–8. The chart lift is an abstract `w` with
   `HasDerivAt w (X_G (w u)) u`.
4. **Agreement at `m = n`.** `lpRescaleNM` at `m = n` is LP-DICT's `lpRescale` (`rfl` or `ext`).
5. **Conditional composition** (distinct name, docstring "conditional"): the generic `nonresonant_drift_of_chartDataNM`
   with an abstract chart Hamiltonian `G` and lift `w` in place of `liftChartHam` and the planar lift. Its premises
   are the engine's inputs plus the trace identity, `realDom` membership along `J`, and stopped slow
   membership.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 400–900 lines. Stop when done or blocked; report any convention mismatch precisely.

## Handoff

`docs/tracks/LP/audits/LP-SP-ADAPT-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-ADAPT.md`,
then `touch .drafts/READY-LP-SP-ADAPT`.
