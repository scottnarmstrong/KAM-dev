# Package LP-SP-NRR: the spatial engine data and stopped drift (MAIN Lemma 13 with 2n slow pairs; Theorem 19)

Wave 4. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff;
module docstrings carry the SPEC §4 sentence). Base: `inp-lp-spnrr` = `inp-lp` + every spatial package so far
(SP-MODEL, SP-GEO, SP-ROT, SP-CHART, SP-PROD, SP-TUBE, SP-CONF, SP-OSC, SP-ADAPT, SP-DOM).

## Template

The planar LP-NRR (landed: `KAM/Planetary/StrongAMD/NonresonantReuse/{Kepler,Pert,PertClass,Hyp,Drift}.lean`,
`lp_stopped_drift`; audit LP-W3B-1). MAIN T19: "There are n fast angles and 2n slow canonical pairs. Lemmas 9–12
apply with exactly this pair count: it changes dimension constants … not the Diophantine exponent or the power
of μ." So:
- **Reuse unchanged** the Kepler data (`lpKepler`, frequencies, `FreqLipschitz`, `lpKepler_isNonresonant`: they
  depend only on the `n` fast actions) and NRS's `lp_scale_choice` with `k = n + n` (the slow-pair count enters
  only through `SL`: `64π k s rB ≤ w²`).
- **Re-do for the spatial chart:**
  - the perturbation `lpPertNM` from SP-DOM's `fc` (spatial `tubeNM` extension) through SP-ADAPT's complex
    unrescaling;
  - its `ext_class` and `WBound` (`wbound_of_sup_bound`);
  - `ExtNFHyp b s K α L 2 ε {0} lpKepler lpPertNM` for `b : PartialBlock n (n + n)`;
  - the trace identity against `lpRescaleHamNM` of the spatial chart Hamiltonian (SP-PROD split);
  - the stopped drift via SP-ADAPT's `nonresonant_drift_of_chartDataNM`.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 13 (429–464) and Theorem 19 (599–603), with `source/AMENDMENTS.md` N6 (strict
`D₀√μ < r_*`: choose `ρ` strictly inside), N4, N12.

## Owned files

`KAM/Planetary/Spatial/NonresonantReuse.lean` (facade) and parts. Do not edit other files.

## Statements

1. `lpPertNM` and its class, sup bound and `WBound` (the (22)/(47) containment via SP-DOM's D5).
2. `lpExtNFHypNM`: every field for `PartialBlock n (n + n)`.
3. `lpTraceNM`: the trace identity on `b.realDom b.rB`.
4. **`spatial_stopped_drift`.** Constants `μ₀, c, T₀` and the widths are chosen before `μ`, `I⁰` and the solution.
   For every `0 < μ ≤ μ₀`, every `I⁰ ∈ 𝓛_δ` with (5), and every spatial moving solution with chart lift meeting
   `nonresonant_drift_of_chartDataNM`'s premises (realDom along `J`, initial action, stopped slow membership
   in ball (47), time bound): `‖Λ(z u) − I⁰‖ ≤ D₀√μ/2`. Premises are only the solution, its lift and the
   localization (D1-style), never a drift or AMD bound.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms`.

Expected size 700–1,500 lines. If an `ExtNFHyp` field cannot be met with the spatial data, STOP and report the
exact field.

## Handoff

`docs/tracks/LP/audits/LP-SP-NRR-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-SP-NRR.md`, then
`touch .drafts/READY-LP-SP-NRR`.
