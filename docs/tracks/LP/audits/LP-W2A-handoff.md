# LP-W2A: combined audit handoff for LP-DOM + LP-NRS (track LP, wave 2)

Branch `inp-lp-w2a` (worktree `/root/code/KAM-inp-lp-thr`) = `inp-lp-dom` (d66fa68b) + `inp-lp` (landed wave 1,
main 22c7517e) + `inp-lp-nrs` (91da0b27), at 0698c776 plus this handoff. The package diff is
`git diff inp-lp...HEAD -- KAM`: 6 new Lean modules (AnalyticDomain facade + Core/Safety/Extension/Containment,
NonresonantScale) plus the regenerated `KAM/Root/Planetary.lean`, about 930 lines. Wave 1 (THR, MOM, GEOMOD,
DICT) is landed and audited (LP-BAR1-1, LP-W1B-1) and NOT in scope. Nothing in track LP is frozen.

Prover handoffs (declarations, checks, axioms, AUDIT FOCUS):
- `docs/tracks/LP/audits/LP-DOM-handoff.md`: MAIN Lemma 8. Brief:
  `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-DOM.md`.
- `docs/tracks/LP/audits/LP-NRS-handoff.md`: MAIN (37), the scale choice and exponential horizon of Lemmas 12/13.
  Brief: `…/packages/LP-NRS.md`.

Source: `docs/tracks/LP/source/MAIN.md` (L8 244–271; L12 381–428; L13 429–464) with
`docs/tracks/LP/source/AMENDMENTS.md`. **N2** (shared `U`), **N3** (`r_* ≤ 4r_g`, (22) within the tube),
**N4** ((35) not a dependency) and **N6** (L13 widths; stopped radius `D₀√μ`, improvement `r/2`) bear directly on
these packages.

## Orchestrator checks (kam-lp, on 0698c776)

- `lp_build.sh` (4G cap) of Geometry, Modulus, Continuation, PlanarDictionary, NonresonantScale, AnalyticDomain:
  all "Build completed successfully".
- `lp_lint.sh`: exit 0. `main_shortname_check.py` on the 6 modules: OK. `git diff --check`: clean.
- Review of the DOM statements D0–D6 and NRS items 1–3 against the briefs: no finding. DOM omits MAIN L8's
  separate first-derivative and denominator clauses. The Lean route (engine Lemma 13) consumes only the scalar
  sup bound of `f` (via `wbound_of_sup_bound`) and the real trace, so this is acceptable; please confirm.

## REPORT FORMAT

One section per package (LP-DOM first, then LP-NRS), each with its own verdict, then a combined verdict.

## AUDIT FOCUS (beyond the two prover handoffs)

LP-DOM:
- The quantifier order of `exists_strongTube`: `R`, `M`, `fc` are chosen before any `I⁰` and `μ`.
- `strongCore` is MAIN's union over `I⁰ ∈ 𝓛_δ` (existential). Check compactness and `strongCore_subset_dom`
  (`Γ_i < I_i`, MAIN line 251).
- `IsSharedTube` (N2) is a premise of D2–D5 and is produced by D1 (`exists_isSharedTube`). Confirm it is typing
  data (a chosen `r_g`), not a smuggled conclusion.
- `strongCore_containment` (D5): the three (22) conditions, stated literally, with `rs ≤ 4 r` (N3).
- `movingHamiltonian_poincareProd_split` (D6): exact, with no truncation.

LP-NRS:
- Items (b), (c), (d), (e) of `lp_scale_choice` against the engine's literal numerics (`ExtNFHyp.divisor_size`,
  `slow`, `cutoff`; `nonresonant`'s `hsmall` and time bound) with `p = 2`.
- `κ, μ₀, c, T₀` depend only on the data, and precede `μ`.
- `diophantine_to_period_one`: `modeSize` is ℓ¹ and agrees with `zBall`.
