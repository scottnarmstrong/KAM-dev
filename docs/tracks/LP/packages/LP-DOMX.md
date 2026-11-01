# Package LP-DOMX: the remaining clauses of MAIN Lemma 8 (chart, momenta and derivative bounds; denominators)

Wave 2 supplement. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped
wrappers, handoff). Base: `inp-lp` (LP-DOM audited in LP-W2A-1).

## Why

LP-DOM proved the clauses of MAIN L8 that the Lean route consumes:
- the holomorphic periodic extension `fc` of the perturbation;
- its sup bound `M`;
- its real trace;
- the (22) containment.

It omitted two sentences of MAIN L8 (line 253):
- "On a slightly smaller version of this domain the chart, momenta, `f`, and all their first derivatives have
  bound `M`";
- "Every Newtonian denominator there has a single holomorphic branch, and its modulus is bounded away from
  zero".

By the campaign's bookkeeping rule (PROGRESS "Carried requirements"), the L8 source node counts PROVED only
once the full conclusion is proved. This package adds the two clauses, from the same `tube` construction.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 8, lines 244–271 (the statement at 253; the proof at 263–271: the complex
neighbourhood of real points, `|w·w − |w₀|²| ≤ 2Qη + η²`, `Re(w·w) ≥ d²/2`, the principal square root, and
Cauchy estimates), with `source/AMENDMENTS.md` N2 and N3.

## Reuse

- `KAM/Planetary/Exponential/ComplexTube.lean` (`tube`, `complexTube`).
- `analyticOnNhd_poincareProd` (`Poincare/Product.lean`).
- `chart_perturbation_analytic`.
- LP-DOM's `strongCore`, `isCompact_strongCore`, `strongCore_subset_chartSafe`, `exists_strongTube`.
- GEOMOD's barrier bounds `dS ≤ |q_i|`, `dP ≤ |q_i − q_j|`, `|q_i| ≤ R`.
- Mathlib Cauchy estimates for holomorphic functions on balls, e.g.
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` or the multivariable `fderiv` bound on polydiscs;
  search first.

## Owned files

`KAM/Planetary/StrongAMD/AnalyticDomain/Bounds.lean` (and parts if needed). Do not edit LP-DOM's files; if the
facade should import the new part, report it. The orchestrator adds the import at landing.

## Statements

Same standing premises and `IsSharedTube` data as LP-DOM.

1. **Chart and momenta.** Apply `tube` to every coordinate function of `poincareProd ν 1` on `chartSafe ν`
   (`4n` real-analytic, fast-shift-periodic functions). Prove:
   - `∃ R' > 0, ∃ Ψc`, holomorphic on `complexTube (strongCore …) R'`;
   - `Ψc` is periodic and has real trace `poincareProd ν 1` (positions and momenta);
   - `‖Ψc‖ ≤ M'` on the half tube.
2. **First derivatives.** On `complexTube (strongCore …) (R''/4)`, with `R'' = min R R'`: `‖fderiv ℂ fc z‖` and
   `‖fderiv ℂ Ψc z‖` are bounded by explicit constants (Cauchy). Constants are uniform: chosen before `I⁰` and
   `μ`.
3. **Denominators.** For every star and pair difference vector `w(z)` of complexified positions, on a smaller
   uniform tube: `Re (w · w) ≥ dS²/2` (resp. `dP²/2`), where `·` is the bilinear complex dot product, not the
   Hermitian norm. Hence `(w · w)^{1/2}` (the principal branch) and its reciprocal are holomorphic, with
   `‖(w · w)^{-1/2}‖ ≤ √2/d`. MAIN lines 266–268.
4. **Facade-level summary** `lemma8_complete`: a single statement collecting LP-DOM's D4/D5 outputs with items
   1–3, quantified as MAIN L8 (constants `r_*, s, b, M` before `I⁰`), for the PROVED bookkeeping. It may restate
   DOM outputs by citing them; do not reprove them.

## Checks and stop condition

- `lp_build.sh`.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–4.

Stop when done or blocked: report, never add a hypothesis silently. Expected size 500–1,200 lines.

## Handoff

`docs/tracks/LP/audits/LP-DOMX-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-DOMX.md`, then
`touch .drafts/READY-LP-DOMX`.
