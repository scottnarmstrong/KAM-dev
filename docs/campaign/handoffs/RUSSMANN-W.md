# Handoff RUSSMANN-W (Opus 5.5): Rüssmann's KAM theorem as a headline

Branch `russmann-w`, worktree `/home/scott/KAM-dev-worktrees/russmann-w`. Commits `274a8ce1` (statement)
… `e3630981` (root imports), followed by this handoff. Nothing frozen, no manifest change, no
existing tracked file modified except the generated `KAM.lean`.

## Outcome

- **Part 1.** The statement draft v0.1 of R-HEAD (`KAM.Russmann.russmann_kam`) and the new definition
  `KAM.Russmann.russmannCover` are in [docs/tracks/R/statement.md](../../tracks/R/statement.md),
  with 8 owner questions and recommendations. `RUSSMANN-W STATEMENT READY` was printed. The
  orchestrator's audit (AUDIT-RUSSMANN-STATEMENT-1) found:
  - PASS on premises, non-degeneracy, cover, non-vacuity and route.
  - F1 (scope: fixed `4⁻ⁿ` vs arbitrary loss) is with the owner. The statement is unchanged, as
    instructed.
  - F2 is expected: `Check.lean` stays the combined check.
  - F3 is fixed: `Check.lean` has the copyright header.
- **Part 2.** Beyond the brief's helper list, the **whole draft R-HEAD is proved**, in inline form:
  `KAM.Russmann.russmann_tori` (`KAM/Russmann/Assembly.lean`). It has R-HEAD's hypotheses verbatim,
  and its conclusion is R-HEAD's with `russmannCover` written out as a set-builder. The probe
  `.drafts/russmann/ProviderCheck.lean` (draft cover, then the draft theorem with body
  `KAM.Russmann.russmann_tori hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real h_russmann`)
  elaborates. **After freezing v0.1, the provider is that one term.**
- **κ-form cost** (orchestrator request): assessed in
  [PROOF-ROUTE.md](../../tracks/R/PROOF-ROUTE.md), last section.
  - Route (B) is recommended: about 500 lines, no new mathematics. It keeps `λ = 2⁻¹⁰`, exports
    track P's already-proved `SelectionLipschitz.lipschitz_joint` (about 150 additive lines), and
    adds in track R a global lipeomorphism extension plus `Δ(ε) → 0` (about 350 lines).
  - Route (A), making `λ(ε) → 0` inside track P, costs 600–900 invasive lines: the angle bound
    comes through the structure field `SelectionChain.composition_small`.

## Files (all new)

| File | Content |
|---|---|
| `docs/tracks/R/statement.md` | math statement, sources, deviations D-R1–D-R5, exact Lean text, owner questions |
| `docs/tracks/R/PROOF-ROUTE.md` | route Steps 0–5, status table, κ-form cost |
| `KAM/Russmann/Torus.lean` | `isInvariantLagrangianTorus_of_isLatticeTorus` (track-P lattice torus ⇒ frozen torus) |
| `KAM/Russmann/FundamentalDomain.lean` | `volume_le_volume_fundamentalDomain_inter` (reduction of angles mod `ℤⁿ` into `[0,1)ⁿ × B`) |
| `KAM/Russmann/FamilyVolume.lean` | `volume_le_of_lower_bound`, `familyImage_volume_lower` (`(1−2⁻¹⁰)^{2n}`), `familyImage_eq_add_angleTranslate` |
| `KAM/Russmann/Frequency.lean` | `realNbhd` facts (open, connected), `analyticOnNhd_frequencyMap`, `analyticOnNhd_gradC` |
| `KAM/Russmann/Nondegeneracy.lean` | **Rüssmann's non-degeneracy lemma** `russmann_finite_order` (exact `QuantitativeInput` form, `ρ = 1`), `russmann_finite_order_frequencyMap` |
| `KAM/Russmann/Bounds.lean` | `M`, `M₀`, `C₁` by compactness: `exists_bound_iteratedFDeriv`, `abs_iteratedFDeriv_scalar_le`, `euclid_iteratedFDeriv_le`, `isCompact_euclidThick`, `exists_hessian_bound` |
| `KAM/Russmann/Domain.lean` | `exists_compact_budget`, `volume_fundamentalDomain` |
| `KAM/Russmann/Data.lean` | `russmannData`, `russmannData_valid`, `russmannData_input` |
| `KAM/Russmann/Assembly.lean` | `russmann_tori` (inline R-HEAD) |

The file sizes are 50–188 lines.

## Approach

All KAM content comes from `KAM.Planetary.weak_kam_quantitative`; nothing in track P was
re-proved. The finite-type lemma reuses `KAM.Planetary.rank_compact` (Part 10's `cp09_unsquared`),
unfolded through `p11maxJet`/`p11dg` exactly as `p11_wr_qi` does for `ρ = 2`.

- **`τ = nμ`.** `μ` is computed once on `closure B`, inside the connected real neighbourhood
  `realNbhd B r₀`, so `τ` precedes `δ`, `K` and `f`.
- **Bounds without Cauchy estimates.** The bounds `M, M₀, C₁` come from continuity of analytic
  derivatives on compact thickenings. `ε₀` is existential, so only their existence matters.
- **The `4⁻ⁿ` constant.** It comes from the inverse-Lipschitz bound (`QuantitativeFamily.lower`
  with `KAM.lip_image_prod`), not from `cell_lower`.
- **Volume over the fundamental domain.** The cover's volume is taken inside `fundamentalDomain B`
  by a mod-`ℤⁿ` rearrangement. The cover is `ℤⁿ`-invariant, so its total volume is `0` or `∞`.

## Checks (exact)

- **Targeted builds.** `nice -n 5 lake build KAM.Russmann.Assembly` → `Build completed successfully
  (9308 jobs)`. It builds all nine modules, with no warnings in `KAM/Russmann/*`. Each module was
  also built individually.
- **Snapshot gap.** The worktree snapshot of `main` lacked the oleans of 43 track-P/Kepler modules
  (the `Nondegeneracy` chain, about 8.1k lines). They were built by the single targeted command
  `nice -n 5 lake build KAM.Planetary.WeakMeasure.FiniteType` (exit 0). This is not a library
  build.
- **Root imports.** `python3 -I scripts/gen_root_imports.py` added 9 imports, committed in
  `e3630981`.
- **Lint.** `sh scripts/lint_sources.sh` printed `check_lean_modules: PASS (1402 Lean files, 0
  comparator configurations)` and `FROZEN-ANCHOR GUARD OK`, then exit 1 from `abi_hashes.py`:
  `object file …/KAM/Frozen/Iso/Defs/BorderedHessian.olean … does not exist`.
  - This is environmental. The ABI step imports every frozen anchor and therefore every provider,
    which is a library-scale build and forbidden here. The audit saw the same failure.
  - The same script with only the ABI line removed (`.drafts/lint_noabi.sh`) exits 0.
  - No `sorry` and no line over 100 characters remain in `KAM/Russmann/*`. The `sorry` the audit's
    lint saw (Nondegeneracy.lean:133–134) was an uncommitted working-copy state; no commit ever
    contained it.
- **Drafts.** `nice -n 5 lake env lean .drafts/russmann/RussmannCover.lean` gives no messages.
  `.drafts/russmann/Check.lean` (sha256 `d57331d5…`) gives only `declaration uses 'sorry'`.
  `.drafts/russmann/ProviderCheck.lean` gives `'KAM.Russmann.russmann_kam' depends on axioms:
  [propext, Classical.choice, Quot.sound]`. The draft declaration files are unchanged:
  `8a2aa0f1…` and `8c2b6040…`.
- **Axioms** (`.drafts/russmann/Axioms.lean`): `[propext, Classical.choice, Quot.sound]` for
  `russmann_tori`, `russmann_finite_order`, `russmann_finite_order_frequencyMap`,
  `isInvariantLagrangianTorus_of_isLatticeTorus`, `volume_le_volume_fundamentalDomain_inter`,
  `familyImage_volume_lower`, `familyImage_eq_add_angleTranslate`, `volume_le_of_lower_bound`,
  `analyticOnNhd_frequencyMap`, `exists_bound_iteratedFDeriv`, `exists_hessian_bound`,
  `exists_compact_budget`, `russmannData_input` and `russmannData_valid`.

## Uncertainties

- The Rus01 PDF is not on this machine. Locators (Thm 1.7 p. 126, §1.1–1.2, Lemma 18.2 pp. 185–186)
  come from `blueprint-P/reviews/p11a-russmann-check.md`.
- `russmann_tori` is only as strong as the unfrozen track-P theorem it uses. That theorem is
  audited, and its axioms are clean.
- The κ-form line counts are estimates. For route (B) I checked the key inequality on paper, and the
  needed track-P clause exists (`ParameterLipschitz.lean:95`). Neither route is formalized.

## Suspected errata and deviations

- **No new erratum in a pinned source.** E-CP09-8 (p. 126 vs 127) is already in the ledger.
- **Deviations introduced** (statement.md §1): D-R1 phase-space volume instead of parameter measure,
  with the constant `4⁻ⁿ`; D-R2 power-law Diophantine instead of Rüssmann's `Φ`; D-R3 uniform
  complex neighbourhood, period 1 and max norms; D-R4 maximal case only; D-R5 explicit closeness
  `δ`.
- **Brief-level issue (not a source erratum).** The brief's candidate `c_n · volume
  (fundamentalDomain B) ≤ volume (cover)` would be vacuous: the cover is `ℤⁿ`-invariant. The draft
  intersects with `fundamentalDomain B`. The brief's `cell_lower` (`2^{-2N}`) cannot give `4⁻ⁿ`
  after a positive loss; `lower` can.

## What remains

- The owner's rulings on questions 1–8, F1 in particular.
- Freezing:
  - files `KAM/Frozen/Russmann/{Defs/RussmannCover,Theorems/RussmannKam}.lean`, byte-identical to
    the drafts;
  - a provider stub `KAM/Provider/Russmann/RussmannKam.lean` with body
    `KAM.Russmann.russmann_tori …`;
  - an independent audit, then sealing.
- If the owner picks the κ-form: route (B) of PROOF-ROUTE.md (about 500 lines).
