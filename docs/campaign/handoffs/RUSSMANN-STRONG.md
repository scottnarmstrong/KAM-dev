# Handoff RUSSMANN-STRONG (Opus 5.5): the strong form of R-HEAD, route (B), and its provider

Branch `russmann-w`, worktree `/home/scott/KAM-dev-worktrees/russmann-w`.
- Commits: `c77a9f3c` (strong assembly), then a merge of `russmann` (`f59b219f`, as instructed:
  brings the frozen R-HEAD, commit `a9f95098`), then `897e42ab` (provider), then `c43bd471` (route
  doc), then this handoff.
- Nothing under `KAM/Frozen/` or `manifest/` was edited. No existing track-P file was changed.

## Outcome

- **The frozen R-HEAD is ready to seal.** The provider `KAM.Provider.Russmann.russmann_kam`
  (`KAM/Provider/Russmann/RussmannKam.lean`):
  - has exactly the frozen type, with the binders copied verbatim;
  - is proved by the single term
    `KAM.Russmann.russmann_tori_strong hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real h_russmann`;
  - imports the frozen definitions and `KAM.Russmann.AssemblyStrong`, never the frozen theorem.
- **Seal probe.** `.drafts/russmann/SealProbe.lean` is a byte copy of the frozen anchor with body
  `by exact KAM.Provider.Russmann.russmann_kam hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real
  h_russmann` (every explicit binder, in order, as in D26). It elaborates; axioms
  `[propext, Classical.choice, Quot.sound]`.
- **Brief items.**
  1. Track P export `weak_kam_quantitative_lip`, with the zero case. It is additive: a new file;
     the family construction of `Assembly.lean` is repeated with one more clause.
  2. Route (B) in track R, and the inline assembly `KAM.Russmann.russmann_tori_strong`. It has
     R-HEAD's hypotheses verbatim and the audit's F1 conclusion, with the cover inlined.
  3. The strong ⇒ `4⁻ⁿ` corollary `KAM.Russmann.russmann_tori_of_strong`, through
     `quarter_le_of_diff_le`.
- **Drafts** (`.drafts/russmann/`, gitignored):
  - `RussmannKamStrong.lean`: the strong form in frozen layout, named `russmann_kam_strong`.
    Superseded by the frozen file, whose type is identical, under the name `russmann_kam`.
  - `CheckStrong.lean`: the combined check, with the cover and `sorry`.
  - `ProviderCheckStrong.lean`: proves the strong theorem by the one-term provider, and the
    `4⁻ⁿ` theorem from `russmann_tori_of_strong`.

## Files

| File | Status | Content |
|---|---|---|
| `KAM/Planetary/Quantitative/AssemblyLipschitz.lean` | new, 140 lines | `QuantitativeFamily.DefectLipschitz`, `p11c_asm_family_lip`, `p11c_asm_zero_family_lip`, `weak_kam_quantitative_lip` |
| `KAM/Russmann/Extension.lean` | new, 144 | `exists_lipeo_extension`, `inner_subset_image`, `box_subset_inner`, `volume_box`, `volume_image_cell_lower`, `exists_inner_volume_gt` |
| `KAM/Russmann/StrongBudget.lean` | new, 106 | `exists_compact_open_budget`, `strong_volume_arith` |
| `KAM/Russmann/AssemblyStrong.lean` | new, 319 | `familyImage_translate_mem`, `familyImage_actions_mem`, `russmann_tori_strong`, `quarter_le_of_diff_le`, `russmann_tori_of_strong` |
| `KAM/Russmann/FundamentalDomain.lean` | edited (mine) | adds `exists_measurableSet_subset_fundamentalDomain_inter`; `volume_le_volume_fundamentalDomain_inter` keeps its statement and is now its corollary |
| `KAM/Provider/Russmann/RussmannKam.lean` | filled (owned by this package) | `KAM.Provider.Russmann.russmann_kam` |
| `KAM.lean` | regenerated | `+4` imports; the generator skips the provider |
| `docs/tracks/R/PROOF-ROUTE.md` | appended | route (B) status table and order of choices |

## Approach

Route (B) of PROOF-ROUTE.md. Track P's internal clause `SelectionLipschitz.lipschitz_joint` (the
defect is `2⁻¹⁰`-Lipschitz on `ℝⁿ × good`) is exported.

- **The lipeomorphism.** `KAM.mcshane_prod` extends the defect with sup bound `Δ`, and
  `E = id + Φ` is a bijection by `KAM.lipeo_onto`. So `E` covers the `Δ`-interior
  `[Δ, 1−Δ)ⁿ × U_Δ` of `[0,1)ⁿ × U`. No degree theory is needed.
- **The near-full image.** It follows that
  `meas T([0,1)ⁿ × good) ≥ (1−2Δ)ⁿ meas U_Δ − (1+2⁻¹⁰)^{2n} meas(U ∖ good)`, using
  `KAM.lip_image_prod`.
- **The limit.** Inner regularity gives `K`, outer regularity gives `U`, continuity from below
  gives `Δ₀`, and the displacement bound `Δ(ε) ≤ c_Δ√ε/γ` gives `Δ → 0`. Together they give
  `(1 − κ) meas B`.
- **The complement.** The measurable mod-`ℤⁿ` reduction gives a measurable `F ⊆ FD ∩ cover`, so
  the complement is bounded by `meas FD − meas F`.

## Checks (exact)

- **Builds.** `nice -n 5 lake build KAM.Russmann.Assembly KAM.Russmann.AssemblyStrong
  KAM.Provider.Russmann.RussmannKam KAM.Planetary.Quantitative.AssemblyLipschitz` →
  `Build completed successfully (9314 jobs)`. No warning in any file of this package.
- **Lint.**
  - `sh scripts/lint_sources.sh` fails only in the ABI step. That step needs oleans of every frozen
    anchor's providers (a library-scale build, forbidden here), as in RUSSMANN-W.
  - With that one line removed (`.drafts/lint_noabi.sh`): `check_lean_modules: PASS (1409 Lean
    files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, exit 0.
- **Root imports.** `python3 -I scripts/gen_root_imports.py`: `+4` lines, committed.
- **Axioms** (`.drafts/russmann/AxiomsStrong.lean`). Each of the following depends only on
  `[propext, Classical.choice, Quot.sound]`:
  `KAM.Provider.Russmann.russmann_kam`, `russmann_tori_strong`, `russmann_tori_of_strong`,
  `quarter_le_of_diff_le`, `KAM.Planetary.weak_kam_quantitative_lip`, `exists_lipeo_extension`,
  `inner_subset_image`, `volume_image_cell_lower`, `exists_inner_volume_gt`,
  `exists_compact_open_budget`, `strong_volume_arith`,
  `exists_measurableSet_subset_fundamentalDomain_inter`, `familyImage_translate_mem` and
  `familyImage_actions_mem`.
- **Draft checks.** `lake env lean .drafts/russmann/CheckStrong.lean` gives only `declaration uses
  'sorry'`. `ProviderCheckStrong.lean` and `SealProbe.lean` give only the axiom lines above.

## Uncertainties

- The proof depends on the unfrozen track-P theorem and on its new additive export.
  `weak_kam_quantitative_lip` is a repackaging of objects that track P already proved
  (`evaluation_bilipschitz`'s output carries `lipschitz_joint`), so no new estimate is involved.
- The kernel replay (`leanchecker`) is not run here; that belongs to the orchestrator's sealing
  step.

## Suspected errata and deviations

- No new erratum in a pinned source.
- No new deviation: the frozen statement adopts D-R1–D-R5 (ruling R1).
- The audit's F1 text writes `∖` (U+2216). The frozen file uses Lean's `\` (SDiff). This is
  already the orchestrator's frozen text; I note it only for the record.

## What remains

Sealing by the orchestrator:
- body `by exact KAM.Provider.Russmann.russmann_kam hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real
  h_russmann`;
- the ABI and anchor checks;
- the kernel replay and an independent audit of the provider chain.
