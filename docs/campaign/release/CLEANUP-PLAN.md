# Clean-up plan for the public release (tracks K, I, N, P)

Read-only analysis of `inp-cleanup` at `a157bd9a` (2026-10-29). Scope: `KAM/**` minus `KAM/Certificate/**`,
`KAM/SpinOrbit/**`, `KAM/Frozen/**`: **1155 files, 245 386 lines** (Planetary 760 files, Nekhoroshev 136, Iso 73,
Head 36, Strip 23, Provider 22, Canonical 21, Apost 19, Kepler 14, ODE 13, Weighted 9, Uniq 6, Diophantine 5, Matrix 5,
Measure 5, Fourier 4, Torus 3, Analysis 1). All counts are from cheap textual scans (regexes over source text, no
elaboration); each category says where they over- or under-count.

## Summary

| # | Category | Count | Effort |
|---|---|---|---|
| 1 | Unreferenced public declarations | 36 (15 `@[simp]`) | small |
| 2 | Campaign language in comments/docstrings | ~450 files (package tags 433, design-doc paths 261, audit/ruling 31+19, dated rulings 4, personal attribution 3 files) | **large, mechanical** |
| 3 | Module docstrings missing / stale | 0 missing; ≥3 stale ("not yet", "later packages") | small |
| 4 | Naming: package-prefixed names | ~1840 declarations (`p11c` 864, `p11` 760, `P11` 65, `p11hs` 44, …); `iso*` ~95, `planet*` 14 | **large, owner decision** |
| 5 | Files > 1000 lines | 2; duplicate statements 38 groups (9 cross-directory) | small |
| 6 | Release blockers | personal attribution in comments, inconsistent copyright lines, absolute paths in scripts/docs, 688 whole-`Mathlib` imports | small–medium |

## 1. Unreferenced public declarations

Method: every non-private `theorem/lemma/def/abbrev/structure/class` whose short name and full name occur only once
(its own declaration) as a token across `KAM/`, `scripts/`, `docs/`, `manifest/`, `blueprint*/`. Over-counts:
`@[simp]` lemmas are used silently by `simp` (keep unless a `simp?` sweep shows otherwise). Under-counts: a name
mentioned in a docstring or doc counts as "used". Three parser false positives were dropped (`orbit`,
`IsActionNorm`, `oscClass` inside docstrings).

**Helpers (likely delete or make `private`)** — 12: `Apost/Constants.lean:175 mSize_le_Theta`,
`Nekhoroshev/Partial/NormalFormInduction.lean:398/404 nnfF_zero/nnfF_succ`, `Planetary/PlanarTorsion/RealFlow/PicardOp.lean:57,60,69`
(`p11cTimeScale_*` ×3), `Planetary/Quantitative/BudgetPositivity.lean:163 qbc_tflat_le_one`,
`Head` frame lemmas `frameL0_mulVec`, `frameN0_mulVec` (`Head/MatrixNorms.lean:60,65`),
`Head/HBounded.lean:48 isometry_ofReal_pi`, `Diophantine/Cohomological.lean:67 directionalCoeff_eq_sum`,
`Nekhoroshev/Averaging/Rank.lean:165 «lambda»` (also a bad name).

**API-looking (keep; they complete a basic API)** — 24: the 7 `Matrix/Calculus.lean` `*_apply` simp lemmas,
`Fourier/Convolution.lean:152,160,176` (`convolution_add`, `convolution_smul_left`, `convolution_unit_right`),
`Diophantine` zero lemmas, `SolverAlgebra.lean:55 solveLinearMap` (+ `solve_directionalCoeff`),
`Head/Data.lean:109,112 unperturbedTorus_fst/snd`, `Strip/Cauchy.lean:145`, `Strip/HigherCauchy.lean:84`, plus `Apost/Schedule.lean:70 deltaSeq_zero`, `Diophantine/FrequencyDependence.lean:110`, `Head/Frequency.lean:47 realInclusion_eq`, `Head/PhaseAverage.lean:65 phaseShift_zero`.

Full list:

| location | declaration | note |
|---|---|---|
| `KAM/Apost/Constants.lean:175` | theorem `mSize_le_Theta` |  |
| `KAM/Apost/Schedule.lean:70` | theorem `deltaSeq_zero` |  |
| `KAM/Diophantine/Basic.lean:28` | theorem `modeSize_zero` | @[simp] |
| `KAM/Diophantine/Basic.lean:51` | theorem `frequencyDot_zero` | @[simp] |
| `KAM/Diophantine/Cohomological.lean:53` | theorem `flowMultiplier_zero` | @[simp] |
| `KAM/Diophantine/Cohomological.lean:67` | theorem `directionalCoeff_eq_sum` |  |
| `KAM/Diophantine/Cohomological.lean:128` | theorem `solveBound_zero_exponent` | @[simp] |
| `KAM/Diophantine/FrequencyDependence.lean:110` | theorem `summableWeighted_solve_sub_solve` |  |
| `KAM/Diophantine/SolverAlgebra.lean:55` | def `solveLinearMap` |  |
| `KAM/Diophantine/SolverAlgebra.lean:61` | theorem `solve_directionalCoeff` |  |
| `KAM/Fourier/Convolution.lean:152` | theorem `convolution_add` |  |
| `KAM/Fourier/Convolution.lean:160` | theorem `convolution_smul_left` |  |
| `KAM/Fourier/Convolution.lean:176` | theorem `convolution_unit_right` | @[simp] |
| `KAM/Head/Data.lean:109` | theorem `unperturbedTorus_fst` | @[simp] |
| `KAM/Head/Data.lean:112` | theorem `unperturbedTorus_snd` | @[simp] |
| `KAM/Head/Frequency.lean:47` | theorem `realInclusion_eq` |  |
| `KAM/Head/HBounded.lean:48` | theorem `isometry_ofReal_pi` |  |
| `KAM/Head/MatrixNorms.lean:60` | theorem `frameL0_mulVec` |  |
| `KAM/Head/MatrixNorms.lean:65` | theorem `frameN0_mulVec` |  |
| `KAM/Head/PhaseAverage.lean:65` | theorem `phaseShift_zero` | @[simp] |
| `KAM/Matrix/Calculus.lean:67` | theorem `matMulCLM_apply` | @[simp] |
| `KAM/Matrix/Calculus.lean:78` | theorem `matMulVecCLM_apply` | @[simp] |
| `KAM/Matrix/Calculus.lean:94` | theorem `matMulRightCLM_apply` | @[simp] |
| `KAM/Matrix/Calculus.lean:105` | theorem `matMulVecRightCLM_apply` | @[simp] |
| `KAM/Matrix/Calculus.lean:108` | theorem `matEntryCLM_apply` | @[simp] |
| `KAM/Matrix/Calculus.lean:115` | theorem `matTransposeCLE_apply` | @[simp] |
| `KAM/Matrix/Calculus.lean:120` | theorem `matTransposeCLM_apply` | @[simp] |
| `KAM/Nekhoroshev/Averaging/Rank.lean:165` | theorem `«lambda»` |  |
| `KAM/Nekhoroshev/Partial/NormalFormInduction.lean:398` | theorem `nnfF_zero` |  |
| `KAM/Nekhoroshev/Partial/NormalFormInduction.lean:404` | theorem `nnfF_succ` |  |
| `KAM/Planetary/PlanarTorsion/RealFlow/PicardOp.lean:57` | theorem `p11cTimeScale_one` |  |
| `KAM/Planetary/PlanarTorsion/RealFlow/PicardOp.lean:60` | theorem `continuous_p11cTimeScale_apply` |  |
| `KAM/Planetary/PlanarTorsion/RealFlow/PicardOp.lean:69` | theorem `continuous_p11cTimeScale` |  |
| `KAM/Planetary/Quantitative/BudgetPositivity.lean:163` | theorem `qbc_tflat_le_one` |  |
| `KAM/Strip/Cauchy.lean:145` | theorem `norm_iteratedDeriv_coordinate_le_of_mem_complexStrip` |  |
| `KAM/Strip/HigherCauchy.lean:84` | theorem `norm_iteratedFDeriv_three_le_of_mem_complexStrip` |  |

## 2. Internal campaign language

| pattern | files | lines |
|---|---|---|
| `package` (e.g. "package N11-F1", "P14 package E1") | 433 | 467 (Planetary 371, Nekhoroshev 50, Head 24, Iso 24, Canonical 17) |
| paths into `docs/campaign`, `docs/tracks`, `docs/errata`, `docs/explorations` | 261 | 262 |
| "Design …" sentences | 342 | — |
| package codes `N11-F2`, `P11A-C8`, `GAP-I1a`, `F2-C1` | 29 (+51 `GAP-`/`F<n>`) | 38 |
| audit / audit fix / audited | 31 | 39 |
| owner / ruling | 19 | 24 |
| track K/I/N/P, campaign, lane, handoff | ~35 | 66 |
| orchestrator, "round 2", dates | 5 | 5 |
| TODO/WIP/FIXME, `sorry` | 0 | 0 |

Worst examples:
- `KAM/Nekhoroshev/Partial/Iterative.lean:42` — "Lane-N ruling F2-C1 (<named contributor>'s team, 2026-10-28)" (dated, names a person).
- `KAM/Planetary/MaximalStep/StepCoeff.lean:364` — "orchestrator ruling 2026-10-28, P11A-C8".
- `KAM/Planetary/MaximalStep/RealLipschitzNodes.lean:206` — "orchestrator ruling OVERNIGHT 03:15, owner to review; audit 1, F1".
- `KAM/Nekhoroshev/Partial/CanonicalMap.lean:284` — "orchestrator ruling 21:15".
- `KAM/Planetary/Nondegeneracy/Interface.lean:190` — "Companions (round 2)".
- `KAM/Head/Adapters.lean:18-20` — design doc + "audit `docs/campaign/audits/DESIGN-P4-audit-1.md`, finding 1".
- `KAM/Iso/Charts/Tori.lean:20,267`, `KAM/Iso/Charts/Apply.lean:22` — "audit fix F1/F2".
- `KAM/Planetary/Averaging/OscillatorStep.lean:21-22` — "see the handoff …"; "package P23-13".

Keep: blueprint labels (`bpP:p3:…`, 764 files) **if** the blueprint ships; otherwise they become dangling (owner decision D3).
Rule for the rewrite: a reason that is mathematical stays, rephrased ("the hypothesis `0 < b.c` is needed because …");
provenance (who, when, which audit/package) goes; design-doc paths are dropped or replaced by the blueprint label.

## 3. Module docstrings

Every in-scope file has a `/-!` module docstring, `module`, a copyright header, and a `public section` (the three
without one — `Planetary/PlanarTorsion/Characters.lean`, `Planetary/Preparation/Slow.lean`,
`Planetary/TwoScale/Measure.lean` — are import-only facades, correct as is). Stale docstrings found by
"not yet / later packages / handoff / to be proved" (3 files; a reading pass will find more):
`Planetary/Averaging/OscillatorStep.lean:21` (says Lie-series transfer "not yet done" — verify against the landed
`osc_iter`), `Planetary/Preparation/HoloData.lean:21,138` ("later packages P2c–P2f"),
`Planetary/PlanarTorsion/RealFlow/Variational.lean:276`. Batch 2 should re-read docstrings it touches anyway.

## 4. Naming

- **Package-prefixed declarations: ~1840.** `p11c` 864, `p11` 760, `P11` 65, `p11hs` 44, `p11euclid` 22,
  `p8` 10, `p11dg` 10, `p11max` 8, `p12c` 6, `p11dot` 6. These encode blueprint part numbers, not mathematics.
- **Clash-dodging prefixes:** `iso*` ~95 (`isoSum` 12, `isoEps` 11, `isoNew` 10, `isoLim` 5, …),
  `planet*` 14, `wbud_*` 24, `qbc_*` 53, `multi_*` 33, `nnf*` 63, `oEps_*` 7, `kep*` 3, `graph*` 1
  (`Iso/Confinement/Setting.lean:230 graphSet`). No `so*`/`soGraph*` in scope (those live in SpinOrbit).
  Mathlib style is namespaces (`KAM.Planetary.Weak.budget_…`), not prefixes.
- **Mathlib-convention deviations:** 73 uses of `lemma` (fine in Mathlib today, but mixed with `theorem`; pick one);
  35 `def` names in snake_case (Prop-valued ones should be UpperCamel structures/`def`s, data `lowerCamel`);
  `«lambda»` (`Nekhoroshev/Averaging/Rank.lean:165`) and `H/F/Mconst_eq_derivConst*` mixed-case names;
  `prop2_hρ0` / `seq_γ₁`-style names that encode paper numbering.
- Renaming is not proposed here; see D1.

## 5. Size and duplication

- Files > 1000 lines (cap 1500): `Planetary/Averaging/OscillatorBracket.lean` (1103),
  `Iso/Apost/ConstantsArith.lean` (1062). Optional split, not required.
- Identical full statements (same binders and conclusion, ≥60 chars): **38 groups, 9 across directories.** Examples:
  `Matrix/Norms.lean:228` = `Strip/RealRestriction.lean:302` (`omegaZero_omegaZero`);
  `Iso/Apost/NewtonError.lean:181` = `Iso/Apost/Torsion.lean:50` (`isoNewtonMap_of_mem`);
  `Apost/Hamiltonian.lean:237 sqMat_apply_eq` = `Head/TorsionRegularGeneral.lean:125 sqMat_apply_entry`;
  `Head/Lagrangian.lean:59` = `Iso/Linear/Energy.lean:45`; `Head/DerivativeBounds.lean:161` = `Head/H1.lean:36`;
  `Planetary/Nondegeneracy/Peel.lean:206` ≈ `SecularForm/Quadratic/Algebra.lean:54` ≈ `SecularSpectrum/TwoPlanets.lean:54`.
  Within-file groups (e.g. `Averaging/OscillatorBracket.lean:441/462/497`, `Nekhoroshev/Partial/Domain.lean:118/373/702`)
  need a look: some are intentional restatements for a frozen signature.
  Near-duplicates (same conclusion, different binders) were not scanned; expect more.

## 6. Release blockers

1. **Personal attribution in Lean comments** (3 files): `Nekhoroshev/Partial/Iterative.lean:42`,
   `Strip/AnalyticTaylor.lean:23`, `Strip/CohomologicalNodes.lean:13,31` credit one named contributor.
2. **Copyright lines differ:** 1139 files carry the two-author line, **16 carry a single-author line**
   (`Apost/Constants,Correction,Exactness`, `Diophantine/*` 4, `Fourier/*` 3, `Matrix/Neumann`, `Strip/*` 8).
   Needs D2. LICENSE is Apache-2.0; headers reference it correctly.
3. **Absolute paths:** `scripts/kernel_replay.sh:39`, `scripts/land-branch.sh:10`, `scripts/wave/w0_checks.py:15`,
   `docs/DECISIONS.md:142`, and 1055 files under `docs/` mention `/root/code`. None in in-scope Lean.
   Resolved by the release pipeline excluding `docs/campaign`, `.drafts`, internal scripts (skill lean-public-release).
4. **Imports:** 688 in-scope files `import Mathlib` wholesale (e.g. `Planetary/PlanarTorsion/Characters.lean:8`).
   Not a blocker, but heavy for the elaboration test; narrowing is lean-elaboration's business.
5. Secrets: none found (token/key pattern scan over 3543 tracked files). Large files: largest tracked are
   `docs/graph/P/DEPGRAPH.md` (2.5 MB), `blueprint-P/blueprint.pdf` (2.5 MB), certificate JSONs (1.6 MB, SO scope) —
   acceptable, but decide whether built PDFs ship.
6. `sorry`/`axiom` in scope: none (scan).

## Proposed batches (independent; each one targeted build + lint)

| batch | content | size | depends on |
|---|---|---|---|
| B1 | Blockers 6.1 + 6.2: strip personal attribution (3 files), unify copyright lines (16 files) | ~20 files, comments only | D2 |
| B2a–B2d | Campaign-language scrub, split by directory: B2a Planetary (~370 files), B2b Nekhoroshev (~50), B2c Head+Iso+Canonical+Apost (~70), B2d rest (~15). Comments/docstrings only, no declaration changes, no builds needed beyond a lint + one compile check | ~450 files | D3 |
| B3 | Unused declarations: delete or `private` the 12 helpers; keep the 24 API lemmas | ~10 files | — |
| B4 | Duplicates: merge the 9 cross-directory groups (keep one, `@[deprecated]` alias or direct replacement) | ~15 files | — |
| B5 | Stale docstrings (3+) and re-read of docstrings touched by B2 | ~5 files | B2 |
| B6 | Renames (package prefixes, `iso*`, `«lambda»`, `lemma`→`theorem`) | ~1900 decls, hundreds of files | D1; last, after B2–B4 |
| B7 | Optional split of the two >1000-line files | 2 files | — |
| B8 | Script/doc absolute paths: handled by the release sync excludes | pipeline | release prep |

B1, B3, B4, B7 can run in parallel; B2 sub-batches are directory-disjoint; B6 touches everything and must run alone.
None of the batches edits `KAM/Frozen/`; renames that reach a frozen statement's dependency must keep the frozen
signature intact (frozen files reference only provider-side names, check before B6).

## Owner decisions

- **D1 (renames):** rename the ~1840 package-prefixed names and the clash-dodging prefixes into namespaces before
  release, or ship as is and document? Large diff; high risk of merge conflicts with SO.
- **D2 (copyright):** one uniform author line for all files?
- **D3 (blueprint):** do the blueprints ship? If yes, `bp*:` labels stay; if no, they go in B2.
- **D4:** do built PDFs and `docs/graph/*/DEPGRAPH.md` ship?
- **D5:** `lemma` vs `theorem` uniformity; keep or delete the 24 API-looking unused lemmas.
