# SO-CSEG-L2 handoff (audit request): stage memoization

Branch `inp-csegl2` (worktree `/root/code/KAM-inp-csegl3`), off `inp-csegl3` at 77ffd19d.
Design: `docs/tracks/SO/design/SO-CSPLIT.md` §3.4, §8 row SO-CSEG-L2. Signatures:
`.drafts/design/SOCsplitSignatures.lean` §(E) and the Gram/torsion/frame bridges of §(F) (identical to
the copy in `/root/code/KAM-inp-socsplit2/.drafts/design/`, checked by `diff`).

## Files

- `KAM/CertificateSharp/Kernel/Stage.lean` (new, 208 lines; imports only `Frame.Majorants`).
- `KAM/CertificateSharp/Tests/Stage.lean` (new, 203 lines).
- No landed definition or statement changed; no SO-CSEG-A/B/L3 file touched; `KAM.lean`/`KAM/Root`
  not regenerated (left to the orchestrator, as for L3).

## Signatures against the audited design

Every statement below is copied verbatim from the signatures file (binders, keys, shapes, names).

| declaration | design status | here |
|---|---|---|
| `matMulEntry` (def) | body verbatim | same |
| `modelMatMul_eq_buildMat` | `rfl` | `rfl` |
| `modelMatMul_eq_of_entries` | stated, `sorry` | **proved** (via the new helper below; `List.map_congr_left`) |
| `matMulEntry_eq_of_products` | proved | same proof |
| `gramModels_eq_of_entries` | stated, `sorry` | **proved** (`unfold gramModels`, `map_congr_left`, case `a ≤ b`) |
| `gramDefectRows_eq_of_entries` | proved | same proof (explicit `congrArg`) |
| `gramCheck_eq_of_rows` | proved | same proof |
| `torsionModels_eq_of_stages` | proved | same proof (`unfold; rw`; no `simp` over the body) |
| `frameNModels_eq_of_stage` | proved | same proof |
| `checkGram_of_gramCheck`, `checkTorsion_eq_of`, `checkFrameT_eq_of`, `checkFrameN_eq_of` | §(F), proved; not in SO-CSEG-B's SegBridges | same statements and proofs, placed in Stage.lean |

One addition not in the signatures file: `buildMat_modelMatrixEntry` (public helper:
an `r × c` list matrix equals `buildMat r c (modelMatrixEntry M)`), used by
`modelMatMul_eq_of_entries`. It is a plain fact about landed defs, not conclusion-shaped.

No signature failed to prove as stated.

## Checks

- `inp_lake_build.sh … KAM.CertificateSharp.Kernel.Stage`: `✔ Built KAM.CertificateSharp.Kernel.Stage
  (3.5s)`, Build completed successfully; no warnings in the new files.
- `inp_lake_build.sh … KAM.CertificateSharp.Tests.Stage`: `✔ Built KAM.CertificateSharp.Tests.Stage
  (4.0s)`, Build completed successfully; no warnings in the new files.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS (1688 Lean files)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (158 frozen declarations)`; exit 1 only for `KAM.lean is out of date; run
  scripts/gen_root_imports.py (KAM/Root/CertificateSharp.lean)` (two new modules; root generation is
  the orchestrator's).
- Lines ≤ 100 columns; no `sorry`/`axiom`/heartbeat or recursion options.
- `#print axioms` of all 11 Stage theorems above, `buildMat_modelMatrixEntry`, `stage_torsion`,
  `stage_gramCheck`: `[propext, Classical.choice, Quot.sound]` each.
- `main_shortname_check.py` (both modules): exit 7,
  `REUSED SHORT NAME gramCheck_eq_of_rows (KAM/CertificateSharp/Kernel/Stage.lean) already in
  KAM/SpinOrbit/Data/GramSplit.lean on unmerged branch inp-sodata3`. The name is the audited design
  signature's; not renamed (needs the orchestrator's ruling: rename here, or the SO-DATA3 probe's is
  dropped/renamed when that branch lands).

## Tests (toy recipes, all `decide +kernel`, each compared with the monolithic run)

Data copied (exposed) from `Tests/Torsion` with the flat embedding `K = (θ, 1)`, `B = 1`, so all stage
literals are short.
- Products: two `CertModel.mul` stages → `matMulEntry_eq_of_products` → `modelMatMul_eq_of_entries`
  reproduce a `1×2 · 2×1` product with nonzero radii (`[[7 ± 53/1000]]`) = `stage_matMul_whole`.
- Gram: entry stage → `gramModels_eq_of_entries` → `B·G` stage → `gramDefectRows_eq_of_entries` →
  `gramCheck_eq_of_rows` (shape by decide) → `gramCheck … = some (0, 1)` = whole run.
- Torsion: 13 stage premises (eps, ms, L, Gi, DL, N0 … Y) → `torsionModels_eq_of_stages` → residual
  decide → `some stageT` = whole run. FrameN: `frameNModels_eq_of_stage` reusing torsion's `stage_N0`.
- R7 timing (profiler, scratch only): whole test module ≈ 1.1–1.5 s type checking, no declaration
  above 0.5 s; recipes are no costlier than the `_whole` runs.

## Uncertainties

- R7 on toys is weak evidence: the toys are too small to separate residual cost from stage cost, and
  my attempt to profile per declaration was not clean. The binding R7 measurement is CAL-2's.
- The test module derives `DecidableEq` for `CC`, `CertPoly`, `CertModel` (global instances in a
  test module nothing imports) to decide `t = lit`; production stage theorems will instead use
  SO-CSEG-A's `modelBeq` soundness.
- The flat toy makes many stages empty/zero; the products toy carries genuine radii, but the Gram and
  torsion recipes do not exercise nontrivial truncation.
- §(F) Gram/torsion/frame bridges were not assigned to SO-CSEG-B's SegBridges, so I placed them in
  Stage.lean; move them if the orchestrator prefers.

## Errata and deviations

No suspected errata in pinned sources. Deviations: the added helper `buildMat_modelMatrixEntry`;
the §(F) bridges' placement; the short-name collision above.

## Orchestrator note (short name)
The short-name clash of `gramCheck_eq_of_rows` with SO-DATA3's probe Data/GramSplit.lean is resolved: the
orchestrator ruled that the audited design name stays, and SO-DATA3 deleted the superseded probe (inp-sodata3
cf56e57b).

## AUDIT FOCUS (orchestrator)
1. Fidelity: every Stage.lean declaration equals the audited signatures §(E) and the Gram/torsion/frame bridges of
   §(F) verbatim; `buildMat_modelMatrixEntry` is the one addition.
2. Soundness of the computation-only equalities, `modelMatMul_eq_of_entries` and `gramModels_eq_of_entries`
   especially (the case `a ≤ b`), and that no `simp` runs over a landed body (design audit 1).
3. Fitness: these lemmas let Gram, torsion and the frames be proved one matrix entry per theorem and reassembled
   into the landed `checkGram`/`checkTorsion`/frame Bools (design M2). Say whether anything is missing for the
   production templates.
4. No landed declaration changed; tests compared against the monolithic runs; replay; axioms.
