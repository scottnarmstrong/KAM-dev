# W7-MEASURE independent package audit 2

Verdict: **PASS for the round-2 tight delta. F1 and F2 are closed.** The handoff's repaired package-completion claim is accurate relative to the unchanged round-1 PASS material and the repairs reviewed here. This is package infrastructure completion, not sealing or proof of the existential `KAM.Wave.nlw2` headline.

## Scope and evidence

Audited HEAD `4649f5bc4fc0afdc905181c7050426801270080a`; comparison branch `inp = 053c70eb8d26d0283fefefa9ff18dee71696ec0f`. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, round-1 audit and the handoff's W7-FIX/AUDIT FOCUS. D53 is binding as supplied by the owner; this checkout's DECISIONS ends at D51.

Compared `git diff inp...HEAD` and `git diff 676057fd..HEAD -- KAM docs`. The latter contains unrelated W3/planetary/graph changes inherited through the branch history; those are outside this audit. The W7 repair commits are `14e9aed4` (F1), `ae55fbef` (F2.1), `406109f0` (F2.2), and `54279e66` (handoff/docstring). Reviewed only `Shells.lean`, the unchanged direct consumer `ShellEst.lean`, new `CoordsInverse.lean` and `ZetaExact.lean`, the comment-only changes in `Coords.lean`, their generated imports, and the corresponding blueprint passages (`freqcoords`, `count` (iii), `ext-zeta`, `shells`, `shell-geom` (ii), `shell-est`). Unchanged round-1 PASS results are carried forward, not re-audited. No agents were delegated.

No provider or frozen anchor is submitted for sealing. Provider/frozen-type and seal-body probes are inapplicable. The only repository source edit by this audit is this report; the temporary axiom probe was removed.

## F1: exact inner shell and consumers — PASS

`Shells.lean:45` defines membership as `I ∈ shellSet q t0 k ∧ a < Metric.infDist I (shellSet q t0 k)ᶜ`. The ordinary Pi metric on `Fin 2 → ℝ` is the sup metric, so this is exactly the blueprint's distance-to-complement definition of `U_{-a} R_k`. There is no pointwise strict-margin surrogate. The complement is nonempty (it contains zero), including outside the standing positive shell parameters, so the new uniform-margin equivalence does not exploit an empty-set distance convention.

For round 1's point `(5/16,5/16)` with `q=t0=1/2`, `k=0`, `a=1/16`, the infimum distance to the removed square is `1/16`, approached from inside that square; the corrected strict inequality excludes the point. This follows directly from the reviewed definition; no new counterexample probe was required.

`volume_shell_diff_inner_le` retains exactly its old binders and conclusion `volume (R_k \ U_{-a} R_k) ≤ ofReal (7*a*t_k)`. Its new proof obtains a nearest point in the closed set `C = ((0,t_k)²)ᶜ ∪ [0,t_{k+1}]²`, which contains `R_kᶜ`. Thus `infDist I C ≤ infDist I R_kᶜ ≤ a`. Attainment is used only for this closed set, not the nonclosed complement. The resulting covering uses the outer layer `(0,t)² \ (a,t-a)²` and the inner layer `(0,s+a]² \ (0,s)²`. The closed upper endpoint includes the formerly missed equality boundary. Their bounds remain `4at` and `3at`, using `a≤t` and `s≤t`; no regularity or attainment premise was introduced.

`git diff 676057fd..HEAD -- KAM/Wave/Measure/ShellEst.lean` is empty. Its existing proof rebuilds against the corrected definition and boundary theorem; `hinner` now literally asks for the source inclusion `U_{-α_k} R_k ⊆ Π_k`. Neither `Π_k` nor `Γ` is enlarged, no premise is added, and the exported bound retains `(7+C₇) α_k^(32/47) / ((1-q²)t_k)`. The earlier round-1 assessment of the shell-estimate conclusion and setup bundling is unchanged. `rg -n shellInner KAM` finds only `Shells.lean` and `ShellEst.lean`; these cover all direct consumers.

## Declaration verdicts

All names below have namespace `KAM.Wave`. Each row is PASS in this delta.

| Node | Declaration | Verdict and reason |
|---|---|---|
| shells | `shellInner` | PASS: literal sup-metric infimum distance to the complement. |
| shells | `mem_shellInner_iff` | PASS: some common `b>a` bounds every complement distance from below; complement nonemptiness proved internally. |
| shell-geom (ii) | `volume_shell_diff_inner_le` | PASS: same assumptions and constant 7, corrected boundary covering. |
| shell-est | `shell_defect_le` | PASS: same text and proof rebuild under the corrected set; no extra premise or weaker result. |
| freqcoords (i) | `measBvec` | PASS: `b_i = λ_i⁻¹`. |
| freqcoords (i) | `measAinvMat` | PASS: all four entries of the displayed `(8π/21)` inverse matrix. |
| freqcoords (i) | `actionAMat_mul_measAinvMat` | PASS: actual right inverse, only mass and positivity parameters. |
| freqcoords (i) | `measAinvMat_mul_actionAMat` | PASS: actual left inverse. |
| freqcoords (i) | `actionAMat_inv` | PASS: matrix inverse equals the displayed matrix. |
| freqcoords (i) | `abs_det_actionAMat` | PASS: absolute determinant equals `measDA`. |
| freqcoords (i) | `actionAMat_inv_mulVec_measBvec` | PASS: exact vector identity `A⁻¹b=(8π/21)λ_J`. |
| freqcoords (ii) | `actionAMat_linfty_opNorm` | PASS: equality with `measNA`, not an upper bound. |
| freqcoords (ii) | `actionAMat_inv_linfty_opNorm` | PASS: equality with `measLA`, not an upper bound. |
| freqcoords (iii) | `omegaTanInv` | PASS: `ζ ↦ A⁻¹(ζ-λ_J)` on all of `ℝ²`. |
| freqcoords (iii) | `measAlin_eq_mulVec` | PASS: identifies the existing linear map with the actual matrix action. |
| freqcoords (iii) | `omegaTan_omegaTanInv` | PASS: right inverse for every frequency vector. |
| freqcoords (iii) | `omegaTanInv_omegaTan` | PASS: left inverse for every action vector. |
| freqcoords (iii) | `omegaTan_bijective` | PASS: global bijectivity, no image-membership premise. |
| freqcoords (iii) | `omegaTanEquiv` | PASS: forward map and displayed inverse with both inverse laws proved. |
| freqcoords (iii) | `omegaTan_eq_add_mulVec` | PASS: exported affine formula with linear part A. |
| ext-zeta | `encard_l1Sphere_eq` | PASS: exact `4*N` for every natural `N≥1`. |
| count (iii), ext-zeta | `tsum_lattice_inv_cube_ennreal` | PASS: exact nonnegative lattice sum in ENNReal. |
| count (iii), ext-zeta | `hasSum_lattice_inv_cube` | PASS: real summability and exact value `measZ3`, not a potentially nonsummable `tsum` convention. |
| count (iii), ext-zeta | `measZ3_lt_seven` | PASS: strict numerical inequality. |
| count (iii), ext-zeta | `tsum_lattice_inv_cube` | PASS: real sum equality and strict bound jointly exported. |

The two norm declarations elaborate under section-local `Matrix.Norms.Operator`; their proofs explicitly unfold `Matrix.linfty_opNorm_def` to the maximum absolute row sum. Mathlib's `linfty_opNorm_eq_opNorm` identifies this with the operator norm on Pi spaces. This is the blueprint's induced sup norm. The larger rows are respectively row 0 for A and row 1 for A⁻¹; the mass-dependent quantities are exactly the previously accepted `measNA` and `measLA`. No constant gains an extra dependence.

The exact-count proof supplies four disjoint injective quadrant families with N points each, then combines their lower bound with the accepted upper bound. The sum proof partitions the entire integer lattice by the natural ℓ¹ radius, removes the zero fibre explicitly, and uses the exact count to obtain `4/N²`. `hasSum_zeta_two` gives `4*(π²/6)=2π²/3=measZ3`. `kAbs` is the ℓ¹ norm of the Fourier index, as in the blueprint. Encoding the omitted zero term as `if k=0 then 0 else ...` is faithful. Nonnegativity and finiteness are established before returning to real `HasSum`.

## Definitions and documentation

The changed definition `shellInner` and four new definitions `measBvec`, `measAinvMat`, `omegaTanInv`, `omegaTanEquiv` are the intended objects on their entire carriers; no junk fallback, conclusion-shaped hypothesis, or assumed inverse law occurs. New bodies are exposed by the modules' `@[expose] public noncomputable section`. `ZetaExact` introduces no top-level definition. Local proof sets/functions are auxiliary constructions, not replacement public objects.

`Coords.lean` changes only documentation: `measS` is now correctly described as a signed pairing and `omegaTan_sub` as the subtraction identity; the inverse/norm documentation points to `CoordsInverse`. The two new modules are publicly imported by the generated Wave root at the tip. The handoff accurately warns that the intermediate F2.1 commit references `ZetaExact` before its next-commit addition; acceptance here is for the audited tip.

## Checks

All Lean/Lake invocations were serial and memory capped. The exact command prefix is:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

1. Targeted builds:

   ```sh
   /root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpl KAM.Wave.Measure.CoordsInverse KAM.Wave.Measure.ZetaExact KAM.Wave.Measure.ShellEst
   ```

   The driver invokes each `lake build <Module>` with the exact prefix above while holding a compile-gate slot. Exit 0. Outputs in order: `Build completed successfully (2845 jobs).`, `Build completed successfully (3179 jobs).`, `Build completed successfully (3199 jobs).` No warnings or errors. ShellEst's build checks the corrected Shells dependency and the direct consumer.

2. Axiom probe `.lake/abi-scratch/W7Audit2.lean`: imports `CoordsInverse`, `ZetaExact`, `ShellEst`; runs `#print axioms` for all 17 new public theorems in the two new modules and for `mem_shellInner_iff`, `volume_shell_diff_inner_le`, `shell_defect_le` (20 total). Exact invocation: the prefix above followed by `lake env lean .lake/abi-scratch/W7Audit2.lean`. Exit 0. Every line reports exactly `[propext, Classical.choice, Quot.sound]`. The declaration table enumerates all checked theorems. Probe removed afterwards.

3. Lint: the prefix above followed by `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpl`. Exit **0**. Output:

   ```text
   check_lean_modules: PASS (3753 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

   No direct invocation of `scripts/lint_sources.sh` was made. The stated file-hash-only application exception is preserved; no application build was requested.

4. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. The generated `KAM/Root/Wave.lean` is the previously disclosed exception (28 added package imports against inp); its repair adds the two intended imports. No generated files were edited by this auditor.

5. `git diff --check 676057fd..HEAD -- KAM/Wave/Measure docs/tracks/W/audits/W7-MEASURE-handoff.md`: exit 0, no output. Forbidden-token/option scan of the new proof modules and repaired Shells: no matches. Current lengths: Coords 327, CoordsInverse 214, Shells 257, ZetaExact 187 lines; all below 1500. The new files have copyright, `module`, public imports, module docstrings and public sections.

6. Kernel replay and short-name checks were already run by the launcher according to the owner. They were not rerun, and unseen launcher outputs are not represented here as independently observed exit codes. This audit's fresh build and axiom results are recorded above.

## Completion, uncertainties and errata

F1 and F2 no longer obstruct the handoff's completion claim. Read with round 1's unchanged PASS material, all previously identified missing package conclusions are now exported, and the shell consumers use the exact blueprint set. No new source/blueprint defect or introduced deviation was found in the reviewed delta. No frozen statement issue was encountered. The minor handoff line references and ZetaExact line count are approximate (current file: 187 lines); they do not affect coverage.

This verdict does not re-audit other package labels, other track changes in the revision range, or the full W-NLW2 assembly. The handoff still correctly identifies W6/W8 obligations; W7 supplies the measure infrastructure and implications, not the final existential theorem. There are no remaining uncertainties about F1/F2 within this scope.
