# P11A-P9 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the authorized raw-data helper package. `KAM.Planetary.forward_tube_core` passes statement and proof review. The signed `forward_tube` and `p11PhysicalDelta` remain deferred to P11A-P1 under the explicit orchestrator ruling in the handoff. No frozen anchor is supplied or sealed by P11A-P9; “seal-ready” is not applicable.

## Scope and authority

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11ap9`. Audited HEAD: `c7d9bd3fd8da985217767bf669e629394ce15b0d`; comparison ref `inp` at initial inspection: `442f6c97a2a78e359368bb82314e4160d8f4ae90`.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the worktree handoff and its AUDIT FOCUS, track-P statement/conventions, P11A design row P9 and physical/forward-tube signatures, design audits 1–3, blueprint P11 lines 230–234 and its P12 proof at lines 32–42, and the imported chart/circular definitions and supporting theorems. The user explicitly overrides the generic brief's main-worktree report destination: this report is in the package worktree at the exact requested absolute path.

Only `KAM/Planetary/Preparation/ForwardTube.lean` is audited as production code. `git diff inp...HEAD` has nine paths: this module plus eight inherited integration changes. `git diff --name-only 7634a3de..HEAD` contains only this module, isolating package commits `cee69ff0` and `c7d9bd3f`. The extra eight paths are outside the explicit AUDIT FOCUS and receive no verdict here. The actual module is 224 lines; its SHA-256 is `bfc4bd9e3a9eace765747dc3455db57686d30525acf1056896c33022f7851b0e`.

The local `.drafts/design/P11ASignatures.lean` is absent. Read the supplied canonical copy at `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA-256 `ffc0ddcad44661d4eeffd7d5bf0900e393ae23a3217c2dfc6edcabb89245fc15`. Its physical-data/forward-tube block (lines 566–593) agrees byte-for-byte with the corresponding embedded block in this worktree's design (lines 1507–1534). Earlier design-audit hashes are historical snapshots, not substituted for the current file.

## Declaration ledger

Names below are in `KAM.Planetary`; private names are source names, not public exports.

| Node / obligation | Declaration / location | Verdict | Reason |
|---|---|---|---|
| Angle reduction, cosine | private `ft_cos_fract`, line 40 | PASS | Integer shifts by `2π` preserve cosine, for every real input. |
| Angle reduction, sine | private `ft_sin_fract`, line 45 | PASS | Same identity for sine. |
| Circular reference periodicity | private `ft_circularPoint_fract`, line 50 | PASS | Literal frozen circular-point formula, componentwise; no positivity needed for angle periodicity. |
| Continuous circular reference | private `ft_continuous_circularPoint`, line 54 | PASS | Trigonometric functions with constant coefficients, including on the total carrier. |
| Compact torus parametrization | private `ft_continuous_assemble`, line 65 | PASS | Literal fast-first assembly, zero secular coordinates. |
| Uniform positive action bound | private `ft_exists_lower`, line 75 | PASS | Positive finite reciprocal-sum lower bound; valid also at `n = 0`. |
| `bpP:p11:forward-tube` | `forward_tube_core`, lines 89–218 | PASS | Exactly the signed conclusion after field substitution; weaker dimension/order premises, correct max norm and periods. |
| Signed physical wrapper | `forward_tube`, design lines 1524–1532 | PASS WITH NOTES | Not present in production, as explicitly authorized. Exact fresh declaration with the one-line core application elaborates. |
| Chosen physical radius | `p11PhysicalDelta`, design lines 1533–1534 | PASS WITH NOTES | Not present in production, as authorized. Witness selection is immediate once P1 supplies `p11_zeta_pos`; its positivity proof is not delivered by P9. |

There is one new public theorem and no new public `def`, `abbrev`, `structure`, instance, or notation. Searches across `KAM/**/*.lean` find no other declaration of `forward_tube_core`; the six `ft_*` helpers are private and occur only in this file.

## Statement fidelity and deferred wrapper

The exact signed `P11Physical` fields are `G`, `m0`, `m`, `a`, `eta`, `n_ge`, `G_pos`, `m0_pos`, `m_pos`, `a_pos`, `ordered`, `eta_pos`. Every core premise is supplied by `D.G_pos`, `D.m0_pos`, `D.m_pos`, `D.a_pos`, and the already-signed arbitrary positive `zeta` argument. There is no extra regularity, ordering, separation, compactness, or conclusion-shaped input. The core does not require `n ≥ 2`, axis ordering, or `eta > 0`, so it is strictly more general than the physical-data statement.

The scratch probe copied the physical structure (expanding only `P11Vec n` to `Fin n → ℝ`), `p11Zeta`, and the signed `forward_tube` declaration, replacing its draft body by:

```lean
forward_tube_core D.G_pos D.m0_pos D.m_pos D.a_pos hzeta
```

This elaborates against the full signed conclusion without `simpa`, casts, extra premises, or weakening. The existential precedes `w`; the chosen radius therefore depends only on the fixed physical inputs and `zeta`. The bound `delta ≤ D.m i * sqrt (D.G * D.m0 * D.a i) / 4`, both non-strict input inequalities, product-domain membership, and strict output norm bound are all preserved literally. The norm is the standard product/Pi max norm, matching blueprint P11/P12 and the frozen physical phase convention. Physical fast angles are `2π`-periodic; the circular reference uses period-one angles `lambda/(2π)`.

For witness selection the probe checked `(forward_tube D hzeta).choose`, positivity from `.choose_spec.1`, and the same expression at `zeta = p11Zeta D` when supplied its positive proof. This checks the intended `p11PhysicalDelta` body but does **not** prove `p11_zeta_pos`; that remains P1's independent responsibility. There is no provider export or frozen theorem in this package, so provider/frozen-type and literal seal-body probes are inapplicable. The signed-wrapper probe is the relevant replacement gate under the handoff ruling.

Blueprint P11's final “in particular” tube membership follows directly from the norm conclusion using the displayed circular angle as witness in frozen `circularTube`. Its omission as a separate conjunct matches the signed declaration and loses no mathematical content.

## Proof and definition audit

1. Lines 99–107 construct the actual circular torus in chart space as the continuous image of the compact cube `[0,1]^n`. This cube parametrizes all residues, including its harmless duplicated endpoints.
2. Lines 108–135 use analyticity of the literal product Poincare chart only on its domain. Subtracting the continuous circular reference gives an open good set. Every circular torus point lies in the domain, and `circularPoint_eq_poincareProd` makes the difference zero there.
3. Lines 136–146 obtain a positive closed-thickening radius `r` around that compact set. A positive common action bound `c ≤ Λ*_i/4` exists, and `delta = min c (min r (r^2/2))` is positive. The proof uses closed distance `≤ r` with a closed thickening contained in an open strict-error set; no strict/non-strict boundary error occurs.
4. Lines 147–164 prove domain membership directly: `Λ_i ≥ Λ*_i - delta ≥ 3Λ*_i/4 > 0`, whereas `Γ_i ≤ delta ≤ Λ*_i/4 < Λ_i`. There is no use of chart values outside its valid domain to establish the theorem.
5. Lines 166–186 shift by `k_i = -floor(lambda_i/(2π))`. `poincareProd_lattice` applies using the domain membership already proved. Both chart and reference are invariant, and the shifted fast angle is exactly `2π * fract(lambda_i/(2π))`.
6. Lines 187–218 compare the shifted point with the circular point at those same residues. The fast-angle difference is zero, action difference is at most `delta ≤ r`, and `Γ_i = (ξ_i²+η_i²)/2 ≤ delta ≤ r²/2` bounds each secular coordinate by `r`. The product/Pi max norm therefore gives distance at most `r`, yielding the strict output bound after undoing the shift.

Definition classification: no new module-level definitions, abbreviations, or structures. Local `Λ₀` is the intended circular action; `K` is the actual compact circular chart torus; `f` is the literal chart error; `delta` is the positive minimum above; `k` is the integer residue shift; `z` is the circular comparison point at the reduced angles. None is a fallback, surrogate object, arbitrary selector, or junk-value construction. The private reciprocal formula is well-defined under positive inputs and gives a valid lower bound even for the empty index type.

## Mechanical checks

All Lean/Lake invocations were serialized in this audit with `LEAN_NUM_THREADS=1` and `nice -n 5`. Builds used the prescribed compile gate; no clean, update, cache fetch, full-library target, or resource-budget override was used. Lint's ABI subprocess inherited both the one-thread environment and nice priority.

### Targeted build

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap9 KAM.Planetary.Preparation.ForwardTube
```

Exit **0**. Output included:

```text
[inp-gate] slot 1 acquired 15:22:43 for KAM.Planetary.Preparation.ForwardTube
Build completed successfully (9112 jobs).
```

The job count includes existing dependency replay. Replayed unused-variable warnings were at `KAM/Kepler/Energy.lean:106`, `KAM/Planetary/Poincare/Chart.lean:212,247`, and `KAM/Kepler/Mass.lean:147,157,500,524`. No warning or error was emitted for the audited module.

### Signed-wrapper and axiom probe

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP9Audit.lean
```

Exit **0** on the corrected probe, with exact output:

```text
'KAM.Planetary.forward_tube_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'P11AP9Audit.forward_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first scratch-only attempt omitted the surrounding `noncomputable section` needed by the copied `p11Zeta` definition and exited 1 with `lean.dependsOnNoncomputable` at probe line 17. Adding that section, as in the original signature file, corrected the probe setup; production code was untouched. No draft `sorry` theorem or assumed `p11_zeta_pos` was imported into the probe.

### Kernel replay

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.ForwardTube
```

Exit **0**; exact output:

```text
replaying KAM.Planetary.Preparation.ForwardTube
```

This single invocation covers the sole new lemma module, including its private proof helpers. There is no separate provider module.

### Source lint

```sh
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated root. Exact complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (650 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other lint checks passed. `KAM.lean` was left untouched, as required.

### Other hygiene

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty output, exit 0.
- `git diff --check inp...HEAD`: empty output, exit 0.
- All 224 lines satisfy the 1500-line module cap. Copyright/authors, `module`, public imports, module docstring, and public section are present.
- No forbidden proof escapes, resource overrides, or `EuclideanSpace` occur in the module.
- Static traversal follows 66 project modules including the audited module. All 49 frozen anchors reached are definitions with manifest state `SEALED`; there are no frozen theorem imports, `DRAFT_SORRY` imports, or provider imports.
- Only the exact requested report persists from this audit; the audit probe/logs under `.lake/abi-scratch/` were removed after validation. No state-changing git command was run.

## Notes, uncertainties, and errata

No material statement defect, proof defect, pinned-source erratum, or new deviation was found in the scoped module. The compact-torus/open-neighbourhood proof is a valid alternative to the blueprint's compact-box/uniform-continuity proof. No external source research was needed: the blueprint explicitly identifies this forward-tube argument as ours.

The handoff's build target `KAM.Preparation.ForwardTube` and original file location are historical; the actual design-path target `KAM.Planetary.Preparation.ForwardTube` was independently built and replayed. The authorized wrapper deferral is retained explicitly: P1 must still define the physical package and `p11Zeta`, prove `p11_zeta_pos`, export the exact signed `forward_tube`, and choose `p11PhysicalDelta`. Acceptance of this core proves none of the downstream preparation, transport, measure, P-FIXED, or other frozen headlines.
