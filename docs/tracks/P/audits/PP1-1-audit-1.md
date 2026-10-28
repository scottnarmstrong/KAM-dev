# PP1-1 independent package audit 1

**Overall verdict: FAIL (hygiene only; mathematics and signatures PASS).** The PP1-1 implementation of `bpP:p1:conv#data` (linear-field portion) and `bpP:p1:omega-algebra` is mathematically sound and matches the design signatures. The source lint rejects two overlong comment lines in the audited module, beyond the explicitly permitted stale-root diagnostic. These require only comment wrapping; no proof defect was found. Other notes concern an unused signature premise and the inherited comparison diff. **Frozen-anchor verdict: not applicable:** this package has no provider export, frozen theorem implementation, or seal body. No I/N/P headline or root is certified by this audit.

Audited worktree: `/root/code/KAM-inp-pp11`; HEAD `6123a91103f32aee4fe1b9d96f4c84c33868a482`; observed `inp` `90cb224ec5c0651eb8ad9009c11dae256607bb02`. Scope is exclusively `KAM/Planetary/Hamiltonian/Algebra.lean` (197 lines), as required by the handoff's AUDIT FOCUS. Read AGENTS.md, PLAN, DECISIONS, the independent-package brief, handoff, Part 1 design and its design audit, Part 1 blueprint, track-P statement conventions, and the three imported frozen definition files. No delegation or prover coordination.

## Findings and comparison scope

0. **H1, blocking hygiene — independent lint does not pass.** `Algebra.lean:18` has 105 Unicode characters; `Algebra.lean:95` has 101. `scripts/lint_sources.sh` explicitly rejects both. The generic brief exempts only the stale `KAM.lean` diagnostic. The handoff's assertion that lint passes (and its description of a lone byte-count issue) is inaccurate: these are two character-count failures. No mathematical change is required. Replace line 18 by:

```text
symplectic linear maps (bijectivity, `|det A| = |c|^d`, `A X_{ℓ∘A} = c X_ℓ`).
Matrices are avoided in the
```

Replace the complete one-line docstring at line 95 by:

```lean
/-- (a) last clause: `Ω(w, X_H z) = DH(z) w` for every `z`
(both sides `0` off differentiability). -/
```

These replacements leave all signatures and proofs unchanged. They are proposed here only; the audit restriction permits no implementation edit. Rerun lint after wrapping; root regeneration remains the orchestrator's task.

1. **N1, informational — unused premise, no repair required.** `Algebra.lean:144` retains `hc : c ≠ 0` in `abs_det_of_symplectic`, exactly as designed (`PART1-LEAN-DESIGN.md:422`). The determinant proof does not need it. This is the blueprint's own premise, not an added restriction. Keep the signature; the build warning is harmless.
2. **N2, comparison provenance — prescribed global clean-diff check is not literally empty.** `git diff inp...HEAD` warns `multiple merge bases, using 2e0825e206cf3230e980da464c07603862236f3c`. `git merge-base --all inp HEAD` returns that commit and `bf7fcdaded519d41be200d90518ed4c2c7cbbde3`. The selected-base diff contains 29 files, including 11 inherited added imports in generated `KAM.lean`. The PP1-1 commit itself (`git diff HEAD^ HEAD --name-only`) adds only `KAM/Planetary/Hamiltonian/Algebra.lean`; its protected-path diff is empty. The requested triple-dot diff for `KAM/Frozen`, `manifest`, and `README.md` is empty. Thus the full triple-dot protected-path condition fails for inherited `KAM.lean` changes, while PP1-1 introduces none. These inherited files were not audited or edited.

## Declaration and node verdicts

All names below are in `KAM.Planetary`; locators refer to `KAM/Planetary/Hamiltonian/Algebra.lean`. Every public theorem's full header, including explicit/implicit binders, was checked byte-for-byte against design Appendix A and independently elaborated as an example applying the implementation theorem.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p1:conv#data`, linear-field portion | `linearField` (35) | PASS | Exact coordinate formula on all `Phase d`, including `d = 0`; no fallback. Other conv data belong to later packages. |
| `bpP:p1:conv#data`, field bridge | `hamiltonianVectorField_eq_linearField` (39) | PASS | Literal frozen field, definitional equality; no differentiability premise. |
| `bpP:p1:omega-algebra` (a) | `symplecticForm_antisymm` (43) | PASS | Exact frozen-sign antisymmetry. |
| (a), nondegeneracy | `eq_zero_of_symplecticForm_right` (49) | PASS | Tests both coordinate-vector families; full carrier. First-slot nondegeneracy follows by antisymmetry. |
| (a), field identity | `symplecticForm_linearField` (73) | PASS | Coordinate expansion gives `Ω(w,Xℓ)=ℓ w` with the correct sign. |
| (a), uniqueness | `eq_linearField_iff` (85) | PASS | Exact iff; subtraction plus nondegeneracy, no uniqueness assumed. |
| (a), total Hamiltonian identity | `symplecticForm_hamiltonianVectorField` (96) | PASS | Arbitrary total H and every z; fderiv totality retained. |
| (b), invertibility | `bijective_of_symplectic` (101) | PASS | `c ≠ 0` and conformality are precisely source premises; finite-dimensional surjectivity follows from injectivity. |
| (b), determinant | `abs_det_of_symplectic` (144) | PASS WITH NOTES N1 | Product-basis Gram determinant, nonzero Gram determinant cancellation, exponent `2*d`, then absolute values. |
| (b), field transport | `apply_linearField_comp_of_symplectic` (178) | PASS | Correct `A X_(ℓ∘A) = c • Xℓ`; equivalent to inverse formula using the proved bijectivity. |
| (c), sign independence | `symplectic_neg_iff` (188) | PASS | Both slots' form changes sign, scalar c unchanged; no restriction on c. |
| `stepP:p1:oa-mat`, expansion helper | private `apply_eq_sum` (58) | PASS | Linear expansion in position/momentum coordinate vectors. |
| (a), subtraction helper | private `symplecticForm_sub_right` (79) | PASS | Exact bilinearity consequence; no extra premise. |
| (b), representation | private `omegaForm` (117) | PASS | Frozen Ω packaged as a real bilinear form. |
| (b), representation bridge | private `omegaForm_apply` (134) | PASS | Definitional equality to Ω. |
| (b), Gram nonsingularity | private `omegaForm_nondegenerate` (136) | PASS | Both slots proved nondegenerate from the coordinate argument. |
| (b), scalar helper | private `linearField_smul` (173) | PASS | Coordinate scalar compatibility. |
| `stepP:p1:oa-b` | Internal proofs of the three (b) theorems | PASS | Determinant and uniqueness route implements the blueprint argument without adding an inverse definition. |
| Module hygiene | `Algebra.lean:18,95` | FAIL H1 | Two comment lines exceed the enforced 100-character limit; exact replacements above. |

## Definitions, hypotheses, and proof fidelity

There are exactly two new definitions: public `linearField` and private `omegaForm`; no new abbrev, structure, or instance. Both are the intended objects on their entire carriers. `linearField` is the supplied coordinate formula, and `omegaForm` adds linearity proofs to exactly the frozen `symplecticForm`. Neither contains an off-domain branch, junk value, analytic assumption, or encoded result.

The only nontrivial hypotheses are a linear functional, a continuous linear endomorphism, `c ≠ 0` where specified, and the source conformal-symplectic equation. `eq_zero_of_symplecticForm_right` and `eq_linearField_iff` characterize nondegeneracy/uniqueness and prove their consequences; they do not assume any later chart, torus, or KAM result. No constants or norm dependences are widened. The max-norm carrier remains `(Fin d → ℝ) × (Fin d → ℝ)`. Every finite-dimensional linear functional is continuous, so continuous linear forms do not narrow the finite-dimensional mathematical statement.

The determinant proof uses `Module.Basis.prod` and the design's permitted bilinear-form route, addressing the design audit's N2. It derives `det(A)^2 = (c^d)^2` by canceling the nonzero Gram determinant, without requiring a Euclidean inner product or computing that determinant as 1. Surjectivity and uniqueness then give the inverse-free field formula with exactly one factor c. Dimension zero and negative nonzero c remain admitted by the signatures and the proofs.

The module imports only Mathlib and frozen **definitions** (`SymplecticForm`, `HamiltonianVectorField`, `Phase`, with definition-only project dependencies). No provider or DRAFT_SORRY theorem is imported. Consequently provider/frozen-type probes, seal-body probes, and imported frozen-theorem SEALED-state checks have no target here. The ten design-signature application probes replace the inapplicable provider probes.

The design expressly replaces the blueprint's matrix presentation by bilinear statements (`PART1-LEAN-DESIGN.md:170–173`). No declaration of `M₀² = -1` or matrix sign equivalence is added. The actual proof uses coordinate evaluation and nondegeneracy instead of a named matrix-square fact; this is the permitted proof route, not a claim to have formalized the literal matrix statements separately.

## Independent checks

All Lean/build/checker commands were sequential with `LEAN_NUM_THREADS=1` and `nice -n 5`. The targeted build used the mandated compile gate. No other worker's processes were altered, no heartbeat/recursion/synthesis budget was changed, and no clean, update, cache-get, full-library build, or package-tree edit was performed.

1. **Targeted build**:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pp11 KAM.Planetary.Hamiltonian.Algebra
```

Exit **0**. Output (warning hint omitted):

```text
[inp-gate] slot 1 acquired 05:17:21 for KAM.Planetary.Hamiltonian.Algebra
⚠ [9051/9051] Replayed KAM.Planetary.Hamiltonian.Algebra
warning: KAM/Planetary/Hamiltonian/Algebra.lean:144:39: Variable name `hc` is not explicitly referenced.
Build completed successfully (9051 jobs).
```

This is a targeted module build with dependency-trace replay, not a clean rebuild.

2. **Exact signatures, totality, and axioms**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PP11Audit.lean
```

Exit **0**. The scratch file copied all ten theorem headers from design Appendix A as examples, filled them by explicit application of the implementation exports, checked the `linearField` definition by `rfl`, and proved `hamiltonianVectorField H z = 0` from `¬ DifferentiableAt ℝ H z` using `fderiv_zero_of_not_differentiableAt`. All checks elaborated without errors or warnings. Exact axiom-query output:

```text
'KAM.Planetary.hamiltonianVectorField_eq_linearField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.symplecticForm_antisymm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eq_zero_of_symplecticForm_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.symplecticForm_linearField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eq_linearField_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.symplecticForm_hamiltonianVectorField' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.bijective_of_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.abs_det_of_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.apply_linearField_comp_of_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.symplectic_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

A separate Python comparison printed `PASS: all 10 public theorem headers byte-identical to design Appendix A.` A scan of the complete module printed `PASS: no forbidden proof escape, resource option, or EuclideanSpace in the audited module.`

3. **Kernel replay**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Algebra
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.Hamiltonian.Algebra
```

This single invocation covers the package's sole module, including its private helper proofs. There is no provider module or separate lemma module in PP1-1.

4. **Repository lint**:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**. Complete output:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-pp11/KAM/Planetary/Hamiltonian/Algebra.lean:18:105
/root/code/KAM-inp-pp11/KAM/Planetary/Hamiltonian/Algebra.lean:95:101
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (413 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module-format, frozen-anchor and ABI checks pass. The stale generated-root message is the brief's allowed exception; the two additional comment-length failures are H1 and prevent a package hygiene PASS.

5. **Module hygiene and edit scope:** 197 lines; copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section` present. The section exposes definitions. No forbidden proof escapes or resource options; no new global instance. `git diff --check` and final scratch cleanup/status checks: **PASS** (exit 0); all three audit-created scratch files were deleted, and final status contains only this new report and the pre-existing untracked handoff.

## Suspected errata, deviations, and limits

No new suspected pinned-source or blueprint mathematical defect was established. The coordinate-free presentation and inverse-free field formula are explicit design departures, faithfully implemented. The design prose saying `M₀² = -1` is “internal to the uniqueness proof” describes the mathematical motivation; the implementation proves uniqueness directly from coordinate nondegeneracy. No matrix-square declaration or additional frozen result is certified.

There is no frozen statement defect to report and no source PDF correction inferred from compilation. No fresh external-source lookup was required for these elementary algebra identities: fidelity was checked against the supplied blueprint and design. The original track statement document retains historical draft-status language; current frozen definitions and owner decisions control the actual objects audited here.

Only this report is an audit-created repository artifact; the pre-existing untracked handoff is preserved. No implementation, frozen definition, manifest, generated root/README, design, blueprint, or original signature file was edited. No commit was made. Report destination follows the user's explicit worktree override of the generic brief's main-worktree destination.
