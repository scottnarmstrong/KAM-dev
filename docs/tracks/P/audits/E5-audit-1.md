# E5 independent package audit 1

Overall verdict: **PASS WITH NOTES**. E5 is complete for its assigned scope. The three required wrappers and all four supporting theorems pass statement and proof review. The only hygiene exception is the generated root being out of date, explicitly permitted by the audit brief. No frozen anchor is proved or sealed by this infrastructure package.

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p14-e5`.
Compared `git diff inp...HEAD`, with HEAD `8248376b1647f137f39f2584445d17a6cd6ba4b5` and `inp` `442f6c97a2a78e359368bb82314e4160d8f4ae90`.
The entire committed delta is the 145-line addition `KAM/Planetary/Exponential/LocalComplexification.lean`, SHA-256 `40b9af9229b6f5d2d9cf7f6cfc49f9b70faaeffb6aa02fea4818289275dd698b`.
The pre-existing untracked `docs/tracks/P/audits/E5-handoff.md` was read and preserved.

Read the package brief, AGENTS.md, PLAN, DECISIONS, track P statement, P14 design row E5 and Appendix A, both P14 design audits, relevant blueprint nodes, frozen Phase and complexifyPhase definitions, and the reused local complexification/restriction interfaces. The original signature file was read from `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` because it is absent in this worktree; its SHA-256 is `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7`. Both design audit reports are under `docs/tracks/P/design/`, rather than the handoff's `audits/` locator. The user's exact worktree report destination overrides the generic brief's main-worktree destination.

## Declaration ledger

All declaration names below have prefix `KAM.Planetary`. Line numbers refer to the audited Lean file.

| Node / obligation | Declaration | Verdict | Evidence |
|---|---|---|---|
| p7:ho-hol; local derivative restriction (L35–51) | `local_complex_restriction` | PASS | Exact signature. Restricts the complex derivative to real scalars, composes with the literal phase inclusion and `Complex.reCLM`, then uses uniqueness of the real derivative. No strip or reality premise added. |
| p14:x-hol, quotient component; F5 (L53–61) | `complex_division` | PASS | Exact signature on an arbitrary complex product-domain subset. Inverse and multiplication consume exactly differentiability and nonvanishing on that subset. No openness premise added. |
| E5 packing support (L64–75) | `e5Pack` | PASS | Literal continuous linear coordinate concatenation; see definition classification. |
| E5 packing support (L77–78) | `e5Pack_apply` | PASS | Definitional equation exposing `Fin.append`; generic RCLike scalar field. |
| E5 packing support (L81–86) | `e5Unpack` | PASS | Literal continuous linear coordinate projections; see definition classification. |
| E5 packing support (L88–94) | `e5Unpack_pack` | PASS | Left inverse on every input, by both coordinate blocks. No dimension positivity premise. |
| E5 max-norm transport (L96–110) | `norm_e5Pack` | PASS | Exact norm equality on the whole carrier. Proves forward bound coordinatewise and reverse bound using the unpacking operator norm ≤ 1. |
| E5 inclusion transport (L112–117) | `e5Pack_complexify` | PASS | Coordinatewise equality of frozen inclusion and existing realInclusion after packing. |
| p14:x-cx; tb-local supplier (L119–143) | `local_analytic_complexification` | PASS | Exact signature. Analyticity of f composed with unpacking feeds P5-CL `local_real_complexification`; packing transports the complex ball and the real trace with the same returned positive radius. |

The supporting declarations are elementary coordinate identities, rather than replacements for blueprint results; their generic RCLike formulation is a harmless generalization. Every theorem hypothesis is analytic/typing data from the intended statement. No conclusion-shaped hypothesis, instance or bundled hard step is introduced.

## Completeness and fidelity

P14 design L378 assigns precisely `complex_division`, `local_complex_restriction`, and `local_analytic_complexification` to E5. The assignments omitted from this package are confirmed separately: `real_trace_identity` to E6 (L379), `secular_parametric_integral` to S4 (L390), `angle_quadrature` to S9 (L395), and `interval_constancy` to A5 (L371). Their absence is not an E5 defect.

For each of the three assigned exports, the full declaration header up to `:=` is byte-identical to both the original signature file and Appendix A. An independent scratch probe copied each complete signature under a fresh name and discharged it with the delivered export, passing all explicit binders in order: `hf v`, `hf`, and `hf hg hg0`, respectively. This tests the actual elaborated consumer application, without importing admitted signatures. There is no frozen target/provider pair here; frozen-type equality and seal-body probes are consequently inapplicable. The per-anchor verdict is **not applicable: no anchor claimed**.

The phase carrier is literally `(Fin d → ℝ) × (Fin d → ℝ)` and its complex analogue. Their product/Pi norms are max norms, so the metric balls are the blueprint's polydiscs, including d=0. The radius is existential after f,x and the analytic premise, exactly as in p14:x-cx. No constant-dependence, norm or quantifier change occurs. The quotient wrapper supplies only the assigned quotient portion of p14:x-hol; existing calculus supplies its other clauses.

At L128 the proof calls the existing P5-CL `KAM.Planetary.local_real_complexification` from `KAM/Planetary/PGAssembly/ComplexLocal.lean`. This is an ordinary proved theorem constructing a complexified power series and a positive local radius, not an assumed extension or a duplicated proof. Its optional boundedness witness is unused because E5's signature does not require a bound. Restriction at L40–51 correctly differentiates the real part through `restrictScalars ℝ`; it does not assert that f is real everywhere or invoke the strip-only restriction theorem.

E5's portion of the N1 default-resource feasibility gate passes. E6 gluing/identity and S4 parameter integration remain separate obligations; their release status and the eventual exponential-safety theorem are outside this audit.

## Definition classification and imports

Exactly two new definitions occur; no abbrev, structure or instance is added.

| Definition | Classification on its whole carrier |
|---|---|
| `e5Pack` | Canonical `Fin.append` concatenation, made into a continuous linear map over any RCLike field. No choice of coordinates, default branch or junk fallback. |
| `e5Unpack` | The pair of projections at `Fin.castAdd d i` and `Fin.natAdd d i`. Defined on every input, including the zero-dimensional carrier; no fallback. |

Their equations and norm/inclusion identities are proved, rather than premises. Bodies are exposed through `@[expose] public noncomputable section`.

Recursive static inspection of the KAM import closure finds 32 modules: 24 frozen definition modules and eight ordinary modules including E5. All 24 frozen imports have manifest kind `definition` and state `SEALED`. There is no provider, frozen theorem anchor or DRAFT_SORRY import. Searching declaration sites throughout KAM finds no other declaration with any of the nine new short names; compilation also confirms there is no full-name collision.

## Independent checks

Every Lean/Lake/checker invocation in this audit was sequential, with `LEAN_NUM_THREADS=1` and niceness 5. No heartbeat, recursion-depth or synthesis override was used. The targeted build went through the required compile gate.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e5 KAM.Planetary.Exponential.LocalComplexification
[inp-gate] slot 1 acquired 15:23:31 for KAM.Planetary.Exponential.LocalComplexification
Build completed successfully (9078 jobs).
exit 0
```

The job count is Lake's dependency graph, not evidence of a from-scratch rebuild. No clean, update, cache download or package edit was performed.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E5Audit.lean
'KAM.Planetary.local_complex_restriction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.complex_division' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.e5Pack_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.e5Unpack_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_e5Pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.e5Pack_complexify' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.local_analytic_complexification' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.e5Pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.e5Unpack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.local_real_complexification' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

This same probe contained the three fresh copied-signature declarations described above and produced no warnings or errors. It is removed after the audit.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.LocalComplexification
replaying KAM.Planetary.Exponential.LocalComplexification
exit 0
```

There is no separate new lemma module to add to this one-invocation replay.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint diagnostic is the explicitly permitted stale generated root. Module checks, frozen-anchor guard and elaborated ABI hashes pass. The root was not regenerated.

Static hygiene: 145 total lines, complete copyright/module/public-import/docstring/public-section form; no forbidden proof token, resource override or EuclideanSpace. `git diff --check inp...HEAD` exits 0 with no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0 with no output. Generated files and frozen files were not edited.

## Blueprint/source defects, uncertainties and deviations

No new suspected pinned-source defect or blueprint contradiction was found in E5. No pinned-PDF re-audit or later consumer implementation is claimed.

Inherited blueprint interface gap, already identified by the design: `blueprint-P/parts/p7-kepler-poincare.tex:173` says “the complex derivative restricts to the real one” and cites `bp:p1:real-restriction`. The cited strip-domain result does not directly apply to that local chart domain. This is an applicability gap in the citation, not a refutation of the derivative identity. E5 supplies the explicit local replacement at L35–51, as required by P14 design L344. No frozen statement was silently changed.

The generic brief's provider/seal checks were specialized to this helper-only scope; the generated-root exception is authorized explicitly. There are no introduced mathematical deviations or unresolved E5 proof obligations. Only the requested report is a persistent audit edit; scratch probes are removed and no state-changing git command was run.
