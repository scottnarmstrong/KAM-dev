# P11A-P0 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the three P0 suppliers. No blocking mathematical or signature-fidelity finding. This package contains no provider or frozen theorem seal; provider/frozen-type and seal-body checks are therefore not applicable. It proves local tools for hc-rot and hc-mean, not the complete holomorphic chart or any planetary headline.

## Scope and authority

Audited HEAD `06f3d3948219fb28882beb8669406c1335401f53`, with `inp` resolving to `686d56cfb012dd62ac088abd79a6dd17cb22eb98`, using `git diff inp...HEAD`. The complete tracked delta is precisely:

- `KAM/Planetary/Preparation/AnalyticExtension.lean`: 214 added lines.
- `KAM/Planetary/Preparation/Schwarz.lean`: 128 added lines.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, the untracked P0 handoff/AUDIT FOCUS, track-P statement, P11A design row P0, SG1/SG2 and signatures, the relevant portions of design audits 1–3, and blueprint-P `p11-cp09-preparation.tex` L75/L83. The supplied signature file is `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` (SHA-256 `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`). The user explicitly places this report in this package worktree, overriding the generic brief's main-worktree destination.

No production file was edited. Only this report and disposable audit scratch under `.lake/abi-scratch/` were written. No git mutation, generated-root regeneration, dependency modification, or source repair was performed. The handoff was already untracked when the audit began.

## Declaration ledger

All names below are in `KAM.Planetary`. PASS here concerns the specified helper, not closure of its entire blueprint node.

| Node / obligation | Declaration and source line | Verdict | Reason |
|---|---|---|---|
| hc-rot / SG1 | `p11_real_slice_identity`, AnalyticExtension:30 | PASS | Exact design signature; induction frees coordinates on a max-norm polydisc, with real accumulation points and the one-variable identity theorem. |
| hc-rot coefficient construction | `p11CMap`, AnalyticExtension:109 | PASS | Genuine coordinatewise complexification on its whole carrier; no fallback. |
| hc-rot coefficient expansion | `p11CMap_apply`, AnalyticExtension:116 | PASS | Literal finite coordinate expansion of the definition; no extra hypotheses. |
| hc-rot real restriction | `p11CMap_real`, AnalyticExtension:124 | PASS | Agrees on diagonal real inputs, exactly what the series comparison needs. This is a construction helper, not a weakened replacement for a blueprint theorem. |
| hc-rot convergence bound | `norm_p11CMap_le`, AnalyticExtension:139 | PASS | Actual operator norm bound by `a^n * ‖P‖`, obtained from all `a^n` coordinate terms. |
| hc-rot / SG1 | `p11_complexification`, AnalyticExtension:163 | PASS | Exact design signature; starts from the supplied real analytic expansion and constructs a complex series with positive radius. |
| hc-mean derivative bridge | `p11_iterate_dslope_zero`, Schwarz:30 | PASS | Vanishing derivatives imply the required iterated divided-slope values vanish, using power-series coefficients and nonzero factorials. |
| hc-mean scalar Schwarz | `p11_schwarz_one`, Schwarz:46 | PASS | Order-k scalar Schwarz on an open disc; no boundary holomorphy premise or assumed estimate. |
| hc-mean / SG2 | `p11_radial_schwarz`, Schwarz:89 | PASS | Exact design signature, including `hM`; full vanishing jets restrict to vanishing derivatives on every radial line. |

Each of the three main theorem headers is identical to the supplied signature after deleting whitespace, including binder order, hypotheses, constants, carriers and conclusion. Separate copied-signature theorems under fresh names elaborate with bodies `exact p11_complexification hf`, `exact p11_real_slice_identity hr hF hzero`, and `exact p11_radial_schwarz hr hM hF hb hj`; each also passes an `example : type_of% @audit_<name> := @<name>` check. No draft signature module was imported.

## Definition and proof audit

The only new definition/abbreviation/structure is `p11CMap`. Its finite sum of continuous complex multilinear maps is the intended complexification for every real continuous multilinear input. Empty products and empty finite sums have the correct zero-arity and zero-dimensional interpretations: when `a = 0` and arity is positive, the original multilinear map vanishes; arity zero retains the constant coefficient. No inhabited-default, conditional choice, inverse, supremum or junk branch occurs in this definition.

Complexification bounds each coefficient by `a^n`, takes `A = max a 1`, and shrinks a strictly positive real-series subradius to `s = r′/A`. The positive lower bound for the complex convergence radius is proved, not assumed. Agreement with f on real inputs follows from the uniqueness of the two convergent sums and continuity of real inclusion. Behavior of the total series-sum function outside the convergence ball is never used.

The identity proof uses the Pi max norm: replacing one coordinate by any point of its radius-r disc preserves the ball. At each induction step the partially real locus supplies infinitely many zeros accumulating at the real center. The terminal condition after n freed coordinates is vacuous. The argument also covers n = 0.

For Schwarz, k-fold divided-slope factorization gives `g(ζ) = ζ^k h(ζ)`. The maximum-modulus principle is applied only on smaller closed discs lying strictly within the original domain; then ρ tends to R from below. Thus no regularity on the original boundary is required. The radial argument uses `R = r/‖z‖` only after separating `z = 0`; it separately handles k = 0 and positive k at zero. For nonzero z, the line maps its full radius-R disc into the ball and the evaluation point 1 lies strictly inside. The existing `KAM.iteratedDeriv_line_eq_iteratedFDeriv` identifies the actual line derivatives. No conclusion-shaped hypothesis, hidden solving premise, norm change, or additional dimension assumption is present.

The KAM import closure contains 40 modules, no provider and no frozen theorem module. Its frozen imports are definition modules only: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary/Phase. Consequently no DRAFT_SORRY theorem is imported; there is no sealed theorem dependency whose state must be checked. Existing carriers are literally `Fin n → ℝ` and `Fin n → ℂ`; `p11Bound` is literally the pointwise norm bound on its stated set.

## Notes, uncertainties and deviations

1. Design SG2 (P11A-LEAN-DESIGN.md:644) proposes the little-o route via `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`. The implementation instead proves the same statement by repeated dslope factorization and maximum modulus. This is a valid proof-route departure with no signature or source-premise change; the handoff's “no deviations” is best read as no statement deviation.
2. Design row P0 (L720) lists C3; the actual proof needs MaximalStep.Basic and the strip modules, with no C3-specific dependency. This is a reduced dependency requirement, not an unpaid premise.
3. The unused `hM` warning is harmless: nonnegativity also follows from the bound at the origin. Retaining it preserves the exact approved design signature.
4. AnalyticExtension's module docstring L21 calls the construction `p11_cmap`; the exported spelling is `p11CMap` (L109). This is a minor documentation typo, not an API or proof defect.
5. These suppliers do not yet apply complexification entrywise to the rotation, prove its matrix identities, or establish the averaged remainder's vanishing jets. Those remain obligations of downstream chart/mean assembly. No such closure is claimed here.

No new suspected defect in a pinned mathematical source or blueprint statement was found. The pre-existing SG1/SG2 proof gaps are addressed at the supplier level; downstream applications remain outside this two-file audit. No external source/PDF claim was independently added by this audit.

## Independent validation receipts

All completed Lean invocations below were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build used the required compile gate. An early lint invocation was stopped during its shell checks before the final serial rerun; no result is claimed from that aborted invocation.

Build command (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap0 KAM.Planetary.Preparation.AnalyticExtension KAM.Planetary.Preparation.Schwarz
```

```text
[inp-gate] slot 2 acquired 12:37:32 for KAM.Planetary.Preparation.AnalyticExtension KAM.Planetary.Preparation.Schwarz
⚠ [9085/9086] Replayed KAM.Planetary.Preparation.Schwarz
warning: KAM/Planetary/Preparation/Schwarz.lean:89:61: Variable name `hM` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hM

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9086 jobs).
```

Copied-signature/type and axiom probe command (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP0Audit.lean
```

The probe imports only the two compiled modules. It contains fresh copies of the three exact design signatures, application bodies and `type_of%` checks described above, followed by `#print axioms` for every new public theorem. Exact output:

```text
'KAM.Planetary.p11_real_slice_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11CMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11CMap_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_p11CMap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_complexification' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iterate_dslope_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_schwarz_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_radial_schwarz' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay command (one invocation, exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.AnalyticExtension KAM.Planetary.Preparation.Schwarz
```

```text
replaying KAM.Planetary.Preparation.Schwarz
replaying KAM.Planetary.Preparation.AnalyticExtension
```

Lint command (exit 1 solely for the expressly permitted stale generated root):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (651 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No other lint diagnostics occurred. Both new files have the required copyright, module command, public imports, docstring and exposed public noncomputable section. The forbidden-token/override scan found no matches in either file. File lengths are 214 and 128, below the 1500-line cap.

Additional read-only checks:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exited 0 with empty output. The final report was checked for trailing whitespace and its exact absolute destination. Disposable audit probes and logs were deleted after their receipts were copied here. The pre-existing handoff remains untouched. The only new persistent repository artifact is this report.

Audited source SHA-256:

```text
19146c4744c4e91a58b8461b9c945ad47f22d7bd1091be58d052416049b75afb  KAM/Planetary/Preparation/AnalyticExtension.lean
e39401618988db432f936da41dbaa211f87a3c2d05c874b22f6c80be08be95ed  KAM/Planetary/Preparation/Schwarz.lean
```
