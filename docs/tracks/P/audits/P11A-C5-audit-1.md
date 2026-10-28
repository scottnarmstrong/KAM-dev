# P11A-C5 independent package audit 1

Verdict: **PASS WITH NOTES** for the two scoped implementation modules and all four signed theorem exports. This package has no frozen theorem anchor or provider to seal (`FROZEN_FILE` / `FROZEN_DECL` are `-` in the homological graph record). This verdict certifies the signed infrastructure interface, not P-FIXED or the complete canonical-step assembly.

## Scope and authority

Audited `/root/code/KAM-inp-p11ac5` at HEAD `92d953c744d42d1f8ef9d9dd7df81962f6bf68b0`, comparison `inp` resolving to `e3c09abddbe2d63d3c4335def1dc126a09046640`. Read AGENTS.md, PLAN, DECISIONS, the package-audit brief, supplied handoff/AUDIT FOCUS, Track P statement, P11A design and design audits 1–3, the R3 signature file, the homological blueprint and graph contracts, and the relevant imported frozen definitions (including the action neighbourhood and Hamiltonian field).

Only `KAM/Planetary/MaximalStep/Homological.lean` and `HomologicalBracket.lean` receive implementation verdicts. `git diff inp...HEAD` warns of multiple merge bases and selects `d8186af4760416753d9fc6f3c93eca3f0bfdc2b9`; the diff contains these two additions and inherited N/P graph changes. Those graph edits are outside the requested audit. The protected-path comparison is empty. The handoff was already untracked at entry. Only this report and temporary `.lake/abi-scratch/` audit artifacts were written; no state-changing git command was used.

The signature and earlier audit files missing from this worktree were read at their actual locations under `/root/code/KAM-inp`. The signature SHA-256 is `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`, matching the R3 audit. The user's exact absolute report destination overrides the generic brief's main-worktree destination.

## Fidelity and refutation results

All eight scoped signed declarations match the supplied R3 signature after whitespace normalization: four definition bodies (`p11Solve`, `p11AngleClass`, `p11AngleAverage`, `p11Affine`) and four theorem headers (`homological_maximal`, `_real`, `_param`, `p11_normal_affine_bracket`). No premise, quantifier, constant, norm or carrier changes. The earlier F1 defect stays repaired: input/competitor polynomial premises apply on `univ ×ˢ B`, not outside B. The solution's unconditional global truncation conclusion is signed and follows from its finite construction.

Checked the finite support enclosure carefully: `hmModes` uses `ceil(T)` and is only an enclosure. `hmCoef` and `hmCut` separately retain the exact real cutoff; summation proofs never silently admit the extra enclosure modes. Division is total in Lean outside divisor hypotheses, but every inversion/cancellation and holomorphy use on B proves nonvanishing from positive D and the D/2 bound. No theorem obtains its analytic content from a zero-denominator fallback.

Coefficient holomorphy is proved by an actual compact torus parametric integral; finite-sum differentiation supplies the equation. Uniqueness compares integral Fourier coefficients of polynomial competitors, then uses nonzero divisors and zero average. Reality pairs k and -k. The scalar parameter estimate places a closed ball of radius t-t' around an inner point strictly inside E+t using the inner point's strict distance margin; it does not assume E convex. The Lambda estimate handles n=0 separately, important because `_param` has no positive-dimension premise. No conclusion-shaped input was found.

## Notes on scope and integration

1. Design schedule L716 says `C4; finite coefficients, averages and parameter derivatives`. C5 does **not** import C4 Cutoff/Divisor. The accepted signed interface already receives the complex-domain `hdiv` and polynomial datum. C4 must supply these to a consumer; C5 proves the remaining homological work directly. Thus `stepP:p11a:hm-div` is an upstream input boundary, not independently proved here. Do not mark the complete blueprint source-premise assembly closed merely because this signed module passes. The scalar theorem can be applied separately to P0 and every P1 component.
2. Blueprint p11a2 L180 includes reality of averages as well as generators. The signed reality export is the generator clause; the new public `coeff_neg_conj` at k=0 also proves conjugation invariance of the actual average, hence its reality. There is no missing analytic assumption, although no separately named average-reality convenience theorem is exported.
3. The signed bracket export gives the general derivative identity. Substitution of the scalar homological equations yields blueprint L183/L197's `-(P-<P>)`; that final assembled specialization is not a separate exported declaration here. This matches the accepted signed bridge.
4. The handoff flags a second `p11Affine` definition on C6. The audited dependency closure has only this definition, so no current collision occurs. Integration must retain one shared definition. The scalar Cauchy helper duplicates the vector C3 proof; this is maintenance debt, not a soundness issue.
5. Expected stale generated-root lint status is recorded below. No generated file was repaired during this report-only audit.

## Per-declaration ledger

Names below are in `KAM.Planetary`; H = Homological.lean, B = HomologicalBracket.lean. Each helper is checked against its displayed finite-sum/analytic responsibility rather than being presented as the whole source proposition.

| Node / responsibility | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| `stepP:p11a:hm-div` | No C5 export; `hdiv` supplied by the C4 consumer boundary | PASS WITH NOTES | This module does not prove divisor extension from real E; do not close that upstream node from this audit. |
| `hm-coeff` | `p11Solve` (H:31) | PASS | Signed finite Fourier solver; exact signed body. |
| `hm-coeff` | `p11AngleClass` (H:35) | PASS | Signed holomorphy and local periodicity predicate; exact body. |
| `hm-coeff` | `p11AngleAverage` (H:39) | PASS | Signed zero Fourier coefficient; exact body. |
| `hm-coeff` | `hmCoef` (H:45) | PASS | Explicit solver coefficient with zero/cutoff guard. |
| `hm-coeff` | `hmCut` (H:51) | PASS | Explicit truncated input coefficient. |
| `hm-coeff` | `hmModes` (H:56) | PASS | Finite enclosing cutoff using natural ceiling; may strictly contain the real cutoff. |
| `hm-coeff` | `mem_hmModes` (H:58) | PASS | Exact ceiling-cutoff membership, not claimed to be the real cutoff. |
| `hm-coeff` | `mem_hmModes_of_le` (H:61) | PASS | Real cutoff implies membership in finite enclosure. |
| `hm-coeff` | `p11Solve_eq` (H:64) | PASS | Solver equals Fourier sum of hmCoef. |
| `hm-coeff` | `truncate_eq` (H:71) | PASS | Existing truncation equals Fourier sum of hmCut. |
| `hm-coeff` | `hmCoef_eq_zero` (H:77) | PASS | Solver support contained in hmModes. |
| `hm-coeff` | `hmCut_eq_zero` (H:85) | PASS | Truncation support contained in hmModes. |
| `hm-coeff` | `fourierSum_finset` (H:91) | PASS | Finite support converts tsum to a finite sum. |
| `hm-coeff` | `summableWeighted_finset` (H:96) | PASS | Finite support gives every weighted summability. |
| `hm-coeff` | `torusCoeff_fourierSum_finset` (H:100) | PASS | Coefficient recovery by existing Fourier uniqueness API. |
| `hm-coeff` | `hasFDerivAt_fourierSum_finset` (H:105) | PASS | Termwise finite-sum derivative with period-one factor. |
| `hm-coeff` | `fderiv_fourierSum_finset` (H:116) | PASS | Directional derivative is coefficient times 2πi k·v. |
| `hm-coeff` | `differentiable_fourierSum_finset` (H:126) | PASS | Entire angle differentiability of finite sums. |
| `hm-a` | `norm_coeff_le` (H:136) | PASS | Strip Fourier decay with explicit parameter membership. |
| `hm-bc` | `differentiableOn_coeff` (H:146) | PASS | Parametric integral proves holomorphy on arbitrary open B. |
| `hm-a` | `sum_exp_le_lambda` (H:198) | PASS | Finite nonzero lattice sum bounded by Lambda; n=0 separately empty. |
| `hm-a` | `norm_hmCoef_le` (H:220) | PASS | Decay divided by πD from divisor lower bound D/2. |
| `hm-a` | `norm_solve_le` (H:241) | PASS | Sum coefficient/character bounds; exact Lambda M/(πD). |
| `hm-coeff` | `differentiableOn_dotC` (H:296) | PASS | Finite linear combination preserves parameter holomorphy. |
| `hm-coeff` | `differentiableOn_hmCoef` (H:302) | PASS | Quotient holomorphy; positive D forces nonzero retained divisors. |
| `hm-coeff` | `differentiableOn_solve` (H:323) | PASS | Entire-angle / B-parameter joint holomorphy by finite sum. |
| `hm-coeff` | `hmCut_zero` (H:339) | PASS | Zero cutoff coefficient for nonnegative T. |
| `hm-coeff` | `hmCoef_zero` (H:343) | PASS | Solver zero coefficient vanishes unconditionally. |
| `hm-coeff` | `fderiv_solve` (H:346) | PASS | Equation with truncated datum for every angle; no polynomial premise needed. |
| `hm-coeff` | `coeff_solve` (H:382) | PASS | Actual integral coefficients equal explicit solver coefficients. |
| `hm-coeff` | `torusCoeff_zero` (H:392) | PASS | Zero function has zero coefficient. |
| `hm-coeff` | `solve_unique` (H:405) | PASS | Coefficient comparison; stronger equality on all univ × B; polynomial competitors supplied locally. |
| `homological-maximal` | `homological_maximal` (H:472) | PASS | Exact signed conjunction, including uniqueness, entire angle extension, average and coefficient bounds. |
| `hm-d` | `conj_character_real` (H:540) | PASS | Conjugation reverses real-angle Fourier mode. |
| `hm-d` | `coeff_neg_conj` (H:554) | PASS | Real datum implies coefficient conjugate symmetry; k=0 also gives reality of the average. |
| `hm-d` | `hmCoef_neg_conj` (H:564) | PASS | Real frequency gives solver coefficient conjugate symmetry. |
| `homological-maximal` | `homological_maximal_real` (H:600) | PASS | Exact signed reality clause; proof works with fewer premises than signed. |
| `hm-bc` | `param_cauchy_scalar` (H:627) | PASS | Scalar Cauchy iteration on nested balls; no hidden convexity of E required. |
| `homological-maximal` | `homological_maximal_param` (H:653) | PASS | Exact signed every-order parameter estimates for solver and average. |
| `hm-bracket` | `p11Affine` (B:29) | PASS | Signed scalar-plus-linear-action generating function; exact body. |
| `hm-bracket` | `p11_normal_affine_bracket` (B:34) | PASS | Exact signed bracket bridge with existing Poisson sign. |

## Definition classification

All seven new definitions are explicit intended objects on their whole total Lean carrier: signed `p11Solve` (finite nonzero-mode quotient sum), `p11AngleClass` (local analytic/periodic predicate), `p11AngleAverage` (actual zero integral coefficient), `p11Affine` (actual affine generator), plus `hmCoef`, `hmCut`, and `hmModes` (coefficient families and finite enclosure). No new abbrev, structure, instance, choice selector or replacement Hamiltonian is introduced. Guarded zero coefficients implement truncation, not an assumed proof. For arbitrary data outside B or with zero divisors, total division and integral conventions exist, but analytic conclusions rely on the stated local regularity/divisor premises, not junk values.

## Hygiene and independent validation

All audit-owned Lean checks were serial, with `LEAN_NUM_THREADS=1`; every actual Lean/Lake invocation ran at nice priority 5. No clean, update, cache fetch, resource override, library rebuild from scratch, frozen edit or generated-root edit was used.

- Targeted gate command: `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac5 KAM.Planetary.MaximalStep.Homological KAM.Planetary.MaximalStep.HomologicalBracket`. The wrapper invokes `nice -n 5 lake build`. Exit **0**; exact success output: `Build completed successfully (9089 jobs).` The gate waited before acquiring slot 2 at 13:28:43 UTC. Build warnings were unused variables and one unused `neg_neg` simp argument; inherited Parameter also reports unused variables. No elaboration error or heartbeat failure.
- Probe command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC5Audit.lean`. Exit **0**, no warnings/errors. Four fresh copies of signed definition bodies were checked against the implementation by `rfl`; four fresh declarations with the exact signed theorem headers were proved by applying the implementation to the explicit binders in order. Provider/frozen-type and seal-body probes are **not applicable** because this package supplies infrastructure rather than an anchor/provider pair.
- The same probe printed axioms of **all 34** new public theorems. Exact output:

```text
'KAM.Planetary.mem_hmModes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.mem_hmModes_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Solve_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.truncate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmCoef_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmCut_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fourierSum_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.summableWeighted_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torusCoeff_fourierSum_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hasFDerivAt_fourierSum_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_fourierSum_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiable_fourierSum_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_coeff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_exp_le_lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_hmCoef_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_solve_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_dotC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_hmCoef' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.differentiableOn_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmCut_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmCoef_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fderiv_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torusCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.solve_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.homological_maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.conj_character_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_neg_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.hmCoef_neg_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.homological_maximal_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.param_cauchy_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.homological_maximal_param' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_normal_affine_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Import closure check: 43 KAM modules; ten frozen imports, all definition anchors with manifest state **SEALED** (`ActionNbhd`, `ComplexStrip`, both Hamiltonian fields, `IsDiophantine`, `IsPrimaryOnStrip`, `IsRealOnReals`, `OmegaZero`, `SymplecticForm`, planetary `Phase`). No provider or frozen theorem occurs. All seven definitions and 34 theorems are public under the exposed noncomputable public section. Both files have copyright, `module`, public imports and module documentation. File lengths: **688** and **84** lines. Direct forbidden-token search returned no matches, including no `EuclideanSpace`, proof escapes, or resource settings. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no diff (only the multiple-merge-base warning). `git diff --check` exited **0**.

Source integrity hashes:

```text
be78b8c2a47b6754d55d221bdcece015d04dc25ebb11930923ee232c66ac38bd  Homological.lean
44f33400ec6303b98ea3910eff55145cfabed382e736369cbb4a2629f033a173  HomologicalBracket.lean
990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec  blueprint-P/parts/p11a2-cutoff-step.tex
8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9  docs/tracks/P/design/P11A-LEAN-DESIGN.md
```

- Kernel replay command: `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.Homological KAM.Planetary.MaximalStep.HomologicalBracket`. Exit **0**. Exact output:

```text
replaying KAM.Planetary.MaximalStep.HomologicalBracket
replaying KAM.Planetary.MaximalStep.Homological
```

- Lint command: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`. Exit **1**, solely the explicitly permitted stale generated-root condition. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (661 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The lint ABI subprocess inherited both single-thread configuration and nice priority 5, and ran after kernel replay exited. No concurrent audit-owned Lean process was launched. All substantive lint checks passed; `KAM.lean` was left untouched as required.

Closeout: removed the audit-owned probe and captured logs after copying their results here. Rechecked the module hashes, report formatting, protected-path diff and `git diff --check`. Only this audit report is newly persistent; the previously untracked prover handoff remains unchanged.


## Suspected source defects, deviations and uncertainties

No new suspected defect in a pinned source or contradiction with the homological blueprint was found. The package follows the accepted R3 decomposition; the upstream C4 boundary, bracket specialization, and merge duplication are explicitly retained above. No source PDF claim is newly certified: this is an implementation/signature/blueprint audit. No frozen-anchor or campaign theorem closure is claimed.
