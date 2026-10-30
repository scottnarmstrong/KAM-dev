# W0-ANALYSIS independent audit 1

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-wpe`, branch `inp-wpe`.
Audited HEAD: `d6dfd6eec9781923f3dc2cdc7ebecd6dfe42a50f`.
Comparison `inp` and merge base: `7b86cf178eaaffba3a7a4205a561b41ef3660455`.

## Verdict

**FAIL for complete fidelity to the assigned CURRENT blueprint nodes.** The package proves substantial, axiom-clean real analysis infrastructure, but the complex-carrier conclusions of `bpW:w0n:recon-bounded` and `bpW:w0n:cubic-bound` are not exported. The real cubic headline, gradient formulas, frozen-definition bridges, and both directions of the PDE correspondence pass at their stated real types. This verdict concerns source-node completion, not a counterexample to those real theorems. There is no provider or anchor seal in scope; provider/type/seal item 1 is N/A by the handoff's AUDIT FOCUS. No theorem-anchor closure is certified.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (including D41 and D43), the external package audit brief, the entire handoff including its refactors/AUDIT FOCUS, current blueprint-W/parts/w0-conventions.tex and the assigned statements/proofs in w0-normalization.tex, relevant frozen Wave definitions, their manifest entries, and the entire `git diff inp...HEAD`. `docs/tracks/W/statement.md` does not exist; `docs/tracks/W/W-STATEMENTS.md` is the actual statement document. Its old draft-status banner is superseded by D41 and the live manifest. The normalization blueprint is byte-identical to current `inp`: SHA256 `83f7f2ebcbf97613e30433401435e374f2731749fd9ef8b44ba2ac9b7697505b`.

Only this report is an intended repository edit. Lean probes were confined to `.lake/abi-scratch/` and removed. No source, manifest, generated root, or git state was changed by the audit.

## Findings and scope

### F1 — missing complex versions (blocking source-node completion)

`blueprint-W/parts/w0-normalization.tex:19-24` explicitly starts with “For c ∈ ℓ^{a,p}_ℂ” and asserts the reconstruction estimate, derivative-series convergence, and coefficient recovery. The package's `WaveEll` (`EllSeq.lean:34`), `waveSineSeries` (`SineSeries.lean:47`), and all these exports accept `ℕ+ → ℝ`. The real results are correct but specialize the source carrier. No complex reconstruction theorem with this exact coefficient estimate and full conclusions is supplied here. Imported complex sine-feature infrastructure does not itself instantiate this source statement for complex sequences.

More directly, `w0-normalization.tex:120-128` defines T “on (ℓ^{a,p}_ℂ)^3” with target “ℓ^{a,p+1}_ℂ”. In contrast, `CubicBound.lean:35` defines `waveTrilinear ... (q q' q'' : ℕ+ → ℝ) ... : ℝ`, and `wave_trilinear_bound` at line 166 quantifies only over real sequences. `waveCubicMultilinear` (`CubicAnalytic.lean:136`) has scalar field ℝ and real lp inputs/output; its analyticity theorem proves real analyticity of the real headline. It does not supply the source's complex trilinear extension and exact bound. A transient probe confirms the named T and sine-series exports reject `Complex.I`-valued input; the source scan confirms there is no replacement complex export in the 18-module delta.

Required closeout: export the complex reconstruction and complex trilinear results on the source carriers (with exactly the stated constants), or obtain an explicit scope ruling that leaves these complex clauses open. A mathematical argument that complexification should be possible is not a Lean attachment. The real headline remains useful and verified.

### N1 — sequence API duplication remains, with correct bridges

`SeqBridge.lean:27,37,44` proves, respectively, `WaveEll ↔ IsEll`, equality of `waveEllNorm` with the membership-indexed `ellNorm`, and equality of `waveEllToLp` with `tauLp` on `IsEll`. These bridges are correct and hold for every real a,p (stronger than a≥0). However, the old objects are still separate `def`s at `EllSeq.lean:34,38` and `PdeBase.lean:45`; they are not aliases of the landed API. Thus a literal “no duplicate ... remains” check is not satisfied. This is a maintenance/scope note, not a defect in the equality proofs. `w0aL2` likewise remains a real raw-series helper corresponding to the landed norm on its intended domain.

The convolution refactor itself does reuse the landed `waveConv`, `waveTwoWeight`, `waveJap`, `waveAlgConst`, and `wave_algebra`; `ConvAlgebra.lean`/`ConvYoung.lean` do not appear in the delta. `waveQuartic` and `waveSign` really are abbreviations of `sineQuarticCoeff` and `boolSign`, and `abs_waveQuartic_le_signs` directly uses `abs_quarticCoeff_le`. The initial handoff's “no Wave/Seq”/“no Normal(other)” description is stale after the explicitly documented refactor: imports now include Seq.Transport, Algebra.*, and Normal.QuarticCoeff.

### N2 — force export packaging

`wave_force_identity` (`PdeForce.lean:87`) proves pointwise equality on [0,π]. Its force series is absolutely summable by `summable_abs_sqrtLam_waveCubic`; `waveSineSeries_tendstoUniformly` then supplies the uniform convergence asserted in the source. This is a composition of exported facts, not an additional premise.

The separate linear identity `-∂ₓ²U+mU=U(λ²q)` is not exported verbatim. `wave_sineModeIter_two` (`PdeForward.lean:36`), the termwise derivative theorem, and the coefficient algebra in `wave_pde_identity` (`:88-116`) implement it inside the full PDE series identity. The advertised `waveSineSeries_two_eq` in `PdeForce.lean:19-20` does not exist. Record the exact surface limitation; consumers wanting that standalone identity must assemble it. No sign or λ/√λ normalization error was found in the implemented PDE proof.

## Node conclusions

| Node / obligation | Exports | Verdict | Reason |
|---|---|---|---|
| bpW:w0n:recon-bounded, full source | waveEll_summable_pow_mul; waveEll_tsum_pow_mul_le; waveSineSeries_*; contDiff/iteratedDeriv; integral recovery | FAIL | F1: real specialization of a complex-carrier statement. Real reconstruction passes; boundedness is expressed by derivative sup estimates and linearity, without a bundled C^k operator. |
| bpW:w0n:gradient | waveG_hasSum; waveCubic_hasSum; hasDerivAt_waveG_coord; integral_waveU_cube_mul_sineMode | PASS | Absolute convergence, factor 1/4, λ_l^(-1/2), and coordinate derivative match; p is arbitrary real rather than p≥0, a strict strengthening. |
| bpW:w0n:algebra bridge | w0a_convAlgebra_nonneg; w0a_summable_of_weighted | PASS | Uses the already-landed complex algebra; nonnegative real specialization is an internal proof tool. |
| bpW:w0n:cubic-bound, general T | wave_trilinear_bound; waveTrilinear_add/smul/swap_* | FAIL | Correct real statement with a≥0, p≥1/2, smoothing p+1, C_*=K_(p+1/2)^2/π; missing complex T. |
| bpW:w0n:cubic-bound, real headline | wave_cubic_bound; cubicGrad_mem_ell; cubicGrad_norm_le; waveCubicLp_* | PASS | Real analytic cubic in weighted lp coordinates, exact constant 8(1+2 Re ζ(3))/π, independent of m. |
| frozen displacement/gradient links | reconU_eq_waveU; cubicGrad_eq_waveCubic | PASS | Exact frozen functions, no replacement definitions; equations verified by fresh terms. |
| frozen classical-solution link | isClassicalSolution_iff_with_univ | PASS | Exact witness predicate, joint continuity and one-sided spatial endpoint derivatives retained. |
| bpW:w0n:pde-equiv (i) | wave_coeff_to_pde | PASS | Source continuity and Banach C¹ hypotheses retained; open-set generalization is stronger. |
| bpW:w0n:pde-equiv (ii) | wave_pde_to_coeff | PASS | Assumes a classical solution and velocity reconstruction; concludes coordinate C¹ and coordinate ODEs. No Banach C¹ premise in this direction. |
| bpW:w0n:force, cubic | wave_force_identity + summability + uniform convergence exports | PASS WITH NOTES | Uniform statement is split across exports; N2. |
| bpW:w0n:force, separate linear formula | wave_sineModeIter_two; wave_pde_identity; iteratedDeriv_waveSineSeries | PASS WITH NOTES | Implemented coefficientwise in the PDE proof; no separate named full linear identity; N2. |
| sequence transport refactor | waveEll_iff_isEll; waveEllNorm_eq_ellNorm; waveEllToLp_eq_tauLp; coeff_isEll_one_one | PASS WITH NOTES | Equalities correct; separate duplicate definitions remain (N1). |
| quartic closed form / other W0 normalization results | landed sineQuarticCoeff/abs_quarticCoeff_le | OUT OF SCOPE | Consumed from inp; not independently reproved or certified by this package audit. |

## Binder audit of source-facing results

Bins: SOURCE = explicit statement premise or source-domain membership; STANDING = m>0; TYPING = parameter/function/index data; RULED = owner correction; EXCESS = unsupported premise. Tables include implicit parameters. Membership in WaveEll is precisely summability of `(ellWeight*a coefficient)^2`, not a conclusion bundle. All `WaveEll` uses in source-facing results are input membership or proved output membership.

The representative reconstruction estimate has these inputs (`waveSineSeries_abs_le`, SineSeries.lean:88):

| Binder | Bin | Evidence |
|---|---|---|
| a | TYPING | source coefficient radius |
| p | TYPING | source real exponent |
| ha : 0<a | SOURCE | w0-normalization.tex:19 |
| c : ℕ+→ℝ | TYPING | real restriction; F1 |
| hc : WaveEll a p c | SOURCE | source input membership |
| k : ℕ | TYPING | derivative order |
| x : ℝ | TYPING | all-real evaluation strengthens the spatial range |

Counts: SOURCE 2, STANDING 0, TYPING 5, RULED 0, EXCESS 0. Other reconstruction lemmas split this into summability, linearity, differentiation and coefficient integration. Their explicit summability premises are the proved intermediate requirements supplied by `waveEll_summable_pow_mul`; none is substituted for source membership in the estimate.

For `waveG_hasSum`, `waveCubic_hasSum`, and `hasDerivAt_waveG_coord`, each of m,a,p,c is TYPING; hm is STANDING; ha and hc are SOURCE; the latter two declarations additionally have l : ℕ+ (TYPING). Counts for waveG_hasSum: SOURCE 2, STANDING 1, TYPING 4, RULED 0, EXCESS 0; the other two have TYPING 5. Formulas match w0-normalization.tex:75-81 and the coordinate derivative clause; arbitrary real p strengthens the source.

`wave_trilinear_bound` (CubicBound.lean:166):

| Binder | Bin | Evidence |
|---|---|---|
| m | TYPING | mass parameter |
| hm : 0<m | STANDING | bpW:w0:mass |
| a | TYPING | radius |
| p | TYPING | regularity exponent |
| ha : 0≤a | SOURCE | w0-normalization.tex:120 |
| hp : 1/2≤p | SOURCE | same |
| q | TYPING | first input; real restriction F1 |
| q' | TYPING | second input; F1 |
| q'' | TYPING | third input; F1 |
| hq : WaveEll a p q | SOURCE | input membership |
| hq' : WaveEll a p q' | SOURCE | input membership |
| hq'' : WaveEll a p q'' | SOURCE | input membership |

Counts: SOURCE 5, STANDING 1, TYPING 6, RULED 0, EXCESS 0. Neither a nor m appears in the exported constant. `waveCubic_eq_trilinear` needs a>0 and membership but no p≥1/2, a valid strengthening of the identification clause. Scalar multiplication/symmetry helpers sometimes hold for all raw sequences because total tsums commute with those operations; additivity is guarded by proven summability.

`wave_coeff_to_pde` (PdeForward.lean:131):

| Binder | Bin | Evidence |
|---|---|---|
| m | TYPING | mass |
| hm | STANDING | bpW:w0:mass |
| I | TYPING | time domain |
| hI : IsOpen I | SOURCE | open interval premise weakened to open set |
| q | TYPING | coefficient curve |
| p | TYPING | momentum curve |
| hq | SOURCE | q(t) ∈ ℓ^{1,1} |
| hp | SOURCE | p(t) ∈ ℓ^{1,1} |
| _hqc | SOURCE | continuity into ℓ^{1,1}; w0-normalization.tex:170 |
| _hpc | SOURCE | same for p |
| hqd | SOURCE | C¹ into ℓ^{1,0} |
| hpd | SOURCE | same for p |
| hqe | SOURCE | q̇=λp in ℓ^{1,0} |
| hpe | SOURCE | ṗ=-λq-𝒢(q) in ℓ^{1,0} |

Counts: SOURCE 9, STANDING 1, TYPING 4, RULED 0, EXCESS 0. The unused `_hqc` and `_hpc` are **not extra premises**: the source explicitly assumes them. `ContDiffOn ℝ 1` is on the lp-valued weighted coordinates, so this is Banach C¹, not coordinatewise C¹. On an open I, within differentiability gives ordinary time derivatives. The two right-hand sequences are proved to belong to WaveEll 1 0 (`:144-154`), so the `waveEllToLp` fallback cannot make either system equation vacuous. Local neighborhoods lie inside I, so arbitrary values outside I do not affect time derivatives.

`wave_pde_to_coeff` (PdeConverse.lean:310):

| Binder | Bin | Evidence |
|---|---|---|
| m | TYPING | mass |
| hm | STANDING | bpW:w0:mass |
| I | TYPING | time domain |
| hI | SOURCE | open-set generalization |
| q | TYPING | curve |
| p | TYPING | curve |
| hq | SOURCE | q(t) ∈ ℓ^{1,1} |
| hp | SOURCE | p(t) ∈ ℓ^{1,1} |
| ut | TYPING | classical derivative witness |
| ux | TYPING | classical derivative witness |
| utt | TYPING | classical derivative witness |
| uxx | TYPING | classical derivative witness |
| hsol | SOURCE | expanded below |
| hut | SOURCE | u_t=V_m(p) on I×[0,π] |
| j | TYPING | arbitrary mode |

The `hsol` binder expands literally into: continuity of each of u,ut,ux,utt,uxx; the time derivative u→ut; the time derivative ut→utt; the within spatial derivative u→ux; the within spatial derivative ux→uxx; the pointwise cubic PDE; and the two Dirichlet boundary equalities. Each is SOURCE, exactly bpW:w0:nlw. There are no other fields/instances. Counting this expansion as 12 logical inputs (5 continuity + 4 derivative + 1 PDE + 2 boundary), counts are SOURCE 16, STANDING 1, TYPING 9, RULED 0, EXCESS 0. There is **no** ContDiffOn premise here: the two real-valued coordinate `ContDiffOn ℝ 1` assertions are conclusions. The handoff focus's possible ambiguity between directions is resolved by the actual type. Differentiation under the integral and two integrations by parts are proved, not assumed as gates.

For the frozen bridges, m and y/u are TYPING, hm is STANDING, and l is TYPING where present; EXCESS 0. `isClassicalSolution_iff_with_univ` unfolds the exact frozen existential predicate and the explicit-witness predicate. The fresh probe checks all three links at their literal types.

## Definition classification (all 23 new def/abbrev declarations)

These are infrastructure helpers, not new manifest entries. Distinguish the raw total-function helper from the mathematical object on its membership carrier. No non-unique choice construction or characterization-defined object is introduced. WELL_DEFINEDNESS/CHARACTERIZATION are N/A_LITERAL for finite formulas; for analytic sums their required convergence is proved at every input where source meaning is claimed. CHOICE_INDEPENDENCE is N/A throughout. No source theorem here relies on an out-of-domain zero/default branch.

| Definition | Classification and body/carrier result |
|---|---|
| WaveEll | Literal real membership predicate; sum of squared weighted coefficients. BODY_MATCH OK for real space; full complex source carrier absent (F1). Duplicates IsEll on reals (N1). |
| waveEllNorm | Raw total sqrt-tsum helper; equals source norm under WaveEll/IsEll. Off-space zero is not a norm; not certified as a source norm on the unrestricted sequence carrier. Bridge proved (N1). |
| waveEllMajorant | Literal M_(a,p,k); convergence for a>0 proved. No meaning as a finite source majorant asserted for a≤0. |
| waveSineSeries | Literal derivative series, real only (F1); convergence proved under weighted membership/summability. Raw off-domain tsum is not a claimed reconstruction. |
| waveQuartic | Literal abbrev to landed sineQuarticCoeff, exactly ∫φ_iφ_jφ_kφ_l. |
| waveHat | Literal q_j/√λ_j, positive mass guards all denominators. |
| waveU | Literal real reconstruction series; absolutely convergent on the claimed weighted domains; rfl link to frozen reconU on coeff y. Raw larger carrier is a helper, not a new global frozen reconstruction definition. |
| waveCubic | Literal real integral gradient; integrability follows from reconstruction continuity on source inputs; exact frozen bridge. |
| waveG | Literal 1/4 integral of U^4; convergence/coordinate characterization proved on source inputs. |
| waveCoordShift | Literal finite-coordinate shift q+t e_l; no choice/fallback. |
| waveSign | Abbrev to landed boolSign; no duplicate sign implementation. |
| w0aL2 | Raw real sqrt sum of squares on ℤ; used as norm only with summability; real/complex norm bridge proved. |
| waveEvenAbs | Literal even absolute-value extension, zero at index zero as required by the source; nonzero branch's toPNat' is positive by the branch condition. |
| waveSignedEmb | Explicit finite-sign/positive-index embedding into ℤ³; injectivity proved. |
| waveTrilinear | Literal real triple series; absolute convergence proved for a≥0,p≥1/2; missing complex carrier F1. |
| waveCubicConst | Exact K_(p+1/2)^2/π, depends only on p. |
| waveCubicHeadlineConst | Exact 8(1+2 Re riemannZeta(3))/π; equality with C_*(1) proved. |
| waveCubicAux | Weighted output lp element of T applied to coeff inputs; membership built from wave_trilinear_bound, not assumed. |
| waveCubicMultilinear | ℝ-continuous trilinear map built with proved linearity and bound; real carrier limitation F1. |
| waveCubicLp | Diagonal of that trilinear map; pointwise formula and norm/analyticity proved on every lp input. |
| waveV | Literal velocity series; convergent on source inputs; rfl frozen reconV bridge. |
| waveEllToLp | Explicit zero fallback off WaveEll; on-domain formula and equality with tauLp proved. Every source-facing use has membership; forward RHS memberships independently proved. Safe as guarded helper; not a faithful global source transport on arbitrary sequences (N1). |
| IsClassicalSolutionWith | Literal classical PDE predicate with explicit derivative witnesses and open-time-domain localization; exact equivalence to frozen predicate at univ. BODY_MATCH/PUBLIC_CARRIER OK for this localized predicate; no hidden analytic gate. |

For these guarded helpers the package-definition verdict is PASS at the stated mathematical input domain, subject to F1 and N1. This does not approve their unrestricted total carriers as new source-facing frozen definitions. In particular, one cannot drop a membership condition merely because a raw norm or coordinate map has a Lean value off the space.

## Check receipts

All audit Lean/Lake invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5` on Lean/checker execution (the compile gate applies nice internally). Lint was run only through the prescribed SLIM wrapper. No clean/cache/update/full-root build was run.

The exact module list `M` was:

```text
KAM.Wave.Normal.Analysis.CubicAnalytic
KAM.Wave.Normal.Analysis.CubicBound
KAM.Wave.Normal.Analysis.CubicHeadline
KAM.Wave.Normal.Analysis.CubicLinear
KAM.Wave.Normal.Analysis.CubicSelect
KAM.Wave.Normal.Analysis.CubicTools
KAM.Wave.Normal.Analysis.EllSeq
KAM.Wave.Normal.Analysis.EvenMajorant
KAM.Wave.Normal.Analysis.Gradient
KAM.Wave.Normal.Analysis.PdeBase
KAM.Wave.Normal.Analysis.PdeConverse
KAM.Wave.Normal.Analysis.PdeForce
KAM.Wave.Normal.Analysis.PdeForward
KAM.Wave.Normal.Analysis.RealAlgebra
KAM.Wave.Normal.Analysis.SelectionRule
KAM.Wave.Normal.Analysis.SeqBridge
KAM.Wave.Normal.Analysis.SineProducts
KAM.Wave.Normal.Analysis.SineSeries
```

`M` was stored as one module per line in `.lake/abi-scratch/w0-modules.txt`; commands below ran from the audited worktree.

1. **Targeted build, exit 0:**

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpe $(cat .lake/abi-scratch/w0-modules.txt)
```

Final output: `Build completed successfully (3286 jobs).` Nonfatal warnings: four deprecated `if_pos`/`if_neg` uses in CubicSelect:159-160, one unused simp argument in CubicHeadline:70, and one implicitly referenced binder in PdeForward:83. No default-heartbeat failure. This is a targeted incremental/overlay build, not a rebuild from scratch.

2. **Kernel replay, one invocation, exit 0:**

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec leanchecker --verbose $(cat .lake/abi-scratch/w0-modules.txt)'
```

Output consisted of 18 `replaying KAM.Wave.Normal.Analysis.<Module>` lines, covering every requested module exactly once; no missing module or diagnostic. The first was `SineSeries`, the last `CubicAnalytic`.

3. **Fresh signature/body, composition, and all-public axioms probe, exit 0:**

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/W0Audit.lean'
```

Probe imports: CubicAnalytic, PdeForward, PdeConverse, SeqBridge. It issued `#print axioms KAM.Wave.<name>` for **every one of the 199 declarations** listed below, including every one of the 176 new public lemmas/theorems. Results: 189 declarations used `[propext, Classical.choice, Quot.sound]`; six used `[propext]`; two used `[propext, Quot.sound]`; two (`waveSignedEmb`, `waveSign`) used no axioms. No project axiom or `sorryAx` occurred in any axiom report.

Fresh explicit examples verified `reconU_eq_waveU`, `cubicGrad_eq_waveCubic`, the full frozen `IsClassicalSolution` iff explicit witnesses on univ, WaveEll iff IsEll, waveEllToLp=tauLp, and the real T bound with the independently written constant `waveAlgConst (p+1/2)^2 / Real.pi`. Further examples composed `waveCubicLp_apply` with the exact frozen cubicGrad bridge and instantiated real analyticity at an arbitrary lp point. The complete explicit source-facing types of `wave_coeff_to_pde` and `wave_pde_to_coeff` were copied into fresh examples and discharged solely by those exports with all explicit arguments in order; both elaborate.

Two intentional `#check_failure` checks on `waveTrilinear ... (fun _ => Complex.I)` and `waveSineSeries 0 (fun _ => Complex.I)` succeeded as negative checks. They printed `Type mismatch: Complex.I has type ℂ but is expected to have type ℝ`. The pretty-printer's recovery `sorry` inside those expected-failure diagnostic terms is not a declaration/proof hole; all 199 axiom reports were clean and the probe exited 0.

4. **Prescribed SLIM lint, exit 0:**

```sh
LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpe
```

Complete output:

```text
check_lean_modules: PASS (1704 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

There was no stale-root exception or substantive lint failure. The wrapper runs `nice -n 5 sh scripts/lint_sources.sh` with the approved build-artifact overlay; no direct unwrapped lint was run.

5. **Static and protected-path checks:** `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` had empty output. The entire three-dot diff contains 20 paths: these 18 Analysis modules (3119 physical lines total, maximum 335 in PdeConverse), the handoff, and an authorized generated `KAM/Root/Wave.lean` change consisting of exactly their 18 imports. No other production path changed. Each of the 18 files has the required copyright/module/public-import/module-doc/public-section format; definitions lie in exposed public noncomputable sections. A code-mask scan found zero prohibited tokens (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`) and zero resource-budget overrides in these modules. No provider, frozen theorem, or generated-root import occurs in their import closure; frozen imports are definitions. The live Wave manifest contains eleven SEALED definitions; `wave.nlw2.v1` remains DRAFT_SORRY and is not imported. `git diff --check` passed. Initial status was clean; final status contains only this untracked report. HEAD and inp hashes were rechecked unchanged.

Raw-log SHA256 receipts (logs captured in scratch during this turn; probe/scratch artifacts removed after extraction):

| Receipt | SHA256 |
|---|---|
| build | `71e61c966c84e08843d9b56c9ff78331e4b94b554ad7533e2c1aa8f3db0f59b7` |
| replay | `08507bfadcd0953e18ee8e475fa7421a59cd8c3b6fd33c42d9e646150b497473` |
| probe | `d8dedd98334601e91bc373f809b7e72b88ab054b3d46d93fb2f7493a73f0172b` |
| lint | `f8769443d8b80eea6897739b17e75d537bdf26bae7c49dcb873ca7397a1b474b` |


## Complete declaration inventory

One row for every new public declaration (176 lemmas/theorems and 23 definitions/abbreviations). Names below have namespace `KAM.Wave`. PASS means the actual helper statement/body is valid within its stated hypotheses, not that a larger complex source node is closed. Source-node verdicts above take precedence. Definitions are classified individually above; technical helper premises (summability, nonnegativity, evenness, polynomial bounds) are proved at the source-facing call sites and are not smuggled into their conclusions.

| Node / module | Declaration and locator | Verdict | Reason / scope |
|---|---|---|---|
| cubic-bound/analytic / CubicAnalytic | `wave_coeff_add` (CubicAnalytic.lean:31) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_coeff_smul` (CubicAnalytic.lean:35) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_fin3_ne_01` (CubicAnalytic.lean:39) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_fin3_ne_02` (CubicAnalytic.lean:41) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_fin3_ne_10` (CubicAnalytic.lean:43) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_fin3_ne_12` (CubicAnalytic.lean:45) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_fin3_ne_20` (CubicAnalytic.lean:47) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_fin3_ne_21` (CubicAnalytic.lean:49) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux` (CubicAnalytic.lean:56) | PASS | Literal helper; see definition classification. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_apply` (CubicAnalytic.lean:64) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_coeff_add_fun` (CubicAnalytic.lean:68) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `wave_coeff_smul_fun` (CubicAnalytic.lean:71) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_add_left` (CubicAnalytic.lean:74) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_add_mid` (CubicAnalytic.lean:82) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_add_right` (CubicAnalytic.lean:90) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_smul_left` (CubicAnalytic.lean:98) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_smul_mid` (CubicAnalytic.lean:105) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_smul_right` (CubicAnalytic.lean:112) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicAux_norm_le` (CubicAnalytic.lean:119) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicMultilinear` (CubicAnalytic.lean:136) | PASS | Literal helper; see definition classification. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicMultilinear_apply` (CubicAnalytic.lean:178) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicHeadlineConst_nonneg` (CubicAnalytic.lean:181) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicMultilinear_norm_le` (CubicAnalytic.lean:186) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicLp` (CubicAnalytic.lean:190) | PASS | Literal helper; see definition classification. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicLp_apply` (CubicAnalytic.lean:193) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicLp_norm_le` (CubicAnalytic.lean:198) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/analytic / CubicAnalytic | `waveCubicLp_analyticOnNhd` (CubicAnalytic.lean:205) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound / CubicBound | `waveTrilinear` (CubicBound.lean:35) | PASS WITH NOTES | Real specialization only; F1 blocks full complex node. |
| cubic-bound / CubicBound | `waveCubicConst` (CubicBound.lean:41) | PASS | Literal helper; see definition classification. |
| cubic-bound / CubicBound | `waveCubicConst_nonneg` (CubicBound.lean:43) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound / CubicBound | `wave_trilinear_pointwise` (CubicBound.lean:48) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound / CubicBound | `wave_trilinear_bound` (CubicBound.lean:140) | PASS WITH NOTES | Real specialization only; F1 blocks full complex node. |
| cubic-bound/headline / CubicHeadline | `waveCubicHeadlineConst` (CubicHeadline.lean:38) | PASS | Literal helper; see definition classification. |
| cubic-bound/headline / CubicHeadline | `wave_one_add_two_zeta_nonneg` (CubicHeadline.lean:40) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `waveAlgConst_three_halves_sq` (CubicHeadline.lean:46) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `waveCubicConst_one` (CubicHeadline.lean:55) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `waveEll_coeff` (CubicHeadline.lean:60) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `wave_lp_norm_eq_sqrt` (CubicHeadline.lean:68) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `norm_eq_waveEllNorm_coeff` (CubicHeadline.lean:72) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `wave_cubic_bound` (CubicHeadline.lean:82) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `cubicGrad_mem_ell` (CubicHeadline.lean:101) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/headline / CubicHeadline | `cubicGrad_norm_le` (CubicHeadline.lean:108) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveEll_add` (CubicLinear.lean:28) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveEll_smul` (CubicLinear.lean:35) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveHat_add` (CubicLinear.lean:40) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveHat_smul` (CubicLinear.lean:44) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `wave_trilinear_terms_summable` (CubicLinear.lean:49) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_add_left` (CubicLinear.lean:66) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_add_mid` (CubicLinear.lean:78) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_add_right` (CubicLinear.lean:90) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_smul_left` (CubicLinear.lean:104) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_smul_mid` (CubicLinear.lean:116) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_smul_right` (CubicLinear.lean:128) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveQuartic_comm12` (CubicLinear.lean:140) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveQuartic_comm23` (CubicLinear.lean:145) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_swap_left_mid` (CubicLinear.lean:151) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveTrilinear_swap_mid_right` (CubicLinear.lean:167) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/linearity / CubicLinear | `waveCubic_eq_trilinear` (CubicLinear.lean:183) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/selection / CubicSelect | `wave_summable_triple` (CubicSelect.lean:30) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/selection / CubicSelect | `waveSign_mul_inj` (CubicSelect.lean:45) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/selection / CubicSelect | `waveSignedEmb` (CubicSelect.lean:57) | PASS | Literal helper; see definition classification. |
| cubic-bound/selection / CubicSelect | `waveSignedEmb_injective` (CubicSelect.lean:61) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/selection / CubicSelect | `even_apply_waveSign` (CubicSelect.lean:71) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/selection / CubicSelect | `wave_selection_sum_le` (CubicSelect.lean:77) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / CubicTools | `wave_pnat_le_lam` (CubicTools.lean:26) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / CubicTools | `wave_ellWeight_add_half` (CubicTools.lean:31) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / CubicTools | `wave_ellWeight_sq_div_lam_le` (CubicTools.lean:38) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / CubicTools | `waveEvenAbs_weighted` (CubicTools.lean:47) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `WaveEll` (EllSeq.lean:34) | PASS | Literal helper; see definition classification. |
| recon-bounded / EllSeq | `waveEllNorm` (EllSeq.lean:38) | PASS | Literal helper; see definition classification. |
| recon-bounded / EllSeq | `waveEllMajorant` (EllSeq.lean:42) | PASS | Literal helper; see definition classification. |
| recon-bounded / EllSeq | `waveEllWeight_pos` (EllSeq.lean:45) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `waveEllNorm_nonneg` (EllSeq.lean:49) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `waveEllMajorant_nonneg` (EllSeq.lean:51) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `waveCauchySchwarz_tsum` (EllSeq.lean:54) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `waveEllWeight_inv_sq` (EllSeq.lean:68) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `summable_waveEllMajorant` (EllSeq.lean:86) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `waveEll_summable_pow_mul` (EllSeq.lean:91) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `waveEll_tsum_pow_mul_le` (EllSeq.lean:104) | PASS WITH NOTES | Real specialization only; F1 blocks full complex node. |
| recon-bounded / EllSeq | `waveEll_mul_poly` (EllSeq.lean:124) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / EllSeq | `memℓp_two_of_waveEll` (EllSeq.lean:161) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `waveEvenAbs` (EvenMajorant.lean:28) | PASS | Literal helper; see definition classification. |
| cubic-bound/majorant / EvenMajorant | `waveEvenAbs_nonneg` (EvenMajorant.lean:31) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `waveEvenAbs_zero` (EvenMajorant.lean:34) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `waveEvenAbs_neg` (EvenMajorant.lean:36) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `waveEvenAbs_pnat` (EvenMajorant.lean:39) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `w0a_conv_even` (EvenMajorant.lean:45) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `w0aHasSum_int_even_pnat'` (EvenMajorant.lean:55) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| cubic-bound/majorant / EvenMajorant | `w0aHasSum_int_even_pnat` (EvenMajorant.lean:65) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveHat` (Gradient.lean:44) | PASS | Literal helper; see definition classification. |
| gradient / Gradient | `waveU` (Gradient.lean:48) | PASS | Literal helper; see definition classification. |
| gradient / Gradient | `waveCubic` (Gradient.lean:52) | PASS | Literal helper; see definition classification. |
| gradient / Gradient | `waveG` (Gradient.lean:56) | PASS | Literal helper; see definition classification. |
| gradient / Gradient | `reconU_eq_waveU` (Gradient.lean:59) | PASS | Exact frozen-definition equation/equivalence. |
| gradient / Gradient | `cubicGrad_eq_waveCubic` (Gradient.lean:62) | PASS | Exact frozen-definition equation/equivalence. |
| gradient / Gradient | `waveU_eq_series` (Gradient.lean:66) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `wave_sqrt_lam_pos` (Gradient.lean:72) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `abs_waveHat_le` (Gradient.lean:75) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveEll_waveHat` (Gradient.lean:82) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `summable_abs_waveHat` (Gradient.lean:94) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveG_hasSum_of_summable` (Gradient.lean:105) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveCubic_hasSum_of_summable` (Gradient.lean:122) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveG_hasSum` (Gradient.lean:145) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveCubic_hasSum` (Gradient.lean:158) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `integral_waveU_cube_mul_sineMode` (Gradient.lean:168) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `waveCoordShift` (Gradient.lean:176) | PASS | Literal helper; see definition classification. |
| gradient / Gradient | `waveU_coordShift` (Gradient.lean:179) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `wave_hasDerivAt_integral_pow_four` (Gradient.lean:199) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `hasDerivAt_waveG_coord_of_summable` (Gradient.lean:240) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / Gradient | `hasDerivAt_waveG_coord` (Gradient.lean:267) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv/definitions / PdeBase | `waveV` (PdeBase.lean:37) | PASS | Literal helper; see definition classification. |
| pde-equiv/definitions / PdeBase | `reconV_eq_waveV` (PdeBase.lean:40) | PASS | Exact frozen-definition equation/equivalence. |
| pde-equiv/definitions / PdeBase | `waveEllToLp` (PdeBase.lean:45) | PASS | Literal helper; see definition classification. |
| pde-equiv/definitions / PdeBase | `waveEllToLp_apply` (PdeBase.lean:48) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv/definitions / PdeBase | `waveEllToLp_apply_div` (PdeBase.lean:52) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv/definitions / PdeBase | `IsClassicalSolutionWith` (PdeBase.lean:60) | PASS | Literal helper; see definition classification. |
| pde-equiv/definitions / PdeBase | `isClassicalSolution_iff_with_univ` (PdeBase.lean:73) | PASS | Exact frozen-definition equation/equivalence. |
| pde-equiv(ii) / PdeConverse | `waveParam_hasDerivAt` (PdeConverse.lean:33) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `waveHasDerivAt_sineMode` (PdeConverse.lean:92) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `waveHasDerivAt_sineMode_deriv` (PdeConverse.lean:101) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `waveSineMode_zero` (PdeConverse.lean:111) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `waveSineMode_pi` (PdeConverse.lean:113) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_integral_second_deriv_mul` (PdeConverse.lean:118) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_summable_abs_sqrtLam_mul` (PdeConverse.lean:167) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_coeff_integral_u` (PdeConverse.lean:174) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_coeff_integral_v` (PdeConverse.lean:179) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_converse_pointwise` (PdeConverse.lean:189) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_contDiffOn_one` (PdeConverse.lean:301) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(ii) / PdeConverse | `wave_pde_to_coeff` (PdeConverse.lean:310) | PASS | Classical PDE/velocity premises; coordinate C¹/system conclusions. |
| force / PdeForce | `waveEll_mono` (PdeForce.lean:31) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `waveEll_sub` (PdeForce.lean:42) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `wave_abs_lam_le` (PdeForce.lean:48) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `wave_abs_sqrt_lam_le` (PdeForce.lean:53) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `waveEll_lam_mul` (PdeForce.lean:60) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `waveEll_sqrtLam_mul` (PdeForce.lean:65) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `waveEll_waveCubic` (PdeForce.lean:70) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `summable_abs_sqrtLam_waveCubic` (PdeForce.lean:80) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| force / PdeForce | `wave_force_identity` (PdeForce.lean:87) | PASS WITH NOTES | Exact pointwise cubic force; uniform convergence assembled; N2. |
| pde-equiv(i) / PdeForward | `waveEll_neg` (PdeForward.lean:33) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `wave_sineModeIter_two` (PdeForward.lean:36) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `wave_sqrt_lam_inv_mul_lam` (PdeForward.lean:43) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `waveSeries_eq_inner` (PdeForward.lean:55) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `continuous_waveFeature` (PdeForward.lean:63) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `waveSeries_hasDerivAt` (PdeForward.lean:67) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `waveSeries_continuousOn` (PdeForward.lean:78) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `wave_pde_identity` (PdeForward.lean:88) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `waveU_eq_betaU_series` (PdeForward.lean:118) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `waveV_eq_betaV_series` (PdeForward.lean:123) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| pde-equiv(i) / PdeForward | `wave_coeff_to_pde` (PdeForward.lean:131) | PASS | Source continuity/Banach C¹/system premises; open-set strengthening. |
| algebra / RealAlgebra | `w0aL2` (RealAlgebra.lean:28) | PASS | Literal helper; see definition classification. |
| algebra / RealAlgebra | `w0a_twoWeight_neg` (RealAlgebra.lean:30) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| algebra / RealAlgebra | `w0aHasSum_int_even` (RealAlgebra.lean:34) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| algebra / RealAlgebra | `w0a_twoMem_ofReal` (RealAlgebra.lean:45) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| algebra / RealAlgebra | `w0a_twoNorm_ofReal` (RealAlgebra.lean:50) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| algebra / RealAlgebra | `w0a_conv_ofReal` (RealAlgebra.lean:55) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| algebra / RealAlgebra | `w0a_convAlgebra_nonneg` (RealAlgebra.lean:62) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| algebra / RealAlgebra | `w0a_summable_of_weighted` (RealAlgebra.lean:79) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| quartic selection / SelectionRule | `waveSign` (SelectionRule.lean:27) | PASS | Literal helper; see definition classification. |
| quartic selection / SelectionRule | `abs_waveQuartic_le_signs` (SelectionRule.lean:30) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| sequence transport / SeqBridge | `waveEll_iff_isEll` (SeqBridge.lean:28) | PASS WITH NOTES | Correct landed API bridge; N1. |
| sequence transport / SeqBridge | `waveEllNorm_eq_ellNorm` (SeqBridge.lean:37) | PASS WITH NOTES | Correct landed API bridge; N1. |
| sequence transport / SeqBridge | `waveEllToLp_eq_tauLp` (SeqBridge.lean:42) | PASS WITH NOTES | Correct landed API bridge; N1. |
| sequence transport / SeqBridge | `coeff_isEll_one_one` (SeqBridge.lean:49) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `waveQuartic` (SineProducts.lean:40) | PASS | Literal helper; see definition classification. |
| gradient / SineProducts | `wave_abs_sineMode_le` (SineProducts.lean:42) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `wave_continuous_sineMode` (SineProducts.lean:46) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `wave_sqrt_two_div_pi_sq` (SineProducts.lean:49) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `abs_waveQuartic_le` (SineProducts.lean:53) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `waveHasSum_mul_abs` (SineProducts.lean:77) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `waveHasSum_cube` (SineProducts.lean:89) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `waveHasSum_fourth` (SineProducts.lean:96) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `wave_summable_abs_mul_sineMode` (SineProducts.lean:108) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `hasSum_waveSineSeries_zero` (SineProducts.lean:116) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `continuous_waveSineSeries_zero` (SineProducts.lean:121) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `abs_waveSineSeries_zero_le` (SineProducts.lean:132) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `hasSum_integral_cube_mul_sineMode` (SineProducts.lean:139) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `summable_abs_cube_terms` (SineProducts.lean:185) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `hasSum_integral_fourth_pow` (SineProducts.lean:197) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| gradient / SineProducts | `summable_abs_fourth_terms` (SineProducts.lean:244) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries` (SineSeries.lean:47) | PASS WITH NOTES | Real specialization only; F1 blocks full complex node. |
| recon-bounded / SineSeries | `wave_abs_sineModeIter_le` (SineSeries.lean:50) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `wave_abs_mul_sineModeIter_le` (SineSeries.lean:57) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `summable_abs_waveSineSeries` (SineSeries.lean:64) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `summable_waveSineSeries` (SineSeries.lean:70) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_abs_le_of_summable` (SineSeries.lean:75) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_abs_le` (SineSeries.lean:88) | PASS WITH NOTES | Real specialization only; F1 blocks full complex node. |
| recon-bounded / SineSeries | `waveSineSeries_add` (SineSeries.lean:94) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_smul` (SineSeries.lean:102) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_tendstoUniformly` (SineSeries.lean:109) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `hasDerivAt_waveSineSeries` (SineSeries.lean:116) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `contDiff_waveSineSeries` (SineSeries.lean:135) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `iteratedDeriv_waveSineSeries` (SineSeries.lean:151) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_zero_eq` (SineSeries.lean:161) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_zero_apply` (SineSeries.lean:167) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveSineSeries_pi` (SineSeries.lean:172) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `waveHasSum_intervalIntegral` (SineSeries.lean:181) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `wave_integral_cos_int_mul` (SineSeries.lean:192) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `wave_integral_sineMode_mul_sineMode` (SineSeries.lean:201) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |
| recon-bounded / SineSeries | `integral_waveSineSeries_mul_sineMode` (SineSeries.lean:232) | PASS | Technical/source step with its stated domain; no source closure beyond node table. |

## Errata, deviations, and limits

No new suspected defect in the pinned published sources is asserted by this audit. The pre-existing errata are retained rather than independently revalidated from PDF images: `docs/tracks/W/errata-check-W0.md:134-143` quotes P96-W p.280's norm-one reconstruction bound and corrects it to √2 (E-W-N-1/N-1); `:152-157` quotes the missing minus sign on λ²q in the p.278 u_tt display (N-4). The package carries √2 in `waveEvenAbs_weighted`, uses the half two-sided norm in CubicBound, and uses the negative linear force. It does not silently revert either correction.

Valid strengthenings: arbitrary real p in the gradient/reconstruction results; all-real spatial uniform convergence; arbitrary open time sets instead of intervals; the cubic/gradient diagonal identification at any p for a>0. The unused continuity hypotheses in (i) remain source premises. Missing complex carriers (F1), remaining parallel sequence definitions (N1), and the non-exported standalone linear-force surface (N2) are implementation scope limits. The source mathematical complex extension may be true, but no exact exported Lean theorem in this package proves it. No repair was attempted in this report-only audit.

Closeout: complete the complex attachments before marking both affected full blueprint nodes proved. Preserve the passing real/PDE/frozen bridges and mechanical receipts. No W2/W3 consumer theorem, frozen nlw2 provider, or campaign theorem is certified here.
