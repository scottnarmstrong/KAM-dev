# W6 independent package audit 2

Overall source verdict: **PASS WITH NOTES** for the requested round-2 delta, including the full new `bpW:w6:tori` implementation. Round-1 findings F1, F2 and F3 are closed by unconditional exports with the literal blueprint weights and constants. No new blocking statement-fidelity defect was found. This package supplies no frozen theorem anchor or provider, so this is not a seal audit of `nlw2`.

## Scope and authority

Audited HEAD: `26a20671d8898e011a03e904e0f45bea332a819f`. Comparison `inp` at inspection: `5090562d4826c933407f5140aa2ea3e2fb32f5bc`. Read `git diff inp...HEAD`; the substantive scope is exactly `git diff 24c56b59..HEAD -- KAM/Wave/Iteration`: 13 modules, 1,174 insertions and 31 deletions. W5 and Assembly changes in the broader diff are excluded. Unchanged round-1 PASS material is retained without re-audit; existing declarations were read only as needed to trace the changed consumers.

The shared `inp` ref advanced during verification. The reproducible broad comparison is therefore `git diff 5090562d4826c933407f5140aa2ea3e2fb32f5bc...26a20671d8898e011a03e904e0f45bea332a819f`, whose merge base is `d3a2c262b6b99851b768298de443febdd8630cb5`. Later unpinned comparisons emitted a multiple-merge-base warning; they do not replace that initial comparison or the fixed tight delta.

Controlling documents: supplied AGENTS instructions and repository `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the external `inp-audit-package.md`, `W6-R2-handoff.md`, `W6-TORI-handoff.md`, `blueprint-W/parts/w6-iteration.tex`, and Track W conventions in `docs/tracks/W/W-STATEMENTS.md`. The generic `docs/tracks/W/statement.md` does not exist. The generic `W6-handoff.md` is absent from this checkout; read it with `git show inp-w6aud:docs/tracks/W/audits/W6-handoff.md`. Read round 1 with `git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md`. That report identifies its actual audited snapshot as `c3ce2152`, distinct from its producer's `24c56b59`; this audit uses the explicitly requested delta baseline. The round-2 focus supersedes the generic focus.

D53 and D60 were verified in `git show main:docs/DECISIONS.md` (main at inspection `4916704ee1a4ebebdf790449c0b74c4a1eef7a20`). All audit-owned Lean/Lake work is serial and capped at 4 GB, without swap, at nice 10 and one Lean thread. Only this report is a repository source edit; the temporary probe is confined to `.lake/abi-scratch/` and removed after checking. No state-changing git command was run.

## Closure of round-1 findings

**F1 — PASS.** `IterLemma.lean:226` defines `W6Stage.PsiN` from `(h.stageStepHyp hd hsmall).hyp.core.Psi`; `PhiN` uses the same core's `Phi`. `phiN_bounds` at line 237 and the transformation conjunct of `w6IterLemma` at line 352 exhibit both

```
PhiN(w) = w + iota(PsiN(w))
D PhiN(w) = I + iota o D PsiN(w).
```

The four nonnegative witnesses bound the lift itself and its derivative, including the parameter differences, with `A0 + lambda_nu A1 <= 2 MF_nu` and `B0 + lambda_nu B1 <= 16 MF_nu/sigma_nu <= 2^(-nu-2)`. The norm on the lift's `StepPhase r_nu` represents `p_+ = 3/2`; the domain represents `p = 1`. The explicit `stepEmbedCLM 1 1 (3/2)` identifies their roles rather than using an ambient norm to claim smoothing. W5's `StepCore.smooth_clause_v` supplies precisely the four bounds. The derivative and displacement identities attach them to the actual stage map. W5's `D_+` agrees with `D_(nu+1)` through the radius/strip recurrences. No `W6StepSmooth` premise remains in this result. The superseded ambient statement was removed, not relabelled as a source result.

**F2 — PASS.** `PrepShiftJ.lean:43`, `W6PrepHyp.shift_Omega_J`, bounds `normLab n * |w6Om7 (H.Om0 xi) n - omegaNor ...|`, with the full parameter-difference bound and `c0 + (alpha/M)c1 <= 3 epsilon`. Here `normLab n = n+3 = ((n.succPNat : real)+2)`, the correct Dirichlet label. `H.Om0` remains definitionally `H.prepStepHyp.hyp.core.OmegaPlus` (`PrepStep.lean:154`); it is not a new frequency. Read W5's consumed `StepOmegaBridge` interface: `core_OmegaPlus_eq` identifies that core output with the original `p+1` Taylor correction, and `OmegaPlus_tail_bound_J` / `OmegaPlus_tail_lip_J` prove its bounds. W6 uses those theorems with its existing split witnesses. No frequency equality or desired bound is added as a hypothesis. The unchanged half-weight export remains a weaker interface for existing consumers.

**F3 — PASS.** `FreqLipJ.lean:45`, `w6wavePairJ`, has the exact parameters `6*pi*gamma*alpha + 8*pi*epsilon0`, `3*gamma*alpha`, `4*epsilon0`, `theta`. It instantiates the previously checked `w6IsFreqPair_of_bounds` using the newly proved J-weighted preparatory bound and the existing iteration increments. `w6WaveFamilyJ` stores those constants, the same `waveD`, actual stage frequencies, and sequence cutoffs. `w6ExclusionJ` proves exclusion for this very family. The wrappers apply the proved reality clauses internally; no additional analytic dependency is assumed. The old D4 family is still exported, but is not used to certify the repaired literal constants. Downstream consumers must select the J family to obtain this exact source interface.

## Smoothing discharge and step-0 adaptation

`StepSmoothW5.lean` proves both universal smoothing contracts, with W5's actual `core.Psi` as witness. The derivative estimate is `8 M0/sigma <= 8 MF/sigma`, using `M0 + lambda M1 <= MF`, `lambda >= 0`, and `M1 >= 0`. The sharp displacement bound is `MF`, not `2 MF`. Neither proof adds an existence or bound hypothesis.

Every source-facing replacement listed in the producer handoff is present in `SmoothSrc.lean`. Each is the corresponding already checked conditional helper applied to `w6StepSmooth_holds` and/or `w6StepSmoothMod_holds`. Conditional helpers retain distinct names. Thus the discharge removes the analytic dependency rather than concealing it in a structure field, typeclass, or new source premise.

The code-only changes in `ComposeStep`, `PrepStep`, `StrongConj`, and the old part of `ToriPrep` replace positional projections of W5's extended conjunction with `stepTheorem_clauses` / `stepTheoremMod_clauses`. Their W6 theorem statements are unchanged. `StepSmooth` changes documentation only. The iter-lemma's new transformation statement is the separately reviewed F1 repair.

## Full audit of the new tori modules

The theorem `W6PrepHyp.w6Tori` (`Tori.lean:196`) has the actual action-angle input `w6InP`, `w6InX`, and holds for every starting size in the stated interval. Its additional parameter-domain hypotheses are W5 action-angle domain data, not desired torus conclusions. `w6PrepHyp_initial` derives the preparatory hypotheses from W5's initial perturbation with the complete `epsilon_in*(1+4 lambda/rho_xi) <= epsilon` bound. At a real parameter, its complex-neighbourhood hypothesis implies the displayed lower-action and upper-norm conditions by taking the neighbourhood centre. The ball smallness assumption is the blueprint's explicit `c_A(t+r^2) < rho1^2` condition and is also needed to type `X_K` and apply Gamma.

* **(i), PASS.** `w6TorusKam_aaDom` derives the action-angle square-root domain, in fact `Re(xi_i+y_i) > r^2`, from the already proved image in `D(s-4 sigma_P, 2 eta_P r)`, its inclusion in `D(1/8,r)`, and `xi_i >= 2r^2`. It also proves ball membership. Holomorphy follows by the chain rule on the open strip. Periodicity composes affine periodicity of the KAM map with periodicity of `aaMap`; realness uses `aaMap_real`. The normal-part witness `aaNormal V` at exponent `3/2` maps through `birkEmbed 1 (3/2) 1`, so the extra half derivative is represented literally.
* **(ii), PASS.** Joint continuity has domain `PiStar × R^2` in the correct parameter-angle order. The intermediate map lands in `aaDomJ`, proved from the preceding domain result. `nu_*` is the actual limit frequency divided by `2*pi`; the Lipschitz proof uses `(N_A+theta)/(2*pi)` (represented by `Real.toNNReal`), without assuming continuity or a Lipschitz conclusion as input.
* **(iii), PASS.** The source-facing invariance result specializes `P,X` to the W5 input Hamiltonian. `aaXN_ofReal_eq_stepXN` identifies the unperturbed fields, including the normal-frequency indexing and signs. `kamHomEmbed_stepRhoK` proves that W5's reweighted input field and the original `aaXP` are the same vector in `p-1`; it does not assert equality in the wrong weight. `birkEmbed_aaDer` commutes the action-angle derivative with the weight inclusion. The chain rule, unconditional KAM invariance, and `aaConjugacy` give exactly `X_Lambda + iota(X_Gbar + X_Gnor + X_K)` in Birkhoff `p-1` coordinates. The stronger intermediate result holds on all `T_(s0/2)`. The final real-angle statement takes ball membership as typing data for `birkXK`; clause (i) supplies that proof, so it is not an unpaid analytic hypothesis.
* **(iv), PASS.** `V` is a smoothing representative in `Phi_P Phi_* theta = iota theta + iota V`; unpacking `kamNorm r V <= e_tor` gives the three exact component bounds. The tangential formula uses the unchanged action components and angle `theta_i+V.angle_i`, with the signs and `2*pi` factor from `aaMap`. The normal Birkhoff bound follows from `aaNormal_norm_le` and contraction of the weight embedding. The constant is the sharp `MF_P + ePhi`, without a factor of two on the preparatory contribution.
* **(v), PASS.** `Gamma_1` is differentiated on `B_rho1` by the W3 derivative at the larger `B_rho0`; the real derivative is the restriction of a complex-linear map, so the complex differentiability inference is justified. `birkGamma_one_fixed` and `exists_birkZ_of_birkRho_eq` prove that `birkZinv Gamma_1 Psi` is a complexification of a real `WaveSpace` vector. Consequently the `reWave` in the final analytic map selects the actual real vector, not a projection used to avoid proving reality. Unit periodicity is extended to all integer vectors before applying `torus_analytic`. The fixed carrier `WaveSpace` is the prescribed weighted-coordinate realization at `a=p=1`.

All strip restrictions are justified by `s0/2 < sInfty = 3s0/4`; `w6WaveSeq.s0 = w6S0` is definitional. No embedding, parameter-family injectivity, Cartesian coefficient dynamics, or frozen headline closure is claimed here; those are subsequent W3/W8 consumers beyond this delta's tori clauses.

## Declaration verdicts

Names below are in `KAM.Wave`; `H.` denotes namespace `W6PrepHyp`. PASS is for the indicated source node or helper, not a frozen seal.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| iter-lemma arithmetic helper | `W6Stage.w6_iter_one_le_three_halves` | PASS | Literal numerical comparison for the embedding. |
| actual stage smoothing lift | `W6Stage.PsiN` | PASS | Same W5 core as `PhiN`; see definition classification. |
| iter-lemma transformations | `W6Stage.phiN_bounds` | PASS | F1 closed, including both Lipschitz bounds. |
| iterative lemma | `W6Stage.w6IterLemma` | PASS | Repaired transformation conjunct; other clauses retained. |
| W5 derivative bound | `StepCore.fderiv_psi_le_MF` | PASS | Monotonicity from W5 flow bound. |
| unmodified smoothing | `w6StepSmooth_holds` | PASS | Actual `core.Psi`, sharp sup bound. |
| modified smoothing | `w6StepSmoothMod_holds` | PASS | Actual modified `core.Psi`, same argument. |
| source iteration hypothesis | `w6IterHyp_src` | PASS | Applies proved smoothing contract. |
| convergence (iii) | `w6ConvTorus` | PASS | Unconditional source wrapper. |
| convergence (iv) | `w6ConvOpsSrc` | PASS | Unconditional source wrapper. |
| invariance | `w6Invariance` | PASS | Unconditional source wrapper. |
| prep-step (iii), sharp | `H.phiP_sharp` | PASS | Sharp smoothing lift; dependency discharged. |
| preparatory map properties | `H.prepK_props` | PASS | Same helper conclusion, dependency discharged. |
| tori in KAM coordinates | `H.w6ToriKam` | PASS | Both smoothing dependencies discharged. |
| prep-step (ii) | `H.shift_Omega_J` | PASS | F2 closed on the actual `H.Om0`. |
| freq-lip | `H.w6wavePairJ` | PASS | F3 closed; literal three frequency envelopes. |
| admissible wave family | `H.w6WaveFamilyJ` | PASS | Same domains, frequencies and cutoffs; exact constants. |
| exclusion | `H.w6ExclusionJ` | PASS | Exclusion for the J family itself. |
| field identification | `aaXN_ofReal_eq_stepXN` | PASS | Exact real-frequency unperturbed field. |
| modified-field weight transport | `kamHomEmbed_stepRhoK` | PASS | Coefficientwise equality in `p-1`. |
| derivative weight transport | `birkEmbed_aaDer` | PASS | Both tangential and normal coordinates checked. |
| normal-part weight transport | `aaNormal_kamHomEmbed` | PASS | Exact normal coordinates; tangential entries vanish. |
| torus normal part | `aaNormal_w6TorusPt` | PASS | Zero normal coordinates of inclusion. |
| periodicity helper | `w6_periodic_zsmul` | PASS | Positive and negative integer induction stays in domain. |
| action-angle input | `w6InP` | PASS | Actual W5 input scalar Hamiltonian. |
| action-angle input field | `w6InX` | PASS | Actual W5 `aaXP`. |
| initial-to-preparatory bridge | `w6PrepHyp_initial` | PASS | Source smoothing, periodicity, reality and full size bound. |
| weight contraction | `norm_homEmbed_gen_apply_le` | PASS | Operator-norm bound at the stated ordered exponents. |
| strip translation | `w6_strip_add_single` | PASS | Real translation preserves imaginary parts. |
| strip inclusion | `w6_strip_half_subset` | PASS | Correct `3s0/4` limit strip. |
| real-angle inclusion | `w6_real_mem_strip_half` | PASS | Positive half strip, zero imaginary coordinates. |
| joint continuity helper | `w6_continuousOn_aaMap_comp` | PASS | Explicit domain mapping into `aaDomJ`. |
| Birkhoff torus | `H.w6TorusBk` | PASS | Literal `aaMap` composed with KAM torus. |
| wave limit frequency | `H.w6OmStarW` | PASS | Same actual starting state and limit as iteration. |
| period-one frequency | `H.w6NuStar` | PASS | Division by `2*pi`. |
| parameter inclusion | `H.mem_of_mem_wavePiStar` | PASS | Stage-zero membership implies preparatory good set. |
| action-angle domain | `H.w6TorusKam_aaDom` | PASS | Domain and ball conclusions proved from source bounds. |
| tori (i) | `H.w6TorusBk_hol` | PASS | Holomorphy, ball, periodicity, reality, smoothing. |
| tori (ii), continuity | `H.w6TorusBk_cont` | PASS | Full product with real angles. |
| tori (iv) | `H.w6TorusBk_close` | PASS | Exact component bounds and coordinate formula. |
| numerical helper | `w6_half_le_one` | PASS | Literal comparison for W3/W5 parameters. |
| strip translations both signs | `w6_strip_sub_single` | PASS | Applies real-translation lemma with `1` and `-1`. |
| tori (ii), frequency | `H.w6NuStar_lipschitz` | PASS | Actual limit; scale `1/(2*pi)`. |
| tori (iii), stronger strip form | `H.w6TorusBk_invariance_strip` | PASS | Actual full Hamiltonian field in `p-1`. |
| tori (v) | `H.w6TorusBk_analytic` | PASS | Gamma transport, proven reality, W1 analyticity. |
| tori (i)–(v) | `H.w6Tori` | PASS | Assembles exactly the five proved clauses. |
| unchanged statements, step-0 projections | `ComposeStep`, `PrepStep`, `StrongConj`, old `ToriPrep` declarations | PASS | Only W5 conjunction accessor changes; no statement drift. |
| dependency documentation | `StepSmooth` | PASS | No code change; discharge documented. |

## Definitions, hypotheses and carriers

Every added explicit definition is classified here; no new structure, abbreviation or instance is introduced by the delta.

| Definition | Classification and carrier check |
|---|---|
| `W6Stage.PsiN` | Actual W5 smoothing displacement of the actual stage map. No fallback added. Its `p_+` interpretation is attached by the explicit embedding and theorems. |
| `W6PrepHyp.w6WaveFamilyJ` | Constructed admissible family, not assumed admissibility. Stores the actual stage functions and exact source constants. |
| `w6InP` | W5's `aaPfun` at `aaOfReal xi`, `a=p=1`. No surrogate Hamiltonian. |
| `w6InX` | W5's `aaXP` for the same parameters and exponent; W5's modified field reweighting is handled explicitly by a bridge. |
| `W6PrepHyp.w6TorusBk` | Composition `aaMap 1 1 (aaOfReal xi) (H.w6TorusKam epsilon0 theta xi)`. A total function; its torus properties are asserted only on the proved good set and strip with domain hypotheses. No off-domain fallback is used as evidence. |
| `W6PrepHyp.w6OmStarW` | The existing iteration's `w6OmStar` at the exact wave starting data. As with the round-1 limit definition, convergence meaning is restricted to the good set. |
| `W6PrepHyp.w6NuStar` | Componentwise `w6OmStarW/(2*pi)`; nonzero denominator is the fixed positive real constant. |

The carried source hypotheses in `W6ConvHyp`, `W6PrepHyp`, and the W5 contracts are unchanged. The new source wrappers prove their helper dependencies. Tori invariance specializes to the actual Hamiltonian input; the more general holomorphy/continuity/closeness/analyticity helpers correctly work for any preparatory Hamiltonian satisfying the source assumptions. No conclusion-shaped hypothesis was found. The typing proof for `birkXK` is supplied by a separately proved clause of the same theorem.

## Mechanical checks

The launcher-provided kernel replay and short-name checks are not visible in this audit history. They were not rerun; **no independently observed replay exit code or launcher name-check output is claimed**. The checks below are independently run and do not substitute for those unseen logs. Provider/type and seal-body probes are inapplicable because no anchor is sealed by W6.

Commands, results, axiom inventory and audited byte hashes follow below.

## Source defects, deviations and limits

No new suspected pinned-source or blueprint defect was found in the reviewed delta. The existing round-1 note about blueprint `stepW:w6:il-div` attributing a Dirichlet-weight conclusion directly to W5 is unchanged and outside this delta; the retained direct W6 perturbation argument remains the recorded explanation. This audit introduces no source or theorem deviation.

The tori implementation makes the W5 action-angle domain requirements explicit, uses ball membership as typing data where required, proves stronger strip invariance before restricting to real angles, and realizes `E_(1,1)` in weighted coordinates as specified by the blueprint. These are faithful elaborations, not extra desired conclusions assumed as hypotheses. The old half-weight and D4 APIs are still present for compatibility; only the J APIs certify the repaired literal source conclusions. This audit does not assert that every downstream W8 consumer has switched APIs.

The upstream W5, W3 and W1 interfaces were inspected at the points used here, without reopening their separate package audits. Unchanged round-1 PASS material is not newly certified. Frozen headline closure, W8 embedding and family injectivity, and unseen launcher replay logs remain outside this report's independent certification scope.

## Independent check receipts

All commands were run from `/root/code/KAM-inp-wpj`. The cap prefix used directly and by the build driver is:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

### Lint

Exact invocation (the outer scope also caps any ABI subprocesses of the prescribed lint wrapper):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpj > /tmp/w6-r2-lint.log 2>&1
```

Exit **0**. Complete diagnostic output:

```text
check_lean_modules: PASS (4024 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

### Targeted builds

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpj KAM.Wave.Iteration.Tori KAM.Wave.Iteration.FreqLipJ > /tmp/w6-r2-build.log 2>&1
```

This driver waits for the memory floor and a compile slot, then runs each target separately and serially as `<cap-prefix> lake build <target>`. It acquires the W capped compile slots; no plain library/application build was requested. Exit **0**. Result lines:

```text
[w_build] slot 3: KAM.Wave.Iteration.Tori (09:29:23)
Build completed successfully (3745 jobs).
[w_build] slot 3: KAM.Wave.Iteration.FreqLipJ (09:29:27)
Build completed successfully (3491 jobs).
```

These two targeted import closures contain all 13 audited modules. Cached upstream jobs replayed pre-existing warnings, including deprecations and unused tactics/variables in Homological and KamStep dependencies. No warning names an `Iteration` source file. Lake's word `Replayed` here refers to cached job diagnostics; this is not an independently run `leanchecker` kernel replay.

### Axioms and family identity probe

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/W6R2Audit.lean > /tmp/w6-r2-axioms-final.log 2>&1
```

Exit **0**, no diagnostics other than the 46 axiom lines below. The probe imported `KAM.Wave.Iteration.Tori` and `KAM.Wave.Iteration.FreqLipJ`, printed every added explicit public declaration's axioms and both revised main iteration statements, and checked by `rfl` that `w6WaveFamilyJ` has `epsilon1 = 3*gamma*alpha`, `epsilon2 = 4*epsilon0`, `D = waveD epsilon0`, and `omega = fun nu => (waveSeq epsilon0 nu).om`. All 46 requested axiom rows were present: 45 standard triples and one `[propext]` subset. The initial invocation of the same probe exited 1 solely because it requested the numeric helper under `KAM.Wave` rather than its actual `KAM.Wave.W6Stage` namespace; the corrected invocation above passed without any implementation change. The temporary probe was deleted after verification.

```text
'KAM.Wave.StepCore.fderiv_psi_le_MF' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6StepSmooth_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6StepSmoothMod_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6IterHyp_src' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6ConvTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6ConvOpsSrc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6Invariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.phiP_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.prepK_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6ToriKam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.shift_Omega_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6wavePairJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6WaveFamilyJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6ExclusionJ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaXN_ofReal_eq_stepXN' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.kamHomEmbed_stepRhoK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.birkEmbed_aaDer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaNormal_kamHomEmbed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.aaNormal_w6TorusPt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_periodic_zsmul' depends on axioms: [propext]
'KAM.Wave.w6InP' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6InX' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6PrepHyp_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_homEmbed_gen_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_strip_add_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_strip_half_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_real_mem_strip_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_continuousOn_aaMap_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusBk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6OmStarW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6NuStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.mem_of_mem_wavePiStar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusKam_aaDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusBk_hol' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusBk_cont' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusBk_close' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_half_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w6_strip_sub_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6NuStar_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusBk_invariance_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6TorusBk_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6PrepHyp.w6Tori' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6Stage.w6_iter_one_le_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6Stage.PsiN' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6Stage.phiN_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.W6Stage.w6IterLemma' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Static checks and protected paths

* `git diff --check 24c56b59..HEAD -- KAM/Wave/Iteration`: exit **0**, no output.
* `git diff --check 5090562d4826c933407f5140aa2ea3e2fb32f5bc...26a20671d8898e011a03e904e0f45bea332a819f -- KAM/Wave/Iteration`: exit **0**, no output.
* `git diff 5090562d4826c933407f5140aa2ea3e2fb32f5bc...26a20671d8898e011a03e904e0f45bea332a819f -- KAM/Frozen manifest KAM.lean README.md`: exit **0**, empty. The generated `KAM/Root/Wave.lean` differs in this broad comparison; no claim is made that all generated-root bytes are unchanged. It is outside the named 13-module delta and was not edited by this audit.
* A Python static scan using `scripts/check_lean_modules.py`'s comment/string masker over the exact 13 delta files found no forbidden proof escapes, resource overrides, `EuclideanSpace`, or direct frozen/provider/root/Assembly imports: **PASS**.
* Audited source total: **2,708 lines**, maximum **392** (`IterLemma`), below the 1,500-line cap. Module structure/exposure checks pass through the prescribed lint.

## Audited module bytes

Hashes identify the source bytes read at HEAD, not a claim of a standalone kernel replay certificate.

| Module (`KAM.Wave.Iteration.*`) | Lines | SHA-256 |
|---|---:|---|
| `ComposeStep` | 354 | `ad238cd927c3b7de6073004abce122ccc0387a6392412da95f4d5135c98e5856` |
| `FreqLipJ` | 126 | `03533fe08402c50bee4a629155a49c1d132c3cba75cc911888fada5aed3baa57` |
| `IterLemma` | 392 | `a42a24786c9f370a21f7a94d673a6ac2eb563aa5b8b5ba32c9a8d775fe318df2` |
| `PrepShiftJ` | 68 | `78543c59dfd08cb5bb2deb04b233222f2cbf2ed8e7b1dbd1e4639fb1411a72d9` |
| `PrepStep` | 279 | `698a238e869abde5422e00a7b225b64f09ea9029fe08cfda5beb78d6e765fbb2` |
| `SmoothSrc` | 167 | `4b486ba831ab5c741b4e88d31eb9db2659a9d69eab2d2a53c119b79f6ce19cbd` |
| `StepSmooth` | 168 | `ea2321d45b79f156ff8059b95f45a3a9ab49dea650524ce2c0fa2d5e69090738` |
| `StepSmoothW5` | 68 | `4e5f8f188341b9783db5522e1333e6bbbdde39d98a50df114b513b3a951d1a0f` |
| `StrongConj` | 114 | `b1020856dee62f331518bae7d4c5e21c9839382c793ef55552f493dc571ebaa7` |
| `Tori` | 245 | `7e36727805afaab215078795ebefd69e14143e98379f1591f2cccf9976685655` |
| `ToriBk` | 282 | `13c502b9f4fb329f8ae3c2802e2e5f994013f47e9d660e4e104358ff786d88f0` |
| `ToriBridge` | 157 | `92dacb0f8caf916a2a258ab6df188ebe9079be09ef25806b700527c29e90b933` |
| `ToriPrep` | 288 | `fd8e109649bdfa00ccc37b05c92d39b04d7d66d7d2ed5841836a110d3f1be482` |
