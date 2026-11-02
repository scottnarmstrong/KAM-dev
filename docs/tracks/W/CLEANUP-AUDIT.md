# Track W clean-up audit (report only)

Scope: the 456 files, 84,252 lines, 5,065 declarations under `KAM/Wave/**` on branch `w-cleanup-audit` (off `main`). No `.lean` file was edited and nothing was built. `KAM.Wave.nlw2` and everything under `KAM/Frozen/**` and `KAM/Provider/**` are out of the findings but count as users. All counts come from Python scans of the source text and are **heuristic** (see each section).

## Summary

| # | Category | Count | Est. diff if acted on |
|---|---|---|---|
| 1 | Dead code, deletion candidates (name appears on no other line of any `.lean` file; not graph-cited; no implicit-use attribute) | 150 decls in 84 files | about 815 lines removed |
| 1b | Dead but carry `@[simp]`/instance (implicit use, do not delete blindly) | 22 | 0 (review only) |
| 1c | Graph-cited but otherwise unused (blueprint-facing, keep) | 130 decls | 0 (keep) |
| 2 | Leftover conditional-helper names (`_of_stepSmooth/_pieces/_eps0_pos/_bounds/_shift/_initial/_stepReal/_gates`) | 38 names, all still used; 35 files carry "conditional helper" docstrings (71 lines) | about 75 docstring lines reworded; renames would touch about 145 lines |
| 3 | Stale or campaign-jargon comments (excluding valid `stepW:`/`bpW:` labels) | 790 lines in 448 files (440 are two boilerplate sentences); 0 dangling `bpW:` labels | about 790 lines edited, 440 of them deleted by two `sed` patterns |
| 4 | Naming problems vs Mathlib | 300 names in targeted patterns; 2,559 names under systematic campaign prefixes | targeted renames about 3,300 lines; prefix/namespace migration about 21,600 lines (about 26% of the track) |
| 5 | Files over 1000 lines / over 1500 lines | 0 / 0 (max 824) | none |
| 6 | Duplicate lemmas | 16 identical-signature theorem groups (33 decls), about 10 genuine near-duplicates; 12 same-name cross-namespace pairs that are structural parallels | about 40 lines removed/merged |

Recommended order: (3) comments, (2) docstring wording, (1) dead code, (6) duplicates, (4) targeted renames, then decide separately on (4) prefix migration. Details at the end.

## 1. Dead code

Method: scanned every `theorem/lemma/def/abbrev/structure/class/instance/inductive` header under `KAM/Wave` (5,065; namespaces tracked via `namespace`/`end`), took the last name component, and counted whole-token occurrences of that component (as a last dotted component, so `H.name`, `.name`, `Full.Name` and bare `name` all count) over all 4,431 `.lean` files under `KAM/`, comments and docstrings included. A name is "dead" if the only occurrence is its own declaration. Caveats: same last component in two places hides deadness (each counts as a use of the other); names used only in comments count as used; generated names (`foo.eq_1`, `_def`), implicit use by `simp`/instance resolution and `to_additive`-style aliasing are invisible to it. Method on strictly code-only text (comments stripped) gives 526 dead of which 321 are graph-cited, so 205 non-graph; the 33 extra non-graph names are mentioned only in comments or docstrings and are not in the lists below.

Totals: 302 dead names by the primary rule = 130 graph-cited (section 1c) + 22 implicit-use (1b) + 150 deletion candidates (1a).

Per directory (declarations / deletion candidates / dead-implicit-use / graph-cited-only):

| Directory | Decls | Candidates | Implicit-use | Graph-cited |
|---|---|---|---|---|
| Homological | 794 | 34 | 1 | 24 |
| Birkhoff | 924 | 24 | 2 | 42 |
| KamStep | 1033 | 19 | 12 | 1 |
| Iteration | 540 | 18 | 0 | 6 |
| Assembly | 263 | 17 | 0 | 2 |
| Cubic | 240 | 13 | 0 | 7 |
| Normal | 349 | 6 | 0 | 1 |
| KamSupport | 134 | 5 | 1 | 1 |
| Measure | 272 | 5 | 0 | 12 |
| Seq | 149 | 3 | 2 | 8 |
| Analytic | 121 | 2 | 4 | 10 |
| Recon | 87 | 2 | 0 | 2 |
| Recon2 | 69 | 1 | 0 | 4 |
| Algebra | 90 | 1 | 0 | 10 |
| total | 5065 | 150 | 22 | 130 |

Kinds among the 150 candidates: 131 theorem, 11 lemma, 6 abbrev, 2 def. Median candidate spans 3 lines (docstring plus statement), longest 34; total about 815 lines. Removing them may in turn orphan their own dependencies (second pass needed).

### 1a. Top 40 files by deletion candidates (file: count; names)

- `KAM/Wave/Homological/PPlusOne.lean` (14): homNormEntryCLM:48, homLamD:50, homLamDiag:52, homPairRep:58, homPairOmegaRaw:100, homLemma1_lipschitz_of_gates:141, norm_homLamD_mul_le:159, homLemma1_equation_all_of_gates:167, homLemma1_fieldBound_of_gates:242, homLam_comm_homTQ:250, homLemma1_zero_modes:268, homEq_Q:314, homLipField_dQ:326, homLemma_lie_iv:351
- `KAM/Wave/Assembly/Ext.lean` (10): w8ext_summable_abs_mul:58, w8ext_tsum_add:63, w8ext_antitoneOn_Icc:75, w8ext_monotoneOn_Icc:85, w8ext_hasDerivAt_exp_mul:95, w8ext_rpow:196, w8ext_rpow_le_rpow:202, w8ext_clm_comp_analyticOnNhd:228, w8ext_fderiv_clm_comp:235, w8ext_le_of_tendsto:242
- `KAM/Wave/Birkhoff/MainBall.lean` (6): isBirkExtension_restrict:42, birkPsi_embed:132, birkXi_embed:137, birkAF_eq:143, birkAF_eq_birkGammaDPlus:161, birkK2_rho:198
- `KAM/Wave/KamStep/TaylorData.lean` (4): tB_differentiableOn:72, tCp_differentiableOn:79, tCm_differentiableOn:84, tBlock_differentiableOn:94
- `KAM/Wave/Cubic/SelectionTwoAlg.lean` (4): waveSelTwo_smul_mid:127, waveSelTwo_smul_right:134, waveSelTwo_add_mid:151, waveSelTwo_add_right:161
- `KAM/Wave/Cubic/SelectionOneSided.lean` (4): waveSelSum_smul_mid:235, waveSelSum_smul_right:241, waveSelSum_add_mid:256, waveSelSum_add_right:265
- `KAM/Wave/Birkhoff/Space.lean` (4): birkCoord_sub:89, birkCoord_neg:93, birk_hasSum_split:122, birkRho_injective:261
- `KAM/Wave/Assembly/UpstreamW6.lean` (4): w8Upstream_gam:40, w8Upstream_gam1:42, w8Upstream_cF:44, w8Upstream_cFnat:46
- `KAM/Wave/KamStep/StepReweightTaylor.lean` (3): tQt_rhoK:130, stepTaylorRho_b:166, stepTaylorRho_a0:169
- `KAM/Wave/Birkhoff/Coords.lean` (3): birkZEquiv_apply:297, birkZEquiv_symm_apply:299, norm_le_sqrt_two_mul_birkZinv:302
- `KAM/Wave/Homological/ModifiedReal.lean` (3): homModSolveTaylor_cm:64, homModSolveTaylor_P':82, homMelnikovMod_of_melnikov:230
- `KAM/Wave/Iteration/Sequences.lean` (3): sigma_zero:202, KNu_pos:361, eps_succ_eq_kappa:365
- `KAM/Wave/KamStep/ExportFlowCore.lean` (2): stepDomain_U_add_int:64, PsiT_one:89
- `KAM/Wave/KamStep/StepReweight.lean` (2): stepZ_comp_stepRhoK:71, stepZb_comp_stepRhoK:75
- `KAM/Wave/Recon/ReconAnalytic.lean` (2): reconUIterCLM_apply:149, reconVIterCLM_apply:152
- `KAM/Wave/Birkhoff/MainYInt.lean` (2): norm_birkGammaDPlusInv_le:204, birkGammaD_embed_birkGammaDPlusInv:217
- `KAM/Wave/Birkhoff/BlockMap.lean` (2): blockMap_const:60, norm_blockMap_le:65
- `KAM/Wave/Assembly/ShellGeom.lean` (2): w8Pi_measurableSet:77, w8Pi_subset_shellInner:148
- `KAM/Wave/Homological/Schur.lean` (2): homKS_lt:47, ellWeight_succ_exponent:202
- `KAM/Wave/Homological/RealSolve.lean` (2): homMultDm_conj:92, homDP'_conj:106
- `KAM/Wave/Homological/LemmaOneAll.lean` (2): homPairRep_eq'_gen:33, one_le_homWt:104
- `KAM/Wave/Homological/ModifiedReweight.lean` (2): norm_homModRhoL_apply_le:59, homDualNorm_rho:108
- `KAM/Wave/Seq/Flow.lean` (2): flowCLM_zero:187, coeffW_flow_snd:220
- `KAM/Wave/Iteration/ConvTorus.lean` (2): w6TorusCLM_apply:53, isClosed_stepReal:62
- `KAM/Wave/Iteration/Params.lean` (2): w6PiStar_subset:63, w6Zone_subset:100
- `KAM/Wave/Iteration/ComposeStep.lean` (2): domNu_anti:99, w6Field_irrel:278
- `KAM/Wave/Measure/MinusSum.lean` (2): isLam_neg:35, measXSet_neg_iff:51
- `KAM/Wave/Measure/Measure.lean` (2): melnikov_prep_zero:172, melnikov_iter:189
- `KAM/Wave/Analytic/ComplexificationCommute.lean` (1): coeffW_weightedDiagCLM:107
- `KAM/Wave/Analytic/Flow/Picard.lean` (1): continuousOn_X:84
- `KAM/Wave/KamSupport/FourierBessel.lean` (1): norm_kamChi:56
- `KAM/Wave/KamSupport/Lattice.lean` (1): kamLattice_const_nonneg:161
- `KAM/Wave/KamSupport/LatticeCount.lean` (1): kamLatticeCode_injective:55
- `KAM/Wave/KamSupport/SchurTest.lean` (1): bound_mono:41
- `KAM/Wave/KamSupport/KamSpace.lean` (1): kamOpNorm_nonneg:123
- `KAM/Wave/KamStep/NewHamTransport.lean` (1): transSolve_unique:80
- `KAM/Wave/KamStep/ParamIntegral.lean` (1): riemannSum_add:153
- `KAM/Wave/KamStep/StepPlus.lean` (1): stepZF:34
- `KAM/Wave/KamStep/TaylorEst.lean` (1): norm_kamToStep:50
- `KAM/Wave/KamStep/RealFlowPicard.lean` (1): stepRealFun_apply:98

44 further files hold 44 candidates (1 each or fewer).

### 1b. Dead but with implicit-use attributes (review, not delete)

lpPointwise_apply (`Analytic/ComplexificationLp.lean:40`), reLp_apply (`Analytic/ComplexificationLp.lean:67`), conjLp_apply (`Analytic/ComplexificationLp.lean:70`), conjLp_conjLp (`Analytic/ComplexificationLp.lean:96`), kamSchurCLM_apply (`KamSupport/SchurTest.lean:171`), factRealZeroLtOne (`KamStep/TaylorFieldRv.lean:32`), toK_add (`KamStep/Phase.lean:44`), toK_smul (`KamStep/Phase.lean:45`), toK_zero (`KamStep/Phase.lean:46`), toK_neg (`KamStep/Phase.lean:47`), stepPhaseNormed (`KamStep/Phase.lean:86`), stepPhaseNormedSpace (`KamStep/Phase.lean:92`), stepPhaseComplete (`KamStep/Phase.lean:144`), aaShift_apply (`KamStep/ActionAngle.lean:136`), scaleS_one (`KamStep/TaylorScale.lean:34`), scaleT_one (`KamStep/TaylorScale.lean:35`), aaUnshift_apply (`KamStep/ActionAngleDeriv.lean:229`), lpDiagCLM_apply (`Birkhoff/Space.lean:167`), birkPiEquiv_apply (`Birkhoff/Reindex.lean:29`), homPolyPrY_apply (`Homological/CompleteLieCont.lean:122`), coeffW_neg (`Seq/Transport.lean:125`), coeffWCLM_apply (`Seq/Transport.lean:194`)

### 1c. Graph-cited but otherwise unused (130; blueprint-facing exports, do NOT delete)

Matched by full name against `LEAN_REF:` fields of `docs/graph/W/packets/*.nodes.md` (1,826 distinct refs). Concentrated in Birkhoff (42), Homological (24), Measure (12), Analytic (10), Algebra (10), Seq (8), Cubic (7), Iteration (6). Sample (first 60 by file):

- `Algebra/Extension.lean:138` waveExt_add
- `Algebra/Extension.lean:145` waveExt_smul
- `Algebra/Extension.lean:315` waveJ_add
- `Algebra/Extension.lean:322` waveJ_smul
- `Algebra/Extension.lean:349` wave_J_norm_le
- `Algebra/TwoSided.lean:127` waveTwoMem_of_lp
- `Algebra/TwoSided.lean:251` wave_conv_summable
- `Algebra/TwoSided.lean:261` wave_conv_assoc_of_mem
- `Algebra/Young.lean:129` wave_young_sqrt_le
- `Algebra/Young.lean:184` waveConv_mono
- `Analytic/ComplexificationCommute.lean:69` complexifyLp_tauLp
- `Analytic/ComplexificationCommute.lean:74` reLp_tauLp
- `Analytic/ComplexificationCommute.lean:78` conjLp_tauLp
- `Analytic/ComplexificationCommute.lean:88` weightedDiagCLM_complexifyLp
- `Analytic/ComplexificationCommute.lean:94` weightedDiagCLM_reLp
- `Analytic/ComplexificationCommute.lean:100` weightedDiagCLM_conjLp
- `Analytic/ComplexificationLp.lean:87` norm_conjLp
- `Analytic/ComplexificationLp.lean:92` conjLp_smul
- `Analytic/ComplexificationLp.lean:100` norm_sq_complexify_add_I_smul
- `Analytic/HoloAnalytic.lean:191` holomorphic_real_part_analytic
- `Assembly/Consts.lean:120` w8C
- `Assembly/Ext.lean:39` w8ext_hasDerivAt_inner
- `Birkhoff/Coords.lean:344` birkReal_injective
- `Birkhoff/LieBirk.lean:56` birkGamma_transport
- `Birkhoff/LieBirk.lean:97` norm_birkGammaD_sub_le
- `Birkhoff/LieBirk.lean:105` birkGammaD_invertible
- `Birkhoff/LieBirkC1.lean:30` birkGamma_contDiffOn
- `Birkhoff/LieBirkC1.lean:37` birkLieMulti_rho
- `Birkhoff/LieBirkC1.lean:45` birkLieMulti_slot
- `Birkhoff/MainBall.lean:173` birkK_eq
- `Birkhoff/MainBall.lean:177` norm_birkK1_le
- `Birkhoff/MainBall.lean:182` norm_birkK2_le
- `Birkhoff/MainBall.lean:187` norm_birkK_le
- `Birkhoff/MainBall.lean:204` norm_birkXK1_le
- `Birkhoff/MainBall.lean:209` norm_birkXK2_le
- `Birkhoff/MainBall.lean:219` birkXK_eq
- `Birkhoff/MainBall.lean:236` birkK1_field
- `Birkhoff/MainBall.lean:243` birkK2_field
- `Birkhoff/MainBall.lean:257` birkXK1_analyticOnNhd
- `Birkhoff/MainBall.lean:263` birkXK2_analyticOnNhd
- `Birkhoff/MainBall.lean:275` birkK_isClassA
- `Birkhoff/MainBall.lean:280` birkK2_isClassA
- `Birkhoff/MainBall.lean:286` birkXK_rho
- `Birkhoff/MainBallReal.lean:67` birkGammaR_analyticOnNhd
- `Birkhoff/MainBallReal.lean:93` birkGammaR_surj
- `Birkhoff/MainBallReal.lean:99` birkGammaR_hasFDerivAt
- `Birkhoff/MainBallReal.lean:107` birkGammaR_symplectic
- `Birkhoff/MainBallReal.lean:116` birkH_gammaR
- `Birkhoff/MainBallReal.lean:131` birkK_real
- `Birkhoff/MainBallReal.lean:145` birkXK_real
- `Birkhoff/MainBallReal.lean:158` birkK_real_fderiv
- `Birkhoff/MainBallReal.lean:172` birkK_real_gradient
- `Birkhoff/MainBallReal.lean:197` birk_conjugacy
- `Birkhoff/MainBallReal.lean:214` birk_transport_tori
- `Birkhoff/MainBallReal.lean:236` birk_transport_tori_real
- `Birkhoff/MainBallReal.lean:262` birk_transport_tori_frozen_coord
- `Birkhoff/MainBallReal.lean:283` birk_transport_tori_frozen
- `Birkhoff/MainBallReal.lean:311` norm_birkRestField_le
- `Birkhoff/MainBallReal.lean:319` birk_transport_tori_weak
- `Birkhoff/MainBallReal.lean:336` birk_transport_tori_weak_real

(+70 more.)

## 2. Leftover conditional helpers

Suffix scan over declaration names plus grep of docstrings (`conditional helper`, `CONDITIONAL helper`, 71 lines in 35 files). Result: **no helper is dead** (every one is used elsewhere), so none can be deleted; most are now internal building blocks that the unconditional source-facing theorems consume (`StepTheoremSrc` derives `stepTheorem` from `stepTheorem_of_eps0_pos` etc.; `Iteration/SmoothSrc` from the `_of_stepSmooth` family; `ConvSource` restates the `_of_stepReal` family with the clauses discharged). The stems exist for 24 of 38; stem existence is name-based only and does not prove it is the unconditional restatement.

| Suffix | Names | Used | Stem exists |
|---|---|---|---|
| `_of_eps0_pos` | 8 | 8 | 2 (`stepTheorem`, `stepTheoremMod`) |
| `_of_stepReal` | 10 | 10 | 10 |
| `_of_gates` | 6 | 6 | 6 (`Homological/PPlusOne`, `Modified*`, `Lemma*`; `homLemma1_lipschitz_of_gates` is referenced only in `PPlusOne.lean`) |
| `_of_pieces` | 6 | 6 | 2 (`w8_injective`, `w8_patchContK`) |
| `_of_stepSmooth` | 4 | 4 | 4 (`w6ConvTorus`, `w6ConvOpsSrc`, `w6Invariance`, `w6ToriKam`) |
| `_of_initial` | 2 | 2 | 0 (`w8_famBound_sharp_of_initial`, `w8ShellPrep_of_initial`) |
| `_of_bounds` / `_of_shift` | 1 / 1 | used | 0 (`w6IsFreqPair_of_bounds` used in FreqLip/FreqLipJ/WaveInst; `w6applicable_k0_of_shift` used only in `Applicable.lean`) |
| `_aux` | 11 | 11 | 10 (`Birkhoff/Main*Frozen*`, `MainTori`, `MainWeak`, `MainRealTori`, `MainConj`; `birkTransport_coeff_aux` has no stem) |
| `Ext` | 24 | 24 | not helpers: extension-by-zero defs (`birkKExt`, `lamExt`, `oddExt`, `waveExt`, ...) |

Other `_aux`-like: 34 names containing `aux/Aux` (e.g. `waveCubicAux*` x9 in `Normal/Analysis/CubicAnalytic.lean:56-119`, `waveTriAux` in `Cubic/TriLp.lean:54`).

Stale docstrings about these (the premise is now discharged but the text still says "to be discharged / is being added"):
- `Iteration/StepSmooth.lean:20-28` and `:46,:60` ("being added to W5 on `inp-w5aa`", "suffix `_of_stepSmooth`, to be discharged by one line once `inp-w5aa` lands"), although `Iteration/StepSmoothW5.lean` now proves `w6StepSmooth_holds`/`w6StepSmoothMod_holds`.
- `Iteration/ComposeMaps.lean:70-73` ("being added to W5 on `inp-w5aa`; every theorem taking `W6IterHyp` is conditional on that dependency"), `Iteration/ComposeStep.lean:33,170`, `Iteration/Invariance.lean:26`, `Iteration/WaveInst.lean:23` ("branch inp-w5r").
- `KamStep/StepTheorem.lean:33,129,199`, `KamStep/StepTheoremMod.lean:37,110`, `KamStep/RealStep.lean:25,38,102,113`, `KamStep/ExportFlowCore.lean:35,296`, `Assembly/ShellInit.lean:29,35,229,265` (premise `bpW:w5:initial` conclusion now available), `Homological/*` "CONDITIONAL helper (assumes the gate ...)" at `Lemma1.lean:40`, `LemmaOneAll.lean:187`, `LemmaOneBounds.lean:256`, `ModifiedBounds.lean:214`, `ModifiedEquation.lean:146`, `ModifiedLipField.lean:121`, `PPlusOne.lean:139,165,240`, `CompleteLieCont.lean:27,160`.
- Recommended: reword to "variant taking `<hyp>` as a hypothesis" and keep the names; rename only if the owner wants the family consolidated.


## 3. Stale or misleading comments and docstrings

Scanned comment text only (docstrings, block and `--` comments). Per-pattern counts (lines / files):

| Pattern | Lines | Files |
|---|---|---|
| "Off-frontier, source-faithful infrastructure" (module doc sentence) | 265 | 265 |
| "the dependency graph is still being built" | 285 | 285 |
| `W<n>-<PKG>` campaign package tags (W5-STEP 86, W4-HOMOLOGICAL 45, W3-MAIN 33, W3-FLOW 32, W3-SETTING 19, W1-ANALYTIC 15, W5-AA 12, W5-MODIFIED 12, W5-REAL 11, W6-PREP 8, W3-DIVISOR-F 7, W4-COMPLETE 5, W6-ITER 5, W5-STEP-B-FIX 5, about 23 other tags, 1-2 each) | 325 | 299 |
| `conditional helper` / `conditional on` | 71 / 12 | 35 / 7 |
| `deviation` and tags D1/D2/D4 (`Assembly/UpstreamW6.lean:17`, `Iteration/ConvSource.lean:112`, `FreqLipJ.lean:20`, `PrepShiftJ.lean:20-21`, `FreqInst.lean:28`, `WaveInst.lean:33`) | 8 | 8 |
| `handoff` / `orchestrator` / `session` / `prover` (`Birkhoff/LieBirk.lean:24`, `Iteration/ConvSource.lean:112`, `Iteration/StepSmooth.lean:22`, `Iteration/WaveInst.lean:33`) | 4 | 4 |
| branch names `inp-w5aa`, `inp-w5r` (`StepSmooth.lean:21,26,46,60`, `ComposeMaps.lean:73`, `WaveInst.lean:23`) | 6 | 3 |
| "finding F<n>" (e.g. `KamStep/FlowCalcJoint.lean:16`) | 10 | 10 |
| "being added" / "Milestone W6" (`Iteration/ConvSource.lean`) | 5 | 3 |
| "not yet in Lean" (`Iteration/Strong.lean:23`) | 1 | 1 |
| `TODO`/`FIXME`/`temporary`/`audit note`/`pending`/`will be`/`waits for`/`round N` | 0 | 0 |
| "gate(s)" (`Hom*Bounds` jargon, e.g. `Homological/CompleteZeroReal.lean:18-19`) | 11 | 8 |

Union of all the above except plain "gate": 790 lines in 448 files. The dominant item is the two boilerplate sentences in each module docstring (about 440 lines): they are now false, since the graph exists (`docs/graph/W`).

Blueprint labels: 221 distinct `bpW:` labels are cited in `KAM/Wave`; all 221 exist among the 397 `\label{bpW:...}` in `blueprint-W/parts/*.tex`. **Dangling `bpW:` citations: 0.** `stepW:` labels (437 in blueprint): one dangling, `stepW:w1:wavePicard` at `KAM/Wave/Analytic/Flow/Integral.lean:15` (3 occurrences). 176 blueprint `bpW:` labels are never cited in `KAM/Wave` (informational).

Other stale items to fix first: `Iteration/ConvSource.lean:17-22` still describes `ConvFreq`/`FreqInst` helpers "assume" clauses that "hold" (accurate but campaign-narrative); `Iteration/StepSmooth.lean:20-28` as in section 2.


## 4. Naming against Mathlib style

Systemic fact: 4,691 of 5,065 declarations (93%) live in the single flat namespace `KAM.Wave`; per-track prefixes substitute for namespaces. Remaining namespaces: `W6SeqData` (99), `StepCore` (96), `W6PrepHyp` (57), `StepHypMod` (29), `W6Stage` (28), `WaveStepHyp` (18), `IsHomContQuadPoly` (11), others <10.

Prefix families (declarations by leading lower-case token): `hom` 605, `birk` 573, `wave` 515, `norm` 343 (mathematical, ok), `step` 338, `w6` 297, `w8` 203, `kam` 140, `aa` 140, `lam` 86, `lie` 85, `meas` 64, `recon` 41, `w8ext` 23. Campaign-coded prefixes (`w0`/`w6`/`w8`, `W6`/`W8`): 595 names (12%), 3,931 touched lines. Systematic namespace substitutes (hom/birk/step/kam/aa/w6/w8/lam/lie): 2,559 distinct names, about 21,650 touched lines; a rename is a very large diff and should be done by namespace migration (`namespace KAM.Wave.Birkhoff` etc.) with scripted `open`, not by hand.

Targeted pattern counts (300 distinct names, about 3,270 touched lines):

| Pattern | Count | Examples |
|---|---|---|
| `_gen` suffix (150: 115 theorems, 33 defs, 2 structures), `HomTaylor_gen`-style | 150 | `Homological/CompleteLemma2.lean:48 homFieldSup_gen`, `Taylor.lean:93 homRy_gen`, `homSolveFamily_gen` |
| Defs/abbrevs with snake_case (should be lowerCamelCase), mostly the `_gen` defs | 34 | `homFieldLip_gen`, `homLamFieldNorm_gen`, `homRtheta_gen` |
| Theorems whose names start upper-case (structure-field style: `R1_field`, `M₀_pos`, `M_sum`, `F_field`; `KamStep/StepHypMod.lean:121-178`) | 71 | `R1_sub`, `M₁_nonneg` |
| Theorems with single-word names not describing the statement (`hK0`, `hqq1`, `hσs'`, `equation`, `core`, `divisors`, `weighted`, `stepTriangle`) | 95 | `KamStep/StepConj.lean:68 hK0`, `RealWeakConj.lean:50 hqq1`, `StepCore.lean:137 hσs'`, `StepHypMod.lean:199 equation` |
| Prime-suffixed theorems | 52 | `uIcc_subset_Icc'` (`Analytic/Flow/Picard.lean:106`), `waveTriML_apply'` |
| Numbered/coded suffixes (`K2a`-like, `C0n`, `c1`, `_128`, `_01/_02/_10/_12/_20/_21`) | 7 + 9 + 92 trailing-digit | `stepC0n`, `stepC2n` (`KamStep/Data.lean:54,57`), `birkDiv_C1i` (`Birkhoff/DivisorCore.lean:158`), `taylorXR_remainder_128` (`KamStep/TaylorEst.lean:192`), `wave_fin3_ne_01..21` (`Normal/Analysis/CubicAnalytic.lean:39-49`), `birk_lt_forty_of_lt_160` |
| `aux/Aux` in name | 34 | `waveCubicAux*` x9, `waveTriAux`, `birk_conjugacy_aux`, `birk_transport_tori_*_aux` (8) |
| `Lemma<n>` in names (blueprint numbering in identifier) | 30 | `homLemma1_*`, `homLemma2Complete_gen` |
| names ending `_lemma` / `helper` / `tmp` | 0 | none |
| `W`/`Mod`/`Src`/`Core`/`Ext` family suffixes (`stepDivisorsW`, `StepHypSrc`, `StepHypModSrc`) | about 90 | semantic, consistent; leave |

Theorem names not in snake_case: no `__`, no names over 43 characters. Structures are all UpperCamelCase; Prop-valued defs are UpperCamelCase (correct).


## 5. File sizes

No file exceeds 1000 lines; none exceeds 1500. Largest: `KamStep/StepTheoremSrc.lean` 824, `Homological/LemmaOneLipBounds.lean` 809, `Homological/ModifiedDivisors.lean` 571, `KamSupport/HilbertMatrix.lean` 439, `KamStep/InitialBound.lean` 430, `Iteration/IterArith.lean` 428, `KamStep/ActionAngle.lean` 425, `KamStep/HoloFderiv.lean` 416, `Iteration/ConvFreq.lean` 414, `Measure/UnpertBounds.lean` 413. Only 3 files exceed 500 lines; mean 185. Counts: over 1500: 0; over 1000: 0.

## 6. Duplicate lemmas

Method: whitespace-collapsed signature after the name, up to the top-level `:=` (bracket depth tracked, so `(p := p)` does not cut it), compared among theorems with signature of 30 or more characters. 16 groups (33 declarations). Signatures are read in their own `variable` context, so equality is necessary, not sufficient.

Probable genuine duplicates (same namespace `KAM.Wave`, same statement):
- `ellWeight_pos`: public `Seq/Transport.lean:39`, private copy `Recon/SineFeature.lean:75`, plus `waveEllWeight_pos` `Normal/Analysis/EllSeq.lean:45` (same statement; `private` hides the clash). Delete the private copy.
- `ellWeight_succ_exponent` `Homological/Schur.lean:202` (dead) and `ellWeight_succ_exponent'` `Homological/Index.lean:43`.
- `kamDomain_isOpen` `KamSupport/KamSpace.lean:138` and `kamDomain_isOpen'` `KamStep/TaylorSmoothing.lean:37` (dead).
- `kamNorm_add_le` `KamStep/Phase.lean:51` and `kamNorm_add_le'` `Iteration/ComposeMaps.lean:79` (dead).
- `kamNorm_le_of_le_radius` `KamSupport/KamSpace.lean:237` and `kamNorm_anti` `Iteration/ComposeStep.lean:74`.
- `aa_kamNorm_sub_le` `KamStep/Initial.lean:121` and `kamNorm_sub_le` `KamStep/StepTheoremSrc.lean:44`.
- `waveBW_pos` `KamStep/StepSetup.lean:31` and `homWaveBW_pos` `Homological/CompleteLemma2.lean:92`.
- `lamTan_eq_lam` `KamStep/ActionAngleNormal.lean:110` and `lamTan_eq` `Birkhoff/QuartBarAlg.lean:38`.
- `stepTheorem_clauses` `KamStep/StepTheoremSrc.lean:221` and `stepTheorem` `:357`; `stepTheoremMod_clauses` `:549` and `stepTheoremMod` `:687` (identical signatures; check whether one is a thin wrapper, `stepTheorem` is a W5 export so keep it).

Structural parallels, same name in different namespaces (not duplicates, hypotheses differ by structure type): `StepCore.{R_eq,R_field,R_sub,R,ε_pos,pb_pos,hσs'}` vs `WaveStepHyp.*` (`KamStep/StepCore.lean:133-157` vs `KamStep/StepHyp.lean:72-108`); `StepHypMod.{FT,F_field,M₀_pos,hσs'}` vs `WaveStepHyp.*` (`StepHypMod.lean:108-178`); `StepHypSrc.split_spec` vs `StepHypModSrc.split_spec` (`StepTheoremSrc.lean:170,497`); `WaveStepHyp.FT_isRealTaylor` vs `StepHypMod.FT_isRealTaylor` (`RealStep.lean:138,159`). 12 same-last-name pairs share a signature; 24 same-last-name groups in total. Mod/non-Mod parallelism (`StepHyp`/`StepHypMod`, `StepHypSrc`/`StepHypModSrc`, `stepTheorem`/`stepTheoremMod`) is a possible larger de-duplication via a common structure, estimated several hundred lines in `KamStep` but out of scope for a clean-up.

Same-type defs (e.g. `homRz/homRzb/homRu/homRv`, `homTP/homTP'/homTQ/homTQt`) share a signature by design and are not duplicates.

## Estimated diff size and recommended order

| Order | Category | Action | Lines removed or changed | Risk |
|---|---|---|---|---|
| 1 | 3 | delete the two boilerplate module-doc sentences; reword jargon (`W5-STEP`, deviation D-tags, branch names, "orchestrator/handoff") and stale "being added" text | about 790 (440 by `sed`) | none (comments only) |
| 2 | 2 | reword the 71 "conditional helper" lines and the stale `inp-w5aa` text | about 75 | none |
| 3 | 1 | delete 150 candidates (then rerun to catch orphans; re-check the 22 implicit-use and keep the 130 graph-cited) | about 815 removed | low; confirm with a core `lake build` |
| 4 | 6 | remove the private `ellWeight_pos` copy and dead primed duplicates (partly already counted in 1) | about 40 | low |
| 5 | 4 | targeted renames: `_gen` (150) and snake-case defs, upper-case theorem names, `K2a`/`C0n`/`_128`, `aux` | about 3,270 touched | medium (cross-file; build needed) |
| 6 | 4 | optional prefix to namespace migration (`hom`, `birk`, `step`, `w6`, `w8`) | about 21,650 touched | high; large diff, do per directory, separate PR |
| - | 5 | nothing to do | 0 | - |

Totals if 1-5 are done: about 4,990 lines touched; with 6, about 26,600 (of 84,252).
