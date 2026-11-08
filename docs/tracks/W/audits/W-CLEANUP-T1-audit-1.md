# W-CLEANUP-T1 independent cheap diff review

Verdict: **PASS** for the requested tier-1 source-diff criteria. No offending declaration, changed kept statement, packet-reference deletion, protected-path edit, or introduced resource override was found.

Reviewed HEAD `1cbe1d07a5943fbcea8e6f28eebf0c6fdbe5dbf1`, base `82e426b28`, and `git diff inp...HEAD` against local `inp` at `e9f483378c2ec454bb6e862fb69fb30219176149`. The Lean diffs in these two comparisons are identical. The explicit range has 412 changed files (411 Lean files and the handoff); the branch comparison additionally adds the historical `docs/tracks/W/CLEANUP-AUDIT.md`. Implementation commits: `77eeb0fd4`, `a0cf90491`, `cb1ce3587`; subsequent commits add/update the handoff.

Read AGENTS.md, PLAN, DECISIONS, the external package-audit brief, `docs/tracks/W/CLEANUP-T1-handoff.md`, and `docs/tracks/W/CLEANUP-AUDIT.md`. The requested `docs/tracks/W/audits/W-CLEANUP-T1-handoff.md` does not exist in this worktree or the main worktree. The explicit user criteria supply the audit focus. This is a source-diff audit; it does not repeat the full package/source proof audit or certify a new seal.

| Check | Verdict | Evidence |
|---|---|---|
| Whole-repository uses of 128 dead declarations | PASS | An individual `git grep -nw -F -e NAME -- .` for each removed last name component; no command errors; no surviving use after resolving Lean identifier boundaries. No directory-restricted search. Applications, scripts, kernel-tests, all blueprints and graph documents are included. |
| Packet `LEAN_REF` preservation | PASS | All removed names checked against every tracked file under `docs/graph/W/packets`; zero removed references. The surviving public `ellWeight_pos` is distinguished from its deleted private copy. |
| Kept declaration headers | PASS | Comment-masked, whitespace-normalized headers through the top-level `:=`/`where` compared before/after, preserving binders and all header tokens; 4,613 kept declaration occurrences, zero mismatches. Repeated short names in different namespaces were checked occurrence by occurrence. |
| Definitions and proof bodies | PASS | No new declarations; kept definitions unchanged. All 18 changed theorem bodies become identical after the three documented duplicate-name redirects and whitespace normalization. 331 changed Lean files are comment/whitespace-only. |
| Remaining command context | PASS | Namespace, variable, attribute and option commands unchanged. Removed one-declaration `include ha hp hc in` in QuartML and `omit hsmall in` in ConvArith belonged to the deleted theorem. Only added import is the public import of Seq.Transport in SineFeature, supplying the identical positivity theorem. |
| Protected paths | PASS | `git diff 82e426b28..HEAD -- KAM/Frozen KAM/Provider manifest docs/graph KAM.lean KAM/Root README.md lakefile.lean` is empty. Both range comparisons confine changed Lean files to KAM/Wave. |
| Resource/proof hygiene delta | PASS | No added forbidden proof escapes or resource-override lines; no deleted declaration has an implicit-use attribute. Maximum changed file: StepTheoremSrc.lean, 822 lines. `git diff --check 82e426b28..HEAD` exits 0 with no output. |

The scans retained comments as uses for name checks, except the historical cleanup proposal, cleanup handoff and historical `docs/tracks/W/audits/` records. No other document was exempted. `git grep -w` treats apostrophes as word boundaries: the hits for deleted `ellWeight_succ_exponent` at `KAM/Wave/Homological/Index.lean:40,48` name the surviving **different** identifier `ellWeight_succ_exponent'`, not the deleted theorem. All other nonhistorical short-name hits concern the surviving public `ellWeight_pos`; the removed copy was private to SineFeature, whose two calls now resolve to the identical public statement. No deleted dead declaration has a surviving exact-token use.

Duplicate checks (source headers and surrounding variable context inspected):

| Removed occurrence | Surviving public statement | Verdict |
|---|---|---|
| Recon/SineFeature private `ellWeight_pos`; Normal/Analysis/EllSeq `waveEllWeight_pos` | Seq/Transport `ellWeight_pos (a p : ℝ) (j : ℕ+) : 0 < ellWeight a p j` | PASS; identical parameters and conclusion; import supplies the public theorem to SineFeature and downstream users. |
| Iteration/ComposeStep `kamNorm_anti` | KamSupport/KamSpace `kamNorm_le_of_le_radius {r r' : ℝ} (hr' : 0 < r') (hr : r' ≤ r) (W : KamPhase) : kamNorm r W ≤ kamNorm r' W` | PASS; identical header after name substitution, including implicit radii and explicit premises. |
| KamStep/ActionAngleNormal `lamTan_eq_lam` | Birkhoff/QuartBarAlg `lamTan_eq (i : Fin 2) : lamTan m hm i = lam m hm (modeIdx i)` | PASS; same ambient `(m : ℝ) (hm : 0 < m)`, same explicit binder and conclusion. |

Docstring revisions leave code unchanged except for the separately inventoried deletions, redirects and import. The corrected label `stepW:w1:picard` exists at `blueprint-W/parts/w1-sequences.tex:884`; all three corrected citations are in comments. No retained theorem is renamed or weakened. Conditional variants retain their hypotheses and names.

Verification commands and observed results:

- `python3 .lake/abi-scratch/wcl_review.py`: extracted 132 removed declaration occurrences; 128 dead declarations plus four duplicate copies; no new declaration; whole-repository grep errors `[]`; packet-reference hits `[]`. A second occurrence-preserving pass reported `ALL_KEPT_DECLARATION_OCCURRENCES 4613 HEADER_MISMATCHES [] UNEXPLAINED_BODY_CHANGES [] COMMENT_ONLY_FILES 331`. The scripts masked nested comments, preserved string contents, tracked binder nesting at the declaration body boundary, and checked nondeclaration command changes separately. Temporary audit scripts/results were removed after report generation.
- `git diff --check 82e426b28..HEAD`: exit 0, empty output.
- Prescribed lint command (including all child Lean/Lake activity within one capped scope):

  ```sh
  systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wcl
  ```

  Exit 0. Exact output:

  ```text
  check_lean_modules: PASS (4483 Lean files, 0 comparator configurations)
  .........................
  ----------------------------------------------------------------------
  Ran 25 tests in 3.812s

  OK
  FROZEN-ANCHOR GUARD OK
  ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
  ```

  The KAMLunarBand file-hash-only qualification is retained; no application rebuild was performed.

No independent build, `#print axioms`, or kernel replay was run: the user explicitly scoped this as cheap diff review and stated the launcher had already run replay/name checks. Those launcher outputs were unavailable and are not represented as independently verified. No provider export or new public theorem was introduced. Source comparison is the evidence for this verdict.

Notes: the handoff's “131 removed names” counts distinct public names, whereas the diff removes 132 declaration occurrences including the private `ellWeight_pos` copy. This is an accounting clarification, not a missing reference. The specified focus-file path is absent as noted above. No suspected pinned-source/blueprint defect or semantic deviation found; no repository source was edited.

Removed-declaration inventory follows. Locations are at base `82e426b28`; `dead` means no surviving exact-token use outside the allowed historical records; `duplicate` is justified above. Every row also passed the packet-reference check.

| Base location | Declaration | Verdict | Classification |
|---|---|---|---|
| `KAM/Wave/Algebra/TwoSided.lean:160` | `waveTwoWeight_zero_left` | PASS | dead |
| `KAM/Wave/Analytic/ComplexificationCommute.lean:107` | `coeffW_weightedDiagCLM` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:58` | `w8ext_summable_abs_mul` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:63` | `w8ext_tsum_add` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:75` | `w8ext_antitoneOn_Icc` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:85` | `w8ext_monotoneOn_Icc` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:95` | `w8ext_hasDerivAt_exp_mul` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:196` | `w8ext_rpow` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:202` | `w8ext_rpow_le_rpow` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:228` | `w8ext_clm_comp_analyticOnNhd` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:235` | `w8ext_fderiv_clm_comp` | PASS | dead |
| `KAM/Wave/Assembly/Ext.lean:242` | `w8ext_le_of_tendsto` | PASS | dead |
| `KAM/Wave/Assembly/ShellGeom.lean:148` | `w8Pi_subset_shellInner` | PASS | dead |
| `KAM/Wave/Assembly/ShellIter.lean:170` | `w8ShellGamma_eq` | PASS | dead |
| `KAM/Wave/Assembly/UpstreamW6.lean:40` | `w8Upstream_gam` | PASS | dead |
| `KAM/Wave/Assembly/UpstreamW6.lean:42` | `w8Upstream_gam1` | PASS | dead |
| `KAM/Wave/Assembly/UpstreamW6.lean:44` | `w8Upstream_cF` | PASS | dead |
| `KAM/Wave/Assembly/UpstreamW6.lean:46` | `w8Upstream_cFnat` | PASS | dead |
| `KAM/Wave/Birkhoff/BlockMap.lean:60` | `blockMap_const` | PASS | dead |
| `KAM/Wave/Birkhoff/BlockMap.lean:65` | `norm_blockMap_le` | PASS | dead |
| `KAM/Wave/Birkhoff/Coords.lean:297` | `birkZEquiv_apply` | PASS | dead |
| `KAM/Wave/Birkhoff/Coords.lean:299` | `birkZEquiv_symm_apply` | PASS | dead |
| `KAM/Wave/Birkhoff/Coords.lean:302` | `norm_le_sqrt_two_mul_birkZinv` | PASS | dead |
| `KAM/Wave/Birkhoff/DivisorCore.lean:118` | `birkDelta_nonneg_mono` | PASS | dead |
| `KAM/Wave/Birkhoff/LieBirkPlus.lean:32` | `lieT_birk` | PASS | dead |
| `KAM/Wave/Birkhoff/MainBall.lean:42` | `isBirkExtension_restrict` | PASS | dead |
| `KAM/Wave/Birkhoff/MainBall.lean:132` | `birkPsi_embed` | PASS | dead |
| `KAM/Wave/Birkhoff/MainBall.lean:137` | `birkXi_embed` | PASS | dead |
| `KAM/Wave/Birkhoff/MainBall.lean:143` | `birkAF_eq` | PASS | dead |
| `KAM/Wave/Birkhoff/MainBall.lean:161` | `birkAF_eq_birkGammaDPlus` | PASS | dead |
| `KAM/Wave/Birkhoff/MainBall.lean:198` | `birkK2_rho` | PASS | dead |
| `KAM/Wave/Birkhoff/MainYInt.lean:204` | `norm_birkGammaDPlusInv_le` | PASS | dead |
| `KAM/Wave/Birkhoff/MainYInt.lean:217` | `birkGammaD_embed_birkGammaDPlusInv` | PASS | dead |
| `KAM/Wave/Birkhoff/QuartML.lean:223` | `birkGradML_apply` | PASS | dead |
| `KAM/Wave/Birkhoff/QuartNormal.lean:45` | `norm_birkNormalPart_le` | PASS | dead |
| `KAM/Wave/Birkhoff/QuartSum.lean:115` | `snoc_eq_vec3` | PASS | dead |
| `KAM/Wave/Birkhoff/Space.lean:89` | `birkCoord_sub` | PASS | dead |
| `KAM/Wave/Birkhoff/Space.lean:93` | `birkCoord_neg` | PASS | dead |
| `KAM/Wave/Birkhoff/Space.lean:122` | `birk_hasSum_split` | PASS | dead |
| `KAM/Wave/Birkhoff/Space.lean:261` | `birkRho_injective` | PASS | dead |
| `KAM/Wave/Cubic/FrozenForm.lean:37` | `ellWeight_add_one` | PASS | dead |
| `KAM/Wave/Cubic/GradLp.lean:65` | `waveGw'` | PASS | dead |
| `KAM/Wave/Cubic/QPair.lean:115` | `wavePairCLM_apply` | PASS | dead |
| `KAM/Wave/Cubic/SelectionOneSided.lean:235` | `waveSelSum_smul_mid` | PASS | dead |
| `KAM/Wave/Cubic/SelectionOneSided.lean:241` | `waveSelSum_smul_right` | PASS | dead |
| `KAM/Wave/Cubic/SelectionOneSided.lean:256` | `waveSelSum_add_mid` | PASS | dead |
| `KAM/Wave/Cubic/SelectionOneSided.lean:265` | `waveSelSum_add_right` | PASS | dead |
| `KAM/Wave/Cubic/SelectionTwoAlg.lean:127` | `waveSelTwo_smul_mid` | PASS | dead |
| `KAM/Wave/Cubic/SelectionTwoAlg.lean:134` | `waveSelTwo_smul_right` | PASS | dead |
| `KAM/Wave/Cubic/SelectionTwoAlg.lean:151` | `waveSelTwo_add_mid` | PASS | dead |
| `KAM/Wave/Cubic/SelectionTwoAlg.lean:161` | `waveSelTwo_add_right` | PASS | dead |
| `KAM/Wave/Cubic/TriML.lean:75` | `waveTriML_apply'` | PASS | dead |
| `KAM/Wave/Homological/AngleSupport.lean:40` | `homEntryCLM_apply` | PASS | dead |
| `KAM/Wave/Homological/CohEq.lean:32` | `homCoeff_continuous_of` | PASS | dead |
| `KAM/Wave/Homological/DivisorsConcrete.lean:164` | `homWeightP_ge_abs` | PASS | dead |
| `KAM/Wave/Homological/LemmaOneAll.lean:33` | `homPairRep_eq'_gen` | PASS | dead |
| `KAM/Wave/Homological/LemmaOneAll.lean:104` | `one_le_homWt` | PASS | dead |
| `KAM/Wave/Homological/Lie.lean:89` | `homPair0Raw_comm` | PASS | dead |
| `KAM/Wave/Homological/ModifiedLipDeriv.lean:258` | `HomCompBounds_gen.mono_scale` | PASS | dead |
| `KAM/Wave/Homological/ModifiedReal.lean:64` | `homModSolveTaylor_cm` | PASS | dead |
| `KAM/Wave/Homological/ModifiedReal.lean:82` | `homModSolveTaylor_P'` | PASS | dead |
| `KAM/Wave/Homological/ModifiedReal.lean:230` | `homMelnikovMod_of_melnikov` | PASS | dead |
| `KAM/Wave/Homological/ModifiedReweight.lean:59` | `norm_homModRhoL_apply_le` | PASS | dead |
| `KAM/Wave/Homological/ModifiedReweight.lean:108` | `homDualNorm_rho` | PASS | dead |
| `KAM/Wave/Homological/NormalPol.lean:73` | `homPairL2_comm` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:48` | `homNormEntryCLM` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:52` | `homLamDiag` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:58` | `homPairRep` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:100` | `homPairOmegaRaw` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:141` | `homLemma1_lipschitz_of_gates` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:159` | `norm_homLamD_mul_le` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:167` | `homLemma1_equation_all_of_gates` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:242` | `homLemma1_fieldBound_of_gates` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:250` | `homLam_comm_homTQ` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:268` | `homLemma1_zero_modes` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:314` | `homEq_Q` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:326` | `homLipField_dQ` | PASS | dead |
| `KAM/Wave/Homological/PPlusOne.lean:351` | `homLemma_lie_iv` | PASS | dead |
| `KAM/Wave/Homological/RealSolve.lean:92` | `homMultDm_conj` | PASS | dead |
| `KAM/Wave/Homological/RealSolve.lean:106` | `homDP'_conj` | PASS | dead |
| `KAM/Wave/Homological/Schur.lean:47` | `homKS_lt` | PASS | dead |
| `KAM/Wave/Homological/Schur.lean:202` | `ellWeight_succ_exponent` | PASS | dead |
| `KAM/Wave/Iteration/ComposeMaps.lean:79` | `kamNorm_add_le'` | PASS | dead |
| `KAM/Wave/Iteration/ComposeStep.lean:74` | `kamNorm_anti` | PASS | duplicate |
| `KAM/Wave/Iteration/ComposeStep.lean:99` | `domNu_anti` | PASS | dead |
| `KAM/Wave/Iteration/ComposeStep.lean:278` | `w6Field_irrel` | PASS | dead |
| `KAM/Wave/Iteration/Constants.lean:84` | `w6S0_eq` | PASS | dead |
| `KAM/Wave/Iteration/ConvArith.lean:194` | `two_two_MF_eq` | PASS | dead |
| `KAM/Wave/Iteration/ConvMaps.lean:241` | `w6PiStarS_eq_It` | PASS | dead |
| `KAM/Wave/Iteration/ConvTorus.lean:53` | `w6TorusCLM_apply` | PASS | dead |
| `KAM/Wave/Iteration/IterArith.lean:79` | `q_nonneg_of_eps` | PASS | dead |
| `KAM/Wave/Iteration/Params.lean:63` | `w6PiStar_subset` | PASS | dead |
| `KAM/Wave/Iteration/Params.lean:100` | `w6Zone_subset` | PASS | dead |
| `KAM/Wave/Iteration/PrepMel.lean:45` | `coeffSum_neg` | PASS | dead |
| `KAM/Wave/Iteration/Sequence.lean:146` | `w6Seq_Pi_subset` | PASS | dead |
| `KAM/Wave/Iteration/Sequences.lean:202` | `sigma_zero` | PASS | dead |
| `KAM/Wave/Iteration/Sequences.lean:361` | `KNu_pos` | PASS | dead |
| `KAM/Wave/Iteration/Sequences.lean:365` | `eps_succ_eq_kappa` | PASS | dead |
| `KAM/Wave/Iteration/WaveData.lean:169` | `w6SigmaP_le_min` | PASS | dead |
| `KAM/Wave/KamStep/ActionAngleNormal.lean:110` | `lamTan_eq_lam` | PASS | duplicate |
| `KAM/Wave/KamStep/Data.lean:95` | `stepC0_pos` | PASS | dead |
| `KAM/Wave/KamStep/ExportFlowCore.lean:89` | `PsiT_one` | PASS | dead |
| `KAM/Wave/KamStep/NewHamTransport.lean:80` | `transSolve_unique` | PASS | dead |
| `KAM/Wave/KamStep/ParamIntegral.lean:153` | `riemannSum_add` | PASS | dead |
| `KAM/Wave/KamStep/RealFlowPicard.lean:98` | `stepRealFun_apply` | PASS | dead |
| `KAM/Wave/KamStep/StepPlus.lean:34` | `stepZF` | PASS | dead |
| `KAM/Wave/KamStep/StepReweight.lean:71` | `stepZ_comp_stepRhoK` | PASS | dead |
| `KAM/Wave/KamStep/StepReweight.lean:75` | `stepZb_comp_stepRhoK` | PASS | dead |
| `KAM/Wave/KamStep/StepReweightTaylor.lean:130` | `tQt_rhoK` | PASS | dead |
| `KAM/Wave/KamStep/StepReweightTaylor.lean:166` | `stepTaylorRho_b` | PASS | dead |
| `KAM/Wave/KamStep/StepReweightTaylor.lean:169` | `stepTaylorRho_a0` | PASS | dead |
| `KAM/Wave/KamStep/TaylorEst.lean:50` | `norm_kamToStep` | PASS | dead |
| `KAM/Wave/KamStep/TaylorSmoothing.lean:37` | `kamDomain_isOpen'` | PASS | dead |
| `KAM/Wave/KamSupport/FourierBessel.lean:56` | `norm_kamChi` | PASS | dead |
| `KAM/Wave/KamSupport/Lattice.lean:161` | `kamLattice_const_nonneg` | PASS | dead |
| `KAM/Wave/KamSupport/SchurTest.lean:41` | `bound_mono` | PASS | dead |
| `KAM/Wave/Measure/Lambda.lean:274` | `hatW_pos` | PASS | dead |
| `KAM/Wave/Measure/Measure.lean:172` | `melnikov_prep_zero` | PASS | dead |
| `KAM/Wave/Measure/Measure.lean:189` | `melnikov_iter` | PASS | dead |
| `KAM/Wave/Measure/MinusSum.lean:51` | `measXSet_neg_iff` | PASS | dead |
| `KAM/Wave/Normal/ActionCoeff.lean:98` | `gN_diag` | PASS | dead |
| `KAM/Wave/Normal/Analysis/CubicTools.lean:38` | `wave_ellWeight_sq_div_lam_le` | PASS | dead |
| `KAM/Wave/Normal/Analysis/EllSeq.lean:45` | `waveEllWeight_pos` | PASS | duplicate |
| `KAM/Wave/Normal/Analysis/EllSeq.lean:51` | `waveEllMajorant_nonneg` | PASS | dead |
| `KAM/Wave/Normal/Analysis/Gradient.lean:75` | `abs_waveHat_le` | PASS | dead |
| `KAM/Wave/Normal/Analysis/PdeBase.lean:40` | `reconV_eq_waveV` | PASS | dead |
| `KAM/Wave/Normal/Analysis/SeqBridge.lean:49` | `coeff_isEll_one_one` | PASS | dead |
| `KAM/Wave/Recon/ReconAnalytic.lean:149` | `reconUIterCLM_apply` | PASS | dead |
| `KAM/Wave/Recon/ReconAnalytic.lean:152` | `reconVIterCLM_apply` | PASS | dead |
| `KAM/Wave/Recon/SineFeature.lean:75` | `ellWeight_pos` | PASS | duplicate |
| `KAM/Wave/Seq/Flow.lean:187` | `flowCLM_zero` | PASS | dead |
| `KAM/Wave/Seq/Flow.lean:220` | `coeffW_flow_snd` | PASS | dead |
