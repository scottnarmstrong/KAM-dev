# Handoff SO-SOUND-A (track SO, part 1): soundness of Static, Ham, Embedding, Gram

Branch `inp-sosounda`, worktree /root/code/KAM-inp-sosounda. Commits (each file committed as soon as
it built): `ef958608` Static (then READY-SO-SOUND-STATIC touched), Ham, Embedding, Gram.

## Files (all new, all Lean modules, all lines <= 100 columns)
- `KAM/Certificate/Sound/Static.lean` (158 lines): `StaticFacts`, `checkStatic_sound`,
  `checkStatic_freq`, `TorusCertificate.emb_structural`; helpers `freqNormLo_le_of_forall`,
  `freqNormLo_le_norm`.
- `KAM/Certificate/Sound/Ham.lean` (158 lines): `checkHamBounds_sound`,
  `TorusCertificate.ham_structural`; helpers `sumRangeQ_eq`, `sum_phaseNat_eq_sumRangeQ`,
  `sum_sum_phaseNat_eq_sumRangeQ`, `norm_le_ballMagQ_of_mem`, `Slp.norm_val_le_slotMagQ`.
- `KAM/Certificate/Sound/Embedding.lean` (164 lines): `checkEmbedding_sound`; helpers
  `sum_finRange_map_eq`, `angleImOk_sound`.
- `KAM/Certificate/Sound/Gram.lean` (41 lines): `checkGram_sound`.
Signed statements are exactly as in SOSignatures §G (names, binders, types).

## Engine lemmas consumed
- `checkStatic_sound`: `checkStatic` unfolded (pure `decide` reads, casts). `checkStatic_freq`:
  `freqNormLo_le_norm` (`‖ω‖ ≥ |ω_i| ≥ |c_i| - r_i`, Pi sup norm; `FreqEncloses`, `box.length = n`
  from checkStatic), `exists_rat_btwn`.
- `emb_structural`: `CertEmbedding.differentiable_eval`, `.isPrimaryOnStrip`, `.isRealOnReals`.
- `ham_structural`: `isOpen_certDomain`, `certDomain_add_int`, `HamExpr.contDiffOn_eval`,
  `HamExpr.eval_add_int`, `HamExpr.eval_real`.
- `checkHamBounds_sound`: `HamExpr.nonvanishingOn_of_balls`, `ballsAux_sound` (slot-in-ball for
  every index, out-of-range slots read 0/ballZero, so no range premise is needed),
  `HamExpr.jet_d1/d2/d3`, `norm_fderiv_le_sum_partials`, `hamiltonianVectorFieldℂ_sumVec`,
  `norm_sumVec`, `norm_fderiv_hamiltonianVectorFieldℂ_le`,
  `norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (with `1 ≤ n` from `StaticFacts.hn`),
  `norm_iteratedFDeriv_two_le_sum_partials`, `phaseNat_finSumFinEquiv_symm`, `phaseNat_lt_add`.
- `checkEmbedding_sound`: `realCompModel_encloses`, `CertModel.norm_le_supBound`,
  `compDerivModel_encloses`, `norm_clm_le_sum_single` (Model/Exp), `convex_complexStrip` +
  `Convex.norm_image_sub_le_of_norm_fderiv_le` (mean value from `Re θ`), `realComp_real`,
  `differentiable_angleAt`, `CertModel.Encloses.addMixed`, `constModel_encloses`,
  `dkModels_encloses`, `tangentMat`, `norm_colMat`, `KAM.norm_le_iff_forall_rowSum`, `sumUp_ge`,
  `LawfulCertArith.ble_sound/ofRatDown_le/ofRatUp_ge/upMul_ge`.
- `checkGram_sound`: `gramCheck_sound` (with `1 ≤ n`, `hW`, `hpe`, strip via `hrho`).

## Checks
- Gate builds: `inp_lake_build.sh … KAM.Certificate.Sound.{Static,Ham,Embedding,Gram}`: each
  `Build completed successfully`; no sorry, no errors.
- Warnings in my files: two `unusedSectionVars` linter warnings (Static: `checkStatic_sound`,
  `emb_structural` carry `[LawfulCertArith α]` unused). Kept deliberately: the signed statements
  sit under `variable [LawfulCertArith α]` in SOSignatures, so I did not `omit` (would change the
  signed type). Orchestrator may choose to `omit` (strictly more general).
- `main_shortname_check.py` on the 4 modules: `short-name check OK`.
- `scripts/lint_sources.sh`: only failure `KAM.lean is out of date; run scripts/gen_root_imports.py`
  (generated root, rule 10; the four new modules need adding). check_lean_modules PASS,
  FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
- No heartbeat issues; no overrides; no forbidden constructs.

## #print axioms (all seven signed theorems)
`checkStatic_sound`, `checkStatic_freq`, `TorusCertificate.emb_structural`, `checkHamBounds_sound`,
`TorusCertificate.ham_structural`, `checkEmbedding_sound`, `checkGram_sound`:
`[propext, Classical.choice, Quot.sound]`.

## Weaknesses in Defs.lean
None found that blocks these four contracts. Notes: `checkHamBounds` `getD` defaults are harmless
(jet bridges are stated with the same `getD` reads; a default slot 0 is the zero slot, whose ball is
checked like every other). `angleImOk` uses `W.rho` passed as `p.rho`; equal to `weight.rho` by
`checkStatic`. Ray margins and `ω* ≠ 0` sound via `freqNormLo` (requires `freqBox.length = n`,
which `checkStatic` checks).

## Errata / deviations
None in pinned sources. No deviation from signed statements.
