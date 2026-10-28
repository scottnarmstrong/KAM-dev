# P23-22 independent audit 1

Audit date: 2026-10-28. Audited HEAD: `fcbf64669b7beef617fde085680dfeb1f18d6b86`.

## Scope and verdict

**Overall release verdict: FAIL (F1: unpermitted source-lint failures).** The exact signed `two_scale_kam` and all ten new helper theorems pass the mathematical, type, axiom and kernel checks; N2's shared-witness applicability gate is discharged for this assembly. However, three overlong lines in the new Theorem module fail the mandatory lint gate beyond the sole permitted stale-root exception. The package is not release-ready. No frozen anchor is assigned or sealed by this package.

The user-specified destination in this package worktree overrides the common brief's main-worktree destination. Only this report and temporary `.lake/abi-scratch/` probes were written. No production repair, git mutation, or generated-root regeneration was performed. All audit Lean/Lake processes were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build used the required compile gate.

Read AGENTS.md, PLAN, DECISIONS, the common package brief, P23-22 handoff/AUDIT FOCUS, P23 design revision 2 node table and N2 release gate (including design audits 1/2), P3a's theorem and inverse-ball statements, P3b's local obligations and final assembly, Track P statement conventions, P23-18 audit 2, P23-20's L1–L6 table, and P23-21's applicability requirements. Inspected the relevant frozen Phase, action/strip carriers, real Hamiltonian vector field and symplectic form, and the downstream P-G anchor. This is the source-premise-only infrastructure theorem, not a provider or a frozen-anchor seal. No provider/frozen-anchor equality or seal-body probe applies. The independent signature probe instead copies the exact signed theorem under a fresh name and applies `two_scale_kam H hL`.

`git diff inp...HEAD` was inspected as requested. Git reports multiple merge bases, using `35ffbe5a7ec4f5cca39e3da808039c0b88c0d4de`; the other is `c5776d12e9876873026dae249ec6f7e3e2dc1d22`. The comparison against inp `d9183adae208ecf2e726620694b69c8168e33006` includes 177 inherited/package files and 106 added lines in generated `KAM.lean`. Thus the literal protected-path diff is **not empty**. The Frozen/manifest/README portion is empty. Isolating the P23-22 commits with `git diff 8978933d..HEAD` gives exactly the three new files below, 427 lines; its protected-path diff is empty. The generated-root difference is inherited, not a P23-22 edit. This audit does not approve all unrelated inherited packages.

| Scoped file under `KAM/Planetary/TwoScale/` | Lines | SHA256 |
|---|---:|---|
| `TheoremInverse.lean` | 111 | `daed7b7472343027fa9c3d545d3509485fb0fdcfcf9dbc07d519a69a6aee8775` |
| `TheoremTorus.lean` | 133 | `3d87be0e062d311a20d6339547c0faef22bae4ae67c968317d8bae1ce97c0776` |
| `Theorem.lean` | 183 | `cba517fb5e7624b6bb0b99dc0d4f9cbb6a8c68d0f56315656697b911428235f3` |

## Signature and public declaration review

Byte comparison of the complete docstring + declaration header + type, ending immediately before `:=`, against `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` L808–853: **equal**, 3494 UTF-8 bytes in each; SHA256 `c81f17d353fce97101d4850a9f4558fa137511586a2c5406b7ca633d44b7eb93`. No whitespace normalization was used. Quantifier order, dependence, constants, norms, all five joint witnesses, local and bounded-global inverse estimates, and exact half-open-cell measure conclusion are retained. The signed `hL` premise is unused by this proof; the proved route works already from `H.L_bound`. It is retained verbatim, not weakened or strengthened in production.

Names below are relative to `KAM.Planetary`; file abbreviations are TI=`TheoremInverse.lean`, TT=`TheoremTorus.lean`, TH=`Theorem.lean`.

| Node / role | Public declaration | Verdict | Reason / locator |
|---|---|---|---|
| real frequency | `KamHyp.freq_real` | PASS | TI:33–36: holomorphy and reality on the actual source neighborhood, positive widths. |
| inverse uniqueness | `KamHyp.realFreq_injOn` | PASS | TI:39–45: complex injectivity on actionNbhd restricts through the real inclusion. |
| source inverse locus | `KamHyp.exists_inverse_locus` | PASS | TI:48–52: unfold Ω image membership; recovered point lies in D₀, uniqueness from realFreq_injOn. |
| inverse local | `KamHyp.inverse_local` | PASS | TI:55–80: apply inverse ball continuation at I with δ=ρ,m=Mbar; coverage and global source injectivity identify the preimage with J. No convexity of D assumed. |
| inverse global | `KamHyp.inverse_global` | PASS | TI:83–107: close pairs use local bound, far pairs use bounded-D diameter and ρ/Mbar≤frequency distance; exact max factor. |
| radius comparison | `rhoHat_le_rho` | PASS | TT:34–35: literal minimum, stronger unconditional statement for arbitrary ScaleData. |
| phase injectivity | `KamHyp.phi_injOn` | PASS | TT:38–58: distinctly conditional generic helper; defect coefficient 768nÊ<1 from 8192nÊ<1, positive scaling. Applied TH:122–123 and TT:125. |
| action injectivity | `KamHyp.i_injOn` | PASS | TT:61–74: same argument with 2560nÊ<1. Applied TH:124 with proved limit-action bound. |
| Hamiltonian differentiability | `KamHyp.Hr_differentiableAt` | PASS | TT:77–101: 32Êρhat≤ρ; real inclusion in open coefficientDom; kam_G_diff restricted to ℝ and composed with inclusion and reCLM. |
| lattice torus assembly | `lattice_torus_of_limit` | PASS | TT:109–129: explicit conditional helper; every hypothesis supplied from one iterative output in TH:137. L1–L6 below. |
| `bpP:p3:two-scale-kam` | `two_scale_kam` | FAIL release / PASS proof | TH:36–177: exact signed source-premise contract, all conditional inputs discharged; F1 blocks mandatory hygiene. |

## Definitions and hypotheses

There are **no new def/abbrev/structure/instance declarations** in these three modules. Local witness constructions are classified as follows:

- `i, Φinf`: proved limits of the very same stage families `(Ds,hs,fs,Ψ,Φ,is)` returned at TH:80. No separately chosen stage family.
- `I₀`: choice from the proved unique inverse locus, TH:91–95. The locus is total and unique on Ω. Arbitrary off-Ω values are permitted by the signed total-function contract and never used in a restricted assertion or to form KO.
- `KCω`: choice of a proved complex extension for the same `Φinf(θ,i(I₀ω))`, TH:97–104. Off-Ω values are similarly unused.
- `K`: explicit lambda `fun ω θ => Φinf (θ, i (I₀ ω))`, TH:125. No independently selected torus or fallback identity.
- D₀, Ω, Dstar, r, Hr, KO in the signed type are exact transparent abbreviations. Hr uses the existing frozen field via its real Hamiltonian, in `(angle,action)` order; r is the final enlargement, not an oscillator radius.

Conditional premises of `phi_injOn`, `i_injOn`, and `lattice_torus_of_limit` are acceptable distinctly named helpers, not source claims. In `two_scale_kam` the only premises are the exact signed `KamHyp` and `hL`. No conclusion-shaped field or instance is added.

## Private-interface release gate: actual application chain

The full commands live in the named source files, not in the original design signature appendix. This table records the exact interfaces consumed and their proved inputs. “Private” here describes the design's conditional implementation boundary; the Lean commands are public for cross-module use.

| Package / helper command | Conditional inputs and actual discharge |
|---|---|
| P23-16 `iterative_all` (ToriSetup:101) | ToriSetup:108–115 obtains one `iterative H` witness tuple and projects its hypotheses, recurrence, conjugacy and symplecticity into S:ActionSteps, P:PsiSteps, Q:StageSteps. These are outputs, not premises on H. |
| P23-17 `limit_actions_of_steps` (LimitActions:289) | ToriSetup:130 applies it to S; returns i with uniform convergence, stage membership, block/tail/location/frequency bounds. TH:83 applies it again to the **same S**, obtaining i′ only to recover the 2560n Lipschitz output absent from ToriLimit. TH:84–90 proves i′I=iI on Ds 0 by `tendsto_nhds_unique` for the same actionChain is. Off-base equality is neither claimed nor needed. |
| P23-18 `PsiSteps.psi_lip_of_steps` (LimitMapPack:77) | Consumed inside P's finite/limit map bounds (e.g. LimitMapLimit:34), P being the projected same-witness stage recurrence. Domain maps, reality, scalar contraction, displacement and sum premises all come from P. |
| P23-18 `PsiSteps.limit_phi_real_of_steps` (LimitMapReal:40) | ToriSetup:131–134 proves `hD : ∀j, i '' Ds 0 ⊆ realTube (Ds j) ((seq p j).ρ/2)` from the just-produced action location, then applies P to hD, retaining Φinf,hU,hL,hper,hbk. |
| P23-18 `PsiSteps.limit_phi_strip_of_steps` (LimitMapStrip:127) | ToriSetup:142 applies P to the same hD and hU, at I∈i''Ds 0. No fresh real limit; angle strip extension and derivative convergence concern these finite maps and this Φinf. |
| P23-20 `tori_limit_of_iterative` (ToriSetup:121) | TH:80 supplies only H and obtains h0,S,P,Q,T for the exact tuple above. T bundles the proved limit/strip outputs; finite stage Lagrangian slices are proved from Q.symp in ToriSetup:143–159. |
| P23-20 `tori_estimates_of_limit` (ToriEstimates:165) | TH:103,135 and TT:120: H, `hD0` (TH:81), same T, and `hΩ0` (TH:96) supply every premise. Produces complex extension, bounds and location. |
| P23-20 `tori_lagr_of_limit` (ToriLagr:55) | TH:136 and TT:121: H,T,hΩ0; returns analyticity, derivative estimate, injective derivative, zero symplectic pullback of the same K. |
| P23-20 `tori_invariance_of_limit` (ToriInvariance:124) | TT:125: H,P,Q,hD0,T,hI₀. All are the same TH:80 outputs. Frequency is realFreq h (I₀ω), rewritten to ω at TH:138, without another 2π conversion. |
| P23-21 `actionsMeas_of_limit` / `torusMeas_of_limit` | Applied inside MeasureJoint:167–168 by `meas_torus_final`, using TH:115–121 block/action-Lipschitz data, TH:105–114 map defect and the essential block SUP bound; scalar smallness and positivity from H. |
| P23-21 `meas_actions_of_limit` / `TorusMeas.meas_torus_of_limit` | The latter is applied at MeasureJoint:170 to the produced TorusMeas; it consumes the former through `volume_tube_diff` (MeasureTorus:66). No cover or measure claim is assumed. |
| P23-21 `meas_torus_final` (MeasureJoint:144) | TH:176–177 passes H,hblk,hlipI,hlipΦ′,hsup,hI₀ and literal reflexive factorization for the same i,I₀,Φinf,K. Unique inverse locus proves surjectivity onto D₀ via exists_omega, then ko_eq identifies the exact KO. |

The optional earlier applicability witnesses `limit_map_of_iterative`, `tori_of_iterative`, and `meas_of_iterative` are not mixed into this proof. Their smaller existential conclusions are unnecessary: P23-22 directly uses the richer ToriSetup joint construction. Every consumed conditional premise is discharged; no separate independent stage/limit selection survives. N2's applicability requirement is met for this final assembly.

## Exhaustive node-to-proof inventory

All node rows in design revision 2 whose Lean mapping contains `two_scale_kam` are listed below. The upstream locators identify the proved local work; the application locator identifies its discharge on this theorem's common witnesses. This is an applicability audit of already audited P23-17–21, not an independent reproof of every upstream analytic lemma.

| Node | Lean discharge / application | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:two-scale-kam` | TH:36–177, exact signed theorem | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:limit-actions` | LimitActions:289 limit_actions_of_steps; ToriSetup:130; TH:80,83–90 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-wp` | LimitActionsChain:63 chain_mem, :116 chain_freq; T.i_mem/i_freq via ToriSetup:130 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-tele` | LimitActions:82 chain_block_le, :251 tail_sum_le, :270 chain_limit; T.i_conv/i_tail; TH:80,84–85 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-loc` | LimitActions:289 location output; ToriSetup:131–133 hD; T.i_tube in TH:80 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-lip` | LimitActions:173 chain_lip, :215 prod_le, :289 limit bound; TH:83–90,119–121 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:psi-lip` | LimitMapPack:77 psi_lip_of_steps; LimitMapLimit:34; ToriSetup:134; TH:80 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-dom` | LimitMapPsi:143 psi_step; LimitMapPack:77 domain clause; same P from TH:80 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-disp` | LimitMapPack:45 psi_disp, :77; same P via ToriSetup:134 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-lip` | LimitMapLip psi_lip_step; LimitMapPack:77; P via ToriSetup:134 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-sum` | LimitMapPack:77 scalar sums; LimitMapLimit:34; ToriSetup:134 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:limit-phi` | LimitMapReal:40 + LimitMapStrip:127; ToriSetup:134–142; TH:80,105–114,131–133 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-tele` | LimitMapDisp:55 phi_disp_complex, LimitMapLimit:160 phi_disp_real; T.phi_block via ToriSetup:134; TH:110–114 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-cauchy` | LimitMapLimit:121 phi_limit; LimitMapReal:40; T.phi_conv/phi_lip; TH:80,105–109 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-per` | LimitMapReal:40 periodicity output; T.phi_per; TH:131–133,151–154 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-an` | LimitMapStrip:127; T.phi_strip; ToriEstimates:55 tori_complex_ext; TH:97–104 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:estimates` | ToriEstimates:165 tori_estimates_of_limit; TH:103,135; TT:120 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:es-sup` | ToriEstimates:165 block triangle and complex ext; TH:103,135,139–140 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:es-loc` | ToriEstimates:165 strict location output; TT:120–125 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:lagr` | ToriLagr:55 tori_lagr_of_limit; TH:136; TT:121,124–125 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lg-cauchy` | ToriLagr:55 strip Cauchy derivative bound; TH:136,141–142 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lg-j` | ToriSetup:143–159 from Q.symp to T.stage_lagr; same tuple TH:80 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lg-lim` | ToriEstimates:35 StripLimit.fderiv_tendsto; ToriLagr:55; TT:121,125 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:invariance` | ToriInvariance:124 tori_invariance_of_limit; TT:125; TH:137–138 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:inv-dphi` | ToriInvConj:118 PsiSteps.psiR_fderiv_bound; same P in TT:125 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:inv-err` | ToriInvStage:103 field_err, ToriInvariance:67 stage_err_le; TT:125 with same P,Q,T | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:meas-actions` | MeasureActions:54 meas_actions_of_limit via MeasureTorus:66; TH:176 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:ma-ext` | MeasureActions:54 cover on action defect; ActionsMeas from TH:176 hblk,hlipI | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:ma-meas` | MeasureActions:54 Lipschitz image bound via MeasureTorus:66; TH:176 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:meas-torus` | MeasureTorus:137 meas_torus_of_limit; MeasureJoint:170; TH:176–177 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-split` | MeasureTorus:137 hcover/h1 and :66 volume_tube_diff; TH:176 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-ext` | MeasureScaled:31 scaled_cover; MeasureTorus:156; TH:176 hsup,hlipΦ′ | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-pre` | MeasureTorus:107 preimage_mem, :159 hΨinv′; TH:176 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-meas` | MeasureScaled:81 lip_image_scaled; MeasureTorus:184 h2; TH:176 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-shell` | MeasureTorus:94 shell_subset and :66 volume_tube_diff; TH:176 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-sum` | MeasureTorus:137 final calc and complementConstant; TH:176–177 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-constr` | TH:80–104,125–127; same stage, limit, inverse and complex witnesses | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-ad` | TH:134–142 from tori_estimates_of_limit and KC choice | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-bc` | TT:109–129, TH:136–139; Lagrangian immersion and exact flow invariance | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-inj` | TH:122–124,143–168; TI:33–107 for inverse locus and both inverse estimates | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-meas` | TH:169–177; same KO under ko_eq and exact cell estimate | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:tori#data` | TH:91–104,125: unique I₀ and literal K on same i,Φinf | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:measure#data` | TH:44–49,76–78,169–177: exact D₀,KO,r and same family | PASS | Same proved witnesses; no new source premise. |

Inventory count: **43 distinct design rows**; no omitted or duplicate row mapped to `two_scale_kam`. The separately mapped inv-conj/inv-lim nodes are consumed through `conj_field` (ToriInvConj:72) / `curve_limit_field` (ToriInvLimit:31), using the proved real symplectic and curve-limit bridges, inside tori_invariance_of_limit.

## IsLatticeTorus L1–L6 and inverse refutation checks

| Clause | Discharge in TheoremTorus:120–129 | Verdict |
|---|---|---|
| L1 real analyticity | `an` from tori_lagr_of_limit | PASS |
| L1 location | `e3 θ` from tori_estimates_of_limit, trivial angle membership | PASS |
| L1 Hr differentiable at Kθ | H.Hr_differentiableAt (e3 θ); 32Êρhat≤ρ from smallness and rhoHat≤ρ; real inclusion lies in open coefficientDom | PASS |
| L2 lattice law | T.phi_per at `(θ,i I₀)`; simp angleShift | PASS |
| L3 injective modulo parameter lattice | H.phi_injOn T.phi_lip gives θ=θ′ under equal values; k=0 witnesses the literal clause | PASS |
| L4 derivative injective | `inj` from tori_lagr_of_limit, same angular derivative | PASS |
| L5 zero symplectic pullback | `lag` from tori_lagr_of_limit, same first derivatives | PASS |
| L6 dynamics | tori_invariance_of_limit H P Q hD0 T hI₀, with frequency identity rewritten TH:138 | PASS |

Cross-frequency shifted equality is stronger than the single-torus L3 requirement: TH:143–161 first uses the full Φinf lattice law, then its injectivity, then i injectivity and inverse identities. It does not infer a global inverse Lipschitz bound from bounded inverse derivative on a disconnected source. TI:62 uses ball continuation on a ball contained in actionNbhd, coverage pulls the second frequency into that ball, and **source injectivity** identifies its preimage with the original J. TI:91 separates close/far pairs for the global estimate and explicitly assumes bounded D. Empty Ω/D cases and off-carrier total-function values do not enter any substantive premise.

## Hygiene and independent execution receipts

All commands ran from `/root/code/KAM-inp-p2322`; no two audit Lean/Lake invocations overlapped.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2322 KAM.Planetary.TwoScale.TheoremInverse KAM.Planetary.TwoScale.TheoremTorus KAM.Planetary.TwoScale.Theorem
   ```

   Exit **0**. Gate output: `[inp-gate] slot 2 acquired 17:40:06 for KAM.Planetary.TwoScale.TheoremInverse KAM.Planetary.TwoScale.TheoremTorus KAM.Planetary.TwoScale.Theorem`. Final output: `Build completed successfully (9205 jobs).` Replayed dependency warnings concern unused variables, deprecated API/tactic names and unused simp arguments; the scoped theorem reports only the unused signed `hL`. No elaboration error or default-heartbeat failure.

2. Independent signature application, full-type equality and axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2322Audit.lean
   ```

   Exit **0**. The probe imports the actual Theorem module, copies the signed command under `audit_signed_two_scale_kam`, and proves it with exactly `by exact two_scale_kam H hL`. It also elaborates `example : type_of% @audit_signed_two_scale_kam := @two_scale_kam`. No fixture definitions or signature-file `sorry` bodies are imported. Literal axiom output:

   ```text
   'KAM.Planetary.KamHyp.freq_real' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.realFreq_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.exists_inverse_locus' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.inverse_local' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.inverse_global' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.rhoHat_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.phi_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.i_injOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.KamHyp.Hr_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lattice_torus_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.two_scale_kam' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. One kernel-replay invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Theorem KAM.Planetary.TwoScale.TheoremInverse KAM.Planetary.TwoScale.TheoremTorus
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Planetary.TwoScale.TheoremTorus
   replaying KAM.Planetary.TwoScale.TheoremInverse
   replaying KAM.Planetary.TwoScale.Theorem
   ```

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**. Complete output:

   ```text
   Lean lines over 100 characters:
   /root/code/KAM-inp-p2322/KAM/Planetary/TwoScale/Theorem.lean:48:114
   /root/code/KAM-inp-p2322/KAM/Planetary/TwoScale/Theorem.lean:68:113
   /root/code/KAM-inp-p2322/KAM/Planetary/TwoScale/Theorem.lean:69:101
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (815 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   **FAIL beyond the permitted stale-root exception:** the three overlong lines are F1. Module-system, frozen-anchor guard and ABI subchecks pass; the overall lint command does not pass.

5. Static checks and scope:

   - Whole-library declaration scan using `scripts/check_lean_modules.py`'s comment-aware namespace/visibility scanner: **813 files; 11 scoped exported theorems; no qualified-name duplicates**. Each scoped fully qualified name occurs exactly once. Same-tail names such as `freq_real` in another namespace are distinct Lean names, not root shadowing. No `_root_` declaration, replacement norm instance, or root shadow module is introduced.
   - Recursive local-KAM import traversal: **159 modules; no provider imports; no frozen theorem imports**, hence no DRAFT_SORRY or improperly imported sealed anchor. Frozen definitions are allowed and retain the actual carriers/fields/forms.
   - All three scoped files have copyright comment, `module`, public interface imports, module docstring and exposed public section. Physical counts: **111, 133, 183**, all below 1500. No sorry/admit/axiom/unsafe/opaque, resource override or EuclideanSpace in scoped source; full lint results recorded separately.
   - Exact declaration byte comparison: **True**, hash and length above. No new definitions. Upstream P23-18's ten modules and P23-21's five modules also match their stored independent-audit SHA256 receipts byte for byte; applicability was checked afresh here.
   - `git diff --check`: exit **0**, no output for the audit's working-tree delta. This does not assert that every inherited branch diff is whitespace-clean.
   - `git diff 8978933d..HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit **0**, empty. The requested broad `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **nonempty** because of inherited KAM.lean, as detailed in scope.
   - Temporary probe and replay/lint logs are removed after their outputs are incorporated here. Final status preserves the pre-existing untracked handoff; the only added deliverable is this report.

## F1 — mandatory lint failure outside the permitted exception

Severity: medium; blocks package release under the supplied brief's hygiene requirement. Exact fresh lint diagnostics:

```text
Lean lines over 100 characters:
/root/code/KAM-inp-p2322/KAM/Planetary/TwoScale/Theorem.lean:48:114
/root/code/KAM-inp-p2322/KAM/Planetary/TwoScale/Theorem.lean:68:113
/root/code/KAM-inp-p2322/KAM/Planetary/TwoScale/Theorem.lean:69:101
```

The three lines are the signed `let Hr` and the two action-block estimates. The handoff's claim that lint reports only the stale generated root does **not** reproduce at fcbf6466. That commit wraps two helper-file lines, leaving these three lines unchanged. They are within the byte-exact signed header/type, so an auditor cannot silently reflow only production while continuing to claim byte equality. Reconcile the production and authoritative signature formatting under the responsible author's authority, preserving the full type, then rerun the exact-byte check and lint. No mathematical type change is required. This audit changes neither source nor lint policy.

## Notes, suspected source defects and deviations

- N1 (integration/baseline): the literal broad protected-path diff is nonempty only in inherited generated KAM.lean, as recorded above. Do not describe this check as empty. P23-22 itself changes no protected path. The expected stale-root lint exception does not erase that separate git-diff result.
- Upstream P23-20 N1 remains a documentation note: `ToriInvConj.lean:16` states `1 + κ₁κ₂/10`, while its proved bound at :118–121 is `1 + κ₁κ₂`. The actual uniform bound is sufficient for invariance and is what this assembly consumes; this report does not silently claim the sharper overview bound.
- No new mathematical source/blueprint defect was found in the scoped proof. Existing blueprint corrections remain explicit: P3b's final source-gap paragraph quotes CP10's “a unique real-analytic embedding”; phase translations prevent that uniqueness, so only the unique **source inverse locus** is claimed here. The same paragraph restricts the global inverse Lipschitz statement to bounded D; TI:83 follows it. P3b estimates/source note distinguishes the slow-action `+1` term from the printed `+Mhat/M`; TH:69 preserves `+1`. These are carried source dispositions, not fresh PDF verification or new errata.
- P23-22 proves no provider equality or frozen root theorem. In particular this report is not a fresh proof audit of the downstream P-G provider, physical reconstruction, positive measure, strict measure inequalities, or all inherited packages. No new deviation is introduced by this report.

Final report checks: 43 unique mapped nodes, all 11 new theorem axiom receipts, all three scoped source hashes unchanged, and no report trailing whitespace. No production files were edited.
