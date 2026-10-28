# P23-22 independent audit 2 — delta review

Audit date: 2026-10-28. HEAD: `7c13609ac1ef132381be20a2e152b9ac134ddd24`.
Baseline: `843596ee` (round-1 report); sole fix commit: `7c13609a`.

**Overall verdict: PASS WITH NOTES. F1 is resolved.** The source-lint gate passes modulo the expressly permitted stale generated `KAM.lean`. The exact elaborated signed type, build, axioms and kernel replay pass. No frozen anchor is assigned or sealed by this infrastructure package.

This is the requested delta audit: round 1's mathematics, ten helper reviews, 43-node inventory and N2 applicability review are carried forward because the only delta is three authorized statement line wraps. This report distinguishes that carried review from the fresh checks below. The explicit user destination overrides the common brief's main-worktree destination. Only this report and temporary worktree-local `.lake/abi-scratch/` files were written; no production, frozen, manifest, generated-root or git state was changed.

Read the current AGENTS.md, PLAN, DECISIONS, common brief, handoff/AUDIT FOCUS, round-1 report, P23 revision-2 N2/shared-witness gate, relevant Track P conventions, P3a theorem and P3b assembly, scoped Lean modules and relevant frozen phase/field/form/downstream P-G anchor. No provider/frozen-type seal probe applies to this package.

## Delta and signature evidence

`git diff 843596ee..HEAD` contains exactly one path, `KAM/Planetary/TwoScale/Theorem.lean`, and exactly three replacements: the old Hr lambda line (48) and first/last action-block bound lines (68/69) each gain one newline and continuation indentation. Both removal of all whitespace and whitespace-split token comparison of the **entire file** return `True`. More strictly, reversing exactly those three replacements reconstructs the baseline bytes exactly. The proof body starting `:= by\n  classical` is byte-identical. Both helper files are byte-identical to baseline; no import or dependency change occurs.

The original signature file `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` still has the original formatting. The baseline docstring/header/type is byte-identical to that file; the new docstring is still byte-identical; the new header/type is token-identical, **not raw-byte-identical**. This is the explicitly authorized whitespace repair, not a renewed claim of literal byte equality. The full signed-statement probe below verifies elaborated type equality independently, including every binder, let, carrier, constant and conclusion.

| File under `KAM/Planetary/TwoScale/` | Lines | SHA256 |
|---|---:|---|
| TheoremInverse.lean | 111 | `daed7b7472343027fa9c3d545d3509485fb0fdcfcf9dbc07d519a69a6aee8775` |
| TheoremTorus.lean | 133 | `3d87be0e062d311a20d6339547c0faef22bae4ae67c968317d8bae1ce97c0776` |
| Theorem.lean | 186 | `bb2700886e8ca3f324b428c070ef520606f9f7b37001b0a0112f9c4dda57f735` |

The requested `git diff inp...HEAD` was inspected (scoped proof diff and broad stat). Current `inp` is `a341f3aebaad7052378f3fd4846d8619bf8da9d9`; Git warns of multiple merge bases and uses `35ffbe5a7ec4f5cca39e3da808039c0b88c0d4de`. The literal `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **nonempty only for inherited KAM.lean**. Frozen/manifest/README are unchanged in that comparison. `git diff 843596ee..HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. This retains round-1 N1 rather than describing the broad protected diff as empty.

## Public declarations and definitions

The following review is carried from round 1 under the verified token-identical delta; TH locators are adjusted to current lines. All eleven axiom checks are rerun below.

| Node / role | Public declaration | Verdict | Reason / locator |
|---|---|---|---|
| real frequency | `KamHyp.freq_real` | PASS | TI:33–36: holomorphy and reality on the actual source neighborhood, positive widths. |
| inverse uniqueness | `KamHyp.realFreq_injOn` | PASS | TI:39–45: complex injectivity on actionNbhd restricts through the real inclusion. |
| source inverse locus | `KamHyp.exists_inverse_locus` | PASS | TI:48–52: unfold Ω image membership; recovered point lies in D₀, uniqueness from realFreq_injOn. |
| inverse local | `KamHyp.inverse_local` | PASS | TI:55–80: apply inverse ball continuation at I with δ=ρ,m=Mbar; coverage and global source injectivity identify the preimage with J. No convexity of D assumed. |
| inverse global | `KamHyp.inverse_global` | PASS | TI:83–107: close pairs use local bound, far pairs use bounded-D diameter and ρ/Mbar≤frequency distance; exact max factor. |
| radius comparison | `rhoHat_le_rho` | PASS | TT:34–35: literal minimum, stronger unconditional statement for arbitrary ScaleData. |
| phase injectivity | `KamHyp.phi_injOn` | PASS | TT:38–58: distinctly conditional generic helper; defect coefficient 768nÊ<1 from 8192nÊ<1, positive scaling. Applied TH:125–126 and TT:125. |
| action injectivity | `KamHyp.i_injOn` | PASS | TT:61–74: same argument with 2560nÊ<1. Applied TH:127 with proved limit-action bound. |
| Hamiltonian differentiability | `KamHyp.Hr_differentiableAt` | PASS | TT:77–101: 32Êρhat≤ρ; real inclusion in open coefficientDom; kam_G_diff restricted to ℝ and composed with inclusion and reCLM. |
| lattice torus assembly | `lattice_torus_of_limit` | PASS | TT:109–129: explicit conditional helper; every hypothesis supplied from one iterative output in TH:140. L1–L6 below. |
| `bpP:p3:two-scale-kam` | `two_scale_kam` | PASS | TH:36–180: exact signed source-premise contract, all conditional inputs discharged; F1 is resolved by the authorized token-identical wrapping. |


No new `def`, `abbrev`, `structure` or instance exists in the three scoped modules. Local constructions retain their round-1 classification: `i` and `Φinf` are the same proved stage limits; `I₀` is chosen from the proved unique source inverse locus on Ω; `KC` from the proved complex extension; and `K ω θ := Φinf (θ, i (I₀ ω))`. Off-Ω total-function values do not enter the restricted claims or KO. D₀, Ω, Dstar, r, Hr and KO are literal local lets in the signed type. No new premise, conclusion-shaped assumption, fallback or carrier change is introduced.

## N2 and complete node inventory (carried, locators updated)

The unchanged proof obtains one tuple `(Ds,hs,fs,Ψ,Φ,is,i,Φinf,h0,S,P,Q,T)` from `tori_limit_of_iterative H` at TH:83. TH:86–93 identifies the second action-limit witness by uniqueness for the same action chain. TH:94–107 chooses the source inverse and complex extension. The limit/action/map/torus/measure applications and all their conditional discharges are unchanged. `lattice_torus_of_limit` still discharges L1–L6 at TT:120–129 from the same H,P,Q,T; TH:140–141 rewrites its frequency to ω. `meas_torus_final` at TH:179–180 receives the same i,I₀,Φinf,K and proved block, Lipschitz, SUP and inverse-locus outputs. Hence round-1 N2 PASS is preserved; no private conditional premise becomes a source premise and no unrelated witnesses are selected.


All node rows in design revision 2 whose Lean mapping contains `two_scale_kam` are listed below. The upstream locators identify the proved local work; the application locator identifies its discharge on this theorem's common witnesses. This is an applicability audit of already audited P23-17–21, not an independent reproof of every upstream analytic lemma.

| Node | Lean discharge / application | Verdict | Reason |
|---|---|---|---|
| `bpP:p3:two-scale-kam` | TH:36–180, exact signed theorem | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:limit-actions` | LimitActions:289 limit_actions_of_steps; ToriSetup:130; TH:83,86–93 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-wp` | LimitActionsChain:63 chain_mem, :116 chain_freq; T.i_mem/i_freq via ToriSetup:130 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-tele` | LimitActions:82 chain_block_le, :251 tail_sum_le, :270 chain_limit; T.i_conv/i_tail; TH:83,87–88 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-loc` | LimitActions:289 location output; ToriSetup:131–133 hD; T.i_tube in TH:83 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:la-lip` | LimitActions:173 chain_lip, :215 prod_le, :289 limit bound; TH:86–93,122–124 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:psi-lip` | LimitMapPack:77 psi_lip_of_steps; LimitMapLimit:34; ToriSetup:134; TH:83 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-dom` | LimitMapPsi:143 psi_step; LimitMapPack:77 domain clause; same P from TH:83 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-disp` | LimitMapPack:45 psi_disp, :77; same P via ToriSetup:134 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-lip` | LimitMapLip psi_lip_step; LimitMapPack:77; P via ToriSetup:134 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pl-sum` | LimitMapPack:77 scalar sums; LimitMapLimit:34; ToriSetup:134 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:limit-phi` | LimitMapReal:40 + LimitMapStrip:127; ToriSetup:134–142; TH:83,108–117,134–136 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-tele` | LimitMapDisp:55 phi_disp_complex, LimitMapLimit:160 phi_disp_real; T.phi_block via ToriSetup:134; TH:113–117 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-cauchy` | LimitMapLimit:121 phi_limit; LimitMapReal:40; T.phi_conv/phi_lip; TH:83,108–112 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-per` | LimitMapReal:40 periodicity output; T.phi_per; TH:134–136,154–157 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lp-an` | LimitMapStrip:127; T.phi_strip; ToriEstimates:55 tori_complex_ext; TH:100–107 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:estimates` | ToriEstimates:165 tori_estimates_of_limit; TH:106,138; TT:120 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:es-sup` | ToriEstimates:165 block triangle and complex ext; TH:106,138,142–143 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:es-loc` | ToriEstimates:165 strict location output; TT:120–125 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:lagr` | ToriLagr:55 tori_lagr_of_limit; TH:139; TT:121,124–125 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lg-cauchy` | ToriLagr:55 strip Cauchy derivative bound; TH:139,144–145 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lg-j` | ToriSetup:143–159 from Q.symp to T.stage_lagr; same tuple TH:83 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:lg-lim` | ToriEstimates:35 StripLimit.fderiv_tendsto; ToriLagr:55; TT:121,125 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:invariance` | ToriInvariance:124 tori_invariance_of_limit; TT:125; TH:140–141 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:inv-dphi` | ToriInvConj:118 PsiSteps.psiR_fderiv_bound; same P in TT:125 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:inv-err` | ToriInvStage:103 field_err, ToriInvariance:67 stage_err_le; TT:125 with same P,Q,T | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:meas-actions` | MeasureActions:54 meas_actions_of_limit via MeasureTorus:66; TH:179 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:ma-ext` | MeasureActions:54 cover on action defect; ActionsMeas from TH:179 hblk,hlipI | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:ma-meas` | MeasureActions:54 Lipschitz image bound via MeasureTorus:66; TH:179 | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:meas-torus` | MeasureTorus:137 meas_torus_of_limit; MeasureJoint:170; TH:179–180 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-split` | MeasureTorus:137 hcover/h1 and :66 volume_tube_diff; TH:179 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-ext` | MeasureScaled:31 scaled_cover; MeasureTorus:156; TH:179 hsup,hlipΦ′ | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-pre` | MeasureTorus:107 preimage_mem, :159 hΨinv′; TH:179 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-meas` | MeasureScaled:81 lip_image_scaled; MeasureTorus:184 h2; TH:179 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-shell` | MeasureTorus:94 shell_subset and :66 volume_tube_diff; TH:179 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:mt-sum` | MeasureTorus:137 final calc and complementConstant; TH:179–180 | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-constr` | TH:83–107,128–130; same stage, limit, inverse and complex witnesses | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-ad` | TH:137–145 from tori_estimates_of_limit and KC choice | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-bc` | TT:109–129, TH:139–142; Lagrangian immersion and exact flow invariance | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-inj` | TH:125–127,146–171; TI:33–107 for inverse locus and both inverse estimates | PASS | Same proved witnesses; no new source premise. |
| `stepP:p3:pf-meas` | TH:172–180; same KO under ko_eq and exact cell estimate | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:tori#data` | TH:94–107,128: unique I₀ and literal K on same i,Φinf | PASS | Same proved witnesses; no new source premise. |
| `bpP:p3:measure#data` | TH:44–50,79–81,172–180: exact D₀,KO,r and same family | PASS | Same proved witnesses; no new source premise. |

Inventory count: **43 distinct design rows**; no omitted or duplicate row mapped to `two_scale_kam`. The separately mapped inv-conj/inv-lim nodes are consumed through `conj_field` (ToriInvConj:72) / `curve_limit_field` (ToriInvLimit:31), using the proved real symplectic and curve-limit bridges, inside tori_invariance_of_limit.


## Fresh execution receipts

PENDING_RECEIPTS

## Findings, limitations and errata

F1 is **closed**: the three overlong statement lines are wrapped without any token, proof or elaborated-type change, and the fresh lint has no line-length diagnostic. The authorized formatting difference from the untouched signature file is explicitly recorded above.

N1 remains the inherited generated-root integration note: broad protected-path diff is nonempty for KAM.lean; its stale-root lint diagnostic is the sole permitted exception. No generated file was regenerated.

Round-1 source dispositions remain unchanged, rather than newly verified against a PDF: `ToriInvConj.lean:16` says `1 + κ₁κ₂/10`, whereas the proved bound at :118–121 is `1 + κ₁κ₂`, sufficient for the consumed invariance argument. P3b's final source-gap paragraph quotes CP10's “a unique real-analytic embedding”; phase translations prevent that uniqueness, so this theorem claims a unique source inverse locus. The global inverse estimate explicitly requires bounded D, and the slow-action estimate retains `+1` as in P3a rather than silently asserting the printed `+Mhat/M`. No fresh source/blueprint defect is introduced by the whitespace delta, and no auditor deviation or production edit was made.

This delta audit preserves the independently reviewed package result; it does not seal downstream P-G, physical reconstruction, positive measure, strict measure estimates or unrelated inherited packages.
