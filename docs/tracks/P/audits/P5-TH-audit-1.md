# P5-TH independent package audit 1

Overall verdict: **PASS WITH NOTES** for P5-TH's exact signed helper contract. No frozen anchor is proved or sealed by this package; P-G remains outside this audit's proof-closure claim. No blocking finding in the three scoped modules. Notes concern inherited branch differences, the declared preliminary-radius split, and a stronger internal smallness condition.

## Scope and authority

Audit snapshot: `/root/code/KAM-inp-p5th`, HEAD `afb6301ada1fe4b0bd140a128551240afb925275`; observed `inp` ref `4edfdd76ba941faaf07d7c979c8cc92821074160`. Scope, per AUDIT FOCUS: only `KAM/Planetary/PGAssembly/Threshold.lean`, `ThresholdAlg.lean`, `ThresholdLimits.lean`. Report location follows the user's explicit absolute path, overriding the generic brief's instruction to write in main inp. No production edits or state-changing git operations.

Read AGENTS.md, PLAN, DECISIONS, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, P5-TH-handoff, P45 design (P5-TH row, proof plan, departures and Revision 4), design audits 1–4, Track P statement, blueprint Part 5 thresholds/parameter facts/rK and Part 4 collar interfaces. Read frozen ProperlyDegenerateKAM and its relevant Phase, cylinder, cylinderCell, fast-diffeomorphism, secular-Birkhoff and Diophantine carriers; compared PGData with the frozen telescope. Traced Parameters, Scales, FrequencyDefs/FrequencyBounds and Collar at the actual consumer boundary. Upstream packages are dependencies, not independently re-audited proof packages here.

The shared signature file is absent in this worktree; used `/root/code/KAM-inp/.drafts/design/P45Signatures.lean`, SHA256 `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402`, matching design audit 4's controlling revision. Whitespace-normalized declarations for `pgCgamma`, `rstar`, `pgRstar`, `param_facts`, `r_k` match exactly; definition bodies for pgCgamma and pgRstar also match. Placement of pgCgamma in ThresholdAlg is transparent through Threshold's public import.

No provider export is added: provider/frozen-type equality and frozen sealing-body probes are **not applicable**. Instead the scratch probe copies each signed theorem under a fresh `audit_` name and supplies `by exact rstar d`, `by exact param_facts d`, or `by exact r_k d r mu h`; definition equalities are tested with `rfl`. This checks the actual signed telescope without importing the unproved frozen P-G theorem.

## Refutation findings and fidelity

1. **Data-only quantifiers preserved.** pgCgamma, pgScales, pgAnalytic and pgRstar depend only on d. rstar selects R0/2 from an eventual conjunction valid for every smaller positive r; the proof does not choose constants after r or mu. PGData contains the literal frozen source premises, with no KAM or measure conclusion added. PGAnalyticSpec and PGScaleSpec are proved outputs of upstream existence theorems, not additional assumptions to rstar.
2. **The smallness split is proved, not assumed.** ThrStatic and ThrSmall merely name explicit finite conjunctions. eventually_static/small prove them. thr_dynamic takes these separate numerical premises under its own distinct name, then rstar discharges them. Likewise thr_e5/e6 are explicitly conditional arithmetic helpers; neither replaces the signed result. No heartbeat, recursion or synthesis-budget override occurs. The former large arithmetic step is split into thr_e5/e6.
3. **Finite, positive volume is earned.** volume_V_pos uses nonempty open V and boundedness before toReal. thr_volumes uses V covered by the core and its collar/bad-frequency pieces; it cancels only finite ofReal errors. The half/quarter factors are paid explicitly. param_facts uses the volume-preserving block product, positive shell width ell>=r^2/4 and finite containing V. No unproved core positivity or measurability assumption is introduced.
4. **The shell factor keeps dimension.** chat_Ehat_lt proves both minimum branches from PGScaleSpec, giving rK<rhoHat/(256n). rhoHat<=l1/2 and ell>=r^2/4 give 2*rK/ell<=k1*sqrt(r)/(64n). k1*sqrt(r)<=1/12 and b<=n give b*x<=1/768; exp(1/768)<2 finishes. All denominators used for inequalities have positive guards.
5. **Preliminary radius is the signed contract.** Blueprint Part 5:154 includes “(C_*+1) sqrt(r_*) <= 1/2”. This package does not supply that final measure-loss shrink. P45 design:435, 508, 1931 explicitly assigns it to `finalRadius` in P5-LO. Thus PASS applies to the signed preliminary rstar, not the entire final blueprint threshold in isolation. Other param-facts conclusions are distributed across rstar and param_facts as designed; no conclusion is silently discarded.
6. **Stronger internal bound, harmless.** Blueprint Part 5:152 says `C_gamma sqrt(r_*) <= 2 Mbar_0 rho_c`. Threshold:45 instead proves `Cgamma*sqrt(r)/2 <= rho`, which is stronger since M0>=1. It suffices together with Kbar^(tau+1)>=1 for rhoBar<=rho. This is achievable by shrinking the data-only radius, not an extra source premise. Also R<exp(-(tau+1)) and R<exp(-1) are stronger than the printed exp(-1/5) cutoff and justify monotonic/log guards. The design explicitly records these guards.

## Declaration-by-declaration disposition

All names below are in `KAM.Planetary`. Helper rows implement substeps of the indicated node; a PASS for a conditional helper means its stated arithmetic contract is valid, not that its numerical premises are source assumptions.

| Node | Declaration (module:line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p5:rstar` | `tendsto_rpow_mul_log_rpow` (ThresholdLimits:24) | PASS | m>0; arbitrary real q; log-power dominated at infinity after inversion. |
| `bpP:p5:rstar` | `le_log_inv_of_le_exp_neg` (ThresholdLimits:34) | PASS | Positive r and exponential upper bound give the stated logarithmic lower bound. |
| `bpP:p5:rstar` | `eventually_lt_of_continuousAt` (ThresholdLimits:41) | PASS | Continuity at zero and strict value bound; restriction to the positive filter. |
| `bpP:p5:rstar` | `eventually_exists_radius` (ThresholdLimits:45) | PASS | Unpacks a positive punctured neighbourhood; no selection assumption. |
| `bpP:p5:rstar` | `sq_log_mono` (ThresholdLimits:50) | PASS | Valid stronger sufficient guard q<=log(1/R); proves all-smaller-r bound. |
| `bpP:p5:rstar` | `pgWidth_lt_one` (ThresholdAlg:26) | PASS | Uses the produced extension delta<1. |
| `bpP:p5:rstar` | `one_le_pgKappa` (ThresholdAlg:29) | PASS | Width positivity and width<1. |
| `bpP:p5:rstar` | `one_le_log_inv` (ThresholdAlg:32) | PASS | Positive r<=exp(-1). |
| `bpP:p5:rstar` | `LP_mul_mu_le` (ThresholdAlg:39) | PASS | Multiplies the source mu bound by LP<=log; no assumption LP*mu is small. |
| `bpP:p5:rstar` | `sqrt_LP_mu_le` (ThresholdAlg:56) | PASS | Square-root estimate from LP*mu upper bound. |
| `bpP:p5:rstar` | `B1_le` (ThresholdAlg:68) | PASS | First maximum branch; cancellation of log powers. |
| `bpP:p5:rstar` | `B2_le` (ThresholdAlg:86) | PASS | Second branch; consumes explicit r^2 log^(tau+1)<=1. |
| `bpP:p5:rstar` | `ratio_le` (ThresholdAlg:100) | PASS | Positive LPmu and lower bound on g; algebraic conditional lemma. |
| `bpP:p5:rstar` | `pgScales_G_pos` (ThresholdAlg:136) | PASS | Derived from produced PGScaleSpec and M0>=1. |
| `bpP:p5:rstar` | `pgCgamma_pos` (ThresholdAlg:142) | PASS | Positivity of the exact data-only formula. |
| `bpP:p5:rstar` | `params_gammaBar` (ThresholdAlg:148) | PASS | Definitional unfolding of both branches. |
| `bpP:p5:rstar` | `gammaBar_le` (ThresholdAlg:153) | PASS | Combines B1/B2 on ThrRange; exact Cgamma. |
| `bpP:p5:rstar` | `gammaBar_ratio` (ThresholdAlg:166) | PASS | Uses first branch to cancel sqrt(LP*mu); exact running powers. |
| `bpP:p5:rstar` | `params_rhoHat` (ThresholdAlg:189) | PASS | Unfolds the minimum, including denominator 3*C1*K0^(tau+1). |
| `bpP:p5:rstar` | `params_Ehat` (ThresholdAlg:193) | PASS | Exact C1^2*r^5/rhoHat^2. |
| `bpP:p5:rstar` | `params_rK` (ThresholdAlg:196) | PASS | Exact 32*Ehat*rhoHat. |
| `bpP:p5:rstar` | `pgK0_pos` (ThresholdAlg:199) | PASS | Positive width and max 1 ensure positivity for every scales record. |
| `bpP:p5:rstar` | `pgScales_k0_pos` (ThresholdAlg:204) | PASS | From k0>=C1^2>=1. |
| `bpP:p5:rstar` | `pgScales_k1_pos` (ThresholdAlg:209) | PASS | Produced scale specification. |
| `bpP:p5:rstar` | `params_rhoHat_pos` (ThresholdAlg:211) | PASS | Both minimum branches strictly positive when r>0. |
| `bpP:p5:rstar` | `rhoHat_le_l1` (ThresholdAlg:220) | PASS | Minimum upper bound, valid without admissibility. |
| `bpP:p5:rstar` | `chat_Ehat_lt` (ThresholdAlg:223) | PASS | Both min branches checked using the two strict scale inequalities; no assumed KAM bound. |
| `bpP:p5:rstar` | `rK_lt` (ThresholdAlg:258) | PASS | Retains chat>=8192*(a+b) and yields 1/(256*(a+b)). |
| `bpP:p5:rstar` | `params_Kbar` (ThresholdAlg:273) | PASS | Exact logarithmic cutoff. |
| `bpP:p5:rstar` | `params_l1` (ThresholdAlg:276) | PASS | Exact k1*r^(5/2). |
| `bpP:p5:rstar` | `params_ell` (ThresholdAlg:279) | PASS | Exact upper-trimmed width r^2/2-3*l1. |
| `bpP:p5:rstar` | `params_l2top` (ThresholdAlg:284) | PASS | Exact upper endpoint r^2/2-2*l1. |
| `bpP:p5:rstar` | `params_rhoBar` (ThresholdAlg:287) | PASS | Exact gammaBar/(2*M0*Kbar^(tau+1)). |
| `bpP:p5:rstar` | `rpow_five_halves` (ThresholdAlg:290) | PASS | Positive-base real-power identity. |
| `bpP:p5:rstar` | `l1_le_rhoBar` (ThresholdAlg:293) | PASS | Second branch and G>=2*M0*k1; valid for arbitrary mu on the positive logarithmic range. |
| `bpP:p5:rstar` | `rhoBar_le` (ThresholdAlg:316) | PASS | Uses M0>=1 and Kbar^(tau+1)>=1; deliberately coarse sufficient estimate. |
| `bpP:p5:rstar` | `volume_V_pos` (Threshold:50) | PASS | Open nonempty V has positive measure; bounded V has finite measure before toReal. |
| `bpP:p5:rstar` | `ev_lt` (Threshold:54) | PASS | Positive constants dominate r eventually. |
| `bpP:p5:rstar` | `pgBoundary_spec` (Threshold:57) | PASS | Unpacks the original boundary witness. |
| `bpP:p5:rstar` | `eventually_static` (Threshold:63) | PASS | All eleven explicit static conditions proved from limits and source data. |
| `bpP:p5:rstar` | `eventually_small` (Threshold:100) | PASS | Nine r-only conditions proved by continuity or r^5 log(1/r) tending to zero. |
| `bpP:p5:rstar` | `pgAnalytic_dio` (Threshold:136) | PASS | Projects the proved one-scale measure clause; not an input field of PGData. |
| `bpP:p5:rstar` | `gammaBar_pos` (Threshold:142) | PASS | Positive second branch; arbitrary mu is allowed. |
| `bpP:p5:rstar` | `ofReal_mul_volume` (Threshold:158) | PASS | Requires finite volume before replacing it by ofReal(toReal). |
| `bpP:p5:rstar` | `thr_volumes` (Threshold:162) | PASS | Set covers and finite ENNReal cancellation prove half/quarter bounds; no positive-core premise. |
| `bpP:p5:rstar` | `rpow_three_halves` (Threshold:239) | PASS | Positive-base power identity. |
| `bpP:p5:rstar` | `thr_key` (Threshold:242) | PASS | Totalized-field multiplicative identity, also valid at zero denominators. |
| `bpP:p5:rstar` | `thr_q_pos` (Threshold:249) | PASS | Positivity of the explicit ratio denominator. |
| `bpP:p5:rstar` | `thr_e5` (Threshold:255) | PASS | Combines proved gammaBar_ratio and explicit smallness with rK bound; scoped arithmetic helper. |
| `bpP:p5:rstar` | `thr_e6` (Threshold:272) | PASS | Combines proved gammaBar_ratio and explicit r^4 bound; scoped arithmetic helper. |
| `bpP:p5:rstar` | `thr_dynamic` (Threshold:294) | PASS | Discharges every mu-dependent conjunct; calls thr_e5/e6 and thr_volumes. |
| `bpP:p5:rstar` | `rstar` (Threshold:361) | PASS | Exact signed statement; chooses R0/2 from eventual_static/small before r,mu. |
| `bpP:p5:rstar` | `thrRange_of_admissible` (Threshold:396) | PASS | Recovers log endpoint bounds using sq_log_mono and R<exp(-(tau+1)). |
| `bpP:p5:param-facts` | `param_facts` (Threshold:407) | PASS | Exact signed statement; shell width positive and joinedActions volume finite/positive. |
| `bpP:p5:rK` | `r_k` (Threshold:443) | PASS | Exact signed statement; ell>=r^2/4, rhoHat<=l1/2 and b<=a+b give exp(1/768)<2. |

## Definition classification

| Definition | Classification and whole-carrier review |
|---|---|
| `pgCgamma` (ThresholdAlg:128) | Exact signed real formula G*(30/width)^(tau+1), meaningful for all PGData; width and G are proved positive. No fallback. |
| `ThrRange` (ThresholdAlg:132) | Explicit proposition naming positivity, exponential/log bounds and the mu range; no witness/default value. Proved from admissible by thrRange_of_admissible. |
| `ThrStatic` (Threshold:32) | Eleven exact static numerical propositions on arbitrary real R. No hidden fields or assumed theorem; eventually_static constructs them. |
| `ThrSmall` (Threshold:41) | Nine explicit r-only inequalities on arbitrary real r; eventually_small proves them. Stronger rho condition is recorded above. |
| `pgRstar` (Threshold:393) | Exact signed choice `(rstar d).choose`, supported by a proved existential for every PGData. No empty-choice branch, junk witness or altered carrier. |

There are no other new defs, abbrevs or structures in scope. All scalar powers, logs, square roots and divisions have Lean's total real meanings outside the stated inequality ranges; no theorem relies on an unintended fallback. Definitions required to unfold are covered by the exposed public noncomputable section.

## Hygiene and independent checks

1. **Targeted build**, serial after lint's first run:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p5th KAM.Planetary.PGAssembly.Threshold
   [inp-gate] slot 2 acquired 14:43:13 for KAM.Planetary.PGAssembly.Threshold
   Build completed successfully (9133 jobs).
   ```

   Exit **0**. Upstream replay emitted unused-variable/simp warnings; no warning or error in Threshold, ThresholdAlg or ThresholdLimits. No clean/update/cache retrieval or root regeneration. The first build gate wait was stopped before acquiring a slot when lint's internal Lean invocation was recognized; that stopped wait is not counted as a build receipt.

2. **Signed-type applications and all public theorem axioms**:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P5THAudit.lean
   ```

   Exit **0**, no warnings or errors. Fresh-name theorem copies apply the exact signed declarations with all explicit arguments in order; pgCgamma/pgRstar definitional equalities close by rfl. All 55 new public theorems and pgRstar have exactly the permitted axiom set. Exact axiom output:

```text
'KAM.Planetary.tendsto_rpow_mul_log_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.le_log_inv_of_le_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eventually_lt_of_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eventually_exists_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sq_log_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgWidth_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.one_le_pgKappa' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.one_le_log_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.LP_mul_mu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sqrt_LP_mu_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.B1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.B2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgScales_G_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgCgamma_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_gammaBar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gammaBar_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gammaBar_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_rhoHat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_Ehat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_rK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgK0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgScales_k0_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgScales_k1_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_rhoHat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rhoHat_le_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chat_Ehat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rK_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_Kbar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_ell' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_l2top' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.params_rhoBar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rpow_five_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.l1_le_rhoBar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rhoBar_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_V_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ev_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgBoundary_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eventually_static' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.eventually_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgAnalytic_dio' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.gammaBar_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ofReal_mul_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thr_volumes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rpow_three_halves' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thr_key' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thr_q_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thr_e5' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thr_e6' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thr_dynamic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rstar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.thrRange_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.param_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.r_k' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.pgRstar' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. **Kernel replay**, one invocation for the three scoped modules:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGAssembly.Threshold KAM.Planetary.PGAssembly.ThresholdAlg KAM.Planetary.PGAssembly.ThresholdLimits
   replaying KAM.Planetary.PGAssembly.ThresholdLimits
   replaying KAM.Planetary.PGAssembly.ThresholdAlg
   replaying KAM.Planetary.PGAssembly.Threshold
   ```

   Exit **0**. No kernel error. This checks actual compiled proof terms, not signature stubs.

4. **Lint**:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (711 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Exit **1**, solely the explicitly permitted stale generated root. All other lint checks pass. The generated root was not edited.

   Procedure note: an initial lint invocation omitted the explicit LEAN_NUM_THREADS/nice prefixes. It finished with the same four status lines, but is not the controlled validation receipt used below. The full lint was rerun with both prefixes, serially after kernel replay. The initial build was still waiting at its gate and was stopped before its slot acquisition; no two audit Lean invocations were run concurrently.

5. **Static integrity**: exact file sizes 511/339/91 lines, all below 1500. Required copyright/module/public imports/docstring/public section present. No sorry, admit, axiom, unsafe, opaque, resource override, or EuclideanSpace in the scoped files. The regex scan over all KAM declaration names found no duplicate new theorem/definition name outside the three files; the compiled build also confirms no declaration collision in the import closure. Recursively inspected all 87 project modules in that closure: **no frozen theorem and no provider import**, hence no DRAFT_SORRY import or manifest-state exception to adjudicate. Frozen definitions are legitimate imports. Scope diff is exactly three new files, 941 lines. Report and scratch are the only audit writes.

6. **Final integrity**: `git diff --check -- docs/tracks/P/audits/P5-TH-audit-1.md`: exit 0. `git diff --no-index --check /dev/null docs/tracks/P/audits/P5-TH-audit-1.md`: exit 1 (new-file difference), no whitespace diagnostics. Python additionally checks the untracked report for trailing whitespace, balanced fences and terminal newline. Scoped source hashes and the shared signature hash were rechecked unchanged. All audit-created scratch files/logs removed; git status contains only the new audit report and the pre-existing untracked handoff. No tracked file changed.


## Branch-level exception and remaining limits

The required command `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**. Git warns `inp...HEAD: multiple merge bases, using 439541a66c17f2ecf1e4c9c3dc4d41f48539beae`. It shows inherited KAM.lean import additions, AveragingMean/Most frozen body seals and their two manifest state changes DRAFT_SORRY->SEALED. README has no diff. This fails the literal branch-wide empty-diff check, and is explicitly not concealed as a clean branch. The P5-TH commits themselves touch only Threshold*.lean (verified with scoped git history); none of these inherited edits is caused by P5-TH. With the user's express three-file focus, this is a landing/integration note, not a mathematical rejection of Threshold. The full branch contains unrelated work not audited here.

No new suspected defect in a pinned paper or frozen statement was found. Existing P45 design notes and design-audit 4's off-cylinder extension correction remain upstream context; this audit does not independently certify CP10/CP11 allegations. The stronger internal rho condition is the only threshold-proof deviation noted above. Missing finalRadius is an explicit package boundary, not theorem closure. No Lean production file, frozen file, manifest, generated root, README, handoff or shared signature was edited by this audit.
