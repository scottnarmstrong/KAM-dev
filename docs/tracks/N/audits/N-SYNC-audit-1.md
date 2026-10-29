# N-SYNC independent audit 1

Overall verdict: **FAIL for the graph sync as a literal closure ledger**. Four checked PROVED rows require correction: `stepN:p1:co-exc`, `stepN:p1:co-time`, sampled `stepN:p1:co-conc`, and `bpN:p12:ext-dep#picard`. No Lean theorem refutation was found. The fresh kernel-replay attempt ended by SIGTERM (returncode -15) without output, so the required replay-success gate is **not established**; this is an additional validation limitation, not evidence of a kernel defect. The conditional constants lemmas and the alternate Picard construction remain valid; their package PASS receipts do not erase the different graph contracts.

Auditor: maud-nsync-1. Date: 2026-10-29. Report destination is exactly `/root/code/KAM-inp-nsync/docs/tracks/N/audits/N-SYNC-audit-1.md`, overriding the generic brief’s main-worktree destination. Read AGENTS, PLAN, DECISIONS, the package brief, N-SYNC-handoff, track-N statement, relevant frozen definitions, graph contracts, blueprint source ranges, actual Lean proof blocks and cited audit rows. Only this report is a persistent edit. No graph, Lean source, frozen file, manifest, generated root, README or git state was edited.

HEAD `0421fbbdb6bfb401c9d6d5f151314df0365eb591`; comparison `inp` `24adb6afac052a3bcb089cf72be220a93cd7b5db`. `git diff inp...HEAD` contains only the 23-line N-SYNC-handoff addition. The sync is already inherited: merge `257bf90231f8caa77b3253381c8a23d407542e08` against its first parent contains the graph changes. Comparing node blocks with that first parent independently gives **235 newly PROVED nodes**. The working graph has 657 PROVED, 48 EXTERNAL, 20 BYPASSED and 3 NOT_STARTED rows.

No new provider or frozen seal belongs to N-SYNC. Provider=frozen-type and copied seal-body tests are therefore N/A for this documentation package; this is not a new seal audit of the six existing N anchors. Their manifest state is SEALED and the guard/ABI checks pass. Graph-source gaps below do not change those manifest states.

| Existing anchor | N-SYNC anchor verdict |
|---|---|
| N-HEAD-C | PASS WITH NOTES: unchanged SEALED anchor; no new seal claimed, graph findings remain |
| N-ZERO | PASS WITH NOTES: unchanged SEALED anchor; outside the selected proof-slice review |
| N-QC | PASS WITH NOTES: unchanged SEALED anchor; outside the selected proof-slice review |
| N-PARTIAL-CONVEX | PASS WITH NOTES: unchanged SEALED anchor; outside the selected proof-slice review |
| N-AVERAGING-MEAN | PASS WITH NOTES: unchanged SEALED anchor; local dependence checked below, no whole-anchor re-audit |
| N-AVERAGING-MOST | PASS WITH NOTES: unchanged SEALED anchor; local dependence checked below, no whole-anchor re-audit |

## Method and reproducible sample

CONFIRMED PROVED means either a literal declaration or an actual local proof block under a PROVED parent, with the explicit audit coverage allowed by ruling (b). A blueprint line-range audit row can cover several steps; declaration existence alone cannot. CONFIRMED BYPASSED means the N-local route is replaced by the identified route; it does not assert that the omitted numerical conclusion was proved, or that imported mathematics has no analogous calculation.

The mandatory review is a conservative superset of the requested Part-3 cases: **every one of the 38 newly PROVED `stepN:p3:*` rows**, not just rows with explicit step ids in their audit tables. Together with all 20 BYPASSED rows, the five Part-10 calls, the three constants steps, the two combined definitions rows, the two Picard rows, and p9#data, there are **71 mandatory rows** (50 PROVED, 20 BYPASSED, 1 NOT_STARTED).

Sample algorithm: parse NODE blocks in current DEPGRAPH; compare LEAN_STATUS with `git show 257bf902^1:docs/graph/N/DEPGRAPH.md`; select current PROVED / previous not-PROVED; exclude mandatory rows; sort the remaining 185 node ids lexicographically; run Python `random.Random(20261029).sample(candidates, 30)`. The sample table retains draw order. Seed **20261029**. This is a sample of the remaining newly PROVED population, not of old PROVED rows or the complete graph. Total reviewed **101 distinct nodes**, **97 CONFIRMED and 4 WRONG**.

## Mandatory table

All file paths in evidence are relative to this worktree; module-qualified names in LEAN_REF retain their namespaces. Reasons supply the independently checked current proof location. Prior audit locators are receipts, not replacements for checking the code.

| Node | Recorded status | Lean declaration / module | Verdict and evidence |
|---|---|---|---|
| `stepN:p1:cc-unit` | BYPASSED | KAM.Nekhoroshev.conic_coercive (KAM/Nekhoroshev/Interfaces/ConicCoercive.lean) | CONFIRMED BYPASSED (D27): ConicCoercive:91-175 keeps N=euclid ξ, handles zero directly and never assumes a unit vector. Alternate homogeneous proof. |
| `stepN:p1:nc-decay` | BYPASSED | KAM.Nekhoroshev.norm_convert (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean) | CONFIRMED BYPASSED (D27): ConstantsAnalytic:173-182 calls the imported summation theorem as a whole. This N-local decay-route step is skipped; coefficient decay remains proved and used inside the imported K theorem. |
| `stepN:p1:nc-sum` | BYPASSED | KAM.Nekhoroshev.norm_convert (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean) | CONFIRMED BYPASSED (D27): Same alternate imported summation route; the coth sum is not an unpaid estimate. This is a bypass of the N-local decomposition, not a claim that geometric summation disappears transitively. |
| `stepN:p1:co-pert` | PROVED | KAM.Nekhoroshev.const_perturbation (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean) | CONFIRMED: ConstantsAnalytic:102-125 constructs WBound on the full complex tube with geometric width s/2; the other conjuncts supply exactly 2π times the bound and Fε≤ε*. The period conversion is an already proved dependency, not an extra h premise. |
| `stepN:p1:co-exc` | PROVED | KAM.Nekhoroshev.const_exceptional (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean) | WRONG → NOT_STARTED / SOURCE_GAP: ConstantsAnalytic:128-146 requires hh : HeadHyp p h; the graph expressly does not supply the h hypotheses. See F1. |
| `stepN:p1:co-time` | PROVED | KAM.Nekhoroshev.const_time (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean) | WRONG → NOT_STARTED / SOURCE_GAP: ConstantsAnalytic:148-171 requires HeadHyp and exports a conditional numerical Ω comparison, not the unconditionally positive maximum in this source contract. See F1. |
| `bpN:p1:norm-convert#decay-route` | BYPASSED | KAM.Nekhoroshev.norm_convert (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean) | CONFIRMED BYPASSED (D27): The explicit N decay route is replaced by the graph’s summation-route, exactly the call in ConstantsAnalytic:182. |
| `stepN:p3:lip-mathlib` | PROVED | KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean) | CONFIRMED under (b): Lipschitz:35-45 constructs local Lipschitz neighborhoods and applies the compact local-to-global theorem; N3-1:42,105 covers the route. |
| `stepN:p3:lip-explicit` | BYPASSED | KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean) | CONFIRMED BYPASSED (D27): Lipschitz:35-45 uses Mathlib compact local-to-global Lipschitz rather than the contradiction/subsequence proof. |
| `stepN:p3:lip-bdd` | PROVED | KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean) | CONFIRMED under (b): Lipschitz:40-42 applies compact continuous boundedness and max C 0. This exact bound is present in the proof block. |
| `stepN:p3:lip-contra` | BYPASSED | KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean) | CONFIRMED BYPASSED (D27): No violating sequence is constructed in gen_lip; compact local-to-global Lipschitz is applied directly. |
| `stepN:p3:lip-compact` | BYPASSED | KAM.ODE.gen_lip (KAM/ODE/Lipschitz.lean) | CONFIRMED BYPASSED (D27): No common-limit subsequence or large-k contradiction is used in gen_lip. |
| `stepN:p3:uc-delta` | PROVED | KAM.ODE.gen_uniform_compact, KAM.ODE.closedThickening (KAM/ODE/Lipschitz.lean) | CONFIRMED under (b): Lipschitz:61-68 obtains δ>0, identifies closedThickening with cthickening, proves inclusion and compactness. The explicit minimum-distance formula is replaced by Mathlib’s equivalent existence construction. |
| `stepN:p3:uc-data` | PROVED | KAM.ODE.gen_uniform_compact (KAM/ODE/Lipschitz.lean) | CONFIRMED under (b): Lipschitz:69-75 applies gen_lip to the compact thickening and includes each center ball. M,L are uniform in the center. |
| `stepN:p3:up-cell` | PROVED | KAM.ODE.gen_uniform_periodic (KAM/ODE/UniformPeriodic.lean) | CONFIRMED under (b): UniformPeriodic:42-52 chooses min δ0 1 and compact [-1,2]^n × cthickening δ K before choosing centers. |
| `stepN:p3:up-translate` | PROVED | KAM.ODE.gen_uniform_periodic (KAM/ODE/UniformPeriodic.lean) | CONFIRMED under (b): UniformPeriodic:54-103 translates all points of each ball by the same floor-angle vector. Periodicity and translation isometry transfer both bounds. |
| `stepN:p3:short-boot` | PROVED | KAM.ODE.gen_short_forward, KAM.ODE.gen_short (KAM/ODE/Existence.lean) | CONFIRMED under (b): Existence:67-83 constructs the closed bootstrap set and its initial point; :120-143 handles reversed time. N3-45:18-19 covers the source proof range. |
| `stepN:p3:short-ext` | PROVED | KAM.ODE.gen_short_forward (KAM/ODE/Existence.lean) | CONFIRMED under (b): Existence:83-111 uses continuity to find a short next segment and a mean-value bound to extend the closed bootstrap set. |
| `stepN:p3:ue-pl` | PROVED | KAM.ODE.gen_uniform_exist, KAM.ODE.picard_lindelof_ball (KAM/ODE/Existence.lean) | CONFIRMED under (b): Existence:155-160 applies picard_lindelof_ball with bound max M 1 and time δ/max M 1, so its radius inequality is discharged. |
| `stepN:p3:ue-stay` | PROVED | KAM.ODE.gen_uniform_exist (KAM/ODE/Existence.lean) | CONFIRMED under (b): Existence:161-176 applies gen_short and converts strict displacement to ball membership and W membership. |
| `stepN:p3:loc-red` | PROVED | KAM.ODE.gen_local (KAM/ODE/Existence.lean) | CONFIRMED under (b): Existence:184-199 obtains uniform data on the compact set (singleton for local existence); ε is chosen before x0,t0. |
| `stepN:p3:uq-compact` | PROVED | KAM.ODE.gen_uniqueness (KAM/ODE/Uniqueness.lean) | CONFIRMED under (b): Uniqueness:33-47 proves compactness and W inclusion for the union of the two solution images of the closed time segment. |
| `stepN:p3:uq-lip` | PROVED | KAM.ODE.gen_uniqueness (KAM/ODE/Uniqueness.lean) | CONFIRMED under (b): Uniqueness:46 invokes gen_lip on those actual compact images. The Lipschitz bound is produced rather than assumed. |
| `stepN:p3:uq-apply` | PROVED | KAM.ODE.gen_uniqueness (KAM/ODE/Uniqueness.lean) | CONFIRMED under (b): Uniqueness:56-77 uses Mathlib’s right/left closed-segment uniqueness and order-connectedness, with no global confinement premise. |
| `stepN:p3:ext-right` | PROVED | KAM.ODE.gen_extend (KAM/ODE/Maximal.lean) | CONFIRMED under (b): Maximal:89-153 extends at a greatest endpoint; :122-133 glues the two one-sided derivatives into HasDerivAt. |
| `stepN:p3:ext-left` | PROVED | KAM.ODE.gen_extend (KAM/ODE/Maximal.lean) | CONFIRMED under (b): Maximal:155-192 applies right extension to reversed time and -F, then proves both endpoints absent and the interval open. |
| `stepN:p3:max-union` | PROVED | KAM.ODE.gen_maximal (KAM/ODE/Maximal.lean) | CONFIRMED under (b): Maximal:244-277 constructs a nonempty GoodInterval union and identifies it with eIoo Tm Tp. No interval existence is assumed. |
| `stepN:p3:max-glue` | PROVED | KAM.ODE.gen_maximal (KAM/ODE/Maximal.lean) | CONFIRMED under (b): Maximal:278-295 uses choice only on good intervals, proves independence by gen_uniqueness_inter, and proves local solution/initial value. The default x0 outside the union is unused by solution claims. |
| `stepN:p3:max-max` | PROVED | KAM.ODE.gen_maximal (KAM/ODE/Maximal.lean) | CONFIRMED under (b): Maximal:296-343 extends a competitor interval, embeds it in the union, and derives interval and solution uniqueness. |
| `stepN:p3:cont-setup` | PROVED | KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean) | CONFIRMED under (b): Continuation:45-63 chooses ε = δ/max M 1 and t1 = max tstar (T−ε/2), within the maximal interval and within ε of the finite endpoint. |
| `stepN:p3:cont-alpha` | PROVED | KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean) | CONFIRMED under (b): Continuation:64-100 constructs the local solution at z(t1), identifies it with z on the overlap by uniqueness, and defines the glued curve. |
| `stepN:p3:cont-glue` | PROVED | KAM.ODE.gen_continuation (KAM/ODE/Continuation.lean) | CONFIRMED under (b): Continuation:91-110 proves the glued solution by open-set union and contradicts maximality beyond T. Time reversal supplies the other endpoint. |
| `stepN:p3:conf-noexit` | PROVED | KAM.ODE.gen_confinement (KAM/ODE/Continuation.lean) | CONFIRMED under (b): Continuation:158-182 applies continuation if Tp≤τ (and symmetrically for Tm); the supplied a priori bound yields the required uniform-data membership. |
| `stepN:p3:conf-concl` | PROVED | KAM.ODE.gen_confinement (KAM/ODE/Continuation.lean) | CONFIRMED under (b): Continuation:183-193 restricts to [-τ,τ], retains the a priori bound, and proves agreement with every solution on every smaller symmetric interval. |
| `stepN:p3:exit-closed` | BYPASSED | KAM.ODE.gen_exit (KAM/ODE/Exit.lean) | CONFIRMED BYPASSED (D27): Exit:56-68 closes only exitSet ∩ Icc 0 a for an actual exit a and minimizes that compact set; it does not need closedness on all of J∩[0,∞). |
| `stepN:p3:exit-min` | PROVED | KAM.ODE.gen_exit (KAM/ODE/Exit.lean) | CONFIRMED under (b): Exit:56-78 minimizes on an actual compact segment, proves global leastness and strict positivity; no open-domain infimum outside J is used. |
| `stepN:p3:exit-bdry` | PROVED | KAM.ODE.gen_exit (KAM/ODE/Exit.lean) | CONFIRMED under (b): Exit:79-89 proves the safe half-open prefix and frontier membership by continuity at the first exit. |
| `stepN:p3:exit-sup` | PROVED | KAM.ODE.gen_exit (KAM/ODE/Exit.lean) | CONFIRMED under (b): Exit:90-104 proves both supremum inequalities for exactly the safe-prefix set. |
| `stepN:p3:hs-deriv` | PROVED | KAM.ODE.ham_smooth (KAM/ODE/Hamiltonian.lean) | CONFIRMED under (b): Hamiltonian:47 applies fderiv_of_isOpen to get the C^k derivative map. N3-2:24 covers the blueprint range. |
| `stepN:p3:hs-comp` | PROVED | KAM.ODE.ham_smooth (KAM/ODE/Hamiltonian.lean) | CONFIRMED under (b): Hamiltonian:48-52 uses continuous-linear evaluation of DH and the minus sign, then product/Pi smoothness. |
| `stepN:p3:per-field` | PROVED | KAM.ODE.ham_periodic (KAM/ODE/Hamiltonian.lean) | CONFIRMED under (b): Hamiltonian:127-135 proves eventual equality under translation, fderiv equality (including totalized derivatives), and field periodicity. |
| `stepN:p3:per-sol` | PROVED | KAM.ODE.ham_periodic (KAM/ODE/Hamiltonian.lean) | CONFIRMED under (b): Hamiltonian:136-138 applies gen_symmetry_translate with the same angleShift, retaining actual derivative and membership. |
| `stepN:p3:red-mem` | PROVED | KAM.ODE.ham_reduction (KAM/ODE/Hamiltonian.lean) | CONFIRMED under (b): Hamiltonian:160-168 proves the product-domain/action-membership equivalence in ham_reduction. N3-2:32 covers this local step. |
| `bpN:p3:s-N#data` | PROVED | KAM.Nekhoroshev.Data, KAM.Nekhoroshev.Wdom (KAM/Nekhoroshev/Interfaces/Setting.lean) | CONFIRMED: Interfaces/Setting:28-39 gives Data and literal Wdom = univ × ball 0 (R+s); H is frozen realHamiltonian. ODE/Specialization:64-77,174-212 supplies open U⊆ball 0 (R+s) at consumers. Frozen IsAnalyticPerturbation includes ε≥0; no missing assumption is hidden in Data. P1-1/P1-2 and N3-10b audit rows jointly cover these objects. |
| `stepN:p3:hi-cite` | PROVED | KAM.Nekhoroshev.holo_input (KAM/Nekhoroshev/Interfaces/HoloReal.lean) | CONFIRMED under (b): Interfaces/HoloReal:352-361 packages C∞, the real/complex field identity and angle periodicity. Source premises are Data, not regularity assumed as an extra input. |
| `stepN:p3:le-red` | PROVED | KAM.Nekhoroshev.ODE.local_exist (KAM/Nekhoroshev/ODE/Specialization.lean) | CONFIRMED under (b): ODE/Specialization:64-77 constructs C1 and the exact frozen/general solution equivalence from holo_input and ham_reduction. |
| `stepN:p3:le-apply` | PROVED | KAM.Nekhoroshev.ODE.local_exist (KAM/Nekhoroshev/ODE/Specialization.lean) | CONFIRMED under (b): ODE/Specialization:100-114 applies gen_local and gen_uniqueness through that equivalence, on the entire interval. |
| `stepN:p3:uc-apply` | PROVED | KAM.Nekhoroshev.ODE.uniqueness_closed (KAM/Nekhoroshev/ODE/Specialization.lean) | CONFIRMED under (b): ODE/Specialization:174-186 applies uniqueness on Icc(-L,L) and treats negative L as an empty interval; agreement on shorter intervals uses restriction. |
| `stepN:p3:cg-set` | PROVED | KAM.Nekhoroshev.ODE.confinement_glue (KAM/Nekhoroshev/ODE/Specialization.lean) | CONFIRMED under (b): ODE/Specialization:202 obtains uniform periodic data on univ × closedBall I0 ρ using compactness and the literal hball inclusion. |
| `stepN:p3:cg-glue` | PROVED | KAM.Nekhoroshev.ODE.confinement_glue (KAM/Nekhoroshev/ODE/Specialization.lean) | CONFIRMED under (b): ODE/Specialization:203-212 translates the a priori bound through hiff and hmem, invokes gen_confinement and translates back, including all competing smaller-interval solutions. |
| `bpN:p4:n-zero` | BYPASSED | coeff_mul (KAM/Weighted/Algebra.lean); coefficients_series (KAM/Weighted/Coefficients.lean) | CONFIRMED BYPASSED (D27): Weighted API works for arbitrary n, including zero. coeff_mul/coefficients_series/cauchy_theta use the dimension-generic APIs; no separate singleton branch is required. |
| `stepN:p4:c1-line` | BYPASSED | general_cauchy (KAM/Weighted/Parametric.lean) | CONFIRMED BYPASSED (D27): Parametric:88-98 applies the imported closed-ball operator estimate and takes the radius limit. Strip/Cauchy:53-77 does a unit-direction line reduction internally. The skipped step is the N-local arbitrary-u reduction, not Cauchy’s underlying one-variable argument. |
| `stepN:p5:tr-h` | BYPASSED | transform (KAM/Canonical/Transform.lean) | CONFIRMED BYPASSED (D27): Transform:148-176 uses first-order flow integration and integral_flow_hasSum for the bounded bracket, instead of high-order Taylor remainders of unbounded h. |
| `stepN:p5:fl-symmetry#real-restriction` | BYPASSED | flow_e (KAM/Canonical/FlowInverse.lean) | CONFIRMED BYPASSED (D27): FlowInverse:196 proves realness by imaginary-part linear maps and Picard integral/convergence estimates; the separate real-restriction C1 bridge is absent. |
| `stepN:p7:cj-real` | BYPASSED | conjugation (KAM/Nekhoroshev/Stability/Conjugation.lean) | CONFIRMED BYPASSED (D27): Conjugation:108-152 uses the complex symplectic field identity and real inclusion intertwining. It never proves det Y=±1 for a real Jacobian. Real domain membership is still explicitly proved by reMap_mem. |
| `stepN:p7:se-stop` | BYPASSED | stopped_extension (KAM/Nekhoroshev/Stability/Transfer.lean) | CONFIRMED BYPASSED (D27): Transfer:49,86 uses closed initial segments and gen_exit with a closed cylinder; it does not construct a connected component of the safe set. |
| `stepN:p7:se-noexit` | BYPASSED | stopped_extension (KAM/Nekhoroshev/Stability/Transfer.lean) | CONFIRMED BYPASSED (D27): Transfer stay_forward excludes first exit by continuity and the closed cylinder, rather than a component-endpoint argument. |
| `stepN:p7:nr-t3` | BYPASSED | nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean) | CONFIRMED BYPASSED (D27): Nonresonant uses drift_bound on the entire transformed orbit and a uniform remainder gradient; the transfer first-exit construction is unnecessary. |
| `stepN:p7:nr-caseB` | BYPASSED | nonresonant (KAM/Nekhoroshev/Stability/Nonresonant.lean) | CONFIRMED BYPASSED (D27): Nonresonant:108-114 estimates drift directly when κ<6; no identity canonical transformation and transfer tuple are manufactured. |
| `stepN:p7:ne-terms` | BYPASSED | no_exit (KAM/Nekhoroshev/Stability/Resonant.lean) | CONFIRMED BYPASSED (D27): Resonant:388-411 uses A≤mr²/16, B≤5mr²/16, C≤mr²/24 instead of the printed Young split. These are adequate for its different contradiction. |
| `stepN:p7:ne-contra` | BYPASSED | no_exit (KAM/Nekhoroshev/Stability/Resonant.lean) | CONFIRMED BYPASSED (D27): Resonant:388-411 contradicts 225mr²/512≤5mr²/12, not the source’s mΔ²/3 versus mr²/4 comparison. |
| `stepN:p7:l2-cone` | BYPASSED | resonant_lemma2 (KAM/Nekhoroshev/Stability/Resonant.lean) | CONFIRMED BYPASSED (D27): Resonant:447-514 uses cone_arith: 347/360≈0.963889<1. This does not prove <0.941. It contradicts the strict >ℓ‖Δ‖ alternative, which is all the proved parent needs. S7-6:89-95 explicitly audits the weaker numerical route. |
| `stepN:p10:hc-setting` | PROVED | confinement (KAM/Nekhoroshev/Assembly/Confinement.lean) | CONFIRMED under ruling (b): Confinement:75-96 actually constructs Theorem1Setting, and :119-128 supplies ε′ smallness and WBound separately. N10-3-audit-1:30 explicitly covers this local obligation; no stability premise is bundled. |
| `stepN:p10:cf-setting` | PROVED | confinement (KAM/Nekhoroshev/Assembly/Confinement.lean) | CONFIRMED under ruling (b): Confinement:75-96 actually constructs Theorem1Setting, and :119-128 supplies ε′ smallness and WBound separately. N10-3-audit-1:30 explicitly covers this local obligation; no stability premise is bundled. |
| `stepN:p10:cf-orbit` | PROVED | confinement, cf_orbit (KAM/Nekhoroshev/Assembly/Confinement.lean) | CONFIRMED under (b): Confinement:99-104 projects the derivative; :118-128 proves initial membership in P and realH = frozen realHamiltonian by rfl. The standalone export is narrower; the audited proof block covers the compound step. |
| `stepN:p10:cf-branch` | PROVED | confinement, cf_branch (KAM/Nekhoroshev/Assembly/Confinement.lean) | CONFIRMED under (b): Confinement:127 obtains the full thm1 branch ka; :130-138 proves its frequency premise; :139-140 then specializes to the shorter horizon. The full-T0 implication exists internally. N10-3-audit-1:32 and audit-2:24 distinguish this from signature equality. |
| `stepN:p10:cf-trans` | PROVED | confinement (KAM/Nekhoroshev/Assembly/Confinement.lean) | CONFIRMED under (b): Confinement:153-170 applies cp_rad, proves τ≤2T exp(E), invokes the branch, and weakens half-radius to ρ. Constants precede h,f,ε. |
| `bpN:p9#data` | NOT_STARTED | - | CONFIRMED as currently NOT_STARTED: the requested definitions audit is supplied below. Numerical and domain objects are faithful on the intended locus; total realH differs from the blueprint’s zero extension outside W. Do not infer whole-carrier equality or silently promote this compound convention row without recording that deviation. |
| `bpN:p9:s-blocks#data` | PROVED | theoremCover (KAM/Nekhoroshev/Poschel/Elementary.lean); CoverParams.radius, CoverParams.alpha, CoverParams.delta, actionBlock (KAM/Nekhoroshev/ResonanceGeometry/Covering.lean); maximalK (KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean) | CONFIRMED: Elementary:42 specializes p,b,K,A; Covering:32-47 defines lam,radius,alpha,delta,actionBlock literally; Maximal:30 defines maximalK. N89-P1:26 and G7:32-39 are definitions rows, not merely theorem receipts. Validity is proved by cover_valid/elementary, not put into the raw record as a stability assumption. |
| `bpN:p12:ext-dep#complete-contraction` | PROVED | contractingWith_picardMap, picard_family (KAM/Nekhoroshev/Averaging/PicardFamilies.lean); contractingWith_voltMap, linear_family (KAM/Nekhoroshev/Averaging/PicardDerivatives.lean) | CONFIRMED: PicardFamilies:54-70 constructs a closed complete subtype of bounded continuous families; contractingWith_picardMap and picard_family:252-300 give the fixed point and uniform geometric Picard error. PicardDerivatives:139-201 contracts on the complete operator-family space and constructs its fixed point. No finite-dimensional Banach theorem is misapplied to that space. This does not by itself assert derivative-iterate convergence. |
| `bpN:p12:ext-dep#picard` | PROVED | ext_dep (KAM/Nekhoroshev/Averaging/LocalDependence.lean); picard_family (KAM/Nekhoroshev/Averaging/PicardFamilies.lean) | WRONG → BYPASSED for this literal construction, with ext_dep as the alternate route (or retain NOT_STARTED until such routing is accepted): LocalDependence:381-423 uses closedBall x0 δ, upper bounds L0,Λn and a radius-δ trap. It does not construct the graph’s closedBall x0 (2δ) with the same δ,r and exact suprema. See F3. |

## Random sample of 30 other newly PROVED rows

| Node | Recorded status | Lean declaration / module | Verdict and evidence |
|---|---|---|---|
| `stepN:p7:rs-field` | PROVED | real_system (KAM/Nekhoroshev/Stability/RealSystem.lean) | CONFIRMED under (b): RealSystem:69 proves real/complex field agreement, C1 and periodicity on the actual real strip. The extension away from that open strip is irrelevant to the field calculation. |
| `stepN:p7:cj-chain` | PROVED | conjugation (KAM/Nekhoroshev/Stability/Conjugation.lean) | CONFIRMED under (b): Conjugation:108-152 proves membership, actual HasDerivAt of reMap Ψ ∘ z and field intertwining via complex chain rule. This is the substantive chain conclusion under (b); no claim that the bypassed real determinant calculation was proved. |
| `stepN:p4:c1-cauchy` | PROVED | general_cauchy (KAM/Weighted/Parametric.lean) | CONFIRMED under (b): Parametric:88-98 obtains every closed-radius bound and takes δ↑R in the operator norm. Evaluation gives the directional inequality. |
| `stepN:p8:mx-c` | PROVED | maximal, klattice_addVector (KAM/Nekhoroshev/ResonanceGeometry/Maximal.lean) | CONFIRMED under (b): Maximal:249, conjunct (c), proves k outside the real span and klattice_addVector with dimension increased by one. It is not just finite existence of maximal lattices. |
| `stepN:p6:div` | PROVED | divisor (KAM/Nekhoroshev/NormalForm/Setting.lean) | CONFIRMED under (b): NormalForm/Setting:148 uses the actual tube witness, norm_dotC_le, FreqLipschitz and α−KLr≥α/q. Both inequalities are retained. |
| `stepN:p7:ec-taylor` | PROVED | energy_core (KAM/Nekhoroshev/Stability/Energy.lean) | CONFIRMED under (b): Energy:77 proves Taylor on the chord; energy_core:237 supplies its (c),(d), actual Hamiltonian energy conservation and the orthogonal decomposition. No Hessian lower bound is concluded without the chord premise. |
| `stepN:p5:co-remainder` | PROVED | composition_series (KAM/Canonical/Composition.lean) | CONFIRMED under (b): Composition:40 calls series_eq and lieSeries_tail; CompositionSeries and the flow Taylor estimate control the hatted ratio ≤8/9. Pointwise equality is a genuine HasSum limit. |
| `stepN:p1:qc-reg` | PROVED | qc_convert (KAM/Nekhoroshev/Interfaces/QuasiConvex.lean) | CONFIRMED under (b): QuasiConvex:37-64 first places I in the real action domain and invokes hessian_convert for n Mcomplex, then enlarges to Bc. The I∈B(0,R) source premise remains. |
| `stepN:p9:bh-rad` | PROVED | block_hyp (KAM/Nekhoroshev/Poschel/BlockHypotheses.lean) | CONFIRMED under (b): BlockHypotheses:303 explicitly exports r=α/(p√n M Ka), r≤4ℓ/m and Mr≤ℓ/2. Ka=K/√n is used, not Ka=K. |
| `stepN:p9:bs-theta` | PROVED | block_stab (KAM/Nekhoroshev/Poschel/BlockStability.lean) | CONFIRMED under (b): BlockStability:111-131 builds hTheta by nonresonant and stopped_extension with the exact multiplicative admissibility. Its time bound is the full Tnr, not a shorter headline horizon. |
| `stepN:p6:nf-real` | PROVED | normal_form (KAM/Nekhoroshev/NormalForm/NormalForm.lean) | CONFIRMED under (b): NormalForm:96 retains the reality clause. StepsCaseB.nf_real and the case-A chain_real establish preservation, with the source negation-closed resonance and reality premises. |
| `stepN:p12:sl-box` | PROVED | slab_freq (KAM/Nekhoroshev/Averaging/Slab.lean); AvgSlab.volume_box_le, AvgSlab.section_dist_le (KAM/Nekhoroshev/Averaging/SlabBox.lean) | CONFIRMED under (b): AvgSlab.section_dist_le and volume_box_le prove the section diameter and Fubini estimate; Slab:170ff instantiates c0 and the box. Side length 2r gives exponent n−1. |
| `stepN:p5:cm-cde` | PROVED | canonical_map_c, canonical_map_d, canonical_map_e (KAM/Canonical/CanonicalMap.lean) | CONFIRMED under (b): CanonicalMap:305,317,327 proves derivative displacement, symplecticity and both inverse identities; the proof also obtains the flow displacement and correct smaller-domain membership. |
| `stepN:p5:ci-coeff` | PROVED | composition_integral (KAM/Canonical/CompositionIntegral.lean) | CONFIRMED under (b): CompositionIntegral:113-173 proves InClass, hcoef by coeff_integral/Fubini and the weighted estimate from finite coefficient sums. Required continuity and derivative-continuity are source class data. |
| `stepN:p1:nc-mat` | PROVED | KAM.Nekhoroshev.bilinear_euclid_bound (KAM/Nekhoroshev/Interfaces/Norms.lean) | CONFIRMED under (b): Norms:93 explicitly factors M0 times the two ℓ1 sums and applies √n factors, including n=0; no conjugate-bilinear form is substituted. |
| `stepN:p9:bh-nr` | PROVED | block_hyp (KAM/Nekhoroshev/Poschel/BlockHypotheses.lean) | CONFIRMED under (b): BlockHypotheses:303 retains nonresonance, conditional strict resonanceDistance<δ for Λ≠⊥, and δ≤mr/8. For Λ=⊥ the projection is zero and δ>0; no strict inequality at zero radius is claimed. |
| `stepN:p8:pr-alg` | PROVED | projection, projection_matrix (KAM/Nekhoroshev/ResonanceGeometry/Projection.lean) | CONFIRMED under (b): Projection:81 proves symmetry/idempotence, fixes the span, orthogonal complement and Pythagoras; projection_matrix:165 identifies AG⁻¹Aᵀ. The basis independence premise guards the inverse. |
| `stepN:p4:pr-tail` | PROVED | truncation_tail (KAM/Weighted/Projections.lean) | CONFIRMED under (b): Projections:111 identifies u−truncate K u with the complementary projection, then proves the exact exp(−2πKσ) WBound. Summability is explicit. |
| `stepN:p7:p2-t3` | PROVED | resonant_prop2 (KAM/Nekhoroshev/Stability/ResonantStability.lean) | CONFIRMED under (b): ResonantStability’s prop2_core/case proofs discharge (T3) with resonant_lemma2 and the case-specific time arithmetic, including full resonance. The exported wrapped theorem retains the final drift result. |
| `stepN:p1:hr-per` | PROVED | KAM.Nekhoroshev.holo_real_d (KAM/Nekhoroshev/Interfaces/HoloReal.lean) | CONFIRMED under (b): HoloReal:299 proves H, DH, field and every iterated derivative invariant under integer shifts on Wdom. Actual derivatives are used. |
| `stepN:p5:ca-chain` | PROVED | canonical_bracket, canonical_field (KAM/Canonical/Symplectic.lean) | CONFIRMED under (b): Symplectic.flow_fderiv_J:177 proves the derivative chain identity; canonical_bracket/canonical_field apply it on the flow domain, with holomorphy from flow_b. |
| `stepN:p6:hom-norm` | PROVED | homological (KAM/Nekhoroshev/NormalForm/Homological.lean) | CONFIRMED under (b): Homological:172 bounds the coefficient divisor by q/(2πα), and its homological theorem sums with the weighted norm and projection bounds. Fourier factors retain 2π. |
| `stepN:p8:gl-div` | PROVED | geometric_lattice (KAM/Nekhoroshev/ResonanceGeometry/Geometric.lean) | CONFIRMED under (b): Geometric’s divisor proof combines geom_formula, volume inequalities and the sqrt bound to get E K δ, at Geometric:182-204. The intermediate chain is in the audited proof block. |
| `stepN:p1:co-conc` | PROVED | KAM.Nekhoroshev.const_conclusion (KAM/Nekhoroshev/Interfaces/Constants.lean) | WRONG → NOT_STARTED / SOURCE_GAP for the compound row: Constants:338 proves the two identities; it does not supply T≤T0/2. The latter inherits the unresolved h scope at co-time. See F2. |
| `stepN:p5:ad-step` | PROVED | adjoint_bound (KAM/Canonical/Adjoint.lean) | CONFIRMED under (b): Adjoint:76,83 and adjoint_induction prove the signed bracket successor and 2/[e(h+i)κλ] bound, using the source width relations. adjoint_bound packages the induction. |
| `stepN:p12:sh-shells` | PROVED | shells_from_slab, shells (KAM/Nekhoroshev/Averaging/Shells.lean) | CONFIRMED under (b): Shells:69 shell_bound bounds dyadic sublevel indicators, with hvol from slab and a common finite upper cutoff; integral_psi/psiD/resid instantiate it. This covers the source shell bounds under (b), without needing named disjoint-shell definitions. |
| `stepN:p5:tr-f` | PROVED | composition_series (KAM/Canonical/Composition.lean); transform (KAM/Canonical/Transform.lean) | CONFIRMED under (b): Composition.composition_series (ii) gives precisely the f0 flow identity. Transform:83,148 applies it and subtracts the constant term, with summability proved. |
| `stepN:p5:co-field` | PROVED | composition_domain (KAM/Canonical/CompositionDomain.lean) | CONFIRMED under (b): CompositionDomain.scaledNorm_field_le, gaugeInterior_half and flow_mem_hat establish each domain/bound assertion. composition_domain:140 packages the required field estimate and membership. |
| `stepN:p1:rd-open` | PROVED | KAM.Nekhoroshev.isOpen_realActionDomain, KAM.Nekhoroshev.isOpen_Wdom, KAM.Nekhoroshev.isOpen_actionNbhd_ball, KAM.Nekhoroshev.isOpen_complexDomain, KAM.Nekhoroshev.realInclusion_preimage_actionNbhd (KAM/Nekhoroshev/Interfaces/Domains.lean) | CONFIRMED under (b): Domains:66,76,95-108 proves real, complex and product openness and real preimage identification. Wdom and complex openness are actually stronger (arbitrary radii). |
| `stepN:p7:ad-close` | PROVED | admissible (KAM/Nekhoroshev/Stability/Resonant.lean) | CONFIRMED under (b): Resonant.admissible:261-308 constructs the closeness witness J0, bounds frequency displacement by Mρ=δ/4 and proves the 5δ/4 projection bound and its variable-I version. |

## WRONG rows and exact unresolved obligations

**F1 — source h-premise scope, two rows.** `docs/graph/N/DEPGRAPH.md:3219` and `:3248` explicitly say “the source does not explicitly state the needed hypotheses on h here”; the NOTE at `:3239` / `:3272` retains this SOURCE_GAP. Blueprint Part 1 `p1-interfaces.tex:227-230` binds H1–H5 only conditionally in clause (d), then clauses (f),(g) use ω and Ω without that condition. Its proof at `:247` and `:249` invokes the conditional lower/derivative bounds. In contrast `ConstantsAnalytic.lean:129` and `:149` require `(hh : HeadHyp p h)`.

For co-exc the first unpaid inequality is `2π ωmin ≤ |frequencyMap (tildeh h) I0|₂`. Set h=0, I0=0 and positive ωmin: every listed numerical/source premise of the raw graph step remains available, but its frequency is zero. A fresh Lean example verifies zero frequency for the constant complex Hamiltonian in dimension 3. For co-time the claimed `Ω0 ≥ 2π ωmin > 0` fails for the same h; arbitrary unbounded linear slopes also show that a fixed M cannot bound frequency without the derivative assumption. Correct status for both: **NOT_STARTED / SOURCE_GAP** under their present source contracts. Do not add HeadHyp silently. The sealed assembly does supply HeadHyp and is not refuted.

**F2 — sampled co-conc is a compound row.** Graph `:3279-3301` retains “whose h-premise scope is unresolved” and requires `T ≤ T0/2` in addition to the radius/exponent identities. `Interfaces/Constants.lean:338-354` proves exactly the identities. `const_time` offers its numerical comparison only for a positive Ω bounded by `2π n M`, and forming that actual Ω with those bounds inherits F1. Correct status for the entire unsplit row: **NOT_STARTED / SOURCE_GAP**. The identities may be independently recorded as proved after an authorized graph split; this report makes no edit or split.

**F3 — literal Picard construction versus a valid alternate.** Graph `:21818-21824`, from blueprint Part 12 `p12-averaging.tex:37`, requires **the same** δ to satisfy `B=closedBall(x0,2δ)⊂W`, exact `L=sup_B |F|`, `Λ=sup_B ‖DF‖`, `r=δ/2`, and iterate confinement in `closedBall(x,δ/2)`. Current `Averaging/LocalDependence.lean:381-423` instead sets δ=ε0/2, bounds F and DF on **closedBall x0 δ**, chooses enlarged nonnegative upper bounds L0,Λn, chooses a using L0+1,Λn+1, and applies `picard_family` with initial radius δ/2 and global trap radius δ. `PicardFamilies.lean:252-265` exports membership in that global trap, not in each centered radius-δ/2 ball. The stronger centered estimate is readily derivable from recurrence and the integral bound, but is not the cited exported or audited proof-block assertion; the closed radius-2δ inclusion is not established for the chosen δ at all. Merely renaming δ to δ/2 also changes r and does not repair literal equality of this compound construction.

`N12-03c-audit-1.md:61` correctly describes a valid internal alternate and the unchanged parent conclusion. That is a proof of `ext_dep`, not an audit asserting the exact raw trap construction. Correct routing recommendation: **BYPASSED** for this literal step under D27, citing the smaller global trap and `ext_dep`; if such a route change is not accepted, leave **NOT_STARTED** until a literal construction is separately supplied. This finding does not question local existence, differentiability or the parent Volterra identity.

No source correction, graph status change or new hypothesis was made by the auditor. F1 is an already recorded blueprint scope defect; F2 is its inherited closure overclaim; F3 is an implementation deviation that the sync represented as literal closure. None is a newly verified defect in Pos93/AKN06/Nei76; this task examined pinned repository blueprint text and delivered Lean rather than re-auditing the PDFs.

## Definitions audit for bpN:p9#data

**Definitions-audit row:** `bpN:p9#data` — `KAM.Nekhoroshev.theoremCover`; `KAM.NormalForm.conjExp`; `KAM.Weighted.polyNbhd`, `Dom`, `InClass`, `coeff`, `modeWeight`, `WSummable`, `WBound`, `HasFiniteWNorm`, `wnorm`; `KAM.Canonical.RealOn`; `KAM.Stability.cpx`, `realNbhd`, `realStrip`, `realH`, `IsOrbit`; `KAM.NormalForm.zBall`; `KAM.Nekhoroshev.eBall`, `maximalK`, `CoverParams.radius`, `.alpha`, `.delta`, `actionBlock`; frozen `KAM.frequencyMap` / `KAM.Nekhoroshev.realPart` — **PASS WITH NOTES on the stated analytic/finite-norm/open-domain locus**. Not a whole-carrier identification of the blueprint’s zero extension. The current NOT_STARTED status is conservative until that section convention deviation is explicitly accounted for; this report supplies the missing definitions classification without editing the graph.

| Object | Named Lean implementation and locator | Classification / fidelity |
|---|---|---|
| p=9/8, b=1/8 | Poschel/Elementary.lean:42 `theoremCover`, fields in Interfaces/CoverParams.lean:28 | Literal numerical fields, for all arguments. No dependence on h,f or initial data. Fresh rfl probes passed. |
| q=9 and its relation to p | NormalForm/Setting.lean:44 `conjExp p = p/(p−1)`; Poschel/BlockStability.lean:63 local `hconj` | q is derived rather than a separately named global constant. At p=9/8 it is exactly 9; fresh norm_num verifies this and p/q=1/8. Likewise 1<p≤3/2 and q≥3 are rational arithmetic, no changed convention. Do not confuse this q with HeadParams.q=m/n of Part 1. |
| V_rD and analytic product domain | Weighted/Domains.lean:32,35 `polyNbhd`, `Dom` | Literal max-norm existential tube and strip product, angles first. Real D is passed as `cpx D`; no Euclidean tube substituted. Empty for nonpositive tube radius. |
| U_rD and W_r | Stability/Setting.lean:42-49 `cpx`, `realNbhd`, `realStrip`; :86 `realInclusion₂_mem_Dom_iff` | Literal real max-norm tube and univ × real tube; equivalence with complex-domain real slice for s>0. |
| O(r,s) and real analytic class | Weighted/Norm.lean:42 `InClass`; Canonical/Setting.lean:143 `RealOn`; Theorem1Setting.f_finite | Holomorphy and period-one angles, plus actual reality and finite weighted norm as required. No boundedness of the integrable Hamiltonian is assumed by the normal-form route. |
| Weighted norm conventions | Weighted/Norm.lean:49-73 `coeff`, `modeWeight`, `wsum`, `WSummable`, `WBound`, `HasFiniteWNorm`, `wnorm` | Period-one Fourier coefficients, weight exp(2πs|k|₁). wsum and real supremum are totalized off the finite locus; WBound/HasFiniteWNorm guard all norm conclusions. These are guarded analytic interfaces, not faithful numerical norms for arbitrary nonsummable data; no proof uses their junk values. |
| Z_K versus E_K | NormalForm/Setting.lean:35 `zBall`; ResonanceGeometry/Lattice.lean:35 `eBall` | Z_K uses ℓ1 Fourier size; E_K uses euclid of integerReal. Both literal on the entire index carrier Fin n→ℤ. Ka=K/√n conversion is retained. |
| M_K | ResonanceGeometry/Maximal.lean:27,30 `klattice`, `maximalK` | A lattice is an additive subgroup; klattice has a short generating set; maximalK is same-rank maximality among K-lattices, not rank-n maximality. Geometry is on the span defined in Lattice.lean:32. |
| DΛ,rΛ,αΛ,δΛ | ResonanceGeometry/Covering.lean:32-47 `CoverParams.lam`, `.radius`, `.alpha`, `.delta`, `actionBlock` | Literal source formulas on admissible cover data and maximal lattices: r0(AK)^(d−n)/volume, α=pMK r, δ=bmr, DΛ=P∩ω⁻¹(blockΛ). Split integer powers give the same formula when AK>0, proved by Valid. General total divisions outside Valid are not source parameter claims. |
| h-real gradient and H-orbit | frozen FrequencyMap.lean:32; Stability/Setting.lean:52-59 `realH`, `IsOrbit` | frequencyMap differentiates the actual real restriction; analytic inputs guard derivative totality. IsOrbit is a genuine field solution with realStrip membership. `realH G x=(G(ιx)).re` on **all** real x, rather than the blueprint p9:12,36 “extended by 0” away from W. On the open real strip these agree and so do their derivatives; off W they need not. Explicit deviation, not a proven global zero extension. |

Other checked definition rows: `bpN:p3:s-N#data` and `bpN:p9:s-blocks#data` are classified in the mandatory table. The graph-sync diff itself introduces **no Lean def/abbrev/structure at all**. Data/Theorem1Setting/PicardBounds are numerical, analytic or typing/source interfaces; none assumes stability, convergence of derivatives or the final theorem. Choose/default curves in Maximal and clamped Picard families have proved local specifications on every consumed point; their outside values are never used for a source-domain theorem.

## Independent hygiene and validation

All elaborations/builds/replays were serialized with `LEAN_NUM_THREADS=1`; all direct Lean/checker calls used `nice -n 5`, and the mandatory compile gate itself runs `nice -n 5 lake build`. No resource-budget override, clean, cache fetch, update, full-library target or production edit was used. The replay failure is reported separately below. The 53 build targets are the unique module paths cited by the checked nodes, listed here in order (the same list was used for the single kernel invocation):

```text
KAM.Canonical.Adjoint
KAM.Canonical.CanonicalMap
KAM.Canonical.Composition
KAM.Canonical.CompositionDomain
KAM.Canonical.CompositionIntegral
KAM.Canonical.FlowInverse
KAM.Canonical.Symplectic
KAM.Canonical.Transform
KAM.Nekhoroshev.Assembly.Confinement
KAM.Nekhoroshev.Averaging.LocalDependence
KAM.Nekhoroshev.Averaging.PicardDerivatives
KAM.Nekhoroshev.Averaging.PicardFamilies
KAM.Nekhoroshev.Averaging.Shells
KAM.Nekhoroshev.Averaging.Slab
KAM.Nekhoroshev.Averaging.SlabBox
KAM.Nekhoroshev.Interfaces.ConicCoercive
KAM.Nekhoroshev.Interfaces.Constants
KAM.Nekhoroshev.Interfaces.ConstantsAnalytic
KAM.Nekhoroshev.Interfaces.Domains
KAM.Nekhoroshev.Interfaces.HoloReal
KAM.Nekhoroshev.Interfaces.Norms
KAM.Nekhoroshev.Interfaces.QuasiConvex
KAM.Nekhoroshev.Interfaces.Setting
KAM.Nekhoroshev.NormalForm.Homological
KAM.Nekhoroshev.NormalForm.NormalForm
KAM.Nekhoroshev.NormalForm.Setting
KAM.Nekhoroshev.ODE.Specialization
KAM.Nekhoroshev.Poschel.BlockHypotheses
KAM.Nekhoroshev.Poschel.BlockStability
KAM.Nekhoroshev.Poschel.Elementary
KAM.Nekhoroshev.ResonanceGeometry.Covering
KAM.Nekhoroshev.ResonanceGeometry.Geometric
KAM.Nekhoroshev.ResonanceGeometry.Maximal
KAM.Nekhoroshev.ResonanceGeometry.Projection
KAM.Nekhoroshev.Stability.Conjugation
KAM.Nekhoroshev.Stability.Energy
KAM.Nekhoroshev.Stability.Nonresonant
KAM.Nekhoroshev.Stability.RealSystem
KAM.Nekhoroshev.Stability.Resonant
KAM.Nekhoroshev.Stability.ResonantStability
KAM.Nekhoroshev.Stability.Transfer
KAM.ODE.Continuation
KAM.ODE.Existence
KAM.ODE.Exit
KAM.ODE.Hamiltonian
KAM.ODE.Lipschitz
KAM.ODE.Maximal
KAM.ODE.UniformPeriodic
KAM.ODE.Uniqueness
KAM.Weighted.Algebra
KAM.Weighted.Coefficients
KAM.Weighted.Parametric
KAM.Weighted.Projections
```

Exact command forms (MODULES is the ordered list above; no full-library build):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-nsync <MODULES>
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/NsyncAudit.lean
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose <MODULES>
LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Build **exit 0**, output `Build completed successfully (3352 jobs).` The gate acquired slot 2 at 16:58:29 UTC. Dependency diagnostics were unused-variable/section-variable and style linter warnings; no elaboration error or heartbeat design signal occurred.

The axiom/parameter/counterexample probe **exit 0** after correcting two auditor probe namespace mistakes (the initial probe exited 1 for unknown identifiers slab_freq and KAM.realPart; production code was never changed). Its 88 axiom reports are reproduced below. Every axiom set is a subset of `{propext, Classical.choice, Quot.sound}`. There are no new public theorems in the sync diff; these are the referenced declarations checked additionally. The probe also checked p,b by rfl, conjExp(9/8)=9 and p/q=1/8 by norm_num, and constant-h zero frequency by simp.

```text
'KAM.Nekhoroshev.shells' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.shells_from_slab' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.slab_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.canonical_map_c' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.canonical_map_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.canonical_map_e' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.composition_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.adjoint_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.canonical_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.canonical_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.composition_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.composition_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.flow_e' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Canonical.transform' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.section_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.AvgSlab.volume_box_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.Data' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ODE.confinement_glue' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ODE.local_exist' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ODE.uniqueness_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.Wdom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.actionBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.bilinear_euclid_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.block_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.block_stab' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.cf_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.cf_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.conic_coercive' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.const_conclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.const_exceptional' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.const_perturbation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.const_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.contractingWith_picardMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.contractingWith_voltMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.ext_dep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.geometric_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.holo_input' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.holo_real_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_Wdom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_actionNbhd_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_complexDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.isOpen_realActionDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.klattice_addVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.linear_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.maximalK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.norm_convert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.picard_family' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.projection_matrix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.qc_convert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.realInclusion_preimage_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.theoremCover' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.homological' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.NormalForm.normal_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.closedThickening' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_maximal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_short' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_short_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_uniform_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_uniform_exist' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_uniform_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.gen_uniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.ham_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.ham_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.ham_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.ODE.picard_lindelof_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.admissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.conjugation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.energy_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.no_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.nonresonant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.real_system' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.resonant_lemma2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.resonant_prop2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.stopped_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.coeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.coefficients_series' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.general_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Weighted.truncation_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay **did not pass**: the single invocation listed above, with all 53 named modules and `LEAN_NUM_THREADS=1`, returned Python `subprocess` **returncode -15 (SIGTERM)** after approximately eight minutes. Captured stdout/stderr was empty (0 bytes). The runner printed exactly:

```text
leanchecker exit -15
```

No audit timeout or termination command was sent. The cause of SIGTERM was not determined; no OOM, external kill source, or failing declaration is asserted. No successful replay receipt exists for this invocation, and no declaration is credited with completed replay from an empty log. The completed build and axiom checks do not replace kernel replay. This negative/incomplete gate is reported rather than silently treated as success or attributed to production proof code.

Lint **exit 0**, complete output:

```text
check_lean_modules: PASS (1342 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

A current recursive scan of the 53 targets found 168 KAM modules, 29 frozen imports, all manifest SEALED, and 0 provider imports. Thus no DRAFT_SORRY theorem or quarantined provider is consumed by this reviewed slice.

This includes module conventions/size limits, forbidden proof escapes/resource overrides, frozen-anchor guard, and all **144** frozen ABI hashes. There was no generated-root exception to waive on this snapshot. The protected-path comparison is empty, exit 0. `git diff --check` is empty, exit 0. Audit scratch inputs/logs were removed after their evidence was embedded here; only the requested report remains untracked. No external communication, git commit or change to source conventions was performed.

Limit: 101 explicitly listed nodes were checked; the sample is not an exhaustive recertification of every one of the 235 promoted rows or every existing sealed theorem. The four WRONG rows remain literal graph obligations notwithstanding successful builds and axiom probes.
