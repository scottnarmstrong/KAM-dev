# Independent audit: P11A-P8b2, round 2

**Overall verdict: PASS WITH NOTES. Audit-1 F1 is resolved.** The unsigned pr-b export now states the literal Hessian bound `≤ 1`, with no stronger premise. Pr-c and the real-slice calculus brick pass. The only validation exception is the brief-permitted stale generated root. No frozen anchor is supplied or sealed by this package; “seal-ready” is not applicable to these infrastructure exports.

Audit date: 2026-10-29. Worktree and exact report destination: `/root/code/KAM-inp-p11ap8b2/docs/tracks/P/audits/P11A-P8b2-audit-2.md`. The explicit user destination overrides the generic brief's main-worktree destination.

Audited HEAD: `d5f6d8ed70006edce973a50c6ca93eac66540bdd`; observed `inp`: `9ffcb3343be139ca6f003a42f0cab4ab6027fbb6`; merge base: `7023f94481d23cd6e94a56fe65e7881f27ceb698`. Reviewed the full `git diff inp...HEAD`: six new Lean modules (3250 lines), plus the committed handoff and round-1 audit (549 lines). The fix commit changes PreparedFreq and adds the round-2 handoff; it does not change other proof modules. Initial worktree status was clean.

Authority read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, track P statement, P11A design decisions/node table/preparation contracts, blueprint-P/parts/p11-cp09-preparation.tex:196–212, graph pr-b/pr-c records, package handoff including AUDIT FOCUS and explicit exclusions, audit-1, all six proof modules, actual derivative/norm definitions, upstream Secular/Fast/Slow contracts, relevant frozen definitions, and the external signed specifications and amount consumer. The previous audit supplied the inventory layout and compatibility-probe template; all verdicts below were checked against current source and fresh validation. No previous checker receipt is substituted for a round-2 run.

## Node and anchor verdicts

| Node / anchor | Lean declaration | Verdict | Reason |
|---|---|---|---|
| stepP:p11:pr-b | KAM.Planetary.p11_pr_b | PASS WITH NOTES | Frequency ≤ 2L+1 and Hessian ≤ 1 literally exported on the complex 3/4 action neighborhood; F1 resolved. |
| stepP:p11:pr-c | KAM.Planetary.p11_pr_c | PASS WITH NOTES | Exact signed diagonal jet predicate after selected-data specialization; ordinary carrier restriction supplies amount_transfer's he. |
| Partial/real-slice brick | p11op_re_le, p11dg_re_le, supporting calculus | PASS | Actual iterated derivatives; explicit Euclidean/max-norm comparison; order zero retained. |
| Frozen anchor/provider | None in this package | N/A | No frozen-type, seal-body or provider-equality obligation is supplied. No headline closure certified. |
| stepP:p11:pr-in | inherited PreparedJets | Supporting infrastructure | Called and proved through, without making the new pr-b/pr-c conclusions into premises. |
| stepP:p11:pr-d | P8b3 | Out of scope | Explicit handoff ruling; supporting dev helpers do not claim this node complete. |
| prepared, amount, signed assembly | P8e | Out of scope | Explicit handoff ruling; data selection, threshold selection and geometry remain assembly work. |

The design table (docs/tracks/P/design/P11A-LEAN-DESIGN.md:176–182) maps the preparation steps collectively to Preparation/Prepared. The handoff splits this package into six modules and explicitly excludes pr-d and assembly. No other in-scope graph node is missing. Graph metadata still says NOT_STARTED for pr-b/pr-c at docs/graph/P/DEPGRAPH.md:20674 and :20702; that is stale bookkeeping, not a proof gap in these two exports. No graph was edited.

## F1 repair and statement fidelity

PreparedFreq.lean:287–305 now exports:

```lean
p11Bound (KAM.actionNbhd (p11PreparedBox n) (3 / 4)) (p11PreparedFreq Q) (2 * C.L + 1) ∧
(∀ I ∈ KAM.actionNbhd (p11PreparedBox n) (3 / 4),
  ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 2 * C.L + 1) ∧
∀ I ∈ KAM.actionNbhd (p11PreparedBox n) (3 / 4),
  ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 1
```

This meets the literal node conclusion at graph :20657, design :394 and blueprint :209 (“the operator norm is ... ≤1≤C₁”). Local `hess` at :326–350 derives the bound once from coordinate derivatives with the explicit factor `n+n`; :351 exports it and derives the weaker signed bound using `1 ≤ C.L`. The positive K is selected before Fast, eps, c, A and Q. The repair adds no premise and no resource override.

Fresh `audit_b_literal` projects the frequency and ≤1 bounds into a standalone statement with the original premises; `audit_b_signed_pair` projects the two original signed bounds. Both elaborate. The result's conjunction is now right-nested: consumers extracting the old Hessian conjunct use `.2.1`, and the new literal bound is `.2.2`. A worktree-wide source scan found no production use of p11_pr_b to break. This report does not assert source compatibility of arbitrary unlanded consumers.

For pr-c (PreparedClose.lean:510), mu, `true`, the open J-ball with radius s2/4, subtraction of varpi, eps normalization, exponent `5*tau+2+(tau+1)*(mu+1)`, and order zero all match the signed clause. The explicit `1 ≤ n` premise is supplied from D.n_ge. Positive K is chosen before Fast/eps/c/cc/A/Q. It does not require theta≤1.

All eps smallness appears as explicit numeric conditions: `0 < eps`, `eps*MF ≤ exp(-1)`, `0 ≤ c`, `3*pi*eps ≤ pi*rz²/16`, `5*eps ≤ s2`, and pr-b's `K*(1+c)*eps*log(1/eps)^Q ≤ 1`. Pr-c uses `K*(1+c) ≤ cc` to absorb the derivative/norm constants. hN/hcheck identify Q with the intended functions; neither assumes the bound being proved. Generic Secular/Fast/Slow specifications are the existing upstream contracts, used by distinctly named conditional helpers; no signed source theorem is replaced with such a helper. No new bundle field, instance, or conclusion-shaped premise occurs. Arithmetic helper assumptions about radii, eta, factorials and powers are discharged by the main callers rather than silently moved to a source theorem.

AMEND P-A002 allows dependence on dimension, fixed data, nu and derivative orders before eps; the construction respects this. C1=2L+1 still depends on L alone. No constant depends on the subsequently quantified eps or c.

The Ops proof commutes holomorphic coordinate derivatives on open sets, expands multilinear inputs in coordinate bases (n^j terms), restricts the actual complex iterated derivative along realInclusion, and applies coordinatewise real part. Euclidean unit inputs have max norm ≤1; Euclidean output is ≤sqrt(m) times max norm. Thus sqrt(m)*n^j is explicitly paid, including j=0. The diagonal sphere is nonempty under 1≤n. There is no norm-instance substitution or EuclideanSpace carrier. Slice/affine identities retain the exact eps^|alpha| scaling.

## Definition classification

Nine public definitions/abbreviations and three private definitions are literal intended objects on their whole carriers. None introduces choice, a fallback branch, a structure or a conclusion-bearing field. DevA/G/Z are scalar majorants, with their estimates proved separately. Total division at zero is not used to fake an analytic conclusion: cancellation and Cauchy estimates have positive eps/radius premises. Inherited chosen-data fallback definitions are unchanged; pr-c is not a proof that a fallback datum satisfies FullSpec.

| Definition | Classification / whole-carrier meaning |
|---|---|
| `p11DevCenter` (`PreparedDev:32`) | Abbreviation for `(real J0, 2*pi*eps)`; the intended center for all parameters. |
| `p11DevProj` (`PreparedDev:339`) | Continuous linear projection onto J coordinates. |
| `p11DevH` (`PreparedDev:519`) | Vector in `Fin 1 -> C` containing `h0+g2`. |
| `p11DevA` (`PreparedDev:526`) | Explicit factorial/radius bound for the polar average. |
| `p11DevG` (`PreparedDev:530`) | Explicit mixed Cauchy bound for g2. |
| `p11DevZ` (`PreparedDev:536`) | Explicit mixed Cauchy bound for the first rho derivative of Z. |
| `p11DevOmv` (`PreparedDev:683`) | Abbreviation for `(omega, Omega/(2*pi))`. |
| `p11CloseFun` (`PreparedClose:30`) | Literal complex normalized-frequency deviation vector. |
| `p11CloseDom` (`PreparedClose:56`) | Intersection of the slow-box slice with the secular ball. |
| private `opsRe` (`PreparedOps:210`) | Coordinatewise real-part continuous real linear map. |
| private `opsExt` (`PreparedOps:388`) | Linear inclusion into the first block, zero in second block. |
| private `opsExtR` (`PreparedDev:399`) | Linear inclusion into the second block, zero in first block. |


## Signed clauses and actual consumer

The following external files were inspected read-only and pinned by SHA-256:

| File | SHA-256 |
|---|---|
| /root/code/KAM-inp/.drafts/design/P11ASignatures.lean | fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9 |
| /root/code/KAM-inp/KAM/Planetary/Preparation/AmountCore.lean | dedce155e5779f9e3a1380368d752f1de68d9078d34e260e6e098d8890a2e092 |

No new public name in the six-module diff is a signed declaration. Existing PreparedData exports remain inherited unchanged. Fresh `rfl` probes copy P11PreparedSpec, p11SlowNormalizedFreq and P11PreparedFullSpec bodies directly from the signature file under fresh names and compare them with the production definitions. They pass. This certifies the relevant inherited definitions' exact bodies, not the unproved signed assembly theorem.

`audit_prc_signed` specializes C=p11SecularData D and A=p11SlowData D nu eps and unfolds only p11SlowNormalizedFreq in the identifying premise. It obtains the literal FullSpec closeness clause; an independent example projects that clause from FullSpec. AmountCore is absent in this checkout; its landed amount_transfer text at :330–343 was inspected without importing or rebuilding another worktree. Its he uses the image carrier `((fun r => J0+eps • r) '' R)`. Pr-c uses the larger J-ball. These sets are not definitionally equal. The probe `audit_amount_he` derives exactly he from pr-c's predicate using image-carrier inclusion and `rho ∈ Rho → ‖rho‖ < 5/4`. No norm, derivative order, normalizer or analytic bound is restated. P8e must supply these geometry facts and the other amount_transfer inputs. This is not a full assembly receipt.

## Every new public declaration

All 97 rows (88 theorems, nine definitions/abbreviations) were matched to the current six modules. Helper PASS is scoped to the actual statement and its use; it does not assert a separate graph-node closure.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| Ops helper | `p11_partial_eq_iteratedFDeriv` (PreparedOps:131) | PASS | Coordinate-count multi-index equals the complex iterated derivative on the indicated basis vectors; openness and holomorphy justify permutation. |
| Ops helper | `p11PartialVec_single` (PreparedOps:148) | PASS | Literal singleton derivative identity, on the whole function carrier, with no holomorphy premise needed. |
| Ops helper | `p11_norm_iteratedFDeriv_le` (PreparedOps:166) | PASS | Multilinear expansion over n^r coordinate choices; max norm on inputs and output, including r=0. |
| Ops helper | `p11_iteratedFDeriv_real_slice` (PreparedOps:217) | PASS | Restricts complex derivatives to real input vectors and applies coordinatewise real part; all derivative orders, including zero. |
| Ops helper | `p11_euclid_jet_re_le` (PreparedOps:240) | PASS | Uses max norm <= Euclidean input norm and Euclidean output <= sqrt(m) times max norm; factor sqrt(m)*n^j is paid. |
| Ops helper | `p11op_re_le` (PreparedOps:260) | PASS | Full real jet bound from coordinate partials using attained operator norm; no metric replacement. |
| Ops helper | `p11dg_re_le` (PreparedOps:271) | PASS | Diagonal real jet bound with explicit nonempty unit sphere (1 <= n); discharges from D.n_ge in signed specialization. |
| Ops helper | `p11_partial_step` (PreparedOps:289) | PASS | Commutation of complex partials on an open holomorphic domain; raises the multi-index by a singleton. |
| Ops helper | `p11_partial_congr` (PreparedOps:303) | PASS | Local equality on an open set transfers through every coordinate derivative. |
| Ops helper | `p11_partial_add` (PreparedOps:308) | PASS | Additivity on the open common holomorphic domain, including order zero. |
| Ops helper | `p11_partial_clm` (PreparedOps:351) | PASS | Continuous complex linear maps commute with all coordinate partials. |
| Ops helper | `p11_norm_partial_le_iterated` (PreparedOps:357) | PASS | Basis-vector evaluation bounded by the actual complex multilinear operator norm. |
| Ops helper | `p11_partial_slice` (PreparedOps:448) | PASS | Fixed slow-action slice corresponds exactly to the appended multi-index (alpha,0). |
| Ops helper | `p11_partial_affine` (PreparedOps:514) | PASS | Exact eps^|alpha| affine scaling, with no division or positivity assumption on the affine scalar. |
| Definition | `p11DevCenter` (PreparedDev:32) | PASS | Literal slow-polydisc center (real J0,2*pi*eps). |
| Dev helper | `p11_dev_mem_box` (PreparedDev:35) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_box_isOpen` (PreparedDev:48) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_rho_norm` (PreparedDev:54) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_G0_diff` (PreparedDev:70) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_J` (PreparedDev:84) | PASS | Derives pure-J identity from the first slow-stage formula; does not assume the derivative identity. |
| Dev helper | `p11_dev_V_sub_Z` (PreparedDev:148) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Z_open` (PreparedDev:175) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_h0_rho` (PreparedDev:187) | PASS | Differentiates the second slow-stage formula; retains eps and 1/(2*pi). |
| Dev helper | `p11_dev_step_const` (PreparedDev:252) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_rho` (PreparedDev:261) | PASS | Higher mixed identity from the derived first rho derivative plus holomorphic commutation. |
| Definition | `p11DevProj` (PreparedDev:339) | PASS | Actual continuous linear projection onto the first action block. |
| Dev helper | `p11DevProj_apply` (PreparedDev:342) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_partial_proj_rho` (PreparedDev:369) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Z_slice` (PreparedDev:422) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Z_jet` (PreparedDev:442) | PASS | Mixed Cauchy bound from the signed zero-order d_rho Z estimate; radii s2/2 and eps, factorials retained. |
| Definition | `p11DevH` (PreparedDev:519) | PASS | One-component vector containing h0+g2 on the whole carrier. |
| Dev helper | `p11DevH_eq` (PreparedDev:521) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Definition | `p11DevA` (PreparedDev:526) | PASS | Explicit factorial/Cauchy-radius bound for the polar-average J derivatives. |
| Definition | `p11DevG` (PreparedDev:530) | PASS | Explicit mixed factorial bound with c*eps^3*ell^(5*tau+2) and radii s2/4,eps/4. |
| Definition | `p11DevZ` (PreparedDev:536) | PASS | Explicit mixed factorial bound for d_rho Z with radii s2/2,eps. |
| Dev helper | `p11_dev_Vh_sub` (PreparedDev:540) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_J_bound` (PreparedDev:550) | PASS | Deviation from d^alpha C.h bounded by eps*DevA + DevG, derived from identities and Cauchy. |
| Dev helper | `p11_dev_append_add` (PreparedDev:603) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_rho_bound` (PreparedDev:627) | PASS | Deviation from eps*d^beta(Omega/(2*pi)) bounded by eps*DevZ + DevG. |
| Definition | `p11DevOmv` (PreparedDev:683) | PASS | Literal vector (omega,Omega/(2*pi)) on the whole complex J carrier. |
| Dev helper | `p11_dev_Omv_diff` (PreparedDev:686) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Omv_jet` (PreparedDev:695) | PASS | Signed complex iterated-jet bound in secular data implies the coordinate-partial bound. |
| Dev helper | `p11_dev_main_omega` (PreparedDev:704) | PASS | Extracts a coordinate of the signed vector jet; bound L through mu+1. |
| Dev helper | `p11_dev_main_Omega` (PreparedDev:719) | PASS | Extracts Omega/(2*pi), rather than Omega; bound L through mu+1. |
| Dev helper | `p11_dev_split` (PreparedDev:735) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_nonzero` (PreparedDev:750) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_main_h` (PreparedDev:757) | PASS | Differentiates C.h once into omega; bound L for orders 1 through mu+2. |
| Dev helper | `p11_dev_V_sub_ball` (PreparedDev:777) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Om_diff` (PreparedDev:788) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Om_slice` (PreparedDev:802) | PASS | Domain, projection, component or multi-index identity supporting the displayed deviation formulas; no analytic estimate is assumed as its own conclusion. |
| Dev helper | `p11_dev_Om_zero` (PreparedDev:818) | PASS | Positive rho multi-index kills a function depending only on J; domain and regularity supplied. |
| Num helper | `p11_num_pow_le` (PreparedNum:22) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_g` (PreparedNum:27) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_z` (PreparedNum:49) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_a` (PreparedNum:67) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_z_final` (PreparedNum:83) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_collect_pure` (PreparedNum:105) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_collect_rho` (PreparedNum:129) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_powl` (PreparedNum:164) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_rpow_mul_le` (PreparedNum:176) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_inv_pow` (PreparedNum:181) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_cl1` (PreparedNum:186) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Num helper | `p11_num_cl2` (PreparedNum:255) | PASS | Explicit real-arithmetic helper; powers, positivity and comparison premises are visible and are discharged by its analytic callers. |
| Resc helper | `p11_resc_prod_le` (PreparedResc:31) | PASS | Factorial or logarithmic monotonicity helper; elementary premises are paid by the rescaling proof. |
| Resc helper | `p11_resc_prod2_le` (PreparedResc:35) | PASS | Factorial or logarithmic monotonicity helper; elementary premises are paid by the rescaling proof. |
| Resc helper | `p11_resc_rpow_le` (PreparedResc:42) | PASS | Factorial or logarithmic monotonicity helper; elementary premises are paid by the rescaling proof. |
| Resc helper | `p11_resc_pure_dev` (PreparedResc:46) | PASS | Conditional arithmetic helper: pure-J deviation with explicit eta, s1-inverse and smallness inputs; these are paid in dev_resc. |
| Resc helper | `p11_resc_pure` (PreparedResc:112) | PASS | Adds the derived main-term L to the pure-J deviation estimate. |
| Resc helper | `p11_resc_Om` (PreparedResc:185) | PASS | Main Omega/(2*pi) contribution bounded by L; vanishes if the rho multi-index is nonzero. |
| Resc helper | `p11_resc_rho_dev` (PreparedResc:212) | PASS | Conditional mixed deviation helper; factorial, eps and logarithmic losses retained explicitly. |
| Resc helper | `p11_resc_rho` (PreparedResc:307) | PASS | Adds eps*L to the mixed deviation estimate. |
| Resc helper | `p11_dev_resc` (PreparedResc:414) | PASS | Uniform positive K chosen before Fast, eps, c, A; proves all rescaled partial bounds through mu+1 from explicit numeric smallness. |
| Freq helper | `p11_freq_isOpen_actionNbhd` (PreparedFreq:32) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_res_eq` (PreparedFreq:41) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_U1_sub` (PreparedFreq:49) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_H_diff` (PreparedFreq:85) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_partial_eq` (PreparedFreq:95) | PASS | Differentiates the identifying N formula on actionNbhd box 1; eps denominator cancels one affine derivative. |
| Freq helper | `p11_freq_smallV_norm` (PreparedFreq:174) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_partial` (PreparedFreq:185) | PASS | All coordinate partials through mu+1 on actionNbhd box 3/4, with L at order zero and eps*L at positive orders. |
| Freq helper | `p11_freq_opNorm_le` (PreparedFreq:262) | PASS | Converts basis bounds to the max-norm operator bound N*B, including the dimension-zero case. |
| pr-b | `p11_pr_b` (PreparedFreq:287) | PASS | Literal frequency <= 2L+1 and Hessian <= 1 exported; additional <= 2L+1 Hessian conjunct is compatible with the signed full spec. |
| Definition | `p11CloseFun` (PreparedClose:30) | PASS | Literal complex vector (d_J h-omega, eps^-1*d_rho h-Omega/(2*pi)); no conditional branch. |
| Close helper | `p11_partial_sub` (PreparedClose:38) | PASS | Local calculus/component/domain identity for the closeness vector; open-domain hypotheses justify differentiation. |
| Definition | `p11CloseDom` (PreparedClose:56) | PASS | Literal intersection of the slice of the slow polydisc with the secular J-ball. |
| Close helper | `p11_close_dom_open` (PreparedClose:60) | PASS | Local calculus/component/domain identity for the closeness vector; open-domain hypotheses justify differentiation. |
| Close helper | `p11_close_append_cast` (PreparedClose:67) | PASS | Local calculus/component/domain identity for the closeness vector; open-domain hypotheses justify differentiation. |
| Close helper | `p11_close_Phi_diff` (PreparedClose:89) | PASS | Complex closeness vector is holomorphic on the intersection of the slow slice and secular ball. |
| Close helper | `p11_close_omega_partial` (PreparedClose:122) | PASS | Local calculus/component/domain identity for the closeness vector; open-domain hypotheses justify differentiation. |
| Close helper | `p11_close_comp` (PreparedClose:139) | PASS | Local calculus/component/domain identity for the closeness vector; open-domain hypotheses justify differentiation. |
| Close helper | `p11_close_block1` (PreparedClose:150) | PASS | First two pr-c contributions from eps*d_J G0 and d_J g2, with shifted J multi-index. |
| Close helper | `p11_close_block2` (PreparedClose:213) | PASS | Last two pr-c contributions from d_rho Z and eps^-1*d_rho g2; correct normalization retained. |
| Close helper | `p11_close_Reta` (PreparedClose:311) | PASS | Local calculus/component/domain identity for the closeness vector; open-domain hypotheses justify differentiation. |
| Close helper | `p11_close_fin1` (PreparedClose:319) | PASS | Pure arithmetic collection of the first block into eps*ell^Q. |
| Close helper | `p11_close_fin2` (PreparedClose:357) | PASS | Pure arithmetic collection of the second block into eps*ell^Q. |
| Close helper | `p11_close_partial` (PreparedClose:393) | PASS | Uniform Kb before Fast, eps, c, A; coordinate partials of the closeness vector through mu on the full stated complex slice. |
| Close helper | `p11_close_re_eq` (PreparedClose:484) | PASS | Uses the secular real-slice identification to identify Re(close vector) with psi-varpi, retaining 2*pi. |
| pr-c | `p11_pr_c` (PreparedClose:510) | PASS | Exact signed diagonal p11JetBound clause after C,A specialization; includes j=0; consumer restriction probe passes. No theta<=1 premise. |


## Fresh validation receipts

Every auditor-started Lean/Lake command, including lint's ABI subprocess, ran serially with `LEAN_NUM_THREADS=1` and inherited `nice -n 5`. No build, leanchecker, probe or lint overlapped another auditor-started Lean/Lake command. No resource limit was raised.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8b2 KAM.Planetary.Preparation.PreparedClose
```

Exit 0. PreparedClose transitively imports all six audited modules. Exact gate/success lines:

```text
[inp-gate] slot 2 acquired 03:24:49 for KAM.Planetary.Preparation.PreparedClose
Build completed successfully (9426 jobs).
```

Cached warnings include unused hypotheses, sequence-focus suggestions and deprecated if_true. The job count includes cache replay; it is not 9426 fresh compilations. No elaboration failure occurred.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedOps KAM.Planetary.Preparation.PreparedDev KAM.Planetary.Preparation.PreparedNum KAM.Planetary.Preparation.PreparedResc KAM.Planetary.Preparation.PreparedFreq KAM.Planetary.Preparation.PreparedClose
```

Exit 0. Complete output:

```text
replaying KAM.Planetary.Preparation.PreparedClose
replaying KAM.Planetary.Preparation.PreparedFreq
replaying KAM.Planetary.Preparation.PreparedResc
replaying KAM.Planetary.Preparation.PreparedNum
replaying KAM.Planetary.Preparation.PreparedDev
replaying KAM.Planetary.Preparation.PreparedOps
```

### All 88 public theorem axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/P8b2R2Axioms.lean
```

Exit 0. Probe imported PreparedClose and printed axioms for every theorem in the declaration inventory, generated directly from current source. Complete output:

```text
'KAM.Planetary.p11_partial_eq_iteratedFDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PartialVec_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_iteratedFDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_iteratedFDeriv_real_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_euclid_jet_re_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11op_re_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dg_re_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_clm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_partial_le_iterated' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_mem_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_box_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_rho_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_G0_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_J' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_V_sub_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Z_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_h0_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_step_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11DevProj_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_proj_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Z_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Z_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11DevH_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Vh_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_J_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_append_add' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.p11_dev_rho_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Omv_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Omv_jet' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_main_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_main_Omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_main_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_V_sub_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Om_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Om_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_Om_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_g' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_z' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_z_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_collect_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_collect_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_powl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_rpow_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_cl1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_num_cl2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_prod2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_pure_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_Om' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_rho_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_resc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_isOpen_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_res_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_U1_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_H_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_smallV_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pr_b' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_partial_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_dom_open' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_append_cast' depends on axioms: [propext, Quot.sound]
'KAM.Planetary.p11_close_Phi_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_omega_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_block1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_block2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_Reta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_fin1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_fin2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_close_re_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pr_c' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every axiom set is a subset of {propext, Classical.choice, Quot.sound}; no sorryAx.

### Literal export, signed-body and consumer probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/P8b2R2Compatibility.lean
```

Exit 0. Complete output:

```text
'KAM.Planetary.audit_prc_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_amount_he' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_b_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_b_signed_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The complete accepted probe is preserved below for reproduction after scratch cleanup:

```lean
import KAM.Planetary.Preparation.PreparedClose
open Set
open scoped BigOperators
noncomputable section
namespace KAM.Planetary

def auditSignedClose {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  ∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4}
      ((fun J => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho))-A.varpi)
      (c*eps*ell^exponent)

example {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (Q : P11PreparedData n)
    (h : P11PreparedFullSpec D nu eps c Q) : auditSignedClose D nu eps c Q := h.2.2.1

theorem audit_prc_signed {n : ℕ} (D : P11Physical n) {nu : ℝ} (hnu : 1 ≤ nu)
    (hC : P11SecularSpec D (p11SecularData D)) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c cc : ℝ} (Q : P11PreparedData n),
      0 < eps → eps * (p11SecularData D).MF ≤ Real.exp (-1) → 0 ≤ c → K * (1 + c) ≤ cc →
      3 * Real.pi * eps ≤ Real.pi * (p11SecularData D).rz ^ 2 / 16 →
      5 * eps ≤ p11s2 (p11SecularData D) nu eps →
      P11FastSpec (p11SecularData D) eps Fast →
      P11SlowSpecOf (p11SecularData D) Fast nu eps c (p11SlowData D nu eps) →
      (∀ rho : P11Vec n, ‖rho‖ < 5/4 → ∀ J : P11Vec n,
        ‖J-(p11SecularData D).J0‖ < p11s2 (p11SecularData D) nu eps/4 →
        Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-(p11SecularData D).J0)) rho) =
          p11SlowNormalizedFreq D nu eps J rho) →
      auditSignedClose D nu eps cc Q := by
  have hn : 1 ≤ n := by have := D.n_ge; omega
  obtain ⟨K, hK, hp⟩ := p11_pr_c hC hnu hn
  refine ⟨K, hK, ?_⟩
  intro Fast eps c cc Q heps hM hc hcc hz h5 hF hA hcheck
  exact hp Q heps hM hc hcc hz h5 hF hA (by
    simpa only [p11SlowNormalizedFreq] using hcheck)

-- The exact he predicate at AmountCore.lean:338-339, with its necessary carrier restriction.
theorem audit_amount_he {n : ℕ} (D : P11Physical n) (nu eps cc : ℝ) (Q : P11PreparedData n)
    (h : auditSignedClose D nu eps cc Q) {R Rho : Set (P11Vec n)}
    (hR : ((fun r => (p11SecularData D).J0 + eps • r) '' R) ⊆
      {J | ‖J-(p11SecularData D).J0‖ < p11s2 (p11SecularData D) nu eps/4})
    (hRho : ∀ rho ∈ Rho, ‖rho‖ < 5/4) :
    ∀ rho ∈ Rho, p11JetBound true (p11PatchData D).mu
      ((fun r => (p11SecularData D).J0 + eps • r) '' R)
      ((fun J => Q.checkW (Fin.append (eps⁻¹ • (J-(p11SecularData D).J0)) rho)) -
        (p11PatchData D).varpi)
      (cc*eps*Real.log (1/eps)^(5*(p11SecularData D).tau+2+
        ((p11SecularData D).tau+1)*((p11PatchData D).mu+1))) := by
  intro rho hrho j hj y hy
  exact h rho (hRho rho hrho) j hj y (hR hy)

#print axioms audit_prc_signed
#print axioms audit_amount_he
end KAM.Planetary
namespace KAM.Planetary
variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}
theorem audit_b_literal (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n}
      {Q : P11PreparedData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      (∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
        (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) /
          (eps : ℂ)) →
      p11Bound (KAM.actionNbhd (p11PreparedBox n) (3 / 4)) (p11PreparedFreq Q) (2 * C.L + 1) ∧
      ∀ I ∈ KAM.actionNbhd (p11PreparedBox n) (3 / 4),
        ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 1 := by
  obtain ⟨K, hK, hp⟩ := p11_pr_b hC hnu
  refine ⟨K, hK, ?_⟩
  intro Fast eps c A Q heps hM hc htheta hz h5 hF hA hN
  have h := hp heps hM hc htheta hz h5 hF hA hN
  exact ⟨h.1, h.2.2⟩
#print axioms audit_b_literal
end KAM.Planetary

namespace KAM.Planetary
variable {n : ℕ} {D : P11Physical n} {C : P11SecularData n}
theorem audit_b_signed_pair (hC : P11SecularSpec D C) {nu : ℝ} (hnu : 1 ≤ nu) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n}
      {Q : P11PreparedData n},
      0 < eps → eps * C.MF ≤ Real.exp (-1) → 0 ≤ c →
      K * (1 + c) * eps * Real.log (1 / eps) ^
        (5 * C.tau + 2 + (C.tau + 1) * ((p11PatchData D).mu + 1)) ≤ 1 →
      3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 → 5 * eps ≤ p11s2 C nu eps →
      P11FastSpec C eps Fast → P11SlowSpecOf C Fast nu eps c A →
      (∀ I ∈ KAM.actionNbhd (p11PreparedBox n) 1, Q.N I =
        (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) /
          (eps : ℂ)) →
      p11Bound (KAM.actionNbhd (p11PreparedBox n) (3 / 4)) (p11PreparedFreq Q) (2 * C.L + 1) ∧
      ∀ I ∈ KAM.actionNbhd (p11PreparedBox n) (3 / 4),
        ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 2 * C.L + 1 := by
  obtain ⟨K, hK, hp⟩ := p11_pr_b hC hnu
  refine ⟨K, hK, ?_⟩
  intro Fast eps c A Q heps hM hc htheta hz h5 hF hA hN
  have h := hp heps hM hc htheta hz h5 hF hA hN
  exact ⟨h.1, h.2.1⟩
#print axioms audit_b_signed_pair
end KAM.Planetary

namespace KAM.Planetary
def auditSigned_P11PreparedSpec {n : ℕ} (D : P11Physical n) (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let U := KAM.actionNbhd (p11PreparedBox n) 1
  let V := KAM.complexStrip (n+n) (C.sigma/72) ×ˢ U
  let smallV := KAM.actionNbhd (p11PreparedBox n) (3/4)
  let W := p11PreparedFreq Q
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  (let A := p11SlowData D nu eps
   (∀ z ∈ V, let y := p11Rescale C.J0 eps z
     Q.N z.2=(A.h0 y.2+A.g2 y.2)/eps ∧ Q.P z=A.f3 y/eps) ∧
   ∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ V →
     let w := (p11FastData D eps).map (p11PolarC (A.Psi (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))
     Q.chain z=C.chart ((fun i => (w.1 i).re),fun i => (w.2 i).re)) ∧
  DifferentiableOn ℂ Q.N U ∧ DifferentiableOn ℂ Q.P V ∧
  (∀ z ∈ V, ∀ i : Fin (n+n), Q.P (z.1+Pi.single i 1,z.2)=Q.P z) ∧
  KAM.Canonical.RealOn V (fun z => Q.N z.2+Q.P z) ∧
  KAM.Canonical.RealOn V Q.P ∧
  (∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ U → (Q.N (KAM.realInclusion (n+n) I)).im=0) ∧
  p11Bound V Q.P (c*eps^(nu+3/2)*ell^(2*C.tau+1)) ∧
  p11Bound smallV W (2*C.L+1) ∧
  (∀ I ∈ smallV, ‖fderiv ℂ W I‖ ≤ 2*C.L+1) ∧
  (∀ y : P11Vec (n+n), ‖y‖ ≤ 5/4 →
    p11PreparedFreqR Q y=Fin.append
      (fun i : Fin n => Q.checkW y (Fin.castAdd n i))
      (fun i : Fin n => eps*Q.checkW y (Fin.natAdd n i))) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    let psi := fun J : P11Vec n => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho)
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4} (psi-A.varpi) (c*eps*ell^exponent)) ∧
  (∀ direction, p11euclid direction=1 → ∀ j, 1 ≤ j → j ≤ A.mu+1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) j y ≤ (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2) ∧
  (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ V →
    fixedHamiltonian D.G D.m0 D.m eps (Q.chain z)=eps*(Q.N (KAM.realInclusion (n+n) z.2)+
      Q.P (KAM.realInclusion₂ (n+n) z)).re)
example : @auditSigned_P11PreparedSpec = @P11PreparedSpec := rfl
end KAM.Planetary

namespace KAM.Planetary
def auditSigned_p11SlowNormalizedFreq {n : ℕ} (D : P11Physical n)
    (nu eps : ℝ) (J rho : P11Vec n) : P11Vec (n+n) :=
  let A := p11SlowData D nu eps
  let I := Fin.append (KAM.realInclusion n J)
    (fun i : Fin n => (eps*(2*Real.pi+rho i) : ℂ))
  let W : P11CVec (n+n) :=
    fun i => fderiv ℂ (A.h0+A.g2) I (Pi.single i 1)
  Fin.append (fun i : Fin n => (W (Fin.castAdd n i)).re)
    (fun i : Fin n => (W (Fin.natAdd n i)).re/eps)
example : @auditSigned_p11SlowNormalizedFreq = @p11SlowNormalizedFreq := rfl
end KAM.Planetary

namespace KAM.Planetary
def auditSigned_P11PreparedFullSpec {n : ℕ} (D : P11Physical n)
    (nu eps c : ℝ) (Q : P11PreparedData n) : Prop :=
  let C := p11SecularData D
  let A := p11PatchData D
  let ell := Real.log (1/eps)
  let exponent := 5*C.tau+2+(C.tau+1)*(A.mu+1)
  P11PreparedSpec D nu eps c Q ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    ∀ J : P11Vec n, ‖J-C.J0‖ < p11s2 C nu eps/4 →
      Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho) =
        p11SlowNormalizedFreq D nu eps J rho) ∧
  (∀ rho : P11Vec n, ‖rho‖ < 5/4 →
    p11JetBound true A.mu {J | ‖J-C.J0‖ < p11s2 C nu eps/4}
      ((fun J => Q.checkW (Fin.append ((eps : ℝ)⁻¹ • (J-C.J0)) rho))-A.varpi)
      (c*eps*ell^exponent)) ∧
  p11JetBound true A.mu (p11thick (p11PreparedBox n) (1/4))
    (p11PreparedFreqR Q) (p11M0 n A.mu C.L) ∧
  (∀ direction, p11euclid direction=1 →
    ∀ y ∈ p11thick (p11PreparedBox n) (1/4),
      p11op (p11scalar 2 (p11PreparedFreqR Q) direction) 0 y ≤
        (2 : ℝ)^(A.mu+1)*(2*C.L+1)^2)
example : @auditSigned_P11PreparedFullSpec = @P11PreparedFullSpec := rfl
end KAM.Planetary
```

### Source lint, import quarantine and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1199 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

KAM.lean was not regenerated. The checks found no forbidden token, resource override, EuclideanSpace code, oversize file or overlong line. All six files have copyright, module, public imports, module docstrings and an exposed public noncomputable section. All public declarations are in KAM.Planetary; the three generic linear maps are private. A current declaration-name scan against other KAM source files found no reused public helper short names and no harmful root shadow.

| Module | Total lines | Maximum Unicode line length |
|---|---:|---:|
| PreparedOps | 531 | 100 |
| PreparedDev | 844 | 100 |
| PreparedNum | 337 | 100 |
| PreparedResc | 557 | 99 |
| PreparedFreq | 362 | 98 |
| PreparedClose | 619 | 100 |

A fresh recursive local KAM import scan reached 380 modules, including 64 frozen definition modules. Every reached frozen module is manifest SEALED. It reached zero provider modules and zero frozen theorem modules, hence no DRAFT_SORRY theorem import. The relevant inherited frozen actionNbhd is the actual complex max-norm neighborhood; fixedHamiltonian retains the fixed-center Newtonian formula. No local carrier or fallback replaces either definition.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

All exit 0, no output. Source hashes were checked again before cleanup. All auditor-created P8b2R2 probes, inventories and logs in .lake/abi-scratch were removed after their receipts were embedded in this report. Final git status has only this untracked report; no production, protected, signature, consumer or prior-report file was changed. No state-changing git command was run.

## Defects, deviations and remaining scope

- **Audit-1 F1: resolved**, by the literal third conjunct and independently elaborated projections. No unpaid in-scope analytic inequality or export remains identified.
- Minor package documentation typo: PreparedOps.lean:16 names `p11_iteratedFDeriv_eq_partial`; the actual theorem at :131 is `p11_partial_eq_iteratedFDeriv`. The displayed mathematical description is accurate; the stale name affects navigation only. No code or documentation repair was made during the audit.
- Graph status metadata still records pr-b/pr-c as NOT_STARTED; an orchestrator can reconcile it with these scoped proof receipts. This audit changes no graph status.
- No new suspected defect in the pinned mathematical source, blueprint proof or frozen statement was found. This review checks the local pinned blueprint slice and actual Lean implementation; it does not revalidate every original external PDF.
- pr-c's larger J-ball supplies amount_transfer's image-carrier estimate by restriction, subject to the explicit geometry facts in the probe. The complete prepared/amount theorem, threshold choice, data selection, pr-d and P-FIXED assembly are not certified here.
- The extra Hessian conjunct strengthens an unsigned export. Relevant signed definitions remain exact and inherited unchanged. Consumers of the old right conjunct must project `.2.1`; no current production caller exists in this worktree.
- The stale generated KAM.lean is the only validation exception, authorized by the audit brief. No other deviation was introduced by this auditor.

**Final package disposition: PASS WITH NOTES for the pr-b/pr-c slice and supporting calculus; F1 closed. No frozen sealing action performed.**
