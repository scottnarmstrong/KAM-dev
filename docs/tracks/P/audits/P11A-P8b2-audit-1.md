# Independent audit: P11A-P8b2, round 1

**Overall verdict: FAIL — export contract F1 at `stepP:p11:pr-b`.** The six modules build and replay in the kernel, and all 88 new public theorems have only permitted axioms. `pr-c` and the real-slice calculus brick pass. The unsigned `p11_pr_b` export omits the explicitly required Hessian bound `<= 1`, although its own proof establishes it locally. This is an interface/completeness failure, not a refutation of the proved proposition.

Audit performed 2026-10-29 in `/root/code/KAM-inp-p11ap8b2`. Audited HEAD: `9d0f2815003c881b3146a016613172ddfc4e4c5a`; comparison ref `inp`: `f38de76be1689652e630490c1007aac7dbd74080`. The entire `git diff inp...HEAD` consists of six new files, 3244 added lines. No production code or git state was changed. The pre-existing untracked handoff was left untouched. The user's exact report destination overrides the generic brief's main-worktree destination.

Read authority: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff including AUDIT FOCUS and overnight rulings, track P statement, design node table and prepared signatures, blueprint preparation proposition/proof, graph pr-b/pr-c records, the six complete added modules, relevant imported specifications and frozen definitions. No frozen theorem anchor or provider is supplied by this package: frozen/provider exact-type and seal-body probes are **not applicable**. This report certifies no frozen headline or full `prepared`/`amount` theorem.

## Required node coverage and finding

| Node / scope | Export | Verdict | Reason |
|---|---|---|---|
| `stepP:p11:pr-b` | `KAM.Planetary.p11_pr_b` | **FAIL** | Frequency bound is literal `2L+1`; Hessian export is `2L+1` instead of required `1`. |
| `stepP:p11:pr-c` | `KAM.Planetary.p11_pr_c` | PASS WITH NOTES | Exact signed closeness clause; explicit data specialization and carrier restriction into amount transfer checked. Generated-root lint exception only. |
| Partial/real-slice brick | `p11op_re_le`, `p11dg_re_le` and calculus helpers | PASS | Actual iterated derivatives and explicit Euclidean comparison factor; kernel and axioms clean. |
| `stepP:p11:pr-in` | inherited `PreparedJets`; new deviation helpers | Supporting infrastructure only | Earlier landed package; derivative estimates are called and derived, not assumed as new export conclusions. |
| `stepP:p11:pr-d` | none claimed | Out of scope | Explicitly reassigned to P8b3 by the handoff ruling; its absence is not a finding. |
| `prepared`, `amount`, signed assembly | none claimed | Out of scope | Explicitly reserved for P8e. No new signed declaration exists in these six files. |

The design table at `docs/tracks/P/design/P11A-LEAN-DESIGN.md:176-182` still maps the preparation slice collectively to `Preparation/Prepared`; this package splits the pr-b/pr-c subproofs into the six modules named in the handoff. There are no additional graph nodes mapped by name to these six new modules. With the explicit pr-d/assembly exclusions, F1 is the only unpaid in-scope node conclusion found.

### F1 — major: expose the already-proved Hessian bound

Locators:

- `KAM/Planetary/Preparation/PreparedFreq.lean:286-302`: theorem signature, ending in `‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 2 * C.L + 1`.
- Same file `:334-348`: local `h2` proves `(n+n) * (eps*L + K0*(1+c)*eps*ell^Q) ≤ 1`; `hop` bounds the actual derivative by that expression. The proof then weakens to `2L+1`.
- `docs/graph/P/DEPGRAPH.md:20657`: “so ¦D^2 N_eps¦ <= 1 <= C_1”.
- `docs/tracks/P/design/P11A-LEAN-DESIGN.md:394`: the same literal step conclusion.
- `blueprint-P/parts/p11-cp09-preparation.tex:209`: “the operator norm is ... <=1<=C_1”.
- AUDIT FOCUS item (1) expressly asks for `|D^2 N| <= 1` literally. `p11_pr_b` is unsigned, so the signed full-spec bound `2L+1` does not authorize weakening this node export.

Refutation probe: copied the complete `p11_pr_b` header under `audit_b_expected`, changed only the final Hessian RHS from `2*C.L+1` to `1`, and used `by exact p11_pr_b hC hnu`. Lean exits 1 with a type mismatch: actual RHS `2*C.L+1`, expected RHS `1` (full diagnostic below).

Repair feasibility was independently tested without editing production: copied the existing complete proof into scratch under `audit_b_stronger_proof` and changed only that RHS to `1`. It elaborates at default resource limits, exit 0, with `[propext, Classical.choice, Quot.sound]`. Exporting this stronger bound, or a separately named literal node export, would address F1. It also implies the signed full-spec bound using `1 <= C.L`; no stronger premise is needed. The auditor has not made this production repair.

## Fidelity, hypotheses, constants, definitions

`p11_pr_b` and `p11_pr_c` choose positive constants before `Fast`, `eps`, `c`, `A`, `Q` (and before `cc` for pr-c). Dependence on n, derivative orders, nu and fixed data is permitted by AMEND P-A002 in the handoff. No constant silently depends on eps or c.

The main exports' smallness premises are explicit numeric inequalities: `0<eps`, `eps*MF<=exp(-1)`, `0<=c`, `3*pi*eps<=pi*rz^2/16`, `5*eps<=s2`, plus the explicit logarithmic smallness condition for pr-b and `K*(1+c)<=cc` for pr-c. The latter compares constants, rather than assuming the desired jet bound. pr-c does not assume theta<=1. The bundled Fast/Slow/Secular specifications are the stated upstream data contracts; no new field is introduced. `hN` and `hcheck` identify the chosen Q with its defining analytic functions. Neither assumes the exported estimate. Conditional arithmetic helpers retain distinct helper names; their eta/radius/factorial premises are proved at their callers in `p11_dev_resc` and `p11_close_partial`.

The Ops brick identifies coordinate partials with complex iterated derivatives by permutation of holomorphic partials on open domains. It expands multilinear arguments into n^j basis combinations, restricts scalars along real inclusion, and applies coordinatewise real part. The real output length is bounded by sqrt(m) times the max norm; real inputs with Euclidean length <=1 have max norm <=1. Thus `sqrt(m)*n^j*B` is paid explicitly. The order-zero case is included. `p11dg_re_le` requires `1<=n` for a nonempty unit sphere, available from `D.n_ge`. No alternate norm instance or `EuclideanSpace` carrier is used.

All 9 new public definitions/abbreviations and all 3 private definitions are literal objects on their full carriers. `p11DevA/G/Z` are explicit scalar comparison expressions, not actual derivatives; their uses prove the corresponding bounds. Lean's total division at zero in these expressions and `p11CloseFun` is not exploited: every division/cancellation-dependent estimate carries positive eps/radius hypotheses. There is no new choice, default, junk-value branch, structure, or conclusion-bearing field.

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

## Signed-clause and consumer compatibility

External files were read-only, at main inp commit `f38de76be1689652e630490c1007aac7dbd74080`:

- `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA256 `fd2c245ea48f1b99f36beb02bba0095e9a55b070be0eae178198fdf20011b9e9`.
- `/root/code/KAM-inp/KAM/Planetary/Preparation/AmountCore.lean`, SHA256 `dedce155e5779f9e3a1380368d752f1de68d9078d34e260e6e098d8890a2e092`.

AmountCore is absent from this package checkout. Its landed text was inspected at `:330-343`; it was not copied into production or built in another worktree. The scratch consumer probe checks the exact `he` predicate, not the entire amount_transfer invocation.

The fresh `audit_prc_signed` probe specializes `C := p11SecularData D`, `A := p11SlowData D nu eps`, unfolds only `p11SlowNormalizedFreq` in the signed checkW identification, and concludes the literal `P11PreparedFullSpec` closeness predicate. Another example obtains that identical predicate from `hFull.2.2.1`. This confirms mu, Boolean `true`, the open J-ball of radius s2/4, subtraction of the selected varpi, eps normalization and exponent `5*tau+2+(tau+1)*(mu+1)` without changing the statement. `D.n_ge` supplies the explicit `hn` in the generic export.

Consumer qualification: `amount_transfer`'s `he` uses carrier `((fun r => J0+eps • r) '' R)`, whereas pr-c uses the larger open J-ball. They have the same jet predicate/function/normalizer, but are not literally equal sets. The scratch `audit_amount_he` derives exactly `he` using only the carrier inclusion and `rho in Rho -> norm rho < 5/4`. The P8e assembly must provide those geometry facts and its other amount_transfer inputs. This is ordinary restriction, not a restatement of the norm or a new analytic estimate; this audit does not claim the full P8e assembly is complete.

No new public name among these 97 occurs as a declaration in the signature file. Existing signed PreparedData declarations are inherited unchanged. Exact equality of full signed `prepared`/`amount` is therefore not claimed by this helper package.

## Declaration inventory

One row per new public declaration (88 theorems, 9 definitions/abbreviations). All names below are in `KAM.Planetary`; locators are under `KAM/Planetary/Preparation/`. A helper PASS means its actual statement and use are sound, not that it independently closes a graph node.

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
| Freq helper | `p11_freq_isOpen_actionNbhd` (PreparedFreq:31) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_res_eq` (PreparedFreq:40) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_U1_sub` (PreparedFreq:48) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_H_diff` (PreparedFreq:84) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_partial_eq` (PreparedFreq:94) | PASS | Differentiates the identifying N formula on actionNbhd box 1; eps denominator cancels one affine derivative. |
| Freq helper | `p11_freq_smallV_norm` (PreparedFreq:173) | PASS | Open-neighborhood/rescaling geometry needed for the exact frequency identity and bounds. |
| Freq helper | `p11_freq_partial` (PreparedFreq:184) | PASS | All coordinate partials through mu+1 on actionNbhd box 3/4, with L at order zero and eps*L at positive orders. |
| Freq helper | `p11_freq_opNorm_le` (PreparedFreq:261) | PASS | Converts basis bounds to the max-norm operator bound N*B, including the dimension-zero case. |
| pr-b | `p11_pr_b` (PreparedFreq:286) | **FAIL F1** | F1: unsigned node export states the Hessian bound <= 2L+1, not the required <= 1; proof contains the stronger estimate locally. |
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

## Independent hygiene checks and exact receipts

Every accepted Lean command used `LEAN_NUM_THREADS=1`, `nice -n 5`, default heartbeat/depth limits, and no parallel check invocation. The targeted build used the required gate and the inherited overlay. No clean/update/cache operation was run.

Auditor deviation: the first stronger-B scratch check was launched before the expected-B command's completion was confirmed. Those first two receipts were discarded because serialization was not assured. Both checks were then rerun using sequential, blocking `subprocess.run` calls; only those replacement results are used below. No production file was edited. Build, axioms, kernel replay, compatibility probe and final lint were separate serialized checks. Other users' unrelated processes in shared worktrees were not controlled by this audit.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap8b2 KAM.Planetary.Preparation.PreparedClose
```

Exit **0**. Output starts `[inp-gate] slot 1 acquired 03:09:46 for KAM.Planetary.Preparation.PreparedClose` and ends:

```text
Build completed successfully (9426 jobs).
```

PreparedClose transitively imports all six audited modules. Lake replayed cached jobs; 9426 is the job count, not a claim that 9426 files were rebuilt. Nonfatal style warnings include unused hypotheses in PreparedNum/PreparedClose, sequence-focus suggestions and deprecated `if_true`; inherited warnings were also replayed. No elaboration error or resource-limit override.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PreparedOps KAM.Planetary.Preparation.PreparedDev KAM.Planetary.Preparation.PreparedNum KAM.Planetary.Preparation.PreparedResc KAM.Planetary.Preparation.PreparedFreq KAM.Planetary.Preparation.PreparedClose
```

One invocation, exit **0**; complete output:

```text
replaying KAM.Planetary.Preparation.PreparedClose
replaying KAM.Planetary.Preparation.PreparedFreq
replaying KAM.Planetary.Preparation.PreparedResc
replaying KAM.Planetary.Preparation.PreparedNum
replaying KAM.Planetary.Preparation.PreparedDev
replaying KAM.Planetary.Preparation.PreparedOps
```

### All new public theorem axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/P8b2Axioms.lean
```

The scratch file imported PreparedClose and issued one `#print axioms KAM.Planetary.<name>` for each of the 88 theorem rows in the inventory. Exit **0**. Complete output follows; every set is a subset of `{propext, Classical.choice, Quot.sound}`:

```text
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
'KAM.Planetary.p11_freq_isOpen_actionNbhd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_res_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_U1_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_H_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_smallV_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_pr_b' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'KAM.Planetary.p11_resc_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_prod2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_rpow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_pure_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_Om' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_rho_dev' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_resc_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dev_resc' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Fidelity probes

All three commands below used the same prefix:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false
```

1. `.lake/abi-scratch/P8b2Compatibility.lean`: exit **0**, with exact output:

```text
'KAM.Planetary.audit_prc_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.audit_amount_he' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The accepted probe contents are preserved here for reproducibility after scratch deletion:

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
```

2. `.lake/abi-scratch/P8b2ExpectedB.lean`: exit **1**, expected negative type probe. Exact diagnostic:

```text
.lake/abi-scratch/P8b2ExpectedB.lean:21:2: error: Type mismatch
  p11_pr_b hC hnu
has type
  ∃ K,
    0 < K ∧
      ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n} {Q : P11PreparedData n},
        0 < eps →
          eps * C.MF ≤ Real.exp (-1) →
            0 ≤ c →
              K * (1 + c) * eps * Real.log (1 / eps) ^ (5 * C.tau + 2 + (C.tau + 1) * (↑(p11PatchData D).mu + 1)) ≤ 1 →
                3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 →
                  5 * eps ≤ p11s2 C nu eps →
                    P11FastSpec C eps Fast →
                      P11SlowSpecOf C Fast nu eps c A →
                        (∀ I ∈ actionNbhd (p11PreparedBox n) 1,
                            Q.N I =
                              (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) / ↑eps) →
                          p11Bound (actionNbhd (p11PreparedBox n) (3 / 4)) (p11PreparedFreq Q) (2 * C.L + 1) ∧
                            ∀ I ∈ actionNbhd (p11PreparedBox n) (3 / 4), ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 2 * C.L + 1
but is expected to have type
  ∃ K,
    0 < K ∧
      ∀ {Fast : P11FastData n} {eps c : ℝ} {A : P11SlowData n} {Q : P11PreparedData n},
        0 < eps →
          eps * C.MF ≤ Real.exp (-1) →
            0 ≤ c →
              K * (1 + c) * eps * Real.log (1 / eps) ^ (5 * C.tau + 2 + (C.tau + 1) * (↑(p11PatchData D).mu + 1)) ≤ 1 →
                3 * Real.pi * eps ≤ Real.pi * C.rz ^ 2 / 16 →
                  5 * eps ≤ p11s2 C nu eps →
                    P11FastSpec C eps Fast →
                      P11SlowSpecOf C Fast nu eps c A →
                        (∀ I ∈ actionNbhd (p11PreparedBox n) 1,
                            Q.N I =
                              (A.h0 (p11Rescale C.J0 eps (0, I)).2 + A.g2 (p11Rescale C.J0 eps (0, I)).2) / ↑eps) →
                          p11Bound (actionNbhd (p11PreparedBox n) (3 / 4)) (p11PreparedFreq Q) (2 * C.L + 1) ∧
                            ∀ I ∈ actionNbhd (p11PreparedBox n) (3 / 4), ‖fderiv ℂ (p11PreparedFreq Q) I‖ ≤ 1
```

3. `.lake/abi-scratch/P8b2StrongerB.lean`: exit **0**. This is the original production theorem/proof copied under a fresh name, changing only the final theorem-statement Hessian RHS to `1`. Its output is:

```text
'KAM.Planetary.audit_b_stronger_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This scratch feasibility check is not a production fix and does not make the present node export pass.

### Source lint, frozen integrity and imports

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the brief-permitted stale generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1199 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

`KAM.lean` was not regenerated. Source checks found no forbidden tokens, overrides, EuclideanSpace carrier, overlong line or oversize file. All six modules have copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section`.

| Module | Total lines | Maximum allowed |
|---|---:|---:|
| PreparedOps | 531 | 1500 |
| PreparedDev | 844 | 1500 |
| PreparedNum | 337 | 1500 |
| PreparedResc | 557 | 1500 |
| PreparedFreq | 356 | 1500 |
| PreparedClose | 619 | 1500 |

All source lines in these six files are <=100 Unicode characters. A direct name scan against other KAM declarations found no reused public helper short names. All new public declarations remain in `KAM.Planetary`; the three generic ops definitions are private. No harmful root shadow was found.

A recursive scan of local KAM imports reached 380 modules, including 64 manifest-bound frozen definitions, all `SEALED`. It reached **zero provider modules and zero frozen theorem modules**; no DRAFT_SORRY theorem import or proof dependency is concealed. Imported frozen definition content relevant to this slice includes the actual complex max-norm `actionNbhd`, `complexStrip`, phase and fixed Hamiltonian definitions. The main proof-axiom and kernel results additionally rule out a transitive sorry dependency in the audited theorems.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

All exit **0**, no output. No protected file differs from the merge base in the audited three-dot diff. Audit changes are report-only; all auditor-created probes and logs in `.lake/abi-scratch/` are deleted after their evidence is embedded here. The pre-existing untracked handoff remains.

## Source/blueprint issues, uncertainties, deviations

- **F1 is an implementation/export deviation from the literal graph/design proof-step and explicit audit focus.** The signed prepared-system proposition and P11PreparedSpec legitimately use the weaker `2L+1`; the proof-step and this audit require the stronger intermediate result `1`. These two levels should not be conflated. The scratch stronger statement proves this is a missing export, not a suspected mathematical defect.
- No additional suspected defect in a pinned mathematical source, frozen statement, or blueprint proof was identified. This is a package audit of the cited local blueprint slice; it is not a new independent validation of all original external PDFs.
- The graph records pr-b/pr-c as `NOT_STARTED` at `docs/graph/P/DEPGRAPH.md:20674` and `:20702`. They are inherited status metadata, untouched in this report-only audit; pr-b must not be marked fully paid while F1 remains.
- `amount_transfer` compatibility was verified against its actual landed predicate text and a Lean restriction probe, not by importing absent AmountCore into this branch or assembling the full signed theorem. P8e still owns the data selection, geometry and assembly obligations.
- The only source-lint exception is stale generated KAM.lean, expressly allowed by the brief. The auditor's temporary serialization lapse and clean replacement checks are disclosed above.

Required next action: retain the valid pr-c/calculus work, expose `p11_pr_b`'s already-proved Hessian `<=1` conclusion, and re-audit that export. No production changes, frozen changes, or sealing action were performed here.
