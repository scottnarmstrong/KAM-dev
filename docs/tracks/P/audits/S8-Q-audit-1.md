# S8-Q independent package audit 1

Date: 2026-10-28. **Overall package verdict: FAIL for the requested complete node slice.**
The signed `KAM.Planetary.SecularForm.quadratic_form` passes the mathematical and exact-statement review; its verification receipts are recorded below. The assigned `stepP:p8:qf-diag2` is not discharged by this package. There is also a short-name uniqueness discrepancy. These findings do not refute the signed expansion.

## Scope, authority and frozen snapshot

Audit scope: only `KAM/Planetary/SecularForm/Quadratic.lean` and its thirteen `Quadratic/*.lean` modules (2033 lines total, maximum 257). Tier 2, read-only proof/statement inspection followed by a separate adversarial recheck and hygiene. Only this report and temporary `.lake/abi-scratch/` artifacts were authorized; no commits, repairs, generated-file changes or external communication. The user's exact worktree report path overrides the brief's generic instruction to write into the main inp worktree. No delegation was used.

Snapshot v1: HEAD `7a82787a610405651cec8aa86b843db69217ae35`; observed `inp` `ccd0fdc16c5e59bc83b9bda4321d2d85eadb8825`. `git diff inp...HEAD` warns of multiple merge bases and chooses `2357d954eb506f13424878cde5561628ba303dfe`; the other bases are `0a5d9f1ed4896fe439fd6cb914bdf85a3d6c73b7` and `aff048b7e4ec66d1eb3f7ac45e5b03552f95434e`. The requested diff has 26 new files / 4041 lines, including inherited S8-D/S8-X files. Those twelve input files are outside this audit's proof scope. The scoped diff SHA-256 is `0c7cdb5ebf7d99cae6595ad793a714673b9b713d36013f85be9d74ab04d27b52`.

Read authority: AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff, P810 design revision 2 and both design audits, relevant Track P statement conventions/P5/P7, Part 8 source and published graph packet, the live main-worktree OVERNIGHT 13:08 ruling. The main OVERNIGHT file read for the ruling had SHA-256 `8123c71c44430455861125904f1d0a2e5c50eaa7377885c5246abe2528b97b6e`. The ruling permits internal literal-average helpers with source premises; it does not approve extra assumptions or a matrix supplied as a premise. No frozen theorem anchor is implemented by this package; provider/frozen seal comparison is inapplicable. The appropriate contract is the signed P810 infrastructure theorem.

| Audited file (relative to `KAM/Planetary/SecularForm/`) | Lines | SHA-256, snapshot v1 |
|---|---:|---|
| `Quadratic.lean` | 74 | `66bb4b3ce960e8729d37caadf3d7e01316ef3dc975f7f55f6b61716f54848235` |
| `Quadratic/Algebra.lean` | 115 | `631e79c335a391e00dbfa478f8c8507e46e99cbc1b9582b1af1f872e1a0014f4` |
| `Quadratic/Calculus.lean` | 124 | `bc14f0de91599b1c66aad89bb88edb74eeeb2887f24110c282e524b42df5f6d7` |
| `Quadratic/Coeff.lean` | 110 | `09495e34b339e81198efbe7642213646e3fe79682d0c47349ed661b32e54e7c8` |
| `Quadratic/Constants.lean` | 82 | `a5770134637ae830d41d980951e45068ba28c4e883e67d2eb403c0af01154164` |
| `Quadratic/Jet.lean` | 177 | `dac9c06aa7aec8759bb2a01f9b70fc9b6efcfd67e3bb1761ecaf9f458405e73e` |
| `Quadratic/Marginal.lean` | 96 | `9cd498b67a81776c1884338f78c1735adec10c9df4cbbbdd0638288654b71a50` |
| `Quadratic/PairDiag.lean` | 165 | `149f057f260a2d057ab6f4934222f0112eae2858f465db32e39cfde82896e6c8` |
| `Quadratic/PairHessian.lean` | 223 | `d36fc5c77c80201ae4ddfa7bec42c57aebbae521d4d6a60b6d64d23a5d70811f` |
| `Quadratic/PairIdentify.lean` | 80 | `5a14fb841b8e5a68aa1e4f042cf71e286d5c6b904b07e2c9bbf909598747b90b` |
| `Quadratic/PairLocal.lean` | 226 | `234d50ea0a62af948c1a2cac023a0c4ff0bb1f84fac7dfd3aa05e6ff80a1f7f6` |
| `Quadratic/PairSplit.lean` | 124 | `06518337411929c96c8fef6427a5fe1e6bff708f6551baa9f1f9d47cea502612` |
| `Quadratic/Schwarz.lean` | 180 | `28f0e54ff39e327881b678e3e535793b3e9a4df00b57004ed40c38ba3b901934` |
| `Quadratic/Uniform.lean` | 257 | `b8c768b99993ee56ce13fb040275b0bc7333ab597710f71bdf1a977bdacce5eb` |

The original signature file is `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, SHA-256 `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`; it is absent from the package worktree. Blueprint Part 8 SHA-256 is `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc`. Design SHA-256 is `f555e21a468123ce906f6818359cb8faaffc5d0435ea0f70c65967cec38722c4`. The untracked, pre-existing handoff SHA-256 is `0f01048ea3573dbe2eff4a1f5d504cd68555dd78f6691cc591ad562fd2580621`.

## Findings and attempted refutations

**F1 — Major, assigned-node coverage gap; survived recheck.** `Quadratic.lean:28–31` says “The diagonalisation cut ... is ... consumed by S9-Q; it is not a separate analytic fact”. The handoff likewise says nothing was added for it. However `blueprint-P/parts/p8-secular-form.tex:170` explicitly states the rotation is “symplectic” and preserves the sum of squares. The published packet `docs/graph/P/packets/P-p8.nodes.md:1262–1283` quantifies an SO diagonalizer and concludes symplecticity, sum-of-squares preservation and the `2*sigma*Gamma` identity. Design row S8-Q at line 432 assigns `qf-pair/assembly/diag2` to this package. None of the 87 public theorems takes an SO matrix or exports these rotation claims.

Adversarial recheck: the signed `quadratic_form` header contains no rotation, diagonalizer, symplecticity or oscillator expression. The signed S9 `lift` (lines 332–344) and `diagonalize` (364–386) do own cooperating stronger future results, and the earlier design audits accepted `quadratic_form` when read with cooperating exports. Thus this is **not** a defect in the signed expansion or an allegation that diagonalisation is false. It is a genuine mismatch with this prompt's requirement that this S8-Q node slice be complete: no source text or 13:08 ruling reassigns this node, and no proof in the audited modules discharges it. Keep the node open or explicitly reassign and independently validate its supplier; do not mark it proved by this package.

**F2 — Minor, short-name hygiene/handoff discrepancy; survived recheck.** `Quadratic/Uniform.lean:31` introduces public `quadRemainder`; `KAM/Apost/NewtonError.lean:70` already defines public `quadRemainder` (namespace begins at line 45). This contradicts the handoff's “New public names are unique (checked by grep against all of KAM)” and the focus's literal no-reused-public-name criterion. Recheck: their fully qualified names differ (`KAM.Planetary.SecularForm.quadRemainder` versus `KAM.Apost.quadRemainder`), so there is no Lean environment redeclaration and no mathematical defect. If the campaign only requires fully qualified uniqueness, this is an informational correction to the handoff; under its stated grep/short-name policy it needs a rename. No other outside-scope short-name candidate was found in the static declaration scan.

**N1 — Expected generated-root staleness.** The brief explicitly permits the `KAM.lean is out of date` lint message; do not regenerate the root during this report-only audit.

No suspected new pinned-paper erratum was found. The inherited p8 line 157 source gap quotes Fej04r p.50, “Le calcul complet est un peu long”; [LR95] is not pinned. This package supplies the assembly/remainder part of the replacement proof; the S8-D/S8-X analytic inputs remain separately audited inputs, not a fresh paper derivation certified here. No numerical-ratio proof or assumed coefficient bundle is used.

**N2 — Inherited branch whitespace.** `git diff --check inp...HEAD` exits 2 for trailing whitespace in `KAM/Planetary/SecularForm/CrossJet/Selection.lean:198` (`simp_rw [mul_comm (Real.cos _)] `). This file belongs to inherited S8-X, outside the requested audit scope. The scoped S8-Q diff passes the same check; no repair was made.

## Statement and proof assessment

`quadratic_form` header is **byte-identical**, from `theorem quadratic_form` through the type before `:=`, to signature lines 175–184. Header-suffix SHA-256: `29983e329f185d722f7a6a732f36d4f9f0bc7a8c083afb338fb84081cfe4dba0`. The proof uses the literal fixed-model `secular`/frozen `secularAverage`, action order `(xi,Lambda,eta)`, physical `planeLength` in the potential, and the signed halved matrix `coeffs`. The fourth-order remainder uses the ambient Pi/product max norm as intended. Constants `r,C` depend on fixed `D,a` and precede every nearby point/action; no point-dependent constant is smuggled into the uniform assertion.

The pair marginal is proved using independent coordinates of the normalized product probability law; continuity supplies measurability and the compact integrability needed when distributing finite sums. `secular_eq_sum_pair` requires source chart membership and pair separation; both are derived near the circular point from `perturbation_analytic`. The two-dimensional average is identified with the literal `pairSlowSecular`, including both factors `(2*pi)^(-1)` and the negative Newtonian potential. The swap proof uses continuity to justify Fubini.

`pair_diag_first/second` obtain the negative diagonal entries from S8-D's literal diagonal jet, radial identity and planet exchange. `pair_second_derivative` at PairHessian:196–205 supplies `cross_hessian D ha hij` from S8-X directly; the coefficients are conclusions, not premises of this planetary theorem. `quad_pair_sum` expands the actual `coeffs/qhat` definitions, counts each unordered pair once and each cross coefficient twice. The jet of order 0 uses the actual circular value; orders 1 and 3 use evenness; order 2 uses the pair sum.

The S8-W deviation is sound: the generic, distinctly named `hessian_pair_form` has genuine conditional derivative/symmetry premises, all discharged for the pair average. Symmetry of the Hessian follows from C2 regularity; reflection kills the two mixed xi/eta entries; the quarter turn identifies the two surviving cross entries. Diagonal blocks come from both diagonal ray identities. Thus it loses no second-order information and does not assume an invariant representation for the physical function. It does not discharge quartic invariant theory for S8-4.

`schwarz_quotient_bound_four` removes the order-four zero and bounds the holomorphic quotient on each smaller circle by the maximum principle; `schwarz_order_four` takes the radius limit. Real/complex iterated-derivative bridges prove the vanishing jet for that complex function. In `remainder_pointwise`, normalize by epsilon = max(norm xi,norm eta); epsilon=0 is handled separately using the circular value, so division at zero is not used. The complex-line bound is `M1+MT+2*r^2*ME`, and Schwarz yields its ratio to `r^4` times epsilon^4. `exists_remainder_constants` constructs all these constants using compact closed balls strictly inside the original analytic domain, shrinks the action neighbourhood to preserve increasing positive axes, and proves their bounds. The final theorem enlarges the resulting coefficient to its absolute value plus one. No uniform remainder hypothesis is left unpaid.

## Per-node verdicts

| Node / anchor | Lean export(s) | Verdict | Reason |
|---|---|---|---|
| signed infrastructure `bpP:p8:quadratic-form` | `quadratic_form` | PASS WITH NOTES | Exact signed type and proved uniform expansion; F1 limits full blueprint coverage, F2 hygiene note. No frozen seal claimed. |
| `stepP:p8:qf-pair` | `secular_eq_sum_pair`, `secular_pair_eq`, `hessian_pair_form`, `pair_second_derivative` | PASS | Literal averages; complete quadratic invariant calculation. |
| `stepP:p8:qf-assembly` | `quad_pair_sum`, `iteratedDeriv_rayRemainder`, `exists_remainder_constants`, `quadratic_form` | PASS | Correct signs/factors, order-four jet and uniform bound. |
| `stepP:p8:qf-diag2` | no export | FAIL (coverage) | F1: no SO rotation, symplecticity, sum-of-squares or oscillator diagonalisation theorem. |

## Declaration inventory

All names below are relative to `KAM.Planetary.SecularForm`; file paths are relative to `KAM/Planetary/SecularForm/`. The generic calculus and Hessian lemmas implement stronger reusable statements and have distinct names; their analytic/continuity/derivative premises are conditional inputs, not extra premises in `quadratic_form`.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| quadratic-form / signed export | `quadratic_form` — `Quadratic.lean:43` | PASS | Byte-identical signed header; constant independent of nearby point. |
| qf-assembly / pair algebra | `quad_sum_erase_split` — `Quadratic/Algebra.lean:27` | PASS | Finite sums and actual signed coefficient definitions; no coefficient premise. |
| qf-assembly / pair algebra | `sum_offdiag` — `Quadratic/Algebra.lean:46` | PASS | Finite sums and actual signed coefficient definitions; no coefficient premise. |
| qf-assembly / pair algebra | `quadPairA_comm` — `Quadratic/Algebra.lean:54` | PASS | Finite sums and actual signed coefficient definitions; no coefficient premise. |
| qf-assembly / pair algebra | `quad_pair_sum` — `Quadratic/Algebra.lean:58` | PASS | Finite sums and actual signed coefficient definitions; no coefficient premise. |
| qf-assembly / calculus | `iteratedDeriv_two_ray` — `Quadratic/Calculus.lean:25` | PASS | Reusable calculus statement, proved from explicit regularity/bound hypotheses. |
| qf-assembly / calculus | `iteratedDeriv_eq_zero_of_bound` — `Quadratic/Calculus.lean:52` | PASS | Reusable calculus statement, proved from explicit regularity/bound hypotheses. |
| qf-assembly / calculus | `iteratedDeriv_two_quadratic` — `Quadratic/Calculus.lean:97` | PASS | Reusable calculus statement, proved from explicit regularity/bound hypotheses. |
| qf-assembly / calculus | `iteratedDeriv_two_of_bound` — `Quadratic/Calculus.lean:109` | PASS | Reusable calculus statement, proved from explicit regularity/bound hypotheses. |
| qf-assembly / analytic coefficients | `analyticAt_axis` — `Quadratic/Coeff.lean:28` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `axis_action` — `Quadratic/Coeff.lean:35` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `action_axis` — `Quadratic/Coeff.lean:39` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `axis_pos` — `Quadratic/Coeff.lean:50` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `continuous_axis` — `Quadratic/Coeff.lean:54` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `eventually_mem_axes` — `Quadratic/Coeff.lean:59` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `eventually_axis_mem_axes` — `Quadratic/Coeff.lean:74` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `analyticAt_constantTerm` — `Quadratic/Coeff.lean:81` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / analytic coefficients | `analyticAt_quad` — `Quadratic/Coeff.lean:96` | PASS | Actual polynomial axis map and analytic coefficients on increasing positive axes. |
| qf-assembly / compact constants | `exists_remainder_constants` — `Quadratic/Constants.lean:27` | PASS | Witnesses and bounds obtained from compactness, before action quantification. |
| qf-assembly / vanishing jet | `analyticAt_raySlow` — `Quadratic/Jet.lean:41` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `continuous_raySlow` — `Quadratic/Jet.lean:47` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `raySlow_zero_mem` — `Quadratic/Jet.lean:54` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `secular_ray_eq` — `Quadratic/Jet.lean:60` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `rayRemainder_zero` — `Quadratic/Jet.lean:81` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `analyticAt_rayRemainder` — `Quadratic/Jet.lean:94` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `rayRemainder_even` — `Quadratic/Jet.lean:103` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `iteratedDeriv_rayRemainder_odd` — `Quadratic/Jet.lean:119` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `iteratedDeriv_two_rayRemainder` — `Quadratic/Jet.lean:124` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-assembly / vanishing jet | `iteratedDeriv_rayRemainder` — `Quadratic/Jet.lean:167` | PASS | Actual remainder; value and derivatives through order three proved zero. |
| qf-pair / marginal | `pi_angleLaw` — `Quadratic/Marginal.lean:37` | PASS | Normalized product-measure identity with stated continuity guard. |
| qf-pair / marginal | `avg_eq_integral_angleLaw` — `Quadratic/Marginal.lean:45` | PASS | Normalized product-measure identity with stated continuity guard. |
| qf-pair / marginal | `avg_pair_marginal` — `Quadratic/Marginal.lean:55` | PASS | Normalized product-measure identity with stated continuity guard. |
| qf-diag / assembly adapter | `iteratedDeriv_two_of_expansion` — `Quadratic/PairDiag.lean:32` | PASS | Diagonal derivatives proved from literal S8-D jet; positive actions/distinct axes derived. |
| qf-diag / assembly adapter | `planeSq_smul'` — `Quadratic/PairDiag.lean:63` | PASS | Diagonal derivatives proved from literal S8-D jet; positive actions/distinct axes derived. |
| qf-diag / assembly adapter | `pair_diag_ray` — `Quadratic/PairDiag.lean:68` | PASS | Diagonal derivatives proved from literal S8-D jet; positive actions/distinct axes derived. |
| qf-diag / assembly adapter | `pair_swap_nbhd` — `Quadratic/PairDiag.lean:93` | PASS | Diagonal derivatives proved from literal S8-D jet; positive actions/distinct axes derived. |
| qf-diag / assembly adapter | `pair_diag_first` — `Quadratic/PairDiag.lean:108` | PASS | Diagonal derivatives proved from literal S8-D jet; positive actions/distinct axes derived. |
| qf-diag / assembly adapter | `pair_diag_second` — `Quadratic/PairDiag.lean:131` | PASS | Diagonal derivatives proved from literal S8-D jet; positive actions/distinct axes derived. |
| qf-pair / Hessian | `crossSlice_apply` — `Quadratic/PairHessian.lean:40` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / Hessian | `hessian_cross` — `Quadratic/PairHessian.lean:46` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / Hessian | `pairReflect_smul` — `Quadratic/PairHessian.lean:69` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / Hessian | `pairQuarter_smul` — `Quadratic/PairHessian.lean:74` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / Hessian | `hessian_pair_form` — `Quadratic/PairHessian.lean:80` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / Hessian | `pair_second_derivative` — `Quadratic/PairHessian.lean:196` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / Hessian | `pair_value_zero` — `Quadratic/PairHessian.lean:208` | PASS | Hessian/ray identity or explicit basis calculation; all physical inputs discharged. |
| qf-pair / literal integral | `secular_pair_eq` — `Quadratic/PairIdentify.lean:29` | PASS | Literal normalized two-angle average; swap guarded by continuity. |
| qf-pair / literal integral | `pairSlowSecular_swap` — `Quadratic/PairIdentify.lean:46` | PASS | Literal normalized two-angle average; swap guarded by continuity. |
| qf-pair / chart and symmetries | `continuous_embedSlow` — `Quadratic/PairLocal.lean:32` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `analyticAt_embedSlow` — `Quadratic/PairLocal.lean:39` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `mem_slowDom_of_realDisc` — `Quadratic/PairLocal.lean:56` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairSeparated_of_realDisc` — `Quadratic/PairLocal.lean:78` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairData_self` — `Quadratic/PairLocal.lean:102` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairSlow_embedSlow` — `Quadratic/PairLocal.lean:107` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairSlowSecular_pairData` — `Quadratic/PairLocal.lean:112` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `secular_embedSlow_eq` — `Quadratic/PairLocal.lean:116` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `axes_pair` — `Quadratic/PairLocal.lean:127` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `action_pair` — `Quadratic/PairLocal.lean:133` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `exists_pair_nbhd` — `Quadratic/PairLocal.lean:140` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `analyticAt_pairSlowSecular` — `Quadratic/PairLocal.lean:162` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `continuous_pairReflect` — `Quadratic/PairLocal.lean:176` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `continuous_pairQuarter` — `Quadratic/PairLocal.lean:181` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairReflect_zero` — `Quadratic/PairLocal.lean:186` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairQuarter_zero` — `Quadratic/PairLocal.lean:189` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairSlowSecular_reflect` — `Quadratic/PairLocal.lean:192` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / chart and symmetries | `pairSlowSecular_quarter` — `Quadratic/PairLocal.lean:208` | PASS | Source domain/separation derived; exact coordinate embeddings and local symmetries. |
| qf-pair / literal splitting | `continuous_planeLength_q` — `Quadratic/PairSplit.lean:55` | PASS | Literal pair potential and guarded integral identities. Private helper; included for completeness. |
| qf-pair / literal splitting | `perturbation_false_eq` — `Quadratic/PairSplit.lean:59` | PASS | Literal pair potential and guarded integral identities. |
| qf-pair / literal splitting | `perturbation_pair_eq` — `Quadratic/PairSplit.lean:67` | PASS | Literal pair potential and guarded integral identities. |
| qf-pair / literal splitting | `secular_eq_avg` — `Quadratic/PairSplit.lean:76` | PASS | Literal pair potential and guarded integral identities. |
| qf-pair / literal splitting | `avg_finset_sum` — `Quadratic/PairSplit.lean:79` | PASS | Literal pair potential and guarded integral identities. |
| qf-pair / literal splitting | `continuous_pairPos` — `Quadratic/PairSplit.lean:86` | PASS | Literal pair potential and guarded integral identities. |
| qf-pair / literal splitting | `continuous_pairTerm` — `Quadratic/PairSplit.lean:95` | PASS | Literal pair potential and guarded integral identities. |
| qf-pair / literal splitting | `secular_eq_sum_pair` — `Quadratic/PairSplit.lean:103` | PASS | Literal pair potential and guarded integral identities. |
| qf-assembly / order-four Schwarz | `schwarz_quotient_bound_four` — `Quadratic/Schwarz.lean:29` | PASS | Holomorphic order-four estimate and derivative bridges proved. |
| qf-assembly / order-four Schwarz | `schwarz_order_four` — `Quadratic/Schwarz.lean:94` | PASS | Holomorphic order-four estimate and derivative bridges proved. |
| qf-assembly / order-four Schwarz | `iteratedDeriv_ofReal` — `Quadratic/Schwarz.lean:118` | PASS | Holomorphic order-four estimate and derivative bridges proved. |
| qf-assembly / order-four Schwarz | `iteratedDeriv_ofReal_comp` — `Quadratic/Schwarz.lean:141` | PASS | Holomorphic order-four estimate and derivative bridges proved. |
| qf-assembly / order-four Schwarz | `uniform_ray_bound` — `Quadratic/Schwarz.lean:168` | PASS | Holomorphic order-four estimate and derivative bridges proved. |
| qf-assembly / uniform ray bound | `quad_smul` — `Quadratic/Uniform.lean:35` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `quad_zero` — `Quadratic/Uniform.lean:44` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `abs_quad_le` — `Quadratic/Uniform.lean:47` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `analyticAt_remainder` — `Quadratic/Uniform.lean:58` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `realDisc_coord` — `Quadratic/Uniform.lean:76` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `polydisc_mono` — `Quadratic/Uniform.lean:84` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `realDisc_mono` — `Quadratic/Uniform.lean:88` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `differentiable_linePt` — `Quadratic/Uniform.lean:95` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `linePt_mem_polydisc` — `Quadratic/Uniform.lean:102` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |
| qf-assembly / uniform ray bound | `remainder_pointwise` — `Quadratic/Uniform.lean:122` | PASS | Actual remainder, max norm and proved normalized-ray estimate. |

## Definition classification (whole carriers)

Every definition is exposed by the surrounding `@[expose] public noncomputable section`. There are no new structures or abbreviations. None branches to a fabricated fallback. Total inverses/integrals inherited from Lean are only interpreted physically after the local chart/separation guards have been established.

| Node / role | Definition | Classification and whole-carrier verdict |
|---|---|---|
| qf-assembly / vanishing jet | `raySlow` — `Quadratic/Jet.lean:33` | PASS: Literal slow ray at action D a for every real parameter. |
| qf-assembly / vanishing jet | `rayRemainder` — `Quadratic/Jet.lean:37` | PASS: Actual difference from the literal constant/quadratic polynomial along the ray. |
| qf-assembly / vanishing jet | `rayPair` — `Quadratic/Jet.lean:52` | PASS: Literal two-planet vector projection of xi/eta. |
| qf-pair / marginal | `angleLaw` — `Quadratic/Marginal.lean:28` | PASS: Actual normalized restricted Lebesgue measure; probability proved using 2*pi>0. |
| qf-pair / Hessian | `crossSlice` — `Quadratic/PairHessian.lean:32` | PASS: Actual continuous linear embedding of two xi directions; linearity proved. |
| qf-pair / chart and symmetries | `embedSlow` — `Quadratic/PairLocal.lean:29` | PASS: Literal rearrangement of two planar vectors at fixed actions. |
| qf-pair / chart and symmetries | `pairReflect` — `Quadratic/PairLocal.lean:171` | PASS: Actual simultaneous eta reflection on the whole vector pair. |
| qf-pair / chart and symmetries | `pairQuarter` — `Quadratic/PairLocal.lean:174` | PASS: Actual simultaneous quarter turn on the whole vector pair. |
| qf-pair / literal splitting | `pairData` — `Quadratic/PairSplit.lean:30` | PASS: Actual two-planet restriction of positive physical data; valid even for repeated indices, which are excluded in pair applications. |
| qf-pair / literal splitting | `pairSlow` — `Quadratic/PairSplit.lean:40` | PASS: Literal coordinate projection, defined for every slow point and indices. |
| qf-pair / literal splitting | `pairPos` — `Quadratic/PairSplit.lean:44` | PASS: Literal one-body Poincare position at the supplied coordinates; no replacement orbit. |
| qf-pair / literal splitting | `pairTerm` — `Quadratic/PairSplit.lean:48` | PASS: Literal negative pair potential with physical planeLength. At collision Lean division is total, but physical conclusions require proved separation. |
| qf-pair / literal splitting | `PairSeparated` — `Quadratic/PairSplit.lean:52` | PASS: Source geometric noncollision for every independent pair of mean longitudes, with i<j; not an assumed conclusion about coefficients. |
| qf-assembly / uniform ray bound | `quadRemainder` — `Quadratic/Uniform.lean:31` | PASS: Actual pointwise secular remainder on the entire slow carrier; F2 concerns short-name reuse only. |
| qf-assembly / uniform ray bound | `linePt` — `Quadratic/Uniform.lean:92` | PASS: Actual complex line at fixed real actions; no off-line continuation substitute. |

The additional anonymous public instance at `Quadratic/Marginal.lean:31` proves `IsProbabilityMeasure angleLaw`; it carries no assumptions and installs no ambient function-space or matrix norm.

## Verification receipts

Only one auditor-controlled Lean/Lake/checker operation was active at a time. Each used `LEAN_NUM_THREADS=1` and `nice -n 5` (the build wrapper supplies niceness). Shared infrastructure was used as provided; no library clean, dependency change or cache download was performed.

1. Target build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s8q KAM.Planetary.SecularForm.Quadratic
   [inp-gate] slot 2 acquired 16:05:53 for KAM.Planetary.SecularForm.Quadratic
   Build completed successfully (9169 jobs).
   exit 0
   ```

   This was an incremental targeted gate check, not a clean rebuild. No warnings in audited files. Replayed upstream warnings: unused variables in `Kepler/Energy`, `Kepler/Mass`, `Poincare/Chart`, `Poincare/D25`, `Poincare/Holomorphic`, `Hamiltonian/Algebra`, `Hamiltonian/Chart`; deprecated `ite_cond_eq_false` in `SecularForm/Coefficients` at 54 and 112. No source modification was needed.

2. Fresh untracked signed-statement and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S8QProbe.lean
   exit 0; 87 axiom outputs; no errors or warnings
   ```

   The probe imports only the proved facade, copies the exact signed header under fresh name `auditS8QSigned`, proves it by `exact quadratic_form D ha`, and elaborates `example : type_of% @auditS8QSigned := @quadratic_form`. Thus the complete polymorphic signed type is checked as well as its source-string identity. No signed `sorry` declaration is imported. There is no frozen provider or seal body to validate here.

   Every public theorem in the declaration inventory was independently queried with `#print axioms`; all 87 outputs have exactly the same list. Representative exact output:

   ```text
   'KAM.Planetary.SecularForm.quadratic_form' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.quad_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.pair_second_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.secular_eq_sum_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.schwarz_order_four' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.SecularForm.exists_remainder_constants' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. One kernel replay invocation, with the full fourteen-module argument list:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.Quadratic \
     KAM.Planetary.SecularForm.Quadratic.Algebra \
     KAM.Planetary.SecularForm.Quadratic.Calculus \
     KAM.Planetary.SecularForm.Quadratic.Coeff \
     KAM.Planetary.SecularForm.Quadratic.Constants \
     KAM.Planetary.SecularForm.Quadratic.Jet \
     KAM.Planetary.SecularForm.Quadratic.Marginal \
     KAM.Planetary.SecularForm.Quadratic.PairDiag \
     KAM.Planetary.SecularForm.Quadratic.PairHessian \
     KAM.Planetary.SecularForm.Quadratic.PairIdentify \
     KAM.Planetary.SecularForm.Quadratic.PairLocal \
     KAM.Planetary.SecularForm.Quadratic.PairSplit \
     KAM.Planetary.SecularForm.Quadratic.Schwarz \
     KAM.Planetary.SecularForm.Quadratic.Uniform
   replaying KAM.Planetary.SecularForm.Quadratic
replaying KAM.Planetary.SecularForm.Quadratic.Calculus
replaying KAM.Planetary.SecularForm.Quadratic.Uniform
replaying KAM.Planetary.SecularForm.Quadratic.PairSplit
replaying KAM.Planetary.SecularForm.Quadratic.Marginal
replaying KAM.Planetary.SecularForm.Quadratic.PairHessian
replaying KAM.Planetary.SecularForm.Quadratic.PairLocal
replaying KAM.Planetary.SecularForm.Quadratic.Constants
replaying KAM.Planetary.SecularForm.Quadratic.Jet
replaying KAM.Planetary.SecularForm.Quadratic.PairIdentify
replaying KAM.Planetary.SecularForm.Quadratic.Algebra
replaying KAM.Planetary.SecularForm.Quadratic.PairDiag
replaying KAM.Planetary.SecularForm.Quadratic.Coeff
replaying KAM.Planetary.SecularForm.Quadratic.Schwarz
   exit 0
   ```

4. Required repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (743 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   exit 1 (only the explicitly permitted generated-root staleness)
   ```

5. Static hygiene: code-mask scan of all fourteen scoped sources found zero `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option`. All fourteen have the copyright, module header, public imports, module docstring and public exposed section. All are below 1500 total lines, hence also below 1500 code lines. The public declaration scan found only the F2 short-name candidate outside scope; there is no fully qualified redeclaration.

6. Import audit: recursively traversed 123 local KAM modules from the fourteen audited modules. No `KAM/Provider` module and no frozen theorem is in the closure. All 55 frozen imports are definition anchors, each `kind=definition`, `state=SEALED` in the manifest. In particular the literal average, physical length and coordinate interfaces are the actual frozen definitions. No DRAFT_SORRY input or conclusion-shaped bundled data occurs.

7. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty stdout, exit 0, apart from the documented multiple-merge-base warning on stderr. `git diff --check`: exit 0. The committed full-branch check `git diff --check inp...HEAD` reports the inherited S8-X whitespace noted in N2; `git diff --check inp...HEAD -- KAM/Planetary/SecularForm/Quadratic.lean KAM/Planetary/SecularForm/Quadratic` exits 0. All fourteen snapshot-v1 source hashes were rechecked and remain unchanged. The existing handoff remains unmodified. The only audit-created repository file is this report; all audit scratch probes, inventories and logs were removed after recording the results. No state-changing git command was used.


## Limits and closeout

This report audits the signed theorem and new helpers against the stated local blueprint obligations. It does not re-audit the internal S8-D/S8-X proofs, certify S9-Q/S9-L, prove a planetary headline, seal a frozen theorem, resolve the external [LR95] provenance gap in isolation, or certify all of Part 8. No source repair or mathematical deviation was introduced. The proved S8-W bypass is acceptable; the unimplemented qf-diag2 ownership change remains a coverage finding.

Closeout: 87/87 new public theorem statements classified and independently queried for axioms; all 15 definitions classified; the probability instance and private helper inspected; signed header identity and fresh polymorphic application probe passed; target build and fourteen-module kernel replay passed; source/module/frozen/ABI checks passed, with the permitted generated-root lint exception. The requested complete node slice is not accepted because F1 remains open. F2 remains a bounded short-name policy/handoff discrepancy; N2 is outside the audit scope. No mathematical repair was authorized or performed.
