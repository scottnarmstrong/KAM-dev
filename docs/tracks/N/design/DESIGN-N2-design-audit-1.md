# Independent audit of DESIGN-N2

Overall verdict: **PASS WITH NOTES**.

This is a refute-first audit of the Part-2 Lean design, not a proof audit or a new theorem seal. No material mathematical, source-fidelity, frozen-object, or consumer defect was found. The two notes concern source coordination and completeness of the departure inventory. No F-series failure is asserted, so no corrected failing signature is required.

## Scope, authority, and immutable inputs

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-design-n2`, branch `inp-design-n2`.

- HEAD: `36c7a857893bf834b88ca2455391e85ccdc2928e`.
- Compared branch `inp`: `a2b5f1c339e197cba1d8b8a982be18318787d086` at inspection. `git diff inp...HEAD` adds only the 505-line design document. The design's recorded historical baseline is not substituted for this comparison.
- Design: `docs/tracks/N/design/N2-LEAN-DESIGN.md`, SHA-256 `42377b6eccc4cac2f9f35feaabd620ea56ded53d38052dfbff84ada06eb7a726`.
- Original signatures: `/root/code/KAM-inp/.drafts/design/N2Signatures.lean`, SHA-256 `6f0af532d88555f0dd089b07298270823eecafd6d46efa540eeda7f8ef87a57a`, 195 lines, 25 theorems and two definitions. Appendix A is byte-identical.
- Blueprint: `blueprint-N/parts/p2-qc-zero.tex`, SHA-256 `ed9954f4a8313436ba58be47d1f061022b49cdf3ad04ba72b0c9467412dce73d`.
- Part 0: `blueprint-N/parts/p0-conventions.tex`, SHA-256 `7872daf0bb0ba79e7cb48c79228057e021f432cca2a22d17217ffc1d1c2faaaa`.
- Packet: `docs/graph/N/packets/N-p02.nodes.md`, SHA-256 `1dbcf0bf6eb0fd30bfc9c2b80348b0a6ca97488239b052265c7d41b6935a3446`.

Read the assigned audit brief, AGENTS.md, PLAN.md, DECISIONS.md, and `.drafts/handoff-DESIGN-N2.md`. The user authorized only this report, a scratch signature copy, and disposable probes. No git mutation, production edit, frozen edit, original-signature edit, or source repair is authorized or performed. The focused tier-2 manuscript-audit method is used with a separate adversarial reconsideration pass; no subagents were used. Evidence and findings are consolidated here rather than creating additional ledgers.

The signature draft was copied to `.drafts/scratch/N2Signatures-audit-1.lean`; probes use `.lake/abi-scratch/` and are removed after inspection. Elaboration uses the shared gated build of `/root/code/KAM-inp`. All 36 transitive project imports from the three imported implementation interfaces were checked: their source bytes match this worktree, and none imports a provider. Shared build use is validation infrastructure, not permission to alter either checkout.

## Signature ledger

Names below are in `KAM.Nekhoroshev`. Line numbers refer to the hashed original signature file. Blueprint labels and their corresponding packet records were compared directly, including hypotheses, binders, norms, domains, and conclusions. Every constant here is supplied as data; there are no newly chosen existential constants with hidden dependence.

| Lean name (line) | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `real_hessian_matrix` (26) | `bpN:p2:qc-deriv`, `stepN:p2:qd-sym` | PASS | Literal real second-derivative coordinates, with explicit symmetry/reconstruction receipts. |
| `bordered_map` (31) | `bpN:p2:qc-kernel` | PASS | Correct CLM on the two ordered product carriers, including nonsymmetric matrices. |
| `bordered_map_apply` (40) | `bpN:p2:qc-kernel` | PASS | Exact coordinate formula for the defined map. |
| `qk_eqs` (45) | `stepN:p2:qk-eqs` | PASS | Both equations obtained from zero output; no nondegeneracy needed. |
| `qk_pair` (51) | `stepN:p2:qk-pair` | PASS | Correctly forces v=0 from pairing, nonzero lambda, and quadratic nonvanishing. |
| `qk_scalar` (58) | `stepN:p2:qk-scalar` | PASS | Nonzero frequency then forces u=0; other inputs allow obtaining v=0. |
| `qc_kernel` (65) | `bpN:p2:qc-kernel`, `stepN:p2:qk-bij` | PASS | Trivial kernel and bijectivity, arbitrary A and either nonzero sign of lambda. |
| `n0` (72) | `bpN:p2:n0` | PASS | Equivalent vacuity formulation: QC forces U empty at dimension zero. |
| `qd_first` (81) | `stepN:p2:qd-first` | PASS | Genuine differentiability and exact finite-sum first component. |
| `qd_freq` (86) | `stepN:p2:qd-freq` | PASS | C1 frequency on U plus genuine derivative and correctly oriented evaluation. |
| `qd_sym` (91) | `stepN:p2:qd-sym` | PASS | Symmetry, matrix reconstruction, and quadratic identity are all explicit. |
| `qd_prod` (98) | `stepN:p2:qd-prod` | PASS | Product rule includes both scalar and action contributions. |
| `qc_deriv` (105) | `bpN:p2:qc-deriv` | PASS | HasFDerivAt supplies differentiability and derivative identity; symmetry is supplied by qd_sym. |
| `qb_unpack` (116) | `stepN:p2:qb-unpack` | PASS | Literal frozen QC clauses with dimension consequence and max-norm lower bound. |
| `qb_deriv` (121) | `stepN:p2:qb-deriv` | PASS | Exact derivative CLM; the quadratic identity is supplied by qd_sym. |
| `qb_pos` (126) | `stepN:p2:qb-pos` | PASS | Strict positivity required by kernel consumer; full m-norm lower bound is recoverable from qb_unpack and qd_sym. |
| `qc_bij` (131) | `bpN:p2:qc-bij`, `stepN:p2:qb-concl` | PASS | Exact frozen-shaped pointwise bijectivity, with positive lambda. |
| `zd_zero` (144) | `stepN:p2:zd-zero` | PASS | Complex vanishing, typed real inclusion, and equality on every point of Wdom. |
| `zd_diff` (148) | `stepN:p2:zd-diff` | PASS | HasFDerivAt for the frozen H with the genuine composed derivative on Wdom. |
| `zd_field` (153) | `stepN:p2:zd-field` | PASS | Exact frozen vector-field value, with correct sign and coordinate order. |
| `zero_deriv` (157) | `bpN:p2:zero-deriv` | PASS | All four clauses on the entire enlarged real domain. |
| `z_init` (168) | `stepN:p2:z-init` | PASS | Both affine initial-value and constant-action conclusions, for arbitrary h. |
| `z_ball` (172) | `stepN:p2:z-ball` | PASS | R/2-ball to R-ball inclusion under the exact local premises. |
| `z_h` (174) | `stepN:p2:z-H` | PASS | Smaller-ball membership, Wdom membership, and genuine H differentiability. |
| `z_curve` (180) | `stepN:p2:z-curve` | PASS | Two-sided HasDerivAt, valid without analytic premises for a fixed frequency vector. |
| `z_eq` (183) | `stepN:p2:z-eq` | PASS | Uses the frozen solution predicate with all three required clauses. |
| `zero` (188) | `bpN:p2:zero` | PASS | Exact frozen-shaped initial/solution/constant-action conjunction. |
| Existing `zero_perturbation_core` | `bpN:p0:zero` | PASS | Existing implementation matches the alias record and frozen theorem binders. |
| Existing `isoenergetic_bijective_of_qc` | `bpN:p0:qcthm` | PASS | Existing implementation matches the alias record; derivative/symmetry receipts cover the explicit source formula. |

All **28 graph records** with a Part-2 statement or proof source are covered. Shared declarations/conjuncts cover qk-bij and qb-concl, and the two Part-0 aliases are included. There are no unclassified signatures.

## Refutation and fidelity checks

1. **Nonsymmetric kernel:** pairing the second kernel equation with v gives lambda times the literal double sum equal to zero. The first equation cancels the u term. Thus the nonvanishing assumption forces v=0, and a nonzero frequency coordinate forces u=0. Equal finite dimensions give surjectivity. Neither symmetry, positivity, a norm bound, nor a quantitative inverse is needed. The n=1 case also works when the quadratic hypothesis is vacuous on the perpendicular subspace.
2. **Dropped dimension premise:** nonzero frequency is impossible on Fin 0. Hence dropping n>=1 from the kernel lemma is sound, and no dimension premise has leaked into the analytic results. For n0, QC on an empty set remains possible, exactly consistent with U=empty.
3. **Hessian transpose:** differentiating the i-th frequency yields D2h[v,e_i], whereas the matrix rows use D2h[e_i,e_j]. C2 on an open neighborhood permits Schwarz; qd_sym explicitly provides the required transposition and quadratic expansion. No equality is silently assumed.
4. **Apparent quantitative weakening:** qb_pos alone gives positivity rather than the displayed m-norm lower bound. Attempted refutation: qb_unpack retains the full lower bound in derivative form and qd_sym equates that derivative with the literal quadratic form. Thus the package exports the complete quantitative assertion without an additional mathematical hypothesis. This is a supplied bridge, not a missing source conclusion.
5. **Derivative totality and enlarged domain:** zero-size perturbation yields equality throughout Wdom, not merely at the orbit or inside the R-ball. Wdom is open and the frozen integrable predicate gives C3 on realActionDomain, identified with the (R+s)-ball. These premises give a neighborhood equality and genuine derivative. No argument depends on the arbitrary total fderiv value outside a differentiability locus.
6. **Affine orbit premise drops:** even an arbitrary total h gives a fixed vector frequencyMap h I0; the resulting time curve is affine and has the stated two-sided derivative. This does not assert that this vector is a genuine gradient without analytic premises. z_eq retains those premises and the H-differentiability guard.

## Consumers: PASS

The requested searches for Part-3 references in tracks I/P were performed as well as the relevant Part-2 references. Part-3 ODE APIs are outside this Part-2 signature scope and are not invented or audited as if delivered here.

Searching all I/P parts and N Parts 7, 11 and 12 for Part-2 labels and their result names found one explicit external reference: `blueprint-I/parts/p3-iso-local-charts.tex:415`, which says the N kernel argument **“is not needed.”** No active use of these Part-2 results was found in the specified P or later N consumers. This is a bounded consumer check, not a claim that Part 2 supplies the Part-3 interfaces.

The internal consumers apply directly:

- qb_unpack supplies the open/C2/nonzero-frequency/coercivity inputs; qd_sym converts the Hessian and quadratic form; positive lambda supplies lambda!=0. qc_kernel then has exactly the required real-product carriers, and qb_deriv identifies the CLM.
- zd_zero and zd_diff give the Wdom derivative/field assertions. z_h puts the orbit in that domain; z_curve gives a two-sided derivative. z_eq uses frozen IsSolutionOn with action membership, differentiability of H, and that exact field derivative.
- Existing isoenergetic_bijective_of_qc and zero_perturbation_core have the exact frozen-shaped inputs and outputs. Their reuse does not prove the general matrix lemma or the enlarged-domain result.

No consumer needs a uniform inverse radius, a new solution predicate, or an extra frequency lower bound.

## Frozen objects and new definitions: PASS

Read the frozen FrequencyMap, HamiltonianVectorField, RealHamiltonian, RealPart, IsStrictlyQuasiConvex, IsSolutionOn, IntegrableOrbit, IsAnalyticIntegrable, IsAnalyticPerturbation, ActionBall, RealActionDomain and ComplexDomain definitions, both frozen theorem anchors, and the Iso IsHamiltonianSolutionOn predicate. The latter is not used as a substitute in the Part-2 signatures.

The signatures use the actual frozen objects. Wdom and Data reuse existing Part-1 declarations. The two new definitions are explicit constructions on their whole carriers: a coordinate second derivative and a finite-dimensional CLM. No new structure/class, conclusion-shaped field, bare-function/matrix global instance, parallel dynamics definition, or junk-value argument is introduced. The kernel input is the source's quadratic nonvanishing premise, not an assumed injectivity conclusion.

## Packages: PASS

The five planned modules form the stated acyclic order: Kernel then Derivative then QCResults; independently ZeroField then ZeroOrbit. Existing QuasiConvex and ZeroPerturbation do not import the new modules. No provider or draft theorem anchor occurs in the transitive imported implementation closure.

The five estimates are 250–400, 250–450, 150–250, 200–350 and 150–250 lines, all below 1500. The n0 declaration is assigned to QCResults even though it appears earlier in the combined scratch file; it is not a prerequisite of Kernel. No new production module was authored, so the targeted compile check is signature elaboration, not a production-module build or a library rebuild.

## Numbered findings and proposed fixes

### N1 — LOW: stale upstream Track-I dependency wording

At the hashed Part-2 blueprint lines 5–6, the kernel is described as **“cited by track I as the isoenergetic gate”**. The current Track-I Part 3 line 415 explicitly says its nonsingular-derivative argument **“is not needed.”** The design already identifies this inconsistency in its consumer discussion and issue 2.

Refutation attempt: searched the specified consumer parts for another active Part-2 use; none was found. The inconsistency survives as upstream coordination text, not an unusable Lean signature.

Proposed fix: in a separately authorized blueprint update, describe the kernel as available infrastructure and remove the claim of an active I gate dependency. No signature change is needed; this does not block prover packages.

### N2 — LOW: departure inventory omits some harmless premise drops

The design's departure table explicitly lists the dimension drop, qk_pair's nonzero-frequency drop and affine-orbit drops. Comparison with the packet also shows qk_eqs does not need any kernel nondegeneracy assumptions; qb_deriv holds for arbitrary real lambda; qb_pos has no lambda parameter at all. These strengthenings are sound but are not all named in the departure inventory.

Refutation attempt: checked whether any omitted condition was needed. Kernel equations follow solely from the CLM application formula; derivative identification is valid even at lambda=0; quadratic positivity depends on QC and perpendicularity, not lambda. No false or unprovable strengthening results.

Proposed fix: expand D-N2-1/D-N2-2 or add one departure row naming these local omissions and their reasons. Keep the signatures unchanged. This is documentation completeness, not a material contract failure.

## Verification receipts

1. **Exact signature elaboration, run once on the unchanged copy:**

   `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n2 .drafts/scratch/N2Signatures-audit-1.lean`

   The gate invokes `LEAN_NUM_THREADS=1 nice -n 5 timeout 1800 lake env lean <absolute-copy-path>` against the shared inp build. Exit **0**, exactly **25** “declaration uses `sorry`” warnings, no errors or other Lean diagnostics. Gate slot 3 was acquired at 05:07:08 UTC.

2. **API, binder, and bridge probe:** same gate on `.lake/abi-scratch/N2AuditProbe.lean`, after the signature process had completed. Exit **0**, the expected 25 draft warnings, all requested `#check` and `#print axioms` outputs, and no error. Gate slot 3 was acquired at 05:12:22 UTC.

   The probe checked all 17 named Mathlib dependencies: `Prod.mk_eq_zero`, `ContDiffOn.fderiv_of_isOpen`, `ContinuousLinearMap.apply`, `hasFDerivAt_pi`, `ContDiffAt.isSymmSndFDerivAt`, `HasFDerivAt.smul`, `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`, `HasFDerivAt.comp`, `Filter.EventuallyEq.fderiv_eq`, `hasDerivAt_id'`, `HasDerivAt.smul_const`, `HasDerivAt.const_add`, `HasDerivAt.prodMk`, `hasDerivAt_const`, `Subsingleton.elim`, `norm_pos_iff`, and `HasFDerivAt.fderiv`. The two helper definitions additionally elaborate their CLM constructors and operations.

   In particular, the actual Schwarz API takes `ContDiffAt` and `minSmoothness 𝕜 2 ≤ n`; for the real C2 use this is the required order-two guard. The finite-dimensional theorem takes equality of finranks and gives injectivity iff surjectivity for the given linear map. The derivative-regularity API requires openness and `m+1 ≤ n`, satisfied with m=1 and n=2.

   Five Part-1 interface types and six critical elaborated draft binder lists were also checked. Open/C2/membership assumptions survive on qc_deriv and qd_freq. All four analytic/radius premises survive on zero_deriv; z_init and z_curve have only affine-orbit data; z_ball has only n,R,hR,I0,hI.

   This proof in the probe successfully recovers the complete quantitative source assertion from the delivered signatures:

   ```lean
   example {n : ℕ} {U : Set (Fin n → ℝ)} {h : (Fin n → ℂ) → ℂ} {m : ℝ}
       (hqc : IsStrictlyQuasiConvex U h m) {I : Fin n → ℝ} (hI : I ∈ U)
       (v : Fin n → ℝ) (hv : (∑ i, KAM.frequencyMap h I i * v i) = 0) :
       m * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, v i * real_hessian_matrix h I i j * v j := by
     obtain ⟨hm, hU, hh, hf, hn, hb⟩ := qb_unpack hqc hI
     rw [(qd_sym hU hh hI).2.2 v]
     exact hb v hv
   ```

   A separate example applied `isoenergetic_bijective_of_qc hqc hI hlam` to the exact target; another proved the frozen frequency/realPart identification by `rfl`. These are interface checks using the draft results, not proofs of those results.

   Fresh axiom outputs:

   | Result | Axioms |
   |---|---|
   | Draft qc_kernel, qc_deriv, zero_deriv | `propext`, `sorryAx`, `Classical.choice`, `Quot.sound` |
   | Existing isoenergetic_bijective_of_qc, zero_perturbation_core | `propext`, `Classical.choice`, `Quot.sound` |

3. **Source lint:**

   `N2_ORIGINAL_PATH="$PATH" PATH="$PWD/.drafts/scratch/bin:$PATH" LEAN_NUM_THREADS=1 scripts/lint_sources.sh`

   Used the designer's existing PATH adapter, inspected before use; no wrapper or lint script was edited. Its ABI Lean invocation restores the original PATH inside the same signature gate. This invocation started only after the API probe finished. Exit **0**, with output:

   ```text
   check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

4. **Mechanical checks:** appendix equality PASS; 28 Part-2 graph records covered; 25 theorem signatures and two explicit definitions; `git diff --check inp...HEAD` exited 0. Final integrity check PASS: all five hashed audit inputs are unchanged, report whitespace passes, `git diff --check` exits 0, and `git status --short` lists only `?? docs/tracks/N/design/DESIGN-N2-design-audit-1.md`. The scratch signature copy and the audit probe were deleted; pre-existing designer scratch files were left untouched.

All audit Lean/lake invocations are serial, with one thread and niceness 5. No resource-budget override, production-module build, library rebuild, clean, update, or cache operation was used.

## Limits and closeout

No new theorem body was proved or kernel-replayed. No fresh pinned-BM11 paper audit was performed: this assignment compares the supplied blueprint, packet, frozen definitions and implementation interfaces. No suspected pinned-paper erratum or frozen-statement defect was found. The two notes above are blueprint/documentation matters. Existing implementation proof audits and quantitative inverse-radius questions are outside scope.

Only this report is a lasting audit deliverable. No change to the design, graph, source, original signatures, providers, manifest, generated root, README, or git history was made.

Closeout: all 27 new declarations and both existing alias interfaces classified; all 28 graph records covered; signature elaboration, API/bridge checks, axiom inspection, source lint and integrity checks complete. No material failure or unresolved tentative blocker remains. N1 and N2 are nonblocking documentation notes.
