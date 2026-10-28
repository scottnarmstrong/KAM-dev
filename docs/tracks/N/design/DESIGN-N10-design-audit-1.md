# Independent design audit: N10, round 1

Overall verdict: **PASS WITH NOTES**.

No material false signature, extra source premise, widened constant dependence, weakened final conclusion, or frozen-object substitution was found. This is approval of the design statements, subject to the explicitly deferred Part 9 interface reconciliation; it is not proof closure or permission to seal an anchor. The user-requested verdict spelling is used here (the generic brief instead offers “PASS WITH FIXES”). There are no FAIL findings and therefore no corrected failing signatures.

## Scope and authority

Audited `docs/tracks/N/design/N10-LEAN-DESIGN.md` on `inp-design-n10` at `4d868ce` (comparison branch `inp` at `f21b16a`), the canonical `/root/code/KAM-inp/.drafts/design/N10Signatures.lean`, and `.drafts/handoff-DESIGN-N10.md`. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the audit brief, and the N10/common designer briefs. `git diff inp...HEAD` contains only the 530-line design addition. No state-changing git operation was used.

Compared directly with `blueprint-N/parts/p10-assembly.tex`, relevant Part 0 and Part 9 statements, `docs/graph/N/packets/N-p910.nodes.md`, and the frozen-root record in `N-p02.nodes.md`. All 36 Part 10 nodes and the Part 0 root have design mappings. Proof-step nodes are checked through their enclosing declarations and helpers rather than treated as independent assumptions.

The canonical signatures SHA-256 is `22021dd133e9ee9b787f52fae98bed1f544f960de5a83ec3ba891c62fb413bfe`. Independently checked: Appendix A is byte-identical to that file; the provider telescope, from its first binder through its result, is byte-identical to the frozen telescope. The file has eight definitions and 22 theorem signatures, 254 lines.

## Signature-by-signature verdicts

Names below are in `KAM.Nekhoroshev`, except the explicitly qualified provider. Line numbers refer to the canonical signatures file. Each row judges the declaration in the documented multi-lemma realization of its blueprint node; in particular `hypotheses_check` is explicitly an analytic component, not a claim that its conjunction alone contains all eight blueprint clauses.

| Lean name (line) | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `HeadParams.s1` (30) | `bpN:p10:choice` | PASS | Exactly geometric width `s/2`. |
| `HeadParams.F1` (31) | `bpN:p10:choice` | PASS | Exactly `coth(pi*s/4)^n`; uses the existing coth. |
| `HeadParams.eps1` (32) | `bpN:p10:choice` | PASS | Exactly `mu*r0^2/(2^10*A^(2*n))`, unscaled. |
| `HeadParams.R0` (33) | `bpN:p10:choice` | PASS | Exactly `r0/A`. |
| `HeadParams.epsPrime` (34) | `bpN:p10:choice` | PASS | Exactly `F1*epsilon`; no perturbation-dependent choice. |
| `HeadParams.tau` (35) | `bpN:p10:confinement` | PASS | Exactly `T*exp(c*epsilon^(-1/(2*n)))`. |
| `HeadParams.rho` (37) | `bpN:p10:confinement` | PASS | Exactly `C*epsilon^(1/(2*n))`. |
| `choice` (40) | `bpN:p10:choice` | PASS | Packs four existing constants of the seven data only. |
| `choice_props` (43) | `bpN:p10:choice-props` (a),(b) | PASS | Positivity, margin and radius inequalities match; `A=11B/mu` and the `R0` identity are already definitions. |
| `cp_dict` (51) | `stepN:p10:cp-dict` | PASS | Both `2*pi` identities, unrestricted epsilon equivalence, and positive-smallness implication match. |
| `cp_rad` (57) | `stepN:p10:cp-rad` | PASS | Preserves the half-radius and the exact exponent, for positive epsilon. |
| `cp_size` (62) | `stepN:p10:cp-size`, `stepN:p10:ex-rho` | PASS | Correct monotonicity consequence; adds valid radius/time positivity. |
| `hc_tubes` (67) | `stepN:p10:hc-tubes` | PASS | Correct complex tube inclusion and real inclusions through `5R/8`, nonemptiness, and initial membership. Product-domain inclusion follows directly. |
| `hc_h` (75) | `stepN:p10:hc-h` | PASS | Holomorphy/reality and Euclidean matrix-action Hessian bound are the intended clauses. The latter is exactly the operator estimate without a new norm instance. |
| `hc_qc` (84) | `stepN:p10:hc-qc` | PASS | Correct conic premise with `ell`, Euclidean curvature `mu`, and existing real Hessian; applies only on the real preimage of the smaller tube. |
| `hc_f` (91) | `stepN:p10:hc-f` | PASS | Existing class, reality and summable weighted bound at `s1`; epsilon positivity/smallness is separately supplied by `cp_dict`. |
| `hc_exc` (99) | `stepN:p10:hc-exc` | PASS | Strict exclusion follows from `mu*r0/8 <= wmin/2 < wmin`; lower bound changes max to Euclidean in the valid direction. |
| `hc_time` (105) | `stepN:p10:hc-time` | PASS | Pointwise frequency bound on the Euclidean closed ball of radius `R0`. Its max-norm containment in the real derivative domain follows from `R0 <= R/176`. |
| `head_time_prefactor` (111) | `stepN:p10:hc-time` | PASS | Positive scalar maximum bounded by `sqrt(n)*M` suffices for `2T <= A^2*s1/Omega`. No orbital conclusion is assumed. |
| `head_field_locality` (116) | `stepN:p10:hc-field` | PASS | Equality of Hamiltonian values on the open real tube implies equality of frozen total fields there. No differentiability premise is needed for equality of total fderiv at locally equal functions. |
| `hypotheses_check` (125) | `bpN:p10:hypotheses-check` | PASS | Analytic conjunction plus the existing ODE `Data`; the remaining clauses are assigned to named helpers and the pending setting construction. See N1. |
| `cf_orbit` (144) | `stepN:p10:cf-orbit` | PASS | Direct projection of the genuine frozen two-sided derivative clause on arbitrary time sets. Initial action and field equality are supplied elsewhere. |
| `cf_branch` (150) | `stepN:p10:cf-branch` | PASS | Correct concrete specialization of Part 9(a), retaining tube membership and the half-radius bound. Uniform `2T` is a justified shorter time, with no prior tube-confinement premise. |
| `confinement` (163) | `bpN:p10:confinement` | PASS | Any OrdConnected interval containing zero, frozen source solution, exact headline radius/time, endpoints included. |
| `ex_ball` (173) | `stepN:p10:ex-ball` | PASS | Closed max ball fits strictly in the open action ball from `norm I0 < R/2` and `rho <= R/4`. |
| `existence` (177) | `bpN:p10:existence` | PASS | Initial value, genuine closed-interval solution and uniform displacement are exactly the three source conclusions. |
| `head_solution_restrict` (187) | `stepN:p10:un-restrict` | PASS | `L <= tau` gives time-set containment; negative L yields an empty smaller interval and does not invalidate the stronger helper. |
| `uniqueness` (193) | `bpN:p10:uniqueness` | PASS | Valid strengthening to analytic ODE Data and arbitrary tau; keeps common initial value, `0 <= L`, `L <= tau`, genuine solutions and EqOn. Includes L=0. |
| `head` (203) | `bpN:p10:head` | PASS | Preserves H1–H7, chosen constants, one exhibited z, drift and comparison with every competing solution. Positivity and margin remain in `choice_props`, used by provider. |
| `KAM.Provider.Nekhoroshev.quasiConvex_nekhoroshev_complexBound` (226) | `bpN:p0:head` | PASS | Literal frozen telescope, including binder order, all quantifiers, max norms, closed intervals and uniqueness. |

## Fidelity and applicability checks

The existing `HeadParams`, `.Pos`, `HeadHyp`, `centralSet` and constants are reused. In particular `HeadHyp` is exactly H1–H5 in order. The six real fields plus n determine every chosen constant before h, f or epsilon is introduced. The existential bound on h in `IsAnalyticIntegrable` is never used to choose those constants. Existence of an orbit may depend on h and f as intended.

For period one, `epsStar=2*pi*eps1`, `F=2*pi*F1`; cancelling these positive factors gives both `cp_rad` equalities. The time prefactor also checks directly: `T=A^2*s/(4*n*M)`, `s1=s/2`, and `sqrt(n)<=n`, hence `2T=A^2*s/(2*n*M)<=A^2*s1/Omega` for `0<Omega<=sqrt(n)*M`. This does not identify the scaled Part 1 maximum with the unscaled Part 9 maximum.

Dropped hypotheses were checked individually. `hc_f` needs neither positive epsilon nor its smallness to establish class/reality/WBound: the frozen perturbation predicate already supplies `0<=epsilon`; positivity and upper cutoff enter only later. `head_field_locality` needs neither positivity of p nor analytic hypotheses, since its real tube is open for any radius, including an empty tube. Restriction needs no positivity assumptions. For uniqueness, dimension, QC, special tau, epsilon smallness and confinement are unnecessary under the existing smooth analytic ODE Data. These are true strengthened helpers, not substitutions of conditional stability for the source theorem.

**Consumer verdict: PASS for the scoped assembly.** The direct consumers are `cf_branch -> confinement -> existence -> head -> provider`, with restriction/uniqueness feeding the last two stages. Existing `ODE.confinement_glue` accepts precisely `Data`, an open action set contained in `ball 0 (R+s)`, positive tau/rho, the closed action ball inclusion, and an a-priori estimate for every open OrdConnected interval through zero. All are supplied with the same frozen Hamiltonian and max-norm product carrier. The extra comparison conclusion of glue may be discarded. `ODE.uniqueness_closed` has the exact two frozen solution predicates and common initial value used by the proposed uniqueness proof; it needs no confinement of the competitor.

The requested cross-track search for `\Nref{bpN:p3:` was performed in I/P, and the analogous references in N Parts 7, 11 and 12 were read. Those references consume the general Part 3 layer, not these Part 10 specializations. In particular I Part 5 uses general barrier/energy/periodic continuation and I Part 7 the Newton/restricted reduction; P Parts 6, 11b and 14 use general reduction/continuation/uniqueness; N Part 7 uses general stopped transfer and energy, N Part 11 mixed-dimension continuation, and N Part 12 general maximal flow/first exit. None can be replaced by the more specialized N10 theorem, and the design does not propose that replacement. A search for `bpN:p10:` in those consumer files has no matches. The cited general APIs and their ownership remain unchanged. This audit does not certify all of Part 3 or the separate consumer designs.

**Frozen-object verdict: PASS.** Read the frozen `IsSolutionOn`, `realHamiltonian`, `hamiltonianVectorField`, `frequencyMap`, `ActionBall`, `RealActionDomain`, `IsAnalyticIntegrable`, `IsAnalyticPerturbation`, `HasComplexHessianBound`, `HasDerivativeBounds`, `IsStrictlyQuasiConvex` and root theorem. No parallel predicate or vector field is introduced. `cf_orbit` preserves the two-sided `HasDerivAt` clause; the final solution retains action membership and differentiability of H at visited points. The locality helper is a bridge to the actual frozen field rather than an assumed equality of fields. No frozen defect was found.

**Definition verdict: PASS.** New definitions are the intended numerical quantities on their full carriers, with no global instances or structures. Real division/rpow are total, but positivity and dimension are supplied at every theorem needing their ordinary positive interpretation. Existing `WBound` includes summability pointwise on the action tube, so no proof relies on junk values of a divergent tsum or unbounded supremum. `Canonical.RealOn`, `Weighted.InClass` and geometric `Dom` are the existing objects.

**Package verdict: PASS WITH NOTES.** Five waves have an acyclic import plan and six exact production paths; estimates are 220/350/250/200/150/90 lines. The provider namespace/path agrees with the actual frozen import. There is no planned import of a provider or DRAFT_SORRY anchor into an implementation module. Part 9 ports and the missing built ODE specialization are accurately identified as pending rather than silently recreated. See N1 and N3.

## Numbered findings and proposed fixes

**N1 — Moderate, explicit reconciliation gate; non-blocking for this design review.** Design lines 112–121 and 233–236 leave `setting`, `omega0` and `thm1` as Part 9 ports. This is expressly permitted by DESIGN-COMMON for an undelivered neighbouring part. The current helper family supplies the mathematical inputs needed by blueprint Part 9; it does not yet supply an elaborated constructor application or a maximum specification. In particular `hc_time` alone bounds pointwise frequencies, and bounding the actual Omega0 requires its maximum/attainment specification. Proposed follow-up: before dispatching N10-3, reconcile the delivered Part 9 carrier, real-set embedding, exact constant definitions, field-value extension, max specification and stopped theorem against the table, and elaborate their concrete application. Do not turn `cf_branch`, a max bound, or tube confinement into an added premise. No current signature replacement is required.

**N2 — Low, consumer documentation.** The design has a good internal consumer map but no explicit negative cross-track inventory. The audit brief requests the I/P and N7/11/12 survey because the Part 3 general APIs have substantially wider applicability than N10. Proposed documentation fix: add the consumer distinction recorded above, explicitly saying N10 is a specialized assembly and does not replace the generic ODE layer. No mathematical or Lean signature change is needed.

**N3 — Low, validation boundary.** The signatures deliberately omit `ODE.Specialization`, whose shared olean is reported absent. Source inspection confirms both named ODE signatures and their applicability, but successful standalone signature elaboration does not test those imports or the future package split. Proposed follow-up: when the upstream build is available, run the targeted N10-4 build with the real imports and subsequently the provider build; inspect axioms before sealing. Do not represent this design check as either build or proof closure.

## Checks and limits

1. Canonical signature elaboration, run once through the mandated wrapper:

   ```sh
   /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n10 .drafts/scratch/N10Signatures.lean
   ```

   Exit 0; gate slot 1 acquired at 05:07:32 UTC; exactly 22 “warning: declaration uses `sorry`” messages, at the 22 theorem declarations, and no other Lean diagnostics. The scratch copy was byte-identical to the canonical file before and after the run. No production module was authored, so this is the targeted design elaboration rather than a `lake build` receipt.

2. `.lake/abi-scratch/n10-audit-probe.lean`, through the same gate, exit 0. All 23 `#check` commands succeeded without warnings/errors. The eight Mathlib declarations are `Real.rpow_le_rpow`, `Real.mul_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.pow_rpow_inv_natCast`, `Real.rpow_neg`, `Real.exp_le_exp` and `Filter.EventuallyEq.fderiv_eq`. Their printed premises give exactly the nonnegativity/nonzero and local-equality requirements used here. In particular `pow_rpow_inv_natCast` needs `n != 0`, derived from the positive dimension, and `fderiv_eq` needs only eventual equality. The other 15 checks cover `Weighted.isOpen_polyNbhd` and the named constants/analytic/QC/Hessian/partial/value bridges. The ODE signatures were read from source; their absent shared olean was independently confirmed.

3. `scripts/lint_sources.sh`, exit 0, with output:

   ```text
   check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   To route its one ABI Lean subprocess through the required gate without editing any script, used a temporary `.lake/abi-scratch/n10-audit-bin/lake` PATH adapter. The invocation was:

   ```sh
   N10_AUDIT_ORIGINAL_PATH="$PATH" PATH="$PWD/.lake/abi-scratch/n10-audit-bin:$PATH" LEAN_NUM_THREADS=1 scripts/lint_sources.sh
   ```

   The adapter accepted only `lake env lean <file>`, restored the original PATH, and invoked `inp_sig_check.sh` on the absolute scratch path. Signature elaboration, declaration probe and lint ran sequentially.

4. Mechanical checks: matching canonical hash, Appendix byte identity, literal frozen telescope identity, 36/36 Part 10 graph mappings, 30/30 signature rows, `git diff --check`, and final `git status --short`. Only the requested report is a persistent worktree addition.

The designer's separate `#print axioms` receipt reports `[propext, sorryAx, Classical.choice, Quot.sound]` for both `head` and the provider. This audit does not claim an independent axioms rerun or a proved main result: every proposed theorem body remains `sorry`, and its successful elaboration cannot establish the theorem. An actual provider must eliminate `sorryAx`; the intended final axioms are only `propext`, `Classical.choice`, `Quot.sound`.

All auditor Lean invocations, including lint's ABI subprocess, are serialized through `inp_sig_check.sh`, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The gate uses the shared inp build; there was no direct build, cache command, cleanup of build artifacts or heartbeat override.

The only persistent authored file is this report. The original signatures, design, frozen files, manifests, source blueprints, graph and handoff are unchanged. Temporary signature-copy/probe/adapter files are removed after validation.

## Errata, deviations and uncertainties

No new pinned-source defect is asserted. The design's inherited Pos93 reports (p.190/p.204 radius condition and the max/l1 cutoff adaptation) were compared with blueprint Part 9's disclosed deviations, not independently checked against the PDF; their source-verification status is unchanged. Part 10's “adds no analysis” sentence is optimistic assembly prose, and the local-field/max obligations are correctly exposed by the design. The scaled/unscaled Omega0 issue is handled by a separate correct arithmetic helper.

The uncertainty is delivery of the Part 9 interfaces and eventual proof elaboration at default heartbeats. There is no heartbeat/resource override, production Lean edit, build-from-scratch, source repair or frozen-statement change in this audit. The scratch copy is the explicit user-authorized exception to the report-only rule; other probes live under `.lake/abi-scratch/` and are deleted.
