# DESIGN-N12 independent design audit 1

Overall verdict: **FAIL** — one medium-severity source-contract omission (F1). Both provider exports match their frozen targets and the submitted signatures elaborate. This verdict does not assert that either averaging theorem is false. Restore the omitted derivative-series conclusion before dispatching these exact signatures as complete implementations of their blueprint contracts.

## Scope and frozen inputs

Focused, refute-first design/source audit, 2026-10-28. Permission envelope: this report only, the explicitly requested signatures copy, and temporary probes under `.lake/abi-scratch/`. No production, frozen, manifest, generated, source, or git-history changes. No delegation. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied audit brief and designer handoff. Applied the manuscript-audit methodology, including a separate adversarial reconsideration pass; no second-agent review is claimed.

Snapshot `frozen-v1`:

| Input | Revision / SHA-256 |
|---|---|
| Worktree HEAD | `8cf4eb8b5e8cafbd222ea027dc6f4b221906016b` |
| `inp` at comparison | `90cb224ec5c0651eb8ad9009c11dae256607bb02` |
| `N12-LEAN-DESIGN.md` | `eecbdc8e536536de93261108c9d3eaad7e36ee36c9a0b4cf99c31ccd96ad82cc` |
| Original `N12Signatures.lean` | `849a21ec5d85a33354061d2c503c5990d0c23f824b9fb0e05c40ecdcc3e9c6e9` |
| `blueprint-N/parts/p12-averaging.tex` | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |
| `docs/graph/N/packets/N-p12.nodes.md` | `2994dff658689fa1b5ad4a4d3908f26ac6369868106683874a85f1c7e44aad4d` |
| `docs/graph/N/DEPGRAPH.md` | `941c8d1d4bb6c17e3369d57b86441798544e1dabc8a9af1735882f75aa8972d2` |

`git diff inp...HEAD` contains exactly the new 939-line design document. Appendix A equals the original 500-line signatures file byte for byte. All 91 packet records with a Part 12 statement or proof locator have design-table rows. Coverage is structural evidence, not proof closure.

Below, new names belong to `KAM.Nekhoroshev`; `Provider.*` means `KAM.Provider.Nekhoroshev.*`. Labels abbreviate `bpN:p12:*` unless otherwise specified. PASS may use an explicitly identified existing-library or definitional bridge.

## Theorem signatures (29)

| Lean name | Blueprint label / graph contract | Verdict | Reason |
|---|---|---|---|
| `fbounds` | `fbounds` | PASS | Correct real max-norm bounds and field identity; the imported HoloReal API bridges real and complex partials, as explained below. |
| `averaged` | `averaged` | PASS | Unit-cube slow-field integral is zero; constant averaged solution and collar are elementary consequences. |
| `avgMaximal_spec` | `s-flow#data` | PASS | Existing maximal predicate, EReal endpoints, frozen field. |
| `ext_dep` | `ext-dep` and six subnodes | PASS | Only C1 input; local flow, genuine derivatives and Volterra equation are conclusions. |
| `compact_max` | `ext-markov#compact-max` | PASS | Joint continuity on a nonempty compact time interval; T=0 is a valid strengthening. Variable-time form follows by u=v*t on the domain subtype. |
| `flow` | `flow` | PASS | Openness, continuity, C1 slices, inverse, determinant and translation. Applying inverse clauses at -t supplies surjectivity and the other inverse. |
| `flow_variational` | `flow` (b) | PASS | Actual two-sided time derivative of the initial derivative; initial identity follows from maximal initial values. |
| `exit` | `exit` | PASS | EReal exit, finite exit before maximal endpoint, boundary hit and relative openness. |
| `coef` | `coef` | PASS | Exact tube, complex derivatives, decay, absolute series and polynomial-weight summability. Zero slow coefficient follows also from averaged. |
| `corrector` | `corrector` | PASS | Rational bounds match; inverse bounds exclude y=0. Dropping κ≤1 is valid here. |
| `wreg` | `wreg` | **FAIL** | F1: the promised termwise derivative equalities are omitted; other displayed estimates match. |
| `envelope_regular` | `corrector`, p12:109 | PASS | Measurable zero extensions and finite envelopes on the valid domain. |
| `«lambda»` | `lambda` | PASS | Transposed differential and Euclidean scalar gauge; no frequency lower bound. |
| `slab` | `slab` | PASS | Both direction-uniform and integer-mode bounds, including Euclidean denominator. |
| `shells_from_slab` | `shells`, conditional helper | PASS | Distinct conditional name; exact four bounds and constants. Ω₀≥0 follows from the norm bound on nonempty G. |
| `shells` | `shells` | PASS | Constructs constants before κ and mode; no added source premise. |
| `envelopes_from_slab` | `envelopes`, conditional helper | PASS | Exact cW,cB,cR,cPhi, including sqrt n and 2π. |
| `envelopes` | `envelopes` | PASS | Derived witnesses and all κ=sqrt ε bounds. |
| `identity` | `identity` | PASS | Correct signs and ε powers in the complex inclusion. Trajectory C1 follows from wreg and the solution law; dropping κ≤1 is valid. |
| `pointwise` | `pointwise` | PASS | Simultaneous all-u bound is equivalent to the compact maximum estimate; correct trajectory guards. |
| `transport` | `transport` | PASS | One half-open initial cell, full domain guards, unnormalised volume, no angle-drift factor. |
| `stopped` | `stopped` | PASS | Witnesses precede all size-one f₁ and ε; controls every time up to the stop. Explicit witness construction remains a proof obligation. |
| `good` | `good` | PASS | Relative openness and measurable bad set; general η and ε>0 are valid strengthenings. |
| `bad` | `bad` | PASS | Re-derives witnesses; threshold and good-data bounds suffice for assemblies. |
| `mean_family` | `stepN:p12:me-flow`, `me-cont`, p0:`avg-totality` | PASS | Equality with genuine flow, continuity/integrability on K, true maximum, nonnegativity and 3R/2 bound. |
| `averaging_mean_core` | `bpN:p0:avg-mean` and `me-*` | PASS | Exact frozen error and Markov conclusion; fixed ε₀=1 strengthening. |
| `averaging_most_core` | `bpN:p0:avg-most` and `mo-*` | PASS | Full-window solution is a conclusion; fixed ε₀=1, η₀=R/8 strengthening. |
| `Provider.averaging_mean` | `bpN:p0:avg-mean` | PASS | Telescope and conclusion are exact textual frozen copies. |
| `Provider.averaging_most` | `bpN:p0:avg-most` | PASS | Telescope and conclusion are exact textual frozen copies. |

## Definitions and structures (42)

Every declaration has a row. There is no global instance on bare function or matrix types.

| Lean name | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `AvgPhase` | `s-setting#data` | PASS | Real Pi product, angles first. |
| `AvgComplexPhase` | `s-setting#data` | PASS | Matching complex Pi product. |
| `AveragingData` | `s-setting#data` | PASS | Only source typing, positivity, analytic and rank premises. |
| `avgDomain` | `s-setting#data` | PASS | univ times actionBall R. |
| `avgG` | `s-setting#data` | PASS | Closed max-norm ball 3R/4. |
| `avgH` | `s-setting#data` | PASS | Frozen realHamiltonian with ε*f. |
| `avgA` | `fbounds` | PASS | Negative real angle partials. |
| `avgB` | `fbounds` | PASS | Real action partials. |
| `avgM` | `s-setting#data` | PASS | Entry i,j of real frequency differential. |
| `avgMaximal` | `s-flow#data` | PASS | Chooses existing maximal predicate; fallback is guarded. |
| `avgTm` | `s-flow#data` | PASS | Left EReal endpoint. |
| `avgTp` | `s-flow#data` | PASS | Right EReal endpoint. |
| `avgFlow` | `s-flow#data` | PASS | Chosen trajectory; assertions are domain-guarded. |
| `avgFlowDomain` | `s-flow#data` | PASS | Initial membership and eIoo time membership. |
| `avgOmega` | `s-flow#data` | PASS | Exact time section. |
| `avgStay` | `exit` | PASS | Strict displacement bound over the whole earlier interval. |
| `avgTau` | `exit` | PASS | EReal supremum supports infinite exit time. |
| `avgCoeff` | `s-data#data` | PASS | Existing Weighted.coeff. |
| `avgBeta` | `s-data#data` | PASS | exp(-π*s*modeSize). |
| `avgQ` | `s-data#data` | PASS | Mode dot frozen frequency. |
| `avgPsi` | `corrector` | PASS | Exact rational divisor; κ>0 at use. |
| `avgPsiD` | `corrector` | PASS | Exact rational derivative. |
| `avgU` | `corrector` | PASS | Complex coefficient times divisor and mode. |
| `avgW` | `corrector` | PASS | Negative character-weighted sum; zero mode vanishes. |
| `avgWenv` | `corrector` | PASS | Exact ENNReal envelope. |
| `avgW1env` | `corrector` | PASS | Exact 2π and modeSize weight. |
| `avgBterm` | `corrector` | PASS | Exact 2n/s and M₂*modeSize weights. |
| `avgBenv` | `corrector` | PASS | ENNReal sum of b_k. |
| `avgRenv` | `corrector` | PASS | Exact residual envelope. |
| `avgPhiEnv` | `corrector` | PASS | ε*4/s B + ε*2/s W1 + R. |
| `avgResidual` | `corrector` | PASS | Inclusion of a minus angle derivative along frequency. |
| `AvgSlabBound` | `slab` | PASS | Derived numerical specification, not a standing premise. |
| `avgLog` | `p12:163 notation` | PASS | 1+log(1/κ), used with 0<κ≤1. |
| `avgSigma` | `coef` | PASS | Excludes zero; summability paid by coef. |
| `avgCW` | `envelopes` | PASS | Exact cW. |
| `avgCB` | `envelopes` | PASS | Exact cB including sqrt n. |
| `avgCR` | `envelopes` | PASS | Exact cR including 10π. |
| `avgCPhi` | `envelopes` | PASS | Exact cPhi including 8π/s. |
| `avgCorrectionQ` | `identity` | PASS | Both real directional derivatives, complex target. |
| `avgCell` | `s-trans#data` | PASS | Half-open angle cell, free actions. |
| `avgStopped` | `s-trans#psi` | PASS | ENNReal integral killed outside stay set. |
| `avgGood` | `good` | PASS | Full-time domain guard and strict genuine maximum. |

## Findings and proposed fixes

### F1 — MEDIUM, blocking source fidelity: wreg loses termwise derivatives

At frozen-v1 `blueprint-N/parts/p12-averaging.tex:113` the source says “the function w is C1, 1-periodic in θ, **with termwise derivatives**”. The packet `N-p12.nodes.md:1069` repeats “with termwise derivatives”; p12:122 identifies the angle derivatives with the differentiated series. Design package N12-06 promises “exact residual series and termwise derivative formulas”.

Submitted signatures:228–248 provide C1 regularity, periodicity, a residual series and derivative **bounds**, but no equality between a derivative of `avgW` and the termwise differentiated sum. The residual series identifies a contraction along ω, not the full angle or action derivative. Proving exactly this signature therefore does not deliver the full assigned source conclusion.

Adversarial reconsideration: the imported generic `hasFDerivAt_tsum_of_isPreconnected` can prove the missing result once local domination is established. It does not already instantiate that result for this corrector. The package prose assigns these steps, and the downstream norm-only applications can still work, so this is an omitted source conclusion, not a counterexample to either root. Nevertheless the brief explicitly requires FAIL for a weakened conclusion. No named corrector-specific bridge in the aggregate restores it.

Proposed fix: preserve all current bounds and add this directional derivative-series conjunct on the full source domain. Alternatively export the added conjunct separately and map the source node to both results. Full corrected signature:

```lean
theorem wreg (d : AveragingData n R s h f) {M₂ κ : ℝ} (hκ : 0 < κ)
    (hM : ∀ I ∈ closedBall (0 : Fin n → ℝ) R,
      ∀ i, ∑ j, |avgM h I i j| ≤ M₂) :
    ContDiffOn ℝ 1 (avgW h f κ) (avgDomain n R) ∧
    (∀ z ∈ avgDomain n R, ∀ v : AvgPhase n,
      HasSum (fun k : Fin n → ℤ =>
        fderiv ℝ (fun y : AvgPhase n =>
          -KAM.character k (KAM.realInclusion n y.1) • avgU h f κ k y.2) z v)
        (fderiv ℝ (avgW h f κ) z v)) ∧
    ∀ z ∈ avgDomain n R,
      (∀ k : Fin n → ℤ, avgW h f κ (z + KAM.ODE.angleShift k) = avgW h f κ z) ∧
      (z.2 ∈ avgG n R →
        ENNReal.ofReal ‖avgW h f κ z‖ ≤ avgWenv h s κ z.2 ∧
        ENNReal.ofReal ‖avgResidual h f κ z‖ ≤ avgRenv h s κ z.2 ∧
        HasSum (fun k : Fin n → ℤ => fun j =>
          -2 * (Real.pi : ℂ) * Complex.I * avgCoeff f (KAM.realInclusion n z.2) k *
            ((κ ^ 2 / (avgQ h k z.2 ^ 2 + κ ^ 2) : ℝ) : ℂ) * (k j : ℂ) *
              KAM.character k (KAM.realInclusion n z.1)) (avgResidual h f κ z) ∧
        (∀ v : Fin n → ℝ,
          ENNReal.ofReal ‖fderiv ℝ (avgW h f κ) z (v, 0)‖ ≤
            avgW1env h s κ z.2 * ENNReal.ofReal ‖v‖) ∧
        (∀ v : Fin n → ℝ,
          ENNReal.ofReal ‖fderiv ℝ (avgW h f κ) z (0, v)‖ ≤
            avgBenv h s M₂ κ z.2 * ENNReal.ofReal ‖v‖) ∧
        ∀ k : Fin n → ℤ, ∀ v : Fin n → ℝ,
          ‖fderiv ℝ (avgU h f κ k) z.2 v‖ ≤ avgBterm h s M₂ κ k z.2 * ‖v‖) := sorry
```

The summands differentiate the actual negative Fourier terms over ℝ. Choosing v=(vθ,0) or (0,vI) recovers both partial derivative series. The zero-mode derivative vanishes. This changes no source premise or frozen statement.

### N1 — LOW: accurately identify the graph hash

Design:414–415 calls `941c8d1...` the “graph packet SHA-256”. That is the hash of `docs/graph/N/DEPGRAPH.md`; `N-p12.nodes.md` has hash `2994dff6...`. Hashing both files refutes a semantic-drift interpretation: this is a label error. Proposed fix: identify the combined graph path accurately and additionally record the actual packet path/hash.

## Consumer, frozen-object, definition and package verdicts

**Consumers: PASS for applicability; source completeness FAIL at F1.** Searched the requested Part 3 references in I/P and N Parts 7/11/12, and separately searched for Part 12 references in I/P and N Parts 7/11. There are no Part 12 references in those external consumers. Their Part 3 references use the existing ODE layer; N12 does not replace its generic carriers or Newton/restricted predicates. No wider claim about those consumers' proofs is made.

Within N12, `flow` at t and -t supplies injectivity and the inverse homeomorphism for `transport`. `exit` keeps the stopped orbit in G and strictly before the maximal endpoint. `wreg` supplies the norms and individual-mode derivative bound needed by `pointwise`. `envelope_regular` supplies measurable zero extensions for Tonelli. `stopped`, `good`, `bad` and `mean_family` supply the estimates, continuity on K and full-window existence needed by the cores. F1 does not invalidate these norm-only applications.

**Frozen objects: PASS.** Read the frozen rank, error, solution, analytic-integrable, analytic-perturbation, action-ball and real-action-domain definitions, and the frozen frequencyMap, realHamiltonian, hamiltonianVectorField and actionNbhd bodies; compared both theorem telescopes and conclusions. They are used literally. `avgH` is exposed and reducible. `ham_reduction` bridges the actual frozen N/I solution predicates to `IsSolutionIn`. Maximality covers connected closed intervals through zero and retains two-sided endpoint derivatives, supplying the room required by the most-data conclusion.

**Definitions: PASS.** `AveragingData` contains source premises only. `AvgSlabBound` is a derived dependency with distinctly named conditional helpers. Zero mode is killed by k. ENNReal sums retain infinite values until finiteness is established on the valid domain. Flow continuity is asserted only on its open domain; the stopped integrand is killed outside the valid stay set. Full-time existence guards the good-set real supremum. Uniqueness establishes the frozen maximum's continuity on K without imposing regularity on Φ off K. No theorem conclusion relies on fallback trajectory values or an unguarded real supremum.

**Packages: PASS, after adding F1 to N12-06 outputs.** The specified import DAG is acyclic. Picard families, initial derivatives, derivative convergence and global flow regularity are separate packages; no C2 or Lipschitz-DF premise is added to `ext_dep`. Uniform continuity of DF and the displayed recurrence suffice for derivative convergence, without asserting contraction of (y,Y). Transport correctly splits translated image pieces and proves their disjointness. All proposed modules are under 1500 lines; sequential subpackages address the larger dispatch families. These are viable proof obligations and estimates, not completed proofs.

Bridge/API details: `holo_real_b` gives iterated real/complex derivative identities on Wdom. Its order-one pure-perturbation instance (zero integrable part), or subtraction of the integrable part, supplies the real/complex partial identification in `fbounds`. `coefficients_deriv` and `coefficients_repr` use the existing coefficient law, and `actionNbhd_eq_polyNbhd` has exactly the frozen tube as its left side. For termwise differentiation the local open/preconnected theorem avoids global off-domain bounds. The Jacobian equality does not itself assert image Borelness; the inverse continuous flow supplies that in this application. These are implementation steps, not new root premises.

Constants: beta=e^(-πs|k|₁), row-sum M₂, Euclidean |k|₂ only in the slab denominator, sqrt n in cB, 8π/s in cPhi and unnormalised phase volume match. `stopped` chooses witnesses before all size-one f₁, enforcing the advertised perturbation uniformity. The mean factor is 1+(3R/2)/(R/8)=13; η₀=R/8 satisfies η₀≤R/4. The removed κ≤1 premises in rational calculus/identity, arbitrary real ε in flow/transport and arbitrary η in good-set openness are valid strengthenings. No frequency lower bound was introduced.

## Verification and limits

The signature check was run once on the exact requested copy:

    LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n12 .drafts/scratch/N12Signatures.lean

The gate runs `nice -n 5 timeout 1800 lake env lean` against the shared `/root/code/KAM-inp` build snapshot; this worktree has no independent `.lake/build`. Result: exit 0, exactly 29 declaration-uses-sorry warnings, no other diagnostics. Checks here were sequential; no additional build or Lean check was started while another audit-owned Lean/lake operation was pending.

A separate temporary name/type probe, using the aggregate's imports, ran through the same gate: exit 0, all 36 checks resolved. The Mathlib declarations checked were:

- `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`;
- `hasFDerivAt_tsum_of_isPreconnected` and `hasFDerivAt_tsum`;
- `ContractingWith.exists_fixedPoint` and `ContractingWith.tendsto_iterate_efixedPoint`;
- `hasFDerivAt_of_tendstoUniformlyOn` and `hasFDerivAt_of_tendstoLocallyUniformlyOn`;
- `hasFDerivAt_integral_of_dominated_of_fderiv_le`;
- `MeasureTheory.meas_ge_le_lintegral_div`, `MeasureTheory.lintegral_prod` and `MeasureTheory.lintegral_tsum`.

The remaining 25 checks covered the concrete KAM reuse interfaces: HoloReal, domain/norm comparisons, coefficients and tube equality, Cauchy/Fourier/summability, maximality, Hamiltonian reduction, periodicity, exit and periodic continuation. Their printed telescopes were inspected against the uses described above.

Proof status remains design-only. The 29 theorem bodies are placeholders. The designer's axiom-print receipt reports `[propext, sorryAx, Classical.choice, Quot.sound]` for both provider exports; that receipt was read, not independently rerun for the original exports. Nothing here seals a frozen theorem or validates a completed implementation.

No pinned PDF was independently re-audited: the authority in this audit was the local blueprint, packet contracts and frozen definitions. The inherited Nei76 p.1298 (17) issue is quoted by p12 as “sup_t z(t) = ∫_{U′} h”; the integral-of-maximum repair and the rational replacement of the piecewise cubic are already declared deviations. No new pinned-source erratum or frozen defect was found. F1 concerns a design omission only; its proposed fix is reported and has not been applied.

Lint command (using the designer's existing task-local gate wrapper, unchanged):

    LEAN_NUM_THREADS=1 PATH=/root/code/KAM-inp-design-n12/.drafts/scratch/gated-bin:$PATH nice -n 5 sh scripts/lint_sources.sh

Independent result: exit 0:

    check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
    FROZEN-ANCHOR GUARD OK
    ABI HASHES OK (144 frozen declarations)

No targeted production-module build applies: the audit changed no Lean module. The brief's exact signatures elaboration was performed instead; neither the library nor Mathlib was rebuilt.
The F1 replacement was independently elaborated in a standalone definitions-only probe as `wreg_revised` through the same gate: exit 0, one expected sorry warning, no other diagnostics. The first probe extraction left adjacent doc comments and failed parsing; removing those probe-only comments fixed that harness error. The submitted design/signatures were not modified.

Temporary `N12AuditNames.lean` and `N12AuditFix.lean` probes were removed. The explicitly requested exact copy remains at `.drafts/scratch/N12Signatures.lean`. Original signature, design, blueprint and packet hashes were rechecked unchanged. `git diff --no-index --check /dev/null <report>` passes; final git status contains only this new report.

Closeout: all 29 theorem signatures and 42 definitions/structures classified; 91/91 source/proof records mapped; frozen exports compared exactly; 36 API names/types checked; original aggregate and proposed repair elaborated; lint passed. F1 remains open and prevents source-contract approval. Heavy analytic/ODE/measure proofs and pinned-PDF correctness remain outside this design audit's verification claim.
