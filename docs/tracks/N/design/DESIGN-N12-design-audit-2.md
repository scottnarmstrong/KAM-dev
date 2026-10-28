# DESIGN-N12 delta design audit 2

Overall verdict: **PASS**.

Both earlier items are resolved: F1's missing termwise derivative conclusion is now part of the actual `wreg` type, and N1's graph hash labels are correct. No new finding was identified in the revision. This is design/source-contract approval; the proofs remain placeholders and neither frozen averaging theorem is proved or sealed.

## Scope, authority and frozen snapshot

Delta audit of revision 2 at `c0abe0340ad59bb8a4ebb79090b744b9f3b6e885` against revision 1 at `8cf4eb8b5e8cafbd222ea027dc6f4b221906016b`. Read the audit brief, AGENTS, PLAN, DECISIONS, first audit, revised handoff, entire commit diff, affected blueprint/packet statements and consumer proof steps. Continued the focused manuscript-audit method. No subagents, production edits or state-changing git operations.

The acceptance condition was closure of every earlier finding, fidelity and applicability of the complete touched surface, unchanged unaffected signatures, and fresh gated elaboration. Unchanged signatures retain audit-1 judgments, supported by exact byte comparison rather than a claimed second full audit.

Snapshot `r2-audit`:

| Input | SHA-256 |
|---|---|
| Revised design | `d66059fe35c7b3f76307ae60df90aa3da66ea089cd3ec073b39cbe2ffd1b6370` |
| Delivered 505-line signatures | `0ad9cf0f84ffc435f1d85360516ad94f5ec100ff4a53c76d410f9e7d3b028369` |
| First audit | `253a0fb2f7d199f8167fbaa14560530e9096c4cd50d4f5bbb57b6103a04cf63e` |
| Revision-2 handoff | `bd335d7c4e78af84f532e1be9461ab9bbed443812c92065c12f6766127d18d4d` |
| Part 12 blueprint | `dd549dc5c3069e1a185767b5fa580d979963fa920a4b9e7939529047d13ebbfc` |
| Combined `docs/graph/N/DEPGRAPH.md` | `941c8d1d4bb6c17e3369d57b86441798544e1dabc8a9af1735882f75aa8972d2` |
| Packet `docs/graph/N/packets/N-p12.nodes.md` | `2994dff658689fa1b5ad4a4d3908f26ac6369868106683874a85f1c7e44aad4d` |

The commit changes only the design document (67 insertions, 7 deletions). The delivered signature text differs from revision 1's committed Appendix A by exactly the five-line conjunct proposed in audit 1. Removing that conjunct recovers the old aggregate byte for byte: all imports, definitions, other signatures, existing conclusions, premises and constants are unchanged. Revised Appendix A equals the delivered file byte for byte.

## Earlier findings and revision review

| Item | Previous severity | Status | Evidence and disposition |
|---|---|---|---|
| F1: omitted termwise derivatives | MEDIUM, blocking source fidelity | **RESOLVED** | Signature:232–236 adds the exact audit-proposed directional `HasSum`. Design:160–161 updates source-node mapping; :280 and :339–357 require the output in N12-06 and explain downstream projections. No further fix required. |
| N1: graph hash mislabel | LOW | **RESOLVED** | Design:433–437 now distinguishes the combined graph from the Part 12 packet, with paths and independently recomputed matching hashes. No further fix required. |

No new numbered finding or proposed signature repair is needed.

F1 fidelity: blueprint p12:113 says “with termwise derivatives”; packet `bpN:p12:wreg` repeats that conclusion. The new conjunct quantifies over **every** z in `avgDomain n R` and **every** real phase direction v, outside the later `avgG` guard. It sums derivatives of the actual negative character-weighted terms and identifies their sum with `fderiv ℝ (avgW h f κ) z v`. The derivative field is ℝ and the target remains the complex Pi space. Selecting v=(vθ,0) and (0,vI) gives both partial series. The k=0 term and its derivative vanish. C1 regularity and the complete former periodicity/residual/norm tail remain intact.

Refutation checks: the repair is not merely a residual contraction, a bound, or an extra hypothesis assuming the missing result. It does not restrict the series equality to G, replace the complex corrector with a real one, change sign, or alter any frozen definition. The apparently different placement of the minus sign is valid: `(-character) • u = -(character • u)` and negation commutes with a summable series. The domain is open, so these are genuine derivatives of the total functions at valid points.

The new proof gate is viable as a design obligation. On a small open preconnected product neighborhood with action closure inside the source ball, coefficient decay and rational-divisor bounds give summable majorants for the terms and their real Fréchet derivatives. The chosen Mathlib theorem requires precisely that local derivative domination, differentiable summands, and convergence at one point. Summability of the derivative linear maps permits applying them to v; derivative uniqueness identifies the resulting map with fderiv. Product/chain rules then expand the partial formulas. These remain proofs to supply in N12-06, not facts established by elaboration.

## Signature ledger

Names and labels follow audit 1: new names lie in `KAM.Nekhoroshev` and `Provider.*` abbreviates `KAM.Provider.Nekhoroshev.*`. The row for `wreg` is freshly re-audited; all other rows are retained on exact unchanged text. The two provider telescopes/conclusions were additionally compared directly with their frozen files again.

### Theorems (29)


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
| `wreg` | `wreg` | PASS | Rechecked in revision 2: full-domain directional derivative HasSum added; source premises and all earlier bounds retained. |
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

## Consumers, frozen objects and packages

**Consumers: PASS.** Blueprint `wr-ac`, `wr-b` and `wr-d` now have the missing derivative-series conclusion available. Their existing quantitative outputs remain available from the third top-level conjunct, as the revision explicitly instructs; C1 remains first, directional HasSum is second. The subsequent identity/pointwise/transport/stopped/assembly contracts and carriers are unchanged. Repeating the search finds no Part 12 references in I/P or N Parts 7/11; their existing Part 3 references are outside this change. No additional consumer premise is introduced.

**Frozen objects: PASS.** No frozen file or manifest changed in the revision. Re-read the literal `IsSolutionOn` and `realHamiltonian` definitions and compared both provider statements directly against their frozen anchors. They remain exact matches. The new series clause uses existing `avgW` and `avgU`, with no parallel definition or assumed equality.

**Definitions: PASS.** All 42 definitions/structures, the local classical instance and every carrier are byte-identical to revision 1. No conclusion-shaped field, new global instance, off-domain regularity assumption or unguarded supremum use is introduced.

**Packages: PASS.** N12-06 gains the explicit equality and both partial series. Its existing dependency on the coefficient and corrector modules already supplies the terms and their analytic bounds. The import DAG, ownership, waves and module line estimates are unchanged; the 505-line signatures aggregate stays below the 1500-line cap. The documentation updates both affected graph mappings and warns consumers about the changed conjunction projection. No cycle, hidden flow assumption or new upstream API is introduced. The 91/91 selected graph rows remain present.

## Verification and limits

Fresh exact-copy elaboration (run once):

    LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n12 .lake/abi-scratch/N12R2AuditSignatures.lean

Result: **exit 0, exactly 29 declaration-uses-sorry warnings, no other diagnostics**. The gate waited for a slot, then used LEAN_NUM_THREADS=1 and nice -n 5 against the shared /root/code/KAM-inp build snapshot. Audit-owned Lean/lake checks were serialized. No resource-budget override or production build was used.

Mechanical checks passed: exact five-line-only signature delta; equality with audit 1's proposed correction; current Appendix equality; both provider telescope/conclusion comparisons against frozen anchors; unchanged 42 definitions/structures and 28 other theorem signatures; 91 selected packet records mapped. No KAM, manifest, blueprint or graph change is present between the audited commits.

Fresh API probe through the same gate: exit 0, no diagnostics. `#check hasFDerivAt_tsum_of_isPreconnected` and `#check hasFDerivAt_tsum` resolve with the expected scalar fields, differentiability and summable derivative-bound telescopes. The local theorem's source in `Mathlib/Analysis/Calculus/SmoothSeries.lean:72` was inspected. The new gate correctly uses the local open/preconnected version; it does not require global bounds on arbitrary total extensions. The unchanged API inventory retains audit 1's checks.

Axiom/proof status: the revised handoff reports `[propext, sorryAx, Classical.choice, Quot.sound]` for both provider exports. That axiom-print receipt was read rather than independently rerun in this delta. The current aggregate still has 29 sorry bodies. This PASS does not remove sorryAx, establish the local domination or ODE/measure proofs, or seal any frozen theorem.

No new source erratum, source deviation or frozen defect was identified. The inherited Nei76 p.1298 (17) issue (“sup_t z(t) = ∫_{U′} h”) and the rational replacement of the piecewise cubic remain documented as before. No pinned-PDF re-audit is claimed.

Independent lint rerun:

    LEAN_NUM_THREADS=1 PATH=/root/code/KAM-inp-design-n12/.drafts/scratch/gated-bin:$PATH nice -n 5 sh scripts/lint_sources.sh

Result: **exit 0**:

    check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
    FROZEN-ANCHOR GUARD OK
    ABI HASHES OK (144 frozen declarations)

The existing gate wrapper was read and reused unchanged for lint's ABI elaboration. No production Lean module changed, so no targeted module build applies. Both audit-owned temporary probes were removed. Audit 1 was preserved unchanged. The final report passes `git diff --no-index --check /dev/null <report>`; status retains the pre-existing untracked audit 1 and adds only audit 2.

Final input hashes were rechecked against the snapshot above. Closeout: **F1 resolved; N1 resolved; no new findings; PASS for revision-2 design/source contracts.** Local dependence, series domination, nonlinear slabs, transport and both provider proofs remain implementation obligations.
