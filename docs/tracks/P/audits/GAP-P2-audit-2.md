# GAP-P2 independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gp2r`.
Audited HEAD: `0d6ffabb538d9fbbf799f4d1c84f6ba00fb00f3e`.
Comparison ref `inp`: `02f1bcd96b3681d37a276e77c2ec795dbece6ae4`.

**Overall: FAIL under the required literal graph-export criterion.** The source-generator
and shared-witness defects of audit 1 have been repaired. The remaining finding is the
replacement of the generator's actual norm by its source upper bound in the named
ratio/range exports (F1). The arithmetic estimates and proofs are sound at the stated
upper bound. This verdict distinguishes that useful result from the stronger literal
NODE contract. No frozen anchor is implemented or seal-ready in this package.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the external
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, track P statement,
P23 design and node table, the handoff and audit 1, all four assigned NODE records,
and their blueprint statements/proofs. The user-specified absolute report destination
controls over the generic brief's MAIN-worktree sentence. Only
`KAM/Planetary/Averaging/OscillatorNodes.lean` is audited as implementation.

The complete `git diff inp...HEAD` has three added files: the 482-line implementation,
the handoff and audit 1. The handoff describes the earlier 331-line revision, not current
HEAD. In particular `p2_oi_range_ab` and `p2_ar_collect` no longer exist: their replacements
are `osc_iter_range_ab` and `p2_ar_apply_collect`. The graph-node audit below evaluates
the current replacements; these stale handoff names are not themselves a proof failure.
There are no new SIGNED declarations and no provider exports. Exact frozen-type and seal-body
probes are therefore inapplicable; no frozen theorem closure is claimed.

## Per-node and declaration verdicts

Names are in `KAM.Planetary`; line numbers refer to OscillatorNodes.lean.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| oi-ratio | `p2_oi_ratio` :213 | FAIL literal export | Derives generator class/bound internally, but defines Φ as δ/(2πα), not the actual generator norm; estimates use the resulting larger θ. F1. |
| oi-ratio, integral clause | `p2_oi_ratio_integral` :250 | FAIL literal export | Same replacement of Φ; otherwise valid integral estimate. The continuity assumptions are sourced in N's composition-integral corollary. |
| oi-range | `p2_oi_range` :285 | FAIL literal export | Numerical chain uses θ computed from δ/(2πα); its first comparison is an equality rather than the source comparison involving actual generator size. Series identity and (a),(b) on the same generator/map are correctly exported. F1. |
| oi-range, (a),(b) helper | `osc_iter_range_ab` :174 | PASS for these clauses | Builds `osc_iter` from original source premises and projects displacement/remainder clauses with exact constants and domains. |
| ar-apply | `p2_ar_apply` :396 | PASS WITH NOTES | Constructs OscHyp from source premises; existential map/g/fs and Hamiltonian/zero-mode identities match the displayed NODE conclusion. Selected view of the full proposition; N1. |
| ar-collect, jointly with ar-apply | `p2_ar_apply_collect` :432 | PASS WITH NOTES | Preserves Ψ,g,fs,Pt together, their Hamiltonian identity, Pt formula, class and exact summed bound and exponential identity. Repairs audit-1 F2; N1. |
| conditional adapter | `OscComposeData.ofDeltaBound` :39 | PASS as helper | Derives composition smallness from the explicit generator upper bound and source smallness. No claim to construct a generator. |
| conditional helper | `osc_ratio_of_gen_bound` :55 | PASS as helper | Generic class/upper-bound version; explicitly renamed so it does not stand in for a source node export. |
| conditional integral helper | `osc_ratio_integral_of_gen_bound` :99 | PASS as helper | Uniform class/bound plus joint continuity of v and Dv are the integral corollary's hypotheses. |
| conditional range helper | `osc_range_of_gen_bound` :124 | PASS as helper | Correct numerical chain and pointwise composition/series identity for an admissible Φ. |
| private scalar helper | `ar_exp_kappa` :345 | PASS | Uses positive ε,s₀ and exact K choice to prove exp(-κ/6)=ε⁵. |
| private source adapter | `ar_hyp` :357 | PASS | Derives K>0, κ≥6, class/bound/reality of μP and smallness internally, with no dependency output as a premise. |

All four assigned graph records were read, including SOURCE_HYPOTHESES,
SOURCE_QUANTIFIERS and SOURCE_CONCLUSION. Source data precede ∀j in ratio and existential
witnesses in ar-apply/collect; no constant is selected after a witness that should precede it.
The source finite g decomposition in range is explicit; the generic u/A data are the test
function and its finite bound for composition. Source norm equalities for f and u are
relaxed to upper bounds, which covers the source equality cases. F1 concerns a different
operation: substituting a larger bound into the conclusion's defined ratio.
The other handoff nodes were already closed or expressly excluded; oi-transfer is not
counted as a missing deliverable. Restricted slice closure still fails at oi-ratio/oi-range.

## F1 — the node's θφ has been replaced by a larger θδ

`docs/graph/P/DEPGRAPH.md:3759` defines
“theta_phi:=2 e b ¦phi¦/delta_nu” and requires the factorial and composition estimates
at that ratio. Its range contract at :3792 uses this same theta_phi. Blueprint
`blueprint-P/parts/p2-averaging.tex:192–193` explicitly defines
η from the actual norm of φ and then compares θφ to 2ebδ/(ᾱδν).

Current `p2_oi_ratio:223–226`, `p2_oi_ratio_integral:266–267`, and
`p2_oi_range:299–301` instead set

```text
φ := oscGen K h f
Φ := δ / (2 * π * α)
θ := 2 * exp 1 * (1 + m) * Φ / δν
```

`oscGen_class_bound`, called at :244, :277 and :333, proves only that the generator
has weighted norm **at most** Φ. Nothing identifies its actual norm with Φ. Thus these
exports prove bounds with θδ = 2ebδ/(ᾱδν), not the specified θφ. Since θφ ≤ θδ < 1,
θδ^j A and (1-θδ)⁻¹ A are generally larger, so those estimates do not imply the
requested estimates with θφ. Even for an exact f norm, the homological estimate can
be strict (for example f can have only zero Fourier mode, giving zero generator).
This is not just a different spelling of the same constant.

The range export's first inequality at :302 becomes a tautological comparison of θδ
with itself. It correctly proves θδ≤e/8 and the series equality, but does not state
the source's first comparison with actual θφ. The documentation at :210–211 and
:281–283 still calls this θφ and describes it using |φ|, hiding this distinction.

Audit-1 F1's extra-premise problem is repaired: the new node exports take h,f and divisor
data, and derive generator class/bound internally. The remaining failure is conclusion
strength. The generic renamed helpers are useful for repairing it: construct the actual
finite supremum of the weighted Fourier sums internally, prove it is nonnegative and
bounded by δ/ᾱ, and instantiate the helpers at that size (and at the actual u norm when
needed). Alternatively a changed graph contract needs an explicit owner/orchestrator
ruling accepting the upper-bound version; this audit does not silently change it.
No such literal actual-norm instantiation is present in the audited module.

## N1 — selected averaging views and repaired witness coupling

The ar-apply NODE at DEPGRAPH.md:4009–4011 / blueprint :236 displays the decomposition
and zero-mode identity. `p2_ar_apply` exports those, together with map analyticity,
injectivity, maps-to, symplecticity, lattice equivariance and real angle-independent g.
It deliberately drops map reality and the quantitative bounds of the full proposition
(blueprint :204–207); it must not replace that full proposition.

The joint theorem now binds Ψ,g,fs,Pt together at :442 and retains the Hamiltonian
identity :453–454, coefficient identity :455–456, and Pt formula :458, before the bound
:460–463. Its proof obtains all witnesses from one `averaged_remainder` application
:466. The Hamiltonian decomposition follows by the retained identity and Pt formula,
not by choosing unrelated witnesses. This closes the displayed collect node
(DEPGRAPH.md:4038–4050, blueprint :237) and repairs audit-1 F2. This remains a selected
view: map reality, Pt reality, the separate correction/tail bounds and component
map displacements are not exported. The literal collect node requires the summed
bound, which is present; no full averaged-remainder proposition is certified here.

## Definitions, applicability and soundness

There are no new `def`, `abbrev` or `structure` declarations. All new declarations are
theorems. Local lets denote explicit arithmetic quantities, actual source generator,
flow, finite sum, transformed Hamiltonian difference, domains and integral. No fallback
or replacement norm is introduced. The Φ substitution is a statement-fidelity issue,
not junk evaluation or a proof escape.

The imported `oscBound` (OscillatorSetting.lean:49–51) asserts weighted summability and
a bound for each parameter; it is not an equality to a supremum. `oscPack` retains
phase order ((θ,q),(I,p)) and Fourier parameter order (I,p,q). Widths remain geometric,
with mode weight exp(2πS|k|₁) and divisor ᾱ=2πα. Assertions restrict total maps to their
legitimate domains. `oscStepMap` unfolds to precisely the same time-one flow used in
the series clause; range's (a) uses the three-halves-loss domain and (b) two losses.
The ratio is nonnegative and small; geometric summability is supplied by the landed
composition/series results, rather than inferred from a total tsum alone. Integral joint
continuity is expressly required by blueprint-N/parts/p5-canonical-maps.tex:203–205.

No extra conclusion-shaped source premise remains in the named node exports.
The generic helpers retain their explicit conditional purpose. The ar_hyp construction
preserves μ, K and ε quantifiers, positivity and reality, and derives rather than assumes
the dependency package. No proof defect was found beyond F1's export fidelity issue.

## Independent validation

All Lean/Lake invocations were serialized with LEAN_NUM_THREADS=1 and nice priority;
the compile gate supplies nice itself. No library clean, update, cache get, package edit,
generated-root regeneration or state-changing git operation was performed.

1. Targeted build (exit 0):

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp2r KAM.Planetary.Averaging.OscillatorNodes
   [inp-gate] slot 3 acquired 02:42:15 for KAM.Planetary.Averaging.OscillatorNodes
   Build completed successfully (9165 jobs).
   ```

   Only replayed warnings: OscillatorFinite.lean:159:37 unused hμ and :161:5 unused hP.
   No warning from OscillatorNodes.lean; no default-heartbeat design signal.

2. Axiom probe (exit 0):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP2Audit2.lean
   ```

   The probe imported only the audited module and printed axioms of every new public
   theorem. Exact output:

   ```text
   'KAM.Planetary.OscComposeData.ofDeltaBound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_ratio_of_gen_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_ratio_integral_of_gen_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_range_of_gen_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.osc_iter_range_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_ratio_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_range' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_ar_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_ar_apply_collect' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay, one invocation (exit 0):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorNodes
   replaying KAM.Planetary.Averaging.OscillatorNodes
   ```

4. Full source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1210 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is the permitted stale generated root. This is not counted as
   a finding, and the root was not regenerated. No substantive lint failure was
   suppressed; the module check, frozen guard and ABI hashes passed independently.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty (exit 0).
   `git diff --check inp...HEAD` and `git diff --check`: empty (exit 0).
   Audited module: 482 lines, maximum Unicode line width 98; copyright, module,
   public imports, module docstring and public section present. Source lint checks
   banned tokens, resource overrides, EuclideanSpace and the 1500-line cap.
   A production declaration-name scan found each of the ten new public theorem
   short names only in this module. All declarations remain in KAM.Planetary;
   no reused public helper short name or harmful root shadow was found.

6. Recursive local-import inspection found 119 local modules, zero providers and
   zero frozen theorem imports. All twelve frozen imports were read and checked
   against the live manifest as SEALED definition anchors: ActionNbhd, ComplexStrip,
   HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip,
   IsRealOnReals, OmegaZero, SymplecticForm, Planetary/Fast, Planetary/Phase,
   Planetary/Slow. No DRAFT_SORRY import or sorryAx occurs in the audited exports.

The temporary probe and audit scratch text were deleted after use. Only this report
was written as a repository deliverable; existing implementation, handoff and audit 1
were left untouched. No commit or other state-changing git operation was performed.

## Uncertainties, suspected errata and deviations

No new suspected pinned-source or frozen-statement defect was identified. Blueprint
p2-averaging.tex:196 already records an oscillator-extension source gap; this audit
checks the assigned graph-to-Lean slice and does not close that external-source gap
or re-certify the original CP10/Pos93 PDFs. F1 is an implementation/export deviation
from the literal graph statement, not a refutation of the analytic estimate. N1 and the
stale handoff mappings are retained explicitly. No audit-introduced mathematical
change, resource override, generated-file edit or errata-ledger edit was made.
