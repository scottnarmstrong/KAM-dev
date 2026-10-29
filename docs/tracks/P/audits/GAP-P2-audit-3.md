# GAP-P2 independent audit 3

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gp2r`.
Audited HEAD: `7a363d29ea242dd381ba218529b3384293c11fdb`.
Comparison `inp` at inspection: `4d8a6848e381c8baaa9072e8d9867e3fc7a36f2a`.
Three-dot merge base: `9208f71fad9c557fdee5db7c9a1b7bd222094650`.

**Overall: FAIL for the literal graph-export contract, solely at oi-range's remainder
denominator (F1).** Audit 2's actual-generator-norm defect is repaired in the ratio,
integral and numerical-range clauses. The remaining remainder estimate is sound as
stated and matches the displayed oscillator iterative lemma, but is weaker than the
literal oi-range NODE conclusion. This distinction also exposes a blueprint precision
discrepancy, recorded below rather than silently resolving it. No frozen anchor is
implemented or seal-ready here.

## Scope and authority

Read AGENTS.md, PLAN, DECISIONS, the external package audit brief, the handoff and
audits 1 and 2, track P's statement/conventions, the relevant P23 design node table
and oscillator addendum, all four assigned NODE records including their hypotheses,
quantifiers and conclusions, and the cited blueprint statements/proofs. Implementation
scope is only `KAM/Planetary/Averaging/OscillatorNodes.lean`. Landed dependencies were
read for applicability, definitions and import state; their proofs are not re-audited.
The explicit user destination controls over the generic brief's MAIN-worktree sentence.

The complete `git diff inp...HEAD` adds the 502-line implementation, the 43-line handoff,
and audits 1 and 2 (205 and 229 lines). No other path is changed. The handoff still
describes the 331-line initial revision and stale names: `p2_oi_range_ab` is now
`osc_iter_range_ab`; `p2_ar_collect` is now the joint `p2_ar_apply_collect`. These are
documentation notes, not additional proof failures. All new exports are UNSIGNED;
there is no provider or signed/frozen declaration in scope. Provider=frozen-type and
seal-body probes are therefore inapplicable. The already-closed handoff nodes and
expressly excluded oi-transfer are not missing deliverables in this restricted audit.

## Per-node and declaration verdicts

Names below are in `KAM.Planetary`; bare line numbers refer to OscillatorNodes.lean.

| Node / role | Declaration : line | Verdict | Reason |
|---|---|---|---|
| stepP:p2:oi-ratio | `p2_oi_ratio` :230 | PASS | Constructs the source generator internally; actual weighted supremum defines Φ and θφ; exact ratio identity, scalar comparison, factorial estimates and composition bound on the two-loss domain. |
| oi-ratio, integral clause | `p2_oi_ratio_integral` :268 | PASS | Same actual generator norm and flow; integral class and bound with the exact θφ factor. Joint continuity is sourced in N's integral corollary. |
| stepP:p2:oi-range | `p2_oi_range` :303 | FAIL literal export | Numerical chain and series/composition identity now use actual θφ and pass. Same-map displacement passes. The remainder denominator still uses θδ instead of θφ; F1. |
| oi-range (a),(b) helper | `osc_iter_range_ab` :174 | PASS for displayed lemma | Builds `osc_iter` from original premises and projects its exact displacement and displayed δ-majorant remainder bound. It does not export the stronger graph denominator. |
| stepP:p2:ar-apply | `p2_ar_apply` :416 | PASS WITH NOTES | Builds OscHyp internally and exports the displayed Hamiltonian and zero-mode identities. Selected view, not the whole averaging proposition; N1. |
| stepP:p2:ar-collect, joint with ar-apply | `p2_ar_apply_collect` :452 | PASS WITH NOTES | Shared Ψ,g,fs,Pt, Hamiltonian identity, Pt formula/class and exact summed bound, with exp(-κ/6)μ=με⁵. N1. |
| conditional adapter | `OscComposeData.ofDeltaBound` :39 | PASS as helper | Derives composition smallness from the generator majorant and source smallness. Distinct helper, not a source-generator theorem. |
| conditional helper | `osc_ratio_of_gen_bound` :55 | PASS as helper | Correct ratio/factorial/composition bounds for any admissible generator bound Φ and test-function bound A. |
| conditional integral helper | `osc_ratio_integral_of_gen_bound` :99 | PASS as helper | Correct uniform integral bound, with sourced continuity assumptions. |
| conditional range helper | `osc_range_of_gen_bound` :124 | PASS as helper | Correct numerical chain and pointwise series identity for any admissible Φ. |
| private norm helper | `osc_actual_norm` :212 | PASS | Proves supremum finite/bounded, nonnegative, and a valid summable weighted bound, including empty domains. |
| private scalar helper | `ar_exp_kappa` :365 | PASS | Positive ε,s₀ and the exact K choice imply exp(-κ/6)=ε⁵. |
| private source adapter | `ar_hyp` :377 | PASS | Derives K>0, κ≥6, class/size/reality of μP and smallness from source premises. |

The restricted four-node slice is incomplete only at the literal oi-range denominator.
Source data precede the universally quantified iteration index or existential averaging
witnesses. No changed constant dependence or reversed existential/universal order was
found. The arbitrary nonnegative bounds δ,A,B cover the source's exact-norm cases;
for a nonempty domain the finite norm of u can be substituted for A. Empty oscillator
domains make the analytic assertions vacuous. The finite g decomposition is source
typing/analytic data, not a dependency output. Named node exports no longer assume
generator class/bound or OscHyp as premises: these are built inside.

## F1 — oi-range still weakens the remainder denominator

`docs/graph/P/DEPGRAPH.md:3792` requires (a),(b) with the replacement
`1-2 q delta/(alpha-bar rho sigma) -> 1-theta_phi`. The same literal wording occurs
in `blueprint-P/parts/p2-averaging.tex:193`. Here θφ is explicitly defined at blueprint
line 192 and DEPGRAPH line 3759 from the **actual** generator norm.

The current theorem correctly defines that norm at :319 and θφ at :320. But its
remainder conclusion at :343–346 is

```text
oscBound ... fp ((1 - θδ)⁻¹ * C * δ)
θδ = 2 e b δ / (ᾱ d)
C  = 2 b / (ᾱ d) * (Rsum + δ) + exp(-2πKσ)
```

The required literal graph conclusion uses `(1-θφ)⁻¹` in this position. The proof
at :348 obtains the remainder clause solely from `osc_iter_range_ab`, whose own
conclusion :201–203 has the same θδ denominator. The later actual-norm construction
at :352–355 repairs only the first, numerical/series conjunct.

Since 0≤θφ≤θδ≤e/8<1, the reciprocal inequality goes in the weakening direction:
`(1-θφ)⁻¹ ≤ (1-θδ)⁻¹`. On nonempty domains the other source bounds give a nonnegative
numerator, so a bound by the larger right-hand side does not establish the smaller
one. There is no equality of the generator norm with δ/ᾱ. The ratio and integral
exports control composition of a supplied test function, but neither states a bound
for this particular fp with numerator Cδ and the smaller denominator. No such
additional remainder derivation occurs inside this audited module.

This finding does **not** refute the numerical estimate or `osc_iter`: the displayed
oscillator iterative lemma at blueprint :187 explicitly uses θδ and is matched exactly.
The proof-step text at :193 and its graph extraction retain the stronger θφ denominator
before that final weakening. Under the handoff's explicit literal NODE rule, the
unsigned node export must retain that stronger intermediate estimate, or an explicit
owner/orchestrator ruling must change the graph contract to the displayed lemma's
majorant version. Neither is present. No implementation, blueprint or graph was edited
to resolve this discrepancy during the audit.

## Repaired norm issue and definition review

There are no new `def`, `abbrev` or `structure` declarations. Local lets give arithmetic
constants, the source generator/flow, oscillator domains, finite sums, Hamiltonian
differences, the integral, and now the actual weighted supremum.

The new private helper :212–223 first proves BddAbove of the image of the weighted
sum using the landed generator bound. Each parameter retains WSummable from that
bound, so the total tsum does not silently evaluate to junk. `le_csSup` supplies the
bound at each parameter, positivity of the summands gives nonnegativity, and
`Real.sSup_le` supplies the upper bound including the empty image (real sSup empty
is zero). Thus no domain-nonemptiness premise or arbitrary fallback is introduced.
The three named oi exports invoke this helper after `oscGen_class_bound`, passing
the resulting actual bound to their generic helpers. This repairs audit 2's F1 for
the ratio, integral and numerical-range clauses.

`oscPack` keeps phase order ((θ,q),(I,p)) and Fourier parameter order (I,p,q).
`wsum` uses weights exp(2πS|k|₁); widths are geometric and ᾱ=2πα is retained.
`oscStepMap` is definitionally the same one-loss-domain time-one flow used by the
series identity. Displacement is on the three-halves-loss domain, while series,
composition and remainder bounds are on the two-loss domain. All assertions about
total maps are restricted to the appropriate domains. Series convergence is justified
by the landed summable geometric construction used by the helpers; the total tsum
in the series identity is not used as a substitute for convergence. No proof escape,
unsourced conclusion premise or heartbeat design signal was found.

## N1 — averaging exports remain selected views

DEPGRAPH :4011 / blueprint :236 displays the decomposition and zero-mode identity;
`p2_ar_apply` exports these from the exact R1,R2,K and analytic/reality premises.
Its private adapter derives the dependency bundle. It deliberately drops the real-map
clause and full quantitative estimates of the proposition (blueprint :204–207).
This remains PASS WITH NOTES for the displayed node, not certification of the whole
averaging proposition or of a real canonical map from this export alone.

The joint theorem :462–483 retains a single Ψ,g,fs,Pt and their Hamiltonian identity,
coefficient identity and remainder formula before exporting the summed bound and
exponential equality. One `averaged_remainder` application at :486 supplies those
witnesses. The transformed decomposition follows algebraically from the retained
identities. Audit 1's witness-coupling defect remains repaired. Separate correction/tail
bounds, map reality, Pt reality and component displacements are not all exported here;
the literal collect node asks for the summed bound, which is present. These exports
must not replace the full averaged-remainder proposition for other consumers.

## Independent checks

Every Lean/Lake invocation below was serialized with LEAN_NUM_THREADS=1. The compile
gate supplies nice priority; subsequent commands explicitly use `nice -n 5`.

Targeted build, exit 0:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp2r KAM.Planetary.Averaging.OscillatorNodes
[inp-gate] slot 3 acquired 02:56:35 for KAM.Planetary.Averaging.OscillatorNodes
✔ [9165/9165] Built KAM.Planetary.Averaging.OscillatorNodes (18s)
Build completed successfully (9165 jobs).
```

Only pre-existing replayed warnings: OscillatorFinite.lean:159:37 unused hμ and
:161:5 unused hP. No warning in OscillatorNodes.lean.

Axiom probe, exit 0:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP2Audit3.lean
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

Kernel replay, one invocation, exit 0:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorNodes
replaying KAM.Planetary.Averaging.OscillatorNodes
```

Full source lint, exit 1:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1210 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The sole failure is the stale generated root explicitly permitted by the brief and
handoff. It is not counted as a finding. No substantive lint failure was suppressed,
and the root was not regenerated. Banned-token/resource-override, EuclideanSpace,
line-width, file-size and module checks produced no additional failure.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty, exit 0.
`git diff --check inp...HEAD` is empty, exit 0. The implementation has 502 lines,
maximum Unicode width 98, and the required copyright/module/interface imports/docstring/
public section. New public declaration names are unique in production sources;
`OscComposeData.ofDeltaBound` is explicitly qualified and all other new declarations
stay inside KAM.Planetary. No harmful root shadow was found.

Recursive local imports comprise 119 modules, zero providers and zero frozen theorem
modules. All 12 frozen definition imports were read and checked against the live
manifest as SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField,
HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero,
SymplecticForm, Planetary/Fast, Planetary/Phase, Planetary/Slow. No DRAFT_SORRY
import or sorryAx occurs in the audited exports.

## Uncertainties, suspected errata and deviations

The blueprint precision discrepancy is exact: :187 prints the weaker θδ denominator;
:193 says to substitute `1-theta_phi`, with θφ defined from the actual generator norm
at :192. Both inequalities may be true, but the latter is a stronger intermediate
claim; one cannot identify the two constants. This is a graph/blueprint export issue,
not a newly verified erratum in CP10 or Pos93. F1 is the corresponding implementation
deviation under the stipulated literal rule. Earlier audit 2 treated the displayed
δ-bound as sufficient for (a),(b); this audit explicitly distinguishes that displayed
lemma from the stricter NODE text.

Blueprint :196 already records the oscillator-extension source gap. This restricted
audit does not close that external-source obligation or independently re-certify the
original PDFs. No frozen-statement defect was found. No proof, generated file, ledger,
package dependency or git state was changed. The scratch probe is deleted after use;
the sole repository deliverable is this report at the user-specified absolute path.
