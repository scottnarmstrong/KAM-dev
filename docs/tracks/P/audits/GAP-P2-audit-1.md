# GAP-P2 independent audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gp2r`.
Audited HEAD: `58568c65f3e2e41f54ce6c3fb6cbdf12ee67fb79`.
Comparison branch `inp`: `d6fa120cc475a689316bdbf716406c2fcc856747`.

**Overall: FAIL for graph-node closure.** The proofs compile and kernel replay passes,
but three of the four requested nodes lack the required source-premise-only, shared-witness
export. No frozen anchor is implemented or seal-ready in this package; provider/frozen-type
and seal-body probes are inapplicable. All new exports are UNSIGNED, as the handoff rules.

The controlling scope is the user-specified report path and the AUDIT FOCUS in
`docs/tracks/P/audits/GAP-P2-handoff.md:41–43`, overriding the generic brief's destination.
Only `KAM/Planetary/Averaging/OscillatorNodes.lean` is audited as new implementation.
`git diff inp...HEAD` contains precisely that new 331-line file. The untracked handoff
was present before this audit and was left untouched.

Read: AGENTS.md, PLAN, DECISIONS, the external package brief, handoff, track P statement,
P23 design (including node table and shared-witness rule), the four graph NODE records,
and the cited blueprint text. Landed dependencies and all 12 frozen definitions in the
local import closure were inspected for applicability/import state, without extending the
implementation audit to their proofs.

## Per-node and declaration verdicts

Names below are in `KAM.Planetary`. Line references without another path refer to
`KAM/Planetary/Averaging/OscillatorNodes.lean`.

| Node / role | Declaration and line | Verdict | Reason |
|---|---|---|---|
| stepP:p2:oi-ratio | `p2_oi_ratio`, 54 | FAIL | Correct generic ratio, factorial-term and composition estimates, but assumes the generator class/bound and `Φ ≤ δ / ᾱ`; never constructs the source generator from h, f and divisor data. See F1. |
| stepP:p2:oi-ratio, integral clause | `p2_oi_ratio_integral`, 97 | FAIL as node export; valid helper | Same generator-output premises. The slice class/bound and joint continuity assumptions are appropriate for the generic integral lemma, but no source-generated remainder is instantiated here. |
| stepP:p2:oi-range, numerical/series clauses | `p2_oi_range`, 121 | FAIL | Exact advertised constants and pointwise series identity under generic generator assumptions, rather than an export derived from the NODE's source hypotheses. See F1. |
| stepP:p2:oi-range, (a),(b) | `p2_oi_range_ab`, 171 | PASS for these clauses only | Source h, divisor, f bound/smallness and finite g decomposition are explicit; `osc_iter` is built inside. Uses the actual `oscStepMap`, exact three-halves-loss displacement bounds and two-loss remainder with the stated denominator. Does not return the numerical/series clauses for that same generator, so it does not close the whole node. |
| stepP:p2:ar-apply | `p2_ar_apply`, 265 | PASS WITH NOTES | Builds `OscHyp` privately from the original analytic, reality, divisor, R2 and K-choice premises. Exposes the displayed Hamiltonian decomposition and coefficient identity, in the source order of source data followed by existential witnesses. The map's reality and the proposition's quantitative bounds are dropped; this is a selected view of the graph's displayed conclusion, not the full averaging proposition. See N1. |
| stepP:p2:ar-collect | `p2_ar_collect`, 300 | FAIL | Correct numerical bound and exponential equality, but existential g and fs have no relation to the averaging map, Hamiltonian identity, or witnesses of ar-apply. It therefore bounds an unrelated selectable remainder. See F2. |
| helper | `OscComposeData.ofDeltaBound`, 39 | PASS as conditional helper | Algebraically derives the composition smallness field from `Φ ≤ δ / ᾱ` and source smallness; it does not prove that bound for the source generator. Its distinct helper name is appropriate. |
| private scalar helper | `ar_exp_kappa`, 214 | PASS | Positive ε and s₀ justify exp/log cancellation and exact fifth power. |
| private source adapter | `ar_hyp`, 226 | PASS | Derives K positivity, κ ≥ 6, the class/size/reality of μP and the joint smallness budget; no dependency conclusion is assumed. |

Restricted slice completeness: oi-ratio FAIL; oi-range FAIL (its (a),(b) portion passes);
ar-apply PASS WITH NOTES for its literal displayed graph conclusion; ar-collect FAIL.
The other GAP-P2 nodes and oi-transfer are outside the assigned slice; they are not
claimed missing. There are no new SIGNED declarations to compare to signature files.

## Findings

### F1 — source generator output is taken as a premise (oi-ratio and oi-range)

Graph `docs/graph/P/DEPGRAPH.md:3757–3759` requires direct-divisor/source iterative data
and says **“use the generator constructed by oi-transfer.”** The corresponding range
contract at `3790–3792` uses the same original data. Blueprint
`blueprint-P/parts/p2-averaging.tex:191` proves **“‖φ‖ ≤ δ / ᾱ”** as part of that transfer;
lines 192–193 then prove the ratio/range statements for this generator.

Instead, lines 58–60, 101–103 and 125–127 assume `hc`, `hb` and `hΦδ` for an independently
quantified φ and Φ. There is no h, f, K, divisor premise, definition `φ := oscGen K h f`,
or internal construction of those output facts in these exports. The adapter at 39–49
only propagates the assumed bound. This is mathematically sound as a generic composition
helper, but fails the focus's explicit rule against taking a proved dependency's OUTPUT
as a premise in a node export. Merely having the original `osc_iter` available does not
make these separate exported statements source-premise-only.

`p2_oi_range_ab` does begin from the original data and returns (a),(b), but does not
instantiate `p2_oi_range` or `p2_oi_ratio` for `oscGen K h f` inside its proof. Thus combining
the names in a handoff does not supply the missing exported source-to-generator bridge.
A repair would retain the generic helpers under helper names and add source-level node
exports which construct the generator and its bounds internally, preserving that same
flow in all conclusions. No such repair was made during this audit.

### F2 — ar-collect loses the shared averaging witnesses

Graph `docs/graph/P/DEPGRAPH.md:4038–4050` specifies **“P~ := (g-mu<P>)+f_*”** and depends
on ar-apply's decomposition. Blueprint `p2-averaging.tex:236–237` introduces g and f_*
through that decomposition and then bounds their collected remainder. The design's
shared-witness rule is explicit at `docs/tracks/P/design/P23-LEAN-DESIGN.md:30`:
**“Preserve shared witnesses across the iteration, limits, tori and complement estimate.”**

The conclusion at 311–319 instead says only that there exist g, fs, Pt with
`Pt = g - μ coeff(P,0) + fs`, Pt in the class, a size bound, and the scalar exponential
identity. There is no Ψ, Hamiltonian identity, independent g/fs estimates, or other
condition making these the averaging witnesses. For example, g = μ coeff(P,0), fs = 0,
Pt = 0 satisfies the function-valued part for any P and any nonnegative target bound,
regardless of whether averaging has been carried out. No class condition on g even
prevents this choice for arbitrary P.

The proof at 324–327 actually obtains the intended witnesses from `averaged_remainder`,
but discards their coupling before export. A valid implementation body cannot repair a
weaker public statement. This is a statement-fidelity failure, not a kernel-soundness
failure. Return the coupled Ψ/decomposition/estimate witnesses together, or retain this
as a local obligation inside a joint source-level construction exporting that coupling.

### N1 — ar-apply is a selected view

Its premises match `DEPGRAPH.md:4009`; `ar_hyp` derives the packaged dependency internally.
The equality and zero Fourier coefficient scaling at 288–291 match the literal displayed
conclusion at `DEPGRAPH.md:4011` / blueprint line 236. Divisor α is rescaled only through
ᾱ = 2πα, with d = min(r s₀, ε₀²) and the exact source K.

At line 296 the proof deliberately drops the map's real-inclusion clause supplied by
`osc_averaging` (landed `OscillatorFinite.lean:84–85`). It also drops the correction/tail
bounds and fs regularity/reality. These are present in the full proposition (blueprint
204–207), but the ar-apply NODE explicitly displays only the decomposition and zero-mode
identity. Hence PASS WITH NOTES for that displayed step; this export must not be treated
as a replacement for the full proposition or as certifying a real canonical map. This
selection also cannot supply the missing coupling in ar-collect.

## Definitions and proof review

No new `def`, `abbrev` or `structure` occurs. `OscComposeData.ofDeltaBound` is a theorem,
not a new definition. Local lets are explicit arithmetic quantities, exact flow and
oscillator domains, actual finite sums, the concrete step map, the corresponding
Hamiltonian difference, and the interval integral. They introduce no junk fallback or
replacement norm. Existing `oscPack` uses phase order ((θ,q),(I,p)) and Fourier parameter
(I,p,q); `oscBound` includes weighted summability, and its bound is a supremum over the
parameter domain of the Fourier sum. Geometric widths and 2π conversion are preserved.
Assertions about total maps are restricted to their legitimate open domains.

The scalar ratio proof uses nonnegative Φ,A, positive losses and exp(1)<4. Powers are
monotone on nonnegative bases. `p2_oi_range` uses exp(1)<2.72 for 0.34 and 0.61, without
an override. The integral export uses the landed joint-continuity contract. `ar_hyp`
uses ε<exp(-1/5) to derive κ>6 and derives, rather than assumes, the μP source bundle.
No kernel proof escape or extra conclusion-shaped premise was found beyond F1's
source-generator applicability problem. F2 is a lost conclusion/coupling.

## Independent validation

All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The compile gate itself supplies nice. Lint ran under nice so its ABI subprocess inherits
that priority and thread limit. No library clean/update/cache operation was run.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp2r KAM.Planetary.Averaging.OscillatorNodes
   [inp-gate] slot 2 acquired 02:26:19 for KAM.Planetary.Averaging.OscillatorNodes
   Build completed successfully (9165 jobs).
   exit 0
   ```

   Only replayed pre-existing warnings: `OscillatorFinite.lean:159:37` unused `hμ`,
   `OscillatorFinite.lean:161:5` unused `hP`. No warning in the audited module.

2. Axiom probe `.lake/abi-scratch/GAPP2Audit.lean`, importing only the audited module,
   printed axioms of all seven new public theorems:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP2Audit.lean
   'KAM.Planetary.OscComposeData.ofDeltaBound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_ratio' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_ratio_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_range' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_oi_range_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_ar_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p2_ar_collect' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

3. Kernel replay, single invocation for the sole new theorem module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorNodes
   replaying KAM.Planetary.Averaging.OscillatorNodes
   exit 0
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

   The only failure is the stale generated root explicitly permitted by the audit brief
   and handoff. It was not regenerated. No substantive lint failure was suppressed.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff --check inp...HEAD`: empty, exit 0. Module size: 331 lines; maximum
   Unicode line width: 99. Copyright/module/public imports/docstring/public section
   present. No banned tokens, EuclideanSpace, resource override, duplicate new public
   helper name or harmful root shadow found; all declarations remain in KAM.Planetary.
   The seven public names occur only in this new file in production KAM sources.

6. Recursive local-import inspection found no provider import and no frozen theorem
   import. The 12 imported frozen files are all definition anchors, each manifest state
   SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC,
   IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, Planetary/Fast,
   Planetary/Phase, Planetary/Slow. No DRAFT_SORRY dependency and no sorryAx in the exports.

The scratch axiom probe is deleted after use. Only this report was written as a
repository deliverable. No state-changing git operation was performed.

## Uncertainties, defects and deviations

No suspected new pinned-source or frozen-statement defect was identified. The failures
above concern Lean export fidelity to the pinned graph/blueprint, not refutations of the
analytic estimates. Blueprint line 196 already records the oscillator-extension source
gap; this audit does not independently re-certify its original external PDFs or close
that broader source obligation. No change to errata ledgers, frozen files or generated
files was made. No heartbeat design signal occurred. The omitted map reality clause is
explicit in the handoff and N1 above; F1/F2 are additional export deviations found here.
