# GAP-P2 independent audit 4

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gp2r`.
Audited HEAD: `400e11b59e5f0421da398b94dfc32e18920801a9`.
Comparison ref `inp` at inspection: `f38de76be1689652e630490c1007aac7dbd74080`.
Three-dot merge base: `9208f71fad9c557fdee5db7c9a1b7bd222094650`.

**Overall: PASS WITH NOTES for the restricted four-node graph-export package.**
Audit 3's F1 is repaired: the same actual-generator ratio now occurs in both the
numerical/series clauses and the remainder denominator of `p2_oi_range`.
No remaining literal-conclusion or added-premise failure was found in the assigned
slice. No frozen anchor/provider is implemented here, and no frozen theorem is
certified seal-ready by this report.

## Scope, authority and comparison

Read the worktree AGENTS.md, PLAN and DECISIONS, the external package audit brief,
the handoff's AUDIT FOCUS and overnight ruling, audits 1–3, track P's statement and
conventions, the P23 design's relevant original/addendum node tables and oscillator
interfaces, all four assigned graph NODE records, and their cited blueprint text.
The explicit user destination overrides the generic brief's MAIN-worktree sentence.
The implementation audit is of `KAM/Planetary/Averaging/OscillatorNodes.lean`.
Dependencies were inspected for exact applicability and import/definition state.
The changed remainder dependency received the specific review described below;
this is not a new audit of every landed dependency or of the full oscillator transfer.

The complete `git diff inp...HEAD` changes six paths: OscillatorNodes.lean (+504),
OscillatorRemainder.lean (+58/-15), the handoff (+43), and audits 1–3 (+205,+229,+230).
Thus the handoff's claim “New file (only)” and 331-line count describe an older
revision. Its `p2_oi_range_ab` and `p2_ar_collect` names are also stale: the current
exports are `osc_iter_range_ab` and `p2_ar_apply_collect`. These are documentation
notes. They do not change the four-node contract or authorize a wider closure claim.
All exports in the assigned module are UNSIGNED. Provider/frozen-type and seal-body
probes are inapplicable. Already closed nodes and explicitly excluded oi-transfer
are not missing deliverables in this restricted audit.

## Per-node and declaration verdicts

All names are in `KAM.Planetary`. Bare lines refer to OscillatorNodes.lean.

| Node / role | Declaration and line | Verdict | Evidence / qualification |
|---|---|---|---|
| stepP:p2:oi-ratio | `p2_oi_ratio` :230 | PASS | Internally constructs the source generator and its actual weighted supremum; exact eta/theta identity, scalar comparison, factorial bounds and composition factor on the two-loss domain. |
| oi-ratio, integral clause | `p2_oi_ratio_integral` :268 | PASS | Same actual norm and generator, integral class and exact theta factor. Joint continuity premises are those of N composition-integral. |
| stepP:p2:oi-range | `p2_oi_range` :304 | PASS | Actual theta numerical chain and series/composition identity, same-map displacements on U, and remainder on V with `(1-theta_phi)⁻¹`. Audit-3 F1 repaired. |
| oi-range projection helper | `osc_iter_range_ab` :174 | PASS as helper | Original source data produce the displayed oscillator iterative lemma's delta-majorant version of (a),(b); final node strengthens the remainder separately. |
| stepP:p2:ar-apply | `p2_ar_apply` :418 | PASS WITH NOTES | Internally derives OscHyp and exports Hamiltonian/zero-mode identities with analytic, injective, symplectic, periodic map and theta-independent g. Selected view; N1. |
| stepP:p2:ar-collect, jointly with ar-apply | `p2_ar_apply_collect` :454 | PASS WITH NOTES | Single shared Psi,g,fs,Pt, Hamiltonian and coefficient identities, remainder formula/class, exact summed bound and exponential equality. N1. |
| conditional adapter | `OscComposeData.ofDeltaBound` :39 | PASS as helper | Derives the composition smallness field from explicit generator majorant and source smallness; distinct helper name. |
| conditional ratio helper | `osc_ratio_of_gen_bound` :55 | PASS as helper | Generic admissible-generator estimate; no claim to construct the source generator. |
| conditional integral helper | `osc_ratio_integral_of_gen_bound` :99 | PASS as helper | Uniform class/bound and joint continuity yield the stated integral estimate. |
| conditional range helper | `osc_range_of_gen_bound` :124 | PASS as helper | Generic majorant numerical chain and series identity; source-generator facts supplied inside node export. |
| private norm helper | `osc_actual_norm` :212 | PASS | Finite supremum is a valid nonnegative bound at most the supplied nonnegative majorant. |
| private scalar helper | `ar_exp_kappa` :367 | PASS | Positive epsilon,s0 and exact K formula imply exp(-kappa/6)=epsilon^5. |
| private premise adapter | `ar_hyp` :379 | PASS | Derives K positivity, kappa budget, class/bound/reality of mu P and R2 smallness internally. |
| changed dependency, not a node export | `osc_remainder_of_gen_bound`, OscillatorRemainder.lean:37 | PASS for applicability | Conditional generator-bound helper; actual generator class/bound/nonnegativity and comparison are produced inside `p2_oi_range`, never exposed as node premises. |
| preserved dependency interface | `osc_remainder_bound`, OscillatorRemainder.lean:119 | PASS for compatibility | Original inp declaration type elaborates against the revised theorem; original delta-majorant constant preserved. |

The slice is complete for oi-ratio, oi-range, ar-apply and ar-collect at their literal
NODE conclusions. Generic test-function data remain universally quantified before
the conclusions; source inputs precede every iteration index and existential
averaging witness. There are no existential constants with enlarged dependence.
Independent universal data may be reordered without changing scope; K is constrained
by its exact formula before the averaging witnesses are selected.

## Source-premise and binder review

Authority: DEPGRAPH :3757–3759 (ratio), :3790–3792 (range), :4009–4011 (apply),
:4038–4040 (collect), blueprint p2 :167–170, :183–194, :222–237, and N p5
composition-integral :203–204. The finite g decomposition is the inherited N p6
setting, not a previously proved result supplied as a premise.

The following table expands each logical input of the named node exports. Rows
shared by several exports apply separately to each occurrence. `R`, `I`, `G`, `A`,
`C` denote ratio, integral, range, ar-apply and joint apply/collect respectively.
Class predicates are expanded into holomorphy and periodicity; bound predicates
into summability and the pointwise weighted bound. DivisorBound expands to the
literal complex-neighbourhood nonresonance inequality for every allowed nonzero k.
RealOn expands to reality at real points of the specified domain.

| Input / expanded field | Exports | Bin | Source |
|---|---|---|---|
| hn: n >= 1 | R,I,G,A,C | SOURCE | p2 :167, :223 |
| hm: m >= 1 | R,I,G,A,C | SOURCE | p2 :167, :223 |
| hα: alpha > 0 | R,I,G,A,C | SOURCE | direct-divisor setting, p2 :224–227 |
| hK: K >= 0 | R,I,G | SOURCE | inherited truncation setting |
| widths: rho > 0 | R,I,G | SOURCE | p2 :183–185, inherited N iterative |
| widths: 2 rho < r | R,I,G | SOURCE | same |
| widths: rhop > 0 | R,I,G | SOURCE | same |
| widths: 2 rhop < rp | R,I,G | SOURCE | same |
| widths: rhoq > 0 | R,I,G | SOURCE | same |
| widths: 2 rhoq < rq | R,I,G | SOURCE | same |
| widths: sigma > 0 | R,I,G | SOURCE | same |
| widths: 2 sigma < S | R,I,G | SOURCE | same |
| hh: h holomorphic on actionNbhd | R,I,G,A,C | SOURCE | direct setting; p2 :223 |
| hdiv: nonresonance on actionNbhd | R,I,G,A,C | SOURCE | direct setting; R1, p2 :226 |
| hf: f holomorphic | R,I,G | SOURCE | p2 :184–185 |
| hf: f fast-periodic | R,I,G | SOURCE | oscillator analytic class, p2 :167–169 |
| hδ: f weighted series summable at every parameter | R,I,G | SOURCE | finite weighted norm, p2 :185 |
| hδ: f weighted sums <= delta | R,I,G | SOURCE | same; allows the exact-norm source case |
| hδpos: delta >= 0 | R,I,G | SOURCE | nonnegative finite norm/majorant |
| hsmall: delta <= (2 pi alpha) dnu/(16 b) | R,I,G | SOURCE | p2 :185, :193 |
| hu: u holomorphic on O | R,G | SOURCE | test function in oi-ratio / N composition |
| hu: u fast-periodic on O | R,G | SOURCE | same class |
| hbu: u weighted series summable on O | R,G | SOURCE | same finite norm |
| hbu: u weighted sums <= A | R,G | SOURCE | same finite norm/majorant |
| hA: A >= 0 | R,G | SOURCE | norm majorant |
| hB: B >= 0 | I | SOURCE | uniform finite norm majorant, N p5 :204 |
| hv: each v(t) holomorphic on O | I | SOURCE | N p5 :204 |
| hv: each v(t) fast-periodic on O | I | SOURCE | same class |
| hv: each v(t) weighted series summable on O | I | SOURCE | same finite norm |
| hv: each v(t) weighted sums <= B | I | SOURCE | same uniform bound |
| hcv: joint continuity of v | I | SOURCE | explicitly N p5 :204 |
| hDc: joint continuity of Dv | I | SOURCE | explicitly N p5 :204 |
| hg: each gj holomorphic | G | SOURCE | inherited finite decomposition |
| hg: each gj fast-periodic | G | SOURCE | same |
| hg: each gj weighted series summable | G | SOURCE | same |
| hg: each gj weighted sums <= Mj | G | SOURCE | same |
| hg: r <= rj | G | SOURCE | same outer-width data |
| hg: rp <= rpj | G | SOURCE | same |
| hg: rq <= rqj | G | SOURCE | same |
| hg: S <= Sj | G | SOURCE | same |
| hr: r > 0 | A,C | SOURCE | p2 :223 |
| hε₀: epsilon0 > 0 | A,C | SOURCE | p2 :223 |
| hs₀: s0 > 0 | A,C | SOURCE | p2 :223 |
| hε: epsilon > 0 | A,C | SOURCE | p2 :223 |
| hε: epsilon < exp(-1/5) | A,C | SOURCE | p2 :223 |
| hμ: mu > 0 | A,C | SOURCE | p2 :223 |
| hK: K = 15/(pi s0) log(1/epsilon) | A,C | SOURCE | p2 :224 |
| hreal: h real on real actions | A,C | SOURCE | p2 :223 |
| hPc: P holomorphic | A,C | SOURCE | p2 :223 |
| hPc: P fast-periodic | A,C | SOURCE | same class |
| hPb: P weighted series summable | A,C | SOURCE | same finite norm |
| hPb: P weighted sums <= 1 | A,C | SOURCE | p2 :223 |
| hPr: P real | A,C | SOURCE | p2 :223 |
| hR2: 2^12 b K s0 mu <= alpha d | A,C | SOURCE | p2 :227 |

Expanded logical-input counts: R has SOURCE=25, I has SOURCE=27, G has SOURCE=33,
and A,C each have SOURCE=19; all have STANDING=0, RULED=0, EXCESS=0.
The integral count includes all four fields of hv, not just its two bundled predicates.
Typing data are separately universally quantified: R has 18 bindings
(n,m,D,r,rp,rq,S,rho,rhop,rhoq,sigma,A,delta,u,K,alpha,h,f); I replaces A,u by
B,v (18); G adds J,gj,rj,rpj,rqj,Sj,Mj (25); A,C have
n,m,D,r,epsilon0,s0,epsilon,mu,K,alpha,h,P (12). All are TYPING; there are no
new instance assumptions. Bound variables internal to periodicity/nonresonance,
time families and decomposition fields are universal indices, not extra premises.

The generic `_of_gen_bound` helpers deliberately accept generator data as conditional
inputs under distinct names. They are not counted as source-generator closure.
OscComposeData has only the seven source-data fields read in its structure;
OscHyp has dimension/radius positivity, budget, holomorphy, reality, class, bound,
divisor and smallness fields. The named exports construct both internally.
No flow, remainder, convergence, map or other conclusion is assumed as a bundled field.

## Audit-3 F1 repair and changed dependency

DEPGRAPH :3792 and blueprint p2 :193 require the replacement denominator
“1-theta_phi”, with theta_phi defined from the actual generator norm at :3759 /
p2 :192. The current node defines that norm at :319, theta at :320, and uses
`(1 - θ)⁻¹` in its remainder estimate at :344. The proof at :352–359 derives
generator class/majorant using `oscGen_class_bound`, then obtains its actual-norm
bound, nonnegativity and comparison using `osc_actual_norm`. These facts feed the
new `osc_remainder_of_gen_bound`; they are not new hypotheses of the node.
The displacement projection still comes from `osc_iter_range_ab` for the same
`oscStepMap`, which unfolds to the identical generator flow on O.

The dependency's generalized proof keeps the decomposition and numerator at the
source delta-majorant while applying the composition-integral and tail-composition
bounds with the supplied generator bound Phi. In particular its integral numerator
is still `2b (delta/(2 pi alpha))/d * (Rsum+delta)`; it does not silently replace a
previously established numerator by a smaller actual-norm numerator. Only the
composition factor becomes `(1-oscTheta m Phi d)⁻¹`. The final algebra factors out
delta and reproduces precisely the node's numerator. For a nonempty target parameter
set, Mj nonnegativity follows by evaluating the original bounds there; empty target
sets are discharged vacuously. No D.Nonempty or Mj positivity hypothesis is added.
The original `osc_remainder_bound` specializes Phi back to delta/(2 pi alpha), so
its interface and every existing caller retain their former constant.

This resolves the literal mismatch without choosing between two different ratios.
The displayed iterative lemma at p2 :187 is the weaker delta-majorant consequence;
the proof at :193 retains the stronger actual-generator factor. These are compatible,
not contradictory. The intermediate estimate is now actually exported.

## Definitions, carriers and selected views

No new def, abbrev or structure is introduced in the assigned module or changed
dependency. Local lets are literal formulas: source generator, actual supremum,
arithmetic constants, domains, finite g sum, Hamiltonian difference fp and integral.
The weighted sum uses exp(2 pi S |k|_1), geometric widths and period-one Fourier
indices `Fin n -> Z`; the phase has Pi norms and order ((theta,q),(I,p)), and
oscPack puts the parameters in (I,p,q) order. No EuclideanSpace or altered norm.

`osc_actual_norm` first proves BddAbove of the image from the valid landed bound.
The WSummable component is retained at every parameter; total tsum is never used
as a replacement for convergence. `le_csSup` gives each pointwise bound;
`Real.sSup_nonneg` and `Real.sSup_le` cover the empty parameter image as well
(real sSup empty is zero). There is no invented nonempty-domain premise, choice of
an arbitrary witness, or fallback relied on for an on-domain assertion.
Generic composition controls u on O and its composition on V, both with the exact
source flow. Displacements remain on the larger three-halves-loss domain U.
The landed summable-series construction used in composition supplies genuine
convergence; the displayed total tsum is not its sole justification.

Definition classification for the new local formulas:
BODY_MATCH: OK; PUBLIC_CARRIER: OK (no new public object);
WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL;
CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.
This does not re-audit every inherited total flow or Fourier definition globally.
All assertions about their analytic behavior are restricted to the sourced domains.

N1: ar-apply/collect are selected views. Their literal NODE conclusions are the
identities at p2 :236 and the collected summed bound at :237, which are present.
The joint export preserves one Psi,g,fs,Pt via a single `averaged_remainder`
application. Neither export states all reality, separate correction/tail bounds or
component-displacement conclusions of the full proposition at :229–232. In
particular the map-realness clause is omitted. Consumers needing those clauses
must use the full landed proposition, not substitute these selected exports.
This is the reason for PASS WITH NOTES, not a missing assigned NODE conclusion.

## Independent verification

All Lean/Lake invocations were serialized, with LEAN_NUM_THREADS=1 and nice -n 5.
No library rebuild, cache fetch, clean, update or generated-root regeneration.

Targeted build, exit 0:

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp2r KAM.Planetary.Averaging.OscillatorNodes
[inp-gate] slot 1 acquired 03:13:39 for KAM.Planetary.Averaging.OscillatorNodes
⚠ [9164/9165] Replayed KAM.Planetary.Averaging.OscillatorFinite
Build completed successfully (9165 jobs).
```

The only build warnings were the existing unused hμ at OscillatorFinite.lean:159:37
and hP at :161:5. No warning was emitted from the assigned module.

Fresh scratch probe, exit 0:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPP2Audit4.lean
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
'KAM.Planetary.osc_remainder_of_gen_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same probe copies the original declaration header of osc_remainder_bound from
`git show inp:KAM/Planetary/Averaging/OscillatorRemainder.lean`, under the fresh name
`audit4_original_remainder_signature`, and proves it by
`exact osc_remainder_bound hn hm hα hK hwidths hh hdiv hf hδ hδpos hsmall hg`.
This checks actual original-type consumption after the dependency refactor. It
elaborated with only unused-let warnings at scratch lines 38,39,40,42,43 for
phi,O,U,u,V inherited from the original type. The scratch file is removed after use.

Kernel replay, one invocation, exit 0:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorNodes KAM.Planetary.Averaging.OscillatorRemainder
replaying KAM.Planetary.Averaging.OscillatorRemainder
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

The sole lint failure is the generated root staleness explicitly permitted by the
brief and handoff; it is not counted as a finding. No substantive lint failure
was suppressed. Forbidden-token/resource-override, EuclideanSpace, module,
line-width and file-size checks produced no additional failure.

Protected-path and whitespace commands, both exit 0 and no output:

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Static checks: OscillatorNodes has 504 lines, maximum Unicode width 98;
OscillatorRemainder has 165 lines, maximum width 100. Both retain the required
copyright, module, public interface imports, docstring and public section.
New public helper short names are unique in production declaration searches;
OscComposeData.ofDeltaBound is explicitly qualified. No harmful root shadow found.

Recursive local import closure has 119 modules, zero providers, zero frozen theorem
modules. The 12 frozen imports are definitions, each with exactly one manifest owner,
state SEALED and matching full-file SHA256: ActionNbhd, ComplexStrip,
HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip,
IsRealOnReals, OmegaZero, SymplecticForm, Planetary/Fast, Planetary/Phase,
Planetary/Slow. No DRAFT_SORRY import or sorryAx in any audited public export.

## Uncertainties, suspected errata and deviations

No new suspected pinned-source erratum or frozen-statement defect was found.
The p2 :187 delta-majorant versus :193 actual-generator intermediate bound is now
faithfully distinguished in Lean. The source gap explicitly recorded at p2 :196
(“the extension is stated by its (short) list of changes, not rewritten in N”)
remains outside this restricted node-export audit; this report does not freshly
certify CP10/Pos93 PDFs or re-audit the whole oscillator extension.

Documentation deviations: stale handoff file inventory, counts and export names;
the helper docstring at OscillatorNodes :172 says “factor 1 - theta_phi”, while its
own conclusion :202 is the delta-majorant factor. The final node :344 now has the
actual theta_phi factor. This is a local comment imprecision, not a proof failure.
The additional dependency edit is explicitly recorded above instead of hidden by
the handoff's single-file claim. No source, graph, frozen file, manifest, generated
file, ledger or git state was edited by this auditor. The only repository deliverable
is this report at the user-specified absolute path.
