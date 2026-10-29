# GAP-P8c independent package audit 3

Date: 2026-10-29 UTC. Worktree: `/root/code/KAM-inp-gp8c`.

**Overall: PASS WITH NOTES for all six nodes under the explicit OVERNIGHT 02:25 ruling.**
The designated evenness export is now `p8_evenness_joint`, which supplies the full
source perturbation-analytic conclusion and the evenness conclusion at one jointly
chosen radius. Audit-2 F1 is closed under that ruling; F2/F3 remain closed. The
legacy `p8_evenness_full` alone still does not state the neighbourhood contract.
This report does not assert that its type changed or that the old export alone passed.

No frozen theorem or provider is implemented by this package. Seal readiness,
provider/frozen equality, and seal-body checks are N/A. No physical headline,
external graph amendment, or downstream consumer closure is certified.

## Scope, authority and frozen inputs

Focused tier-2, refute-first source correspondence and Lean package audit, using
`lean-statement-audit` and `manuscript-audit`. The permission envelope is the user's
report-only instruction plus transient worktree `.lake/abi-scratch/` probes, targeted
build, kernel replay and lint. No source repair, commit, push, or delegation.
The user's absolute report destination overrides the brief's main-worktree default.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the package brief, track-P statement,
GAP-PLAN-P.md's GAP-P8c section, both preceding audits, the full current handoff,
the six complete NODE records, their cited blueprint statements and proofs, and
supporting definitions/proofs needed to establish the actual meanings.

Snapshot HEAD: `9f7379ce713c5703c7d1d0fab91a9dbcd23e4fa2`.
Initial comparison `inp`: `d6fa120cc475a689316bdbf716406c2fcc856747`.
`git diff inp...HEAD` warns of multiple merge bases and selects
`bc356ad4f4046c04a35a0c7bd15b8efeb3e39048`; the other merge base is
`537fc2a837002555fbe2766678b1c8454274228f`.
These hashes, together with the following SHA256 values, define snapshot audit3-v1:

| Input | SHA256 |
|---|---|
| `KAM/Planetary/SecularForm/EvenIdentNodes.lean` | `8fa9f802c49d846c9288f594e8c008d4fec23a2caecfa89a7ea5b6e7b8664dc2` |
| Working-tree `docs/tracks/P/audits/GAP-P8c-handoff.md` | `2756a1db42bc2553b05365aa15c0e986c5ca5fca57b546b33c54becd53873321` |
| `docs/graph/P/DEPGRAPH.md` | `3efb008b21f505c3a02d59b29f4e92e08d886cb76dd3313f2d13d4ff079b7b01` |
| `blueprint-P/parts/p8-secular-form.tex` | `413806b9fcc86156e0b241da85668677b44bf142897c7039940504a50ae1febc` |

The handoff already had one uncommitted line when this audit began, explicitly:

> a p8 node export may choose its own radius r provided it states, at that same r,
> the full perturbation-analytic conclusion together with the node's own conclusions.
> p8_evenness_joint is the evenness export in that form.

This is an orchestrator ruling for owner review under D29, not a new owner approval
of a frozen statement. It explicitly supersedes the original table's evenness mapping.
The earlier handoff size, revision and arithmetic-only descriptions are stale.

Inspected the full three-dot diff: the only Lean change is the 803-line target
module. The remaining changes are two previous audits, the handoff, graph/packet
status and note updates, and the P-A001 extension-agreement amendment in the graph
and amendments packet. These include other packages' PROVED/BYPASSED labels;
this audit does not certify those labels. None changes the six audited NODE contracts.
No matching entry for these exports occurs in project `*Signatures.lean`: all are
UNSIGNED; no signed declaration changed. Only the nominated module is audited
for package correctness; inherited dependencies are not re-certified wholesale.

## Per-node verdicts

All names in this table have prefix `KAM.Planetary.SecularForm`.
Graph and blueprint line numbers refer to audit3-v1 above.

| Node | Export; Lean lines | Graph; blueprint lines | Verdict | Source correspondence |
|---|---|---|---|---|
| `stepP:p8:ev-tay` | `p8_ev_tay`; 224–243 | 15172–15200; 83 | PASS | Both actual models, all odd jets zero, critical origin, every diagonal jet invariant under arbitrary rotation and eta reflection. These generate diagonal O(2); factorial rescaling gives the homogeneous Taylor polynomial. Analyticity is proved internally, not supplied as a new premise. |
| `stepP:p8:ev-quad` | `p8_ev_quad`; 248–270 | 15202–15228; 84 | PASS | Full-n mixed Hessian block vanishes and eta-eta block equals xi-xi. Basis evaluation gives B=0, C=A in the canonical symmetric Taylor representation. |
| `bpP:p8:evenness` | `p8_evenness_joint`; 449–531 | 15112–15141; 75–84 | PASS WITH NOTES | At one positive radius, from physical data and ordered base axes alone: full perturbation-analytic conclusion, four invariances, odd-jet vanishing, criticality, O(2)-invariant Taylor parts, half-Hessian quadratic formula, symmetric analytic A and analytic jets on the entire projected action slice. Radius choice follows the explicit 02:25 ruling. |
| `bpP:p8:identities` | `p8_identities_full`; 671–676 | 15526–15554; 129–140 | PASS | Exactly I1 and I2 for every alpha in [0,1), including zero, with the source's normalized integral and actual derivatives. |
| `stepP:p8:id-1` | `p8_id1`; 692–736 | 15556–15583; 138 | PASS | Source index Q=q+1: actual beta monomial differentiated, multiplier 2Q(2Q+1), Pochhammer coefficient equality, and identification with the RHS monomial of degree 2Q-1. |
| `stepP:p8:id-2` | `p8_id2`; 743–797 | 15585–15612; 139 | PASS | Zero branch and positive branch Q=r+1 are both included, with actual differentiated monomials, multiplier 2Q(2Q+3), Pochhammer equality, and alpha times the RHS term; its degree 2r+3 is distinct from 1. |

Completeness: all six design nodes are established. The coefficient exports are
stronger in alpha (all real alpha for the finite monomial identities). Reordering
q and alpha does not widen any constant dependence: there are no existential
constants. The inherited Laplace series identification/termwise differentiation
provides the link to the actual analytic functions; these coefficient nodes do
not separately require a new HasSum export. O(2) invariance is not a claim of the
separate invariant-theory/Weyl node about generation by dot products.

## Radius finding: discovery and adversarial refutation

Audit-2 F1 concerned separate domains and a smaller witness without a joint full
analytic conclusion. The old `p8_evenness_full` (325–351) remains a valid chart-domain
and action-domain helper, and `p8_evenness_nbhd` (395–442) remains a valid smaller-radius
helper. Neither is silently relabelled as the new source export.

The new joint proof obtains `perturbation_analytic_full D ha` at 504, proves the
action-domain neighbourhood from physical base data, and returns `min r0 epsilon`.
The action-slice inclusion is proved at 512–520 using the sup norm and positive
ordered axes. The radius precedes model choice, points, angles, all jet orders and
all polynomial arguments. It depends only on D and a. No analytic output, symmetry,
Hessian identity, jet equality or chosen radius is a hypothesis.

Refutation attempt: compare every analytic field with AnalyticNodes.lean:534–573,
then try to consume them and evenness at the SAME witness in Lean. The new export
contains separation and its real physical identification/collision-free consequence;
perturbation holomorphy, joint continuity, angle periodicity, real identification;
secular holomorphy, real identification, real analyticity; and both real and complex
derivative-average formulae. The proof restricts each field along `hsub`/`hsubR`
(525–528); it does not retain an unrelated existential witness. The stronger inherited
bound r0 < rho/2 is exposed only as r < rho; the blueprint requires r < rho0, so
this is not a source weakening. Integrability, which is not an explicit conjunct
of `perturbation_analytic_full`, follows at this same witness from joint continuity,
real identification and compactness of the angular cell; the transient probe checks
this consequence without assuming it. The earlier proposed blocker is refuted under
the recorded new ruling. No surviving package blocker was found.

## Expanded inputs and definition audit

The following rows classify each node-input binder/expanded Data field; grouped
exports share precisely these binders. Counts are per row, not per repeated use.
All source locators are in blueprint p8:17–22, 75–84, 129–139 and graph conv#data.

| Binder or expanded field | Bin | Count | Meaning |
|---|---|---:|---|
| `{n : Nat}` | TYPING | 1 | Finite dimension. |
| `D.G`, `D.m0`, `D.m` | SOURCE | 3 | Physical data, with kappa=G*m0. |
| `D.hG`, `D.hm0`, `D.hm`, `D.hn` | SOURCE | 4 | Positive G, m0, each mass and n>=1; no analytic fields. |
| `{a : Vec n}`, `ha : a in axes n` | SOURCE | 2 | Base axes; ha expands to positivity and StrictMono. |
| `{I : Vec n}`, `hI : I in actionDomain D` | SOURCE | 2 | Action of positive ordered axes; hI expands to existence of those axes and action equality. |
| `b : Bool` | SOURCE | 1 | The two actual source models. |
| `{alpha : Real}`, `hAlpha : alpha in Ico 0 1` | SOURCE | 2 | Literal endpoint interval; hAlpha expands to 0<=alpha and alpha<1. |
| `q : Nat`, `r : Nat` | SOURCE | 2 | Source coefficient indices, shifted to cover Q>=1. |

Row-count totals: SOURCE 16, TYPING 1, STANDING 0, RULED 0, EXCESS 0.
The radius ruling changes output witness scope, not an input binder. Variables in
conclusions (jet orders, points, angles and vectors) are universally quantified outputs.
Generic helper inputs below are their explicit local mathematical hypotheses, not
inputs to any source-node export. No bundled hard step is hidden in Data.

Exactly four new definitions, all literal linear operators on their whole carrier:

| Definition; line | Body/carrier verdict | Intended object |
|---|---|---|
| `slowRotCLM`; 75 | PASS | Continuous linear map with cos/sin rotation blocks. |
| `slowRotCLE`; 86 | PASS | Same map with inverse rotation by -theta; inverse identities proved. |
| `slowReflCLE`; 108 | PASS | Product of identity and negation, eta reflection. |
| `slowEmbCLM`; 157 | PASS | Continuous linear reordering (I,(xi,eta)) -> (xi,I,eta). |

For each definition: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS
N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A;
DEFINITION_VERDICT PASS. No fallback, arbitrary selected response or invented off-domain
branch. Four defining-equation examples elaborate in the transient probe. Vec is
literally Fin n -> Real; physical planeLength is sqrt(sum of two squares), and the
ambient Pi norm is used only for neighbourhood inclusion. The secular average is
the frozen literal normalized angular integral. No norm or coordinate-order switch.

## Every other public theorem

All rows PASS as the helper actually stated. The first two names have prefix
`KAM.Planetary`; all others have prefix `KAM.Planetary.SecularForm`. Together with
the six source exports above this inventories all 34 public theorems.

| Declaration; line | Meaning and limitation |
|---|---|
| `iteratedFDeriv_invariant_of_equiv`; 47 | Local equality under a linear equivalence implies tensor equivariance; arbitrary normed real spaces. |
| `fderiv_fderiv_invariant_of_equiv`; 63 | Bilinear second derivative specialization. |
| `slowRotCLM_apply`; 81 | Literal rotation formula. |
| `slowRotCLE_apply`; 105 | Literal underlying map. |
| `slowReflCLE_apply`; 111 | Literal reflection formula. |
| `eventually_mem_slowDom_zero`; 114 | Positive base actions give a chart neighbourhood. |
| `slowSecular_eventually_rotate`; 134 | Local invariance of actual secular function. |
| `slowSecular_eventually_reflect`; 147 | Local reflection invariance. |
| `slowEmbCLM_apply`; 164 | Coordinate embedding equation. |
| `analyticAt_slowSecular_jet`; 168 | Partial-jet analyticity from proved joint analyticity and continuous linear composition. |
| `analyticOnNhd_slowSecular_jet`; 217 | The same on actionDomain. |
| `analyticAt_slowSecular_fix`; 273 | Fixed model at the circular base. |
| `slowSecular_fix_second_jet`; 284 | Half-Hessian equals the landed quadratic form, using the proved remainder jet. |
| `coeffs_transpose`; 305 | Symmetry on all axes vectors; stronger domain is harmless. |
| `slowSecular_second_jet`; 310 | Both models, internally supplied same_jets and source action inversion. |
| `p8_evenness_full`; 325 | Valid global chart/action helper; alone still not the neighbourhood contract. |
| `eventually_mem_actionDomain`; 358 | Positive ordered inverse-axis neighbourhood, constructed. |
| `p8_evenness_nbhd`; 395 | Valid partial joint bundle, superseded as node export by p8_evenness_joint. |
| `laplace_def_neg_arg`; 536 | Literal integral parity via pi translation, all real s/alpha and natural k. |
| `laplaceC_neg`; 563 | Parity of the actual total series definition. |
| `laplace_def_eq_re`; 571 | Real integral equals real part of complex series on (-1,1), s>0. |
| `analyticAt_laplace_def_zero`; 585 | Two-sided analytic germ of the actual integral, justifying endpoint derivatives. |
| `analyticAt_iteratedDeriv_two`; 599 | Analytic second derivative of an analytic real function. |
| `eq_zero_of_continuousAt_of_zero_Ioo`; 607 | Endpoint zero by continuity and one-sided limit uniqueness. |
| `p8_identity_one`; 618 | Literal I1 on [0,1), not alpha times I1. |
| `p8_identity_two`; 645 | Literal I2 on [0,1). |
| `deriv_monomial_succ`; 679 | Derivative of c*x^(p+1). |
| `iteratedDeriv_two_eq_deriv`; 685 | Actual second-derivative identity. |

## Verification receipts

All Lean-bearing commands are serialized with `LEAN_NUM_THREADS=1`, nice -n 5.
No clean, cache fetch, update, heartbeat/recursion/synthesis override, generated-root
regeneration or state-changing git command was used.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8c KAM.Planetary.SecularForm.EvenIdentNodes
   ```

   Exit 0. Gate: `[inp-gate] slot 1 acquired 02:29:40 for KAM.Planetary.SecularForm.EvenIdentNodes`.
   Final output: `Build completed successfully (9175 jobs).`
   Inherited warnings were replayed (unused variables in Kepler/Chart/Hamiltonian
   dependencies, deprecated ite_cond_eq_false in Coefficients); none in the target.

2. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.EvenIdentNodes
   ```

   Exit 0. Complete output: `replaying KAM.Planetary.SecularForm.EvenIdentNodes`.

3. Fresh exact-use, definition and axiom probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GP8cAudit3.lean > .lake/abi-scratch/GP8cAudit3-probe.log 2>&1
   ```

   Exit 0 on the final refactored probe; no errors or warnings. All 34 public
   theorems have fully elaborated type checks and exactly the axiom receipt
   `depends on axioms: [propext, Classical.choice, Quot.sound]`.
   Eleven examples pass: general I1, I1/I2 at zero, both positive differentiated
   monomial identities, four literal defining equations, the complete analytic
   package with four invariances at one witness, and integrability at the joint
   witness. No sorryAx or project axiom.

   The initial large combined consumption probe reached the default
   200000-heartbeat limit at whnf/isDefEq. This scratch design signal was addressed
   by naming the analytic predicate, splitting conjunction fields, and restoring
   the source namespace/scopes (the copied periodicity formula needed Real.pi).
   No budget was increased; no production declaration was changed.

4. Project import closure: 129 modules, 56 frozen modules. All 56 are manifest-owned
   SEALED definitions (lookup by manifest path); no provider, frozen theorem or
   DRAFT_SORRY import. The frozen-anchor guard/ABI checks below independently pass.

5. Source hygiene: 803 lines, maximum Unicode line length 100; required copyright,
   module, public imports, module documentation and exposed public section present.
   Four literal definitions, 34 public theorems, no new structure/abbrev. No forbidden
   proof escape, resource override or EuclideanSpace. Source declaration-name scan
   finds no reused short name elsewhere in KAM; no harmful root shadow.
   `git diff inp...HEAD --check` exits 0. Protected-path diff is empty:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

6. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/GP8cAudit3-lint.log 2>&1
   ```

   Exit 1; complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1196 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   PASS modulo the brief's expressly permitted generated-root exception; no other
   lint failure. The generated root was not edited.

## Source defects, deviations and limits

Blueprint p8:76 says `S(R_theta(xi,eta),Lambda)=S(xi,Lambda,eta)` for S declared
on the box of p8:22. The box is not invariant: a planet's (0.9*r,0.9*r) rotates
by pi/4 to (0,0.9*sqrt(2)*r), outside it. A box-only definition needs a transformed-point
guard or a larger-domain interpretation. The graph's NOTE at 15141 already records
this. Here S is the actual globally defined integral; chart-domain invariance proves
the stronger equality, and the neighbourhood conclusion uses it. This is a carried
blueprint domain issue, not a new defect in the physical pinned source.

The joint-radius reformulation is explicit and authorized by the recorded overnight
ruling, pending owner review. No new source premise or unrecorded implementation
deviation was introduced. The graph still says NOT_STARTED for these nodes and
names older gaps; this report provides evidence for the orchestrator, not an edit
to those statuses. Frozen-anchor sealing and later consumers remain separate work.

Final integrity: HEAD and all four snapshot hashes above are unchanged. During
the audit inp advanced externally to `91dc441efbdc614303b82bef60b36c8fbc45819b`.
Rechecked the full three-dot diff: same 15 files, 1796 insertions and 342 deletions;
selected merge base unchanged, whitespace check passes, protected-path diff empty.
Only this report was created outside scratch; the pre-existing handoff modification
was preserved byte-for-byte. The transient probe and both scratch logs were removed.
Report whitespace validation passes. No source, frozen file, manifest, graph or
generated file was edited.

Final verdict: **PASS WITH NOTES for GAP-P8c under OVERNIGHT 02:25; all six nodes pass.**
