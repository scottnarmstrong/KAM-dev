# GAP-P8c independent package audit 1

Audit date: 2026-10-29 (UTC). Worktree: `/root/code/KAM-inp-gp8c`.
Audited HEAD: `5e9c21463b805a8a311ffea3421714830b7756b5`.
Comparison branch `inp`: `8dc8bedc37b2b4dad2163b79fbcf35ff51fdffdb`.

**Overall: FAIL for literal graph-node completion.** The Lean module is sound under its
stated types, but three unsigned exports do not state the entire literal node contract:
`bpP:p8:evenness`, `stepP:p8:id-1`, and `stepP:p8:id-2`. The other three nodes pass.
No frozen theorem is being sealed by this package; provider/frozen-type and seal-body
checks are consequently N/A. This verdict does not claim a false Lean theorem.

Scope is ONLY `KAM/Planetary/SecularForm/EvenIdentNodes.lean`. Read the local rules,
PLAN, DECISIONS, track P statement, package brief, handoff including AUDIT FOCUS,
GAP-PLAN-P.md:359–369, P810 design, and all six NODE records and their cited blueprint
lines. The prompt's exact report path overrides the brief's default main-worktree path.
No implementation, graph, manifest, frozen file, generated root, or README was edited.

`git diff inp...HEAD` was inspected in full: exactly one added file, 536 lines.
The handoff was already untracked on entry. All exports here are UNSIGNED: no matching
entry for the new names was found in the available `*Signatures.lean` files, including
P810Signatures and P11BSignatures. Existing signed declarations are unchanged.

## Per-node source fidelity

Names in this table have prefix `KAM.Planetary.SecularForm.`. Lean line numbers refer
to EvenIdentNodes.lean. Graph line numbers refer to docs/graph/P/DEPGRAPH.md.

| Node | Export / Lean lines | Source record; blueprint lines | Verdict | Reason |
|---|---|---|---|---|
| `stepP:p8:ev-tay` | `p8_ev_tay`, 223–242 | graph 15172–15200; p8-secular-form.tex:83 | PASS | Both actual secular models, every ordered positive action vector: all odd tensors vanish, first derivative vanishes, and every diagonal jet is invariant under rotation and reflection. These generators give the source diagonal O(2) invariance. Evaluating the continuous multilinear jet on repeated u is the homogeneous Taylor polynomial, up to the invariant factorial scalar. No invariant-theory/dot-product claim is required by this node. Analyticity and local invariances are proved inside supporting lemmas, not required as output-shaped premises. |
| `stepP:p8:ev-quad` | `p8_ev_quad`, 247–269 | graph 15202–15228; blueprint:84 | PASS | Zero mixed bilinear block and equality of the two diagonal Hessian blocks give B=0 and C=A in canonical Taylor/Hessian coordinates. Basis-vector specialization gives every matrix entry; dividing the Hessian by 2 does not affect these equalities. Holds for full n and both models. Reflection and the quarter turn are built inside the proof. |
| `bpP:p8:evenness` | `p8_evenness_full`, 324–350 | graph 15112–15141, especially 15119–15121; blueprint:75–80 | FAIL | The invariance component is a valid stronger chart-domain statement. The remaining Taylor, quadratic and coefficient-analyticity components are instead restricted to `actionDomain D`. The named bundle never quantifies the source base axes and shared analytic polydisc radius, nor connects all actions in that polydisc to this action domain. Thus the entire source neighbourhood conclusion, with the source's common radius and quantifier scope, is not exported. See F1. |
| `bpP:p8:identities` | `p8_identities_full`, 491–496; `p8_identity_one`, 438–461; `p8_identity_two`, 465–488 | graph 15526–15554; blueprint:129–140 | PASS | Exactly I1 and I2 for every α in [0,1), including 0, with the literal normalized Laplace integral. Positive α uses landed identities; continuity at 0 is proved from analyticity of the integral on a two-sided neighbourhood. No division by α at the endpoint and no extra premise. |
| `stepP:p8:id-1` | `p8_id1`, 501–512 | graph 15556–15582, especially 15563–15565; blueprint:138 | FAIL | Correct reindexed Pochhammer coefficient equality and an RHS series-term formula, but no conclusion identifying the coefficient on the differentiated LHS. The differential operator's effect on the β monomials is absent from the theorem type and its proof. See F2. |
| `stepP:p8:id-2` | `p8_id2`, 519–530 | graph 15585–15611, especially 15592–15594; blueprint:139 | FAIL | Correct positive-index arithmetic and a zero multiplier at q=0; the last conjunct describes an unmultiplied RHS Laplace term. It does not identify the coefficients of the differentiated LHS or export the absence of the α term on the multiplied RHS. See F3. |

The package's six-node list agrees with GAP-PLAN-P.md:360. No seventh graph node is
assigned to this new module. Three passing nodes plus supporting arithmetic and local
geometry do not make the six-node slice complete under the handoff's literal-export rule.

### F1 — source action neighbourhood not assembled

The source order is physical data and base axes a*, then the shared radius ρ* from
perturbation-analytic, then points in N_R(ρ*), then θ. Its coefficient conclusions are
on that action neighbourhood. In contrast, the type at 324–344 has two independent
regions: `slowDom D` for invariances and `actionDomain D` for all Taylor/analyticity claims.
The proof at 345–350 simply assembles those separate statements. It introduces no
source radius or inclusion for its action projection.

This is **not** a complaint that `slowDom` is smaller than the source box. It is larger:
`ModelTransfer.lean:37–60`, `realDisc_subset_slowDom`, restricts the four invariances
back to every source disc with r<rho. That composition was independently elaborated.
Nor is it a claim that the missing neighbourhood result is mathematically false.
`actionDomain` is the image of positive strictly ordered axes under `action`
(Basic.lean:47–50); a suitable action neighbourhood can be obtained by further work.
What is missing under this audit's literal rule is the common source-radius bundle
and the proof that its full action slice satisfies the guards of the exported Taylor
and coefficient results. Do not silently replace the source ρ* by another radius.

Required closeout: export the source neighbourhood conclusion with a radius shared
with the analytic source package, proving the relevant action inclusion inside the
construction; or record an explicit source/domain ruling and audit that exact successor.
The chart-domain strengthening itself needs no repair.

### F2 — id-1 arithmetic is not the differentiated coefficient statement

`p8_id1 q` proves, with source index Q=q+1,

    2Q(2Q+1) ((1/2)_Q/Q!)² = (3/2)_Q (3/2)_(Q-1)/(Q!(Q-1)!),

and unfolds `laplaceTerm (3/2) 1 q`. This arithmetic is correct, and reindexing Q≥1 as
q+1 is exact; absence of an α binder in an α-independent arithmetic identity is not
an error. However, neither conjunct mentions β, its series, differentiation, or a
coefficient operation linking the displayed number to αβ''+2β'. Its proof only uses
`coef1`, an algebraic simplification of `halfCoef`, and `laplaceTerm_eq_coef_mul`.

The source explicitly identifies that LHS coefficient, including the action of
α∂²+2∂ on each monomial. Landed LaplaceIdentities.lean has derivative-series and
monomial-combination tools, but their existence does not put this conclusion in the
unsigned export. A coefficient/series or termwise differential statement tied to the
actual β series must accompany the arithmetic. A `HasSum` formulation is one option,
not a required representation. The already passing I1 theorem remains passing.

### F3 — id-2 omits the operator/shift coefficient identification

`p8_id2 r` proves a q=0 zero multiplier, then the correct arithmetic for q=r+1.
Its last conjunct is the defining term of `laplaceTerm (3/2) 2 r`, of degree 2r+2.
The source RHS is **α times** this series, of degree 2r+3=2q+1. The extra factor α
is not incorrect in the source or contradicted by this theorem; it is simply absent
from the exported term identification. Likewise the source zero α coefficient on
that multiplied RHS is asserted only in the docstring, not in the theorem conclusion.
The proof invokes `coef2`, arithmetic, and the term definition, without identifying
the differential operator on the actual b-series. Require that identification,
including both sides at q=0 and the multiplication/shift for q≥1. Passing I2 does not
turn a different unsigned coefficient theorem into the literal step export.

## Binder / premise audit

There are no conclusion-shaped inputs in any of the six node exports. In particular,
none takes analyticity, invariance, a Hessian identity, `same_jets`, a coefficient
identity, or a differential identity as an input. The failures above are missing
conclusion/scope attachments, not hidden axioms or assumed dependency outputs.

The physical data bundle was expanded, rather than accepted as an uninterpreted
hypothesis. Basic.lean:38–45 supplies exactly the following fields. The source is
blueprint p8:17 and :21, with κ=G*m0; all have bin SOURCE.

| Expanded binder | Bin | Source attachment |
|---|---|---|
| `D.G : ℝ` | SOURCE | positive gravitational constant, p8:17 |
| `D.m0 : ℝ` | SOURCE | positive central mass, p8:17 |
| `D.m : Fin n → ℝ` | SOURCE | planetary masses, p8:17 |
| `D.hG : 0 < D.G` | SOURCE | p8:17 |
| `D.hm0 : 0 < D.m0` | SOURCE | p8:17 |
| `D.hm : ∀ i, 0 < D.m i` | SOURCE | p8:17 |
| `D.hn : 0 < n` | SOURCE | n≥1, p8:17 |

Other outer inputs, one row per binder of the named node declarations:

| Exports | Binder | Bin | Attachment |
|---|---|---|---|
| `p8_ev_tay`, `p8_ev_quad`, `p8_evenness_full` | implicit `n : ℕ` | TYPING | Fin n coordinate dimension; positivity is D.hn |
| `p8_ev_tay`, `p8_ev_quad` | implicit `I : Vec n` | SOURCE | source circular-torus actions |
| `p8_ev_tay`, `p8_ev_quad` | `hI : I ∈ actionDomain D` | SOURCE | positive ordered base axes, p8:21; expands to ∃a∈axes n, action D a=I, with axes=(all a_i>0)∧StrictMono a |
| `p8_ev_tay`, `p8_ev_quad`, `p8_evenness_full` | `b : Bool` | SOURCE | either of the two actual secular models |
| `p8_identities_full` | implicit `α : ℝ` | SOURCE | graph 15534; p8:130 |
| `p8_identities_full` | `hα : α ∈ Ico 0 1` | SOURCE | expands to 0≤α and α<1; graph 15533 |
| `p8_id1` | `q : ℕ` | SOURCE | source Q≥1 encoded Q=q+1 |
| `p8_id2` | `r : ℕ` | SOURCE | positive branch q=r+1; zero branch is a separate conjunct |

Counting the displayed membership guards as one logical binder each, the counts
(SOURCE, STANDING, TYPING, RULED, EXCESS) are (10,0,1,0,0) for each ev step,
(8,0,1,0,0) for the evenness bundle, (2,0,0,0,0) for identities, and (1,0,0,0,0)
for each coefficient step. Expanding hI exposes only the source axes conditions
and the definitional action equality; expanding hα exposes the two source endpoint
inequalities. All five-bin tests have zero EXCESS. F1 concerns extending conclusions
to the source neighbourhood, not the legitimate source-base use of hI in the ev steps.

## Supporting declarations and definitions

Every new public declaration is covered here or in the node table. Generic conditional
helpers are audited as helpers, not substituted for a source node. Prefixes are
`KAM.Planetary.` for the first two and `KAM.Planetary.SecularForm.` otherwise.

| Declaration | Verdict / meaning |
|---|---|
| `iteratedFDeriv_invariant_of_equiv` (46) | PASS helper: local equality under a continuous linear equivalence transports jets; actual equivalence, no regularity conclusion assumed. |
| `fderiv_fderiv_invariant_of_equiv` (62) | PASS helper: second derivative specialization of the tensor statement. |
| `slowRotCLM_apply` (80) | PASS: literal rotation formula. |
| `slowRotCLE_apply` (104) | PASS: same map after bundling the inverse. |
| `slowReflCLE_apply` (110) | PASS: η reflection. |
| `eventually_mem_slowDom_zero` (113) | PASS: neighbourhood supplied from positive source actions. |
| `slowSecular_eventually_rotate` (133) | PASS: local rotation invariance built from evenness. |
| `slowSecular_eventually_reflect` (146) | PASS: local reflection invariance built from evenness. |
| `slowEmbCLM_apply` (163) | PASS: literal coordinate insertion/permutation. |
| `analyticAt_slowSecular_jet` (167) | PASS: action analyticity of a jet, constructed from joint secular analyticity and a linear partial-derivative restriction. |
| `analyticOnNhd_slowSecular_jet` (216) | PASS on its stated action domain. |
| `analyticAt_slowSecular_fix` (272) | PASS at a positive ordered source base. |
| `slowSecular_fix_second_jet` (283) | PASS: degree-two normalization 1/2, both slow blocks, literal landed coefficient matrix. |
| `coeffs_transpose` (304) | PASS, stronger domain: symmetry for all a, inherited from coeffs_hermitian. |
| `slowSecular_second_jet` (309) | PASS: same formula for both models via same_jets, with no output premise. |
| `laplace_def_neg_arg` (356) | PASS helper, stronger carrier: integral parity for all real s, α and natural k. Period shift by π supplies the identity. |
| `laplaceC_neg` (383) | PASS helper: termwise parity, including the total tsum semantics. |
| `laplace_def_eq_re` (391) | PASS: the integral and real part of the complex series agree throughout (-1,1), using parity for negative α. |
| `analyticAt_laplace_def_zero` (405) | PASS: two-sided analyticity of the actual integral, s>0. |
| `analyticAt_iteratedDeriv_two` (419) | PASS generic helper: twice differentiated analytic germ. |
| `eq_zero_of_continuousAt_of_zero_Ioo` (427) | PASS generic helper: continuous germ plus vanishing on (0,1) implies zero at 0. Its premise is the advertised generic helper's input, not an assumed planetary identity. |
| `p8_identity_one` (438), `p8_identity_two` (465) | PASS individually, with exactly the source endpoint guard. |

There are four new definitions, no new abbrev, structure, class, choice-defined object,
or source-object default branch:

| Definition | Body and public carrier | Classification |
|---|---|---|
| `slowRotCLM` (74) | (ξ,η)↦(cosθ ξ−sinθ η, sinθ ξ+cosθ η), all real θ and all Fin n vectors | Literal auxiliary linear map; PASS |
| `slowRotCLE` (85) | same map, inverse rotation by −θ; both inverse laws proved | Literal auxiliary equivalence; PASS |
| `slowReflCLE` (107) | product of identity and negation | Literal auxiliary equivalence; PASS |
| `slowEmbCLM` (156) | (Λ,(ξ,η))↦(ξ,Λ,η) | Literal auxiliary linear map; PASS |

For each: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL;
CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.
All four defining equations were independently elaborated in the scratch probe.
The section's `@[expose]` exposes their bodies. No arbitrary chosen witness occurs.

The inherited meaning-carrying objects were read at their definitions: Data, axes,
action, axis, actionDomain, secular, slowSecular, slowDom, realDisc, coeffs, quad,
pcoef, halfCoef, laplaceTerm, laplaceC and laplace_def. The actual frozen
secularAverage and assemble preserve the normalized (2π)^(-n) average and the
(ξ,Λ,η) dictionary, not an abstract substituted function. The Laplace normalization
is (2π)^(-1), matching p8:112. These inherited definitions were not changed.

## Independent verification

All Lean-bearing checks were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The lint wrapper inherits both settings for its ABI subprocess. No clean, update,
cache fetch, full rebuild, heartbeat override, or package mutation was used.

1. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8c KAM.Planetary.SecularForm.EvenIdentNodes
   ```

   The gate invokes `nice -n 5 lake build`. Exit 0:
   `[inp-gate] slot 1 acquired 01:43:38 for KAM.Planetary.SecularForm.EvenIdentNodes`;
   `Build completed successfully (9174 jobs).`
   Existing dependency warnings were replayed for unused variables in Energy, Chart,
   Real and D25 and deprecated ite_cond_eq_false in Coefficients. No target-file warning.

2. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.EvenIdentNodes
   ```

   Exit 0. Output: `replaying KAM.Planetary.SecularForm.EvenIdentNodes`.

3. Transient probe `.lake/abi-scratch/GP8cAudit.lean`, importing only the target:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GP8cAudit.lean
   ```

   The initial probe exited 0 and printed axioms for all 29 new public theorems.
   Every output was `depends on axioms: [propext, Classical.choice, Quot.sound]`.
   Specifically this includes all six named node exports and both individual endpoint
   identities. The full declaration inventory is the six-node and support tables above.
   There is no sorryAx or project axiom. A second run adds exact source I1/I2 applications,
   separate α=0 applications, the source-polydisc restriction of all four invariances,
   and the four defining-equation checks; its result is recorded below.

4. Import closure: 128 project modules, including 56 frozen definition modules;
   all 56 are manifest `kind=definition`, `state=SEALED`. No provider or frozen theorem
   module, hence no DRAFT_SORRY anchor, in the transitive project import closure.
   This is an import/manifest check; the 29 axiom checks independently confirm proof
   closure for the declarations actually used.

5. Hygiene: target has 536 lines, maximum line length 99; copyright, `module`,
   public imports, docstring and public noncomputable section all present. No forbidden
   token, resource override, EuclideanSpace, root-namespace declaration, or duplicate
   public helper short name was found. The short-name search covered the other KAM
   sources; the two generic helpers remain in KAM.Planetary, not Lean's root namespace.
   `git diff inp...HEAD --check` exits 0.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

6. Repository lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Final result recorded below. The expected generated-root line is explicitly
   permitted by the brief and handoff and is not a package finding.

## Suspected source defects, deviations and limits

- Blueprint p8-secular-form.tex:76 says `S(R_θ(ξ,η),Λ)=S(ξ,Λ,η)` for S on N_R(ρ*).
  At :22 that set is a rectangular box. A point (0.9ρ*,0.9ρ*) in one slow plane
  rotates by π/4 to (0,0.9√2ρ*), outside the box. Thus the displayed restricted-domain
  formulation needs a transformed-point guard or a larger-domain interpretation.
  This is already noted at DEPGRAPH:15141. The landed chart-domain invariance and
  the independently checked restriction handle the equality for the globally defined
  Lean secular function. No new physical/source erratum is claimed from this issue.
- F1–F3 are exact package deviations from the current literal unsigned-export mandate.
  The handoff openly mentions domain and coefficient-only changes, but disclosure is
  not an authorization to mark different node statements complete.
- Jet-diagonal evaluation rather than an explicit polynomial datatype, and canonical
  Hessian blocks rather than matrices named A,B,C, are faithful mathematical encodings;
  neither is independently a finding. No Weyl dot-product representation is requested
  by these six nodes.
- No conclusion about a frozen planetary headline, track theorem closure, or downstream
  consumer closure follows from this isolated package audit. No source repair or
  graph-status change was made.

## Final check receipts

- Extended source/definition probe: exit 0, no errors or warnings. It reprinted all
  29 allowed axiom lists and elaborated all eight added examples: I1/I2 together on
  [0,1), I1 at 0, I2 at 0, all four source-disc invariances together, and the four
  auxiliary defining equations.
- Lint exit 1, with the complete output:

  ```text
  KAM.lean is out of date; run scripts/gen_root_imports.py
  check_lean_modules: PASS (1195 Lean files, 0 comparator configurations)
  FROZEN-ANCHOR GUARD OK
  ABI HASHES OK (144 frozen declarations)
  ```

  This is PASS modulo the exact generated-root exception; no substantive lint
  failure remains. KAM.lean was not regenerated.
- Probe source and this audit's scratch logs were removed after the receipts were
  copied into this report. No source changes were made. Final `git diff inp...HEAD --check` exited 0; report whitespace check passed.
  Final status contains only this new report and the pre-existing untracked handoff;
  HEAD and inp remain at the hashes recorded above.

Final status: **FAIL (literal six-node package completion)**; individual Lean
proof/kernel/axiom checks PASS; repository lint PASS modulo the authorized generated
root exception. The permitted root exception is not included in the three findings.
