# GAP-P8c independent package audit 2

Date: 2026-10-29 UTC. Worktree: `/root/code/KAM-inp-gp8c`.
HEAD: `dc9ab3c472e1c2b5220751c5a79ed163993f99c7`.
Comparison `inp`: `22d2f2f0a82dcd9f5927d99635cd2e3650ec4924`.

**Overall: FAIL under the handoff's literal named-export contract.** Five of the
six nodes pass. Audit-1 findings F2 and F3 are closed. F1 remains for the nominated
`p8_evenness_full`; the added `p8_evenness_nbhd` establishes a genuine smaller-radius
neighbourhood result, whose scope and remaining attachment issue are detailed below.
Lean build, kernel replay and axiom checks pass. This is a statement-contract failure,
not a refutation of a Lean theorem.

No frozen anchor or provider is implemented here: provider/frozen type equality and
seal-body probes are N/A. No headline, track or consumer closure is certified.

## Scope and authority

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, track P statement,
GAP-PLAN-P.md:359–369, the handoff including AUDIT FOCUS, audit 1, the six complete
NODE records and their cited blueprint statements/proofs. Source locators below use
`blueprint-P/parts/p8-secular-form.tex` and `docs/graph/P/DEPGRAPH.md`.
The user's exact report location overrides the brief's main-worktree default.

Inspected the full `git diff inp...HEAD`: the target module is added (714 lines),
alongside audit 1 and the handoff. Only the target Lean module is audited for package
correctness. Supporting definitions and proofs were read to check actual meanings.
No matching entry for these exports occurs in `KAM/**/*Signatures.lean`; they are
UNSIGNED. No existing signed declaration changes. The handoff is stale: it still
identifies the old HEAD, 536 lines, arithmetic-only coefficient exports and no
`p8_evenness_nbhd`. A commit title mentioning a handoff is not an updated node mapping.

## Per-node verdicts

All short exports below are in `KAM.Planetary.SecularForm`.

| Node | Declaration and Lean lines | Graph; blueprint | Verdict | Reason |
|---|---|---|---|---|
| `stepP:p8:ev-tay` | `p8_ev_tay`, 223–242 | 15172–15200; 83 | PASS | Actual two secular models: all odd tensors vanish, the first derivative vanishes, and diagonal jets are invariant under rotations and reflection. These generate diagonal O(2); factorial normalization preserves invariance of each homogeneous Taylor polynomial. Analyticity/local invariance are constructed internally from source data. |
| `stepP:p8:ev-quad` | `p8_ev_quad`, 247–269 | 15202–15228; 84 | PASS | Mixed Hessian block is zero; eta and xi diagonal blocks agree, for full n and both models. This is B=0 and C=A in canonical Hessian/Taylor coordinates; basis specialization gives entries. |
| `bpP:p8:evenness` | nominated `p8_evenness_full`, 324–351; added `p8_evenness_nbhd`, 394–442 | 15112–15141; 75–84 | FAIL | The nominated export retains separate chart and action domains without the source base/radius/action-slice attachment. The successor supplies a smaller-radius joint neighbourhood, but does not state the result for the already selected source radius. See F1. |
| `bpP:p8:identities` | `p8_identities_full`, 582–587 | 15526–15554; 129–140 | PASS | Literal I1 and I2 for every alpha in [0,1), including zero; actual normalized integral and derivatives. Analyticity on a two-sided germ justifies the endpoint continuity argument. |
| `stepP:p8:id-1` | `p8_id1`, 603–646 | 15556–15583; 138 | PASS | With source Q=q+1, differentiates the actual beta-series monomial, exposes the multiplier 2Q(2Q+1), proves the Pochhammer equality, and identifies the result with the RHS series term of degree 2Q-1. F2 closed. |
| `stepP:p8:id-2` | `p8_id2`, 654–708 | 15585–15612; 139 | PASS | Differentiates the actual b-series monomials at q=0 and q=r+1, exposes the multiplier, and identifies the positive branch with alpha times the RHS term. Its degree is 2r+3, explicitly distinct from 1. F3 closed. |

The six-node design list is exactly the handoff's slice. A changed index notation,
jet-diagonal representation or Hessian representation is not independently a failure.
The coefficient steps are monomial coefficient comparisons; a new HasSum theorem is
not required. Their alpha identities hold for every real alpha, so also on the source
interval, including zero. Their coefficients have no alpha dependence; specialization
recovers the source quantifier order without changing constants or scope. The actual
series identification is the inherited `hasSum_laplaceTerm`, and termwise derivative
machinery is in `LaplaceIdentities.lean`.

## F1: named export and selected source radius still do not match

Graph 15119–15121 fixes the scope as:

> rho_* of bpP:p8:perturbation-analytic

and orders quantifiers as physical data/base axes, rho_*, point in N_R(rho_*), theta.
`p8_evenness_full` has only `(D : Data n) (b : Bool)` as outer inputs. Its invariances
are on `slowDom D`; Taylor/quadratic/analyticity claims are on `actionDomain D`.
Its statement is unchanged from audit 1. Under the explicit AUDIT FOCUS requirement
that the **named declaration** state the literal node conclusion, it still fails.

The revision makes substantial progress beyond that old statement:

- `eventually_mem_actionDomain` proves openness at each positive ordered source base,
  using positive actions, continuity of `axis`, strict ordering and `action_axis`.
- `p8_evenness_nbhd` obtains the analytic witness `r0` internally, obtains an action
  neighbourhood epsilon, then returns `r = min r0 epsilon` (422–438).
- At this single returned radius it proves separation, complex differentiability of
  `secularC`, real analyticity of `secular`, all four invariances, all Taylor/quadratic
  assertions, and jet/matrix analyticity on the full projected real-disc action slice.
  The inclusion into `actionDomain` is proved at 427–435, not assumed.
- The witness precedes both model choices, all points, and all jet orders. Radius
  dependence is only on physical data and base axes. No dependency output is an input.

Thus the former claim that no neighbourhood inclusion is constructed is now obsolete.
The successor is PASS as the smaller-radius theorem it actually states. However, it
neither proves the conclusions for the original witness `r0`, nor identifies the new
radius with the rho_* already shared in the source contract. The bound `r < rho D a`
is only a bound by the geometric rho_0 (Basic.lean:65), not that identification.
Its type also restates only selected outputs of `perturbation_analytic`: it omits
perturbation holomorphy/joint continuity, complex-to-real identifications and
integrability, although these can be restricted to the smaller disc from the existing
proof. Those restrictions are not a joint public export in the current declaration.

Required closeout: either export the literal result with the already selected source
radius, or explicitly adopt/map a joint successor source package with the smaller
shared radius and its required analytic outputs. Update the nominated node export
accordingly. This auditor does not silently remap `p8_evenness_full` or choose a new
source radius. No assertion is made that such a successor is mathematically false.

## Premises and definition audit

Expanded `Data n` (Basic.lean:38–45): G,m0,m and their positivity, plus n>0, are exactly
source physical data. `n : Nat` is typing data. `I in actionDomain D` expands to
existence of positive strictly ordered axes a with `action D a = I`; `ha : a in axes n`
expands to positivity and StrictMono. Both are source-base conditions. `b : Bool`
selects the two actual models. `alpha in Ico 0 1` is the literal source endpoint guard;
q and r encode the source natural coefficient indices. No export takes analyticity,
invariance, same_jets, Hessian equality or a differential identity as a premise.
SOURCE/TYPING bins suffice for node inputs; STANDING/RULED/EXCESS contain no additional
hypothesis. Generic conditional helpers below are audited as helpers, not source exports.

Exactly four new definitions; all have literal bodies on their entire public carrier:

| Definition; line | Classification / verdict |
|---|---|
| `slowRotCLM`; 74 | PASS: literal simultaneous rotation, all real theta and all slow vectors. |
| `slowRotCLE`; 85 | PASS: same rotation, inverse angle -theta; both inverse laws proved. |
| `slowReflCLE`; 107 | PASS: identity on xi and negation on eta. |
| `slowEmbCLM`; 156 | PASS: literal permutation/insertion (I,(xi,eta)) -> (xi,I,eta). |

For all four: BODY_MATCH=OK, PUBLIC_CARRIER=OK; no junk/default branch, chosen
witness or proof-dependent object. WELL_DEFINEDNESS and CHARACTERIZATION=N/A_LITERAL;
CHOICE_INDEPENDENCE=N/A. The exposed public section exposes their bodies; four fresh
rfl probes verify their defining applications. No new abbrev, structure or class.
Inherited secular/slowSecular use frozen `secularAverage` and `assemble`, retaining
(2*pi)^(-n) normalization and the (xi,Lambda,eta) dictionary. `laplace_def` retains
(2*pi)^(-1); `laplaceTerm`, `halfCoef`, `poch`, and `pcoef` are the literal series data.

## Other public declarations

Each theorem below has verdict PASS on its stated scope; none substitutes for F1.
The six named exports are individually covered above. The four definitions are above.
This inventory accounts for every new public declaration (33 theorems, four definitions).
The first two names have prefix `KAM.Planetary`, all remaining names `KAM.Planetary.SecularForm`.

| Declaration; line | Reason / scope |
|---|---|
| `iteratedFDeriv_invariant_of_equiv`; 46 | Generic local equivariance transports iterated derivatives by a linear equivalence. |
| `fderiv_fderiv_invariant_of_equiv`; 62 | Second-order specialization of that tensor identity. |
| `slowRotCLM_apply`; 80 | Literal rotation formula. |
| `slowRotCLE_apply`; 104 | Underlying map equality. |
| `slowReflCLE_apply`; 110 | Literal reflection formula. |
| `eventually_mem_slowDom_zero`; 113 | Chart neighbourhood from positive ordered base actions. |
| `slowSecular_eventually_rotate`; 133 | Actual local rotation invariance from landed evenness. |
| `slowSecular_eventually_reflect`; 146 | Actual local reflection invariance from landed evenness. |
| `slowEmbCLM_apply`; 163 | Literal embedding formula. |
| `analyticAt_slowSecular_jet`; 167 | Analytic dependence of partial jets, built from joint secular analyticity. |
| `analyticOnNhd_slowSecular_jet`; 216 | Analyticity on the stated action domain. |
| `analyticAt_slowSecular_fix`; 272 | Fixed-model analyticity at the circular source base. |
| `slowSecular_fix_second_jet`; 283 | Correct half-Hessian normalization of the landed quadratic form. |
| `coeffs_transpose`; 304 | Stronger-domain real symmetry, all a. |
| `slowSecular_second_jet`; 309 | Both models through same_jets, internally applied. |
| `eventually_mem_actionDomain`; 357 | Positive/order neighbourhood and inverse action identity proved. |
| `p8_evenness_nbhd`; 394 | Valid smaller-radius joint neighbourhood theorem; see F1 for source attachment limits. |
| `laplace_def_neg_arg`; 447 | Integral parity via pi translation, all real s and alpha, natural k. |
| `laplaceC_neg`; 474 | Termwise parity, valid for total tsum as defined. |
| `laplace_def_eq_re`; 482 | Integral equals real part of complex series throughout (-1,1), s>0. |
| `analyticAt_laplace_def_zero`; 496 | Two-sided analytic germ of the actual integral. |
| `analyticAt_iteratedDeriv_two`; 510 | Generic differentiation of an analytic germ. |
| `eq_zero_of_continuousAt_of_zero_Ioo`; 518 | Generic continuity/one-sided uniqueness helper. |
| `p8_identity_one`; 529 | Literal I1 on [0,1). |
| `p8_identity_two`; 556 | Literal I2 on [0,1). |
| `deriv_monomial_succ`; 590 | Literal monomial differentiation, arbitrary real c. |
| `iteratedDeriv_two_eq_deriv`; 596 | Definitional second derivative equality, arbitrary function. |

## Independent checks

All Lean-bearing checks were serialized with `LEAN_NUM_THREADS=1`. No clean, update,
cache fetch, full-library build, heartbeat override or state-changing git was run.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gp8c KAM.Planetary.SecularForm.EvenIdentNodes
   ```

   Exit 0; `[inp-gate] slot 2 acquired 02:16:01 for KAM.Planetary.SecularForm.EvenIdentNodes`;
   `Build completed successfully (9174 jobs).` The gate uses nice -n 5. Existing
   dependency warnings were replayed (unused variables and deprecated ite_cond_eq_false);
   no target-module warning.

2. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularForm.EvenIdentNodes
   ```

   Exit 0; complete output: `replaying KAM.Planetary.SecularForm.EvenIdentNodes`.

3. Fresh transient probe:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GP8cAudit2.lean
   ```

   Exit 0; no errors or warnings. It checks the fully elaborated types and prints axioms
   of **all 33 public theorems**, individually inventoried in the tables above, including
   `p8_evenness_nbhd`. Every axiom receipt is exactly
   `depends on axioms: [propext, Classical.choice, Quot.sound]`.
   No sorryAx or project axiom. Nine additional examples elaborate: general I1,
   separate I1/I2 at zero, both differentiated positive monomial identities, and four
   defining equations. The actual invocation redirects stdout/stderr to the scratch log.

4. Import closure checked from source: 128 project modules, 56 frozen modules;
   all 56 match manifest entries `kind=definition`, `state=SEALED`. No provider,
   frozen theorem or DRAFT_SORRY anchor is imported. Manifest lookup uses its `path` key.

5. Hygiene: 714 lines; maximum Unicode line length 100. Copyright, module, public
   imports, module docstring and exposed public section are present. Source-name scan
   finds no reused public theorem/definition short name elsewhere in KAM. All new names
   are in KAM.Planetary or its SecularForm namespace; no harmful root shadow.
   `git diff inp...HEAD --check` exits 0.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

6. Repository lint command and final receipt are recorded below.

## Suspected source defects, deviations and uncertainty

Blueprint p8:76 states `S(R_theta(xi,eta),Lambda)=S(xi,Lambda,eta)` for S on the
rectangular box defined at p8:22. That box is not rotation invariant: one planet's
(0.9*rho_*,0.9*rho_*) rotates by pi/4 to (0,0.9*sqrt(2)*rho_*), outside the box.
This needs a transformed-point guard or larger-domain interpretation. It is already
noted at graph:15141 and in the handoff. Landed chart-domain invariance supplies a
valid larger-domain equality of the globally defined secular function. This is not
a new physical-source erratum and does not excuse F1's separate action/radius issue.

The smaller-radius successor is openly documented in its docstring (384–393), rather
than hidden. Its existence is valid; its use as the literal node would change the
current named-export/shared-source-radius contract. No new source ruling was found
in the handoff. This report does not introduce one. No other suspected defect or
implementation deviation was found in the audited slice.

## Final lint and integrity receipts

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, with complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1195 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

This is PASS modulo the brief's expressly permitted generated-root exception; no
other lint failure. KAM.lean was not regenerated. The invocation redirected output
to `.lake/abi-scratch/GP8cAudit2-lint.log`.

During the audit, `inp` advanced externally from the comparison hash above to
`5d2c928069e3d3bcea1f688373decd8fda061515`. Rechecked `git diff inp...HEAD`:
the same three-file diff (714 + 300 + 49 lines) and unchanged merge base
`537fc2a837002555fbe2766678b1c8454274228f`. Diff whitespace check passes;
protected-path diff remains empty. Audited HEAD did not change.

Only this report was written outside the allowed scratch directory. This audit's
probe and two scratch logs were removed after recording the receipts. Final status
contains only `?? docs/tracks/P/audits/GAP-P8c-audit-2.md`; report whitespace validation
passes. No source, frozen file, manifest, graph or generated file was edited.

Final verdict: **FAIL for bpP:p8:evenness under the nominated literal contract;
PASS for the other five nodes.** F2/F3 closed; smaller-radius successor verified,
but F1's literal named-export/source-radius attachment remains open.
