# P13-A independent package audit 1

Overall verdict: **PASS WITH NOTES for the P13-A infrastructure slice**. The four signed theorem types and the signed definition match; the fixed P-G inputs are constructed jointly from the actual Part 11b patch. No frozen anchor is owned or proved by this package. In particular, **P-FIXED is not seal-ready on the strength of this package**; the later P13-B/P13-C applications and terminal provider remain separate obligations.

## Scope and snapshot

Audited only `KAM/Planetary/FixedAssembly/Data.lean`, HEAD `3c6c09d80c6332484c5192c9bae94a82b4306384`. Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff, P1213 design including its full characterization/delivery and SOURCE_GAP sections, design audits 1 and 2, current standalone signatures, Part 13 blueprint/packet, track P statement, relevant frozen definitions and P-FIXED anchor, and actual consumed upstream implementations. The user's exact worktree report destination overrides the generic brief's main-worktree instruction. No implementation, frozen file, manifest, generated root, or git state was edited.

`git diff inp...HEAD` warns of multiple merge bases and selects `d775cfa33857efd3efd0725c8398516a0e7bc864`. The observed inp ref was `463375ee3fdc33faa02362b5343333301deed4be` (live ref may advance). The complete comparison has 18 files, 2458 insertions and 90 deletions: this module plus inherited WeakKAM, torsion, graph, audit and generated-root changes. `git diff --name-status fe7a2903..HEAD` isolates the two P13-A commits and returns only `A KAM/Planetary/FixedAssembly/Data.lean`. The full comparison was retained separately for scope/protected-path review; the inherited packages are not reclassified as P13-A work.

| Input | SHA-256 |
|---|---|
| FixedAssembly/Data.lean | `528f91e90d8301f77e841503f97a1d11f7ea10688eb2dcc47e2acf74cb3f8c4d` |
| P1213-LEAN-DESIGN.md | `da905471b106707950e1de2c433228a74a967117f81e07cd767a1c7ffea05768` |
| /root/code/KAM-inp/.drafts/design/P1213Signatures.lean | `1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447` |

## Declaration and node ledger

`FA` means `KAM.Planetary.FixedAssembly`; `PA` means `KAM.Planetary.PlanarAssembly`. All implementation locators in the first table refer to the sole audited file.

| Declaration | Verdict | Reason |
|---|---|---|
| `FA.perturbation`, 33-34 | PASS | Signed definition is the literal constant coupling family of total fFix composed with PA.total_chart; fresh copied definition is equal by rfl. |
| `FA.fixed_hamiltonian_form`, 37-42 | PASS | Exact signed header; exact existing product-chart identity, for arbitrary real coupling and general n (also harmlessly n=0). |
| `FA.perturbation_difference`, 45-51 | PASS | Exact signed header; algebraic difference with denominator 2*m0, no positivity or domain premise. This export deliberately claims only the difference identity. |
| `FA.chart_of_preserves_fast`, 54-67 | PASS | Exact signed header; conditional helper with descriptive name, genuine fast-action preservation and product-domain guards; all real couplings. |
| `FA.pg_hypotheses`, 105-354 | PASS | Exact signed header and original physical premises only. All sets, chart, radii and jets chosen together before coupling; full analytic, lattice, inverse-derivative, Hamiltonian, tube, H1-H6 conclusions. |
| private `tube_isOpen`, 69-75 | PASS | Continuity of action and slow length gives the literal open tube. |
| private `shift_mem_tube`, 77-89 | PASS | Integer fast shifts leave action and slow coordinates fixed. |
| private `slowLength_lt`, 91-102 | PASS | Two oscillator-disc square bounds, r0<=rS/2, and rS>0 imply strict slow-length bound. |

The following lists every one of the 15 graph rows assigned to P13-A by design:78-92. Signed exports follow their deliberately split signatures; additional source claims are attached through the upstream common construction, not attributed to a narrower theorem merely because of its name.

| Node | Lean declaration / proof evidence | Verdict | Reason |
|---|---|---|---|
| `bpP:p13:fixed-hamiltonian-form` | FA.fixed_hamiltonian_form; FA.pg_hypotheses; upstream fixed branch | PASS | (a) product identity; (b) actual secular identification/jets; (c) actual fixed Birkhoff branch, as detailed below. |
| `stepP:p13:fh-chart` | FA.fixed_hamiltonian_form; Product analyticOnNhd_fFix_poincareProd | PASS | Exact splitting and existing analytic perturbation in actual product domain. |
| `stepP:p13:fh-id` | FA.perturbation_difference; SecularForm.identification/same_jets; Birkhoff/Estimate | PASS | Difference is exact; action-only averaged correction and matching slow jets are upstream proved facts, not an inference from the square identity alone. |
| `stepP:p13:fh-bnf` | patch -> PlanarBirkhoffResult -> hf fixed branch, Data:244-245,344-347 | PASS | Fixed pullback, common owner T and cube, actual frequency/torsion and sixth-order certificate. |
| `bpP:p13:data` | FA.pg_hypotheses:155-258 | PASS | Joint patch, positive nested boxes, collar, small radius, fixed perturbation and owner jets; later P-G constants belong to data#choices/P13-B. |
| `bpP:p13:chart` | FA.pg_hypotheses; FA.chart_of_preserves_fast | PASS | All signed geometric, Hamiltonian and physical-tube clauses for one chart. |
| `stepP:p13:ch-same` | FA.pg_hypotheses:231-243,274-330 | PASS | Reuses Hamiltonian-independent PA helpers and actual hdom/hch/hinjT/hact/htr. |
| `stepP:p13:ch-ham` | FA.chart_of_preserves_fast, Data:286-288 | PASS | Replaces moving perturbation by fFix, retaining real coupling and h. |
| `bpP:p13:pg-hypotheses` | FA.pg_hypotheses | PASS | Complete signed P-G input tuple; no P-G theorem used. |
| `stepP:p13:pg-sets` | FA.pg_hypotheses:185-228,259-273 | PASS | Open connected bounded V, closure V subset W, positive collar/radius/B and shift-invariant open chart domain. |
| `stepP:p13:pg-h1` | Data:331-333 | PASS | Joint analyticity of constant coupling family on Icc 0 1 times the closed cylinder, using strict closure containment in O. |
| `stepP:p13:pg-h2` | Data:334-340 | PASS | Actual chart periodicity implies fixed-family periodicity on the cylinder. |
| `stepP:p13:pg-h3` | Data:340-343, PA.fast_diffeo | PASS | Same literal Kepler h and actual smooth inverse on positive W. |
| `stepP:p13:pg-h4` | Data:244-258,344-347 | PASS | Owner fixed Birkhoff form restricted to V and smaller positive radius; exact frozen 1/2 quartic normalization. |
| `stepP:p13:pg-h56` | Data:348-354 | PASS | One positive B from the same compact axis cube and symmetry of actual p11c_beta, uniform in coupling. |

`bpP:p13:data#choices` is explicitly assigned to the subsequent fixed P-G application; it is not an omitted P13-A claim. No new unsigned public theorem purports to close a broader graph node. No public HELPER short name, root shadow, new instance, or hidden typeclass premise was introduced.

## Characterization and delivery gates: checked against bodies

**Same owner objects, one common construction.** Data:168-169 eliminates `patch p hp a haxes eta1 heta1` once, producing the good axis cube, B and one `PlanarBirkhoffResult`. Its definition at `PlanarTorsion/Birkhoff/Defs.lean:42-73` quantifies O', F, chi and T *before* `forall fhat in {hatFix,hatMov}`. It certifies `T = p11c_rotationLift p o p11c_liftFlow chi.eval`, with common domain, chart, image guard and both physical branches. This is direct consumption of the upstream common construction permitted by design:66, not two independently proved Birkhoff existentials retroactively identified. PA.pg_hypotheses uses that same owner construction (PA Data:144-145). The fixed proof selects the fixed branch at Data:244.

**Canonical jets on that same cube.** The upstream branch gives a P0 with `forall I in p.actions '' closedBall a0 r, P0 I = p11c_secular fhat I 0`, plus the expansion and frozen Birkhoff predicate using that exact P0, `2*p11c_sigma p (p.axes I)` and `p11c_beta p (p.axes I)`. The local `hVsub` and `hVint` attach V to this very cube (Data:193-194); the witness tuple (Data:256-258) uses the fixed P0 and those literal frequency/torsion functions. No fresh unrelated jet witnesses are substituted. Although the local obtain discards the P0 equality and sixth-order clauses, both are proved upstream about precisely the P0 bound there; they are not assumed or guessed.

**C0 and deltaS identified.** `p11cB_C p I` is defined in Birkhoff/Jets:40 as `p11c_secular (p11c_hatFix p) I 0`. This is the fixed constant certificate just described. The explicit Part-8 C0 is `SecularForm.constantTerm`. A fresh no-sorry probe established

```lean
example (p : PlanarData) (hp : p.Valid) (a : Fin 2 → ℝ) (ha : a ∈ p11c_axes) :
    p11cB_C p (p.actions a) =
      SecularForm.constantTerm (p11cSecularData p hp) a := by
  have h := SecularForm.rayRemainder_zero (p11cSecularData p hp) (p11c_axes_mem ha) 0 0
  have h' : SecularForm.secular (p11cSecularData p hp) false
      (0, SecularForm.action (p11cSecularData p hp) a, 0) -
      SecularForm.constantTerm (p11cSecularData p hp) a = 0 := by
    simpa only [SecularForm.rayRemainder, SecularForm.raySlow, zero_smul,
      zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] using h
  exact sub_eq_zero.mp h'
```

For I in V the proof's `hbeta` supplies `p.axes I` in the same cube, and `p11cB_actions_axes` identifies its actions with I. Thus this is the required C0(a(I)), not an arbitrary constant. For the moving model, `p11cB_estimate` at Birkhoff/Estimate:73-95 proves the same-cube moving constant is `p11cB_C + SecularForm.modelDelta` using the actual identification theorem. Its fixed branch uses d=0. This also supplies the P0mov=C0+deltaS dictionary. The proof of the expansion fixes the same `Omega=2 sigma` and `beta=beta-hat`, with the frozen `(1/2) sum beta_ij R_i R_j` factor, rather than relying on a bare signature or determinant coincidence.

**Fresh outputs versus equality of projections.** Neither PA.pg_hypotheses nor FA.pg_hypotheses exports equality to witnesses selected by a separate elimination of the other theorem. No such equality is claimed here. The common-map/source certificate is the upstream joint result; each signed consumer projection selects fresh joint witnesses as the approved signature comment and row P13-A require. A future consumer needing literal equality between two independently extracted tuples must use the upstream joint result directly. Repeating the call shape alone would not prove that equality. No fixed P-G threshold is taken from a moving application; P-G is not applied by this module.

## Applicable SOURCE_GAP review

The handoff's statement that gaps are not re-examined is insufficient by itself; I inspected the actual consumed chain and checked its axioms and kernel replay as recorded below.

| Retained gate | Actual proof route and disposition |
|---|---|
| `stepP:p11b:bt-rot#lift`, analytic eigenframe | Frame:35-43 defines an explicit normalized two-dimensional eigenvector/SO(2) frame. Frame:47-62 proves the nonzero off-diagonal/norm; Frame:84-126 proves analyticity using those positive guards; global_planar_frame and rotationLift_chart attach it to physical data. No simple-connectedness-only lift is assumed. |
| `stepP:p11b:fl-bd`, uniform real existence | QuarticFlow/Energy:245-265 uses gen_uniform_compact on a compact confining ball and gen_confinement, with the two-sided Riccati estimate, to produce an actual solution. QuarticFlow/Spec:57-78 proves existence/uniqueness removes the fallback branch. QuarticFlow:42 onward fixes a common positive radius before I,z and proves the time-one bound/inverse. |
| `stepP:p11b:li-tay`, real Lie/Taylor | NormalForm/Taylor:65-101 proves the chain rule and order-two integral Taylor formula along an actual real solution using integration by parts. It does not invoke an N holomorphic SmallField theorem on unsupported real input. |
| `stepP:p11b:lm-prop`, full-lift symplectic applicability | Lift/Defs:58-61 defines the full action-dependent real Hamiltonian. Lift/Iterate:140-165 applies p11cVar_isSymplecticOn to a jointly analytic real local flow, then composes the short-time maps on guarded domains; RealFlow/Variational:154-275 proves the variational/symplectic argument. Fast-angle derivatives are included by the full Hamiltonian construction. |
| Part 7 real analytic square roots/reciprocals and image guards | Actual Product analytic/symplectic exports are consumed through PA.chart_of_birkhoff; hTm/hdom keep T(O) in the true Poincare and collision-free domains. |
| Part 9 periods | htr is covariance for arbitrary real fast shifts; specialization uses 2*pi*k at Data:233-243. No period-one torus theorem or frequency/time rescaling is used. |
| P-G/Part 5 gates and general-n wrapper K1-K6 | Not consumed here. No P-G anchor, provider or other frozen theorem occurs in the transitive local import closure. These gates stay with their owning later packages; this audit does not close them. |

The upstream graph retains `stepP:p11b:li-ord` as BYPASSED (packet P-p11b.nodes.md:1037-1040), with the T10 audit/ruling and the direct remainder-bound route under D27. This audit does not relabel that literal intermediate statement as proved. The consumed Lie estimate and the separate real Taylor applicability theorem are the actual delivered results.

## Definitions, hypotheses, and justified differences from blueprint wording

The entire new definition inventory is **one def**, FA.perturbation. It is the actual total composition on its whole carrier, constant in the dummy coupling; no piecewise zero, choice of jets, new predicate/structure, or fabricated off-domain object exists. All theorem uses are confined by actual chart/cylinder guards. Private helper theorems add no definitions.

The design deliberately uses total compositions rather than blueprint p13:57,80-82,91's zero extensions. Off-domain values are unused, so this is an already declared totalization difference, not a changed physical law. The locally chosen `r0=min(rS/2,rho)` is allowed to be smaller than rS/2: it ensures strict closed-cylinder containment and the required forward physical-tube control. The signature requires a positive available radius, not equality to a maximal radius. `delta=1` is legitimate because the implementation proves tube inclusion for every r<=r0, ignoring the extra `2*r^2<=delta` premise; this strengthens the conditional clause. B is a uniform positive lower bound from the actual cube, which is all the signed consumer needs.

No conclusion-shaped root premise, modified physical law, widened coupling-dependent constant, substituted carrier, source-defined norm change, or introduced source defect was found. The conditional fast-action helper does not replace the source theorem: pg_hypotheses supplies its guard from hact. The P-FIXED frozen statement remains unchanged and unproved by this slice. No new pinned-paper erratum is asserted; this is a local blueprint/Lean package audit, not a fresh paper audit.

## Independent validation

All audit-owned Lean invocations were sequential with LEAN_NUM_THREADS=1 and nice -n 5. The targeted build used the required compile gate; its slot wait was allowed to finish. No clean, update, cache get, dependency-directory edit, resource override, generated-root rewrite or full-library target was run. Scratch probes were under this worktree's .lake/abi-scratch and were deleted after validation.

### Targeted build and exact signatures

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-fx13a KAM.Planetary.FixedAssembly.Data
[inp-gate] slot 1 acquired 00:42:31 for KAM.Planetary.FixedAssembly.Data
Build completed successfully (9382 jobs).
exit 0
```

The build replayed upstream linter warnings (unused variables and unused simp arguments, including PA.Data:58 and :155); none was a P13-A elaboration error. No default-heartbeat failure occurred.

Mechanical comparison of all four theorem headers against the current standalone signatures, removing whitespace only, returned EXACT HEADER for each. The probe copied those four signed headers under fresh names, with proofs applying the actual exports in binder order, and copied the signed perturbation definition with an rfl equality check. Thus it elaborated the actual signed consumer surface; no hypothetical upstream signature or sorry-backed design declaration was imported. A further example proved the C0 identity printed above.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-fx13a-1.lean
exit 0
```

Exploratory probes initially hit an unimported optional upstream identifier and simplification mismatches in the extra C0 example. Those scratch-only issues were corrected; the final single probe exited 0. They were not package errors. Provider=frozen-type and frozen seal-body probes are **inapplicable**: this module has no provider export and does not prove the P-FIXED anchor.

### Fresh axiom output

Every new public theorem and the following consumed upstream exports were queried in that successful probe. No sorryAx or other unapproved axiom occurs.

```text
'KAM.Planetary.FixedAssembly.fixed_hamiltonian_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.perturbation_difference' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.chart_of_preserves_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.pg_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.patch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.birkhoff_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.global_planar_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_lie_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cVar_isSymplecticOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lift_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.identification' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularForm.same_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cB_fhat_clause' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p12c_slow_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.total_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.product_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.chart_of_birkhoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.forward_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.fast_diffeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.pg_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Planetary.FixedAssembly.Data \
  KAM.Planetary.PlanarAssembly.Data \
  KAM.Planetary.PlanarTorsion.Patch \
  KAM.Planetary.PlanarTorsion.Birkhoff \
  KAM.Planetary.PlanarTorsion.Frame \
  KAM.Planetary.PlanarTorsion.QuarticFlow \
  KAM.Planetary.PlanarTorsion.NormalForm.Taylor \
  KAM.Planetary.PlanarTorsion.Lift \
  KAM.Planetary.PlanarTorsion.RealFlow.Variational
exit 0
```

One invocation replayed the local dependencies and all nine named modules. Final output:

```text
replaying KAM.Planetary.PlanarTorsion.Patch
replaying KAM.Planetary.PlanarAssembly.Data
replaying KAM.Planetary.FixedAssembly.Data
```

### Source lint, frozen guard and ABI

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1163 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failing lint item is the expected generated-root freshness check expressly allowed by this brief. Module hygiene, frozen-anchor integrity and elaborated ABI checks pass independently. KAM.lean was not regenerated.


### Static and protected-path checks

The module is 358 lines, maximum line length 99 Unicode characters, and has copyright/authors, module, public imports, module documentation, exposed public section. Static scan found no sorry, admit, axiom, unsafe, opaque, EuclideanSpace or set_option. Its one definition and four public theorem names stay in FA; repeated private helpers do not collide with PA's private declarations.

A recursive read-only import scan found 336 local KAM modules, **zero frozen theorem modules and zero provider modules**. Thus there is no imported DRAFT_SORRY theorem and no sealed-theorem state exception to justify. Only frozen definitions are consumed.

```text
git diff inp...HEAD -- KAM/Frozen manifest README.md
# empty (apart from multiple-merge-base warning)
git diff inp...HEAD -- KAM.lean
# inherited five import additions; NOT empty
git diff fe7a2903..HEAD -- KAM/Frozen manifest KAM.lean README.md
# empty
git diff --check
exit 0
```

The brief's literal full-comparison protected-path check is not entirely clean: KAM.lean has inherited BirkhoffClauses/Generic/Patch/WeakKAM import additions. They predate both P13-A commits; no P13-A commit edited a protected path. This is recorded explicitly rather than silently claiming the three-dot diff is empty. The auditor left it untouched.


## Closeout

No blocking finding in the sole audited module. PASS WITH NOTES records the generated-root lint exception and inherited protected-root delta, plus the precise infrastructure scope. The common upstream map/canonical-jet certificates were checked directly; equality of independently selected PA/FA output tuples is neither supplied nor claimed. Later fixed P-G thresholds, physical application and the terminal P-FIXED provider remain outside this package.

The only persistent audit-created repository artifact is this exact report. The pre-existing untracked P13-A-handoff.md was preserved; no source repair, git mutation, new frozen statement, or errata-ledger change was performed.
