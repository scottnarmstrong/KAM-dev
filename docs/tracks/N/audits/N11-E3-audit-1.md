# Independent N11-E3 package audit 1

Overall verdict: **FAIL — incomplete graph slice.** The eleven signed declarations match the delivered signatures, and the inspected proofs establish their stated conclusions without added premises. Two assigned graph contracts have clauses absent from these proofs/exports. Signature fidelity and a successful kernel check do not establish those missing clauses.

The frozen N-PARTIAL-CONVEX anchor is **not assessed as seal-ready**: this package contains supporting lemmas, not its provider. Its frozen proof remains `by sorry`; no sealing or campaign theorem closure is claimed.

## Scope and authority

Audit date: 2026-10-28. Worktree `/root/code/KAM-inp-n11e3`, HEAD `6110c0228201ec20f9cd333ed2ef59af6cf6f60e`; comparison `inp` resolved to `f5376c6dffbc49d970aeb4f9b37796a46f764133`.

Read the external package brief, repository rules, PLAN, DECISIONS, N11-E3 handoff/AUDIT FOCUS, design and both independent design audits, track-N statement (especially its historical partial-convex addition), frozen partial-convex anchor and actual imported definitions, p11c source statements/proofs, and the relevant graph contracts. The user's exact worktree report destination overrides the brief's generic main-worktree destination. No production file, frozen file, manifest, graph, generated file or git state was changed. Only this report persists; probes were confined to `.lake/abi-scratch/` and removed.

`git diff inp...HEAD` was inspected in full: four added files, 1270 lines (Coordinates 298, Domain 435, Hessian 360, Setting 177). Setting/Coordinates are earlier N11-A/B work, read for context and import/body meaning; the substantive verdict here covers **only Domain/Hessian**. Git warns `multiple merge bases, using be6fc7b01267bd5d16506ff11a84c1f7b93cc791`; the other merge base is `9d16b3127c8a9fe9af335c5b64874bd29f32ebd8`. The requested three-dot comparison was retained literally.

Pins:

| Artifact | SHA-256 |
|---|---|
| Domain.lean | `17dee3538c30c5ed3f78cce5069ddae48cfa91c3121adf3f2df6b5ae757ad111` |
| Hessian.lean | `3e62ae00756ab4e4095e17309f6599477d2bae5fa3f2ac5c48e5a2245bcb4de4` |
| `/root/code/KAM-inp/.drafts/design/N11Signatures.lean` | `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4` |

## Findings

### F1 — Major: dm-field omits the scaled field transport and physical analyticity clauses

Design `N11-LEAN-DESIGN.md:268–271` assigns `bpN:p11:domain` and `stepN:p11:dm-field` to `domain`/`domain_field`, in these modules. The literal source at `blueprint-N/parts/p11c-partial-stability.tex:138,142` says the frozen converted Hamiltonian “equals” the real part of the holomorphic sum and “is real analytic”, and that “rescaling” the slow variables “turns weight” 2π into c. The graph makes this explicit at `docs/graph/N/DEPGRAPH.md:18292`: `SOURCE_CONCLUSION: H-hat_mu is the real part of a holomorphic function, so Lemma real-system(a) applies; rescaling x=lambda x-tilde turns weight 2 pi into c; ...`.

`Domain.lean:114–143` proves precisely its signed physical equality, at weight `2*Real.pi`. Its internal `hpt` is a useful global scalar identity with the actual frozen Hamiltonian. However, it never transports a derivative/vector field under the slow scaling. `domain` at lines 369–431 establishes the scaled perturbation's class and weighted bound, not a transformed field identity. There is no occurrence of `realWfield b.c` or a derivative of the slow-coordinate scaling in either audited module, and no proof of openness/real analyticity of the converted physical Hamiltonian on `physicalDomain`. `slowScale_extCx` only commutes inclusion with coordinate multiplication.

Adversarial recheck: a scalar pullback by `slowScale` is not the field conjugacy. Both slow derivatives pick up a λ factor, and applying the inverse coordinate scale gives the new weight `2π/λ²`. This requires a chain-rule argument and domain identification; it is not definitional reduction of `domain_field`. Physical equality remains correct without hP because the frozen Hamiltonian is unguarded; that bypass does not establish physical analyticity.

Disposition: **FAIL completeness**, not a counterexample to the signed theorem. Preserve every signed declaration. Add a separately named companion proving the actual slow-scaling field/orbit transport, with positive fixed λ, the physical/scaled domains, and weight `b.c`; establish the physical holomorphic-real restriction/analyticity clause as well. Alternatively the owner must explicitly reassign those graph clauses and cease claiming the current E3 slice complete. A downstream proof could discharge them, but no such payment occurs in the audited slice.

### F2 — Medium: real-hessian identification is paid only after taking real parts

`docs/graph/N/DEPGRAPH.md:18979–18988`, `bpN:p11:hessian#real-hessian`, requires: “the real derivatives of h_R at I are restrictions of the complex derivatives; Q(I)=D^2 h_R(I)=Q_C(I), symmetric and real, and omega(I) is the real gradient”. Its source is `blueprint-N/parts/p11c-partial-stability.tex:126`; design line 292 assigns it internally to `hessian_at_sign`.

The unsigned helper `Hessian.lean:62–104` correctly proves

```
D²(realPart h)(I)[u,v] = Re(D²h(cx I)[cx u,cx v]).
```

Its premises deliberately require holomorphy, but no reality. `hessHelper_real_fderiv` likewise identifies real parts of first derivatives. The bridge is used correctly at lines 183 and 265 for numerical inequalities. The proofs do not establish that the complex derivative values on real vectors have zero imaginary part, or Hessian symmetry on the real slice. The `real` field constructed at lines 300–305 concerns function values, not derivatives. `frequencyMap_signed` rescales the already defined real frequency; it does not supply the missing real/complex derivative identification.

Adversarial recheck: the unsigned helper applies to `h(z)=i*z₀²`, so its equality with a real-part projection cannot by itself certify equality with the complex Hessian or its reality. Under the actual source's reality hypothesis these additional conclusions should be provable by differentiating the real-valued restriction and using holomorphy. No such proof is present here. The norm bridge and convexity theorems need only the real-part identity and remain valid.

Disposition: **FAIL literal node completeness**. Add a distinct source-premised companion or internal proof establishing complex derivative reality and symmetry on the full open real slice, alongside the existing real-part identity. The unsigned helper's own statement is sound and is not misnamed as a full graph-node export.

## Declaration and node ledger

Names are in `KAM.Nekhoroshev`; D/H denote Domain/Hessian. PASS means the stated declaration is proved faithfully, not that its entire parent graph contract is closed.

| Node / obligation | Declaration / locator | Verdict | Reason |
|---|---|---|---|
| block-setting | `block_setting` D40 | PASS | Fixed Ic, inner core 3d/4, starting radius r, width d/4; literal signed body. |
| perturbation pair | `signedH` D42 | PASS | σh/(2π), actual h on the full carrier. |
| perturbation pair | `signedF` D44 | PASS | σμP/(2π), fast angle multiplied by 2π, genuine slow pair. |
| fixed slow scaling | `slowScale` D49 | PASS | Both slow coordinates multiplied by λ, fast coordinates unchanged. |
| block-setting | `blockPert` D52 | PASS | Composition with the fixed block scale, no iterated-radius substitution. |
| physical set | `physicalDomain` D57 | PASS | Actual max-norm action ball and existential slow tube around S. |
| dm-field, physical equality | `domain_field` D114 | PASS signed theorem | Actual frozen `degenerateHamiltonian`; physical field equality, same σ. |
| auxiliary collar inclusion | `polyNbhd_realBall_subset` D146 | PASS | Radius ≤ρ and collar at Ic suffice; no positive-radius premise needed. |
| dm-pts/dm-norm | `domain` D369 | PASS signed theorem | Collar, scaled ext_class, correct coth(πs)^n μ/(2π) bound. |
| domain, whole node | `domain` + `domain_field` + Hessian | FAIL | Signed analytic/norm/convexity clauses paid; F1 leaves source clause (c) incomplete. |
| dm-pts | private `blockLift_mem` D198 and `domain` | PASS | Frozen tube, strict imaginary margins, collar and closed core used literally. |
| dm-norm | `domain` D425–431 | PASS | InClass at 2s, loss s; positive s and exact eps normalization. |
| dm-field, whole step | `domain_field` D114–143 | FAIL | F1: physical equality paid; scaled field transport and physical analyticity unpaid. |
| real/complex Hessian auxiliary | `realPart_hessian_apply` H62 | PASS | General open-domain, real-part identity; no added reality premise. |
| revision-2 F1 bridge | `FastConvex.toRealFastConvex` H164 | PASS | Same m,M; real-slice upper bound from complex bound, no dimension factor. |
| selected sign | `hessian_at_sign` H243 | PASS signed theorem | Uses supplied DefiniteSign; m≤Mc from nonempty G and a unit coordinate vector. |
| Hessian and sizes | `hessian` H337 | PASS signed theorem | One global frozen sign; signed FastConvex and frequency lower bound on full real collar. |
| hs-op | private `hessHelper_hess_bound` H129, `hessian_at_sign` | PASS numerical clause | Conjugate-column test and ∞≤Euclidean yield the same Mc, not nMc. |
| hessian#real-hessian | `realPart_hessian_apply` + internal uses | FAIL full contract | F2: real-part bridge established; complex reality/symmetry not established. |

## Definition classification and proof review

All six new public definitions and the one private definition are classified; Hessian adds no definitions, abbreviations or structures.

| Definition | Whole-carrier classification |
|---|---|
| `block_setting` | Literal block record. μ and r are unrestricted in its definition; analytic uses separately prove d>0 and λ>0 from μ>0,r>0. Empty slow cores are allowed, with empty analytic bases handled literally. |
| `signedH` | Total scalar multiple of the original h. No guard, indicator or fallback. |
| `signedF` | Total evaluation of the original P after the explicit coordinate regrouping and period conversion. The unused PartialData argument does not alter P. |
| `slowScale` | Polynomial coordinate map for every real λ, including zero; inverse-scale arguments use positive λ only. |
| `blockPert` | Exact pullback of signedF by the fixed block scaling. No substitute perturbation. |
| `physicalDomain` | Existential open max tube; empty S gives empty set. No infimum-at-empty-set convention is relied on. |
| private `blockLift` D61 | Literal regrouping `(θ;I,q,p) ↦ ((2πθ,q),(I,p))`; body agrees with the signed perturbation on the entire carrier. |

The imported `FastConvex` and `RealFastConvex` structures match the signed source text after whitespace removal. They are respectively complex and real-slice upper-Hessian assumptions, not stability conclusions. `PartialData` and `DefiniteSign` also match the signature text; the latter is the actual selected frozen definiteness witness. No frequency upper bound, block normal form, confinement estimate, replacement-field equality or conclusion-shaped hypothesis is introduced.

The Hessian proof controls the Euclidean column norm by testing the original max-norm bilinear form on the conjugate column, with division/cancellation guarded by its positive norm branch. The real/complex bridge obtains local regularity from holomorphy on an open set; it does not assume a second-derivative equality. The restriction bridge works even for nonpositive R (its real action obligations are then vacuous).

The domain proof uses λR=d/4, R≤ρ/2, and 2s=ρ/(2π). It establishes all four components of the actual `partialComplexDomain`; the slow real part stays inside D through the closed core and the slow imaginary parts stay strictly below ρ. The frozen perturbation's actual four conjuncts supply holomorphy, unit bound, reality and periodicity. Weighted conversion uses the bound at 2s before restricting the class to s. No unjustified boundary continuation or extra 2π factor was found.

## Verification

All Lean/Lake invocations are serialized with `LEAN_NUM_THREADS=1`, under `nice -n 5`; the prescribed compile gate was used for the targeted build. No heartbeat, synthesis, recursion or other resource override was used. Checks and outputs are recorded below.

Static checks independently returned:

```
SIGNED HEADER block_setting EXACT
SIGNED HEADER signedH EXACT
SIGNED HEADER signedF EXACT
SIGNED HEADER slowScale EXACT
SIGNED HEADER blockPert EXACT
SIGNED HEADER physicalDomain EXACT
FULL SIGNED HEADER domain EXACT
FULL SIGNED HEADER domain_field EXACT
SIGNED HEADER FastConvex.toRealFastConvex EXACT
SIGNED HEADER hessian_at_sign EXACT
SIGNED HEADER hessian EXACT
SOURCE BUNDLE RealFastConvex EXACT
SOURCE BUNDLE FastConvex EXACT
PartialData EXACT
DefiniteSign EXACT
Domain lines 435 over100 []
Hessian lines 360 over100 []
Domain forbidden code matches: []
Hessian forbidden code matches: []
IMPORT CLOSURE 88 providers [] frozen theorems []
```

Header comparison removes whitespace only and retains binder names/order, premises, full `let` conclusions, norms and carriers. The Lean probe separately copies the six signed definition bodies and checks function equality by `rfl`, and copies the five signed theorem declarations under fresh names, closing them with their production theorem and checking the complete polymorphic types with `type_of%`. It does not import or elaborate the signature file's placeholder proofs.

The import walk recursively inspected all KAM imports from both modules. It reaches **no provider and no frozen theorem** (therefore no DRAFT_SORRY theorem import). The imported frozen definitions are actual manifest-owned modules. Public helper searches found exactly one declaration each: `polyNbhd_realBall_subset` at Domain:146 and `realPart_hessian_apply` at Hessian:62. All new public names are under `KAM.Nekhoroshev`; no root declaration, namespace hijack or new global instance is introduced. Existing `KAM.Head.hessian` is in a separate namespace, and the Hessian field use resolves as `hh.hessian`.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no diff, only the multiple-merge-base warning above. `git diff --check` exited 0.

## Source/design defects, deviations and limits

No false pinned-source assertion or new source erratum was found. F1/F2 are implementation/design-coverage discrepancies, with exact quoted source/graph clauses above; neither refutes the frozen theorem. Design audit 2's PASS concerned target interfaces and did not prove these omitted clauses. Its claim of design-level correspondence does not override the current explicit COMPLETE-slice audit requirement.

The reported Hessian → Domain import is sound and acyclic: signedH lives in Domain. The design prose at line 375 only says Domain/Hessian depend on Setting/Constants, never the reverse; that wording does not itself prohibit this extra edge. The actual acyclic import closure was checked. The signed `domain_field` retains unused source parameters; only the sign choice is needed for its global algebraic field proof. This is a harmless stronger proof of its signed result, with unused-variable warnings to be recorded in the build output.

Earlier design notes about the open-ball endpoint at p11c:31 and the stale adjoint locator p11b:69–86 are outside this slice; no source or graph was silently repaired. No upstream N11-A/B audit verdict is independently reissued here. The frozen anchor/provider equality and seal-body checks are inapplicable to this helper-only package; all five signed theorem exports were instead checked directly against their exact signed types. The actual frozen anchor was read, but was not imported into the audit probe.

### Targeted compile gate — PASS, exit 0

```
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-n11e3 \
  KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian
```

Decisive output:

```
[inp-gate] slot 1 acquired 19:36:24 for KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian
⚠ [3241/3242] Replayed KAM.Nekhoroshev.Partial.Domain
Build completed successfully (3242 jobs).
```

Domain diagnostics: `110:76` unused simp argument `Fin.append_left`; unused source variables at `115:5` hμ, `115:42` hIc, `115:59` hR, `115:72` hRR, `116:5` hd, `117:51` hP. Contrary to the handoff's unused-variable list, **hσ is used** (`hσ.1` at line 143) and receives no unused-variable warning. Other replayed warnings belong to upstream Gradient:168 and Coordinates:118–236 (unused simp/tactics and unreachable tactics); no additional audited Hessian warning appeared. These were warning diagnostics, not failed jobs; no warning-suppression option was added. The job count includes cached/replayed dependency jobs, not a clean rebuild.

### Exact-type/body probe and axiom audit — PASS, exit 0

```
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11E3Audit.lean
```

All six `rfl` definition comparisons, five copied signed theorem bodies and five full polymorphic `type_of%` comparisons elaborated with no diagnostic. Complete axiom output:

```
'KAM.Nekhoroshev.domain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.domain_field' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.polyNbhd_realBall_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.realPart_hessian_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.FastConvex.toRealFastConvex' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hessian_at_sign' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.hessian' depends on axioms: [propext, Classical.choice, Quot.sound]
```

This covers **every new public theorem** in the audited files. In particular there is no `sorryAx` dependency.

### Kernel replay — PASS, exit 0

One invocation, after the exact-type/axiom probe completed:

```
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Partial.Domain KAM.Nekhoroshev.Partial.Hessian
```

Complete output:

```
replaying KAM.Nekhoroshev.Partial.Hessian
replaying KAM.Nekhoroshev.Partial.Domain
```

### Source lint

```
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the permitted stale generated root. Complete output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (899 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The brief explicitly permits this generated-root exception; it is a **PASS WITH NOTES for hygiene**, not a waiver of F1/F2. KAM.lean was not regenerated. No other source-lint violation appeared.

### Final artifact checks

Removed `.lake/abi-scratch/N11E3Audit.lean` after the checks. Final `git diff --check` exits 0; report trailing-whitespace check returns `[]`; `git diff --no-index --check /dev/null <report>` emits no whitespace diagnostic (exit 1 denotes the new file's diff). Protected-path three-dot diff is still empty. Status retains only the pre-existing untracked handoff and this new untracked audit report. No tracked edits or state-changing git commands occurred.

Return the slice for the two missing companion proofs described in F1/F2. The existing signed declarations, definitions and checked theorem bodies need no signature change. Passing compilation, axioms, kernel replay and the permitted lint exception certify the implemented results; they do not pay the literal graph clauses omitted from this package.
