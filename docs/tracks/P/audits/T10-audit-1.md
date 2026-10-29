# T10 independent package audit 1

**Overall: FAIL the requested complete-slice gate (F1). The two signed exports PASS.**
No proof-soundness, extra-premise, signature, carrier, or constant-dependence defect was found
in `KAM.Planetary.real_lie_taylor` or `KAM.Planetary.lie`. However, the literal intermediate
conclusion of the assigned graph node `stepP:p11b:li-ord` is not established. The implementation
proves the parent estimate by a valid different route. That distinction must be retained under
the handoff's explicit requirement that every assigned graph node be established.

There is no provider or frozen theorem anchor in T10; “seal-ready” is inapplicable. This report
does not close P-G, P-PLANAR, P-FIXED, or the later physical Birkhoff assembly.

## Scope and authority

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-p11c-t10`.
HEAD: `74ee13aa7d425f95aef1d532d9ec70bae0faf262`.
Comparison ref `inp`: `086928650ca9281e65a68123f75f45436881167a`.
`git diff inp...HEAD` warns about multiple merge bases and uses
`8f19267d4a71f86284c9979293b8f991fb2c0b96`.

Read AGENTS.md, PLAN, DECISIONS, the package brief, T10 handoff, P statement,
P11C design and its available design audit 1, standalone signatures, the relevant blueprint
and graph records, and the used coordinate/jet/bracket/flow definitions. Only the four
NormalForm files are audited. The full three-dot diff also contains six inherited T9
QuarticFlow files; these were inspected for scope/dependency attribution, not independently
reaudited as T9. The protected-path diff is empty. The user's exact worktree report path
overrides the generic brief's main-worktree destination.

Current input SHA-256:

| Input | SHA-256 |
|---|---|
| P11C design | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `6a9b154b4d1d18dc40d41e41a914452c3efe6f8ebe8a9701f3d23b1c2c07c5b7` |
| `blueprint-P/parts/p11b-planar-torsion.tex` | `f8ce70a3460c855e1e04ea1a8d39c7a32a550f38b8097ca993a6a17efe012bf1` |
| `docs/graph/P/DEPGRAPH.md` | `4fd42e5a9a5648fee2974afcdacfcb9e5d02f2496379e983fc2f7d204a087c96` |

The current signature hash differs from the historical design-audit receipt. Both T10
statements were compared with the current signature file, not inferred from that receipt.

## F1 — Medium: literal Orders node remains unproved

Authority: design `P11C-LEAN-DESIGN.md:118–121` assigns all four nodes below to T10;
section 4 says their “exact obligations remain the labelled source step and graph contract.”
The handoff additionally requires the slice to be COMPLETE.

`blueprint-P/parts/p11b-planar-torsion.tex:162` says
“`\{\mathcal R,\chi\}=O(\lvert z\rvert^8)`” and
“`\{\{K,\chi\},\chi\}=O(\lvert z\rvert^6)`”.
`docs/graph/P/DEPGRAPH.md:30708` expressly retains these in SOURCE_CONCLUSION,
together with `{K,chi}=-(F-<F>)+O(|z|^6)` and the double-bracket trajectory bound.

Actual implementation: `NormalForm.lean:108` applies Taylor only to `N0`.
Lines 109–126 replace its first bracket by `-D`, and bound the brackets of the quartic
families F and D. Lines 154–165 bound `R(I,g 1)` directly using
`p11cN_remainder_bound`; lines 166–184 sum these terms. No local assertion or export
establishes the bracket of R, the first bracket of the full K, or its double bracket.
The uniform sixth-order bound on R itself is not the literal derivative-order statement.

This is a coverage/deviation finding, not a false theorem or an unpaid inequality in the
signed `lie` proof. It does not require changing either signed statement. To satisfy the
current complete-slice contract, prove the missing literal Orders assertions from the
source analytic/jet hypotheses. Alternatively the orchestrator can explicitly adopt and
record a route substitution under DECISIONS D27: mark the unused intermediate node
BYPASSED and cite this proof and audit, rather than mark its literal conclusion PROVED.
This report does not silently perform that graph change or waive the user's completeness gate.

## Node coverage

Names below are in `KAM.Planetary`.

| Node | Lean declaration / proof location | Verdict | Reason |
|---|---|---|---|
| `bpP:p11b:lie` | `lie`, NormalForm:62–184; imported `average_action_polynomial` | PASS | Exact signed compact-uniform sixth-order estimate; average is the actual torus average, with analytic quadratic action polynomial supplied by T7. |
| `stepP:p11b:li-tay` | `p11cN_hasDerivAt`, `real_lie_taylor`, Taylor:55–101 | PASS | Actual solution, chain rule, integrability, integration by parts and FTC; closes the real/complex applicability gap without a SmallField premise. |
| `stepP:p11b:li-ord` | NormalForm:109–165; Bounds; Remainder | FAIL completeness | Cubic-gradient products and composed R suffice for the parent, but full-K and R-bracket assertions are bypassed; F1. |
| `stepP:p11b:li-sum` | NormalForm:166–184; Bounds:99–103; imported `average_action_polynomial` | PASS | Exact cancellation and sixth-order bound; action-polynomial conclusion supplied by the actual average formula. |

## Every new public declaration

All 16 declarations are theorems. Auxiliary rows describe their mathematical role rather
than claim separate blueprint nodes or treat helper hypotheses as source theorems.

| Declaration | Location | Verdict | Reason |
|---|---|---|---|
| `real_lie_taylor` | Taylor:64 | PASS | Signed statement exactly matches signature L470–475 modulo whitespace; fresh application with all explicit binders elaborates. `hU` is unused but retained verbatim. |
| `lie` | NormalForm:62 | PASS | Signed statement exactly matches signature L477–487 modulo whitespace; fresh application with all explicit binders elaborates. A,r precede I,z; vanishing five-jet and joint analytic germs retained. |
| `p11cN_flow_congr` | NormalForm:41 | PASS | Equality of parameter slices gives equality of the selected flows, including their total definitions. |
| `p11cN_bracket_le` | NormalForm:47 | PASS | Operator norm evaluation and cubic bounds imply the sixth-power bound; bound premises are generic helper inputs proved at the call sites. |
| `p11cN_clm_apply` | Taylor:31 | PASS | Analytic bilinear evaluation of an analytic map family and vector. |
| `p11cN_field_analytic` | Taylor:38 | PASS | Analytic derivative coordinates give the literal frozen Hamiltonian vector field. |
| `p11cN_bracket_analytic` | Taylor:49 | PASS | Analytic derivative evaluation gives the actual bracket on U. |
| `p11cN_hasDerivAt` | Taylor:55 | PASS | Chain rule at every supplied solution time; no flow existence assumed beyond its explicit solution input. |
| `p11cN_bracket_neg` | Taylor:104 | PASS | Oddness in the first observable, using total fderiv negation. |
| `p11cN_first_order` | Taylor:109 | PASS | First-order FTC along an actual solution, with integrability proved. |
| `p11cN_iteratedFDeriv_line` | Remainder:32 | PASS | Affine-line derivative identity on the open differentiability domain, for all k including zero. |
| `p11cN_remainder_bound` | Remainder:56 | PASS | Joint analytic germs plus compactness give one positive radius and uniform sixth-order bound, including z=0 and empty K. A need not be positive here; lie uses its absolute value. |
| `p11cN_fderiv_slice` | Bounds:32 | PASS | Joint derivative composed with the actual inr map equals the phase-slice derivative. |
| `p11cN_grad_bound` | Bounds:44 | PASS | Sphere compactness and quartic homogeneity yield a positive uniform cubic gradient constant; zero phase handled separately. |
| `p11cN_sub_family` | Bounds:90 | PASS | Coefficientwise subtraction produces an actual quartic family, for every I,z. |
| `p11cN_average_family` | Bounds:99 | PASS | Actual normalized torus average represented by a quartic family on O via proved T7 action coefficients and T8 action realization. |

There are no extra source premises or conclusion-shaped inputs in either signed theorem.
The generic bound helpers take the estimates they combine, but `lie` obtains every such
estimate from proved quartic/compactness/flow results. C has no regularity premise because
it cancels at the same parameter. This strengthens the analytic-source version as intended
by the design. No production consumer of these new exports exists yet in this worktree.
The designed T16 consumer receives the unchanged signed estimate and the imported analytic
average polynomial; the direct remainder route imposes no new consumer obligation.

## Definition classification and proof review

**No new def, abbrev, structure, instance, notation, or root-level declaration.** All exports
live in `KAM.Planetary`; the 14 auxiliary names have the unique `p11cN_` prefix, with no
duplicate declaration elsewhere in KAM. The signed short name `lie` is the required signature.

Used objects retain their owning definitions: `Phase 2` is the product of two Pi spaces;
its norm is the max norm. `p11c_slowLength` is the explicit Euclidean four-coordinate length;
`oscillatorAction` is `(p²+q²)/2`; `p11c_bracket G X` is `dG(X_X)` with the frozen field sign.
`p11c_JetEq 5 f 0` equates all iterated derivatives through order five to those of zero,
including the value at zero. QuarticFamily is a finite homogeneous degree-four polynomial
with analytic coefficients, not an assumed normal form. The average is the normalized
radian character integral, not a substitute function.

The inherited `p11c_flow` has an identity fallback outside existence. `lie:79–94` obtains
the actual solution and its initial value from T9 `flow`, after shrinking the radius, and
transports from the homological quartic representative using `p11cN_flow_congr`.
No estimate uses the fallback. The local analytic/compact proof of the remainder bounds
the sixth derivative on `K × closedBall 0 (delta/2)`, restricts to rays, proves every lower
Taylor term zero, and applies Mathlib's Taylor bound. Its `B/120` coefficient is a valid
coarse bound, not a claim of the sharper factorial coefficient.

Norm conversion is explicit: the trajectory satisfies `‖g t‖² ≤ 2 slowLength(z)²`, hence
`‖g t‖⁶ ≤ 8 slowLength(z)⁶`. Radius `min r1 (rR/2)` keeps the endpoint in the remainder
ball. The final positive constant is
`8*(Cf*Cx) + 8*(CD*Cx) + 8*|AR| + 1`. Compactness fixes all these constants before I,z.
The two interval integral bounds and endpoint remainder bound are combined by an exact
identity; no regularity of the slow-independent C is used.

## Independent validation

All Lean-bearing commands below are sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No clean/update/cache command, heartbeat override, generated-root edit, frozen edit,
manifest edit, or git mutation was made. Probe files are confined to `.lake/abi-scratch/`.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t10 KAM.Planetary.PlanarTorsion.NormalForm
   [inp-gate] slot 1 acquired 22:42:36 for KAM.Planetary.PlanarTorsion.NormalForm
   Build completed successfully (9174 jobs).
   exit 0
   ```

   The gate invokes `nice -n 5 lake build`. The only T10 warning is
   `NormalForm/Taylor.lean:64:45: Variable name hU is not explicitly referenced.`
   Other replayed warnings are inherited unused binders/deprecations in Kepler, Poincare,
   Characters, Hamiltonian.Algebra and Homological. No sorry or elaboration failure.

2. Fresh signed-statement/application and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T10Audit.lean
   exit 0; no errors or warnings
   ```

   Each `example` copied the complete statement from the current signature file, and used
   respectively `by exact real_lie_taylor hU K chi hK hc g hg` and
   `by exact lie hO F freq hf hnr C R hR hj K hK hKO`.
   Provider/frozen `type_of%` seal probes are inapplicable because neither exists here.
   The same file ran `#print axioms` for every name in the declaration table. Exact result
   for each of the 16 exports: `[propext, Classical.choice, Quot.sound]`.

   ```text
   'KAM.Planetary.p11cN_flow_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_bracket_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.lie' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_fderiv_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_grad_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_sub_family' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_average_family' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_iteratedFDeriv_line' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_remainder_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_clm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_field_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_bracket_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.real_lie_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_bracket_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.p11cN_first_order' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.NormalForm KAM.Planetary.PlanarTorsion.NormalForm.Taylor KAM.Planetary.PlanarTorsion.NormalForm.Remainder KAM.Planetary.PlanarTorsion.NormalForm.Bounds
   replaying KAM.Planetary.PlanarTorsion.NormalForm
   replaying KAM.Planetary.PlanarTorsion.NormalForm.Remainder
   replaying KAM.Planetary.PlanarTorsion.NormalForm.Taylor
   replaying KAM.Planetary.PlanarTorsion.NormalForm.Bounds
   exit 0
   ```

4. Source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1036 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   PASS WITH NOTES under the brief's explicit generated-root exception: the sole failing
   check is stale KAM.lean. It was left untouched. The ABI subprocess inherited the single
   thread setting and niceness; no other Lean command from this auditor ran concurrently.

5. Static/source checks:

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   [empty diff; multiple-merge-base warning only; exit 0]
   git diff --check inp...HEAD
   [no whitespace errors; multiple-merge-base warning only; exit 0]
   ```

   Recursive local import inspection visits 128 KAM modules: no provider, no frozen theorem
   imports; all 47 frozen files are definition anchors listed as SEALED in the manifest.
   Forbidden-token/resource-option/EuclideanSpace scan: no matches in the four audited files.
   Each file has copyright, `module`, public imports, module docstring, and a public section.

   | File | Physical lines | Maximum characters per line |
   |---|---:|---:|
   | NormalForm.lean | 188 | 98 |
   | NormalForm/Taylor.lean | 126 | 97 |
   | NormalForm/Remainder.lean | 142 | 100 |
   | NormalForm/Bounds.lean | 107 | 97 |

   Total 563 physical lines (the handoff's 560 is a minor counting discrepancy).

## Errata, deviations and remaining uncertainty

No new pinned-source mathematical defect was identified. F1 is a proof-route deviation
from the literal blueprint/graph intermediate assertions, omitted from the prover's
“Errata / deviations: None” receipt. No signed declaration changed, and no frozen defect
was found. The real Taylor export supplies the missing real bridge recorded in the
graph's li-tay SOURCE_GAP; the older complex SmallField theorem is not applied.

The design's historical graph hash and historical signature receipt are not current
snapshot identities; current hashes are recorded above. No external source PDF audit or
independent T9 re-audit is claimed. The unresolved complete-slice issue is exactly F1;
proof validity of the signed estimate and closure of the literal Orders node remain
separate verdicts.

Final report validation: `git diff --no-index --check /dev/null` on this report passes;
no PENDING placeholders remain. All four auditor scratch files (probe, import inventory,
kernel log, lint log) were removed. Final tracked working-tree diff is empty; git status
contains only this report and the pre-existing untracked T10 handoff. No commit was made.
