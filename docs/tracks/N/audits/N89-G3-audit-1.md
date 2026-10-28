# Independent package audit: N89-G3

**Overall verdict: PASS WITH NOTES.** The scoped volume package implements its full design contract with sound proofs and no added source premises. All four principal theorems PASS. This is an infrastructure package audit: no frozen theorem anchor is assigned, sealed, or closed by G3, and no N-HEAD-C closure is claimed.

Audited worktree: `/root/code/KAM-inp-n89g3`; HEAD `0d950561ee45ace5d270bd834e9a80a261d55e26` (2026-10-28). Report destination follows the user's explicit worktree path, overriding the generic brief's main-worktree destination.

## Scope, authority, and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/N/audits/N89-G3-handoff.md`. Mathematical authorities inspected: `docs/tracks/N/design/N89-LEAN-DESIGN.md` (especially decisions 2/4, G3 ownership, and Appendix A), both design audits at `docs/tracks/N/design/DESIGN-N89-design-audit-{1,2}.md`, the original `/root/code/KAM-inp/.drafts/design/N89Signatures.lean`, `blueprint-N/parts/p8-resonance-geometry.tex:15–91`, and the track-N statement. The original signatures are absent from this worktree's `.drafts/design/`; the handoff's design-audit reports live in `design/`, not `audits/`. The actual original and checked-in reports were read at their existing paths.

Executed the requested `git diff inp...HEAD`. At audit time `inp` was `ef8fc426c638557035e6101216aad4ef8b8a570e`; Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 313c5e7e5854640055fcd8089ff18446da1fe5c3
```

That comparison lists `Projection.lean` (230 additions) and `Volume.lean` (447 additions). Per the explicit AUDIT FOCUS, the independently audited production file is **only** `KAM/Nekhoroshev/ResonanceGeometry/Volume.lean`; inherited G1/G2 infrastructure was read as dependency context, not re-certified here. Also compared `git diff inp-n89g2...HEAD -- 'KAM/Nekhoroshev/ResonanceGeometry/Volume*.lean'`: exactly one new file, 447 additions. `inp-n89g2` resolved to `6c89ccae4c16ba53632e696453999ef94730fb14`; its unrestricted triple-dot diff includes other merged history, so it must not be represented as a one-file global diff.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` has no diff output (only the same merge-base warning). No protected or generated file was edited by this audit.

## Statement and proof assessment

The bodies of `gram`, `volume_def`, and `addVector`, and the complete declaration headers of `lattice_volume`, `lattice_volume_index`, `lattice_volume_cyclic`, and `lattice_volume_hadamard` are literally equal to the original design signatures. Fresh declarations copying those four signatures with bodies `by exact lattice_volume Λ`, `by exact lattice_volume_index b c N hN`, `by exact lattice_volume_cyclic g hg`, and `by exact lattice_volume_hadamard v hv` elaborate successfully. There is no provider/frozen type-equality or seal-body check to perform: this package adds ordinary infrastructure declarations in `KAM.Nekhoroshev`, with no provider export or frozen anchor.

`lattice_volume` retains: arbitrary-basis Gram identity; positive integer square; lower bound one; bottom volume one; top volume one; equal-rank sublattice monotonicity; and all three add-vector conclusions. Index, cyclic, and Hadamard formulas are separately public, as required. The explicit `euclid` function is the Euclidean length from `Interfaces/Norms.lean`, rather than the max norm of the ambient function type. No Hamiltonian premise, short basis, saturation, primitive generator, positive dimension, or conclusion-shaped hypothesis was introduced. Results also hold for n=0, a valid stronger extension of the blueprint's n≥1 convention.

At `Volume.lean:55–88`, positivity comes from real independence of an actual integer basis and `Matrix.PosDef.conjTranspose_mul_self`; basis changes use the proved unimodular coordinate relation. The chosen basis affects neither the square nor the nonnegative root. Empty rank is handled by the empty determinant, not a fallback value. The index proof compares nonnegative squares; monotonicity separately supplies nonvanishing of the integer determinant from equal-rank inclusion.

At `Volume.lean:158–233,337–394`, the add-vector argument proves a genuine appended integer basis, represents the projection by coefficients in the old span, and subtracts that projection using an explicit unitriangular matrix of determinant one. Last-row determinant expansion for the orthogonal appended column gives `det Gram(A) * (c ⬝ᵥ c)`. Taking nonnegative square roots proves the exact product. The auxiliary orthogonality hypothesis in `det_gram_snoc_orth` is legitimate data for that separately named matrix helper and is discharged from G2 in `addVector_facts`; the hard geometric step is not assumed by the exported result. This is an explicit alternative proof of the blueprint's Schur-complement step (`p8:86`), avoiding an inverse and working uniformly at rank zero. It preserves the source statement; it is a proof-route deviation only.

The cyclic formula uses a genuine one-vector basis with g≠0. Hadamard at `Volume.lean:413–445` uses independence of the initial subfamily, the exact generated-subgroup identity, nonmembership of the final vector in the earlier real span, and the complementary projection bound from G2. Both factors in the product comparison have the needed nonnegative signs.

## Declaration-by-declaration results

All names below are in `KAM.Nekhoroshev`; line numbers refer to `Volume.lean`. Helpers with no separately prescribed design signature were assessed against their stated algebraic role and actual use in the blueprint proof. Their conditional assumptions are explicit typing or independence/orthogonality data and are discharged at use.

| Node / proof step | Lean declaration | Verdict | Reason |
|---|---|---|---|
| `bpN:p8:volume-def` | `gram` (L29) | PASS | Literal design body: real Gram matrix of integer columns. |
| `bpN:p8:volume-def` | `volume_def` (L32) | PASS | Literal design body; all ranks, including the empty determinant. |
| `stepN:p8:lv-ab` | `gram_eq_map` (L38) | PASS | Integer Gram matrix transported through the real ring homomorphism. |
| `stepN:p8:lv-ab` | `gram_det_eq` (L43) | PASS | Determinant commutes with integer-to-real casting. |
| `stepN:p8:lv-ab, lv-c` | `gramZ_det_mul` (L48) | PASS | Exact determinant-square identity for every square integer coordinate matrix. |
| `bpN:p8:ext-gram` | `gramZ_det_pos` (L55) | PASS | Basis real independence gives injective mulVec and positive Gram determinant. |
| `stepN:p8:lv-ab` | `gramZ_det_basis_change` (L74) | PASS | Unimodular determinant squared is one. |
| `stepN:p8:lv-ab` | `volume_sq_eq` (L81) | PASS | Every integer basis, with dimension identified by basis_card_eq_latticeDim. |
| `bpN:p8:volume-def` | `volume_nonneg` (L90) | PASS | Square-root nonnegativity; no hidden assumption. |
| `stepN:p8:lv-ab` | `volume_sq_int` (L92) | PASS | Positive integer witness, not merely a nonnegative real square. |
| `bpN:p8:lattice-volume(b)` | `one_le_volume` (L96) | PASS | Positive integer square and nonnegative volume imply the bound. |
| `bpN:p8:volume-def` | `volume_bot` (L103) | PASS | Empty determinant equals one; square-root sign resolved. |
| `stepN:p8:lv-d` | `topBasis` (L112) | PASS | Standard integer coordinate basis transported to the top subgroup. |
| `stepN:p8:lv-d` | `basisMatrix_topBasis` (L115) | PASS | Basis matrix equals the identity, including n=0. |
| `bpN:p8:lattice-volume(d)` | `volume_top` (L119) | PASS | Identity Gram determinant and nonnegative square root. |
| `stepN:p8:lv-c` | `lattice_volume_index` (L128) | PASS | Literal design type; exact absolute determinant factor, no extra inclusion premise. |
| `bpN:p8:lattice-volume(c)` | `volume_mono` (L142) | PASS | Equal-rank inclusion gives a nonzero integer determinant of modulus at least one. |
| `stepN:p8:lv-e` | `snocCol` (L158) | PASS | Appends the actual column on every matrix entry. |
| `bpN:p8:ext-schur / lv-e` | `det_gram_snoc_orth` (L163) | PASS | Orthogonal appended column gives a block Gram determinant via last-row expansion. |
| `stepN:p8:lv-e` | `shearMat` (L195) | PASS | Identity with last column subtracting the coefficient vector; final diagonal entry remains one. |
| `stepN:p8:lv-e` | `det_shearMat` (L199) | PASS | Upper triangular with diagonal one, including d=0. |
| `stepN:p8:lv-e` | `snocCol_mul_shear` (L213) | PASS | Exact column subtraction kv minus A.mulVec x. |
| `stepN:p8:lv-e` | `det_gram_snoc_shear` (L223) | PASS | Gram determinant invariant under the determinant-one column shear. |
| `bpN:p8:ext-indep` | `integer_independent_of_real` (L238) | PASS | Restricts real independence to integer scalars; no converse assumed. |
| `stepN:p8:lv-e` | `closureBasis` (L246) | PASS | Actual basis of the generated subgroup from integer independence. |
| `stepN:p8:lv-e` | `basisMatrix_closureBasis` (L260) | PASS | Columns are exactly the given integer vectors. |
| `stepN:p8:lv-e` | `latticeDim_closure` (L265) | PASS | Dimension follows from a genuine basis. |
| `stepN:p8:lv-e, lv-f` | `lattice_closure_range` (L269) | PASS | Generated subgroup has exactly the stated real span. |
| `stepN:p8:lv-e` | `basis_closure_eq` (L278) | PASS | Basis generates the entire subgroup, in both directions. |
| `stepN:p8:lv-d` | `lattice_volume_cyclic` (L292) | PASS | Literal design type; nonzero generator, 1-by-1 Gram determinant, explicit Euclidean length. |
| `bpN:p8:lattice-volume(e)` | `addVector` (L314) | PASS | Literal design body: subgroup sum with the cyclic subgroup. |
| `stepN:p8:lv-e` | `addVector_eq_closure_snoc` (L317) | PASS | Exact subgroup equality for appended chosen basis. |
| `stepN:p8:lv-e` | `snoc_independent` (L324) | PASS | Outside the real span ensures real, then integer, independence. |
| `bpN:p8:lattice-volume(e)` | `addVector_facts` (L337) | PASS | Dimension increment, exact volume product, and nonzero orthogonal component all proved. |
| `bpN:p8:lattice-volume` | `lattice_volume` (L398) | PASS | Literal design type; all seven conjuncts retained. |
| `stepN:p8:lv-f` | `lattice_volume_hadamard` (L413) | PASS | Literal design type; induction with add-vector identity and contractive complementary projection. |

## Definition classification and imports

There are seven new definitions, no abbrevs or structures:

| Definition | Classification on its whole carrier |
|---|---|
| `gram` | Real transpose-product of the integer matrix cast entrywise; defined correctly even without independence. |
| `volume_def` | Genuine lattice covolume from an actual basis; positive radicand and arbitrary-basis identity proved for every lattice, including bottom. |
| `topBasis` | Standard integer basis transported through the top-subgroup equivalence for every n. |
| `snocCol` | Entrywise append of the supplied real column for all n,d, including d=0. |
| `shearMat` | Actual determinant-one elementary column shear for every coefficient vector and d. |
| `closureBasis` | Basis of the actual generated subgroup, under exactly integer linear independence; construction proves spanning by subgroup closure induction. |
| `addVector` | Exact subgroup supremum Λ + ℤk for all Λ,k, whether or not rank increases. |

No junk object, fallback branch, fabricated inverse, additional global instance, or carrier change occurs. `@[expose] public noncomputable section` exposes the definitions that must unfold.

Direct KAM imports are only `ResonanceGeometry.Lattice` and `Projection`. A recursive KAM import scan reached 57 modules, no provider, and no frozen theorem module. Its 19 frozen definition modules all have manifest state `SEALED`; none has state `DRAFT_SORRY`. In particular the existing frozen frequency, Hamiltonian, realPart, and solution definitions were inspected as inherited context. G3's actual premises and conclusions remain pure subgroup/linear algebra, and it does not substitute for a frozen dynamical statement. The all-theorem axiom audit below independently excludes inherited `sorryAx` from every new theorem.

## Independent validation

The explicit build, signature/axiom probe, kernel replay, and final lint invocation used `LEAN_NUM_THREADS=1`; these checks completed sequentially, with no second audit Lean job launched while one was pending. The final lint was launched under `nice -n 5` so its internal ABI Lean process inherits that priority. No resource override, package-cache mutation, root regeneration, full-library target, or state-changing git command was used.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g3 KAM.Nekhoroshev.ResonanceGeometry.Volume
```

Exit **0**. Exact output:

```text
[inp-gate] slot 1 acquired 07:44:08 for KAM.Nekhoroshev.ResonanceGeometry.Volume
⚠ [3190/3212] Replayed KAM.Nekhoroshev.Stability.Gradient
warning: KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name `hgr` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hgr

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (3212 jobs).
```

The warning is inherited dependency output; `Volume.lean` emitted no warning. The job count is Lake's dependency-graph count, not a claim that this targeted command rebuilt all modules.

2. Signature and all-public-theorem axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G3Audit.lean
```

Exit **0**, no errors or warnings. Four copied design declarations elaborate with exact applications to their corresponding production theorems; every production theorem was queried. Exact axiom output:

```text
'KAM.Nekhoroshev.gram_eq_map' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.gram_det_eq' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.gramZ_det_mul' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.gramZ_det_pos' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.gramZ_det_basis_change' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.volume_sq_eq' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.volume_nonneg' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.volume_sq_int' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.one_le_volume' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.volume_bot' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.basisMatrix_topBasis' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.volume_top' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.lattice_volume_index' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.volume_mono' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.det_gram_snoc_orth' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.det_shearMat' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.snocCol_mul_shear' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.det_gram_snoc_shear' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.integer_independent_of_real' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.basisMatrix_closureBasis' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.latticeDim_closure' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.lattice_closure_range' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.basis_closure_eq' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.lattice_volume_cyclic' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.addVector_eq_closure_snoc' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.snoc_independent' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.addVector_facts' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.lattice_volume' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.lattice_volume_hadamard' depends on axioms: [propext, choice, Quot.sound]
```

Lean prints `choice` for the permitted classical choice axiom. No theorem depends on `sorryAx` or any additional axiom. The temporary probe is deleted after validation.

3. Kernel replay (one invocation; no provider or additional new lemma module exists):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.Volume
```

Exit **0**. Exact output:

```text
replaying KAM.Nekhoroshev.ResonanceGeometry.Volume
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (460 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

There are no line-length, source-escape, module, frozen-guard, or ABI failures.

5. Static and diff checks: `Volume.lean` has **447 lines**, longest line **98 Unicode characters**, below both limits. A scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, and `set_option` returns no matches. The copyright, `module`, public imports, module docstring, exposed public section, and ambient coordinate types satisfy the file rules. `git diff --check` exits **0**, without output. No production/provider quarantine violation was found.

## Uncertainties, errata, deviations, and handoff

No suspected new blueprint defect, frozen-statement defect, source erratum, or heartbeat design signal was found. No pinned PDF was independently re-audited; the source-fidelity assessment here is against the prescribed blueprint and original Lean design signatures. The only proof-route deviation is the explicit shear/block-determinant proof in place of the blueprint's inverse-based Schur formula, justified above. Generated-root staleness is the exact lint exception allowed by this audit brief; the orchestrator owns regeneration. The inherited Gradient warning is nonblocking and outside scope.

Authored file: `/root/code/KAM-inp-n89g3/docs/tracks/N/audits/N89-G3-audit-1.md` only. The pre-existing untracked `N89-G3-handoff.md` is preserved. Temporary audit scratch is removed; no production, frozen, manifest, generated, blueprint, or design file is edited. No root theorem or earlier G1/G2 package is newly certified by this report.
