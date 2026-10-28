# Independent package audit: N89-G1

Date: 2026-10-28. **Overall verdict: PASS WITH NOTES**. This is a lattice infrastructure package; no frozen anchor is supplied or sealed. Provider/frozen-type equality and seal-body probes are **not applicable**. No N-HEAD-C, N-QC, N-ZERO, or other root closure is asserted.

## Scope and authorities

Audited `git diff inp...HEAD` in `/root/code/KAM-inp-n89g1`: HEAD `3bc810616832f3503fdb659df109290b98859330`, current inp `33c688a1d1c9d25d7099f328479f4f53b0301bb4`. The entire branch diff adds only `KAM/Nekhoroshev/ResonanceGeometry/Lattice.lean` (216 lines). Module SHA-256: `4ebb9fafcd1aff16338d99e99e829f54ccae55fdfa1faf82dc4a530418c87c69`.

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff and its AUDIT FOCUS, track-N statement conventions, design N89 §4–6 and G1 proof plan, and both `docs/tracks/N/design/DESIGN-N89-design-audit-{1,2}.md`. Compared raw blueprint `blueprint-N/parts/p8-resonance-geometry.tex:7–46`, with p9 setting and consumers as context. Reviewed upstream `resSpan`, `resSpace`, and `euclid` bodies and the Mathlib scalar-extension/PID APIs. No source PDF was independently re-audited, and no external source lookup was needed for this repository-source audit.

The supplied original `.drafts/design/N89Signatures.lean` lives in `/root/code/KAM-inp`, not this package checkout; its SHA-256 is `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`, matching design audit 2. All five main theorem headers match it **byte for byte**. The eight new definition/abbreviation bodies also match their intended signature definitions. The explicit user path overrides the generic brief's MAIN-worktree output instruction: this report is inside the package worktree.

## Declaration and node results

All names below are in `KAM.Nekhoroshev`; line numbers refer to Lattice.lean. PASS means the stated component passes, subject to the package notes below.

| Blueprint node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| p8:lattice | `Lattice` (31) | PASS | Literal additive subgroup of integer coordinate vectors. |
| p8:lattice | `lattice` (32) | PASS | Literal real span of all subgroup vectors. |
| p8:lattice | `latticeDim` (33) | PASS | Real dimension of that span. |
| p8:lattice / casting | `integerReal` (34) | PASS | Coordinatewise integer-to-real inclusion. |
| p8 conventions | `eBall` (35) | PASS | Closed Euclidean cutoff, with no ambient max-norm substitution. |
| p8:lattice | `resonance` (36) | PASS | All integer dot-product equations via upstream `resSpace`. |
| p8:lattice-basis | `basisMatrix` (37) | PASS | Integer columns of an actual basis. |
| p8:ext-indep | `integer_independent_real` (41) | PASS | Integer independence genuinely implies real independence, no extra premise. |
| Casting helper | `integerReal_injective` (48) | PASS | Injectivity follows coordinatewise from integer casting. |
| Span helper | `integerReal_mem_lattice` (54) | PASS | Subgroup member is in the defining real span. |
| p8:ext-free / lb-basis helper | `basis_val_linearIndependent` (59) | PASS | Subtype inclusion preserves integer basis independence. |
| p8:ext-indep helper | `basis_real_linearIndependent` (64) | PASS | Applies the proved scalar-extension step. |
| Coordinates helper | `basisMatrix_apply_repr` (69) | PASS | Exact integral reconstruction from basis coordinates. |
| lb-basis helper | `basis_span_eq` (78) | PASS | Both span inclusions proved; no rationality assumption on real coefficients. |
| lb-basis helper | `basis_card_eq_latticeDim` (99) | PASS | Real independence plus spanning computes rank. |
| p8:ext-free / lb-basis helper | `exists_basis` (105) | PASS | PID submodule basis transported through the actual subgroup carrier. |
| p8:lattice-basis(a), stepN:p8:lb-basis | `lattice_basis` (109) | PASS | Rank bound, rank-sized basis, integer/real rank equality and every finite basis covered. |
| p8:lattice | `lattice_resonance` (123) | PASS WITH NOTES | Orthogonal-complement equality and zero-rank equivalence proved; dimension formula is G2 scope (see N2). |
| p8:lattice-basis choice | `latticeBasis` (156) | PASS | Selects an existing basis of the proven rank. |
| lb-unimod helper | `basisMatrix_eq_mul` (159) | PASS | Change matrix entries are exactly basis coordinates. |
| p8:lattice-basis(b), stepN:p8:lb-unimod | `lattice_basis_change` (165) | PASS | Integral unimodular transition and converse both proved. |
| p8:lattice-basis(c), stepN:p8:lb-sub | `lattice_basis_sub` (187) | PASS | Equal-rank inclusion yields an integer matrix with nonzero determinant. |

## Premises, definitions and proof review

Binder audit: the following table expands every kind of public input; ambient implicit `n : ℕ` occurs in each theorem. All omitted logical bins are zero. The dimensions, vectors, subgroup carriers, indices, elements and basis objects are TYPING; subgroup inclusion, membership, integer independence and unimodularity are SOURCE. There is no extra instance binder. Canonical Mathlib algebra/module instances are determined by these carriers. A `Basis` contains linear independence and spanning as its mathematical definition; asking for a basis in a basis-change theorem is source data, whereas existence is proved separately.

| Declarations | Expanded inputs in order (after implicit n) | Classification / source |
|---|---|---|
| `integer_independent_real` | implicit d; v; hv | d,v TYPING; hv SOURCE: p8:ext-indep |
| `integerReal_injective` | none | TYPING n only |
| `integerReal_mem_lattice` | implicit Λ; implicit k; hk | Λ,k TYPING; hk SOURCE: p8:lattice span membership |
| `basis_val_linearIndependent`, `basis_real_linearIndependent`, `basis_span_eq`, `basis_card_eq_latticeDim` | implicit d; implicit Λ; b | All TYPING: p8:lattice-basis(a), an actual basis |
| `basisMatrix_apply_repr` | implicit d; implicit Λ; b; x; i | All TYPING: basis, element of subgroup, coordinate index |
| `exists_basis`, `lattice_basis`, `lattice_resonance` | Λ | TYPING: arbitrary subgroup |
| `basisMatrix_eq_mul`, `lattice_basis_change` | implicit d; implicit Λ; b; c | All TYPING: two bases of the same subgroup and cardinality |
| `lattice_basis_sub` | implicit d; implicit Γ; implicit Λ; hΓ; b; c | hΓ SOURCE: p8:lattice-basis(c); all others TYPING |
| `lattice_basis` internal universal conclusion | d; b | TYPING: every finite basis, after existential rank/basis conclusions |
| `lattice_basis_change` converse conclusion | U; determinant ±1 proof | U TYPING; determinant condition SOURCE: p8:lattice-basis(b) |

Counts over theorem declaration inputs (not conclusion binders): **TYPING 56, SOURCE 3, STANDING 0, RULED 0, EXCESS 0**, counting shared input occurrences separately. The five main theorems have no changed binder order or constants. No numerical constants or hidden dependence are introduced. Equal dimension in `lattice_basis_sub` is represented by both bases having index `Fin d`; `basis_card_eq_latticeDim` proves equivalence with equality of the source ranks. Source b and c are basis inputs, not assumed existence results.

Definition classification (all eight): `Lattice` is a literal type abbreviation; `lattice`, `latticeDim`, `integerReal`, `eBall`, `resonance`, and `basisMatrix` are literal formulas on their complete declared carriers. For each: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. `latticeDim` is on a finite-dimensional real subspace, so finrank has its intended dimension meaning. `eBall` also has an honest meaning for negative K (empty), and the algebra remains valid at n=0.

`latticeBasis` is an explicitly noncanonical auxiliary selection, not a claim of a unique source-defined basis. BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK via `(lattice_basis Λ).2.1`; CHARACTERIZATION OK by the `Basis (Fin (latticeDim Λ)) ℤ Λ` type; CHOICE_INDEPENDENCE N/A for a selected basis; DEFINITION_VERDICT PASS. No uniqueness of a basis is claimed. Basis-change invariance is supplied for any two bases; basis independence of later volume definitions remains G3's obligation. No default, zero fallback or unproved choice witness is used.

The PID proof applies `Submodule.basisOfPid (Pi.basisFun ℤ (Fin n))` to `Λ.toIntSubmodule`. Transport by `(AddEquiv.refl Λ).toIntLinearEquiv` uses the same additive carrier and integer scalar action. It neither assumes finite generation nor real rank. `basis_span_eq` proves spanning using finite `sum_repr`; real independence then identifies the natural basis size, and `finCongr` reindexes it. The scalar-extension theorem used at line 43 is explicitly for vectors of coordinates over R, mapped coordinatewise through an algebra map to a faithful domain S. Its hypotheses hold for ℤ→ℝ; this is not an invalid arbitrary-module tensor claim.

For basis changes, `b.toMatrix c` has integer entries, and `Basis.isUnit_det` proves determinant ±1. The converse constructs a genuine ℤ-linear equivalence from unit determinant. For subgroup inclusion, basis coordinates yield N, and det N=0 would yield a nonzero real kernel vector annihilated by the real-independent columns of c. The proof covers empty matrices (determinant 1). Resonance equality is proved by real span induction; zero dimension is reduced to the zero span and injectivity of integer casting.

## Validation receipts

The commands below were independently executed in this worktree; prover receipts were not substituted for reruns.

1. Targeted build (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g1 KAM.Nekhoroshev.ResonanceGeometry.Lattice
   ```

   The wrapper runs `nice -n 5 lake build` under the compile gate. Output:

   ```text
   [inp-gate] slot 1 acquired 07:13:10 for KAM.Nekhoroshev.ResonanceGeometry.Lattice
   ⚠ [3189/3210] Replayed KAM.Nekhoroshev.Stability.Gradient
   warning: KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name `hgr` is not explicitly referenced.
   Build completed successfully (3210 jobs).
   ```

   The omitted lines are Lean's generic naming/linter hint. There is no diagnostic in the audited file.

2. Exact-design-type and full axiom probe (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G1Audit.lean
   ```

   Imported the audited module, copied the five original design theorem headers into `example` declarations, and applied the corresponding implementations to their explicit binders (`v hv`, `Λ`, `Λ`, `b c`, `hΓ b c`). These checks use the original design's full statements, not a weakened local reconstruction. Added `#print axioms` for every new public theorem, with exact output:

   ```text
   'KAM.Nekhoroshev.integer_independent_real' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.integerReal_injective' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.integerReal_mem_lattice' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.basis_val_linearIndependent' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.basis_real_linearIndependent' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.basisMatrix_apply_repr' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.basis_span_eq' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.basis_card_eq_latticeDim' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.exists_basis' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.lattice_basis' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.lattice_resonance' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.basisMatrix_eq_mul' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.lattice_basis_change' depends on axioms: [propext, choice, Quot.sound]
   'KAM.Nekhoroshev.lattice_basis_sub' depends on axioms: [propext, choice, Quot.sound]
   ```

   `choice` is the standard choice axiom as printed by this toolchain. There is no `sorryAx` or project axiom.

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.Lattice
   ```

   Exit **0**, exact output:

   ```text
   replaying KAM.Nekhoroshev.ResonanceGeometry.Lattice
   ```

   This is the single required kernel invocation; there are no separate new lemma modules or provider modules in the package.

4. Full repository lint (exit **1**, solely the expressly allowed stale generated root):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (440 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Procedural deviation: an initial unprefixed `sh scripts/lint_sources.sh` was launched while the targeted build command was pending; its internal ABI check invokes Lean. It returned the same four lines and exit 1. That launch did not enforce the requested environment/priority or command serialization. The full lint was therefore rerun with the exact prefix above after both initial commands had exited, followed serially by the probe and kernel replay. The final validation receipts use those corrected commands. No claim is made that the initial launch complied with the process rule.

5. Static and repository checks:

   ```sh
   git diff --stat inp...HEAD
   git diff --check inp...HEAD
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   ```

   The stat is one new file, 216 insertions. Both following commands exit **0** with empty output. A Python scan of the audited module reports **216 lines**, **maximum 99 Unicode characters per line**, and **no forbidden token or set_option**. The complete source was checked for module header, copyright, public imports, docstring, public section and exposed definitions; all conform. No resource override, sorry, admit, axiom, unsafe, opaque or EuclideanSpace occurs. Existing repository lint agrees. Report whitespace and final working-tree checks are recorded below.


## Notes, defects and handoff limits

- **N1 (nonblocking):** the generated root is stale. This is the explicit lint exception allowed by the audit brief; no generated file was changed. The targeted build also replays an existing upstream unused-variable warning at `Stability/Gradient.lean:168:5` for `hgr`; Lattice.lean emits no warning.
- **N2 (coverage boundary):** blueprint p8:29 says the resonance space is the orthogonal complement, “of dimension n-d”. G1 proves the orthogonal characterization; the design's G2 `projection_distance` signature provides the finrank-of-kernel sum. Do not mark the entire p8:lattice dimension assertion closed solely from this module. This is not a changed signature or blocker for the assigned G1 package.
- The scalar-extension proof uses the stronger existing Mathlib base-change API instead of spelling out minors. This is a valid proof-route change within the design's “minors or scalar extension” plan, not a statement deviation. No new suspected source erratum was found. Previously recorded Pos93 issues in the design concern later packages and are not certified afresh here.
- No provider or frozen theorem is imported in the full project import closure (55 modules). Its 19 frozen imports are definitions, all manifest state SEALED. Thus neither a DRAFT_SORRY theorem nor a provider enters transitively. Protected-path branch diff is empty.
- Only this report was authored in the repository. Temporary probes were confined to `.lake/abi-scratch/` and removed after validation. No state-changing git, frozen/manifest/generated-file edit, dependency change or proof repair was performed.

Final checks: `git diff --check inp...HEAD` and `git diff --no-index --check /dev/null /root/code/KAM-inp-n89g1/docs/tracks/N/audits/N89-G1-audit-1.md` exit **0**, with no output. Final status contains only the pre-existing untracked handoff and this new report. `.lake/abi-scratch/N89G1Audit.lean` has been deleted. The audited module hash remains unchanged.
