# N89-G2 independent package audit 1

**Verdict: PASS WITH NOTES (package implementation).** All seven source-facing theorems, three definitions and seven helper theorems in `KAM/Nekhoroshev/ResonanceGeometry/Projection.lean` pass the scoped audit. No mathematical, signature, definition-totality, extra-premise, axiom or kernel-replay blocker was found. The notes are the permitted stale generated root, a replayed upstream warning, and moving comparison refs. No frozen anchor is supplied or sealed by this package; frozen-anchor seal readiness is **N/A**, and this report asserts no headline/root closure.

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-n89g2`.
Audited HEAD: `804c7f4012dc2c78e2bf8343cf8838fe35a83ebb`.
Audited file SHA-256: `1262aaa4cfb7ca9e65b0ffe739c6bffabea3f2e67937905cb64017eaf0346463`.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the external `inp-audit-package.md` brief, the local `N89-G2-handoff.md`, N statement conventions, the G2 design row and proof plan, both design audit reports, the actual Part-8 blueprint, and the relevant upstream definitions/proofs. Applied the statement-audit skill's binder, definition and axiom checks to this internal library package; these are not manifest-bound frozen declarations.

The user's explicit output path overrides the generic brief's main-worktree destination. The handoff's AUDIT FOCUS narrows implementation review to `Projection.lean`; G1's `Lattice.lean` is an upstream input, not independently recertified here. No implementation, frozen file, manifest, generated root or README was edited.

The handoff's `.drafts/design/N89Signatures.lean` is absent in this package worktree. Read the supplied file at `/root/code/KAM-inp/.drafts/design/N89Signatures.lean` (SHA-256 `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`) and the matching G2 declarations in design Appendix A (`docs/tracks/N/design/N89-LEAN-DESIGN.md:653–702`). All seven complete theorem headers, including the RHS `let A := ...` in `projection_matrix_lattice`, match after whitespace normalization. All three complete definition commands match too. Fresh Lean declarations copied from these exact signatures elaborate with the existing exports and exactly their explicit outer binders.

Comparison receipts:

- `git diff inp...HEAD` contains only `Lattice.lean` (+216) and `Projection.lean` (+230). The inspected `inp` ref was `42e1afbf28c6097caabe5a9b6d5d7a81463eeae7`; Git reported multiple merge bases and selected `33c688a1d1c9d25d7099f328479f4f53b0301bb4`.
- Also inspected `git diff inp-n89g1...HEAD` as requested by the focus. That ref currently names `9fd13ea076cdd33e0fc6588a7af23550470b2716`, with merge base `3bc810616832f3503fdb659df109290b98859330`, so its full diff includes 24 files of unrelated integrated history. Its `Projection.lean` path diff is the same new 230-line file. `git diff HEAD^ HEAD --stat` confirms that the G2 commit itself adds only `Projection.lean`. Its actual parent is the G1 merge `f95c89b`.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The unrelated generated-root history in the current G1-ref comparison is not a G2 edit.
- Initial status contained only the supplied untracked `docs/tracks/N/audits/N89-G2-handoff.md`; it was preserved.

## Declaration and node audit

All names below are in `KAM.Nekhoroshev`; line numbers refer to `Projection.lean`. `bpN:p8:projection` is the source contract, at `blueprint-N/parts/p8-resonance-geometry.tex:53–68`; its defining conventions use the Euclidean norm and real dot product (p8:7–9), not the ambient Pi max norm. Design row G2 is at design:306 and its proof plan at design:347–352.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Internal norm identity | `euclid_sq_eq_dot` (28) | PASS | Square of the actual Euclidean square-root sum equals the real dot square. |
| Internal norm positivity | `euclid_nonneg'` (32) | PASS | Actual square-root nonnegativity; no new norm. |
| Internal ordered-square helper | `euclid_le_of_sq_le` (34) | PASS | Nonnegative target and squared inequality imply the norm bound; conditional helper only. |
| Internal orthogonality helper | `orthProj_perp` (39) | PASS | Self-adjointness and identity on V give `(v-Pv) dot w=0` for w in V. |
| Internal uniqueness helper | `eq_zero_of_mem_of_perp` (45) | PASS | Applies orthogonality to the vector itself; positive definite real dot product. |
| `bpN:p8:projection` well-definedness | `projection_exists_unique` (50) | PASS | Existence is supplied in the proof by `exists_orthProj`; difference of two candidate images lies in V and is perpendicular to V, hence zero. No existence or uniqueness assumption. |
| Canonical projector | `proj` (63) | PASS | Chooses from the proved unique existence; complete characterization and choice independence are proved. |
| Complement | `compProj` (66) | PASS | Literally `v - proj V v` on the full carrier. |
| Internal complete choice specification | `proj_spec` (68) | PASS | Actual chosen projector is idempotent/self-adjoint, takes values in V and fixes V. |
| Internal pointwise uniqueness | `proj_eq_of_perp` (72) | PASS | Candidate in V and perpendicular residual imply equality with the chosen projector. Both candidate premises are discharged in source-facing proofs. |
| `bpN:p8:projection`, `stepN:p8:pr-alg`, `stepN:p8:pr-dist`, `stepN:p8:pr-nest` | `projection` (81) | PASS | All eight conjuncts retained: orthogonal projector, range, fixed points, perpendicular residual, Pythagoras, both contractions, pointwise uniqueness, both nested compositions. |
| Rank-zero convention, p8:56 | `projection_zero` (117) | PASS | Chosen projector onto bottom is exactly the zero linear map. |
| Resonance distance | `resonanceDistance` (121) | PASS | Euclidean length of lattice-span projection, with actual minimum/attainment proved below. |
| `bpN:p8:projection(c)`, `stepN:p8:pr-dist` | `projection_distance_subspace` (125) | PASS | Arbitrary real V: complementary point is perpendicular, attains the stated distance, and every perpendicular point has at least this distance. No lattice restriction. |
| Lattice specialization / `bpN:p8:lattice` dimension | `projection_distance` (146) | PASS | Specializes via proved `lattice_resonance`; minimum, attainment and range/kernel rank-nullity included. |
| `bpN:p8:projection`, `stepN:p8:pr-alg` | `projection_matrix` (165) | PASS | Arbitrary real independent columns; exactly `A * (A.transpose * A)⁻¹ * A.transpose`, applied to every real vector. Gram invertibility is proved, not assumed. |
| Lattice matrix specialization | `projection_matrix_lattice` (220) | PASS | Real-column theorem instantiated with integer basis casts; G1 supplies real independence and equality of the real column span to `lattice Λ`. |

The seven helpers are operationally public under the file's public section, so they were also checked and included in axiom inspection. They are internal in mathematical role, not substitutes for the seven source-facing results. No widened constant dependence occurs: there are no existential constants in these signatures. Generality for arbitrary subspaces and independent real columns is retained, resolving the original design audit's F1 concern. Statements also include the valid stronger extensions n=0 and d=0; no positivity or nonemptiness premise is introduced.

## Binder / hypothesis audit

The following table enumerates outer inputs, including implicit dimensions, for every new theorem and definition. SOURCE means an explicit mathematical condition of the source or the distinctly named internal helper; TYPING means ambient data. There are no implicit class/instance hypotheses beyond the concrete standard real/vector/submodule structures. The bundled `hP` is expanded into both fields. Logical implications inside the conclusions of `projection` and the distance statements are the literal characterization/minimization clauses of p8:56–60, not premises of the exported theorem.

| Declaration | Binder / expanded field | Bin | Source / reason |
|---|---|---|---|
| `euclid_sq_eq_dot` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `euclid_sq_eq_dot` | `x` | TYPING | real vector; norm identity |
| `euclid_nonneg'` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `euclid_nonneg'` | `x` | TYPING | real vector; square-root norm |
| `euclid_le_of_sq_le` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `euclid_le_of_sq_le` | `{x}` | TYPING | real vector |
| `euclid_le_of_sq_le` | `{b}` | TYPING | real comparison target |
| `euclid_le_of_sq_le` | `hb` | SOURCE | internal helper: b ≥ 0 |
| `euclid_le_of_sq_le` | `h` | SOURCE | internal helper: squared inequality |
| `orthProj_perp` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `orthProj_perp` | `{V}` | TYPING | real submodule |
| `orthProj_perp` | `{P}` | TYPING | real linear map |
| `orthProj_perp` | `hP.idem` | SOURCE | internal helper: P(Pv)=Pv; standard projector definition |
| `orthProj_perp` | `hP.symm` | SOURCE | internal helper: dot-product self-adjointness |
| `orthProj_perp` | `hid` | SOURCE | internal helper: P fixes V |
| `orthProj_perp` | `v` | TYPING | real vector |
| `orthProj_perp` | `{w}` | TYPING | real vector |
| `orthProj_perp` | `hw` | SOURCE | internal helper: w belongs to V |
| `eq_zero_of_mem_of_perp` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `eq_zero_of_mem_of_perp` | `{V}` | TYPING | real submodule |
| `eq_zero_of_mem_of_perp` | `{x}` | TYPING | real vector |
| `eq_zero_of_mem_of_perp` | `hx` | SOURCE | internal helper: x belongs to V |
| `eq_zero_of_mem_of_perp` | `h` | SOURCE | internal helper: x perpendicular to every vector of V |
| `projection_exists_unique` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `projection_exists_unique` | `V` | TYPING | p8:53–60; arbitrary real subspace |
| `proj` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `proj` | `V` | TYPING | p8:53–60; arbitrary real subspace |
| `proj_spec` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `proj_spec` | `V` | TYPING | p8:53–60; arbitrary real subspace |
| `projection` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `projection` | `V` | TYPING | p8:53–60; arbitrary real subspace |
| `compProj` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `compProj` | `V` | TYPING | p8:54; real subspace |
| `compProj` | `v` | TYPING | p8:54; real vector |
| `proj_eq_of_perp` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `proj_eq_of_perp` | `V` | TYPING | real submodule |
| `proj_eq_of_perp` | `v` | TYPING | real vector |
| `proj_eq_of_perp` | `w` | TYPING | candidate projected vector |
| `proj_eq_of_perp` | `hw` | SOURCE | p8:57: candidate lies in V |
| `proj_eq_of_perp` | `h` | SOURCE | p8:57: residual perpendicular to V |
| `projection_zero` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `resonanceDistance` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `resonanceDistance` | `Λ` | TYPING | p8:30–31,61; integer subgroup |
| `resonanceDistance` | `w` | TYPING | p8:61; real vector |
| `projection_distance` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `projection_distance` | `Λ` | TYPING | p8:30–31,61; integer subgroup |
| `projection_distance` | `w` | TYPING | p8:61; real vector |
| `projection_distance_subspace` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `projection_distance_subspace` | `V` | TYPING | p8:58; arbitrary real subspace |
| `projection_distance_subspace` | `w` | TYPING | p8:58; real vector |
| `projection_matrix` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `projection_matrix` | `{d : ℕ}` | TYPING | p8:54; column dimension; d=0 extension |
| `projection_matrix` | `A` | TYPING | p8:54; arbitrary real n by d matrix |
| `projection_matrix` | `hA` | SOURCE | p8:54: independent real columns |
| `projection_matrix_lattice` | `{n : ℕ}` | TYPING | p8:7,9; finite-dimensional real carrier; valid n=0 extension |
| `projection_matrix_lattice` | `{d : ℕ}` | TYPING | integer basis indexing dimension |
| `projection_matrix_lattice` | `{Λ}` | TYPING | p8:30–31; integer subgroup |
| `projection_matrix_lattice` | `b` | SOURCE | p8:37–39,61; genuine ℤ-basis data (not a projection assumption) |

Counts for the expanded table: SOURCE=12, STANDING=0, TYPING=46, RULED=0, EXCESS=0 (58 rows). Treating basis data as SOURCE is conservative: it bundles span/linear-independence data explicitly requested by the lattice specialization, never a projection or distance conclusion. The well-definedness theorem has only n and V; the main general projection/distance theorems have no logical premises. The only matrix premise is column independence, exactly as in the blueprint.

## Definition classification and proof review

`proj` is characterization-defined. `projection_exists_unique V` proves unique existence before the definition. `proj_spec` proves the full chosen specification; `projection` includes it and the complete source properties, while `proj_eq_of_perp` supplies pointwise uniqueness. An independent probe also proves, for any P with that specification, `P = proj V` by `(projection_exists_unique V).unique hP (proj_spec V)`.

- BODY_MATCH: OK
- PUBLIC_CARRIER: OK (all real submodules, including zero subspace and n=0)
- WELL_DEFINEDNESS: OK (proved unique existence; no assumed witness)
- CHARACTERIZATION: OK (full specification and source characterization proved)
- CHOICE_INDEPENDENCE: OK (explicit Lean equality probe)
- DEFINITION_VERDICT: PASS

`compProj` is a literal definition of `id - proj`, evaluated at v. BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.

`resonanceDistance` is the literal Euclidean projected length, semantically the characterized distance to `resonance Λ`. `projection_distance_subspace` and `projection_distance` prove attainment and the universal lower bound on the complete carrier. BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: OK; CHARACTERIZATION: OK; CHOICE_INDEPENDENCE: OK (inherits the unique projector); DEFINITION_VERDICT: PASS. There are no new abbreviations, structures, default branches, off-domain fallbacks or global instances.

Upstream meanings checked directly: `euclid` is `sqrt (sum ‖x i‖²)` (`Interfaces/Norms.lean:31`); `IsOrthProj` has exactly idempotence and dot-product self-adjointness (`Stability/Energy.lean:30–32`); `lattice` is the real span of integer subgroup vectors, and `resonance` is their dot annihilator (`ResonanceGeometry/Lattice.lean:31–36`, with `lattice_resonance`). The projection construction does not alter the ambient Pi norm.

The proof of `projection` expands the dot square for Pythagoras, derives the contractions from nonnegative squares, and proves both nesting identities by fixed-point/uniqueness properties. The distance proof expands `w-u = proj V w + (compProj V w-u)`, with orthogonal terms. The matrix proof shows real-column independence makes the Gram mulVec injective, derives a unit determinant and `G*G⁻¹=1`, then proves the matrix expression lies in the column span and has perpendicular residual. Thus Mathlib's total nonsingular inverse is used only after invertibility is established, including the empty-matrix case. The lattice corollaries use actual upstream proofs, not bundled new assumptions. No circular import or hard proof step assumed in a premise was found.

## Independent verification receipts

Commands were issued in this worktree. The targeted build, final lint rerun, Lean probe and kernel checker used `LEAN_NUM_THREADS=1`; Lean checks were serialized. The initial lint invocation was unwrapped (`sh scripts/lint_sources.sh`); the final serial rerun below enforces both the thread limit and niceness. No clean, update, cache retrieval or package edit was performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89g2 KAM.Nekhoroshev.ResonanceGeometry.Projection
```

The gate invokes `nice -n 5 lake build` internally. Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 07:22:53 for KAM.Nekhoroshev.ResonanceGeometry.Projection
⚠ [3188/3211] Replayed KAM.Nekhoroshev.Stability.Gradient
warning: KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name `hgr` is not explicitly referenced.
Build completed successfully (3211 jobs).
```

The replayed dependency warning suggests renaming/removing an unused binding; it is outside this package. No warning or heartbeat failure was reported for `Projection.lean`.

### Exact types, definitions and axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89G2Audit.lean
```

Final exit **0**. The scratch file imported only the audited module, copied each of the seven complete design theorem signatures under `audit_<name>`, and supplied these bodies:

| Fresh signature | Exact body / explicit outer arguments |
|---|---|
| `audit_projection_exists_unique` | `by exact projection_exists_unique V` |
| `audit_projection` | `by exact projection V` |
| `audit_projection_zero` | `by exact projection_zero` |
| `audit_projection_distance_subspace` | `by exact projection_distance_subspace V w` |
| `audit_projection_distance` | `by exact projection_distance Λ w` |
| `audit_projection_matrix` | `by exact projection_matrix A hA` |
| `audit_projection_matrix_lattice` | `by exact projection_matrix_lattice b` |

For each fresh signature, also checked `example : type_of% @audit_<name> := @<name>`. These are full elaborated-type checks, not specialization-only tests. Three `rfl` examples checked the exact defining equations of `proj`, `compProj`, `resonanceDistance`; the extra uniqueness probe above passed. No frozen/provider equality or seal-body test applies: there is no package provider or associated frozen theorem. The fresh-signature assembly checks supply the relevant analogue.

An initial scratch-generation attempt stopped its header extraction at the `let A :=` inside the final theorem's type, causing parser errors in that probe. Corrected extraction to the final `:= sorry`/`:= by` boundary, rechecked all seven complete headers, and reran successfully. This was a probe-generation error, with no production edit.

`#print axioms` was run for every new declaration, including all seven helpers and all three definitions. Exact final output:

```text
'KAM.Nekhoroshev.euclid_sq_eq_dot' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.euclid_nonneg'' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.euclid_le_of_sq_le' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.orthProj_perp' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.eq_zero_of_mem_of_perp' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection_exists_unique' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.proj' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.compProj' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.proj_spec' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.proj_eq_of_perp' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection_zero' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.resonanceDistance' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection_distance_subspace' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection_distance' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection_matrix' depends on axioms: [propext, choice, Quot.sound]
'KAM.Nekhoroshev.projection_matrix_lattice' depends on axioms: [propext, choice, Quot.sound]
```

Here `choice` is Lean's printed classical choice axiom. No `sorryAx` or project-specific axiom occurs.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.ResonanceGeometry.Projection
```

Exit **0**, output:

```text
replaying KAM.Nekhoroshev.ResonanceGeometry.Projection
```

This is the sole new G2 lemma module; there is no provider module to add to the invocation.

### Lint, imports and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated root. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (449 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The same output and exit status were observed in the initial lint invocation. The root was not regenerated.

Separate static checks of the scoped file returned **230 lines**, **maximum width 99 characters**, and **no occurrences** of `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, or `set_option`. The copyright, `module`, public imports, module docstring and exposed public noncomputable section are present. No module exceeds the owner's size cap, and the scoped file satisfies the 100-character limit.

The three direct imports are `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, `Mathlib.LinearAlgebra.Matrix.ToLin` and `KAM.Nekhoroshev.ResonanceGeometry.Lattice`. A recursive source import scan found 56 project modules including the target, **no provider modules**, and 19 frozen imports, all definition anchors in manifest state **SEALED**. There is no transitive frozen theorem import, DRAFT_SORRY anchor or provider leakage. Kernel replay and axiom closure independently support the semantic dependency check.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0** with no substantive output (Git may emit the multiple-merge-base warning described above). No protected file was changed by this audit. Probe files were deleted after validation; final status is recorded below.

## Findings, errata and limits

No suspected new source or blueprint defect was found in the audited projection statements/proofs. The alternate uniqueness-first construction implements the same projector as the source's matrix formula, with that equivalence actually proved. The stronger zero-dimensional/empty-column coverage is valid and explicit, rather than a silent added hypothesis or fallback.

The known design-audit F1 gap is closed at implementation level by the proved arbitrary-real-column matrix theorem and arbitrary-subspace distance theorem. The other design audit's scheduling and Pöschel-constant findings concern different packages and are outside this G2 implementation scope. No pinned source PDF was re-audited: the blueprint labels the projection lemma “Standard (Pos93 p. 202 uses these properties silently).” The verdict covers the named library contracts and their proofs; it does not assert independent certification of all G1 code, downstream consumers, or any frozen N/I/P theorem.

Final repository status after probe deletion:

```text
?? docs/tracks/N/audits/N89-G2-audit-1.md
?? docs/tracks/N/audits/N89-G2-handoff.md
```

Only the first file was written by this auditor; the second was supplied before the audit. No state-changing git command was used.
