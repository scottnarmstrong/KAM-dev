# S9-S independent package audit 1

Overall verdict: **PASS WITH NOTES** for both `KAM.Planetary.SecularSpectrum.local_analytic` and `local_analytic_unique`. This is an infrastructure-package verdict. S9-S has no provider or frozen theorem anchor, so no frozen seal is authorized or claimed by this report.

Audited HEAD: `1d3815c101bd5dab44a0e48733030c506953ce40`; comparison ref `inp`: `31f0bfbf70c07b1eefd006237f331c00e003a0e5` at inspection. The required `git diff inp...HEAD` warns of multiple merge bases and chooses `f4d1a3178d2fd696e15dc0e0c9dd383f03b5e80c`; the other base is `fcf99720d2823512b072b865e8b3c87121b593fb`. I used the requested comparison without substituting another base. Its ninth file, `SecularForm/Coefficients.lean`, is inherited S8-C work and is outside the explicit audit focus.

The audited files are `KAM/Planetary/SecularSpectrum/LocalAnalytic.lean` and the seven modules `LocalAnalytic/{Projection,Frame,Analytic,Eigenvalues,Sorted,Existence,Unique}.lean`. Only this report is written as a repository artifact, at `/root/code/KAM-inp-s9s/docs/tracks/P/audits/S9-S-audit-1.md`, following the user's explicit worktree destination instead of the generic brief's main-worktree destination.

Read: AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief and handoff; P810 design row S9-S and Appendix A; both design audits under `docs/tracks/P/design/`; `blueprint-P/parts/p9-secular-spectrum.tex`, especially lines 15–22 and 107–114; track P statement; imported carrier/norm and relevant frozen definition bodies. The original signatures live at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean`, not the absent relative path in this worktree. Their SHA-256 is `492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d`, matching design audit 2.

## Statement fidelity and proof review

Both main theorem headers are identical after whitespace normalization to the original signatures (lines 305 and 870) and the design appendix (lines 862 and 1427). The wrapped `hDiag` line changes whitespace only. No hypothesis, quantifier, radius dependence, norm, carrier or conclusion changed. An independent Lean probe copied each original signature under a fresh name and proved it with exactly `by exact local_analytic hW hM hAn hx0 hSimple` and `by exact local_analytic_unique hW hWc hR hS hDiag`. Full polymorphic `type_of%` comparisons also elaborate. Frozen/provider type and literal seal-body probes are inapplicable because this package supplies neither a provider nor an anchor; these signature probes serve the corresponding infrastructure check.

The matrix carriers are literally `Fin n → Fin n → ℝ`, with vectors `Fin n → ℝ`; the ball uses the ambient Pi max norm. There are no perturbation constants or hidden norm conversions. The source's positive dimension is generalized to all n, including zero: sign selection handles the empty determinant explicitly. The basepoint equality to the sorted spectrum is constructed at Existence:79 and need not be a new premise. Although not a separate conclusion field, it is determined by ordered orthogonal diagonalization, as proved in the uniqueness algebra. Strict increase implies the source's simple spectrum throughout the ball.

`la-ev`: the analytic implicit function theorem is genuinely invoked at `ContDiff` order `ω`, not merely smooth order `∞`. The scalar derivative is converted to an invertible partial continuous linear map using c inverse. Local Mathlib `Analysis/Calculus/ImplicitContDiff.lean:55–96` supplies the basepoint value, eventual equation, and analytic regularity; `ContDiff/Defs.lean:118–133` confirms the analytic meaning of `ω`. Separability of the product characteristic polynomial supplies the nonzero derivative. Finite intersections give one positive radius for analyticity, strict ordering, roots and projection positivity. Hermitian spectral data are used for the initial real sorted factorization; discontinuous choices of Mathlib eigenvectors are never treated as analytic.

`la-adj` and `la-vec`: Cayley-Hamilton and Lagrange interpolation establish symmetric mutually orthogonal idempotents and the eigen-equation. A characteristic root supplies a nonzero eigenvector fixed by its projection. If every projection diagonal entry were nonpositive, the identity trace(P) = sum of squares of all entries would contradict nonzeroness. A fixed positive entry at the base point persists locally. Dividing the chosen column by its positive square root gives an analytic frame with F transpose F = F F transpose = 1 and the required diagonalization. All algebraic helper assumptions, including charpoly factorization and positivity, are derived inside the parent theorem; they are not extra assumptions passed to the source result.

`la-so`: continuity of determinant and preconnectedness of the ball make its value a constant sign. Constant diagonal signs correct it to determinant one without changing the decomposition. For uniqueness, equal characteristic polynomials and strict ordering give equal spectra pointwise. Commutation with a diagonal matrix having distinct entries forces R transpose S diagonal. Its entries are signs, their product is one, and continuity on the connected patch makes each sign constant. Analyticity of the spectrum itself is not assumed in the uniqueness helper; ordering plus diagonalization suffices. The unused hW binder is retained from the exact design signature.

## Notes and boundaries

1. **Declared proof-route substitution, accepted.** Projection:33 defines the Lagrange polynomial projection, not the blueprint's literal adjugate quotient (`p9-secular-spectrum.tex:112`, “Eigenprojections by the adjugate”). The required projector identities and frame construction are proved directly. No theorem in these eight modules asserts the equality with `adj(σ I-M)/p'(σ)` or trace(P)=1. Those literal intermediate identities should not be marked independently proved; graph bookkeeping should describe the replacement route (or an applicable bypass), while the parent local spectral theorem is proved. The handoff already discloses the substitution. Uniqueness similarly uses ordered root ranges rather than the IFT uniqueness lemma. `exists_analytic_root` is explicitly only the existence fragment of external fact e-ift; it does not claim its full local-uniqueness conclusion.
2. **S8-C dependency is unnecessary for this generic interface.** S9-N's `sorted` and `isSO` are imported and used as designed. S8-C's coefficients and sigma are not imported or duplicated by S9-S. The generic matrix theorem accepts M and its genuine analytic/Hermitian/simple-spectrum premises; the planetary consumer must instantiate it with the delivered coefficient family and prove simplicity. This is compatible with the revised ownership ruling in design audits 1–2, but does not certify a downstream coefficient specialization, global frame, or planetary headline.
3. **Permitted generated-root lint exception.** The only lint failure is the explicitly permitted stale KAM.lean message. No generated file was regenerated.

No suspected defect in a pinned paper is established by this audit; no new PDF/source audit is claimed. No false blueprint statement was found in the audited proof. A contextual documentation typo in the imported, out-of-scope `SecularSpectrum/Norms.lean:16` says “decreasingly sorted spectrum”; its actual reversed-antitone definition is increasing, as required by blueprint line 16 and independently proved in Sorted. This is inherited prose, not an S9-S code deviation, and was left unchanged.

## Declaration inventory

All names below are relative to `KAM.Planetary.SecularSpectrum`; file locators are under `LocalAnalytic/`. These 37 rows include all 35 new public theorems and both definitions. PASS on a proof-cut row assesses the described replacement obligation; it does not assert unexported literal adjugate identities.

| Node / role | Lean declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| `la-adj / la-vec` | `analyticAt_mat_entry` (Analytic:33) | PASS | Coordinate analyticity on the Pi matrix carrier. |
| `la-adj / la-vec` | `analyticAt_mat_mul` (Analytic:37) | PASS | Finite sums of products; no new norm instance. |
| `la-adj` | `analyticAt_list_prod` (Analytic:44) | PASS | Induction on a finite ordered product of analytic matrices. |
| `la-adj` | `eigProj_eq_list` (Analytic:52) | PASS | Exact finite product identity for the Lagrange polynomial definition. |
| `la-adj` | `analyticAt_eigProj` (Analytic:61) | PASS | Analytic inverse denominators at distinct nodes; erased-index zero factor handled separately. |
| `la-vec` | `analyticAt_eigFrame` (Analytic:74) | PASS | Analytic projection entries divided by square roots of strictly positive entries. |
| `e-ift / la-ev` | `exists_analytic_root` (Eigenvalues:34) | PASS | Scalar parameter IFT at analytic order omega; derivative invertibility proved from c nonzero. Existence fragment only. |
| `la-ev` | `analyticAt_det` (Eigenvalues:64) | PASS | Determinant is an analytic finite sum of finite products. |
| `la-ev` | `det_shift_eq_eval` (Eigenvalues:71) | PASS | Characteristic polynomial evaluated at s equals det(s I - M). |
| `la-ev` | `exists_eigenvalue_branch` (Eigenvalues:82) | PASS | Simple roots imply nonzero polynomial derivative; scalar analytic IFT supplies branch and base value. |
| `la-so` | `exists_signs` (Existence:30) | PASS | Prescribed sign product constructed, including n=0 compatibility. |
| `la-so` | `isSO_mul_diagonal_signs` (Existence:41) | PASS | Orthogonality and determinant of the corrected frame computed exactly. |
| `la-so` | `diagonal_signs_conj` (Existence:54) | PASS | Column signs preserve the diagonal quadratic decomposition. |
| `bpP:p9:local-analytic` | `local_analytic` (Existence:62) | PASS | Exact design signature; branches, common positive ball, positive normalization and constant determinant correction constructed. |
| `la-vec` | `eigFrame` (Frame:31) | PASS | Literal normalized projection columns; positivity is discharged in existence. |
| `la-vec` | `eigFrame_transpose_mul` (Frame:42) | PASS | Projection multiplication and positive square roots prove column orthonormality. |
| `la-vec` | `eigFrame_mul_transpose` (Frame:72) | PASS | Square-matrix left/right inverse identity. |
| `la-vec` | `mul_eigFrame` (Frame:76) | PASS | Normalized projection columns satisfy the eigenvector equation. |
| `la-vec` | `eigFrame_diagonalises` (Frame:89) | PASS | Intertwining plus orthogonality yields M = F diag(sigma) F transpose. |
| `la-adj` | `eigProj` (Projection:33) | PASS | Lagrange polynomial evaluation; replacement for literal adjugate formula. |
| `la-adj` | `aeval_eq_zero_of_forall_eval` (Projection:39) | PASS | Pairwise coprime linear factors divide q; Cayley-Hamilton kills their product. |
| `la-adj` | `aeval_mulVec_of_eigen` (Projection:51) | PASS | Polynomial evaluation acts on an eigenvector by scalar evaluation. |
| `la-adj` | `transpose_aeval` (Projection:64) | PASS | Polynomial in a real symmetric matrix is symmetric. |
| `la-adj` | `eigProj_transpose` (Projection:71) | PASS | Projection symmetry from transpose_aeval. |
| `la-adj` | `eigProj_mul` (Projection:77) | PASS | Lagrange interpolation plus Cayley-Hamilton gives idempotence and mutual annihilation. |
| `la-adj` | `mul_eigProj` (Projection:101) | PASS | Eigenprojection intertwining proved by polynomial root evaluation. |
| `la-adj` | `exists_eigenvector` (Projection:115) | PASS | A listed characteristic root gives a nonzero kernel vector; no spectral witness assumed. |
| `la-adj` | `eigProj_mulVec_eigenvector` (Projection:125) | PASS | Projection fixes its eigenvector by the Lagrange self-evaluation identity. |
| `la-adj / la-vec` | `exists_eigProj_diag_pos` (Projection:132) | PASS | Nonzero symmetric idempotent has a positive diagonal entry via sum of squared entries. |
| `e-spec / la-ev` | `sorted_eq_eigenvalues_comp` (Sorted:33) | PASS | Existing sorted spectrum is the eigenvalue list composed with a bijection. |
| `la-ev` | `sorted_monotone` (Sorted:41) | PASS | Reverse the antitone Mathlib enumeration. |
| `la-ev` | `sorted_strictMono` (Sorted:49) | PASS | Monotonicity plus the stated injectivity gives strict increase. |
| `e-spec / la-ev` | `charpoly_eq_prod_sorted` (Sorted:57) | PASS | Mathlib Hermitian charpoly factorization reindexed by the sorting bijection. |
| `la-ev` | `charpoly_eq_prod_of_roots` (Sorted:69) | PASS | n distinct roots exhaust the monic degree-n characteristic polynomial. |
| `la-so` | `eq_of_conj_diagonal` (Unique:33) | PASS | Characteristic products have equal root ranges; strictly increasing finite enumerations coincide. |
| `la-so` | `frame_eq_signs` (Unique:56) | PASS | Simple spectrum forces R transpose S diagonal; orthogonality and determinant give signs with product one. |
| `bpP:p9:local-analytic / la-so` | `local_analytic_unique` (Unique:100) | PASS | Exact design signature; continuous diagonal signs are constant on the connected set. |

The facade adds no declaration; it publicly imports Unique and hence all seven proof modules.

## Definition classification

| Definition | Classification | Whole-carrier behavior and use |
|---|---|---|
| `eigProj` (Projection:33) | Exposed auxiliary polynomial matrix | Exactly `aeval M (Lagrange.basis univ σ j)` for all matrices/nodes. Repeated nodes use the field's total inverse in the literal polynomial; projector/analytic claims carry distinct-node hypotheses, discharged by the parent. No arbitrary selected spectral object or fabricated fallback. |
| `eigFrame` (Frame:31) | Exposed auxiliary normalized-column matrix | Exactly projection entry divided by the square root of its selected diagonal entry on the whole carrier. Outside positivity this is the ordinary total real square-root/division expression, with no asserted normalization there. Every normalization/analytic consumer supplies and proves strict positivity locally. |

There are no new abbreviations, structures, instances, bundled result fields or global norm instances. The temporary chosen roots and column indices in the existence proof are witnesses constructed from proved existence, not input premises.

## Independent checks

All auditor-controlled Lean-bearing commands were serialized and used `LEAN_NUM_THREADS=1`, `nice -n 5`, default heartbeats, with builds routed through the prescribed compile gate. The initial lint launch was stopped during its Python guard stage and rerun with the explicit resource environment below; it did not reach a Lean invocation. The queued build was suspended while lint/probe/replay ran, preventing auditor-controlled overlap. Other users' processes were not modified.

1. **Targeted build**:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9s KAM.Planetary.SecularSpectrum.LocalAnalytic
   ```

   The gate invokes `nice -n 5 lake build`. Exit **0**. Gate receipt and final output:

   ```text
   [inp-gate] slot 2 acquired 13:11:55 for KAM.Planetary.SecularSpectrum.LocalAnalytic
   Build completed successfully (9118 jobs).
   ```

   All reported module actions were replays; the independently kernel-checked package artifacts were reused. The only package diagnostic was:

   ```text
   warning: KAM/Planetary/SecularSpectrum/LocalAnalytic/Unique.lean:100:49: Variable name `hW` is not explicitly referenced.
   ```

   Replayed upstream unused-variable warnings: Energy:106 (`hm`, `hκ`); Poincare/Chart:212,247 (`hm`, `hκ`); Mass:147,157 (`hκ`),500 (`hw`),524 (`hm`, `hκ`). No error, sorry warning or heartbeat failure. No resource option was changed.

2. **Exact signature and axiom probe**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9SAuditProbe.lean
   ```

   Exit **0**; no errors or warnings. The two copied-signature declarations and two full polymorphic type comparisons elaborate. `#print axioms` was run for every one of the 35 public theorem names inventoried above. Every output is exactly the same allowed list. Full output:

   ```text
'KAM.Planetary.SecularSpectrum.analyticAt_mat_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_mat_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_list_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigProj_eq_list' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_eigProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_eigFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.exists_analytic_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.det_shift_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.exists_eigenvalue_branch' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.exists_signs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.isSO_mul_diagonal_signs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.diagonal_signs_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.local_analytic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigFrame_transpose_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigFrame_mul_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.mul_eigFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigFrame_diagonalises' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.aeval_eq_zero_of_forall_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.aeval_mulVec_of_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.transpose_aeval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigProj_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigProj_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.mul_eigProj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.exists_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigProj_mulVec_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.exists_eigProj_diag_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sorted_eq_eigenvalues_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sorted_monotone' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sorted_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.charpoly_eq_prod_sorted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.charpoly_eq_prod_of_roots' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eq_of_conj_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.frame_eq_signs' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.local_analytic_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Single-invocation kernel replay**, including the facade and every proof module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Planetary.SecularSpectrum.LocalAnalytic \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Projection \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Frame \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Analytic \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Eigenvalues \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Sorted \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Existence \
     KAM.Planetary.SecularSpectrum.LocalAnalytic.Unique
   ```

   Exit **0**. Exact verbose output:

   ```text
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Eigenvalues
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Unique
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Sorted
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Projection
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Frame
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Analytic
replaying KAM.Planetary.SecularSpectrum.LocalAnalytic.Existence
   ```

4. **Required source lint**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, exclusively for the brief's allowed generated-root exception. Exact output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (639 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

5. **Static hygiene and quarantine**: all eight files have copyright/module/public imports/module docstring/public section, and definitions are exposed. Line counts: facade 25; Projection 173; Frame 98; Analytic 88; Eigenvalues 114; Sorted 84; Existence 147; Unique 150 (879 total). No forbidden proof escape, resource override or EuclideanSpace occurrence in these files; no new instance. The facade's transitive KAM import closure contains 72 modules, with 47 frozen modules, all manifest-classified SEALED definitions and no frozen theorem or provider. There is no imported DRAFT_SORRY anchor. The public theorem axiom checks independently exclude sorryAx and custom axioms.

6. **Protected paths / whitespace**:

   ```sh
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   git diff --check -- docs/tracks/P/audits/S9-S-audit-1.md
   ```

   Each exits **0**; the protected-path diff is empty. The first two commands print only Git's multiple-merge-base warning, already recorded above. A separate Python check validates this untracked report's trailing whitespace, declaration-row completeness and absence of pending-result placeholders before handoff.


## Handoff

Files written: only this report. Approach: refute-first signature, carrier/domain, source-cut and import review, followed by independent elaboration, kernel replay and source/ABI hygiene checks. No production code, frozen file, manifest, generated root, README, branch or dependency was changed. Temporary probe files and logs are removed after copying their results below. No unresolved mathematical failure or default-heartbeat design signal was found. Remaining boundaries are the proof-route bookkeeping and downstream consumer application described above.
