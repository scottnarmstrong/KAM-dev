# Independent S9-2 package audit 1

Overall verdict: **PASS WITH NOTES** for each of KAM.Planetary.SecularSpectrum.n2 and KAM.Planetary.SecularSpectrum.n2_global_frame. No proof or statement defect found in the sole audited module. Notes concern inherited branch/root hygiene. These are infrastructure exports; this package supplies and seals no frozen anchor. Provider/frozen-type and frozen seal-body probes are therefore not applicable.

Audited HEAD: 92d3a376fcd065e7c1fd1fc9e5ad33a00c70868a. Comparison ref inp observed at 4edfdd76ba941faaf07d7c979c8cc92821074160. Scope: KAM/Planetary/SecularSpectrum/TwoPlanets.lean only, 423 lines, SHA-256 14f100a51b50ac8709831c24065ced36144012721d2a11f7a1557ae17f088514.

Read the assigned brief, AGENTS.md, PLAN.md, DECISIONS.md, handoff/AUDIT FOCUS, P810 design S9-2 row and proof/signature plan, both design audits, track P statement, blueprint p9:193–204, and the relevant imported definitions and interfaces. The untracked signature is absent in this worktree; used /root/code/KAM-inp/.drafts/design/P810Signatures.lean read-only, SHA-256 492cda44ef3de718cd0b98ffe00116a2bb676b5551575b5df9f9e9261a8f3e0d, matching design revision 2.

## Findings and scope notes

1. **No S9-2 failure.** Both export headers match the signature file after whitespace normalization. Fresh Lean probe copies use exactly those signatures under fresh names with bodies by exact n2 D ha and by exact n2_global_frame D. Additional examples of type_of% @audit_n2 := @n2 and its global-frame analogue check whole elaborated types. No premise, instance, constant dependence, norm or carrier changed.
2. **The requested three-dot diff is broader than the package.** git diff inp...HEAD warns “multiple merge bases, using 8d5767d684b5cf6041cf3e8a54e43818be0c67c9” and reports 13 files, 786 insertions, 65 deletions. The protected-path check is **not empty**: KAM.lean has 47 added imports. KAM/Frozen, manifest and README.md have no diff. The five S9-2 commits e5be5d96 through 92d3a376 change only TwoPlanets: git diff --stat e5be5d96^..HEAD gives one file and 423 insertions; protected-path diff over that range is empty. The landing orchestrator must handle inherited changes; this audit does not certify the entire branch as a one-file protected-path-clean diff.
3. **Valid proof-plan variation.** Blueprint p9:202 constructs an explicit eigenvector using q12>0. The implementation normalizes S9-S local frames with R[1,1]>0, proves uniqueness, and glues. It uses the essential positive off-diagonal fact and proves the full global conclusion; it does not infer a global frame from simple spectrum alone. The handoff associates global-frame work with stepP:p9:n2-res; the literal blueprint places it in stepP:p9:n2-mat. This is an approach/locator note, not missing proof.

## Declaration and node inventory

Names have prefix KAM.Planetary.SecularSpectrum. Helper rows describe proof ingredients, not additional standalone blueprint claims. Conditional frame hypotheses are discharged by local_analytic and are never substituted for source conclusions. Nodes covered: bpP:p9:n2, stepP:p9:n2-mat, stepP:p9:n2-res.

| Node / role | Declaration (source line) | Verdict | Reason |
|---|---|---|---|
| p9:n2-mat | pairB_pos (35) | PASS | Positive Laplace coefficient at the physical ratio in (0,1). |
| p9:n2-mat | pairA_pos (48) | PASS | Uses proved pairA-pairB>0 and pairB>0. |
| p9:n2-mat | pairA_swap (54) | PASS | Unconditional min/max symmetry; stronger carrier form. |
| p9:n2-mat | action_nonneg (57) | PASS | Positive mass times nonnegative sqrt; valid on the whole carrier. |
| p9:n2-mat | coeffs_two_diag0 (62) | PASS | Literal first diagonal entry, no extra axes premise. |
| p9:n2-mat | coeffs_two_diag1 (68) | PASS | Literal second diagonal entry using symmetry. |
| p9:n2-mat | coeffs_two_off01 (74) | PASS | Literal off-diagonal entry and denominator. |
| p9:n2-mat | coeffs_two_off10 (78) | PASS | Other off-diagonal entry via pairB_comm. |
| p9:n2-mat | sorted_two_sum (88) | PASS | Trace identity for every real Hermitian 2x2 matrix. |
| p9:n2-mat | sorted_two_prod (96) | PASS | Determinant identity for every real Hermitian 2x2 matrix. |
| p9:n2-mat | eq_of_sum_prod (104) | PASS | Generic conditional helper identifying strictly ordered real pairs. |
| p9:n2-mat | trace_two (116) | PASS | Exact blueprint trace, algebraically equivalent form. |
| p9:n2-mat | det_two (120) | PASS | Exact determinant with proved positive denominators. |
| p9:n2-mat | det_two_pos (137) | PASS | Uses pairA>pairB>0 and positive actions. |
| p9:n2-mat | disc_two_pos (147) | PASS | Square plus strictly positive 4B²/(L0 L1). |
| p9:n2-mat | sigma_two_lt (160) | PASS | Sorted order and positive discriminant exclude equality. |
| p9:n2-res | sigma_two_neg (172) | PASS | S9-D positive coercivity and spectral upper bound. |
| p9:n2-res | sigma_two_inj (177) | PASS | Strict order on Fin 2 gives injectivity. |
| p9:n2-res | nr4_two_iff (182) | PASS | Both directions; complete enumeration in [-4,4]² with l1 filter. |
| p9:n2-res | two_trace_det_iff (211) | PASS | Exact factorization; negative strict order excludes reciprocal ratios. |
| bpP:p9:n2 | n2 (236) | PASS | Exact signature, all six conjuncts and no new premises. |
| p9:n2-mat / frame | isOpen_axes (251) | PASS | Finite intersections of strict inequalities, every dimension. |
| p9:n2-mat / frame | eigenvalues_injective_of_sorted (260) | PASS | Uses proved permutation between eigenvalue enumerations. |
| p9:n2-mat / frame | isSO_neg (269) | PASS | Negation preserves SO in dimension two. |
| p9:n2-mat / frame | neg_conj (274) | PASS | Double negation preserves diagonalization. |
| p9:n2-mat / frame | frame_sigma (281) | PASS | Trace/product and strict order identify local branches with sigma. |
| p9:n2-mat / frame | frame_entry_ne (301) | PASS | Positive off-diagonal and orthonormal column exclude R[1,1]=0. |
| p9:n2-mat / frame | NormFrame (326) | PASS | Faithful exposed normalization predicate; definition classified below. |
| p9:n2-mat / frame | normFrame_unique (329) | PASS | S9-S sign ambiguity, determinant one and positive entry force both signs +1. |
| p9:n2-mat / frame | normFrame_smul (352) | PASS | Distinct conditional helper; sign scaling supplies normalization. |
| p9:n2-mat / frame | sign_const (362) | PASS | Continuous nowhere-zero real function on preconnected set retains sign. |
| p9:n2-mat / frame | local_normFrame (370) | PASS | Normalizes S9-S local analytic frame by one constant sign on a ball. |
| bpP:p9:n2 / global frame | n2_global_frame (405) | PASS | Exact signature; uniqueness glues local normalized analytic frames globally. |

## Definitions and mathematical fidelity

NormFrame (326–327) is the only new top-level def/abbrev/structure. It is an exposed proposition on the whole carrier: SO, equality with the literal coefficient matrix diagonalized by the actual sorted spectrum, and positive entry (1,1). It contains no existence, regularity or simplicity field. Its existence and uniqueness on physical axes are proved. No new structure or abbreviation exists.

The proof-local choice R (414) selects the proved normalized frame on axes 2 and is zero outside it. This fallback is harmless: all diagonalization conclusions are membership-guarded; openness and a ball contained in axes prove neighborhood analyticity by local agreement. The proof never claims the fallback is orthogonal. Other local objects are square roots, algebraic abbreviations or signs ±1.

The entry formulas unfold qhat and coeffs. Unconditional diagonal simplification is justified by action_nonneg even outside physical axes. Strict positivity correctly requires physical axes. Data contains only positive masses, G and dimension data; axes means positivity and strict order. action, pairA, pairB, coeffs, sigma, sorted, isSO and nr4 retain their literal upstream bodies. Ambient vectors are Fin n → ℝ. SO uses transpose multiplication and determinant one, not a Pi-norm isometry.

S9-D supplies pairA-pairB>0 and negative spectrum; the upstream Laplace theorem supplies pairB>0. Determinant/discriminant denominators are proved positive. S9-S supplies sorted spectral facts, local analytic frames and their sign ambiguity; trace and product identify the local ordered spectrum with sigma. S9-G supplies nr4/k4 including injectivity and every nonzero integer vector of l1 size at most four. Resonance casework includes both signs and zeros; factorization excludes inverse ratios using strict negative order.

Global normalization preserves determinant one specifically in dimension two. The eigenvector equation and positive off-diagonal prove the normalization entry nonzero. Frame uniqueness forces both signs +1, giving local agreement of pointwise choices with analytic frames. No topology/monodromy assumption is smuggled into the statement. Analytic eigenvalues also follow from the analytic global diagonalizer and analytic coefficients; a separate eigenvalue-analyticity export is not part of either assigned signature.

## Independent validation

All auditor-controlled Lean/Lake invocations were sequential with LEAN_NUM_THREADS=1 and nice -n 5, directly or inside the required compile wrapper. No clean/update/cache fetch, root regeneration, production edit or state-changing git action occurred.


1. Targeted build (exit 0):

       LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s92 KAM.Planetary.SecularSpectrum.TwoPlanets

   The wrapper runs nice -n 5 lake build. Output: [inp-gate] slot 1 acquired 14:44:22 for KAM.Planetary.SecularSpectrum.TwoPlanets; Build completed successfully (9129 jobs). Replayed upstream warnings occurred in Kepler.Energy, Poincare.Chart, Kepler.Mass, SecularForm.Coefficients, SecularSpectrum.Definiteness and LocalAnalytic.Unique (unused variables, deprecated tactics/lemmas, style); no TwoPlanets warning or default-heartbeat design signal.

2. Exact signature copies and all public theorem axioms (exit 0):

       LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S92Audit.lean

   The scratch probe imports TwoPlanets, copies the two design signatures under fresh audit names, supplies the exact bodies described above, and checks both complete types with type_of%. No sorry/frozen theorem is introduced into the probe. All 32 public lemmas/theorems were queried. Exact axiom output:


~~~text
'KAM.Planetary.SecularSpectrum.pairB_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairA_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.pairA_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.action_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.coeffs_two_diag0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.coeffs_two_diag1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.coeffs_two_off01' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.coeffs_two_off10' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sorted_two_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sorted_two_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eq_of_sum_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.trace_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.det_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.det_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.disc_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sigma_two_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sigma_two_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sigma_two_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.nr4_two_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.two_trace_det_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.n2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.isOpen_axes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.eigenvalues_injective_of_sorted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.SecularSpectrum.isSO_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.neg_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.frame_sigma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.frame_entry_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.normFrame_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.normFrame_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sign_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.local_normFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.n2_global_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

3. One kernel replay invocation (exit 0):

       LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.TwoPlanets

   Exact output:


~~~text
replaying KAM.Planetary.SecularSpectrum.TwoPlanets
~~~

4. Full lint (exit **1**, not a passing lint receipt):

       LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh

   Exact output:


~~~text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (699 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD FAILED:
- nekhoroshev.d28.averaging_mean.v1: DRAFT_SORRY imported directly or transitively outside explicit frozen/audit allowlist: KAM.lean
- nekhoroshev.d28.averaging_mean.v1: DRAFT provider imported directly or transitively outside its provider and frozen anchor: KAM.lean
- nekhoroshev.d28.averaging_most.v1: DRAFT_SORRY imported directly or transitively outside explicit frozen/audit allowlist: KAM.lean
- nekhoroshev.d28.averaging_most.v1: DRAFT provider imported directly or transitively outside its provider and frozen anchor: KAM.lean
ABI HASHES OK (144 frozen declarations)
~~~

   The stale-root line is the brief's permitted exception. The four frozen-anchor quarantine errors are **additional failures beyond that exception**; they must not be relabeled as a passed guard. All identify inherited generated KAM.lean, none TwoPlanets or its import closure. The package-local theorem verdict is PASS WITH NOTES; the full-worktree hygiene gate remains FAIL pending orchestrator root reconciliation. ABI hashes pass for all 144 declarations. The report-only rule and generated-file prohibition preclude repairing KAM.lean here.

5. Static source checks (PASS): one module, 423 lines, all lines at most 100 Unicode characters; copyright, module command, public imports, module docstring, exposed public section. No sorry/admit/axiom/unsafe/opaque, EuclideanSpace, heartbeat/recursion overrides or any set_option. A declaration-name scan over all other KAM Lean files found no duplicate short name for any of the 33 new declarations, including all four coeffs_two_* helpers. No added hypotheses or conclusion-shaped bundled fields found.

6. Import quarantine (PASS for audited module): recursively traversed 83 KAM modules from TwoPlanets. No provider module or frozen theorem module occurs, so no DRAFT_SORRY theorem import or provider-to-provider edge occurs. Frozen definitions are not frozen theorem assumptions; there is no imported theorem state requiring a SEALED exception.

7. Git checks: git diff --check inp...HEAD exits 0, with only the multiple-merge-base warning. git diff --check exits 0. Protected-path command git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md produces the inherited KAM.lean diff described above; it is not empty. git diff inp...HEAD -- KAM/Frozen manifest README.md and git diff e5be5d96^..HEAD -- KAM/Frozen manifest KAM.lean README.md are empty. No protected file was edited by this audit.

## Errata, deviations and limitations

No suspected pinned-source or blueprint mathematical defect was found in this scope. The current blueprint p9:199 correctly says Phi4 and the trace/determinant product have the same zero set and explicitly rejects equality up to a nonvanishing factor; the old multiplicity error from the design history is not reintroduced.

The valid global-frame proof variation and handoff step-label mismatch are recorded above. No signature or source-object deviation was introduced. This audit does not replay an independent pinned-PDF transcription audit, audit upstream package proofs in full, certify the other 12 files in the three-dot diff, or close a planetary frozen theorem. The main practical limitation is the inherited full-worktree root/quarantine failure.

Only this report was added by the auditor outside ignored scratch. The pre-existing untracked S9-2-handoff.md was left unchanged. Audit probe and captured scratch outputs were removed after embedding the receipts here.
