# Independent audit S9-L, audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.SecularSpectrum.lift` and the S9-L package. The exact design contract is proved; no mathematical blocker or added source premise was found. There is no frozen anchor or provider export in this package, so no anchor is being certified seal-ready. The branch-wide protected-path check is nonempty for an inherited generated-root change, detailed below.

Audited HEAD: `a7d5bf4d0467b82540dcd1b576c4ac950968a582`. Recorded `inp`: `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`; `inp-s9n`: `50de825c3f654adc885132a6517d4ad6c090d131`. Read the supplied audit brief, worktree AGENTS.md, PLAN.md, DECISIONS.md, S9-L handoff, P810 design row/proof plan/Appendix A, both design audits, the p9 lift statement and proof, the relevant track-P statement conventions and frozen phase/form/coordinate definitions. The user explicitly overrides the generic brief's main-worktree output destination: this report is in the S9-L worktree.

## Scope and comparison notes

Both `git diff inp...HEAD` and `git diff inp-s9n...HEAD` were inspected. Git warns for the former: `multiple merge bases, using 50de825c3f654adc885132a6517d4ad6c090d131`. These comparisons include unrelated previously merged work in addition to the eight Lift files. This audit follows the handoff's explicit Lift-only scope; it does not recertify S9-N or the unrelated averaging, assembly and measure packages.

**N1: protected-path comparison is not empty.** `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` shows exactly four added imports in `KAM.lean`, from commit `5991245cabc06e69ec900cb6006b45f72cc85eb0` ("Regenerate KAM.lean (PGMeasure/ResonanceSlow, PGAssembly/ComplexGlue, SecularForm/Basic, Averaging/CorrectorRegular)"). No frozen, manifest or README delta appears. This commit precedes the S9-L work. Independently, `git diff --exit-code 3f14f8d..HEAD -- KAM/Frozen manifest KAM.lean README.md` exits 0, and `git diff 3f14f8d..HEAD --name-only` lists only the eight assigned Lift files. Thus the literal branch-wide invariant is not satisfied, but the S9-L commits do preserve every protected path. No generated file was repaired during this audit.

**N2: original signature location.** `.drafts/design/P810Signatures.lean` is absent from this worktree. The current original at `/root/code/KAM-inp/.drafts/design/P810Signatures.lean` was read without modification. The extracted bodies of `liftMap`, `liftInv`, `liftDomain` and the entire type of `lift` each match both that original and the worktree design Appendix A byte for byte. No claim rests only on the handoff's statement-match assertion.

## Mathematical review

The coordinate order remains the frozen `(phi,q;I,p)` order: `assemble I theta eta xi`. `length2` is the explicit Euclidean scalar from S9-N, not the ambient Pi max norm. `IsSymplecticOn 1` uses the frozen `symplecticForm`, with sign `sum (u.2*v.1-u.1*v.2)` on both sides. Analyticity gives genuine differentiability wherever this predicate is used; total `fderiv` cannot make the conclusion vacuous.

The action-dependent angle correction contains the full directional derivative of R. Its line derivative includes the two slow-variable contributions, the second derivative of R and the product of first derivatives. The matrix core assumes only orthogonality and the two skew differentiated-orthogonality identities. At `symplecticForm_dLift` those are derived from `hAn`, `hR` and openness by `deriv_orth`; the common second-derivative term is justified by `hess_symm`. The Maurer-Cartan cancellation is implemented by this algebraic route and commuting entry derivatives, rather than by assuming a Maurer-Cartan field or exporting a separately named general differential-form theorem. This pays the parent's advertised proof cut.

For the inverse, `liftInv_eq_liftMap_transpose` holds on `liftDomain W`; openness promotes it to neighbourhood equality before transferring analyticity and fderiv. No global equality beyond that domain is assumed. The two composition identities are algebraic even without analyticity. Both maps preserve `fast w.2` by their definitions, so they map the cylinder into itself. Separate scratch examples verify both MapsTo statements; with the exported inverse identities this supplies the blueprint's "diffeomorphism ... onto itself" reading even though MapsTo is not a separate conjunct of the design signature. Analyticity and inverse identities provide an analytic inverse on the open cylinder.

The parent has exactly the source premises: W open, R analytic near W, and R(I) in SO(n) on W. There is no extra simplicity, boundedness, smallness, dimension or derivative identity premise. Translation equivariance is valid for every real vector c, and several algebraic helpers require no regularity, valid strengthenings. No constant-dependence or norm weakening occurs.

## Node and declaration inventory

All names below are in `KAM.Planetary.SecularSpectrum`. Locators refer to `KAM/Planetary/SecularSpectrum/`; helper rows are proof infrastructure, not new blueprint assumptions. Definition rows are classified further below. All 69 public declarations (61 theorems/lemmas, 8 definitions) are included.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p9:lift` | `lift` (Lift.lean:34) | PASS | Exact design statement; both analytic/symplectic maps, inverse identities, action/length preservation and every real fast-angle translation. |
| `stepP:p9:lift-bij` | `analyticAt_assemble` (Lift/Analytic.lean:31) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_fast_snd` (Lift/Analytic.lean:45) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_fast_fst` (Lift/Analytic.lean:50) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_slow_snd` (Lift/Analytic.lean:55) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_slow_fst` (Lift/Analytic.lean:60) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_matrix_entry` (Lift/Analytic.lean:65) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `fderiv_entry` (Lift/Analytic.lean:70) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_fderiv_apply` (Lift/Analytic.lean:79) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `isOpen_liftDomain` (Lift/Analytic.lean:84) | PASS | Coordinate analytic/derivative adapter with the stated regularity. |
| `stepP:p9:lift-bij` | `analyticAt_liftMap` (Lift/Analytic.lean:87) | PASS | Analytic entries and scalar derivative evaluations; neighbourhood conversion uses openness. |
| `stepP:p9:lift-bij / lift-concl` | `liftMap` (Lift/Basic.lean:32) | PASS | Literal design object; see definition classification. |
| `stepP:p9:lift-bij / lift-concl` | `liftInv` (Lift/Basic.lean:39) | PASS | Literal design object; see definition classification. |
| `stepP:p9:lift-bij / lift-concl` | `liftDomain` (Lift/Basic.lean:46) | PASS | Literal design object; see definition classification. |
| `stepP:p9:lift-bij / lift-concl` | `fast_fst_assemble` (Lift/Basic.lean:50) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `slow_fst_assemble` (Lift/Basic.lean:53) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `fast_snd_assemble` (Lift/Basic.lean:56) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `slow_snd_assemble` (Lift/Basic.lean:59) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `assemble_eta` (Lift/Basic.lean:62) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `length2_eq_dotProduct` (Lift/Basic.lean:68) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `length2_mulVec_of_orth` (Lift/Basic.lean:71) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `isSO_mul_transpose` (Lift/Basic.lean:78) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `isSO_transpose_mul` (Lift/Basic.lean:81) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `sum_transpose_mulVec_mul` (Lift/Basic.lean:83) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `liftInv_liftMap_of_isSO` (Lift/Basic.lean:89) | PASS | Actual composition identity at w; purely algebraic, no differentiability needed. |
| `stepP:p9:lift-bij / lift-concl` | `sum_mulVec_mul` (Lift/Basic.lean:105) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `liftMap_liftInv_of_isSO` (Lift/Basic.lean:110) | PASS | Reverse composition identity at w; actual angle shifts cancel. |
| `stepP:p9:lift-bij / lift-concl` | `fast_snd_liftMap` (Lift/Basic.lean:125) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `length2_slow_fst_liftMap` (Lift/Basic.lean:129) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `length2_slow_snd_liftMap` (Lift/Basic.lean:134) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `assemble_add_append` (Lift/Basic.lean:139) | PASS | Coordinate, orthogonality or inverse algebra; valid on its stated carrier. |
| `stepP:p9:lift-bij / lift-concl` | `liftMap_add_append` (Lift/Basic.lean:146) | PASS | Every real translation, globally and without regularity premises; stronger than lattice-only equivariance. |
| `stepP:p9:lift-anti` | `hasDerivAt_mat` (Lift/Calculus.lean:33) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_mat_entry` (Lift/Calculus.lean:37) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_vec_entry` (Lift/Calculus.lean:41) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_mat_transpose` (Lift/Calculus.lean:45) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_mat_mul` (Lift/Calculus.lean:49) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_mat_mulVec` (Lift/Calculus.lean:58) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_vec_dot` (Lift/Calculus.lean:67) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_line` (Lift/Calculus.lean:76) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `hasDerivAt_comp_line` (Lift/Calculus.lean:80) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `deriv_orth` (Lift/Calculus.lean:86) | PASS | Differentiates R R-transpose = 1 on an open neighbourhood; no derivative constraint assumed. |
| `stepP:p9:lift-anti` | `deriv_orth'` (Lift/Calculus.lean:103) | PASS | Equivalent skew derivative identity derived from deriv_orth and orthogonality. |
| `stepP:p9:lift-anti` | `analyticOnNhd_transpose` (Lift/Calculus.lean:116) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `isSO_transpose` (Lift/Calculus.lean:121) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `fderiv_transpose` (Lift/Calculus.lean:124) | PASS | Coordinate calculus or transpose adapter; regularity and orthogonality explicit. |
| `stepP:p9:lift-anti` | `liftInv_eq_liftMap_transpose` (Lift/Calculus.lean:133) | PASS | Equality on the actual domain; derivative of transpose and skew identity give the opposite angle shift. |
| `stepP:p9:lift-form / lift-mc` | `dot_mulVec_swap` (Lift/Core.lean:33) | PASS | Finite matrix/dot-product identity. |
| `stepP:p9:lift-form / lift-mc` | `dot_transpose_mulVec` (Lift/Core.lean:37) | PASS | Finite matrix/dot-product identity. |
| `stepP:p9:lift-form / lift-mc` | `dot_transpose_transpose` (Lift/Core.lean:41) | PASS | Finite matrix/dot-product identity. |
| `stepP:p9:lift-form / lift-mc` | `core_identity` (Lift/Core.lean:45) | PASS | Conditional matrix identity; differentiated orthogonality supplied by deriv_orth at its consumer, not assumed by lift. |
| `stepP:p9:lift-form` | `hasDerivAt_assemble` (Lift/Deriv.lean:31) | PASS | Explicit derivative computation or linear coordinate adapter. |
| `stepP:p9:lift-form` | `dTheta` (Lift/Deriv.lean:46) | PASS | Explicit auxiliary formula; see definition classification. |
| `stepP:p9:lift-form` | `dP` (Lift/Deriv.lean:59) | PASS | Explicit auxiliary formula; see definition classification. |
| `stepP:p9:lift-form` | `dQ` (Lift/Deriv.lean:64) | PASS | Explicit auxiliary formula; see definition classification. |
| `stepP:p9:lift-form` | `dLift` (Lift/Deriv.lean:69) | PASS | Explicit auxiliary formula; see definition classification. |
| `stepP:p9:lift-form` | `hasDerivAt_phase_line` (Lift/Deriv.lean:72) | PASS | Explicit derivative computation or linear coordinate adapter. |
| `stepP:p9:lift-form` | `hasDerivAt_liftMap_line` (Lift/Deriv.lean:76) | PASS | Computes all angle and slow-block terms, including derivative of derivative of R. |
| `stepP:p9:lift-form` | `fderiv_liftMap_eq` (Lift/Deriv.lean:125) | PASS | Analyticity supplies differentiability; uniqueness of line derivatives identifies actual fderiv. |
| `stepP:p9:lift-anti / lift-mc` | `clm_apply_eq_sum` (Lift/Hessian.lean:32) | PASS | Entrywise second-derivative or finite-basis identity. |
| `stepP:p9:lift-anti / lift-mc` | `hess` (Lift/Hessian.lean:43) | PASS | Explicit auxiliary formula; see definition classification. |
| `stepP:p9:lift-anti / lift-mc` | `hess_eq_sum` (Lift/Hessian.lean:46) | PASS | Entrywise second-derivative or finite-basis identity. |
| `stepP:p9:lift-anti / lift-mc` | `fderiv_eq_sum` (Lift/Hessian.lean:52) | PASS | Entrywise second-derivative or finite-basis identity. |
| `stepP:p9:lift-anti / lift-mc` | `hess_symm` (Lift/Hessian.lean:56) | PASS | Analytic scalar entries give commuting actual second derivatives; no symmetry premise. |
| `stepP:p9:lift-anti / lift-mc` | `hasDerivAt_fderiv_line` (Lift/Hessian.lean:62) | PASS | Actual line derivative of the matrix derivative; open-domain eventual equality justifies entrywise conversion. |
| `stepP:p9:lift-form / lift-mc / lift-concl` | `symplecticForm_split` (Lift/Symplectic.lean:33) | PASS | Frozen-form split or full cancellation identity. |
| `stepP:p9:lift-form / lift-mc / lift-concl` | `sum_mul_dot` (Lift/Symplectic.lean:40) | PASS | Frozen-form split or full cancellation identity. |
| `stepP:p9:lift-form / lift-mc / lift-concl` | `sum_dTheta` (Lift/Symplectic.lean:45) | PASS | Exact contraction of angle correction, including Hessian and first-derivative products. |
| `stepP:p9:lift-form / lift-mc / lift-concl` | `symplecticForm_dLift` (Lift/Symplectic.lean:62) | PASS | Full frozen-form identity; orthogonal derivative and Hessian symmetry are proved inputs. |

## Definition classification

| Definition | Classification and whole-carrier behavior |
|---|---|
| `liftMap` | Exact design formula on all `Phase (n+n)`, using total Mathlib fderiv; on the theorem domain analyticity supplies the intended derivative. No chosen witness, branch or replacement map. |
| `liftInv` | Exact opposite correction and R multiplication on all phase points; theorems restrict to orthogonal R where inverse claims are made. |
| `liftDomain` | Exact cylinder `{w : Phase (n+n) | fast w.2 in W}`; no hidden restriction on angles or slow coordinates. |
| `hess` | Entrywise iterated actual Frechet derivative on all R,I,x,y; no symmetry axiom. Its interpretation as the smooth Hessian and its symmetry are proved under analyticity. |
| `dTheta` | Explicit candidate angle derivative including all Hessian/product/slow-variable terms. Equality to the derivative is proved under the source regularity. |
| `dP` | Explicit derivative of R-transpose times the second slow coordinate; both product-rule terms retained. |
| `dQ` | Corresponding first-slow-coordinate derivative, with both terms retained. |
| `dLift` | Assembly of the four candidate derivative blocks. `fderiv_liftMap_eq` establishes its actual derivative meaning under analyticity. |

No new structure, abbreviation, typeclass instance or witness-selection definition occurs. Total derivative fallback values outside the differentiable domain are ordinary auxiliary values; no analytic-domain theorem relies on such a fallback. All definitions are in the exposed public section.

## Independent checks

Commands ran from `/root/code/KAM-inp-s9l`. Auditor-controlled Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and niceness 5. No clean, update, cache-get, dependency edit or whole-library build was run. One preliminary lint invocation was stopped after its static guard, before ABI elaboration; the complete resource-limited lint run is recorded below.

### Targeted build

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s9l KAM.Planetary.SecularSpectrum.Lift
[inp-gate] slot 1 acquired 10:30:42 for KAM.Planetary.SecularSpectrum.Lift
Build completed successfully (9118 jobs).
exit 0
```

The gate runs `nice -n 5 lake build` for this target. Replayed upstream warnings were unused binders in `KAM/Kepler/Energy.lean:106`, `KAM/Planetary/Poincare/Chart.lean:212,247`, and `KAM/Kepler/Mass.lean:147,157,500,524`. No Lift warning or default-heartbeat failure appeared. The replay job count is Lake's target dependency count, not an instruction to rebuild the library from scratch.

### Signature, binder application, domain and axiom probes

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9LAudit.lean
exit 0
```

The scratch imports only the completed Lift facade. A fresh `audit_lift_copy` has the exact original design type and body `by exact lift hW hAn hR`; both `example : type_of% @audit_lift_copy := @lift` and its reverse elaborate. Both MapsTo examples elaborate. The only probe diagnostics are two deprecation warnings for `Set.mem_setOf_eq` at scratch lines 26 and 30; no errors. This is the exact-contract/application check appropriate to a non-provider infrastructure package; there is no frozen theorem to seal or compare against.

Every new public theorem was then checked with `#print axioms`, not just the facade result. The exact axiom output follows:

```text
'KAM.Planetary.SecularSpectrum.lift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_fast_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_fast_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_slow_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_slow_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_matrix_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fderiv_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.isOpen_liftDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticAt_liftMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fast_fst_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.slow_fst_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fast_snd_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.slow_snd_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.assemble_eta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_eq_dotProduct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_mulVec_of_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.isSO_mul_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.isSO_transpose_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_transpose_mulVec_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.liftInv_liftMap_of_isSO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_mulVec_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.liftMap_liftInv_of_isSO' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fast_snd_liftMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_slow_fst_liftMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.length2_slow_snd_liftMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.assemble_add_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.liftMap_add_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_mat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_mat_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_vec_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_mat_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_mat_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_mat_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_vec_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_comp_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.deriv_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.deriv_orth'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.analyticOnNhd_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.isSO_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fderiv_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.liftInv_eq_liftMap_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.dot_mulVec_swap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.dot_transpose_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.dot_transpose_transpose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.core_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_assemble' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_phase_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_liftMap_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fderiv_liftMap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.clm_apply_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hess_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.fderiv_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hess_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.hasDerivAt_fderiv_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.symplecticForm_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_mul_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.sum_dTheta' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.SecularSpectrum.symplecticForm_dLift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 61 outputs contain exactly `[propext, Classical.choice, Quot.sound]`; none contains `sorryAx` or another axiom.

### Static hygiene and imports

```text
rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/SecularSpectrum/Lift.lean KAM/Planetary/SecularSpectrum/Lift
(no matches; exit 1)
git diff --check inp...HEAD
(no whitespace diagnostics; exit 0; multiple-merge-base warning as above)
```

All eight files have the copyright header, `module`, public imports, module docstring and exposed public noncomputable section. Raw line counts: Lift 76; Basic 170; Analytic 127; Calculus 149; Hessian 87; Deriv 141; Core 96; Symplectic 102. Total 948; maximum 170, below 1500. Maximum line width is 100. These are independently measured counts; the handoff's Basic count of 168 differs by two physical lines without affecting the size gate.

The direct package inputs are S9-N `Norms`, `Kepler.Basic`, Mathlib and the internal Lift DAG. A recursive scan of all 72 reachable KAM source files finds zero `/Provider/` modules and zero frozen `/Theorems/` modules. The frozen imports are definitions only, so there is no SEALED/DRAFT_SORRY theorem-state exception to exercise. The 61 clean transitive axiom closures independently exclude hidden use of a draft theorem. No conclusion-shaped premise, bundled theorem field, new ambient norm instance or forbidden carrier occurs.

## Suspected source defects, deviations and limits

No new suspected defect in the blueprint, frozen declarations or pinned source was found. The lift is explicitly an original result: p9 line 121 says "Ours; the lift of a parameter-dependent symplectic map is standard (Maurer--Cartan)." No external-paper theorem is substituted here. The inherited source gap at p9 line 146 says the action-dependent rotation is symplectic on the full phase space "only after the angle correction"; this package proves precisely that correction. It does not claim to re-audit Fej04r/CP09/CP10, prove diagonalization, transport through the oscillator polar chart, close torsion, or seal a frozen root.

The design's global total R versus a family defined only on W is harmless: all analytic and symplectic assertions are restricted to the open cylinder and use derivatives from neighbourhoods inside W. The implementation's entrywise second derivatives are a calculus representation choice preserving the actual derivatives and source hypotheses. Conditional algebraic helpers have distinct names and are discharged by the parent proof. No new mathematical deviation or erratum is alleged.

## Kernel replay receipt

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularSpectrum.Lift KAM.Planetary.SecularSpectrum.Lift.Basic KAM.Planetary.SecularSpectrum.Lift.Analytic KAM.Planetary.SecularSpectrum.Lift.Calculus KAM.Planetary.SecularSpectrum.Lift.Hessian KAM.Planetary.SecularSpectrum.Lift.Deriv KAM.Planetary.SecularSpectrum.Lift.Core KAM.Planetary.SecularSpectrum.Lift.Symplectic
replaying KAM.Planetary.SecularSpectrum.Lift
replaying KAM.Planetary.SecularSpectrum.Lift.Calculus
replaying KAM.Planetary.SecularSpectrum.Lift.Hessian
replaying KAM.Planetary.SecularSpectrum.Lift.Symplectic
replaying KAM.Planetary.SecularSpectrum.Lift.Deriv
replaying KAM.Planetary.SecularSpectrum.Lift.Core
replaying KAM.Planetary.SecularSpectrum.Lift.Analytic
replaying KAM.Planetary.SecularSpectrum.Lift.Basic
exit 0
```

This was one invocation for the facade and every lemma module, after the signature/axiom process exited and before the complete lint run began.

## Complete lint receipt and final artifact check

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (532 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the exact permitted `KAM.lean is out of date` diagnostic. Module hygiene, frozen file hashes and all 144 elaborated ABI hashes pass. No forbidden proof escape, resource override, overlong line or oversized file is reported. The generated root was left untouched as required.

Final report validation: all 69 new public declarations are inventoried; all 61 new public theorem axiom outputs are present; no trailing whitespace. `git diff --no-index --check /dev/null /root/code/KAM-inp-s9l/docs/tracks/P/audits/S9-L-audit-1.md` emits no whitespace diagnostics (exit 1 because this is a new-file diff). `git diff --check inp...HEAD` exits 0. The only repository file created by this audit is this report; the pre-existing untracked `docs/tracks/P/audits/S9-L-handoff.md` is preserved. Audit scratch `.lean` and captured-output files were removed after incorporating the receipts. No state-changing git command was used.

Final disposition: **PASS WITH NOTES**. The exact S9-L lift contract and all five associated proof cuts are discharged, including the full action-dependent symplectic cancellation. Notes N1 and N2 concern comparison provenance and signature location; neither is a mathematical gap in the audited implementation. There is no frozen-anchor seal or campaign/root closure claim.
