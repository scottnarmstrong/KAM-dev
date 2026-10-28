# N11-L1 independent package audit 1

Overall verdict: **FAIL for complete slice acceptance**. The five public theorems are sound as stated; `ef-id` passes. The claimed `ef-C` export is a valid conditional estimate, but does not establish the complete literal node assigned by the audit focus. No proof escape, false identity, or projection error was found. This is a statement/completeness finding, not a kernel failure.

## Scope and authority

Audited 2026-10-28 in `/root/code/KAM-inp-n11l1`, HEAD `8f924ce0d0016030307f265fdd8290832c538c5b`; comparison `inp` was `eedc66febf1e2749337a502351ab1515c1779c15`.
Only production file audited: `KAM/Nekhoroshev/Partial/EnergyIdentity.lean`, SHA-256 `7353cc62d7267609a7ce299449f6b209a205d833bbd2a1e0fdc7bfc79cae6128`.

Read AGENTS.md, PLAN, DECISIONS, external package brief, handoff/AUDIT FOCUS, N11 design and both design audits, external signatures, N track statement, the partial-convex frozen theorem and relevant frozen definitions, and blueprint p11c L78–108. The signatures SHA-256 was `a87a457f07c997e6a922e3f3ada6bf8f3e82195761a6f7109fabeef80f08ef04`. The current file is authoritative; older design-audit fingerprints describe older deliveries.

The user's exact worktree report destination overrides the generic brief's MAIN-worktree destination. Only this report is a persistent audit edit; temporary probes/logs were confined to `.lake/abi-scratch/` and removed. No production fixes, frozen edits, git mutations, network research, or delegated work.

`git diff inp...HEAD` emits `multiple merge bases, using ca5b8ed55a4e550447c36b2ad3a71b0f6eada37d` and includes 81 files, 11072 insertions and 357 deletions. Its protected-path diff is **not empty**: inherited `KAM.lean`, the N-HEAD-C seal, and its manifest state change appear. These are reported rather than silently ignored. The package starts after merge `4bba1d30`; `git diff 4bba1d30..HEAD --stat` contains only EnergyIdentity (429 additions), and that range's protected-path diff is empty. No N11-L1 protected-path violation is attributed to the inherited integration history. Other packages in the three-dot diff are outside the explicit single-file audit scope.

## Declaration and node ledger

Names below are in `KAM.Nekhoroshev`.

| Node / role | Declaration and file line | Verdict | Reason |
|---|---|---|---|
| Supporting class lemma | `ext_class_liftFast`, L65 | PASS | Holomorphy transported through the actual fast-action projection; fast-only functions are angle-periodic; reality follows on the visited tube. RealFastConvex is the energy-source bundle, not the rejected complex-bound bundle. |
| Supporting class lemma | `ext_class_add`, L74 | PASS | Actual pointwise sum preserves holomorphy, periodicity and reality. No extra conclusion-shaped assumption. |
| `stepN:p11:ef-id`, eq:lie | `energy_identity`, L239 | PASS | Exact differential identity, including weighted slow bracket and self-bracket cancellation; no frequency upper bound. HasDerivAt is stronger than an informal derivative equality. |
| `stepN:p11:ef-id`, real form | `energy_identity_re`, L282 | PASS | Real gradient is the frozen frequencyMap, with complex-to-real transport proved locally; no alternate frequency definition. |
| Generic transverse estimate | `transverse_pairing`, L337 | PASS as conditional helper | Proves the displayed bound with supplied majorants B1–B4. Works for both time signs and for any orthogonal projection fixing the resonance span. |
| Complete `stepN:p11:ef-C`, p11c L103–107 | `transverse_pairing`, L337–425 | **FAIL** | Missing source-to-majorant estimates and numerical terminal conclusion; see F1. The declaration's docstring explicitly identifies it with this node. |
| Frozen N-PARTIAL-CONVEX | `partialConvex_nekhoroshev` | Not seal-ready; outside this slice | L1 provides no provider export or frozen seal. The frozen theorem still has its manifest-bound placeholder body. No full-anchor proof is inferred from this package. |

There are **no SIGNED declarations for L1** in the delivered signature file: none of these five names occurs there. Exact provider/frozen-type and seal-body probes are therefore not applicable to this helper package. In particular, the signed `energy_free` at signature L583 is L2's obligation, not an export implemented by this file. Its source premises cannot be replaced by L1's four majorant assumptions.

## F1 — Major: the claimed ef-C node is only partially discharged

Evidence: EnergyIdentity L332–351 identifies `transverse_pairing` as “step `ef-C`” but assumes

- B1 bounds the real bracket on the entire orbit stretch;
- B2 bounds the angular gradient there;
- B3 bounds frequency drift there;
- B4 bounds the initial projected frequency.

Its conclusion at L352–354 is only

`C ≤ |Re fs(y(t1)) − Re fs(y(0))| + |t1| (B1 + (B3+B4) B2)`.

Blueprint `p11c-partial-stability.tex` L103–107 does more. Besides the first displayed supremum estimate, it derives the angular and bracket bounds on the **half-radius tube**, substitutes `M Delta = M r/4` and `5 delta/4`, checks the numerical coefficient, and concludes literally

`C ≤ 2 eta + 0.1220 M r eta |t*| / s ≤ 2 etaBar + 0.0061 m r^2`.

The local file neither states nor proves that terminal estimate. It has no remainder WBound premise from which B2 or endpoint oscillation is established, no half-tube estimate for B1, and no derivation of B3/B4 from the source Hessian/initial/resonance data. The handoff expressly leaves all four bounds to L2. This is honest disclosure, but does not meet the user's requirement that every assigned node be established and an unsigned node export state its literal conclusion. A true general estimate with additional proof obligations is not complete node closure.

Adversarial recheck: the bound is not merely a different arrangement of `M Delta` and `5 delta/4`. The four majorants are unconstrained parameters apart from their bounding premises; the theorem has no smallness/time data allowing the final constants to be inferred. Its internal proof uses those premises, not the RealFastConvex Hessian/convex fields to establish them. This excludes a hidden internal proof of the missing node tail.

Required disposition: retain the valid conditional helper under an explicitly conditional role and add the source-instantiated numerical corollary/proof, or obtain an explicit reassignment of the numerical tail to L2 and audit its completed implementation before recording ef-C as established. This audit does not silently change the node allocation. No change to the signed L2 or frozen theorem is authorized or needed.

## Projection deviation and L2 consumption

The claimed projection deviation itself **passes**. For `DeltaI = I(t1)-I(0)` and the source `PiPerp = id-P`, its action is exactly `DeltaI-P DeltaI`. Self-adjointness gives

`(omega0-P omega0) dot DeltaI = omega0 dot (DeltaI-P DeltaI)`.

A fresh Lean example proved this with `rw [sub_dotProduct, hP.symm, dotProduct_sub]`, exit 0. The production proof establishes the same equality at L409–419. Thus this representation introduces no constant loss and does not change C. Requiring only that P fix the resonance span generalizes the canonical projection case; L2 can select the projection onto that span using the existing `KAM.Stability.exists_orthProj`.

The signed L2 assumptions supply the appropriate kinds of inputs: RealFastConvex; WBounds for g and fs; spectral support; NearResonance; initial collar; slow margin; and smallness/time data. They do not supply B1–B4 verbatim. L2 must still prove them on its stopped stretch, use the smaller tube for the bracket estimate, and finish the arithmetic. `Energy.lean` is absent in this checkout and repository search finds no consumer of L1 outside this module. Consequently there is no observed consumer break from the dual pairing, but actual unaffected L2 compilation and full source-premise consumption cannot be certified. The first unpaid quantitative attachment is B1–B4, not the projection rewrite.

## Definitions and proof review

No new public def, abbrev, structure, instance, or root declaration is introduced. All five public theorem names are unique in the repository search; they stay in the intended namespace. The three private definitions are:

| Definition | Classification | Whole-carrier behavior |
|---|---|---|
| `wvec`, L87 | Coordinate algebra | Weighted skew field for an arbitrary complex continuous linear functional; slow signs and weight c agree with Setting.wfield. Self-pairing vanishes for every c, including zero. No fallback. |
| `fastCLM`, L135 | Coordinate projection | Genuine complex continuous linear map selecting the first n base coordinates, valid also for zero coordinate dimensions. No fallback. |
| `cxCLM`, L181 | Scalar inclusion | Genuine real continuous linear map on both factors; equals extCx componentwise. No fallback. |

Derivative totalization is guarded by holomorphy at interior visited points. `fast_mem_polyNbhd` extracts the fixed fast center from the actual base witness. The real Hamiltonian's indicator agrees locally with its real holomorphic restriction inside the open real domain; `real_system` supplies the field identity. The proof does not exploit off-domain indicator values. `freq_real` uses local reality to identify the complex differential with frozen frequencyMap. The weighted self-bracket cancellation includes both slow directions. For the transverse bound the observable `(omega0-P omega0) dot I + Re fs` cancels the resonant g-gradient by self-adjointness and spectral support. The convex mean-value estimate on `uIcc` handles negative, positive, and zero time. No upper bound on omega or conclusion-shaped confinement hypothesis is hidden in these proofs.

The dependency closure has no provider or frozen theorem imports, hence no DRAFT_SORRY anchor dependency. Its frozen imports are definitions only. Standard axiom results below independently confirm no sorryAx enters any public export.

## Independent verification

Every audit Lean/Lake command used `LEAN_NUM_THREADS=1` and `nice -n 5`; build, probe, kernel replay and lint were run sequentially. One audit Lean command at a time; unrelated sessions elsewhere on the host were not controlled by this audit. No resource limit was overridden.

1. Targeted compile gate:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11l1 KAM.Nekhoroshev.Partial.EnergyIdentity
   ```

   Exit **0**. Output begins `[inp-gate] slot 1 acquired 20:54:30 for KAM.Nekhoroshev.Partial.EnergyIdentity` and ends `Build completed successfully (3275 jobs).` Replayed warnings occur in inherited Stability.Gradient, Partial.Coordinates and Partial.RealSystem; no target-file diagnostic was emitted.

2. Fresh `.lake/abi-scratch/N11L1Audit.lean`, importing only EnergyIdentity, with all five `#print axioms` commands and the projection equality example:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11L1Audit.lean
   ```

   Exit **0**, no error. Exact axiom output:

   ```text
   'KAM.Nekhoroshev.ext_class_liftFast' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.ext_class_add' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.energy_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.energy_identity_re' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.transverse_pairing' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.EnergyIdentity
   ```

   Exit **0**. Exact output: `replaying KAM.Nekhoroshev.Partial.EnergyIdentity`.

4. Source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the explicitly permitted stale-generated-root exception. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (923 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generated root was left untouched.

5. Static and artifact checks: 429 lines, no line longer than 100 Unicode characters; required module header, copyright, public imports, docstring and public noncomputable section are present. No sorry/admit/axiom/unsafe/opaque/EuclideanSpace or resource overrides in the target. No reused public helper short name or harmful root shadow found. `git diff --check` passes. The new-report `git diff --no-index --check /dev/null docs/tracks/N/audits/N11-L1-audit-1.md` emitted no whitespace diagnostics (exit 1 because the files differ). Temporary audit probe/log/diff files were removed; final status contains only the pre-existing untracked handoff and this new report.

## Source defects, deviations and remaining uncertainty

No new suspected error in a pinned mathematical source or blueprint equation was found. No pinned PDF was independently re-audited in this scoped Lean package review. The design audit's rejection of a complex Hessian premise remains respected here: RealFastConvex has only a real upper Hessian bound. The unsigned conditional replacement of complete ef-C is a package-to-blueprint deviation (F1), not evidence that the blueprint is false. The dual projection formulation is equivalent and acceptable. Historical design findings are not reopened by this report.

Do not mark ef-C complete or N-PARTIAL-CONVEX seal-ready from this package alone. The result can be accepted as sound omega-free identity infrastructure, with the quantitative attachment explicitly unpaid until the prescribed node is completed or reassigned and checked.
