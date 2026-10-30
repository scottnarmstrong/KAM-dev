# Independent SO-LOCK design audit 1

**Overall verdict: FAIL.** The 17 submitted declarations elaborate, but the proposed trusted square-root extension has two material contract defects (F1, F2), and the coordinate transport description disagrees with the landed maps (F3). These are design failures, not Lean elaboration failures. The odd-periodic Banach route and the conditional confinement signatures are viable. No theorem is proved or approved for freezing by this audit.

Auditor: maud-lockdesign-1, 2026-10-30. Audited HEAD `50807049876a82a57c8a5b6c9663206cdd7456f3`, base branch `inp` at `fa002b432ee0a320a0c96c0654b083ce8bd3b00d`. Read AGENTS.md, PLAN, DECISIONS (especially D45), the specified audit brief, both handoff filenames, the designer's originating brief/addendum, the design, freeze proposal, scoping study, and relevant landed implementation. Reviewed the complete `git diff inp...HEAD`: four additions only (design, freeze proposal, signatures, designer handoff); no production or frozen change.

## Signature-by-signature verdict

Names below have prefix `KAM.SpinOrbit.Lock`. PASS means the displayed contract survived this design audit; it does not mean its `sorry` body is proved. Numerical PASS entries remain provisional as explicitly required by the submitted DATA convention.

There is **no `blueprint-SO/` or `docs/graph/SO/` in this checkout**, and no SO-LOCK labels/consumer uses were found in the I/N/P blueprints. Accordingly, “SO §…” below is an exact design/scoping contract locator, not an invented blueprint label. The existing shared barrier contracts are `bpN:p3:gen-invariant` and `bpN:p3:gen-barrier` in `blueprint-N/parts/p3-hamiltonian-ode.tex:352,358`; these were compared directly with `KAM/ODE/Exit.lean:107,140`. Full new-track blueprint/packet fidelity is unavailable until those artifacts exist (N2).

| Lean name (signature line) | Blueprint label / available contract | Verdict | Reason |
|---|---|---|---|
| `IsSyncOrbit` (32) | No SO label; SO §1.1, D45 | PASS | C², period one, odd, and the exact physical second-order equation. `soField_eq` proves the proposed frozen-field spelling equivalent. |
| `lunarSyncOrbit` (39) | No SO label; SO §1.1 | PASS | Choice over the intended predicate; its fallback cannot enter downstream proofs once `_spec` is proved. Global uniqueness is only among the stated odd solutions. |
| `lunarSyncOrbit_spec` (43) | No SO label; SO §1.2, §2 | PASS | Genuine existence target, no hidden assumptions. Green/Banach route is consistent with this odd-periodic target. |
| `lunarSyncOrbit_unique` (46) | No SO label; SO §1.2, §2 | PASS | No pinning-ball premise; oddness provides both Dirichlet boundary values. Does not assert uniqueness among all periodic solutions (N4). |
| `lunarSyncOrbit_bound` (49) | No SO label; SO §1.2, §2.1 | PASS, DATA gate | Exact proposed literals match the proposal, but the recommended crude proof does not establish them; see N1. |
| `libAction` (56) | No SO label; SO §1.1; SCOPE §1 L1 | PASS | Correct elliptic quadratic form with the right nested product projections. Uses of positivity correctly assume Ω > 0. |
| `lunarOmega` (60) | No SO label; SO §1.1, §1.4 | PASS, DATA gate | Rational 0.1644, positively cast to ℝ. Final value must agree with the certified coordinate package. |
| `lunar_sync_lock` (68) | No SO label; D45/addendum, SO §1.2 | PASS, DATA gate | Names ψ*, quantifies arbitrary real initial states in the tube, all real times, exact `soField`, and uniqueness of global solutions. Existence of the required barrier and the literal inequalities remain unpaid. |
| `lunar_sync_lock_nonvacuous` (78) | No SO label; SO §1.2 | PASS | Action is identically zero at the stated centre point. This does not establish that an observed initial state lies in the tube. Dropping it is only a proposal. |
| `LockBarrier` (86) | No SO label; SO §1.5, §5; shared `bpN:p3:gen-invariant` | PASS | Explicit conditional helper certificate, not an assumed source result. Continuity, periodicity, positive lower bound and all-interval invariance are adequate. The complex argument is of Y/√Ω + i√Ω X, matching the sine/cosine convention. |
| `lock_confinement` (100) | SO §5; shared `bpN:p3:gen-barrier` | PASS | Ω > 0 and C² centre supply continuity of the action; P-periodicity removes the argument cut. Positive `Iin` protects the origin; V has frontier on the barrier. Global existence/uniqueness comes from the landed theorem. |
| `abs_le_of_libAction_lt` (107) | No SO label; SO §5; SCOPE §1 L1 | PASS | Nonnegative summands imply I > 0 from the premise; no separate I-positivity premise is missing. Norms are scalar absolute values as intended. |
| `sqrt_libAction_le` (113) | No SO label; SO §1.4 | PASS | Triangle inequality after weighting the two coordinates. The hypotheses force r,r′ ≥ 0; no regularity of arbitrary centre functions is needed for this pointwise algebraic statement. |
| `sqrtSem` (120) | No SO label; SO §4 | PASS | Principal complex power on its whole carrier. Its use as a new expression constructor breaks an existing global reality contract (F1), not this scalar definition. |
| `differentiableAt_sqrtSem` (123) | No SO label; SO §4 | PASS | Right half-plane is a sufficient branch domain. Available API is `DifferentiableAt.cpow_const` (N3). |
| `sqrtSem_sq` (125) | No SO label; SO §4 | PASS | Principal square root squares to w, including w = 0. No dropped nonzero premise is required here. |
| `sqrtSem_ball` (129) | No SO label; SO §4 | PASS | hs and the ball premise force r ≥ 0. Principal-root real part is nonnegative, so the denominator √w+s has modulus at least s. This scalar positive-centre rule is sound; it does not rescue the different model witness in F2. |

No submitted declaration is independently refuted. The overall FAIL concerns the additional extension/transport contracts the design explicitly requires provers to implement. Corrected contracts for those failures follow.

## Findings and corrected contracts

### F1 — HIGH — New principal sqrt makes existing unconditional expression-reality theorems false

**Location:** design §4, lines 225–239 and 258–260; `KAM/Certificate/Expr/Basic.lean:131–172`; consumer `KAM/Certificate/Sound/Ham.lean:68–77`.

The design requires all existing soundness theorems to be “re-proved with the new case.” `HamExpr.exists_real_eval` and `HamExpr.eval_real` currently quantify over **every** expression and **every** real point without a domain premise. The proposed expression `.sqrt (.const (-1))` evaluates to the principal square root of −1, which is not real. There is no new inductive proof case of the existing statements. This is an actual whole-carrier counterexample, even though the lunar data will avoid it.

**Fix:** explicitly replace these unfrozen global reality contracts with domain-qualified versions and update their consumers. `ham_structural` already has `hnv` and real-point membership, so its public conclusion can stay unchanged. Audit every other consumer; do not merely state that the old proofs acquire another case. Suggested exact replacement shapes in namespace `KAM.Certificate`:

```lean
theorem HamExpr.exists_real_eval_on {n : ℕ} (e : HamExpr n)
    {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hnv : e.NonvanishingOn S) (θ I : Fin n → ℝ)
    (hz : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ S) :
    ∃ r : ℝ, e.eval ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) = (r : ℂ)

theorem HamExpr.eval_real_on {n : ℕ} (e : HamExpr n)
    {S : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    (hnv : e.NonvanishingOn S) (θ I : Fin n → ℝ)
    (hz : ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ S) :
    (e.eval ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
```

These are proposed new unfrozen interfaces, not changes to any frozen anchor. Principal sqrt semantics must remain intact as ruled.

### F2 — HIGH — Composition witness accepts the opposite root; the quadratic argument is circular

**Location:** design §4, lines 250–254.

Take constant f = 1, W = W₀ = −1, ε_W = 0. Both stated checks hold: W²−f = 0 and ‖W−W₀‖ = 0 < |W₀| = 1. But √f = 1 and ‖√f−W‖ = 2, whereas the claimed zero-residual error bound is zero. The proposed inequality only yields e(2−e) ≤ 0 here; e = 2 is allowed. A quadratic inequality cannot select the small branch without a separate branch/continuation argument. The counterexample's algebra and principal-root value were checked by a sorry-free Lean `norm_num` example.

**Fix:** require a positive real anchor for W with a checked margin that places W in the right half-plane, and derive a denominator bound independently of the unknown error. A conservative scalar contract, usable pointwise on the strip, is:

```lean
theorem sqrtSem_model_error {f W : ℂ} {s d ε : ℝ}
    (hs : 0 < s) (hd : 0 ≤ d) (hds : d < s)
    (hf : 0 < f.re) (hW : ‖W - (s : ℂ)‖ ≤ d)
    (hres : ‖f - W ^ 2‖ ≤ ε) :
    ‖sqrtSem f - W‖ ≤ ε / (s - d)
```

Indeed Re W ≥ s−d > 0 and Re √f ≥ 0, hence |√f+W| ≥ s−d. The model checker must prove uniform versions of these bounds in its actual semantic norm, include outward rounding, and give the typed witness/check/soundness declarations. A coefficient-norm estimate cannot be inferred merely from a pointwise estimate. A sharper small-root formula needs an independently proved branch-selection lemma.

### F3 — HIGH — Coordinate transport uses the wrong landed map direction and omits an explicit momentum translation

**Location:** design §3 lines 187, 196, 203–207; compare `KAM/SpinOrbit/Rotated.lean:31–39,63–64` and frozen vector fields `KAM/Frozen/Defs/HamiltonianVectorField{,C}.lean:24–27`.

The landed `soRotMap` maps rotated coordinates **to physical** coordinates and leaves its first action equal to physical p. Its inverse goes from physical to rotated coordinates. It does not implement p′ = p−1. Thus “hence soField after soRotMapInv” is the wrong direction, and the displayed centred formulas cannot be inserted unaltered as `lockMapC` into `soRotHC` (whose kinetic term is P₀²/2−P₀).

There is also a literal two-form sign error: the displayed sine/cosine polar map satisfies dX∧dY = dα∧dI, or equivalently dY∧dX = dI∧dα. It does **not** satisfy the written dX∧dY = dI∧dα. The polar map itself is compatible with the frozen convention once this is corrected.

**Fix:** commit exact real and complex map definitions, include P₀ = 1+c′+Y, use `soRotMap` for physical projection, and state the actual conjugacy. A concrete corrected real contract is the following (local names are new suggestions; none is claimed landed):

```lean
def lockX (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 / (Real.pi * Ω)) * Real.sin (2 * Real.pi * z.1 0)

def lockY (Ω : ℝ) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  Real.sqrt (z.2 0 * Ω / Real.pi) * Real.cos (2 * Real.pi * z.1 0)

def lockToRotR (Ω : ℝ) (c : ℝ → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (![c (z.1 1) + lockX Ω z, z.1 1],
   ![1 + deriv c (z.1 1) + lockY Ω z,
     z.2 1 - deriv c (z.1 1) * (deriv c (z.1 1) + lockY Ω z) +
       lockX Ω z * deriv (deriv c) (z.1 1)])

def lockToPhysicalR (Ω : ℝ) (c : ℝ → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ × ℝ × ℝ :=
  (z.1 1 + c (z.1 1) + lockX Ω z,
   1 + deriv c (z.1 1) + lockY Ω z, z.1 1)

def lockHamiltonianR (Ω : ℝ) (c : ℝ → ℝ)
    (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) : ℝ :=
  z.2 1 + (lockY Ω z) ^ 2 / 2 - (deriv c (z.1 1)) ^ 2 / 2 +
    lockX Ω z * deriv (deriv c) (z.1 1) +
    soV (z.1 1 + c (z.1 1) + lockX Ω z) (z.1 1) - 1 / 2

theorem lock_conjugacy {Ω : ℝ} (hΩ : 0 < Ω) (c : ℝ → ℝ)
    (hc : ContDiff ℝ ⊤ c) (z : (Fin 2 → ℝ) × (Fin 2 → ℝ)) (hI : 0 < z.2 0) :
    fderiv ℝ (lockToPhysicalR Ω c) z
      (KAM.hamiltonianVectorField (lockHamiltonianR Ω c) z) =
    soField (lockToPhysicalR Ω c z)
```

The complex eval identity must use the complexification of this corrected `lockToRotR`, not the untranslated p′ map. A trigonometric centre is smooth; if the full four-dimensional map is instead parameterised by arbitrary c, C² alone does not justify differentiating its c″ clock-action component. Give the required higher regularity explicitly. These repairs preserve the physical headline.

## Notes and remaining gates

**N1 — MEDIUM — Literal bounds are placeholders, not targets discharged by the chosen crude estimate.** Design §2.1 explicitly proposes replacing 13/10⁶ by 3/10⁵, but the signatures and proposal still contain 13/10⁶ and 1/10⁴. Evaluating the displayed coefficient formulas gives L ≈ 0.033763 (the advertised 0.067 is a conservative overestimate), η ≈ 0.000535393. The c=0 argument as written yields η/(32−L) ≈ 1.67487·10⁻⁵ and a derivative bound ≈ 1.33990·10⁻⁴, neither sufficient for the two displayed literals. These floating computations diagnose the gap; they are not certified bounds or a refutation of the tighter true values. Fix both literals using proved rational bounds, or give the sharper analytic/residual argument. Keep N65 certifier thresholds, residuals, graph positivity, final tube-transfer inequalities and all DATA literals open until actual kernel evidence. The radius rules in §1.4 are conservative (they also add r,r′ after action transfer); this loses sharpness but is not unsound.

**N2 — MEDIUM — Critical interfaces and new-track fidelity are not yet reviewable.** No SO blueprint/packets exist. In §1.5/§6, `LockGraphCert`, `lockBarrier_of_certV2`, `lunar_sync_lock_of_cert`, `lockHamExpr_eval`, `_clock` and the map/inverse/conjugacy contracts have only names or ellipsis sketches. Several do not require the new constructor just to state. Before dispatching these packages, supply actual typed signatures, centre/frequency/domain binders, lawful arithmetic instances, equality tying `g.base.ham` to the transformed Hamiltonian, graph monotonicity and displacement margins. A bare passing generic certificate does not imply this physical `LockBarrier`. In particular, `LockBarrier.invariant` must be produced from the certifier and conjugacy, never assumed in a source theorem. The existing structure is legitimate as an explicitly named conditional helper.

**N3 — LOW — One cited Mathlib name does not exist.** `#check Complex.differentiableAt_cpow_const_of_mem_slitPlane` reports `Unknown constant` on the pinned build; no matching declaration was found in Pow sources. The alternative `DifferentiableAt.cpow_const` exists and takes the slit-plane premise as needed; import `Mathlib.Analysis.SpecialFunctions.Pow.Deriv`. Replace the nonexistent alternative name. The contraction API names, bounded-continuous-function completeness and interval-integral derivative API all checked successfully.

**N4 — LOW — Delete the claim of uniqueness without oddness.** Design §1.1 lines 55–57 says uniqueness among all periodic solutions is also true. Given any solution ψ, ψ+1/2 has the same force (q has period 1/2), is periodic, and is distinct as a real-valued function. The scoping study itself identifies the two synchronous orientations. Oddness excludes this translate and must remain in the uniqueness predicate. No correction to the submitted odd-only theorem is needed.

**N5 — LOW — Ownership and proof-replay wording.** The package table's split is acyclic at package level and its new-file size estimates fit 1500 lines, but its “all Lean under Lock/” sentence has the declared checker-file exceptions. Assign and inventory every shared checker file before LOCK-SQRT and recheck existing sizes after additions. `LOCK-DATA` mentions `#eval/decide` replay modules: source lint forbids `#eval` in production Lean; reserve diagnostic evaluation for scratch/scripts and use kernel-checked proof declarations for production certificates. Data cost and the under-900-line aspiration are projections, not measured results.

## Consumer, frozen-object, definition and package verdicts

- **Consumers: FAIL for the whole route**, owing to F1–F3 and the untyped interfaces in N2. The existing `lock_confinement → gen_barrier` application is compatible: W=G=univ, J=univ, global solution, open V, initial point outside S. The positive-Iin core avoids the undefined polar angle at the centre; period-one P removes the branch cut. `Graph/Inverse.lean:223–236` supplies the right all-interval uniqueness pattern. A forward physical orbit from the torus is preferable to a nonexistent global real-valued inverse polar angle.
- **Frozen objects: PASS for submitted statements, pending future bridge implementation.** No `KAM/Frozen/SpinOrbit` directory or SO manifest anchors exist in this checkout: D40 is approval to freeze later, not evidence of a completed freeze. “Frozen soField” in the handoff/design is therefore inaccurate locally. Both proposal spellings use the landed model and `soField_eq` supplies the bridge (independently proved by `rw` in the probe). Read the actual frozen real/complex Hamiltonian vector fields and `realHamiltonian`; no parallel replacement of them was introduced. `HamExpr` is not frozen or referenced by the manifest; extending it is permitted, subject to the corrected soundness contracts.
- **Definitions: PASS for the 6 submitted definition/structure declarations.** No global instance is introduced. `libAction` is total, but positivity is only used under Ω>0. `deriv` on arbitrary curves is only used algebraically in the transfer helper; geometric uses supply smoothness. `LockBarrier` is a conditional helper, not closure of the native certificate route. The chosen orbit's fallback is excluded by the explicit existence theorem. **Proposed expression/model definitions: FAIL** until F1/F2 are repaired.
- **Packages: PASS WITH NOTES for size and coarse dependency order; not ready for full proof dispatch.** LOCK-PO and the conditional LOCK-CONF can proceed; LOCK-SQRT requires F1/F2 and shared-file ownership; LOCK-COORDS requires F3 and exact signatures. No new file is designed above 1500 lines. No source theorem is replaced by an assumed barrier.

## Validation receipt

The original signatures were copied byte-for-byte into `.drafts/scratch/SOLockSignatures.lean` and elaborated **once**, using the prescribed gated wrapper, which runs against `/root/code/KAM-inp`'s build snapshot:

```text
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-lockdesign .drafts/scratch/SOLockSignatures.lean
[sig-gate] slot 1 acquired 16:11:19
exit 0
11 warnings: declaration uses `sorry`
lines 43,46,49,68,78,100,107,113,123,125,129; no other diagnostics
SHA256 original = scratch:
ed378c946712c0c8e53edcfc9cf346f5b84fbc5155fbd249e3133b59d0f0c2c7
```

Additional probes were confined to `.lake/abi-scratch/SOLockAuditProbe.lean`. An initial auditor import guessed `V2.RouteA` (not a landed module); it was corrected to `V2.RouteARefinedEngine`. The negative API probe produced the N3 diagnostic. A notation-only probe was changed to the full `BoundedContinuousFunction` name. The final probe run exited 0, with no warnings; it checked the cited APIs, `routeAV2`, `checkTorusCertificateV2_sound`, the reality contracts, a proof of the orbit-equation bridge and the opposite-root counterexample. These were separate small probes; the submitted signature file was not re-elaborated.

`#print axioms` on each of `soField_eq`, `so_global_exists_unique`, `KAM.ODE.gen_barrier` and `checkTorusCertificateV2_sound` returned exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The 11 draft theorems themselves remain `sorry` declarations and hence use `sorryAx`; their existence is not proof evidence. No new production module exists to target with `lake build`, so the requested signature elaboration is the targeted Lean gate; no library rebuild or kernel replay of nonexistent proofs was attempted. All audit elaborations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; no budget overrides or state-changing git operations were used.

`git diff --check inp...HEAD`: exit 0. Source lint was run as `LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh` and exited 1. Its relevant output was:

```text
check_lean_modules: PASS (1628 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
.../.lake/abi-scratch/tmptwwjdlli.lean:1:0: error: unknown module prefix 'KAM'
No directory 'KAM' or file 'KAM.olean' in the search path entries:
.../KAM-inp-lockdesign/.lake/build/lib/lean
```

The worktree has no `.lake/build`; the signature gate deliberately uses the shared `inp` build instead. No forbidden-token, line-size, generated-root, module-header or frozen-file diagnostic was emitted. **The overall lint gate did not pass, and the worktree-local ABI check is unverified**; no build snapshot or generated files were created to mask that limitation. The earlier lint invocation was interrupted during the Python frozen-anchor check, before its Lean ABI phase, and replaced by the fully serialized invocation above. There was no overlap of audit Lean processes.

Final cleanup removed `.drafts/scratch/SOLockSignatures.lean` and `.lake/abi-scratch/SOLockAuditProbe.lean`; the ABI tool removed its own temporary file. `git status --short` contains only the requested untracked report; `git diff --check` exits 0. The report is the sole retained edit.

## Errata, deviations and scope

F1–F3 and N1–N5 concern our own design/code contracts, not suspected defects in a pinned external source. No pinned-source erratum is asserted: this audit does not validate Celletti novelty claims. The design correctly leaves that literature claim conditional. Banach instead of Newton–Kantorovich is a justified departure for the odd problem; its Green bound is 1/32 on an interval of length 1/2 and the derivative bound is 1/4. The global uniqueness characterisation remains limited to odd solutions. Naming ψ* satisfies the originating brief's addendum. Numerical literals and freeze approval remain future gates.

Only this report is retained as an audit edit. Temporary signature/probe files are removed. No repair was silently applied to the design, signatures, frozen files, manifest, generated roots or README.
