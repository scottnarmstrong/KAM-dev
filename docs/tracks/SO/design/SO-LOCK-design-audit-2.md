# SO-LOCK strict delta design audit 2

**Overall verdict: FAIL.** The revised total square root preserves unconditional reality, the anchored witness excludes the opposite root, and the corrected real coordinate maps/conjugacy have the right signs and direction. However, the claim that **every landed declaration keeps its statement** fails at `HamExpr.nonvanishingOn_of_inv_good` (finding 1). The newly typed `lockHamExpr_clock` is false for negative Ω (finding 2). Neither defect is detected by elaborating `sorry` bodies. Nothing is approved for freezing or claimed proved here.

Auditor: maud-lockdesign-2, 2026-10-30 UTC. Tier 2, refute-first delta audit under the supplied design-audit brief and the manuscript-audit protocol. Authorization: retain only this report; temporary scratch elaborations permitted; no source repairs, commits, frozen/manifest/generated-file changes, or library rebuilds. Scope is F1–F3, N1–N5 and changed sections of the three submitted design artifacts. Unchanged round-1 conclusions are carried as scope boundaries, not independently recertified.

## Frozen inputs and comparison

Worktree HEAD: `6c076a6d958d7ea98988a1b896d94e8297b4adca`. Delta base: `50807049876a82a57c8a5b6c9663206cdd7456f3`. All locators below refer to this HEAD unless stated otherwise. Reviewed `git diff 50807049 HEAD`, including the revised handoff and unmodified round-1 report added to history. The delta changes no `KAM/` or `manifest/` file.

| Input | SHA256 |
|---|---|
| `docs/tracks/SO/design/SO-LOCK-DESIGN.md` | `46b5eed0fa824040b3eef7f1d463ca27d74a9acff32583437d93b948518d1452` |
| `.drafts/design/SOLockSignatures.lean` | `66199f977fc491c4d14e1b0d8f6977fc9c626b5d12fb52b9f95670484f13ddf8` |
| `docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` | `48c095c36dcbdfa0c5b77d52d4c1913fb019785ad5b8296b7ebf063b2ddf5094` |
| `.drafts/handoff-DESIGN-LOCK.md` | `f6c7c09e945b7cb067b123cbbd57c19f1b5fb06145debbe04e503387b60029f5` |
| `docs/tracks/SO/design/SO-LOCK-design-audit-1.md` | `cb30b6ab0b13678a1d70f3ad3c59cd8ad9d363d9ce5c9269ec2ed2a39949dff4` |

Read the repository rules, PLAN, DECISIONS and the requested audit brief. The signature wrapper used the shared `inp` build; shared source HEAD observed during verification was `003c5a3a04b09690bc03ab763b69e159641da2b4`. The inspected `Expr/{Basic,Ball,Diff}.lean`, `SpinOrbit/Rotated.lean`, and both frozen Hamiltonian-vector-field definitions were independently byte-compared with that checkout: all SAME. No remote information was needed.

## Findings

### 1. HIGH — F1 only partially closed: inverse safety cannot establish the new sqrt domain arm

**Anchors:** design §4.2:332–342, “This changes no existing equation, so no landed statement's text changes”; §4.6:388, “No landed declaration's statement changes.” Landed `KAM/Certificate/Expr/Ball.lean:380–381,424–426`:

```lean
def SlpInvGood (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (ops : List SlpOp) : Prop :=
  ∀ j a : ℕ, ops[j]? = some (SlpOp.inv a) →
    ∀ z ∈ S, (Slp.vals n z ops).getD a 0 ≠ 0

theorem HamExpr.nonvanishingOn_of_inv_good {D : Set Ph} (hD : IsOpen D) (e : HamExpr n) :
    ∀ (s ops : List SlpOp), (slpCompile e s).1 <+: ops → SlpInvGood n D ops →
      e.NonvanishingOn D
```

The proposed `.sqrt a` arm of `NonvanishingOn` requires `∀ z ∈ D, 0 < (a.eval z).re`. The existing premise certifies only nonzero operands of inverse instructions. It says nothing about real-part positivity. Adding a separate theorem named `nonvanishingOn_of_sqrtGood` cannot supply the missing premise to this existing universal theorem.

**Refutation of the unchanged-contract claim:** take `n = 1`, `e = .sqrt (.action 0)`, and the open domain `D = {z | ‖z.2 0 - Complex.I‖ < 1/4}`. On this domain the action is nonzero and away from the nonpositive real axis. The proposed sqrt jet and its inverse-of-root derivative instructions have nonzero inverse operands throughout D, so `SlpInvGood` holds for the emitted program. Nevertheless D contains the point with action `Complex.I`, whose real part is zero, so the proposed `e.NonvanishingOn D` is false. This defeats the natural attempted repair “the derivative emits an inverse, so invGood already pays for sqrt.” Even an emitted inverse of the original action would only establish nonzeroness. Reinterpreting the sqrt arm as slit-plane membership would be a different submitted contract; the submitted arm explicitly requires positive real part.

**Required correction:** explicitly resolve the old helper, rather than promising an induction case. A sound new contract, after defining `SlpSqrtGood` as specified by the design, is:

```lean
theorem HamExpr.nonvanishingOn_of_program_good
    {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D) (e : HamExpr n)
    (s ops : List SlpOp) (hp : (slpCompile e s).1 <+: ops)
    (hi : SlpInvGood n D ops) (hs : SlpSqrtGood n D ops) :
    e.NonvanishingOn D
```

This is a proposed post-extension contract, not an elaborated declaration in the submitted file. It does **not** by itself preserve the old theorem. The designer must either obtain an explicit exception for replacing/restricting that unfrozen helper, or explicitly redesign the safety predicate/compiler so the literal old helper is true, documenting the semantic change. Silently strengthening the meaning of `SlpInvGood` is not a match-case-only repair.

The consumers `HamExpr.nonvanishingOn_of_balls` (`Expr/Ball.lean:497–502`) and `nonvanishingOn_of_ballsTrig` (`CertificateSharp/Ham/BallsTrig.lean:400–405`) can retain their statements: successful balls must provide **both** safety predicates, then use the new combined lemma. `checkHamBounds_sound` and `TorusCertificate.ham_structural` can also retain their statements. The old intermediate universal theorem is the unpaid obligation.

**Positive F1 result:** `sqrtE` sends real x ≤ 0 to 0 and real x > 0 to the nonnegative real root. Thus `HamExpr.exists_real_eval` (`Basic.lean:131`) keeps precisely its existing unconditional statement, with a new sqrt induction case via `sqrtE_ofReal`. `HamExpr.eval_real` (`Basic.lean:169`) also keeps its statement, and its existing proof can remain unchanged: it calls `exists_real_eval` and projects the imaginary part. The handoff's “one case each” is imprecise: `eval_real` is not an induction. Integer periodicity, open-domain smoothness under the extended `NonvanishingOn`, compiler soundness, and `jet_d1/d2/d3` all have compatible existing contracts; the unconditional `jet_v0` remains a value identity, not a global differentiability assertion.

**Status:** survived a separate adversarial pass over the actual inverse predicate, emitted derivative denominators, domain arm, and both direct consumers. This is a design-level contradiction for the specified emission, not a kernel counterexample to the unextended landed language.

### 2. HIGH — N2/F3 delta: `lockHamExpr_clock` needs positive Ω

**Anchor:** signatures:282–284, and design §3:283, “holds on 0 < Re I.” The theorem quantifies arbitrary `Ω : ℚ`; only `0 < (z.2 0).re` is assumed. Positive action does not place `I/(πΩ)` or `IΩ/π` on the analytic branch when Ω is negative.

**Counterexample using the required eval identity:** choose Ω = −1, `cs = []`, and `z = ((0,0),(1,0))`. Here `Re I = 1 > 0`, both sqrt operands are −1/π, and both totalized roots are zero. Write C = `soV(0,0) − 1/2`. Then `soRotHC (lockToRotC (-1) [] z) = C`. Approach z through `I = 1 + i t`, t > 0, leaving the two angles and clock action fixed at zero. Along this sequence X = 0, while the sqrt operand for Y is off the cut, so `Y² = −(1+i t)/π`. Hence the Hamiltonian value is `C − (1+i t)/(2π)`, with limit `C − 1/(2π) ≠ C`.

By `lockHamExpr_eval` (which intentionally quantifies all Ω and all z), the expression evaluator is therefore discontinuous at z, hence not complex differentiable there. Lean's total `fderiv` is zero at a nondifferentiable point (`fderiv_zero_of_not_differentiableAt`, checked in the probe). Applying it to the clock direction gives **0**, contradicting the asserted **1**.

**Adversarial check:** affine dependence on J̃ does give a clock-direction partial derivative, but the statement uses the full Fréchet derivative. Affine dependence on one variable does not repair discontinuity in another. Ω = 0 is not this counterexample: total division then collapses the polar terms. The negative-Ω case suffices.

**Corrected signature:**

```lean
theorem lockHamExpr_clock (Ω : ℚ) (hΩ : 0 < Ω) (cs : List ℚ)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : 0 < (z.2 0).re) :
    fderiv ℂ (lockHamExpr Ω cs).eval z
      (KAM.Certificate.phaseBasis (.inr 1)) = 1
```

The graph/assembly callers already have `hΩ`, so this repair changes no physical headline or frozen definition. Status: survived the affine-clock alternative and direct expansion through the landed `soRotHC` convention. The new constructor does not yet exist, so this is an analytic counterexample to the joint proposed definitions/eval/clock contracts, not a claimed sorry-free Lean proof.

### 3. LOW — N1: bounds are now reachable; precision rule and proof-status wording need correction

The previous orbit-literal obstruction is closed at design level. Using `Fraction` arithmetic on the exact seven polynomials of `SpinOrbit/Model.lean:64–73`, e = 549/10000, ε = 69/200000 and π majorant 31416/10000 gives:

```text
L_upper   = 0.03376315624360834… <= 0.033764
eta_upper = 0.0005353940265159194… <= 0.00053540
eta_upper / (32 - L_upper) = 0.000016748734895909… <= 17/1000000
(eta_upper + L_upper * (17/1000000))/4
          = 0.0001339920000430152… <= 27/200000
```

The four displayed comparisons were checked as exact rational inequalities, not floating comparisons. This validates arithmetic conditional on the proposed analytic majorants; it does not prove the Green/contraction theorem in Lean. Design:123 says “proved by `norm_num`” and the proposal summary says “are proved,” but the submitted theorem is `sorry`. Read these as the intended proof route; replace the completed-proof wording before owner review.

The centre triangle bounds give r ≤ 0.00002936716 and r′ ≤ 0.000215123240736 using the same π upper bound. Floating diagnostic evaluation gives δ ≈ 0.00110512, entry action after transfer ≈ 0.01315226 < 0.013238, angle bound ≈ 0.20508434 < 0.21, and spin bound ≈ 0.02545266 < 0.026. These confirm comfortable provisional margins, conditional on the stated barrier extrema. They are not certified torus bounds.

Design:142 calls Rp the “smallest 3-digit rational,” but 0.0255 already exceeds 0.02545266 and has three significant digits. The displayed 0.026 is safe but is not that smallest value if “digit” means significant digit, as in the entry rule. Specify decimal places or change the rounding rule; this is an owner-facing literal-selection discrepancy, not an unsound confinement estimate. The no-double-δ transfer is valid.

Status: note survives recomputation; no claim that the actual headline literals have passed the kernel.

### 4. NOTE — N2: interfaces substantially supplied; original source/graph and implementation gates remain

The revised `LockGraphCert` and two certificate consumers now expose Ω, centre coefficients, positive time scaling, the exact `hham` equality, lawful backend, V2 witness, graph check, frequency enclosure and Diophantine data. The barrier theorem also has the necessary positive widened lower action. `lunar_sync_lock_of_cert` can obtain that positivity from the eventual literal-check soundness (or has a vacuous entry premise for nonpositive Iin); it must not silently assume it.

The graph route can use the landed `soGraph_exactTorus_of_certified` for monotonicity/action transfer. Clock rigidity and graph inversion then construct the librational graph, with the frequency divided by κ after undoing the time scaling. In design:291–295, `Φ(K∞(θ+tω))` is a physical solution only when ω denotes this **unscaled** frequency, not the certifier's original ωstar or sinf·ωstar. The typed contracts permit this correction. `LockBarrier.invariant` remains an output; no source theorem assumes it as a replacement for the certificate proof.

There is still no `blueprint-SO/` or `docs/graph/SO/` in this snapshot. No invented blueprint labels are assigned below. The design itself is the available local contract. The three explicit placeholder definitions, all 26 theorem bodies, the literal checker and its soundness, sqrt-domain plumbing and actual kernel data remain unpaid. Their being named and typed closes the missing-interface aspect of N2, except for findings 1–2; it does not close a theorem or permit removal of implementation gates.

### 5. LOW — N5: inventory is useful, but “match cases only” is not an accurate implementation contract

All listed current line counts were checked with `wc -l` and agree with §4.6. There are 13 non-test paths plus the optional 14th test path. The exact landed-file inventory, with the scope of required additions, is:

| Landed path under `KAM/` | Required delta; existing theorem contracts |
|---|---|
| `Certificate/Expr/Basic.lean` | New constructor, eval/domain arms, reality/periodicity/smoothness induction cases; `eval_real` proof need not change. |
| `Certificate/Expr/Slp.lean` | Opcode and semantic step arm. The table's compiler-arm attribution belongs in `Diff.lean`, not this file. |
| `Certificate/Expr/Ball.lean` | Ball soundness cases plus new sqrt-safety extraction; **old helper exception in finding 1**. |
| `Certificate/Expr/Diff.lean` | Compiler arm, new-node soundness, empty-domain case; existing compiler/value/jet theorem signatures can remain. |
| `Certificate/Expr/DiffNode.lean` | New sqrt-node constructor/proofs; existing node theorem signatures can remain. |
| `Certificate/Expr/DiffBuild.lean` | Possible builder helpers; no exhaustive HamExpr/SlpOp case presently requires a change. |
| `Certificate/Expr/DiffCalculus.lean` | New calculus lemmas; no expression match to extend. |
| `Certificate/Expr/DiffCalculus3.lean` | New higher-derivative lemmas; no expression match to extend. |
| `Certificate/Expr/Compose.lean` | New witness field/counter/routing and composition soundness cases; existing theorem signatures can remain. |
| `Certificate/Expr/ComposeModels.lean` | Optional helpers; no exhaustive HamExpr/SlpOp case presently requires a change. |
| `Certificate/Sound/Ham.lean` | Domain proof plumbing; public soundness/structural statements can remain. |
| `CertificateSharp/Ham/BallsTrig.lean` | Sqrt ball case **and sqrt-safety extraction**, then combined domain proof. |
| `CertificateSharp/Kernel/Prune.lean` | Operand dependency `[a]` for `.sqrt a`, step-congruence case and aligned sqrt-witness pruning. A bare “pass-through” is insufficient. |
| `Certificate/Tests/Ball.lean` (optional) | Current file contains concrete examples, not an exhaustive expression match. Existing examples can remain; new examples are optional. |

These are the landed paths proposed to change, not thirteen files each containing only one new match case. New structures/fields, helper lemmas and safety extraction are explicitly necessary. Existing sqrt-free expression semantics and old `NonvanishingOn` equations can remain unchanged, but exact reduction and old-certificate compatibility still require implementation checks. Shared-file ownership and the BALLFIX sequencing gate are now acknowledged. Production data use kernel proof declarations instead of `#eval`; that part of N5 is closed. No planned new file exceeds the cap; actual sizes/costs are still projections.

## F2 and F3 positive checks

**F2: PASS at design level.** For the witness checks in design §4.5, `0 ≤ d < s` and `‖W-s‖ ≤ d` imply `Re W ≥ s-d > 0`. On `Re f > 0`, `sqrtE f` is the principal root, squares to f, and has nonnegative real part. Thus `‖sqrtE f+W‖ ≥ Re(sqrtE f+W) ≥ s-d`, independent of the unknown approximation error. Factoring `f-W²` proves the stated ε/(s-d) bound. The old f=1,W=−1 counterexample fails the anchor check for **every** s>0, since `‖−1-s‖=1+s>s>d`. A uniform model sup bound matches `CertModel.Encloses` (`Model/Basic.lean:84–87`); no coefficient-norm estimate is being inferred from a pointwise estimate. `hdeg = 0` makes the witness model's normalization correct. Outward rounding and failed-check behavior still need the implementation and proof of `sqrtWitnessRadius`/`sqrtWitness_sound`; these are currently `sorry`.

**F3: PASS for the real maps, inverse and conjugacy; FAIL only for the new complex clock contract in finding 2.** Compared directly with `Rotated.lean:31–36,53–54` and the frozen real/complex vector fields: physical projection is `(Q₀+Q₁,P₀,Q₁)`, with P₀ = 1+c′+Y. Substitution into `P₀²/2−P₀+P₁+V` gives exactly `J̃+Y²/2−c′²/2+Xc″+V−1/2`.

The polar map satisfies `dY∧dX=dI∧dα`. For the centre shift, the mixed terms in `dP₀∧dQ₀` are `c′ dY∧dφ+c″ dφ∧dX`; those from `dP₁∧dφ` cancel them. Adding or dropping the φ-only shear −c′ preserves the two-form. With the actual frozen convention `X_H=(∂_I H,−∂_θ H)`, the resulting equations are `Xdot=Y`, `Ydot=−c″−Vq`, `φdot=1`; hence `qdot=1+c′+Y=p` and `pdot=−Vq`. The C³ premise suffices for the full derivative. Action recovery and the arg inverse use Ω>0 and positive action in their stated places. The complex centre derivatives have the correct 2π(k+1) factors and second-derivative minus sign. The all-z eval identity is algebraic and does not require `sqrtE²=z` on the cut; it is therefore a viable target as written.

## Delta signature ledger

All names have prefix `KAM.SpinOrbit.Lock`. Every row below corresponds to an added or statement-changed declaration. “PASS” evaluates the proposed contract, not its proof. Contract column gives design sections because SO blueprint labels/packets do not exist locally. Unchanged declarations (`IsSyncOrbit`, the choice definition, spec/unique, `libAction`, `LockBarrier`, confinement and the two scalar transfer helpers) are outside this delta re-audit.

| Declaration (signature line) | Contract | Verdict / reason |
|---|---|---|
| `lunarSyncOrbit_bound` (53) | §1.4, §2 | PASS; revised literals reachable, finding 3 proof-status note. |
| `lunarOmega` (64) | §1.4, §7 | PASS, provisional DATA; positive rational 8/65. |
| `lunar_sync_lock` (72) | §1.2, §1.4 | PASS, provisional DATA; literal changes consistent with transfer margins. |
| `lunar_sync_lock_nonvacuous` (82) | §1.2 | PASS; same zero-action argument with revised entry literal. |
| `sqrtE` (125) | §4.1 | PASS; total real-preserving definition, analytic only away from cut. |
| `sqrtE_ofReal` (128) | §4.1 | PASS; fixes the original reality counterexample. |
| `differentiableAt_sqrtE` (131) | §4.1 | PASS; eventual equality to cpow on open slit plane. |
| `sqrtE_sq` (134) | §4.1 | PASS; appropriately restricted to slit plane. |
| `sqrtE_re_nonneg` (136) | §4.1 | PASS; zero on cut, principal-root real part elsewhere. |
| `hasDerivAt_sqrtE` (139) | §4.4 | PASS; positive real part pays for analytic branch/nonzero root. |
| `sqrtE_ball` (144) | §4.3 | PASS; r<s² gives Re z>0; denominator ≥s. |
| `sqrtE_model_error` (149) | §4.5 | PASS; anchored denominator bound, no opposite root. |
| `SqrtWitness` (159) | §4.5 | PASS; untrusted data, inequalities checked by checker. |
| `sqrtWitnessRadius` (169) | §4.5 | PASS as specified checker interface; body pending. |
| `sqrtWitness_sound` (172) | §4.5 | PASS; lawful arithmetic, degree zero, strip sup enclosure. |
| `lockX` (185) | §3 | PASS; period-one sine and elliptic scaling. |
| `lockY` (188) | §3 | PASS; matching cosine/scaling. |
| `lockToRotR` (193) | §3 | PASS; physical momentum and clock-action correction. |
| `lockToPhysicalR` (201) | §3 | PASS; correct landed map direction/projection. |
| `lockHamiltonianR` (205) | §3 | PASS; exact algebraic pullback. |
| `lockToPhysicalR_eq` (209) | §3 | PASS; projection identity. |
| `libAction_lockToPhysicalR` (215) | §3 | PASS; includes Ω>0 and I≥0. |
| `lockToPhysicalR_surj` (221) | §3 | PASS; correct arg orientation, I>0 excludes origin. |
| `lock_conjugacy` (229) | §3 | PASS; C³, I>0, Ω>0 and frozen field convention. |
| `lockCentre` (235) | §3 | PASS; rational sine polynomial. |
| `lockCentreC` (239) | §3 | PASS; explicit complexification. |
| `lockCentreDC` (243) | §3 | PASS; first derivative factors. |
| `lockCentreDDC` (247) | §3 | PASS; second derivative sign/factors. |
| `lunarLockCentre` (252) | §7 | PASS as provisional numerical data, not a certified residual. |
| `lockCentre_contDiff` (254) | §3 | PASS; finite sine sum is smooth. |
| `lockToRotC` (258) | §3 | PASS; total definition; analytic region needs positive Ω. |
| `lockToRotC_ofReal` (267) | §3 | PASS; supplies Ω>0 and I>0. |
| `lockHamExpr` (275) | §3 | PASS as placeholder target; no existing constructor implementation. |
| `lockHamExpr_eval` (278) | §3 | PASS; algebraic all-carrier identity feasible after extension. |
| `lockHamExpr_clock` (282) | §3 | **FAIL**, finding 2. |
| `LockGraphCert` (294) | §1.5, §6 | PASS; explicit data wrapper, no assumed invariance. |
| `lockBarrier_of_certV2` (303) | §1.5, §6 | PASS as conditional contract; graph, positive action and Hamiltonian equality supplied. |
| `lockLiteralCheck` (317) | §1.4 | PASS as placeholder interface; body/soundness must enforce all transfer and positivity conditions. |
| `lunar_sync_lock_of_cert` (320) | §1.5, §6 | PASS as conditional contract, subject to specified literal-check soundness. |

N3 is closed: `DifferentiableAt.cpow_const` exists with the slit-plane premise and was checked by Lean. N4 is closed: the false uniqueness-without-oddness claim is deleted and the half-turn translate counterexample is now stated. N5 is partially closed as recorded in finding 5. Source/consumer readiness remains FAIL overall because of findings 1–2. Frozen-object use remains compatible: actual frozen field definitions were read, no replacements introduced, and the proposal's orbit-equation spelling is bridged by landed `soField_eq`. The draft's initial “frozen physical model” docstring is stale wording; no SO anchor has been frozen locally.

## Verification receipt and limits

The submitted signatures were copied byte-for-byte to `.drafts/scratch/SOLockSignaturesAudit2.lean` and elaborated **once**:

```text
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-lockdesign .drafts/scratch/SOLockSignaturesAudit2.lean
[sig-gate] slot 1 acquired 16:25:54
exit 0; 29 warnings: declaration uses `sorry`; no other diagnostics
original SHA256 = scratch SHA256 =
66199f977fc491c4d14e1b0d8f6977fc9c626b5d12fb52b9f95670484f13ddf8
```

Warning lines: 45,48,53,72,82,104,111,117,128,131,134,136,139,144,149,169,172,209,215,221,229,254,267,275,278,282,303,317,320. This includes the three placeholder definitions. The remaining theorem proofs are drafts using `sorryAx`; this run does not prove the new claims.

A separate scratch API/axiom probe, `.drafts/scratch/SOLockAudit2Probe.lean`, used the same wrapper, slot 1 at 16:27:52: exit 0, no warnings. It `#check`ed `DifferentiableAt.cpow_const`, `fderiv_zero_of_not_differentiableAt`, both reality theorems, and `HamExpr.nonvanishingOn_of_inv_good`, confirming the latter's exact missing-premise interface. `#print axioms` for landed `HamExpr.exists_real_eval`, `HamExpr.eval_real`, `soRotMap_symplectic`, `soField_eq`, and `checkTorusCertificateV2_sound` each returned exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The signature run, lint ABI attempt and API probe were serialized; no audit Lean processes overlapped. No heartbeat, recursion-depth or synthesis-budget override was used. No new production module exists to build; the prescribed scratch elaboration is the targeted Lean gate for this report-only audit.

`LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh` exited **1**:

```text
check_lean_modules: PASS (1628 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
.../.lake/abi-scratch/tmpsk6cfuzi.lean:1:0: error: unknown module prefix 'KAM'
No directory 'KAM' or file 'KAM.olean' in the search path entries:
.../KAM-inp-lockdesign/.lake/build/lib/lean
```

No other lint diagnostic appeared. As in round 1, this worktree lacks its own `.lake/build`; the prescribed signature wrapper uses the shared build instead. **Full lint/ABI validation did not pass.** No local build snapshot or generated root was created to conceal the failure.

`git diff --check 50807049 HEAD`: exit 0. `git diff --quiet 50807049 HEAD -- KAM manifest`: exit 0. Exact rational computations were read-only Python evaluations; the floating tube-margin diagnostics are explicitly provisional. Both auditor scratch files were deleted after validation. Final `git diff --check` passed; the sole retained worktree change is this report. Input hashes were rechecked at closeout.

No pinned-source erratum is alleged. Findings concern our own design/interface contracts and literal/proof-status wording. No novelty claim, numerical generator, actual checker extension, new proof, full SO blueprint, kernel data or unchanged round-1 proof argument was audited to completion. Closeout of this delta audit is complete as a **FAIL report**, with findings 1–2 unpaid and no silent repair.
