# LOCK-COORDS-R independent audit 1

**Overall verdict: PASS WITH NOTES for the real coordinate package.** The complete assigned real slice is present, its signed statements and literal definitions match the corrected design, and the conjugacy is to the actual physical `soField`. No frozen anchor is implemented or sealed by this package; “seal-ready” is inapplicable. The complex/HamExpr, certificate-to-barrier, data and headline assembly gates remain separate work.

Auditor: `maud-lockcoords-1`; 2026-10-30 UTC. Focused, tier-2, report-only audit. Authorization permits this exact report and temporary `.lake/abi-scratch/` probes, with serial, nice-priority Lean checks and `LEAN_NUM_THREADS=1`. No implementation repair, commit, merge, source regeneration or external write was performed.

## Inputs, scope and comparison

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, the original `PKG-LOCK-COORDS-R.md`, corrected SO-LOCK design §§1,3,6 and design audits 1–3. The literal contract is `/root/code/KAM-inp/.drafts/design/SOLockSignatures.lean` §§2,6, byte-identical to the lockdesign worktree copy. The local handoff is 59 lines and **contains no section or paragraph labelled AUDIT FOCUS**; its declared file/statement scope and the original package brief govern this audit. This documentation omission did not prevent verification.

Snapshot `frozen-v1`:

- HEAD: `60cd4c675db896464be3dd3941b999e90e31d5e5`.
- `inp` at audit entry: `98ced4ab75d556db5dcbac5d5850f9c293b07940`.
- Initial merge base: `1316016668e558526520a7820d3f6c94afaa2d96`.
- Initial full `git diff inp...HEAD`: seven new Lean files, 1303 insertions; SHA256 `729b62ed91292270ab047237ee89fdaab66f168c7cbcfdf75d6ee821bc38fdd3` (64672 bytes). The full diff was read, including merged PO/CONF code.
- Coordinate implementation: `c08ab7b2`; merge of PO/CONF: `268794c9`; ownership adjustment: HEAD. The coordinate change itself comprises Maps, Inverse and Conjugacy; the four other files are merged dependencies.

The shared `inp` ref advanced during this audit. At recheck it was `2807401d4af30e95cc55f907940684611e36c247`; `git merge-base --all inp HEAD` returned both `e780f59fb5d7808ab8713dfe2cf686264704815f` and the original merge base. Consequently a repeated `git diff inp...HEAD` warned “multiple merge bases” and selected the older PO branch base, showing 23 files including unrelated pre-existing BallRound/W/errata changes. The frozen original comparison above is the audit surface. This is a moving-ref/crisscross-merge limitation, not an auditor edit or a claim that the live three-dot diff contains only this package. In particular its apparent `KAM/Root/Certificate.lean` addition is inherited BallRound integration; the original frozen seven-file comparison contains no generated-file edit.

All locators below refer to frozen-v1. No `blueprint-SO/`, SO frozen package anchor, provider or source dependency graph was supplied. The corrected local design/signature contract is used; no I/N/P blueprint label or frozen theorem closure is invented. Frozen `KAM.hamiltonianVectorField` (`kam.hamiltonianVectorField.v1`, SEALED) was read directly: `(∂I H, −∂θ H)` for `Σ dI∧dθ`.

| File | SHA256 |
|---|---|
| `KAM/SpinOrbit/Lock/Coords/Maps.lean` | `2e83565278406d761d0f92e390bf8b66a53ea400169842d5c7abfd1bec223e00` |
| `KAM/SpinOrbit/Lock/Coords/Inverse.lean` | `2f8a737fb9e59e0042f0477f4948de2590064c46968e42524c0c5be401792358` |
| `KAM/SpinOrbit/Lock/Coords/Conjugacy.lean` | `37ba2364ca882d7c21029d5314425c858f5a1d814d55056e900aa2c2f3c67f51` |
| `KAM/SpinOrbit/Lock/Confine.lean` | `5653469d434a9fc42a5c84e5214e264439d365bd643f6ae266b363ce0cbc09d7` |
| `KAM/SpinOrbit/Lock/PO/Green.lean` | `a3046eb37afc076baa00c20aa6b11d6f9b827d03cd1a6768374dad2eaa043efd` |
| `KAM/SpinOrbit/Lock/PO/Contraction.lean` | `b9a429bc2832196d83bbd006bdd829348b8978647ed30e2ff4c049f5042a6be4` |
| `KAM/SpinOrbit/Lock/PO/Orbit.lean` | `9d60c414f08692c57dd4c904685181d13c2480b74ce8249907db3883599e9b71` |
| `/root/code/KAM-inp/.drafts/design/SOLockSignatures.lean` | `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d` |
| `/root/code/KAM-inp-lockdesign/docs/tracks/SO/design/SO-LOCK-DESIGN.md` | `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d` |
| `docs/tracks/SO/audits/LOCK-COORDS-R-handoff.md` | `5a9faecfba9fdedcdd1c1aa2ac8b7c66b251776b5efe04e2d4b23b4523ff21a2` |

## Declaration ledger

All declarations below are in `KAM.SpinOrbit.Lock`. “PASS/helper” certifies the distinct helper statement, not a replacement of a signed result. Five theorem headers and seven definition headers match the signature file modulo whitespace, including binder names, order, explicitness, carriers and conclusions. All seven definition bodies also match modulo whitespace. Fresh copies of the five signed theorem types were inhabited by their actual exports, with explicit arguments in declaration order; all seven independently compared literal definitions were checked by `rfl`. The shared `libAction` definition received its own literal-equation probe.

| Design node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| §3; Maps:33 | `lockX` | PASS | Signed real sine polar piece. |
| §3; Maps:37 | `lockY` | PASS | Signed real cosine polar piece. |
| §3; Maps:42 | `lockToRotR` | PASS | Includes `P₀=1+c′+Y` and exact clock-action shear. |
| §3; Maps:50 | `lockToPhysicalR` | PASS | Physical `(q,p,φ)` in rotated→physical direction. |
| §3; Maps:54 | `lockHamiltonianR` | PASS | Exact `J̃+Y²/2−c′²/2+Xc″+V−1/2`. |
| §3; Maps:58 | `lockToPhysicalR_eq` | PASS | Signed projection identity, no domain premise. |
| §3; Maps:68 | `lockHamiltonianR_eq` | PASS/helper | Actual real rotated Hamiltonian composition, all Ω,c,z. |
| §1.4/§3; Maps:79 | `lockCentre` | PASS | Exact finite rational sine polynomial. |
| §1.4; Maps:84 | `lunarLockCentre` | PASS | All three rational coefficients match. |
| §3; Maps:86 | `contDiff_list_sum_map` | PASS/helper | General finite smooth sum; no assumptions on result. |
| §3; Maps:92 | `lockCentre_contDiff` | PASS | Full `ContDiff ℝ ⊤`, including empty coefficient list. |
| §3; Inverse:28 | `libAction_lockToPhysicalR` | PASS | Includes `I=0`; requires only Ω>0 and I≥0. |
| §3; Inverse:49 | `lockToPhysicalR_surj` | PASS | Exact explicit preimage on positive action; J̃=0 is legitimate. |
| §3; Conjugacy:38 | `lockXα` | PASS/helper | Literal α-partial coefficient. |
| §3; Conjugacy:42 | `lockXI` | PASS/helper | Literal I-partial coefficient, used only at I>0. |
| §3; Conjugacy:46 | `lockYα` | PASS/helper | Literal α-partial coefficient. |
| §3; Conjugacy:50 | `lockYI` | PASS/helper | Literal I-partial coefficient, used only at I>0. |
| §3; Conjugacy:53 | `hasDerivAt_lockX_line` | PASS/helper | Both varying α and I differentiated. |
| §3; Conjugacy:63 | `hasDerivAt_lockY_line` | PASS/helper | Both varying α and I differentiated. |
| §3; Conjugacy:74 | `lockX_lockY_bracket` | PASS/helper | `Xα YI−XI Yα=1`, correct orientation and period-one factors. |
| §3; Conjugacy:96 | `hasDerivAt_lockHamiltonianR_line` | PASS/helper | All terms differentiated, including c‴ and both potential partials. |
| §3; Conjugacy:125 | `hasDerivAt_lockToPhysicalR_line` | PASS/helper | Exact three-component directional differential. |
| §3; Conjugacy:141 | `differentiableAt_lockHamiltonianR` | PASS/helper | Genuine Fréchet differentiability; no reliance on total-fderiv fallback. |
| §3; Conjugacy:151 | `differentiableAt_lockToPhysicalR` | PASS/helper | Genuine Fréchet differentiability at positive I. |
| §3; Conjugacy:161 | `lock_conjugacy` | PASS | Exact signed theorem for arbitrary C³ centre and I>0. |
| §2 of signatures; Confine:40 | `libAction` | PASS/dependency | Single shared definition; matches intended elliptic action. |

## Binder and premise audit

Here SOURCE refers to the exact corrected design/signature contract. Types `Fin 2 → ℝ`, products and real functions retain the prescribed carriers. No additional typeclass or bundled logical premise appears in the signed coordinate theorems. Each row below is one binder, in outer-to-inner order. Totals: SOURCE 7, TYPING 13, STANDING 0, RULED 0, EXCESS 0.

| Theorem | Binder | Bin | Authority |
|---|---|---|---|
| `lockToPhysicalR_eq` | Ω : ℝ | TYPING | signatures §6 |
| same | c : ℝ→ℝ | TYPING | signatures §6 |
| same | z : (Fin 2→ℝ)×(Fin 2→ℝ) | TYPING | signatures §6 |
| `libAction_lockToPhysicalR` | implicit Ω : ℝ | TYPING | signatures §6 |
| same | hΩ : 0<Ω | SOURCE | design §3 positive Ω |
| same | c : ℝ→ℝ | TYPING | signatures §6 |
| same | z : phase point | TYPING | signatures §6 |
| same | hI : 0≤z.2 0 | SOURCE | design §3 action identity includes zero |
| `lockToPhysicalR_surj` | implicit Ω : ℝ | TYPING | signatures §6 |
| same | hΩ : 0<Ω | SOURCE | design §3 positive Ω |
| same | c : ℝ→ℝ | TYPING | signatures §6 |
| same | x : ℝ×ℝ×ℝ | TYPING | signatures §6 physical carrier |
| same | hx : 0<libAction Ω c x | SOURCE | design §3 punctured plane |
| `lock_conjugacy` | implicit Ω : ℝ | TYPING | signatures §6 |
| same | hΩ : 0<Ω | SOURCE | design §3 positive Ω |
| same | c : ℝ→ℝ | TYPING | signatures §6 arbitrary centre |
| same | hc : ContDiff ℝ 3 c | SOURCE | design §3 explicit C³ contract |
| same | z : phase point | TYPING | signatures §6 |
| same | hI : 0<z.2 0 | SOURCE | design §3 nonsingular annulus |
| `lockCentre_contDiff` | cs : List ℚ | TYPING | signatures §6 |

The additional differential helpers have distinct names and explicit calculus premises: Ω,c,z,v are typing data; positive Ω/I are domain premises; `hd0`, `hd1`, `hd2` mean differentiability of c,c′,c″. These are *conditional calculus helpers*, not additional premises of `lock_conjugacy`: its proof derives all three from the signed C³ premise at Conjugacy:166–169. The bracket helper assumes no bracket or conjugacy. The finite-sum helper assumes smoothness of each summand; `lockCentre_contDiff` supplies it for each explicit sine mode. Both algebraic map identities are unconditional. No coefficient estimate, source result, unknown invariant barrier or downstream certificate is assumed by any coordinate result.

## Definition classification

- `lockX`, `lockY`, `lockToRotR`, `lockToPhysicalR`, `lockHamiltonianR`: literal all-carrier formulas from the corrected design, with no invented branch. `Real.sqrt`, division and `deriv` have Lean's total semantics, as explicitly intended by design §3 (“the definitions are total”). The action theorem restricts to I≥0, and differential/conjugacy theorems restrict to I>0 and Ω>0; they do not pretend to give a polar chart at a singular radius.
- `lockCentre`: literal finite sum. `getD k 0` is read only at `k∈List.range cs.length`, hence within bounds; the default is not a missing-mode workaround. The empty list defines zero as intended.
- `lunarLockCentre`: literal rational data, no choice or fallback.
- `lockXα`, `lockXI`, `lockYα`, `lockYI`: literal coefficient formulas for the displayed partial derivatives. Their differential uses carry the stated positive-action domain; no global differentiability at I=0 is claimed.
- Shared `libAction`: literal `π(ΩX²+Y²/Ω)`, defined in Confine and imported only where required. No competing copy remains in Maps.

For all twelve definitions just listed (eleven coordinate definitions and shared libAction): `BODY_MATCH: OK`; `PUBLIC_CARRIER: OK`; `WELL_DEFINEDNESS: N/A_LITERAL`; `CHARACTERIZATION: N/A_LITERAL`; `CHOICE_INDEPENDENCE: N/A`; `DEFINITION_VERDICT: PASS`. The four coefficient definitions are exported without `@[expose]`; external consumers use their public differential/bracket theorems, and no cross-module unfolding of those bodies is needed by the signed slice. Maps' meaning-carrying definitions are exposed.

Merged dependency definitions were also inspected: `lockW`, `LockBarrier.barrierValue` and `lockRegion` are literal formulas; `LockBarrier` is the explicitly conditional design certificate, including its invariance field, not a replacement for LOCK-GRAPH. `lockPrim`, `greenD`, `green` are literal integral formulas; `soLip`, `soEta`, `syncForce`, `poSet`, `IsSyncOrbit` are literal constants/functions/predicates. `syncMap` and `toPoSet` bundle explicitly proved bounds and symmetry. `syncFixed` uses Mathlib's proved contraction theorem. `lunarSyncOrbit` has the signed conditional-choice spelling, but `exists_isSyncOrbit` proves its condition unconditionally, `lunarSyncOrbit_spec` proves the property, and `lunarSyncOrbit_unique` proves uniqueness; its zero branch is unreachable, not unpaid off-source semantics. These inherited objects are not used to hide a premise of the coordinate proofs.

## Refute-first semantic and consumer checks

1. **Frame direction / missing translation (old F3).** Reconstructed from Rotated:31–36 and Hamiltonian:62–67: physical q=Q₀+Q₁, p=P₀ and clock action J=P₁−P₀. Maps includes P₀=1+c′+Y. Substituting yields the stated K including −1/2. Besides `lockHamiltonianR_eq`, the fresh probe proves K equals the actual `soHR` at these physical four-dimensional coordinates. The omitted P₀ translation and inverse-map direction from the old design do not recur.
2. **Two-form sign and 2π.** Independently differentiate X=A sin(2πα), Y=B cos(2πα), B=ΩA, A²=I/(πΩ). The bracket is `(AΩ/(2πB))·2π cos²+(B/(2πΩA))·2π sin²=1`. The formal bracket proof establishes B=ΩA from positive square roots, then uses sin²+cos²=1. Thus dY∧dX=dI∧dα agrees with the frozen vector field.
3. **Boundary and inverse.** The action identity handles I=0 by squared-root identities under I≥0. For the inverse, w=Y/√Ω+i√ΩX and `libAction=π‖w‖²`; positive action proves w≠0 before using `cos_arg`. The principal argument only selects a preimage; no globally continuous angle inverse is claimed. The free clock action is ignored by the physical projection, so choosing J̃=0 loses nothing in this surjectivity statement.
4. **Avoiding the total-fderiv trap.** Conjugacy:141–158 proves actual differentiability, using the positive radicands. Conjugacy:166–178 obtains c,c′,c″ differentiability from C³ and equates line derivatives to Fréchet differentials via `soHasDerivAt_line`. Both α and I partials are present. Evaluating the frozen X_K gives φdot=1, qdot=Y·bracket+1+c′=p and pdot=c″−(c″+Vq)·bracket=−Vq. The last algebra is checked by Lean, not an assumed field identity.
5. **Consumer strength.** A fresh chain-rule probe takes an arbitrary curve u with `HasDerivAt u (X_K(u t)) t` and positive action and proves `HasDerivAt (Φ∘u) (soField(Φ(u t))) t` using the actual exported differentiability and conjugacy theorems. This checks pointwise physical solution transport with no orbit or periodic-centre premise. In LOCK-GRAPH the certificate is for κK, so its torus frequency must first become `(sinf/κ) • ωstar`, as corrected in design §3 and audit-2 finding 4. This package gives precisely the unscaled K→soField bridge; it does not supply clock rigidity, graph construction, time-unscaling, or the final certificate.

No mathematical mismatch survived these adversarial checks. There is no asserted new pinned-source defect. Prior F3 is resolved for this real slice; complex clock/domain issues belong to LOCK-COORDS-C/SQRT and are not silently declared solved here.

## Verification receipts

All Lean/Lake/checker/ABI runs were serial, with `LEAN_NUM_THREADS=1`; direct invocations used `nice -n 5`, and gated builds use it inside the wrapper. No heartbeat, recursion or synthesis override was used.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-lockcoords KAM.SpinOrbit.Lock.Coords.Maps
Build completed successfully (2913 jobs). exit 0

[same gated command, target KAM.SpinOrbit.Lock.Coords.Inverse]
Build completed successfully (2958 jobs). exit 0

[same gated command, target KAM.SpinOrbit.Lock.Coords.Conjugacy]
Build completed successfully (2914 jobs). exit 0

[same gated command, target KAM.SpinOrbit.Lock.PO.Orbit]
Built KAM.SpinOrbit.Lock.PO.Green (33s)
Built KAM.SpinOrbit.Lock.PO.Contraction (6.2s)
Built KAM.SpinOrbit.Lock.PO.Orbit (7.2s)
Build completed successfully (2893 jobs). exit 0
```

The first three builds replayed the existing Expr.Basic:85 unused `hS` warning; Inverse and Orbit replayed the existing ODE.Exit:36 unused `NormedSpace ℝ E` warning. No warning is in any of the seven new files. “Jobs” above is Lake's total dependency accounting, not a clean-library rebuild. No clean/update/cache operation or package source change was performed.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/LockCoordsAudit1.lean
exit 0; no diagnostics; 72 public-theorem axiom outputs
```

The probe copies the five signed theorem headers verbatim, replacing each proof with `exact <export> <explicit binders in order>`, compares the seven signed definition literals by definitional equality, checks the shared action literal, and adds the two composition probes described above. An initial auditor-only curve probe used the nonexistent convenience projection `hc.differentiable_deriv`; that probe exited 1 at scratch line 103. Replacing it with `contDiff_succ_iff_deriv` followed by differentiability produced the clean successful run above. No production source change was needed, and the error is not a package finding.

The successful probe printed all 14 public coordinate theorems and all 58 public theorems in the merged dependency files. Every one returned exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or other axiom occurred. Coordinate outputs:

```text
'KAM.SpinOrbit.Lock.lockToPhysicalR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockHamiltonianR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.contDiff_list_sum_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockCentre_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.libAction_lockToPhysicalR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockToPhysicalR_surj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockX_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockY_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lockX_lockY_bracket' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockHamiltonianR_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.hasDerivAt_lockToPhysicalR_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.differentiableAt_lockHamiltonianR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.differentiableAt_lockToPhysicalR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.Lock.lock_conjugacy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.SpinOrbit.Lock.Coords.Maps KAM.SpinOrbit.Lock.Coords.Inverse \
  KAM.SpinOrbit.Lock.Coords.Conjugacy KAM.SpinOrbit.Lock.Confine \
  KAM.SpinOrbit.Lock.PO.Green KAM.SpinOrbit.Lock.PO.Contraction KAM.SpinOrbit.Lock.PO.Orbit
replaying KAM.SpinOrbit.Lock.PO.Orbit
replaying KAM.SpinOrbit.Lock.PO.Contraction
replaying KAM.SpinOrbit.Lock.PO.Green
replaying KAM.SpinOrbit.Lock.Confine
replaying KAM.SpinOrbit.Lock.Coords.Conjugacy
replaying KAM.SpinOrbit.Lock.Coords.Inverse
replaying KAM.SpinOrbit.Lock.Coords.Maps
exit 0
```

LINT_RECEIPT_PENDING

SHADOW_RECEIPT_PENDING

Source and comparison checks:

```text
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-lockcoords KAM.SpinOrbit.Lock.Coords.Maps \
  KAM.SpinOrbit.Lock.Coords.Inverse KAM.SpinOrbit.Lock.Coords.Conjugacy
short-name check OK (no reused public short name); exit 0

cmp /root/code/KAM-inp/.drafts/design/SOLockSignatures.lean \
  /root/code/KAM-inp-lockdesign/.drafts/design/SOLockSignatures.lean
exit 0; no output

git diff 98ced4ab75d556db5dcbac5d5850f9c293b07940...HEAD \
  -- KAM/Frozen manifest KAM.lean KAM/Root README.md
exit 0; empty

git diff --check 98ced4ab75d556db5dcbac5d5850f9c293b07940...HEAD
exit 0; empty
```

No forbidden proof escape, resource override, `EuclideanSpace` or `native_decide` occurs in the seven-file delta. All files have the required copyright/module/import/docstring/public-section form. Line counts / maximum Unicode line lengths: Maps 98/97, Inverse 96/96, Conjugacy 186/99, Confine 228/100, Green 249/99, Contraction 226/99, Orbit 220/96. No source file approaches 1500 lines.

## Notes, deviations and remaining gates

- The expected stale generated root is a permitted lint note under the audit brief. Its regeneration belongs to landing; it was not attempted here.
- The handoff documents the ownership ruling assigning `libAction` to LOCK-CONF. Inverse therefore imports Confine; Maps and Conjugacy do not. This adds the explicit dependency missing from the older package-table shorthand “Model, Rotated”; Confine imports no coordinate module, so there is no cycle or duplicate definition.
- The missing handoff AUDIT FOCUS label and moving `inp` ref are documented scope/provenance notes. Neither changes the pinned coordinate statements.
- This is a package audit against the corrected local design, not an external Celletti literature audit, an SO graph audit, a new frozen-anchor seal, or proof of the lunar headline. Certificate/HamExpr linkage and physical-time unscaling remain consumer obligations outside this real package.
- No implementation deviation or suspected external pinned-source erratum was introduced by the auditor. Only this report is retained; all auditor scratch files are removed before the READY marker.

FINAL_CLOSEOUT_PENDING
