# LOCK-SQRT independent package audit 1

**Overall: FAIL the literal landed-statement preservation contract. Mathematical/checker soundness: PASS on this audited slice; the only lint failure is the explicitly allowed stale generated root.** Four existing handwritten test theorems change elaborated type in addition to the explicitly permitted helper replacement. This is a certificate-format migration, not a false theorem or an added analytic hypothesis, but the implementation brief does not grant that additional statement exception and the handoff expressly claims it did not occur. No implementation repair or permission request is part of this audit.

Auditor: `maud-locksqrt-1`, 2026-10-30 UTC. Tier 2, single-auditor refute-first source/type/proof review. No subagents. The user's exact worktree destination overrides the generic brief's main-worktree destination. Only this report is retained; temporary probes/logs are confined to worktree `.lake/abi-scratch/` and removed after their evidence is recorded.

## Scope, authority, and immutable inputs

- HEAD: `a12b69cb0f35e3e57fa76f5b793c44269f855f68` (`LOCK-SQRT: trusted primitive HamExpr.sqrt (D45)`).
- `inp`: `a5f010ebcb430f2c7a9b15726507db29321760eb`; merge base: `1316016668e558526520a7820d3f6c94afaa2d96`.
- Reviewed the complete `git diff inp...HEAD`: 24 files, 1231 insertions, 62 deletions; 22 Lean files and two Python emitters.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (especially D45), `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, and `/root/code/KAM-inp/.drafts/briefs/lock/PKG-LOCK-SQRT.md`.
- The supplied handoff contains no literal `AUDIT FOCUS` heading. Its complete contract/ABI claims, deviations and final namespace ruling, together with design §4.1–4.6, define the focus.
- Design: `/root/code/KAM-inp-lockdesign/docs/tracks/SO/design/SO-LOCK-DESIGN.md`, revision 3, SHA256 `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d`.
- Signatures: `/root/code/KAM-inp-lockdesign/.drafts/design/SOLockSignatures.lean`, §5:121–179, SHA256 `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d`. Verified byte identity with the copy in `/root/code/KAM-inp/.drafts/design/` and the canonical design copy in `/root/code/KAM/`.
- Read design audit 3 for the helper exception and its retained limitations. No SO blueprint/frozen theorem anchor is assigned to this checker package. Thus provider/frozen-type equality and a seal-body assembly test are **not applicable**; no I/N/P theorem is certified seal-ready here. Design §4 and signed checker contracts replace the generic blueprint-node authority for this slice. Frozen `KAM.complexStrip` and actual `CertModel.Encloses`, arithmetic-law interface, and downstream Hamiltonian consumers were inspected.

The authorized envelope is report-only inspection, scratch probes, targeted builds and kernel replay; no state-changing Git, source repair, root regeneration or frozen edit. The one temporary log mistakenly redirected to the base checkout during an initial failed probe launch was removed immediately; no source there was changed. Corrected base probes lived in this worktree and read base oleans via its `lake env`.

## Finding F1: additional handwritten statement changes (contract / evidence failure)

**Verdict: survives refutation; FAIL exact ABI preservation.**

Authority: implementation brief, Contract: “you may change exactly ONE landed statement”; “Every other landed declaration keeps its exact statement”. Handoff, Contract / ABI check: “No hand-written theorem or definition changed type” and the test modules are explicitly included in its claimed comparison.

At this HEAD the following handwritten statements in `KAM/Certificate/Tests/Compose.lean` add the fourth constructor argument `[] : List (ℕ × SqrtWitness ℚ)` inside their propositions:

| Declaration | HEAD line | Full elaborated difference | Verdict |
|---|---:|---|---|
| `KAM.Certificate.composeTest_noChar` | 116 | `Witnesses.mk exp inv []` becomes `Witnesses.mk exp inv [] []` | FAIL literal contract |
| `KAM.Certificate.composeTest_noExp` | 121 | `Witnesses.mk [] inv chars` becomes `Witnesses.mk [] inv chars []` | FAIL literal contract |
| `KAM.Certificate.composeTest_noInv` | 126 | `Witnesses.mk exp [] chars` becomes `Witnesses.mk exp [] chars []` | FAIL literal contract |
| `KAM.Certificate.composeTest_n2` | 153 | Its literal `Witnesses.mk [] [] chars` gains a fourth `[]` | FAIL literal contract |

**Independent reproduction/refutation:** generated `#check @name` for every source-declared existing public theorem/definition/structure/inductive in all 16 modified landed Lean files, importing those modules on both actual `inp` and this HEAD. Used `set_option pp.all true` and `set_option pp.oneline false`; both corrected probes exit 0. Compared the complete, unabridged outputs. Of 392 baseline declarations: 391 remain; 387 are byte-identical after stripping outer whitespace, four differ exactly as above; the old helper is removed and the new helper added. Separate extraction of the four raw source headers before `:= by` confirms the differences independently of the pretty printer. These four names are not generated recursors or equations. Initial `pp.oneline true` output abbreviated types as `[...]` and misleadingly hid the changes; it was discarded and rerun unabridged. The final comparison contains no such abbreviation.

**Attempt to disprove the finding:** the extra field is an allowed data-language extension, and these are sqrt-free tests with the empty list. Thus their intended mathematics and truth value are preserved, and retaining the old anonymous literals would fail to elaborate. This explains and limits the migration; it does not make a handwritten proposition containing a new constructor argument literally identical, nor authorize an unstated extra exception. This finding is about exact interface/evidence compliance, not a soundness counterexample. Correct the ABI receipt and obtain an explicit disposition permitting the four test-statement migrations (or supply a contract-compliant alternative) before marking the package unconditionally accepted. No implementation change was made by this auditor.

## Mathematical review and refutation results

1. **Total semantics (§4.1): PASS.** `sqrtE` is exactly the signed total function: zero on the closed nonpositive real axis, complex power elsewhere. The apparent off-slit fallback is explicitly intended source semantics, not hidden junk. `sqrtE_eq_exp`/eventual equality give holomorphy on the slit plane. Squaring is claimed only there. `sqrtE_re_nonneg` holds everywhere, and `sqrtE_ofReal` proves real-valuedness for every real input. `exists_real_eval` gains its induction case; `eval_real` retains its proof. No unconditional square-back claim is smuggled in.
2. **Domain extraction (§4.2): PASS.** `NonvanishingOn (.sqrt a)` is exactly operand safety plus positive real part. `SlpInvGood` is unchanged; new `SlpSqrtGood` quantifies over every actual sqrt instruction and its operand value in the full program. Ordinary and trig prefix lemmas reject invalid/forward/self references through the impossible default-ball inequality `0 < 0`. Enclosure plus `r < re c` establishes operand positivity on the entire `certDomain`. The combined helper first obtains operand safety by induction, then identifies its compiled slot using prefix preservation and operand compiler soundness. It does not use the parent sqrt's differentiability circularly. Both balls consumers supply the added predicate from their own successful pass.
3. **Ball rule (§4.3): PASS.** `sqrtE_ball` derives positive radicand real part from `‖z-s²‖ ≤ r < s²`, then uses factorization and `re sqrtE ≥ 0`. `ballSqrt` checks `r < re c`, computes a rational anchor, bounds the centre error by `|re c-s²|+|im c|`, checks positive anchor and `R < s²`, and applies outward `ballRound`. Newton accuracy is not a premise of soundness. Bad anchors or near-cut balls may reject a valid mathematical input, but cannot certify an invalid enclosure. Negative radii cannot give a counterexample to `ballSqrt_sound`, since its membership premise would then be impossible.
4. **Jets (§4.4): PASS.** First, second and third directional derivatives have coefficients `1/2`, `-1/4`, `3/8`, with all three mixed second-times-first terms present. The inverse-root calculus is derived from the first derivative and previously proved inverse/product rules on an open domain. `slpSqrtPre` preserves the value everywhere, including off the analytic domain; only derivative tables require positive real part. The node emits the original sqrt instruction before reciprocal powers; the prefix theorem lets safety extraction find it. `slpCompile_sound` composes the actual operand result into `slpSqrtNode_sound`. The all-real `Fin n` product carriers and derivative ordering agree with the existing jet bridges.
5. **Witness (§4.5): PASS.** `sqrtWitness_sound` is universal over certificate-supplied polynomial, positive anchor/margin, backend and model configuration. It assumes the produced operand enclosure and zero model degree, as signed, and successful checking. It proves radicand positivity and a uniform strip enclosure. The checker verifies `0 ≤ d < s`, `supBound(W-s) ≤ d`, and `supBound(g-s²) < s²`, then computes the residual bound with all model errors. `re W ≥ s-d > 0` and `re sqrtE ≥ 0` bound the denominator; `g-W² = (sqrtE g-W)(sqrtE g+W)` pays the error. Downward-rounded guards and upward-rounded radius multiplication have the correct direction. The previous opposite-root counterexample fails the anchor guard. No advice, Newton convergence or branch choice is trusted.
6. **Composition/pruning (§4.6): PASS.** `toDeg ... 0` supplies the signed degree premise. The composer selects the first witness keyed by the actual output slot, runs the checker, and uses its enclosure conclusion. Missing/wrong-key witnesses return `none`. Pruning preserves slot numbers, so copying the keyed list preserves alignment; dead sqrt witnesses are unread. `opDeps (.sqrt a) = [a]` makes retained roots retain their dependencies. The existing general congruence and `composePruned_sound` proofs cover the new constructor after recompilation. Product advice key `[3]` is re-keyed through `forWitness 3 slot`; unsuitable advice uses the existing checked fallback.
7. **Consumers: PASS (scoped).** Exact full type comparison preserves production `nonvanishingOn_of_balls`, `nonvanishingOn_of_ballsTrig`, `contDiffOn_eval`, `exists_real_eval`, `slpCompile_sound`, `Slp.compose_sound`, `composePruned_sound` and all other compared production interfaces. `Sound/Ham.lean` and the V2 engine are unchanged by the requested diff. Actual `checkHamBounds_sound` obtains operand safety from balls, derivative bounds from the jet bridges, and `ham_structural` uses the extended predicate. No output frequency, lunar-coordinate identity, LOCK-GEN certificate, barrier, or final confinement theorem is established by this package audit.

## Definition classification

All new definitions/structures are classified individually in the declaration ledger below. The principal classes are:

- Literal total semantic function: `sqrtE`; BODY_MATCH OK, PUBLIC_CARRIER OK, WELL_DEFINEDNESS/CHARACTERIZATION N/A_LITERAL, CHOICE_INDEPENDENCE N/A, DEFINITION_VERDICT PASS.
- Literal safety predicate: `SlpSqrtGood`; exactly design §4.2, not a conclusion-shaped substitute for a source theorem.
- Finite computational helpers: `sqrtNewton`, `sqrtAnchor`, `ballSqrt`, `slpSqrtD3`, `slpSqrtTail`, `slpSqrtPre`, `slpSqrtNode`. All are total finite algorithms; soundness uses checked conditions rather than guessed approximation accuracy.
- Certificate data and model constructions: `SqrtWitness`, its `.model`, `sqrtAnchorDiff`, `sqrtRadicandDiff`, `sqrtResidual`, `sqrtWitnessRadius`. The structure has only polynomial/anchor/margin data, no proof field. Model operations retain existing uniform-strip meaning; zero degree is explicit. Checker `none` is a documented rejection, not a fabricated mathematical value.
- The 13 new concrete test definitions are finite rational fixtures/programs, not public mathematical choice constructions.

For these finite literal/computational definitions: BODY_MATCH OK, PUBLIC_CARRIER OK, WELL_DEFINEDNESS N/A_LITERAL, CHARACTERIZATION N/A_LITERAL, CHOICE_INDEPENDENCE N/A, DEFINITION_VERDICT PASS. No new `Classical.choose`-defined object or characterization-defined mathematical object occurs. Extended landed definitions have exactly their disclosed new constructor/field/match arms; the original sqrt-free equations remain intact.

## Signed theorem binder audit

The eight signed theorem headers were copied from §5, changing only the allowed checker namespace/references, and elaborated against the implementations with no extra premises. `sqrtE` was additionally checked against its literal defining equation by `rfl`; `SqrtWitness` fields agree with the signed structure. Types use the signed open complex strip and uniform norm. Classification below is per binder, including implicit typing data; repeated binders are listed within each declaration. No widening of constant dependence occurs.

| Signed declaration | Binder | Bin | Authority |
|---|---|---|---|
| `sqrtE_ofReal` | `x` | TYPING | Signatures §5, exact corresponding header |
| `differentiableAt_sqrtE` | `z` | TYPING | Signatures §5, exact corresponding header |
| `differentiableAt_sqrtE` | `hz` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_sq` | `z` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_sq` | `hz` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_re_nonneg` | `z` | TYPING | Signatures §5, exact corresponding header |
| `hasDerivAt_sqrtE` | `z` | TYPING | Signatures §5, exact corresponding header |
| `hasDerivAt_sqrtE` | `hz` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_ball` | `z` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_ball` | `s` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_ball` | `r` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_ball` | `hs` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_ball` | `hr` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_ball` | `h` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `f` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `W` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `s` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `d` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `ε` | TYPING | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `hs` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `hd` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `hds` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `hf` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `hW` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtE_model_error` | `hres` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `α` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `[CertArith α]` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `n` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `W` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `s` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `N` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `cfg` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `g` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `gf` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `S` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `r` | TYPING | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `hW` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `hg` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `hdeg` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `hS` | SOURCE | Signatures §5, exact corresponding header |
| `sqrtWitness_sound` | `[LawfulCertArith α].val_ofInt` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].ofRatUp_ge` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].ofRatDown_le` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].add_err` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].val_neg` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].mul_err` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].val_abs` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].upAdd_ge` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].upMul_ge` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].ble_sound` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].blt_sound` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |
| `sqrtWitness_sound` | `[LawfulCertArith α].beq_sound` | STANDING | Signed backend law class; `Arith/Interface.lean:49–66` |

Counts: SOURCE 16, STANDING 12, TYPING 24, RULED 0, EXCESS 0. The namespace relocation is the handoff’s supplied `kam-inp-24` ruling, not an extra theorem hypothesis. `hg` expands to the pointwise degree-scaled strip enclosure in `Model/Basic.lean:84–87`; `hW` is the signed successful weight check, `hdeg` its signed zero-degree condition, and `hS` the actual checker success equation. Every `LawfulCertArith` field is a general backend arithmetic/comparison law, not the square-root conclusion. Auxiliary conditional node/table lemmas carry explicitly realized input slots as local compiler invariants; the public compiler supplies them rather than exporting them as new certificate premises.

## Declaration ledger

One row per source-declared public declaration across all changed Lean files (477 total; generated recursors/equation compiler declarations are not counted). Fully qualified names distinguish namespaced methods. `PASS retained type` means the unabridged base/HEAD comparison passes; semantic extensions/proof edits are covered above. The 86 new declarations comprise 58 theorems and 28 definitions/structures. F1's four rows fail only the literal preservation requirement. Source locations below are at the pinned HEAD.

| Contract/node | Declaration | Location | Verdict | Reason / classification |
|---|---|---|---|---|
| §4.2–4.6 | `KAM.Certificate.cexpHalvings` | `KAM/Certificate/Expr/Ball.lean:45` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.certCExpSmall_reduced` | `KAM/Certificate/Expr/Ball.lean:48` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.certCExpReduced_cexpHalvings_isSome` | `KAM/Certificate/Expr/Ball.lean:60` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballPiLo` | `KAM/Certificate/Expr/Ball.lean:81` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballPiHi` | `KAM/Certificate/Expr/Ball.lean:84` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ball_two_pi_zpow_mem` | `KAM/Certificate/Expr/Ball.lean:86` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.constBall` | `KAM/Certificate/Expr/Ball.lean:103` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.mem_constBall` | `KAM/Certificate/Expr/Ball.lean:107` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.inv_ball_bound` | `KAM/Certificate/Expr/Ball.lean:130` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballZero` | `KAM/Certificate/Expr/Ball.lean:160` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballOf` | `KAM/Certificate/Expr/Ball.lean:163` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStepG` | `KAM/Certificate/Expr/Ball.lean:169` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballForce` | `KAM/Certificate/Expr/Ball.lean:205` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStep` | `KAM/Certificate/Expr/Ball.lean:211` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.revGet` | `KAM/Certificate/Expr/Ball.lean:217` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsRev` | `KAM/Certificate/Expr/Ball.lean:223` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsAux` | `KAM/Certificate/Expr/Ball.lean:233` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.balls` | `KAM/Certificate/Expr/Ball.lean:245` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsSpec` | `KAM/Certificate/Expr/Ball.lean:250` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.revGet_reverse` | `KAM/Certificate/Expr/Ball.lean:257` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsRev_eq` | `KAM/Certificate/Expr/Ball.lean:269` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsAux_eq_spec` | `KAM/Certificate/Expr/Ball.lean:290` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.BallRel` | `KAM/Certificate/Expr/Ball.lean:298` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.toC_zero_rat` | `KAM/Certificate/Expr/Ball.lean:302` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.toC_ratCast` | `KAM/Certificate/Expr/Ball.lean:305` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballZero_mem` | `KAM/Certificate/Expr/Ball.lean:308` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.BallRel.ballRel_nil` | `KAM/Certificate/Expr/Ball.lean:313` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.BallRel.ballRel_snoc` | `KAM/Certificate/Expr/Ball.lean:315` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballForce_eq_some` | `KAM/Certificate/Expr/Ball.lean:333` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballForce_some` | `KAM/Certificate/Expr/Ball.lean:343` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStep_char` | `KAM/Certificate/Expr/Ball.lean:351` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStepG_sound` | `KAM/Certificate/Expr/Ball.lean:358` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStep_sound` | `KAM/Certificate/Expr/Ball.lean:459` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsSpec_sound` | `KAM/Certificate/Expr/Ball.lean:467` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsAux_sound` | `KAM/Certificate/Expr/Ball.lean:485` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.val_mem_ball` | `KAM/Certificate/Expr/Ball.lean:495` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStep_inv_lt` | `KAM/Certificate/Expr/Ball.lean:507` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsSpec_prefix_inv` | `KAM/Certificate/Expr/Ball.lean:518` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballsAux_prefix_inv` | `KAM/Certificate/Expr/Ball.lean:549` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.ballStep_sqrt_lt` | `KAM/Certificate/Expr/Ball.lean:559` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.ballsSpec_prefix_sqrt` | `KAM/Certificate/Expr/Ball.lean:569` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.ballsAux_prefix_sqrt` | `KAM/Certificate/Expr/Ball.lean:600` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.SlpInvGood` | `KAM/Certificate/Expr/Ball.lean:610` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.invGood_of_balls` | `KAM/Certificate/Expr/Ball.lean:614` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.SlpSqrtGood` | `KAM/Certificate/Expr/Ball.lean:634` | PASS | Literal positive-real operand predicate, design §4.2 |
| §4.2–4.6 | `KAM.Certificate.Slp.sqrtGood_of_balls` | `KAM/Certificate/Expr/Ball.lean:638` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.jetSmoothOn_empty` | `KAM/Certificate/Expr/Ball.lean:656` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.slpMulO_prefix_self` | `KAM/Certificate/Expr/Ball.lean:658` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.slpInvPre_emit_prefix` | `KAM/Certificate/Expr/Ball.lean:661` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.slpInvNode_emit_prefix` | `KAM/Certificate/Expr/Ball.lean:666` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.HamExpr.nonvanishingOn_of_program_good` | `KAM/Certificate/Expr/Ball.lean:675` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` | `KAM/Certificate/Expr/Ball.lean:768` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.sqrtNewton` | `KAM/Certificate/Expr/BallSqrt.lean:32` | PASS | Finite guarded computation/model construction, design §4.3/4.5 |
| §4.2–4.6 | `KAM.Certificate.sqrtAnchor` | `KAM/Certificate/Expr/BallSqrt.lean:38` | PASS | Finite guarded computation/model construction, design §4.3/4.5 |
| §4.2–4.6 | `KAM.Certificate.ballSqrt` | `KAM/Certificate/Expr/BallSqrt.lean:44` | PASS | Finite guarded computation/model construction, design §4.3/4.5 |
| §4.2–4.6 | `KAM.Certificate.ballSqrt_lt_re` | `KAM/Certificate/Expr/BallSqrt.lean:52` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.re_pos_of_ball` | `KAM/Certificate/Expr/BallSqrt.lean:59` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.re_pos_of_mem_ballSqrt` | `KAM/Certificate/Expr/BallSqrt.lean:67` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.ballSqrt_sound` | `KAM/Certificate/Expr/BallSqrt.lean:72` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.HamExpr` | `KAM/Certificate/Expr/Basic.lean:39` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.modePhase` | `KAM/Certificate/Expr/Basic.lean:55` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.HamExpr.eval` | `KAM/Certificate/Expr/Basic.lean:60` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.HamExpr.NonvanishingOn` | `KAM/Certificate/Expr/Basic.lean:77` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.contDiff_modePhase` | `KAM/Certificate/Expr/Basic.lean:88` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.HamExpr.contDiffOn_eval` | `KAM/Certificate/Expr/Basic.lean:92` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.modePhase_add_int` | `KAM/Certificate/Expr/Basic.lean:115` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.HamExpr.eval_add_int` | `KAM/Certificate/Expr/Basic.lean:123` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.HamExpr.exists_real_eval` | `KAM/Certificate/Expr/Basic.lean:143` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.HamExpr.eval_real` | `KAM/Certificate/Expr/Basic.lean:184` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.certDomain` | `KAM/Certificate/Expr/Basic.lean:191` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.isOpen_certDomain` | `KAM/Certificate/Expr/Basic.lean:196` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.certDomain_add_int` | `KAM/Certificate/Expr/Basic.lean:215` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.Witnesses` | `KAM/Certificate/Expr/Compose.lean:58` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.CertModel.mulN` | `KAM/Certificate/Expr/Compose.lean:69` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.ComposeState` | `KAM/Certificate/Expr/Compose.lean:81` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.slotEntry` | `KAM/Certificate/Expr/Compose.lean:89` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.pair_snd` | `KAM/Certificate/Expr/Compose.lean:91` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.slotEntry_fst` | `KAM/Certificate/Expr/Compose.lean:94` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.slotEntry_snd` | `KAM/Certificate/Expr/Compose.lean:97` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.ComposeState.slot` | `KAM/Certificate/Expr/Compose.lean:102` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.ComposeState.pushSlot` | `KAM/Certificate/Expr/Compose.lean:107` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.charResolve` | `KAM/Certificate/Expr/Compose.lean:113` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.charEntry` | `KAM/Certificate/Expr/Compose.lean:129` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.charSlot` | `KAM/Certificate/Expr/Compose.lean:140` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeStep` | `KAM/Certificate/Expr/Compose.lean:148` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeOps` | `KAM/Certificate/Expr/Compose.lean:187` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.Slp.compose` | `KAM/Certificate/Expr/Compose.lean:196` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.CertModel.mulN_supNormUp` | `KAM/Certificate/Expr/Compose.lean:209` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.CacheValid` | `KAM/Certificate/Expr/Compose.lean:214` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.ComposeState.SlotsEnclose` | `KAM/Certificate/Expr/Compose.lean:219` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.ComposeState.slotsEnclose_nil` | `KAM/Certificate/Expr/Compose.lean:228` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.ComposeState.SlotsEnclose.pushSlot` | `KAM/Certificate/Expr/Compose.lean:242` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.charResolve_sound` | `KAM/Certificate/Expr/Compose.lean:283` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.charEntry_sound` | `KAM/Certificate/Expr/Compose.lean:326` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.charSlot_sound` | `KAM/Certificate/Expr/Compose.lean:358` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeStep_sound` | `KAM/Certificate/Expr/Compose.lean:385` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeOps_sound` | `KAM/Certificate/Expr/Compose.lean:461` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.Slp.compose_sound` | `KAM/Certificate/Expr/Compose.lean:479` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpScaleNode` | `KAM/Certificate/Expr/Diff.lean:39` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpScaleNode_sound` | `KAM/Certificate/Expr/Diff.lean:43` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpExpScaleNode` | `KAM/Certificate/Expr/Diff.lean:53` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpExpScaleNode_sound` | `KAM/Certificate/Expr/Diff.lean:57` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpCombine` | `KAM/Certificate/Expr/Diff.lean:66` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpCombine_sound` | `KAM/Certificate/Expr/Diff.lean:72` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpPowNode` | `KAM/Certificate/Expr/Diff.lean:86` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpPowNode_sound` | `KAM/Certificate/Expr/Diff.lean:90` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.negKey` | `KAM/Certificate/Expr/Diff.lean:111` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.modePhase_negKey` | `KAM/Certificate/Expr/Diff.lean:113` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpTrigNode` | `KAM/Certificate/Expr/Diff.lean:124` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpTrigChar` | `KAM/Certificate/Expr/Diff.lean:130` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpDivNode` | `KAM/Certificate/Expr/Diff.lean:136` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.JetSmoothOn.charFn` | `KAM/Certificate/Expr/Diff.lean:139` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpTrigNode_sound` | `KAM/Certificate/Expr/Diff.lean:143` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpTrigChar_sound` | `KAM/Certificate/Expr/Diff.lean:155` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpDivNode_sound` | `KAM/Certificate/Expr/Diff.lean:167` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.cos_eq_exp` | `KAM/Certificate/Expr/Diff.lean:176` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.sin_eq_exp` | `KAM/Certificate/Expr/Diff.lean:184` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpCompile` | `KAM/Certificate/Expr/Diff.lean:193` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.jetSmoothOn` | `KAM/Certificate/Expr/Diff.lean:227` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.nonvanishingOn_empty` | `KAM/Certificate/Expr/Diff.lean:231` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpCompile_sound` | `KAM/Certificate/Expr/Diff.lean:246` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.jet` | `KAM/Certificate/Expr/Diff.lean:342` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpCompile_prefix` | `KAM/Certificate/Expr/Diff.lean:350` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.zero_slot_val` | `KAM/Certificate/Expr/Diff.lean:354` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.slpOv_eq_val` | `KAM/Certificate/Expr/Diff.lean:363` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.list_getD_map` | `KAM/Certificate/Expr/Diff.lean:370` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.jet_v0` | `KAM/Certificate/Expr/Diff.lean:374` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.jet_d1` | `KAM/Certificate/Expr/Diff.lean:378` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.jet_d2` | `KAM/Certificate/Expr/Diff.lean:394` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.HamExpr.jet_d3` | `KAM/Certificate/Expr/Diff.lean:420` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.4 | `KAM.Certificate.JetSmoothOn.sqrtE` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:32` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.sqrtE_comp_ne_zero` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:36` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.jetDeriv_sqrtE` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:39` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.jetDeriv_sqrtE_inv` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:54` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.jetDeriv_sqrtE_inv_cube` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:65` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.jetDeriv2_sqrtE` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:76` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.jetDeriv3_sqrtE` | `KAM/Certificate/Expr/DiffCalculusSqrt.lean:93` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.slpSqrtD3` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:34` | PASS | Finite SLP/table builder, design §4.4 |
| §4.4 | `KAM.Certificate.slpSqrtTail` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:41` | PASS | Finite SLP/table builder, design §4.4 |
| §4.4 | `KAM.Certificate.slpSqrtTail_sound` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:51` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.slpSqrtPre` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:108` | PASS | Finite SLP/table builder, design §4.4 |
| §4.4 | `KAM.Certificate.slpSqrtNode` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:118` | PASS | Finite SLP/table builder, design §4.4 |
| §4.4 | `KAM.Certificate.slpSqrtPre_emit_prefix` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:122` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.slpSqrtPre_spec` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:128` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.slpSqrtNode_sound` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:162` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.4 | `KAM.Certificate.slpSqrtNode_emit_prefix` | `KAM/Certificate/Expr/DiffNodeSqrt.lean:171` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.Certificate.SlpOp` | `KAM/Certificate/Expr/Slp.lean:30` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp` | `KAM/Certificate/Expr/Slp.lean:40` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.slpConstVal` | `KAM/Certificate/Expr/Slp.lean:44` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.SlpOp.step` | `KAM/Certificate/Expr/Slp.lean:48` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.vals` | `KAM/Certificate/Expr/Slp.lean:59` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.val` | `KAM/Certificate/Expr/Slp.lean:63` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.HamJet` | `KAM/Certificate/Expr/Slp.lean:70` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.phaseNat` | `KAM/Certificate/Expr/Slp.lean:78` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.vals_append_prefix` | `KAM/Certificate/Expr/Slp.lean:82` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.vals_append` | `KAM/Certificate/Expr/Slp.lean:91` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.vals_length` | `KAM/Certificate/Expr/Slp.lean:97` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.val_append` | `KAM/Certificate/Expr/Slp.lean:105` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.vals_snoc` | `KAM/Certificate/Expr/Slp.lean:114` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.Certificate.Slp.val_snoc_self` | `KAM/Certificate/Expr/Slp.lean:120` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.1–4.2 | `KAM.Certificate.sqrtE` | `KAM/Certificate/Expr/Sqrt.lean:33` | PASS | Literal signed total root; approved cut semantics |
| §4.1–4.2 | `KAM.Certificate.sqrtE_eq_exp` | `KAM/Certificate/Expr/Sqrt.lean:35` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_eventuallyEq` | `KAM/Certificate/Expr/Sqrt.lean:46` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.contDiffAt_sqrtE` | `KAM/Certificate/Expr/Sqrt.lean:50` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.differentiableAt_sqrtE` | `KAM/Certificate/Expr/Sqrt.lean:56` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_sq` | `KAM/Certificate/Expr/Sqrt.lean:59` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_ne_zero` | `KAM/Certificate/Expr/Sqrt.lean:64` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_re_nonneg` | `KAM/Certificate/Expr/Sqrt.lean:70` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.mem_slitPlane_of_re_pos` | `KAM/Certificate/Expr/Sqrt.lean:93` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_ofReal` | `KAM/Certificate/Expr/Sqrt.lean:97` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.hasDerivAt_sqrtE_of_mem` | `KAM/Certificate/Expr/Sqrt.lean:108` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.hasDerivAt_sqrtE` | `KAM/Certificate/Expr/Sqrt.lean:122` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_model_error` | `KAM/Certificate/Expr/Sqrt.lean:128` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.1–4.2 | `KAM.Certificate.sqrtE_ball` | `KAM/Certificate/Expr/Sqrt.lean:154` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.5 | `KAM.Certificate.SqrtWitness` | `KAM/Certificate/Model/SqrtWitness.lean:37` | PASS | Signed finite witness data; no assumed analytic conclusion |
| §4.5 | `KAM.Certificate.SqrtWitness.model` | `KAM/Certificate/Model/SqrtWitness.lean:47` | PASS | Literal finite witness model/checker construction, design §4.5 |
| §4.5 | `KAM.Certificate.sqrtAnchorDiff` | `KAM/Certificate/Model/SqrtWitness.lean:50` | PASS | Finite guarded computation/model construction, design §4.3/4.5 |
| §4.5 | `KAM.Certificate.sqrtRadicandDiff` | `KAM/Certificate/Model/SqrtWitness.lean:54` | PASS | Literal finite witness model/checker construction, design §4.5 |
| §4.5 | `KAM.Certificate.sqrtResidual` | `KAM/Certificate/Model/SqrtWitness.lean:59` | PASS | Literal finite witness model/checker construction, design §4.5 |
| §4.5 | `KAM.Certificate.sqrtWitnessRadius` | `KAM/Certificate/Model/SqrtWitness.lean:66` | PASS | Literal finite witness model/checker construction, design §4.5 |
| §4.5 | `KAM.Certificate.slpConstVal_neg_rat` | `KAM/Certificate/Model/SqrtWitness.lean:80` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.5 | `KAM.Certificate.SqrtWitness.model_encloses` | `KAM/Certificate/Model/SqrtWitness.lean:83` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.5 | `KAM.Certificate.sqrtWitness_sound` | `KAM/Certificate/Model/SqrtWitness.lean:88` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.5 | `KAM.Certificate.composeTestW` | `KAM/Certificate/Tests/Compose.lean:37` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_weight` | `KAM/Certificate/Tests/Compose.lean:39` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestPi` | `KAM/Certificate/Tests/Compose.lean:41` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_pi` | `KAM/Certificate/Tests/Compose.lean:43` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestRound` | `KAM/Certificate/Tests/Compose.lean:46` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestJ` | `KAM/Certificate/Tests/Compose.lean:49` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestIPow` | `KAM/Certificate/Tests/Compose.lean:54` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestRange` | `KAM/Certificate/Tests/Compose.lean:62` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestCharE` | `KAM/Certificate/Tests/Compose.lean:65` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestCos` | `KAM/Certificate/Tests/Compose.lean:70` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestK` | `KAM/Certificate/Tests/Compose.lean:73` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestProg` | `KAM/Certificate/Tests/Compose.lean:76` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestInv` | `KAM/Certificate/Tests/Compose.lean:81` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestWit` | `KAM/Certificate/Tests/Compose.lean:85` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestCfg` | `KAM/Certificate/Tests/Compose.lean:89` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestRun` | `KAM/Certificate/Tests/Compose.lean:94` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_all` | `KAM/Certificate/Tests/Compose.lean:98` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_scalar` | `KAM/Certificate/Tests/Compose.lean:104` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_conj` | `KAM/Certificate/Tests/Compose.lean:110` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_noChar` | `KAM/Certificate/Tests/Compose.lean:116` | FAIL F1 | Fourth empty witness field changes handwritten proposition |
| §4.5 | `KAM.Certificate.composeTest_noExp` | `KAM/Certificate/Tests/Compose.lean:121` | FAIL F1 | Fourth empty witness field changes handwritten proposition |
| §4.5 | `KAM.Certificate.composeTest_noInv` | `KAM/Certificate/Tests/Compose.lean:126` | FAIL F1 | Fourth empty witness field changes handwritten proposition |
| §4.5 | `KAM.Certificate.composeTest_pinFail` | `KAM/Certificate/Tests/Compose.lean:132` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_offProgram` | `KAM/Certificate/Tests/Compose.lean:136` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestK2` | `KAM/Certificate/Tests/Compose.lean:144` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTestProg2` | `KAM/Certificate/Tests/Compose.lean:147` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_normKey` | `KAM/Certificate/Tests/Compose.lean:149` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.5 | `KAM.Certificate.composeTest_n2` | `KAM/Certificate/Tests/Compose.lean:153` | FAIL F1 | Fourth empty witness field changes handwritten proposition |
| §4.5 | `KAM.Certificate.composeTest_sound` | `KAM/Certificate/Tests/Compose.lean:163` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyW` | `KAM/Certificate/Tests/Defs.lean:31` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyPi` | `KAM/Certificate/Tests/Defs.lean:33` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyCfg` | `KAM/Certificate/Tests/Defs.lean:36` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyCos` | `KAM/Certificate/Tests/Defs.lean:45` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyK` | `KAM/Certificate/Tests/Defs.lean:48` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyH` | `KAM/Certificate/Tests/Defs.lean:51` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyB` | `KAM/Certificate/Tests/Defs.lean:54` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyWit` | `KAM/Certificate/Tests/Defs.lean:57` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyBox` | `KAM/Certificate/Tests/Defs.lean:59` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyCC` | `KAM/Certificate/Tests/Defs.lean:61` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsToyS` | `KAM/Certificate/Tests/Defs.lean:64` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTestCfg` | `KAM/Certificate/Tests/Defs.lean:67` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTestParams` | `KAM/Certificate/Tests/Defs.lean:72` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTestCert` | `KAM/Certificate/Tests/Defs.lean:77` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_ham` | `KAM/Certificate/Tests/Defs.lean:95` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_ham_fail` | `KAM/Certificate/Tests/Defs.lean:98` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_emb` | `KAM/Certificate/Tests/Defs.lean:101` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_emb_fail` | `KAM/Certificate/Tests/Defs.lean:104` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_inv` | `KAM/Certificate/Tests/Defs.lean:108` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_inv_fail` | `KAM/Certificate/Tests/Defs.lean:111` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_energy` | `KAM/Certificate/Tests/Defs.lean:114` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_energy_fail` | `KAM/Certificate/Tests/Defs.lean:117` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_gram` | `KAM/Certificate/Tests/Defs.lean:120` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_torsion` | `KAM/Certificate/Tests/Defs.lean:123` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.defsTest_static_fail` | `KAM/Certificate/Tests/Defs.lean:126` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negCfg` | `KAM/Certificate/Tests/Negative.lean:57` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negK` | `KAM/Certificate/Tests/Negative.lean:68` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negH` | `KAM/Certificate/Tests/Negative.lean:72` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negConst` | `KAM/Certificate/Tests/Negative.lean:75` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negB` | `KAM/Certificate/Tests/Negative.lean:78` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negCC` | `KAM/Certificate/Tests/Negative.lean:81` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negS` | `KAM/Certificate/Tests/Negative.lean:84` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negParams` | `KAM/Certificate/Tests/Negative.lean:86` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negPi` | `KAM/Certificate/Tests/Negative.lean:91` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negBase` | `KAM/Certificate/Tests/Negative.lean:93` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negBase_passes` | `KAM/Certificate/Tests/Negative.lean:111` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negResidual` | `KAM/Certificate/Tests/Negative.lean:116` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negResidual_fails` | `KAM/Certificate/Tests/Negative.lean:118` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negGramZero_fails` | `KAM/Certificate/Tests/Negative.lean:124` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negGramTwo_fails` | `KAM/Certificate/Tests/Negative.lean:129` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negTorsZero_fails` | `KAM/Certificate/Tests/Negative.lean:134` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negMu_fails` | `KAM/Certificate/Tests/Negative.lean:142` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negExpH` | `KAM/Certificate/Tests/Negative.lean:150` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negExp` | `KAM/Certificate/Tests/Negative.lean:154` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negExp_control` | `KAM/Certificate/Tests/Negative.lean:161` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negExp_fails` | `KAM/Certificate/Tests/Negative.lean:163` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negWeight_fails` | `KAM/Certificate/Tests/Negative.lean:170` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negDivH` | `KAM/Certificate/Tests/Negative.lean:179` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negDiv` | `KAM/Certificate/Tests/Negative.lean:185` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negDiv_passes` | `KAM/Certificate/Tests/Negative.lean:192` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negDivBall_fails` | `KAM/Certificate/Tests/Negative.lean:196` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negDivWit_fails` | `KAM/Certificate/Tests/Negative.lean:202` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negBoxZero_fails` | `KAM/Certificate/Tests/Negative.lean:209` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negRay_fails` | `KAM/Certificate/Tests/Negative.lean:214` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negPiNarrow` | `KAM/Certificate/Tests/Negative.lean:223` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negPi_fails` | `KAM/Certificate/Tests/Negative.lean:225` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneW` | `KAM/Certificate/Tests/Negative.lean:234` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOnePi` | `KAM/Certificate/Tests/Negative.lean:236` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneCfg` | `KAM/Certificate/Tests/Negative.lean:239` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneCos` | `KAM/Certificate/Tests/Negative.lean:248` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneK` | `KAM/Certificate/Tests/Negative.lean:251` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneH` | `KAM/Certificate/Tests/Negative.lean:254` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneB` | `KAM/Certificate/Tests/Negative.lean:257` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneWit` | `KAM/Certificate/Tests/Negative.lean:260` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneBox` | `KAM/Certificate/Tests/Negative.lean:262` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneCC` | `KAM/Certificate/Tests/Negative.lean:264` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneS` | `KAM/Certificate/Tests/Negative.lean:267` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneTestCfg` | `KAM/Certificate/Tests/Negative.lean:270` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneTestParams` | `KAM/Certificate/Tests/Negative.lean:275` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOneTestCert` | `KAM/Certificate/Tests/Negative.lean:280` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negOne_torsion` | `KAM/Certificate/Tests/Negative.lean:298` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negPerm3` | `KAM/Certificate/Tests/Negative.lean:302` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negPerm3_selfInverse` | `KAM/Certificate/Tests/Negative.lean:305` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negPerm3_fails` | `KAM/Certificate/Tests/Negative.lean:313` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negCharH` | `KAM/Certificate/Tests/Negative.lean:322` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negChar` | `KAM/Certificate/Tests/Negative.lean:328` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negCharCompose` | `KAM/Certificate/Tests/Negative.lean:336` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negChar_pin_fails` | `KAM/Certificate/Tests/Negative.lean:340` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.negChar_pin_passes` | `KAM/Certificate/Tests/Negative.lean:346` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRParams` | `KAM/Certificate/Tests/RatData.lean:21` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRHam` | `KAM/Certificate/Tests/RatData.lean:26` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRWeightH` | `KAM/Certificate/Tests/RatData.lean:29` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRWeight` | `KAM/Certificate/Tests/RatData.lean:32` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRCentre` | `KAM/Certificate/Tests/RatData.lean:35` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRRadius` | `KAM/Certificate/Tests/RatData.lean:38` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRBox` | `KAM/Certificate/Tests/RatData.lean:41` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTREmb` | `KAM/Certificate/Tests/RatData.lean:44` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRWit` | `KAM/Certificate/Tests/RatData.lean:47` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRGramInv` | `KAM/Certificate/Tests/RatData.lean:50` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRTorsInv` | `KAM/Certificate/Tests/RatData.lean:53` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRCfgFull` | `KAM/Certificate/Tests/RatData.lean:57` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRCfgLow` | `KAM/Certificate/Tests/RatData.lean:60` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRPi` | `KAM/Certificate/Tests/RatData.lean:63` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyTRCert` | `KAM/Certificate/Tests/RatData.lean:70` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.sqrtToyW` | `KAM/Certificate/Tests/Sqrt.lean:37` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtToyPi` | `KAM/Certificate/Tests/Sqrt.lean:39` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtToyCfg` | `KAM/Certificate/Tests/Sqrt.lean:41` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtToyCos` | `KAM/Certificate/Tests/Sqrt.lean:49` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtToyK` | `KAM/Certificate/Tests/Sqrt.lean:51` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtToyCC` | `KAM/Certificate/Tests/Sqrt.lean:53` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTestParams` | `KAM/Certificate/Tests/Sqrt.lean:55` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTestCert` | `KAM/Certificate/Tests/Sqrt.lean:60` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtBallWeight` | `KAM/Certificate/Tests/Sqrt.lean:79` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTest_ballWeight` | `KAM/Certificate/Tests/Sqrt.lean:81` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ball` | `KAM/Certificate/Tests/Sqrt.lean:85` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ball_isSome` | `KAM/Certificate/Tests/Sqrt.lean:91` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ball_mem` | `KAM/Certificate/Tests/Sqrt.lean:94` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ball_left_fails` | `KAM/Certificate/Tests/Sqrt.lean:99` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ball_axis_fails` | `KAM/Certificate/Tests/Sqrt.lean:102` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_anchor_small` | `KAM/Certificate/Tests/Sqrt.lean:106` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTestG` | `KAM/Certificate/Tests/Sqrt.lean:111` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTestWit` | `KAM/Certificate/Tests/Sqrt.lean:113` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTest_witness` | `KAM/Certificate/Tests/Sqrt.lean:115` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_witness_opposite_root` | `KAM/Certificate/Tests/Sqrt.lean:119` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_witness_negative_anchor` | `KAM/Certificate/Tests/Sqrt.lean:123` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_witness_encloses` | `KAM/Certificate/Tests/Sqrt.lean:128` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTestProg` | `KAM/Certificate/Tests/Sqrt.lean:137` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTest_compose` | `KAM/Certificate/Tests/Sqrt.lean:139` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_compose_missing_witness` | `KAM/Certificate/Tests/Sqrt.lean:144` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTestH` | `KAM/Certificate/Tests/Sqrt.lean:152` | PASS | Finite rational test fixture/program |
| tests | `KAM.Certificate.sqrtTest_ham` | `KAM/Certificate/Tests/Sqrt.lean:157` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ham_fail` | `KAM/Certificate/Tests/Sqrt.lean:160` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_ham_quartic` | `KAM/Certificate/Tests/Sqrt.lean:165` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_balls` | `KAM/Certificate/Tests/Sqrt.lean:168` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_nonvanishing` | `KAM/Certificate/Tests/Sqrt.lean:173` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.sqrtTest_balls_fail_closed` | `KAM/Certificate/Tests/Sqrt.lean:178` | PASS | Concrete kernel regression |
| tests | `KAM.Certificate.torsTestW` | `KAM/Certificate/Tests/Torsion.lean:41` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_weight` | `KAM/Certificate/Tests/Torsion.lean:43` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestPi` | `KAM/Certificate/Tests/Torsion.lean:45` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_pi` | `KAM/Certificate/Tests/Torsion.lean:47` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestConst` | `KAM/Certificate/Tests/Torsion.lean:52` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestMat` | `KAM/Certificate/Tests/Torsion.lean:54` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestCC` | `KAM/Certificate/Tests/Torsion.lean:57` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestSwap` | `KAM/Certificate/Tests/Torsion.lean:59` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_border` | `KAM/Certificate/Tests/Torsion.lean:62` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_failClosed` | `KAM/Certificate/Tests/Torsion.lean:66` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestA3` | `KAM/Certificate/Tests/Torsion.lean:78` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_F7` | `KAM/Certificate/Tests/Torsion.lean:81` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestCfg` | `KAM/Certificate/Tests/Torsion.lean:91` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestCos` | `KAM/Certificate/Tests/Torsion.lean:100` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestK` | `KAM/Certificate/Tests/Torsion.lean:103` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestH` | `KAM/Certificate/Tests/Torsion.lean:106` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestB` | `KAM/Certificate/Tests/Torsion.lean:109` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestWit` | `KAM/Certificate/Tests/Torsion.lean:112` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestBox` | `KAM/Certificate/Tests/Torsion.lean:114` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestS` | `KAM/Certificate/Tests/Torsion.lean:117` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestModels` | `KAM/Certificate/Tests/Torsion.lean:119` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTestRun` | `KAM/Certificate/Tests/Torsion.lean:123` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_pipeline` | `KAM/Certificate/Tests/Torsion.lean:128` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_pipelineFail` | `KAM/Certificate/Tests/Torsion.lean:130` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_sound` | `KAM/Certificate/Tests/Torsion.lean:134` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.torsTest_endToEnd` | `KAM/Certificate/Tests/Torsion.lean:149` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Params` | `KAM/Certificate/Tests/Toy2Data.lean:21` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Ham` | `KAM/Certificate/Tests/Toy2Data.lean:27` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2WeightH` | `KAM/Certificate/Tests/Toy2Data.lean:30` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Weight` | `KAM/Certificate/Tests/Toy2Data.lean:33` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Centre` | `KAM/Certificate/Tests/Toy2Data.lean:36` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Radius` | `KAM/Certificate/Tests/Toy2Data.lean:42` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Box` | `KAM/Certificate/Tests/Toy2Data.lean:45` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Emb` | `KAM/Certificate/Tests/Toy2Data.lean:50` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Wit` | `KAM/Certificate/Tests/Toy2Data.lean:56` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2GramInv` | `KAM/Certificate/Tests/Toy2Data.lean:59` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2TorsInv` | `KAM/Certificate/Tests/Toy2Data.lean:62` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2CfgFull` | `KAM/Certificate/Tests/Toy2Data.lean:71` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2CfgLow` | `KAM/Certificate/Tests/Toy2Data.lean:74` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Pi` | `KAM/Certificate/Tests/Toy2Data.lean:77` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2RootLo` | `KAM/Certificate/Tests/Toy2Data.lean:84` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2RootHi` | `KAM/Certificate/Tests/Toy2Data.lean:88` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2AlgCoeffs` | `KAM/Certificate/Tests/Toy2Data.lean:91` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2Cert` | `KAM/Certificate/Tests/Toy2Data.lean:95` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dParams` | `KAM/Certificate/Tests/Toy2dData.lean:21` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dHam` | `KAM/Certificate/Tests/Toy2dData.lean:27` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dWeightH` | `KAM/Certificate/Tests/Toy2dData.lean:32` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dWeight` | `KAM/Certificate/Tests/Toy2dData.lean:35` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dCentre` | `KAM/Certificate/Tests/Toy2dData.lean:38` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dRadius` | `KAM/Certificate/Tests/Toy2dData.lean:45` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dBox` | `KAM/Certificate/Tests/Toy2dData.lean:48` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dEmb` | `KAM/Certificate/Tests/Toy2dData.lean:53` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dWit` | `KAM/Certificate/Tests/Toy2dData.lean:61` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dGramInv` | `KAM/Certificate/Tests/Toy2dData.lean:97` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dTorsInv` | `KAM/Certificate/Tests/Toy2dData.lean:100` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dCfgFull` | `KAM/Certificate/Tests/Toy2dData.lean:130` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dCfgLow` | `KAM/Certificate/Tests/Toy2dData.lean:140` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dPi` | `KAM/Certificate/Tests/Toy2dData.lean:150` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dRootLo` | `KAM/Certificate/Tests/Toy2dData.lean:157` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dRootHi` | `KAM/Certificate/Tests/Toy2dData.lean:161` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dAlgCoeffs` | `KAM/Certificate/Tests/Toy2dData.lean:164` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT2dCert` | `KAM/Certificate/Tests/Toy2dData.lean:168` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Params` | `KAM/Certificate/Tests/Toy3Data.lean:21` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Ham` | `KAM/Certificate/Tests/Toy3Data.lean:29` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3WeightH` | `KAM/Certificate/Tests/Toy3Data.lean:33` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Weight` | `KAM/Certificate/Tests/Toy3Data.lean:36` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Centre` | `KAM/Certificate/Tests/Toy3Data.lean:39` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Radius` | `KAM/Certificate/Tests/Toy3Data.lean:53` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Box` | `KAM/Certificate/Tests/Toy3Data.lean:56` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Emb` | `KAM/Certificate/Tests/Toy3Data.lean:69` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Wit` | `KAM/Certificate/Tests/Toy3Data.lean:85` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3GramInv` | `KAM/Certificate/Tests/Toy3Data.lean:88` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3TorsInv` | `KAM/Certificate/Tests/Toy3Data.lean:92` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3CfgFull` | `KAM/Certificate/Tests/Toy3Data.lean:114` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3CfgLow` | `KAM/Certificate/Tests/Toy3Data.lean:117` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Pi` | `KAM/Certificate/Tests/Toy3Data.lean:120` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3RootLo` | `KAM/Certificate/Tests/Toy3Data.lean:127` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3RootHi` | `KAM/Certificate/Tests/Toy3Data.lean:132` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3AlgCoeffs` | `KAM/Certificate/Tests/Toy3Data.lean:136` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.Certificate.toyT3Cert` | `KAM/Certificate/Tests/Toy3Data.lean:140` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.TrigShape` | `KAM/CertificateSharp/Ham/BallsTrig.lean:34` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.TBall` | `KAM/CertificateSharp/Ham/BallsTrig.lean:39` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.tbZero` | `KAM/CertificateSharp/Ham/BallsTrig.lean:42` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.tbMag` | `KAM/CertificateSharp/Ham/BallsTrig.lean:45` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.mulShape` | `KAM/CertificateSharp/Ham/BallsTrig.lean:48` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.mulShape_cases` | `KAM/CertificateSharp/Ham/BallsTrig.lean:54` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.stepT` | `KAM/CertificateSharp/Ham/BallsTrig.lean:68` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.ballsAuxT` | `KAM/CertificateSharp/Ham/BallsTrig.lean:92` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.ballsTrig` | `KAM/CertificateSharp/Ham/BallsTrig.lean:101` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.ShapeRel` | `KAM/CertificateSharp/Ham/BallsTrig.lean:108` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.TRel` | `KAM/CertificateSharp/Ham/BallsTrig.lean:112` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.TRel.nil` | `KAM/CertificateSharp/Ham/BallsTrig.lean:115` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.TRel.length` | `KAM/CertificateSharp/Ham/BallsTrig.lean:118` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.tb_fst_getD` | `KAM/CertificateSharp/Ham/BallsTrig.lean:122` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.getD_append_lt` | `KAM/CertificateSharp/Ham/BallsTrig.lean:127` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.getD_append_ge` | `KAM/CertificateSharp/Ham/BallsTrig.lean:131` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.TRel.snoc` | `KAM/CertificateSharp/Ham/BallsTrig.lean:135` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.trig_add_bound` | `KAM/CertificateSharp/Ham/BallsTrig.lean:156` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.stepT_sound` | `KAM/CertificateSharp/Ham/BallsTrig.lean:208` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.ballsAuxT_sound` | `KAM/CertificateSharp/Ham/BallsTrig.lean:304` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.val_mem_ballsTrig` | `KAM/CertificateSharp/Ham/BallsTrig.lean:324` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.norm_val_le_slotMagQ_trig` | `KAM/CertificateSharp/Ham/BallsTrig.lean:335` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.ballsAuxT_prefix_inv` | `KAM/CertificateSharp/Ham/BallsTrig.lean:344` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.invGood_of_ballsTrig` | `KAM/CertificateSharp/Ham/BallsTrig.lean:381` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.ballsAuxT_prefix_sqrt` | `KAM/CertificateSharp/Ham/BallsTrig.lean:404` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.CertificateSharp.sqrtGood_of_ballsTrig` | `KAM/CertificateSharp/Ham/BallsTrig.lean:439` | PASS | Proved scalar/jet/safety/compiler/model contract; standard axiom closure |
| §4.2–4.6 | `KAM.CertificateSharp.nonvanishingOn_of_ballsTrig` | `KAM/CertificateSharp/Ham/BallsTrig.lean:453` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.opDeps` | `KAM/CertificateSharp/Kernel/Prune.lean:35` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.nopOp` | `KAM/CertificateSharp/Kernel/Prune.lean:44` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.liveStep` | `KAM/CertificateSharp/Kernel/Prune.lean:47` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.liveSet` | `KAM/CertificateSharp/Kernel/Prune.lean:51` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.liveClosed` | `KAM/CertificateSharp/Kernel/Prune.lean:55` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.pruneOps` | `KAM/CertificateSharp/Kernel/Prune.lean:60` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.pruneOk` | `KAM/CertificateSharp/Kernel/Prune.lean:64` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.pruneProg` | `KAM/CertificateSharp/Kernel/Prune.lean:68` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.keepFlagged` | `KAM/CertificateSharp/Kernel/Prune.lean:73` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.expFlags` | `KAM/CertificateSharp/Kernel/Prune.lean:77` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.invFlags` | `KAM/CertificateSharp/Kernel/Prune.lean:84` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.prune` | `KAM/CertificateSharp/Kernel/Prune.lean:91` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.Slp.composePruned` | `KAM/CertificateSharp/Kernel/Prune.lean:99` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.opDeps_step_congr` | `KAM/CertificateSharp/Kernel/Prune.lean:107` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.pruneOps_length` | `KAM/CertificateSharp/Kernel/Prune.lean:112` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.pruneOps_getD` | `KAM/CertificateSharp/Kernel/Prune.lean:115` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.liveClosed_spec` | `KAM/CertificateSharp/Kernel/Prune.lean:119` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.prune_vals_take` | `KAM/CertificateSharp/Kernel/Prune.lean:134` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.pruneProg_val` | `KAM/CertificateSharp/Kernel/Prune.lean:178` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| §4.2–4.6 | `KAM.CertificateSharp.Slp.composePruned_sound` | `KAM/CertificateSharp/Kernel/Prune.lean:199` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyW` | `KAM/SpinOrbit/Tests/GraphCert.lean:28` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyPi` | `KAM/SpinOrbit/Tests/GraphCert.lean:30` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyCfg` | `KAM/SpinOrbit/Tests/GraphCert.lean:32` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyCos` | `KAM/SpinOrbit/Tests/GraphCert.lean:35` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyK` | `KAM/SpinOrbit/Tests/GraphCert.lean:37` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyParams` | `KAM/SpinOrbit/Tests/GraphCert.lean:40` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToyBase` | `KAM/SpinOrbit/Tests/GraphCert.lean:44` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphToy` | `KAM/SpinOrbit/Tests/GraphCert.lean:62` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphTest_pass` | `KAM/SpinOrbit/Tests/GraphCert.lean:74` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphTest_mono_fail` | `KAM/SpinOrbit/Tests/GraphCert.lean:78` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphTest_range_fail` | `KAM/SpinOrbit/Tests/GraphCert.lean:82` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |
| tests | `KAM.SpinOrbit.graphTest_margin_fail` | `KAM/SpinOrbit/Tests/GraphCert.lean:88` | PASS | Retained full elaborated type; constructor/proof extensions as reviewed |

## Snapshot hashes

SHA256 of every changed implementation file; together with the fixed design/signature hashes above, this is frozen-v1.

| File | SHA256 |
|---|---|
| `KAM/Certificate/Expr/Ball.lean` | `c70b00185b2750438bee38df03f9e96ab84bc3147c55c65e532b0b4ca7bebfdb` |
| `KAM/Certificate/Expr/BallSqrt.lean` | `a1db28f6bc6ef4315a1f06ffdfb209161b374a7221fd1d08c0f8b5218cec3134` |
| `KAM/Certificate/Expr/Basic.lean` | `f31f08c6b176ab3d1b6990852c2f5b462a612e43be742150096c5b5e28e055f6` |
| `KAM/Certificate/Expr/Compose.lean` | `c260e7e0d1d91d40ce9f21f61b0e9451cb325af0c8c07bd243779d4a722d91fd` |
| `KAM/Certificate/Expr/Diff.lean` | `49aae0278b61d804ca3ca1b25b660bd3bbb41659445114073af238e0c1bff731` |
| `KAM/Certificate/Expr/DiffCalculusSqrt.lean` | `3f242fc1d7efc2c46a9768dddf3956b6c6616b8ab4ff8a2ac464bf7294cc1f55` |
| `KAM/Certificate/Expr/DiffNodeSqrt.lean` | `c5f5f592327677bba98e2b4a8442e3ab717ee1111247bc887072f9c3b4f0c2dc` |
| `KAM/Certificate/Expr/Slp.lean` | `f32560c8003c302e0f8265a78434369242f647b0f60bdf60d5576e6c6855bc98` |
| `KAM/Certificate/Expr/Sqrt.lean` | `6181a7876944839847dec79233270e0e55ac6b087a9f818046700f070951bae4` |
| `KAM/Certificate/Model/SqrtWitness.lean` | `1f27aaa3e83acb96546a9731c173bde9e7eba1ca7f26ef4919a1c3222f8bd9b2` |
| `KAM/Certificate/Tests/Compose.lean` | `222852b43948444a86143fa53d6da5858854ca30e683c44c70d8c85fca9bbce5` |
| `KAM/Certificate/Tests/Defs.lean` | `5db37aa2554f57fbb6814aafb2340ba0ff90a043980e8e2ad9fd53088735ed31` |
| `KAM/Certificate/Tests/Negative.lean` | `a60bc1b4c0e21cd1fe4eba21ec58cb0febc849ff63fccc2e939c334c079fffe8` |
| `KAM/Certificate/Tests/RatData.lean` | `1900668356289791ff9cdfaf097818a345d91fe4bf30d0d7be8cee5ef2121313` |
| `KAM/Certificate/Tests/Sqrt.lean` | `c1303ee057b5e5e51f72a9b37ef5868303e09fd69399269fdd51b26b61df7690` |
| `KAM/Certificate/Tests/Torsion.lean` | `70d194629e659c2803e385e026c13607002e275e4d99bbb000b53ec339a022b2` |
| `KAM/Certificate/Tests/Toy2Data.lean` | `4066860bfdf3680da2e6f58b8ef43d9dec97fb039af3c6bff86ef0b62092bcc6` |
| `KAM/Certificate/Tests/Toy2dData.lean` | `bf48085178f44a65ef47c09c17b7b096624afd6cea0abca66d836d16c96ea269` |
| `KAM/Certificate/Tests/Toy3Data.lean` | `b4472d7766e3b093b81cde86754cf5c418c39d3fc08604f75e75468dbbc841f4` |
| `KAM/CertificateSharp/Ham/BallsTrig.lean` | `318e69c0eaea94abaaa2b804f4f04385638e340ff0b659e78facce30a094018f` |
| `KAM/CertificateSharp/Kernel/Prune.lean` | `e7046af09564ba5aeeeefdaa5f689eeea75a377b943e41b26b843f3a5fc33863` |
| `KAM/SpinOrbit/Tests/GraphCert.lean` | `45188f51c8ad5ccf04aaa3d1ce41ead1bc980159ddff640dc7b2e146fdbacc37` |
| `scripts/sjs/kernel_probe_gen.py` | `6397dc59454daa2877f210038148d2f88dea6d92ee034d89e5db9f5e769b615c` |
| `scripts/spin_orbit/toy_lean_cert.py` | `c8e01a267247ce456ff47fef236d4b8564f9e0b531e7bd67fc3dbd181cc433c9` |

## Disclosed deviations and source/design notes

- The signatures place the checker primitives under `KAM.SpinOrbit.Lock`; the implementation uses `KAM.Certificate`. The handoff’s `kam-inp-24` note explicitly accepts this namespace deviation. The copied source-header probes otherwise match all eight signed theorem contracts. The model witness/checker is also implemented in the shared checker namespace, consistent with design §4.6.
- Witnesses use slot-keyed lookup instead of a new counter; slots survive pruning. This preserves the existing `ComposeState.slotsEnclose_nil` statement and gives a direct alignment argument.
- Adding the defaulted fourth field changes anonymous constructor arity; nine landed test/data files and two emitters migrate their literals. This disclosed data-format change is mathematically benign; F1 identifies the four additional handwritten proposition changes that the ABI receipt omitted. Generated constructor/recursor/equation types necessarily change with the language extension and are not silently counted as retained handwritten contracts.
- New focused `DiffCalculusSqrt` and `DiffNodeSqrt` modules replace the proposed edits to the existing calculus/node files. Emission via reciprocal powers is algebraically equivalent to the derivative expressions described in the design; coefficients and derivative ordering were checked through order three.
- `ballSqrt` explicitly checks the original operand ball’s positive-real margin; this is design §4.3 step 1, and separately enables safety extraction. The additional slit-plane derivative lemma is stronger support, not a stronger premise on a signed theorem.
- Product site `[3]` is an implementation choice for the square-root residual. Missing advice pays the crude product error; it does not bypass the residual bound.
- Design §4.3:425 promises a lemma named `ballStep_sqrt_sound`; the implementation supplies the actual soundness through `ballSqrt_sound` and the new case of the unchanged `ballStepG_sound`/`ballStep_sound` contracts. No mathematical obligation is missing; the draft helper-name inventory is not the landed API.
- Retained design §4.1:331–332 says reality theorems get “one new proof case each”. `eval_real` is not an induction: its unchanged proof projects `exists_real_eval`. Design §4.6 and the implementation correctly record this. This is an editorial inconsistency already noted in design audit 3, not an external-source defect.
- No suspected defect in a pinned external mathematical source was found in this bounded checker audit. No external source/blueprint theorem was newly promoted. The new source/evidence defect is F1’s incorrect ABI receipt.

Known practical limitation: high-order ball bounds can inflate substantially (`½√(I⁴)` uses `M = 1000` although its exact third derivative is zero). This affects acceptance/tightness, not the proven soundness implication. The untrusted Python numerical mirrors do not gain general sqrt support in this package; only the two touched Lean emitters are updated. Lunar-specific coordinate and certificate work remains outside scope.

## Verification commands and results

All audit-launched Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5` (build wrapper supplies `nice`). No clean/update/cache fetch, library-from-scratch build, resource override, or generated-root repair was performed. Other campaign processes on this shared host were not stopped or managed by this audit.

### Targeted gated builds

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-locksqrt KAM.Certificate.Tests.Sqrt \
  KAM.CertificateSharp.Tests.BallsTrig KAM.CertificateSharp.V2.Tests.TrigCombined \
  KAM.SpinOrbit.Tests.GraphCert KAM.SpinOrbit.LunarAssemblySharpGen
```

Exit 0. Exact terminal success: `Build completed successfully (3564 jobs).`

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-locksqrt KAM.Certificate.Tests.Compose KAM.Certificate.Tests.Defs \
  KAM.Certificate.Tests.Negative KAM.Certificate.Tests.RatData KAM.Certificate.Tests.Torsion \
  KAM.Certificate.Tests.Toy2Data KAM.Certificate.Tests.Toy2dData KAM.Certificate.Tests.Toy3Data
```

Exit 0. Exact terminal success: `Build completed successfully (3265 jobs).` The two targeted closures cover all 22 changed Lean modules and downstream Hamiltonian/V2/graph consumers. Replayed warnings are pre-existing (Basic unused `hS`, PiHigh unused simp argument, and inherited ODE unused section variable); no new-file warning or default-heartbeat failure occurred.

### Source-header and edge probes

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Signed.lean
```

Final exit 0, empty output. The probe copied the eight signed theorem headers from §5 (not `type_of%` of the implementation), checked the literal `sqrtE` equation and witness-model equation, and instantiated the combined program-safety contract. Extra `decide +kernel` checks covered zero radicand rejection, self-referencing sqrt rejection, `opDeps (.sqrt 7) = [7]`, successful trig-ball evaluation of `½√(I⁴)`, rejection of a zero-containing trig-ball radicand, and successful slot-keyed witness composition through pruning. The retained `Tests.Sqrt` module has positive/negative ball, witness, composition and Hamiltonian-bound tests; both the existing and new tests are kernel proofs, without `native_decide`. Initial scratch-only launch errors (an incorrect V2 namespace, a wrong base-relative path, and an incorrectly ordered `Slp.balls` test application) were corrected and all affected final probes rerun; they are not source failures.

### Full existing-declaration type comparison

```sh
# From the base checkout, while HEAD there equals the pinned inp commit:
LEAN_NUM_THREADS=1 nice -n 5 lake env lean \
  /root/code/KAM-inp-locksqrt/.lake/abi-scratch/ABI-base.lean
# From this package worktree:
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/ABI-head.lean
```

Both final exits 0. Probes import all 16 modified landed modules plus the unchanged Hamiltonian/V2 consumer modules; for each original source declaration they print a name boundary and `#check @name` under `pp.all true`, `pp.oneline false`. No heartbeat option is used. Result: **387 identical retained types, four F1 migrations, one sanctioned deletion/replacement**. Generated constructors/equations were not represented as handwritten declarations. A separate source comparison confirms every F1 header differs only by the necessary fourth empty witness list and associated parentheses/line wrapping.

### Axiom closure

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Axioms.lean
```

Final exit 0, no diagnostics. `#print axioms` on all 215 public theorem declarations in changed files (including all 58 newly added ones), plus `checkHamBounds_sound`, `TorusCertificate.ham_structural`, and `KAM.CertificateSharp.V2.checkTorusCertificateV2_sound`: **218 checks**. Of these, 204 use all three standard foundations, six use `[propext, Quot.sound]`, seven use `[propext]`, and `pair_snd` uses no axioms. No `sorryAx` or project-specific axiom occurs. Exact output follows.

```text
'KAM.Certificate.certCExpSmall_reduced' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced_cexpHalvings_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ball_two_pi_zpow_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mem_constBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.inv_ball_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.revGet_reverse' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.ballsRev_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toC_zero_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toC_ratCast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballZero_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.BallRel.ballRel_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.BallRel.ballRel_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballForce_eq_some' depends on axioms: [propext]
'KAM.Certificate.ballForce_some' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.ballStep_char' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStepG_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_inv_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballStep_sqrt_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsSpec_prefix_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballsAux_prefix_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.invGood_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.sqrtGood_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetSmoothOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpMulO_prefix_self' depends on axioms: [propext]
'KAM.Certificate.slpInvPre_emit_prefix' depends on axioms: [propext]
'KAM.Certificate.slpInvNode_emit_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_program_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballSqrt_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.re_pos_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.re_pos_of_mem_ballSqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballSqrt_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.contDiff_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.contDiffOn_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.eval_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.exists_real_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.eval_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isOpen_certDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certDomain_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.pair_snd' does not depend on any axioms
'KAM.Certificate.slotEntry_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotEntry_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.mulN_supNormUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ComposeState.slotsEnclose_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ComposeState.SlotsEnclose.pushSlot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charResolve_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charEntry_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charSlot_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeOps_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.compose_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpScaleNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpExpScaleNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCombine_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpPowNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modePhase_negKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.charFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTrigNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpTrigChar_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpDivNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.cos_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sin_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jetSmoothOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompile_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpCompile_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.zero_slot_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpOv_eq_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.list_getD_map' depends on axioms: [propext]
'KAM.Certificate.HamExpr.jet_v0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.jet_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.JetSmoothOn.sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_comp_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_sqrtE_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv_sqrtE_inv_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv2_sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.jetDeriv3_sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpSqrtTail_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpSqrtPre_emit_prefix' depends on axioms: [propext]
'KAM.Certificate.slpSqrtPre_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpSqrtNode_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpSqrtNode_emit_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_append_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.vals_snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_snoc_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_eventuallyEq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.contDiffAt_sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.differentiableAt_sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_re_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mem_slitPlane_of_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hasDerivAt_sqrtE_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hasDerivAt_sqrtE' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_model_error' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtE_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slpConstVal_neg_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.SqrtWitness.model_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtWitness_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_noChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_noExp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_noInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_pinFail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_offProgram' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_normKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_n2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_ham' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_ham_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_emb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_emb_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_inv_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_energy_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTest_static_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negBase_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negResidual_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negGramZero_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negGramTwo_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negTorsZero_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negMu_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negExp_control' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negExp_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negWeight_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negDiv_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negDivBall_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negDivWit_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negBoxZero_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negRay_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negPi_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negOne_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negPerm3_selfInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negPerm3_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negChar_pin_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.negChar_pin_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ballWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ball_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ball_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ball_left_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ball_axis_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_anchor_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_witness_opposite_root' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_witness_negative_anchor' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_witness_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_compose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_compose_missing_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ham' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ham_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_ham_quartic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_balls' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_nonvanishing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrtTest_balls_fail_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_border' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_failClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_F7' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pipelineFail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_endToEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.mulShape_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.TRel.nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.TRel.length' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.tb_fst_getD' depends on axioms: [propext, Quot.sound]
'KAM.CertificateSharp.getD_append_lt' depends on axioms: [propext]
'KAM.CertificateSharp.getD_append_ge' depends on axioms: [propext]
'KAM.CertificateSharp.TRel.snoc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.trig_add_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.stepT_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.val_mem_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.norm_val_le_slotMagQ_trig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_prefix_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.invGood_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.ballsAuxT_prefix_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.sqrtGood_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.nonvanishingOn_of_ballsTrig' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.opDeps_step_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.pruneOps_length' depends on axioms: [propext, Quot.sound]
'KAM.CertificateSharp.pruneOps_getD' depends on axioms: [propext, Quot.sound]
'KAM.CertificateSharp.liveClosed_spec' depends on axioms: [propext, Quot.sound]
'KAM.CertificateSharp.prune_vals_take' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.pruneProg_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.Slp.composePruned_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_mono_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_range_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_margin_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.ham_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.V2.checkTorusCertificateV2_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Moving-base control

The shared `inp` branch advanced during the audit to `d600c634e77f75013abaa6c27c985139e888f8c5` (LOCK-ASM1 integration and root regeneration). A fresh `git diff inp...HEAD --stat` still gives exactly the same 24-file/1231-insertion/62-deletion package diff; the merge base remains `13160166…`. `git diff a5f010eb inp --` over the package's existing checker/test paths is empty, and the base checkout has no uncommitted changes to those paths. Thus the initial declaration snapshot and the fresh full type comparison remain valid; no base theorem change was hidden by that movement. The package’s protected-path triple-dot diff is still empty.

### Exact source-header / edge-probe content

The following temporary file was elaborated successfully and then removed.

```lean
import KAM.Certificate.Tests.Sqrt
import KAM.CertificateSharp.Ham.BallsTrig
import KAM.CertificateSharp.Kernel.Prune
open KAM KAM.Certificate
noncomputable section
example (z : ℂ) : sqrtE z = (if z.im = 0 ∧ z.re ≤ 0 then 0 else z ^ (1 / 2 : ℂ)) := rfl
example (x : ℝ) : ∃ r : ℝ, sqrtE (x : ℂ) = (r : ℂ) := by exact sqrtE_ofReal x
example {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ sqrtE z := by exact differentiableAt_sqrtE hz
example {z : ℂ} (hz : z ∈ Complex.slitPlane) : sqrtE z ^ 2 = z := by exact sqrtE_sq hz
example (z : ℂ) : 0 ≤ (sqrtE z).re := by exact sqrtE_re_nonneg z
example {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt sqrtE (1 / (2 * sqrtE z)) z := by exact hasDerivAt_sqrtE hz
example {z : ℂ} {s r : ℝ} (hs : 0 < s) (hr : r < s ^ 2)
    (h : ‖z - (s : ℂ) ^ 2‖ ≤ r) : 0 < z.re ∧ ‖sqrtE z - s‖ ≤ r / s := by exact sqrtE_ball hs hr h
example {f W : ℂ} {s d ε : ℝ} (hs : 0 < s) (hd : 0 ≤ d) (hds : d < s)
    (hf : 0 < f.re) (hW : ‖W - (s : ℂ)‖ ≤ d) (hres : ‖f - W ^ 2‖ ≤ ε) :
    ‖sqrtE f - W‖ ≤ ε / (s - d) := by exact sqrtE_model_error hs hd hds hf hW hres
variable {α : Type} [CertArith α]
example [LawfulCertArith α] {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {S : SqrtWitness α} {r : α} (hS : sqrtWitnessRadius n W cfg g S = some r) :
    (∀ θ ∈ complexStrip n W.rho, 0 < (gf θ).re) ∧
      (⟨0, S.poly, r⟩ : CertModel α).Encloses n W.rho (fun θ => sqrtE (gf θ)) := by exact sqrtWitness_sound hW cfg hg hdeg hS
example (n : ℕ) (D : Set ((Fin n → ℂ) × (Fin n → ℂ))) (ops : List SlpOp) :
    SlpSqrtGood n D ops ↔ (∀ j a : ℕ, ops[j]? = some (SlpOp.sqrt a) →
      ∀ z ∈ D, 0 < ((Slp.vals n z ops).getD a 0).re) := Iff.rfl
example {n : ℕ} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D) (e : HamExpr n) :
    ∀ (s ops : List SlpOp), (slpCompile e s).1 <+: ops → SlpInvGood n D ops →
      SlpSqrtGood n D ops → e.NonvanishingOn D :=
  HamExpr.nonvanishingOn_of_program_good hD e
example : ballSqrt slpBallPrec ⟨0, 0⟩ 0 = none := by decide +kernel
example : (Slp.balls 1 ⟨[.sqrt 0]⟩ ⟨1 / 4, 5⟩ [] [] 8) = none := by decide +kernel
example : KAM.CertificateSharp.opDeps (.sqrt 7) = [7] := rfl
example (S : SqrtWitness α) : S.model = (⟨0, S.poly, CertArith.ofInt 0⟩ : CertModel α) := rfl

example : (KAM.CertificateSharp.ballsTrig 1 sqrtTestH.jet.prog sqrtBallWeight [1] [1 / 10] 8).isSome = true := by
  decide +kernel
example : KAM.CertificateSharp.ballsTrig 1 (HamExpr.sqrt (.action 0) : HamExpr 1).jet.prog
    sqrtBallWeight [0] [1 / 2] 8 = none := by decide +kernel
example : (KAM.CertificateSharp.Slp.composePruned 1 sqrtTestProg sqrtToyK
    ⟨[], [], [], [(1, sqrtTestWit 2 2)]⟩ sqrtToyW sqrtToyCfg sqrtToyPi [1]).isSome = true := by
  decide +kernel

```

### Independent kernel replay

One invocation, after all other Lean probes had completed:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Expr.Ball KAM.Certificate.Expr.BallSqrt KAM.Certificate.Expr.Basic KAM.Certificate.Expr.Compose KAM.Certificate.Expr.Diff KAM.Certificate.Expr.DiffCalculusSqrt KAM.Certificate.Expr.DiffNodeSqrt KAM.Certificate.Expr.Slp KAM.Certificate.Expr.Sqrt KAM.Certificate.Model.SqrtWitness KAM.Certificate.Tests.Compose KAM.Certificate.Tests.Defs KAM.Certificate.Tests.Negative KAM.Certificate.Tests.RatData KAM.Certificate.Tests.Sqrt KAM.Certificate.Tests.Torsion KAM.Certificate.Tests.Toy2Data KAM.Certificate.Tests.Toy2dData KAM.Certificate.Tests.Toy3Data KAM.CertificateSharp.Ham.BallsTrig KAM.CertificateSharp.Kernel.Prune KAM.SpinOrbit.Tests.GraphCert KAM.Certificate.Sound.Ham KAM.CertificateSharp.V2.Engine
```

Exit **0**. Exact output:

```text
replaying KAM.CertificateSharp.V2.Engine
replaying KAM.Certificate.Sound.Ham
replaying KAM.SpinOrbit.Tests.GraphCert
replaying KAM.CertificateSharp.Kernel.Prune
replaying KAM.CertificateSharp.Ham.BallsTrig
replaying KAM.Certificate.Tests.Toy3Data
replaying KAM.Certificate.Tests.Toy2dData
replaying KAM.Certificate.Tests.Toy2Data
replaying KAM.Certificate.Tests.Torsion
replaying KAM.Certificate.Tests.Sqrt
replaying KAM.Certificate.Tests.RatData
replaying KAM.Certificate.Tests.Negative
replaying KAM.Certificate.Tests.Defs
replaying KAM.Certificate.Tests.Compose
replaying KAM.Certificate.Model.SqrtWitness
replaying KAM.Certificate.Expr.Sqrt
replaying KAM.Certificate.Expr.Slp
replaying KAM.Certificate.Expr.DiffNodeSqrt
replaying KAM.Certificate.Expr.DiffCalculusSqrt
replaying KAM.Certificate.Expr.Diff
replaying KAM.Certificate.Expr.Compose
replaying KAM.Certificate.Expr.Basic
replaying KAM.Certificate.Expr.BallSqrt
replaying KAM.Certificate.Expr.Ball
```

This replays all 22 changed Lean modules and the two named downstream soundness modules against the kernel. It does not replay lunar LOCK-GEN data or establish a headline theorem.

### Source lint and protected paths

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, with exactly this output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/Certificate.lean)
check_lean_modules: PASS (1634 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

The sole lint failure is the brief's explicitly permitted generated-root exception. The root was not regenerated. Module checks, proof-escape/resource/type/size checks, frozen-anchor guard and all 158 frozen ABI hashes pass. Maximum changed Lean file length: **778** (`Expr/Ball.lean`); all changed files meet the 100-column/module requirements. No new `sorry`, `axiom`, `admit`, `unsafe`, `opaque`, `native_decide`, heartbeat/recursion/synthesis override or `EuclideanSpace` occurs. Changed implementation files import no provider or DRAFT_SORRY anchor; the only direct frozen import in the modified checker source is the existing `Frozen.Defs.ComplexStrip`.

```sh
git diff --check inp...HEAD
git diff --check
git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
```

All exit 0 with empty output. Frozen/generated protected paths are unchanged by the package. The source hashes above were rechecked after all validation, with **zero drift**. No tracked file was modified by the auditor. The original untracked handoff is left intact; this report is the sole retained audit addition. All audit-created scratch probes and logs were removed after their results and probe content were recorded here.

## Closeout and disposition

| Gate | Result |
|---|---|
| Complete requested diff and local design/source review | PASS, 24 changed files |
| Signed scalar/witness contracts and literal definitions | PASS, accepted namespace relocation recorded |
| Domain extraction, jets through order three, composition/pruning | PASS |
| All 28 new definitions/structures classified | PASS |
| All 58 new theorem axiom closures, plus existing public/consumer checks | PASS, 218 axiom checks total |
| Targeted builds | PASS, both commands exit 0 |
| One-invocation kernel replay | PASS, 24 modules, exit 0 |
| Frozen guard / 158 ABI hashes / protected-path diff | PASS |
| Source lint | PASS WITH NOTES: exit 1 solely for authorized stale generated root |
| Literal existing handwritten declaration preservation | **FAIL F1: four extra test-proposition migrations** |
| Frozen theorem seal readiness | N/A: this checker package introduces/seals no frozen theorem |

**Final package verdict: FAIL the stated single-exception ABI contract; PASS for the audited checker proofs and their declared consumers.** F1 requires a corrected handoff/ABI receipt and an explicit disposition of the four test-signature migrations. No substantive analytic premise, conclusion, norm, carrier or consumer weakening was found. The documented engine extension remains scoped infrastructure; no lunar final theorem or campaign closure follows from this audit.
