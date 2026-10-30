# SO-LOCK strict delta design audit 3

**Overall verdict: PASS WITH NOTES.** Revision 3 resolves the two blocking findings of audit 2 under the supplied sub-orchestrator ruling. The sole proposed replacement of an existing landed theorem contract is `HamExpr.nonvanishingOn_of_inv_good`; its replacement takes both inverse and sqrt safety. The four named consumer statements can remain unchanged with sound proof routes. `lockHamExpr_clock` now requires positive Ω. No further necessary landed theorem-statement change was found in this bounded design review. This is approval of the revised design contracts, not of an implemented checker, proved theorem, frozen statement or kernel-passed certificate.

Auditor: maud-lockdesign-3, 2026-10-30 UTC. Scope: **only audit-2 findings 1–5 and changed text**, comparing `6c076a6d958d7ea98988a1b896d94e8297b4adca` with audited HEAD `4560032011a1e6b12d3262be9584ea85d16c23bc`. Read repository rules, PLAN, DECISIONS, the supplied audit brief, revision-3 diff, response table and handoff. Applied the focused manuscript-audit protocol: fixed inputs, mechanical statement/caller comparison, adversarial re-check of the proposed repairs, then validation. No subagents or external sources were used. Authorization permits this report and temporary scratch verification only; no design repair or state-changing git operation was performed.

## Input snapshot

| Input | SHA256 at audited HEAD |
|---|---|
| `docs/tracks/SO/design/SO-LOCK-DESIGN.md` | `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d` |
| `.drafts/design/SOLockSignatures.lean` | `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d` |
| `docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` | `a6df58747ebc11eb2aaa3a3f6217f791a282b62f31c761ce6f579fdad73368d8` |
| `.drafts/handoff-DESIGN-LOCK.md` | `efa023540d77c3441f35e8e14a404b63a4778eea7cdc70aecdb40c0c7e987a50` |

The complete requested delta contains only these four revised files and the committed audit-2 report. `git diff --quiet 6c076a6d 45600320 -- KAM manifest` exits 0: **no landed source statement has actually changed yet**. The exception below concerns the planned LOCK-SQRT implementation. The shared `inp` HEAD observed for elaboration was `003c5a3a04b09690bc03ab763b69e159641da2b4`. Inspected `Expr/{Basic,Ball,Diff}.lean`, `Sound/Ham.lean` and `CertificateSharp/Ham/BallsTrig.lean` were byte-identical between the audit worktree and shared checkout.

## Numbered findings and dispositions

### 1. CLOSED — Audit-2 finding 1: single-helper exception and preserved consumers

**Evidence:** design §4.2:343–411 at this HEAD; §4.6:455–475; response §10:627; proposal Q8. The design now explicitly says “delete it and replace it by a new name” and states:

```lean
theorem HamExpr.nonvanishingOn_of_program_good {D : Set Ph} (hD : IsOpen D) (e : HamExpr n) :
    ∀ (s ops : List SlpOp), (slpCompile e s).1 <+: ops → SlpInvGood n D ops →
      SlpSqrtGood n D ops → e.NonvanishingOn D
```

The new predicate is spelled out, not assumed equivalent to inverse safety:

```lean
def SlpSqrtGood (n : ℕ) (S : Set ((Fin n → ℂ) × (Fin n → ℂ))) (ops : List SlpOp) : Prop :=
  ∀ j a : ℕ, ops[j]? = some (SlpOp.sqrt a) →
    ∀ z ∈ S, 0 < ((Slp.vals n z ops).getD a 0).re
```

`SlpInvGood` keeps its existing meaning. This matches the ruling supplied in the task: one unfrozen landed helper may change, documented for owner review. The exception is recorded in design §4.2, its summary/inventory and proposal Q8; it is not represented as an already-granted owner freeze approval. No extra confirmation is needed to complete this audit.

**Adversarial check of the repair.** In the old counterexample, `.sqrt (.action 0)` at action i fails `SlpSqrtGood`, so it cannot satisfy the repaired theorem's premises. To avoid circularity in the new sqrt induction case, first use the induction hypothesis on the operand to obtain its `NonvanishingOn`; then use existing compiler soundness/value agreement for that operand, the sqrt instruction's index and the prefix lemmas to identify the operand slot with `a.eval`. The new safety premise supplies its positive real part. Both predicates are supplied on the same full `ops`, and prefix value stability connects the operand's compiled prefix to that full program. No analyticity of the parent sqrt is assumed to derive its own domain safety.

For the two new safety-extraction lemmas, a successful sqrt ball step certifies `r < s²`, with the positive anchor required by the ball rule. Slot enclosure and `sqrtE_ball` give positivity of the **operand**, not merely of the output root. Prefix preservation transports the checked operand enclosure to final slots. Invalid/out-of-range operands must be rejected by this same check: a zero operand cannot lie in an accepted positive-real ball. The trigonometric pass needs its own prefix/extraction argument, which is now explicitly listed as `sqrtGood_of_ballsTrig`. These are sound proof routes; their new proof bodies remain implementation work.

The direct caller search over all `KAM/` found exactly two calls to the old helper: `Expr/Ball.lean:501` and `CertificateSharp/Ham/BallsTrig.lean:404`. Its declaration is at `Expr/Ball.lean:424`. No additional caller was found.

| Existing landed declaration | Existing statement retained | Sound revised proof route |
|---|---|---|
| `HamExpr.nonvanishingOn_of_balls` (`Expr/Ball.lean:497–500`) | `checkWeight … = true` and successful `e.jet.prog.balls … = some bs` imply `e.NonvanishingOn (certDomain …)`. All binders and conclusion stay unchanged. | Apply the new combined helper to `e.jet.prog.ops` and its compile prefix; the same successful pass supplies `Slp.invGood_of_balls` **and** new `Slp.sqrtGood_of_balls`. |
| `nonvanishingOn_of_ballsTrig` (`CertificateSharp/Ham/BallsTrig.lean:400–403`) | The analogous weight premise and successful `ballsTrig … = some bs` imply the same domain predicate. All binders and conclusion stay unchanged. | Use the combined helper with existing `invGood_of_ballsTrig` and new `sqrtGood_of_ballsTrig` from the same pass. |
| `checkHamBounds_sound` (`Certificate/Sound/Ham.lean:81–88`) | `checkStatic c = true` and `checkHamBounds c = true` imply `c.ham.NonvanishingOn c.D` and the existing five bounds on `DH`, `X_H`, `DX_H`, `D²X_H`, and `D²H`, with the same `c.params.M`. No bound or premise changes. | Its line 98 obtains `hnv` through the unchanged balls theorem; unchanged-contract jet bridges identify derivatives and the same slot-bound/operator-norm arguments apply. New sqrt jet cases are proved under the extended domain predicate. |
| `TorusCertificate.ham_structural` (`Certificate/Sound/Ham.lean:68–77`) | Existing `hnv : c.ham.NonvanishingOn c.D` implies openness, integer-translation stability, complex differentiability, periodicity and real-point reality. All quantifiers and conclusions stay unchanged. | Its current proof still uses `contDiffOn_eval`, `eval_add_int`, and unconditional `eval_real`; the new domain arm pays for sqrt smoothness and `sqrtE_ofReal` pays for the reality induction. |

`SplitBounds.lean:194,209,228` and `V2/HamClaim.lean:61` use the balls theorems, not the retired helper, so no new premise is pushed into those callers. The existing inverse-safety extraction statements also remain compatible: sqrt steps need only preserve their existing inverse guarantees, while separate new lemmas extract sqrt guarantees.

**Single-exception verdict: PASS at design level.** The only existing landed theorem proposed for deletion/replacement is the named helper. New constructors, definition arms, witness fields, helper declarations and proof cases are the separately disclosed language/data extension; they are not additional replacements of existing theorem contracts. Existing sqrt-free equations retain their meanings. `exists_real_eval`, `eval_real`, `contDiffOn_eval`, compiler/value/jet soundness and the four consumers above require no further statement change. This does not assert that a future unreviewed implementation has preserved them: the eventual implementation diff, ABI checks and checker audit must enforce that contract.

### 2. CLOSED — Audit-2 finding 2: positive Ω repairs the clock contract

**Evidence:** signatures:284–286 and design §3:292–301. The one changed draft theorem statement is now:

```lean
theorem lockHamExpr_clock (Ω : ℚ) (hΩ : 0 < Ω) (cs : List ℚ)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) (hz : 0 < (z.2 0).re) :
    fderiv ℂ (lockHamExpr Ω cs).eval z (KAM.Certificate.phaseBasis (.inr 1)) = 1
```

Positive Ω and π make both radicands have positive real part whenever `Re I > 0`. They lie in the analytic branch locally. The centre functions, trigonometric terms and remaining algebraic operations are holomorphic there, so the **full** Fréchet derivative exists. The pullback depends on J̃ through exactly the summand J̃, giving clock derivative 1. The old negative-Ω discontinuity example is excluded. This checks the full differentiability issue, rather than merely an affine partial derivative.

The graph and assembly consumers already carry `hΩ : 0 < g.Ω`; they can supply the added premise. `lockHamExpr_eval` (signatures:279–280) keeps its all-Ω/all-z statement. Its proof target is algebraic substitution into `soRotHC`, without simplifying a squared root to its radicand on the cut, so it does not need the positivity premise. No headline or landed theorem changes here: `lockHamExpr_clock` is an unlanded draft.

### 3. CLOSED WITH LOW EDITORIAL NOTE — Audit-2 finding 3: proof status and literal rounding

**Evidence:** design §1.4:114–153; signature docstring:50–52; proposal summary item 3. The revised text now says “Intended route, not yet proved,” distinguishes the four exact rational comparisons checked in audit 2 from the unproved contraction argument, and keeps the torus-dependent literals provisional. No numerical theorem was newly proved by this revision or this audit.

The clarified rule uses multiples of 1/10000 for Iin, 1/100 for Rψ and 1/1000 for Rp. It explains why Rp is 0.026 rather than the three-significant-digit 0.0255. Those decimal grids are compatible with the displayed provisional outputs and with the unchanged safety inequalities.

**Residual wording:** design:146 still calls Iin the “largest 3-significant-digit rational,” and line 147 still calls Rψ “2-digit,” before lines 148–150 state the authoritative decimal grids. These descriptions agree for the current numbers, but are not identical rounding policies for arbitrary future data. The response table explicitly selects decimal grids. Remove the older phrases in a later editorial pass so the owner-facing rule has one spelling. This is not a blocker or a request to alter the current literals.

### 4. CLOSED AS A DESIGN NOTE — Audit-2 finding 4: physical frequency and remaining gates

**Evidence:** design:309–313 explicitly sets the physical frequency to `(sinf/κ) • ωstar`, undoes the certificate's κ time scaling, and states that the resulting clock component is 1. This is the correct direction: the vector field of κK is κ times that of K, so an exact torus at `sinf • ωstar` for κK becomes a torus at `(sinf/κ) • ωstar` for K. Positive κ is already present in both certificate consumers. No hidden sign reversal or extra physical-time scaling remains in the changed description.

The absence of SO blueprint/graph artifacts, the placeholder definitions, pending safety/jet/witness/literal proofs, actual data and kernel checks remain the scope limitations already recorded in audit 2. This delta does not claim to close them. The reference `soRotBarrier_of_certified` exists in `Graph/Cert.lean:260`; the landed rotated-frame proof uses the same time-unscaling and clock-rigidity pattern.

### 5. CLOSED WITH LOW EDITORIAL NOTE — Audit-2 finding 5: landed-file inventory

**Evidence:** design §4.6:455–488 and §6:505–507. The inventory now explicitly lists constructors, arms, fields, helpers and safety extraction, attributes the compiler arm to `Diff.lean`, includes trigonometric sqrt-safety extraction, and requires operand dependency `[a]`, congruence and aligned witness pruning in `Prune.lean`. The test file is optional. `Sound/Ham.lean` is correctly listed as needing no expected statement or proof edit after the lower-level replacements. The one helper replacement is disclosed throughout the revised summary, inventory and package description.

Shared-file ownership, BALLFIX sequencing, size checks and verification of old-certificate reduction remain implementation gates. No new package dependency or file-size problem is introduced by this delta.

**Residual wording:** unchanged design §4.1:331–332 still says both reality results get “one new proof case each.” The revised inventory at line 464 and response table at line 612 correctly say that `eval_real` keeps its proof; only `exists_real_eval` has the new induction case. The retained revision-2 portion of the handoff also contains the historical “13 landed files get match cases” wording, while its revision-3 preface and revised canonical inventory supersede it. These are editorial inconsistencies, not an additional theorem-contract exception.

## Changed-interface ledger

No new SO blueprint labels are assigned by this audit. The contract locators are the revised design sections.

| Interface | Contract | Verdict |
|---|---|---|
| `SlpSqrtGood` (new Markdown declaration) | §4.2:356–357 | PASS: explicit positive-real operand safety, separate from inverse safety. |
| `Slp.sqrtGood_of_balls` (new Markdown declaration) | §4.2:359–362 | PASS: successful ordinary ball pass supplies the new predicate. |
| `sqrtGood_of_ballsTrig` (new Markdown declaration) | §4.2:364–367 | PASS: successful trig-ball pass supplies it independently. |
| `HamExpr.nonvanishingOn_of_program_good` (replacement Markdown declaration) | §4.2:389–391 | PASS under the explicit one-helper exception. |
| `lockHamExpr_clock` (changed draft theorem) | §3; signatures:284–286 | PASS: positivity premise repairs full differentiability. |
| `lockHamExpr_eval` (docstring change only) | §3; signatures:279–280 | PASS: statement unchanged; algebraic all-carrier identity. |

The four new/replacement safety declarations mention a constructor that does not yet exist in landed Lean. They were audited as exact design contracts, not reported as elaborated implementations. The scratch signatures elaborate the actual submitted file; they do not validate those Markdown proof bodies. A mechanical comparison of the 26 draft theorem headers before `:=`, ignoring whitespace, found exactly one changed header: `lockHamExpr_clock`.

## Verification and closeout

The submitted signature file was copied byte-for-byte to `.drafts/scratch/SOLockSignaturesAudit3.lean` and elaborated **once** with the prescribed wrapper:

```text
LEAN_NUM_THREADS=1 nice -n 5 \
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-lockdesign .drafts/scratch/SOLockSignaturesAudit3.lean
[sig-gate] slot 1 acquired 16:34:01
exit 0; 29 warnings: declaration uses `sorry`; no other diagnostics
SHA256 original = scratch =
aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d
```

Warning lines: 45,48,53,72,82,104,111,117,128,131,134,136,139,144,149,169,172,209,215,221,229,254,267,275,279,284,305,319,322. The file contains 26 theorem declarations and three placeholder definitions with `sorry` bodies. All new proof claims remain drafts with `sorryAx`; no main result was proved or sealed. No production module was added, so no production target was rebuilt; the scratch elaboration is the targeted gate for this report-only task.

`LEAN_NUM_THREADS=1 nice -n 5 scripts/lint_sources.sh`, run after the signature Lean process completed, exited **1**:

```text
check_lean_modules: PASS (1628 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
.../.lake/abi-scratch/tmp0wrtsttv.lean:1:0: error: unknown module prefix 'KAM'
No directory 'KAM' or file 'KAM.olean' in the search path entries:
.../KAM-inp-lockdesign/.lake/build/lib/lean
```

No other lint diagnostic appeared. This worktree still lacks its own build snapshot; the prescribed signature wrapper uses the shared build. **Full lint/ABI validation did not pass.** This is the same validation limitation as audit 2; no generated files or build overlay were created to mask it. No Lean processes of this audit overlapped, and no resource override, clean build, frozen/generated-file edit or state-changing git operation was used.

A separate consumer probe in `.drafts/scratch/SOLockAudit3Consumers.lean` initially attempted to import `KAM.CertificateSharp.Ham.BallsTrig`; the shared build has no `BallsTrig.olean`, so that attempt exited 1 before checking any declarations (slot 1, 16:36:21). No build was started to fill it. A reduced probe importing `KAM.Certificate.Sound.Ham` used the same wrapper (slot 1, 16:36:38), exited 0 with no warnings, and `#check`ed the exact statements of `HamExpr.nonvanishingOn_of_balls`, `checkHamBounds_sound` and `TorusCertificate.ham_structural`. `#print axioms` on each returned exactly `[propext, Classical.choice, Quot.sound]`. The trig-balls theorem was verified directly from its source and caller list; its compiled type/axioms were **not independently replayed** in this round. The signature file itself was not re-elaborated by either consumer probe.

`git diff --check 6c076a6d 45600320` and final `git diff --check`: exit 0. Both temporary scratch files were deleted. Input hashes were rechecked unchanged. Final `git status --short` contains only `?? docs/tracks/SO/design/SO-LOCK-design-audit-3.md`; this report is the sole retained edit.

No external pinned-source erratum is alleged. The accepted helper replacement is the sole substantive design deviation covered by the supplied ruling and proposal Q8. Existing proof/kernel/data/source-graph gates are retained. The only new audit notes are the residual editorial wording above and the validation limitation below; none reopens a blocking mathematical finding.
