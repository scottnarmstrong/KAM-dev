# SO-LOCK-COST delta review 4

**Overall verdict: PASS WITH NOTES.** Revision 4 resolves the review-3 findings at source/design level: the fallback covers the full program tail, the one-sqrt variant uses new names, the runner selects the existing built checkout and fails closed, and G2claim checks the whole pass against the refined Ham claim. Segmentation is explicitly transferred to SO-CSPLIT, whose **unmeasured 25–60 CPU-hour and 100–200 MB lock projection** is now the baseline. No probe was run, no resource target is established, and no implementation/proof completion is implied by this verdict.

Auditor: maud-lockcost-4, 2026-10-30 UTC. Scope: **only review-3 findings and changed text**, including the requested SO-CSPLIT ownership/projection comparison. No re-audit of SO-LOCK-DESIGN, the landed mathematical proofs, or SO-CSPLIT's internal proof/resource model. Read repository rules, PLAN and DECISIONS. Applied a focused refute-first source review: pinned inputs, checked repairs against the previous counterexamples and actual sources, then static validation. This report is the sole edit.

## Snapshot

Audited revision: **`c4ef8923d6110703bc354b38111af3eb6aca2328`**, compared with `424d7108dd469ec8292eaef265a4284d253ad9a9`. Note locators below refer to c4ef8923. `SO-LOCK-COST.md` SHA256: `edab9b500f0252046ddbc293f988ea54b90664f9bde7c9b8a68a9e2c54d4ef50`.

SO-CSPLIT was read through branch objects, without checking out or modifying it: `inp-socsplit2` at **`a6c13677886761fa8f8dd3dd31dedfcccc3b2a4b`**, `docs/tracks/SO/design/SO-CSPLIT.md` SHA256 `dbddbc72588a46fdfca466e65929362fbe502a7281d4ed84306b283c2d700c05`. Its status is design only; its lock estimates explicitly say “unmeasured; wide error.”

Current `inp` HEAD observed: `7855c9914752f3269e7cc00ea73b4578ea58db85`. The landed two-root `KAM/SpinOrbit/Lock/Coords/HamExpr.lean` remains SHA256 `3cb6ac0a98d41776e8db30e696e9d4adafb3d0aa84d59fbf6c9af604889ae6a7`; its definition and all-z eval theorem were inspected only to verify preservation/naming. Built `HamExpr.olean` and `V2/HamClaim.olean` exist in that checkout.

Inspected gate files under `/mnt/HC_Volume_106379410/kam-data/so-lock/gate/`:

| File | SHA256 |
|---|---|
| `G0_emit.lean` | `0fd7770537b950b283df18bbe2d4421a1d653d2d75c146c9b8935dcc6b77a0dc` |
| `GateLib.lean.inc` | `58305f114c86e0ff19fbdd7e4f22fac9e0a492c82a3e94f857e36a16515c5891` |
| `G1a_force.lean` | `c7dfb569b6c5fa7c9b2e83da1ad1b7b1b82c2306312da329f11acaa23094dfc5` |
| `run_gate.sh` | `e9ce0061bca7dd3278aef4fdeef19931fb2180d5678c15270df23b958603d2cd` |
| `balldy_run.sh.orig` | `c18048b8d14d582bf6927708d3d873d301e448a0d00b652f2f68587adf5d6bb9` |

Only these source files were present; no generated G1b/G1c/G2/G2claim files or new run receipts were present. Generated propositions below were checked from the templates, not from executing G0.

## 1. CLOSED — G1c now pays for the complete program tail

**Evidence:** note:185; `G0_emit.lean:41–53`; `GateLib.lean.inc:30–33`. The first three comparisons cover `[0,800)`, `[800,1600)` and `[1600,2400)`. The fourth now compares:

```text
opsBeq (lockJ.prog.ops.drop 2400) (lockOpsLit.drop 2400) = true
```

There is **no `.take` on the last comparison**, and `opsBeq` checks both list lengths and every paired operation. The review-3 extra-trailing-operation example therefore fails this last comparison rather than passing the fallback. Together with equality of the three earlier slices, generic `List.take_append_drop` identities reconstruct equality of the entire programs; an independently assumed actual length of 3158 is no longer needed for this implication. The four table comparisons then complete all five `HamJet` fields.

The note explicitly includes measuring the structural assembly itself. G1a remains a scout, G1b remains the full five-field comparison, and G1lit remains a literal-cost/count diagnostic rather than the missing proof of original-program length. This is a complete intended fallback contract. The generic Bool-to-equality lemmas and assembly still belong to SO-CSPLIT M0 and must be proved; the gate's `jetBeq` and SO-CSPLIT's proposed `HamJet.beq` must be identified or bridged explicitly when wiring those proofs. None of these new lemmas requires a landed statement change.

No G1 success or sub-9-GB resource receipt is claimed. If the actual compiled count differs from the historical 3158, the literal-count diagnostic and later segment planning must be updated from checked data; the repaired full-tail equality itself does not silently discard operations.

## 2. CLOSED — The one-sqrt variant is now additive under genuinely new names

**Evidence:** note §5:126–146 and §8:221–227. The proposed declarations are now `lockHamExprLean`, `lockHamExprLean_eval` and `lockHamExprLean_clock`. The note explicitly preserves landed `lockHamExpr`, its all-z `lockHamExpr_eval`, and `lockHamExpr_clock`.

The new eval theorem retains both Ω>0 and Re I>0, which place `IΩ/π` in the analytic sqrt branch and justify replacing Y²/2 by `(Ω/(2π)) I cos²(2πα)`. The negative-action and negative-Ω counterexamples to an unrestricted rewrite are explicitly acknowledged. They no longer threaten a landed statement, because the old two-root body and old theorem are not replaced.

Only the new variant's certificate instance/glue selects the new expression. The barrier/domain positivity check remains an explicit new obligation; the clock argument uses equality on the open positive-real-action set. Remaining sqrt/inverse safety remains checked. Choosing the variant requires re-emitting the **entire matching jet, bridge and probe data**. Current gate files target the landed two-root form, so their eventual receipts cannot automatically be relabeled as one-root receipts.

This closes the naming/contract finding. No new expression, eval proof or selection ruling was implemented or approved by this audit. The pre-existing Q8 exception is neither enlarged nor needed for this repair.

## 3. CLOSED — Runner path, error handling and measurement conventions are repaired

**Evidence:** note:166–178; `run_gate.sh:9–41`. The runner now selects `/root/code/KAM-inp`, which exists and has the cited built Hamiltonian object. It uses `set -eu`, a fail-closed `cd`, a recorded revision, and an object-file existence check. The absent `inp-lockcc` path is no longer used as its working directory.

Both `emit` and `probe` now call the same locked, capped function. It sets `LEAN_NUM_THREADS=1`, uses the shared kernel-probe lock, `MemoryMax` and no swap, and records USER/SYS CPU, wall time, RSS, rc, cgroup `memory.peak` and OOM events. It temporarily disables fail-on-error to collect the child status, restores it, and returns that saved rc; failure is no longer hidden by a final successful logging pipeline. A missing cgroup peak is explicitly `UNMEASURED`, not zero. This matches the stated deferral rule for incomplete measurements.

`sh -n run_gate.sh` exits 0. This is shell syntax inspection only, not execution of either branch. The revision/olean checks identify the intended environment but are not a proof that all build artifacts are fresh; the eventual run must retain its exact revision/import receipt. A successful process with no captured peak still has no usable cap measurement. These are ordinary receipt limits, not surviving defects in the repaired runner.

## 4. CLOSED AT PROBE-CONTRACT LEVEL — G2claim now checks actual claim passing

**Evidence:** note:186–187; `G0_emit.lean:55–100`; the added `V2.HamClaim` import in the prelude. G2 is correctly relabeled as evaluator-success and exact-segment evidence only. The new whole-pass G2claim distinguishes:

```text
none                          -> evaluator-fail
some balls, hamClaimOk false   -> claims-fail
some balls, hamClaimOk true    -> claims-pass
```

For P=128 and P=320, the generated kernel proposition runs `ballsRev` from the empty state over **all literal operations**, reverses its reverse-ordered output, and evaluates:

```text
hamClaimOk 4 lockJetLit balls.reverse lockClaimL
```

The four claims are dh=1.925, dx=140.4, d2x=35150 and d2h=166. Their order agrees with `RefClaim`'s actual fields, and `m=4` is correct for the two-angle/two-action Hamiltonian. The generated source imports the actual checker, not a hand-written approximation. `hamClaimOk` checks the d1 sum, each d2 row sum, each d3 row sum and the total d2 sum, so this observes the final refined Ham inequalities that G2 previously omitted. The remaining frame entries in the literal are not checked by `hamClaimOk` and are not claimed paid here.

G0's printed verdict is explicitly untrusted triage. Acceptance requires the corresponding kernel theorem too; switching to P=320 is no longer assumed to repair failure. The printed and generated checks use the same P/domain/claim data; their jet inputs must be connected through the verified G1 bridge. If the monolithic claim theorem exceeds the cap, the note defers its final stage to the exact SO-CSPLIT chain rather than declaring a resource success.

**Limits retained:** no current kernel claim pass exists, middle segments/full chain are unmeasured, and base-Hamiltonian bounds remain a separate consumer obligation. `hamClaimOk` is not itself the Bool `hamBoundsOk`. When preserving the landed base checker, a P=128 refined-claim result must not be silently treated as equality to the landed fixed-320 pass. Keep the original base pass at its original computation, or supply the explicitly justified additional consumer/proof route. This is an integration requirement for later implementation, not a new premise on a landed theorem.

One small wording remnant survives in `G0_emit.lean:61`: the prefix failure message still includes “claims/margins.” The canonical note and the new `evaluator-fail`/`claims-fail` triage now give the correct distinction. Treat the older message as evaluator failure; its text is an editorial cleanup, not a blocker.

## 5. PASS WITH PROVENANCE LIMIT — Segmentation ownership and SO-CSPLIT baseline are correctly represented

**Evidence:** note §§0,2,3,6,8 and response:258; SO-CSPLIT §§0,3.1,4.5,6–7. The revised note transfers composition, Gram, torsion, frame and single-product/staged work to **SO-CSPLIT M0–M3**. It withdraws the competing `sharedBaseV2`/pruned-base implementation and states that SO-CSPLIT proves the **landed Bools** by new equality/recipe lemmas. Ham ball checkpoints are an explicit requested analogue for that tooling, not claimed to be already delivered.

SO-CSPLIT §7 at the pinned branch tip actually gives:

```text
about 170 M calls; about 2,300 theorems at B=75 k
about 300 packed products
25–60 CPU-h
100–200 MB ledger for one lock torus
unmeasured; wide error
```

Those are the baseline numbers now used by C1 and the ledger discussion. The cost note does not add a second separate packed-shard bill to C1: its description explicitly includes packed shards and fixed theorem costs. C2–C7 separately cover jet bridge, Ham passes, ledger/data modules, bites, generation, graph/SOS and final assembly. Whole-module CPU totals remain the intended measurements; a literal baseline is not added again to a measured module total.

The new arithmetic is consistent with its stated assumptions:

```text
25 × 0.93 / 3 × 0.73 = 5.6575 CPU-h
60 × 0.93 / 2 × 0.86 = 23.994 CPU-h
100–200 MB × 0.7      = 70–140 MB
```

Thus the displayed 5.7–24 range is a conditional **C1** estimate, not a total or an established gain. Even the proposed smaller ledger remains over the 50 MB O2 flag. The unchanged full baseline does not meet the ≤20-hour goal; C6–C7 remain unknown. No extra sharing discount is taken.

**Provenance limit:** this review verifies faithful use and ownership of SO-CSPLIT's projection, not its independent correctness. Its rate fit, lock-size calibration, stage proofs, ledger size and heavy-module builds still need the audits/gates assigned there. Copying a projection into the baseline does not turn it into a measurement. The note explicitly requires re-running SO-CSPLIT's CAL gate on lock data and flags owner review of ledger volume; no unsupported cap or budget guarantee is introduced by the transfer.

## 6. Remaining unmeasured work and closeout conditions

The note now lists the unpaid work rather than allowing G1–G2 to settle the whole route. In this inspection **all** probes remain unrun; specifically:

- G0 emission, G1a, literal costs, G1b/full equality, G1c/component and structural assembly costs have no new receipt.
- G2 trial segments, G2claim at either P, middle segments, full ball chain and final consumers are unmeasured.
- SO-CSPLIT's lock-specific CAL, single-product splits, staged linear operations, shard/decode widths, complete consumers and assembly are unmeasured here.
- The actual lock ledger, advice/model/Gram/torsion data, generation CPU, bites/reuse identity, graph/SOS and final assembly remain open.
- The one-root and box variants remain future choices with their own re-emission/claim/resource checks.

Not every bridge/Ham-only item requires the full LOCK-DATA model emission, but the full segmented model campaign does. The note's line 198 should be read as the downstream emission dependency, not as a claim that current G1/G2 have run or require those models. Either way its explicit decision rule is sound: **any unmeasured bill row means defer**, and a remedy that fails its own probe is reported. A note-level PASS does not authorize a ≤20-hour or under-10-GB completion claim.

## Verification receipt

**No probes were run.** Neither `emit`, `probe`, `#eval`, generated Lean source, SO-CSPLIT CAL, nor any numerical generator was executed. No source or generated data under the gate directory, `inp` or `inp-socsplit2` was modified. No resource override or state-changing git operation was used.

Checks performed: requested pinned diff/log; read-only source and branch-object inspection; hashes; existence of the current built import objects; `sh -n run_gate.sh` (exit 0); `git diff --check 424d7108 c4ef8923` (exit 0); and final diff/status/input-hash checks. The source-only review does not supply a Lean elaboration, new proof, axiom or resource receipt. Source lint was not re-run because it invokes a Lean ABI probe and this turn explicitly forbids running probes; no Lean source was changed and no fresh lint/ABI pass is claimed.

No pinned mathematical-source erratum is alleged. No prior review was edited. The only new file is this report. The blocking review-3 findings are closed within the requested delta; the remaining notes are explicit implementation/measurement boundaries and the small diagnostic-text remnant above.
