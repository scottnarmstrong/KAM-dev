# SHARP-C7 handoff: pruned and shared compose (checker side of the sharp certifier)

Brief: `/home/scott/kam-tools/briefs/SHARP-C7.md` (Sonnet), branch `sharp-c7`; design row C7 of
`docs/campaign/design/CERTIFIER-SHARPNESS.md` §6 (levers K-g1, K-g2 of §4.3). LOCAL-COMMON applies.
Nothing under `KAM/Certificate/**` or any SO path was edited.

## Files (new)
- `KAM/CertificateSharp/Kernel/Prune.lean` (222 lines): `liveSet`/`liveClosed`/`pruneOk`, `pruneProg`,
  `prune` (program and witnesses), `Slp.composePruned`, `pruneProg_val`, `Slp.composePruned_sound`.
- `KAM/CertificateSharp/Kernel/Shared.lean` (276): `checkInvEnShared`, `checkTorusCertificateShared E`,
  `invarianceOk_sound`, `energyOk_sound`, `checkInvEnShared_sound`, `checkGram_of_checkTorsion`,
  `checkTorusCertificateShared_sound`.
- `KAM/CertificateSharp/Tests/Shared.lean` (71): kernel tests on T2, T3, T2d.
- `scripts/certifier/shared_compose_bench.lean.txt`: native timing script (copy to `.drafts/`, run).
- `KAM.lean` regenerated (3 imports).

## Approach
- **K-g1 pruning.** A dead operation is replaced by `const 0`, so slot numbers, operand references and the
  product keys `[0, slot]` are unchanged. The exp and reciprocal witnesses that only dead operations consumed are
  dropped (`prune`). The live set comes from an untrusted backward pass and is *verified* by `liveClosed`; on
  failure `prune` returns the program and witnesses unchanged. So `pruneProg_val` (same value at every wanted slot)
  needs no correctness proof of the pass, and `Slp.composePruned_sound` is exactly `Slp.compose_sound` for the
  original program.
- **K-g1 sharing.** One `composePruned` with wanted `v0 :: d1Slots`; `energyOk` on the head, the landed invariance
  sup bounds on the tail (`invarianceOk` is the landed `checkInvariance` body).
- **K-g2.** `checkTorsion` already begins with the same `gramCheck`; `checkGram_of_checkTorsion` shows it contains
  the Gram check, so `checkGram` is dropped (the 9 heavy products are no longer run twice).
- **Contracts.** `checkInvEnShared_sound` proves exactly the `hE` and `hEn` conclusions, from the same hypotheses
  as `checkInvariance_sound_of` and `checkEnergy_sound_of` (copies of their proofs with the composition as a
  hypothesis). `checkTorusCertificateShared_sound` has the conclusion of `checkTorusCertificateWith_sound`; the
  engine `E` is any `AposterioriEngine`. No conclusion-shaped premise.

## Checks and output
- `lake build KAM.CertificateSharp.Tests.Shared`: success (T2, T3, T2d: `pruneOk`, `checkInvEnShared`,
  `checkTorusCertificateShared oldEngine` all `decide +kernel`; `toyCert2d_liveCount = (156, 60)`).
- `scripts/lint_sources.sh`: no finding from my files; `check_lean_modules: PASS (1461)`; frozen guard OK.
  The only remaining message is the known `abi_hashes.py` failure on an unbuilt frozen module (worktree).
- `#print axioms` of `Slp.composePruned_sound`, `pruneProg_val`, `checkInvEnShared_sound`,
  `checkTorusCertificateShared_sound`, `toyCert2_shared_sound`, `toyCert2d_shared_passes`: all
  `[propext, Classical.choice, Quot.sound]`.

## Measured comparison (landed vs mine; toys only)
Live operations of `v0 :: d1Slots`: T2 17/20 (7 of 10 heavy), T3 31/37 (14 of 20), T2d 60/156 (29 of 92 heavy
mul/exp/inv). Native timing of landed `checkInvariance && checkEnergy` against `checkInvEnShared`
(`shared_compose_bench`, 20 runs, err perturbed per run; two sessions): 

| toy | landed | shared |
|---|---:|---:|
| T2d | 164–168 ms | 29–32 ms (**5.3–5.6×**) |
| T3 | 58–69 ms | 48–53 ms |
| T2 | 13–14 ms | 9–17 ms (no gain: tiny) |

Kernel (`decide +kernel`, one declaration, T2d, user time minus the 1.1 s import baseline and ≈2.5 s jet unfolding):
two full composes ≈ 3.8 s, one full compose of the same wanted list ≈ 3.8 s, one pruned ≈ 4.5 s.

## Uncertainties
- **In a single kernel declaration sharing and pruning gain nothing, and pruning costs.** The kernel's whnf cache
  already shares the identical `composeOps` between the two landed composes, and kernel laziness skips dead
  `mul`/`add` models; only dead exp/inv witness checks are forced. Pruning itself is quadratic in program length
  (≈ 0.7–1 s at 156 ops; I estimate ≈ 30 s at 887 ops, which is negligible against the hours of compose, but is
  an extrapolation). The gain appears for strict (native) evaluation and for invariance and energy checked in
  separate declarations (as the SO sharding does), which is the design study's 4.6× setting. I did not run the lunar
  data, as instructed, and could not count live ops of the lunar jet (`KAM.SpinOrbit` is not built in this
  worktree); the 887 → 445 figure is the study's.
- Pass/fail equivalence with the landed `checkInvariance && checkEnergy` is not a theorem. The arithmetic of live
  slots is identical, but dropping witnesses shifts the exp/inv counters used in `cfg.forWitness` advice keys, so
  advice lookups may differ from the landed run (soundness is unaffected). It agrees on all three toys.
- The engine interface only replaces `test`, so the shared certifier is a separate definition
  (`checkTorusCertificateShared E`), not an `AposterioriEngine`.

## Errata / deviations
- None found in pinned sources. Deviation: the energy and invariance soundness proofs are duplicated (copied with the
  composition as hypothesis), because the landed lemmas are stated over `checkInvariance c = true` and cannot be
  edited.
- Not done: K-e, K-b, K-c, K-g4 (SO-owned proposals).
