# SO-TOYFIX2 independent package audit 1

Audit date: 2026-10-30. Worktree `/root/code/KAM-inp-sotoyfix2`.
Compared `git diff inp...HEAD` in full (11 files, including structural comparison of every changed JSON leaf and exact re-emission of the large literal replacement).
HEAD `5492d97f950faf168b11cc18c026229ee4dc84e0`; inp `0319427f9030707d7d39672fb464a2954dfc1afa`.
The user's exact worktree-local report path overrides the generic brief's main-worktree destination.

## Verdict

**PASS WITH NOTES** for `KAM.Certificate.toyCert2d_passes` and `KAM.Certificate.toyCert2d_torus`.
Both have exactly the signed §J names and types, without hypotheses. `toyCert2d : TorusCertificate 2 ℚ` also matches.
This package supplies test applications, not a provider or a new frozen seal: provider/frozen-type and seal-body probes are inapplicable. No frozen anchor is modified or newly declared closed by this audit.
The notes concern stale documentation and the change in import path for existing T2d names; no mathematical or proof-escape defect was found.

Read: AGENTS.md, PLAN, DECISIONS, audit brief, handoff/AUDIT FOCUS, signed `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:1120–1161`, SO design §8 and embedded §J, track-I statement/I-G1, `blueprint-I/parts/p2-iso-iteration.tex:329–355`, the frozen isoenergetic statement and relevant frozen definitions. There is no `docs/tracks/SO/statement.md`; the specified signed SO interface and ruling are the applicable authority. Tracks N/P have no changed nodes here.

## Declaration audit

All names below are in `KAM.Certificate`. T2d theorem locations refer to `KAM/Certificate/Tests/Toy2d.lean`.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| §J / 32 | `toyCert2d` | PASS | Exact rational dimension-2 certificate alias. |
| §8 static / 34 | `toyCert2d_static` | PASS | Closed kernel decision; shape, positive parameters, weights and π checks. |
| §8 balls / 36 | `toyCert2d_hamBounds` | PASS | Closed kernel decision; denominator certification and all five Hamiltonian bounds. |
| §8 embedding / 38 | `toyCert2d_embedding` | PASS | Closed kernel decision; domain margin and derivative bound. |
| §8 residual / 40 | `toyCert2d_invariance` | PASS | Closed kernel decision; positive error budget, full-stage composition. |
| §8 energy / 42 | `toyCert2d_energy` | PASS | Closed kernel decision; energy-average enclosure. |
| §8 Gram / 44 | `toyCert2d_gram` | PASS | Closed kernel decision; inverse witness verified. |
| §8 torsion / 46 | `toyCert2d_torsion` | PASS | Closed kernel decision; bordered inverse and bound verified. |
| §8 smallness / 48 | `toyCert2d_smallness` | PASS | Both literal rational inequalities checked. |
| §J / 50 | `toyCert2d_passes` | PASS | Exactly `checkTorusCertificate toyCert2d = true`. |
| §8 frequency / 55 | `toyCert2d_freq` | PASS | Root and algebraic box checks enclose the exact signed real vector. |
| §J / 63 | `toyCert2d_torus` | PASS | Exactly `CertifiedTorus toyCert2d ![lunarNuMinus / 2, 1 / 2]`; no premises. |
| T2 regression | `toyCert2` | PASS | Existing definition unchanged. |
| T2 regression | `toyCert2_passes` | PASS | Existing proof unchanged. |
| T2 frequency identity | `toyLunarFreq_eq_algFreq` | PASS | Existing explicit coefficient identity, unchanged. |
| T2 regression | `toyCert2_freq` | PASS | Existing proof unchanged. |
| T2 regression | `toyCert2_torus` | PASS | Existing black-box application unchanged. |

Every public data definition in `Tests/Toy2dData.lean` was classified; all are concrete, total data, with no new structures or abbreviations:

| Location | Declaration | Verdict / classification |
|---|---|---|
| 21 | `toyT2dParams` | PASS: literal rational parameters, τ=1, ρ=9, ρ∞=1, γ=1/42, s=2, err=10^-42>0. |
| 27 | `toyT2dHam` | PASS: literal expression tree with the genuine division and a=10^30. |
| 32 | `toyT2dWeightH` | PASS: concrete geometric domain weight at 451/50. |
| 35 | `toyT2dWeight` | PASS: concrete strip weight at 9. |
| 38 | `toyT2dCentre` | PASS: two rational action coordinates. |
| 45 | `toyT2dRadius` | PASS: two radii 1/50. |
| 48 | `toyT2dBox` | PASS: rational enclosure of the exact reference vector. |
| 53 | `toyT2dEmb` | PASS: primary identity angles and constant rational actions. |
| 61 | `toyT2dWit` | PASS: one nontrivial reciprocal polynomial and one character witness; empty exponential list is intentional. |
| 97 | `toyT2dGramInv` | PASS: literal 2×2 identity polynomial witness. |
| 100 | `toyT2dTorsInv` | PASS: literal rational 3×3 bordered inverse witness. |
| 130 | `toyT2dCfgFull` | PASS: cutoff 10^6, 24/8 orders, 34 direct advice keys. |
| 140 | `toyT2dCfgLow` | PASS: same settings; no truncation. |
| 150 | `toyT2dPi` | PASS: Machin enclosure data checked by static stage. |
| 157 | `toyT2dRootLo` | PASS: rational lower enclosure endpoint for √5. |
| 161 | `toyT2dRootHi` | PASS: rational upper enclosure endpoint for √5. |
| 164 | `toyT2dAlgCoeffs` | PASS: literal affine algebraic frequency coefficients. |
| 168 | `toyT2dCert` | PASS: direct assembly of those fields; whole-certificate `expHalvings=8`, `expOrder=24` match JSON. |

The configuration's `fun _ _ => none` is the intentionally absent packed-product advice, not an assumed answer or a mathematical fallback: the actual advice book uses `.direct`, and key coverage is exact. All rational/list/witness records denote their literal objects on their entire carriers. Existing generic list defaults are not a way around the shape checks here. The public alias adds no choice, junk value, source premise, or instance carrying the conclusion.

## Focus: the ruling and proof route

Signed §J at lines 1147–1151 explicitly permits “a rational `a > 1` large enough that the strip, and hence the smallness threshold, are moderate.” Choosing the exact rational integer 10^30 complies. The expression is still `J + (p²/2)·(N/N)`, `N=a+cos(2πq)`, rather than an expression tree with the quotient simplified away. A fresh Lean `rfl` probe confirmed the literal Hamiltonian equality, and a kernel decision confirmed positive err.

`Defs.lean:293–295` orders the conjunction as static, Hamiltonian bounds, embedding, invariance, energy, Gram, torsion, smallness. `Toy2d.lean:50–53` supplies exactly those eight closed results in that order and simplifies their Boolean conjunction; no check is omitted or replaced by an assumption.

`Toy2d.lean:63–70` applies the existing `checkTorusCertificate_sound` directly to passes, frequency enclosure and `lunarNuMinus_half_isDiophantine`, after proving γ=1/42 and τ=1. The frequency enclosure checks √5 and `checkAlgBox`, not an approximate equality with the exact reference vector. `Soundness.lean:62–79` assembles the analytic hypotheses and calls `KAM.Iso.Apost.g1_explicit`. The existing explicit G1 theorem implements blueprint `bpI:p2:g1`; the toy does not infer the conclusion solely from numerical output.

The division really reaches both guarded routes: `Expr/Ball.lean:155–184` returns `none` unless the inverse input radius is strictly less than the maximum absolute component of its centre, and `Defs.lean:237–240` rejects `none`. For this denominator the centre is a=10^30 and the conservative cosine radius is `2052684210367924024698804359963/500000 < a`. There is no nonzero-denominator premise. `Expr/Compose.lean:166–173` consumes `invWit` and calls `Model/Inv.lean:63–73`, which requires δ<1 before accepting the reciprocal residual. The witness has 15 nonzero terms, 14 nonconstant, actual support |k|≤7 (within the planned K=9), emitted on the 2^-895 grid. Exact rounding makes the planned outer terms zero; this explains the term count without making the witness constant or exact by assumption.

Both configuration cutoffs are 10^6 and the largest product support is 32: no stage truncates. Mirror pair counts reproduce 7,994 full and 4,100 low. Both books contain 34 required/provided keys and zero missing/extra keys. Python planning floats choose candidate parameters only; Lean checks exact emitted rational data.

## Validation receipts

All Lean/Lake/kernel tasks ran serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource override, clean/update/cache operation or generated-root rewrite was used. Scratch stayed in `.lake/abi-scratch/sotoyfix2-audit/` and was deleted after recording the receipts.

Build command:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sotoyfix2 KAM.Certificate.Tests.Toy2d KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Rat
[inp-gate] slot 1 acquired 00:52:32 ...
Build completed successfully (3313 jobs).
exit 0
```

Replayed dependencies emitted existing unused-argument/variable warnings in Arith/PiHigh, Expr/Basic, Sound/Static and Sound/Ham; no build failure.

Kernel replay:

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Tests.Toy2d KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy2dData
replaying KAM.Certificate.Tests.Toy2dData
replaying KAM.Certificate.Tests.Toy2
replaying KAM.Certificate.Tests.Toy2d
exit 0
```

Fresh probe command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/sotoyfix2-audit/Probe.lean`, exit 0. It checked the three signed declarations by explicit typed examples, the Hamiltonian expression by `rfl`, positive err by `decide +kernel`, and printed axioms for every public theorem in Toy2d and Toy2. Each of the following gave exactly `[propext, Classical.choice, Quot.sound]`:

```text
toyCert2d_static toyCert2d_hamBounds toyCert2d_embedding toyCert2d_invariance
toyCert2d_energy toyCert2d_gram toyCert2d_torsion toyCert2d_smallness
toyCert2d_passes toyCert2d_freq toyCert2d_torus
toyCert2_passes toyLunarFreq_eq_algFreq toyCert2_freq toyCert2_torus
```

The initial extra Hamiltonian-equality probe used `decide` and failed only because `HamExpr` has no synthesized decidable equality. Replacing that scratch proof with `rfl` gave the successful probe above; production code was not changed.

A recursive local source-import check found 153 KAM modules, no provider imports, and 19 frozen definition anchors, all manifest state SEALED; no unmanifested frozen module or DRAFT_SORRY anchor. The frozen isoenergetic theorem was also read for background, but the toy's actual proof closure goes through the implementation theorem, not through a provider import.

Lean file sizes / maximum Unicode columns: Toy2 60/97; Toy2d 72/100; Toy2dData 186/99. All satisfy 1500/100 limits and have copyright, `module`, public imports, docstrings and exposed public sections. Protected-path diff `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output (exit 0).

Independent capped source replay (scratch file was an exact copy of the 72-line production Toy2d source):

```text
systemd-run --user --scope -p MemoryMax=6G -p MemorySwapMax=0 env LEAN_NUM_THREADS=1 /usr/bin/time -v nice -n 5 lake env lean .lake/abi-scratch/sotoyfix2-audit/Toy2dReplay.lean
Elapsed (wall clock) time (h:mm:ss or m:ss): 1:08.62
Maximum resident set size (kbytes): 4183864
Swaps: 0
Exit status: 0
```

This independently reruns all eight separate `decide +kernel` proofs and the assembled result, rather than trusting imported passes theorems. It verifies feasibility of the production assembly under the cap. The handoff's individual sub-check timing/RSS table and its experimental whole-check decision are prover measurements, not individually repeated here. The experimental whole-check RSS of 6.39 GB is not a claim that RSS was below 6 GB; its successful cgroup run and the separate production assembly are distinct observations. The production source replay above is the independent cap receipt.

Mirror/data commands (outputs redirected only into scratch; Python scripts that create Lean probes inherited `TMPDIR=/root/code/KAM-inp-sotoyfix2/.lake/abi-scratch/sotoyfix2-audit`, `PYTHONDONTWRITEBYTECODE=1`, `LEAN_NUM_THREADS=1`; their Lean subprocesses use `nice -n 5`):

```text
python3 scripts/spin_orbit/toy_gen.py certificates/so-toys/jets.json .lake/abi-scratch/sotoyfix2-audit T2d
T2d passes {'checkStatic': True, 'checkHamBounds': True, 'checkEmbedding': True, 'checkInvariance': True, 'checkEnergy': True, 'checkGram': True, 'checkTorsion': True, 'checkSmallness': True} 2.8s
exit 0

python3 scripts/spin_orbit/toy_keys.py certificates/so-toys/jets.json .lake/abi-scratch/sotoyfix2-audit
T2 OK {'cfgFull': (0, 0, 0, 0), 'cfgLow': (0, 0, 0, 0)}
T2d OK {'cfgFull': (34, 34, 0, 0), 'cfgLow': (34, 34, 0, 0)}
T3 OK {'cfgFull': (0, 0, 0, 0), 'cfgLow': (0, 0, 0, 0)}
TR OK {'cfgFull': (0, 0, 0, 0), 'cfgLow': (0, 0, 0, 0)}
exit 0

python3 scripts/spin_orbit/toy_negative.py certificates/so-toys/jets.json .lake/abi-scratch/sotoyfix2-audit /root/code/KAM-inp-sotoyfix2
all as intended: True  lean controls false: True
exit 0

python3 scripts/spin_orbit/toy_crosscheck.py /root/code/KAM-inp-sotoyfix2 certificates/so-toys/jets.json .lake/abi-scratch/sotoyfix2-audit
jets_identical: T2=true, T2d=true, T3=true
ball slots: T2=20/20, T2d=156/156, T3=37/37, TR=20/20; all identical=true
landed_predicates: all 26 values true
exit 0
```

All 16 negative mutations fail their intended sub-check; all three Lean controls are false. In particular the enlarged-strip denominator mutation fails `checkHamBounds`, and replacing Q by zero fails invariance, energy and torsion. Recomputed negative.json equals the committed file exactly. Regenerated T2d.json equals the entire committed JSON exactly, including verification metadata. Calling `toy_lean_cert.emit(T2d.json, 'toyT2d')` reproduced every emitted declaration byte for byte within Toy2dData; the final handwritten record assigns every corresponding field directly and agrees on the remaining 8/24 settings. Exhaustive JSON leaf comparison against inp isolated the jets change to two T2d constant slots (19,49) and its source string, with no other toy affected. The retained comparison and generation scratch was removed after this audit.

Repository lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1390 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the brief's expressly allowed generated-root staleness. The forbidden-token/escape, resource-limit, size/line-width, module and frozen/ABI checks had no other complaint. `KAM.lean` was left untouched.

`git diff --check` and `git diff inp...HEAD --check` both returned exit 0 with no output. Final status contains only the requested untracked audit report; scratch probes and logs were deleted. No git state-changing operation was performed.


## Notes, uncertainties and errata

1. **Stale project documentation, nonblocking under the explicit signed ruling.** `docs/tracks/SO/design/SO-LEAN-DESIGN.md:720` and `:2025` still say `((3 + cos 2πq)/(3 + cos 2πq))`. `docs/tracks/SO/studies/SO-TOYGEN.md:95–96,120–127` still describe the old a=3 denominator, small strip and 531-term witness; its tables and kernel-cost discussion likewise describe the old data. For example line 127 says `δ = sup|1 − Q(3 + cos 2πq)| ≈ 10^−197`. These are stale descriptions of the concrete chosen toy after the authorized parameter change, not defects in a pinned mathematical source. Reconcile them when integrating; the signed §J ruling and current handoff correctly describe the new choice.
2. **Module move.** Existing T2d names moved from `Tests.Toy2` to `Tests.Toy2d`, with the same namespace and theorem types. Importing only Toy2 no longer exposes them; consumers should import Toy2d. No production Lean consumer of these names was found outside the test modules. The generated root also needs Toy2d, as recorded by lint; audit scope prohibits regenerating it.
3. No suspected new defect in a pinned mathematical source, frozen signature, blueprint G1 node, or native black-box application. No production-code deviation introduced by this auditor. Numerical mirror outputs remain untrusted cross-checks; the checked Lean theorems and kernel replay provide proof evidence. This toy result establishes neither the lunar physical certificate nor a new campaign theorem seal.
