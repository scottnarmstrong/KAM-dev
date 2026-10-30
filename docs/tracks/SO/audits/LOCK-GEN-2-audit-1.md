# LOCK-GEN-2 independent numerics audit 1

**Verdict: PASS WITH NOTES — untrusted numerical study and partial data emitter only.**

The landed Hamiltonian and the emitted design tree agree, including the κ wrapper required by
`lockBarrier_of_exact_torus`. The 3116/3158 distinction is correct. The reported residual and rational
threshold calculations reproduce. An independent rational transcription of the landed ball pass accepts
the four Hamiltonian claims even for the full wrapped program. This is not a certificate acceptance,
Lean proof, kernel replay, or closure of D45. In particular, the Python result called `refinedCore`
does not include Lean's small-divisor site checks.

## Scope, authority, and frozen inputs

Audit date: 2026-10-30. Worktree `/root/code/KAM-inp-lockgen2`, branch `inp-lockgen2`.
Snapshot HEAD `2c293847d3107de7629b40b2efa6bccaefdcd80b`; `inp` and the comparison base are
`7e8f8c0224ec6fd0fab2e3c9707c61076abe57d2`. Locators below refer to this snapshot unless an
external artifact is explicitly named. The initial worktree status was clean.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (including D45),
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, `.drafts/handoff-LOCK-GEN-2.md`,
`docs/tracks/SO/design/SO-LOCK-DESIGN.md` §4.5, and the landed consumer/checker definitions.
Applied the manuscript-audit skill at tier 2, with source comparison, executable checks, and a
separate attempt to refute each finding. No subagents were used. The user's permission envelope
already specified the sole writable report, Python at nice priority on at most two cores, and no Lean.
No repair, commit, data regeneration, process termination, or external gate execution was authorized
or performed by this auditor.

The three-dot diff contains only seven new Python files and the study-note addition (1773 added lines).
All seven files and Parts 2–3 were reviewed. Protected-path diff
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md` is empty.

SHA256 manifest of package inputs:

| File | SHA256 |
|---|---|
| `scripts/spin_orbit/lock_ham.py` | `f67f4e82cfcda9b692a063a2428a57f5396c47ab5ebe9a0f4fcaac65dd910bd2` |
| `scripts/spin_orbit/lock_jet.py` | `492cbf788956a720ca2060f6afda951318e4cb160c907be78003f7f4c8d76c5e` |
| `scripts/spin_orbit/lock_balls.py` | `933872b37d69b6bef682642491e6d7e72c4ab3acde027d911f93b0947ee2f4a4` |
| `scripts/spin_orbit/lock_v2.py` | `afb04683d06973ac737b301de10c44321a77e20a37694b7a8f55517819864d9a` |
| `scripts/spin_orbit/lock_trunc.py` | `34e1a43d1edd1686b3f8f5a2c8677925f1a7ae911e7db9fc4f2b81d878ec4008` |
| `scripts/spin_orbit/lock_emit.py` | `cfeb0d57e85d604386f952ad2cc9b3218393ff0bef3fa187ebd75763fb5f84ea` |
| `scripts/spin_orbit/lock_gate.py` | `42d5f93e5aa7dc076dce0c5b372e7072634d417b16317bc3511f6882b890192f` |
| `docs/tracks/SO/studies/LOCK-GEN-NUMERICS.md` | `d55d2a3af7814df19f3cc7da61b7e0e37737edc17d19f76a380294ec2aa09b46` |

External data root: `/mnt/HC_Volume_106379410/kam-data/so-lock/`.

| Artifact relative to that root | SHA256 |
|---|---|
| `gen2/lockN65_D90x18_rho100.json` | `c2d677875a38112761b43037a3ab1ec9f32fcbd613cabda472ef298a8cdb1575` |
| `gen2/pkg_rho100_mu1000.json` | `9a9868c2e308abf5e3def4a7210af5564679338e20d31e121e05b2c723194d09` |
| `gen2/scan1.json` | `e47bc4f86180a4e340d7b1ebcebd9ca892b124bdc8fd60217d6c51bb290cf7b6` |
| `gen2/trunc1.json` | `b18bb6731484f9e539c07e1eb47a75ba6c4e80b572e34d0209dccd864fe8ce2d` |
| `gate/G1lit.lean` | `9e78f37fd25afcd066cc8843bfd59d0b07a7a2796eaf45b87a065e969de4d0de` |
| `gate/G2_segments.json` | `7fb58f9e79d075962d22cc99a2d4bfca219ce44b75d109e1de2e05c9da1304f3` |

Selected landed reference hashes:

| File | SHA256 |
|---|---|
| `KAM/SpinOrbit/Lock/Coords/HamExpr.lean` | `3cb6ac0a98d41776e8db30e696e9d4adafb3d0aa84d59fbf6c9af604889ae6a7` |
| `KAM/SpinOrbit/Lock/Graph.lean` | `71e53cd713b81f13271ef007f8994b71cd812eb6360a77dd0beffb2bed4c7b29` |
| `KAM/Certificate/Expr/Ball.lean` | `c70b00185b2750438bee38df03f9e96ab84bc3147c55c65e532b0b4ca7bebfdb` |
| `KAM/Certificate/Expr/BallSqrt.lean` | `a1db28f6bc6ef4315a1f06ffdfb209161b374a7221fd1d08c0f8b5218cec3134` |
| `KAM/Certificate/Expr/DiffNodeSqrt.lean` | `c5f5f592327677bba98e2b4a8442e3ab717ee1111247bc887072f9c3b4f0c2dc` |
| `KAM/CertificateSharp/V2/RouteARefined.lean` | `9ed93b16aa04e11450a39539b8993eae3ec8584586fbe93de806b438abf88038` |

## Findings

1. **Medium — the reported “exact refinedCore” is a proper subset of the landed test.**
   `lock_v2.py:406` calls the Fraction routine `v2_q.refinedCore`; the latter's parts are
   `Xs`, `wf`, `okB`, `tail`, and `final` (`v2_q.py:295`). In contrast,
   `KAM/CertificateSharp/V2/RouteARefined.lean:63` explicitly conjoins
   `sitesOk Q w.core.J box w.κ p.γ w.sites`. That conjunct is absent from Python.
   The note's “`refinedCore` holds” and “Certified site constants” at lines 191–193 therefore
   need the qualification **arithmetic subtest with proposed prefix constants**.
   The site constants originate in floating `c_freq × 1.01`; no `BiteWit` acceptance is established.
   Refutation attempt: checked the imported routine and its documentation, rather than inferring
   a gap from the wrapper alone. Its docstring expressly says “the Lean biteOk is NOT mirrored.”
   This disclosure preserves the study's untrusted status, but does not supply the missing conjunct.
   No trusted theorem or production Lean file in this diff consumes the floating result.
   Closeout condition for certificate use: produce and check the sites, BaseFacts, HamFacts,
   FrameFacts, and the full landed test. The present numerical verdict does not discharge them.

2. **Low — κ independence is approximate for the actual computation.**
   Notes line 134 says “thr/κ does not depend on κ”; handoff line 7 says it “drops out exactly.”
   At ρ = 1/100 and μ = 1/1000 the stored log10(threshold/κ) values are:

   | κ | log10(threshold/κ) |
   |---:|---:|
   | 1/2 | −18.036174937418117 |
   | 1 | −18.03482689345352 |
   | 2 | −18.0341096439397 |
   | 4 | −18.033823075481994 |

   Refutation attempt: compared equal ρ/μ rows and inspected scaling in `scan`, rather than
   comparing unrelated packages. `σT = up(1.0101/κ) + μ`, fixed μ, decimal rounding, and the
   discrete X* search are not an exact homogeneous parameter transformation. The discrepancy is
   small and does not undermine choosing κ = 1, but an exact cancellation theorem is not established.
   Likewise, “optimum” means best sampled ρ, and failure of the sampled frame at ρ = 1/50 does
   not prove nonanalyticity there. Closeout condition: qualify these statements or supply proofs.

3. **Medium qualification — the float ball pass predicts claims; it is not an enclosure implementation.**
   `lock_balls.py:14,31` uses a much tighter π bracket than Lean's `piLoQ/piUpQ`, `cmath.exp`
   with an analytic radius instead of the finite Taylor-ball evaluator, and `math.sqrt` instead of
   the nine rational Newton steps. Relative radius inflation does not enclose every possible centre
   rounding error (in particular a zero-radius constant stays zero-radius). NumPy/cmath square roots
   also differ from total `sqrtE` on negative real inputs; Lean's `sqrtE` is zero on that cut.
   `Slp`'s out-of-range-zero semantics and total inverse are not general Python evaluator semantics.
   These differences are harmless only within the declared valid-program/right-half-plane study scope.

   Refutation attempt: first substituted Lean's coarse π bracket on the reconstructed scan domain.
   Predicted d2x moved from 34801.27188161629 to 34801.358556383435, well below 35150.
   Then independently transcribed the actual rational ball rules, including dyadic outward rounding
   at P = 320, nine-step `sqrtAnchor`, finite `certCExp` at Taylor order 30 and its exact remainder,
   and `cexpHalvings`. On the gate's rational domain and the **wrapped 3158-op program**, the
   four exact rational comparisons all pass:

   | Quantity | Rational-pass value, displayed as a float | Claim |
   |---|---:|---:|
   | dh | 1.9073642647131375 | 1.925 |
   | dx | 139.32346879419669 | 140.4 |
   | d2x | 34913.952425783275 | 35150 |
   | d2h | 164.74606693724033 | 166 |

   The domain was `weightH = (1523/100000, 1101/1000)`, centre
   `[37/2500, 49986/100000]`, radius `[2615/1000000, 109/100000]` from `gate/GateLib.lean.inc`.
   This independently supports the numerical sizing claim; it remains an untrusted Python calculation.
   The note's “certified disc pass” / “what the kernel can certify” should identify this distinction.
   The bound sums themselves match `Defs.lean:151` and `V2/HamClaim.lean:29` exactly.

4. **Medium qualification — sqrt witness candidates are plausible, but composition acceptance is pending.**
   `lock_emit.py:254,346–358` supplies exact rational anchor/margin strings, selected using floats.
   The four slot keys are correct, and their following inverse slots have witnesses too:

   | sqrt slot | Function | anchor s | margin d |
   |---:|---|---|---|
   | 17 | √(PΩ/π) | 376/15625 | 493/125000 |
   | 433, 787, 1983 | √(P/(πΩ)) | 195523/1000000 | 32037/1000000 |

   All satisfy `0 ≤ d < s` in Fraction arithmetic. An independent finite-polynomial check expanded
   the real half lattice with conjugates and used `|re|+|im|` coefficients, a rational upper bound
   for exp(2πρ), and the coarse rational π enclosure. It obtained bounds for `‖W−s‖` of
   0.0026290164957281765 and 0.021357857272880386, respectively, strictly below d. For the emitted
   finite P polynomial the corresponding `‖g−s²‖/s²` bounds were 0.2213748734949643 and
   0.22133739354109386, below one.
   Refutation attempt: used conservative rational coefficient bounds instead of trusting the
   generator's float spread × 1.5. This rules out an observed anchor-sign/spread defect in these data.
   It does **not** compute `sqrtResidual`, accumulated input-model radii, or CertFixed arithmetic.
   The remaining literal obligation is the landed `sqrtWitnessRadius` call
   (`Model/SqrtWitness.lean:66`), including `supBound(g−W²)/(s−d)` and its effect on the final residual.
   The JSON's real-series `{zero,half}` encoding also needs expansion into the landed `CertPoly`
   field of `SqrtWitness`; it is an intermediate encoding, not already a typed Lean witness.

5. **Medium qualification — partial emitter and gate coverage are disclosed, and remain partial.**
   Notes P2.7 and the handoff explicitly retain missing `gramInv`, `torsInv`, and a numerical
   `freqBox`; the JSON also lacks complete `weightH`, centre/radius, weight, and `piEnc` fields.
   Its `params.domain` contains only rhoH and r1. The emitter docstring's “landed TorusCertificate
   format” is consequently an intended target, not the literal complete schema. No complete
   route-A witness/caps/site payload is emitted by `final_check`, either. `package_params` does
   not reject disagreement between CLI rho/κ and a supplied package row; current emitted values
   do agree, so this is a future-use validation risk rather than a defect in this artifact.

   The gate still measures the bare tree. Verified `G0_emit.lean` versus its `.orig-3158` backup:
   only the stated length correction, `lockN` guard, and tail-location correction occur. All nine
   literal printer comparisons (G1 plus eight G2, including the four archived tails) pass byte for
   byte. All eight segment-manifest hashes agree. Old tail lengths are 358/758; new intended starts
   are 2716/2316 for L = 400/800. The corrected tail probes do not yet exist in the gate root.
   Refutation attempt: checked the archived files and manifest against actual program slices,
   not merely the manifest's stored `printer_checks`. There is no op-order mismatch, but a hash
   is not a ball-equation proof. Existing `.out` files were read as historical receipts only.
   The gate's pending full bridge and corrected probes require later authorized Lean work.
   `lock_gate.main` was deliberately not run: it rewrites and moves external data.

6. **Process deviation — the reported pkill cannot be certified as affecting only its author's job.**
   Handoff line 41 records `pkill -f "lock_v2.py claims"` and says “It matched only my own job.”
   Name matching is broader than an explicit PID and could match another worker or a shell command
   containing that text. This is a real disclosed deviation, not a mathematical defect.
   Refutation attempt: searched the package and available handoff for command/process evidence;
   found the admission but no contemporaneous PID/match list proving the claimed exclusive impact.
   Neither collateral damage nor the absence of collateral damage is established here. No process
   was killed during this audit. The separate handoff admission that full lint invoked Lake and
   populated `.lake/packages` is also historical; this auditor did not repeat or clean it up.

## Surface-by-surface assessment and definition classification

| Surface | Assessment | Reason |
|---|---|---|
| `lock_ham.lock_ham_expr`, design form | PASS for Ω = 8/65, the stated nonempty centre | Same right nesting, rational coefficients, forcing order, skipped m = 2 sine, sqrt radicands, trig phases, and powers as `HamExpr.lean:40–108` |
| `lock_ham_scaled` and emitted ham text | PASS | `.mul (.const κ) lockHamExpr`, as `Graph.lean:85` requires; JSON text equals current printer output |
| `lock_jet` | PASS on the package program | All 3116 ops and all five HamJet fields match G1lit; wrapper adds one const and 41 products |
| Generic numerical evaluators | PASS WITH NOTES | Restricted valid inputs/right-half-plane only; not total Lean semantics on all carriers |
| `lock_balls` and bounds | PASS WITH NOTES | Structurally faithful sizing predictor; independently checked exact rational claims, finding 3 |
| `lock_v2`, `threshold`, `final_check` | PASS WITH NOTES | Correct inspected rational schedule/constants/final comparisons; omits sitesOk and uses proposed input bounds |
| `lock_trunc`, `lock_emit.residual` | PASS as sampled measurements | Actual emitted real polynomial reproduces residual; no analytic alias/tail enclosure |
| `sqrt_witness`, `classify_witnesses` | PASS WITH NOTES | Correct slots, signs, anchors and margins for this instance; model acceptance pending |
| `package_params`, JSON assembly | PASS WITH NOTES | Partial data description; current parameters agree; no full certificate consumer acceptance |
| `lock_gate` | PASS WITH NOTES | Printer/slices/hash correction verified without mutation; bare-tree scope and pending tails retained |
| Notes Parts 2–3 | PASS WITH NOTES | Measurements reproduce; exactness/certification wording and scaling need the qualifications above |

The alternative `form="lean"` is an explicitly labelled conditional algebraic simplification, not the
landed tree and not used in the audited emitted data. Python `add_all` requires a nonempty input, while
Lean's `lockAddAll []` is zero; Ω = 0 also falls outside the Python rational reciprocal's domain. These
are scoped generator functions, not replacement definitions on the whole Lean carrier.

## Verification evidence

All Python invocations used the following prefix, with inline programs supplied on stdin and no probe files:

```sh
env PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2 \
  MKL_NUM_THREADS=2 NUMEXPR_NUM_THREADS=2 nice -n 10 taskset -c 0,1 python3 -
```

The affinity restriction limits the whole invocation, including child processes, to CPUs 0 and 1.
No Lean, Lake, or leanchecker command ran. No emitted data or gate artifact was modified.

Checks and observed output:

- `git diff --stat inp...HEAD`, `git diff --numstat inp...HEAD`, file inspection of all additions;
  protected-path diff empty; `git diff --check inp...HEAD` exit 0.
- `compare_jets(jet(2, lock_ham_expr(...)), parse_jet_lit(G1lit))`:
  `{'lengths': (3116, 3116), 'first_diff': None, 'roots': True}`.
- Wrapped census: 3158 ops; const 309, action 5, char 56, add 775, mul 1997, exp 4, inv 8, sqrt 4.
  Nonzero output entries: 1 + 4 + 9 + 27 = 41. Heavy products energy/invariance/torsion: 5/24/128;
  full-program MM count 1026. These reproduce P2.1/P2.6.
- Independently evaluated the compiled program at one real and two complex right-half-plane points
  against `lock_ham_jet`; maximum normalized errors in orders 0–3:
  `[4.24e-21, 3.55e-18, 5.54e-16, 7.26e-15]`. This is a numerical cross-check, not an interval proof.
  An initial attempt to use the documented real-only `prog_values` at complex points raised TypeError;
  the auditor replaced that probe evaluator with an inline cmath character evaluator. No package fix.
- `final_check(pkg, Fraction(9,10**20))`: X* = 59/125, disp = 169/5000000000000000 = 3.38e-14;
  `okB=True`, arithmetic parts `Xs,wf,okB,tail,final=True`.
  At `Fraction(5,10**19)`: X* = 263/100, disp = 1.89e-13; `okB=False`, arithmetic result false.
- `threshold(lock_package(...), rational_claims)`:
  `log10_thr=-18.03482689345352`, X* = 121/50,
  `log10_disp_coef=5.575893439046467`, binding `['J2 tail']`, `ok=True`.
  Inspected `StepQ`, `NumQ`, and `finalOkA` against `v2_q`; finding 1 is the substantive missing test.
- Reconstructed the **actual emitted** real embedding from its mantissas and conjugate half lattice,
  converted precision 112 back to S = 101, and called
  `lock_emit.residual(Grid(), tr, 101, Fraction(1,100), Fraction(1))`.
  It ran in 101 seconds and reproduced every stored weighted and grid-sup statistic:

  | Row | Weighted residual | Grid sup |
  |---|---:|---:|
  | α | 5.0836621362576097e-20 | 1.952316852089764e-21 |
  | I | 2.096690193784097e-23 | 4.241307424109739e-25 |
  | J̃ | 3.513761137701461e-24 | 1.0014400508652901e-25 |
  | Energy | 9.435428721515188e-25 | 2.771548043049682e-26 |

  Half-term counts: 1636/1576/1509. Finite grid FFT norms do not enclose unresolved Fourier tails,
  aliasing, witness error, or rounding radii. This rerun did not regenerate the upstream Galerkin solution.
- Exact rational finite-polynomial sqrt checks and the independent 320-bit rational ball transcription:
  findings 3–4. The latter used `ballRound`'s scale
  `2^(P-(log2 |num m| - log2 den m))`, downward-rounded centre coordinates, upward-rounded radius
  including centre shifts; `sqrtNewton` nine times; `expAux` N = 30 with remainder
  `32/(31! * 31)` and rounded repeated squaring. All operations used Fraction; comparisons were exact.
- Source-only lint adaptation: read `scripts/lint_sources.sh` into memory and ran it with
  `sh -c <text> scripts/lint_sources.sh`, replacing **only** its `abi_hashes.py ... --check` invocation
  with `printf '%s\n' 'ABI SKIPPED: no Lean authorized'`. The on-disk script was not edited.
  The ABI tool launches `lake env lean`, so the unmodified full lint would violate the audit's no-Lean scope.
  Output: `check_lean_modules: PASS (1689 Lean files, 0 comparator configurations)`,
  `FROZEN-ANCHOR GUARD OK`, `ABI SKIPPED: no Lean authorized`, `source-only lint exit 0`.
  Other source checks were silent. Full lint/ABI, targeted Lean builds, #print axioms, and kernel replay
  are **not run**, rather than reported as passing. There are no new Lean declarations to axiom-audit.

## Closeout and remaining scope

All six requested audit questions are addressed. No tree mismatch, missing sqrt-slot witness,
incorrect derivative coefficient, or refutation of the recommended numerical threshold was found.
The current diff introduces no trusted floating-point dependency: it contains no Lean implementation
or acceptance proof, and the landed checker still requires its own rational/backend tests. The numerical
data must remain untrusted until those tests are proved for the complete certificate.

The 12–100 CPU-hour estimate is explicitly a projection from product counts, assumed size/width
exponents, and R2 timings; this audit did not measure a lock kernel run. The pruned count is not the
cost of the currently unpruned 3158-op composition. Notes identify this limitation, the empty advice
books, the 1.8 residual margin, sampled frames, proposed bordered torsion bound, and missing graph check.
The sharper-Ham-pass benefit is also a projection. No claim about a certified periodic centre, final
confinement theorem, novelty, or reading Celletti (1994) in full follows from this study.

Suspected pinned-source errata: none identified. In-repository issues are the exact-scaling and
certification wording above, the superseded sizing projection, and the design's insufficiently explicit
mention of reciprocal witnesses emitted by sqrt differentiation. No production changes were made.
The sole audit modification is this report. No requested mathematical check is silently promoted to a
Lean proof or seal-ready result.
