# Independent audit SO-DEFS — 2026-10-29

**Verdict: PASS WITH NOTES for SO-DEFS (definition/checker infrastructure).** No new frozen
anchor or provider is delivered, so no new anchor is seal-ready on this report. The existing
`KAM.Iso.isoenergetic_kam` is manifest `SEALED`; `KAM.Iso.Apost.g1_explicit` is its explicit-constant
implementation theorem, not itself a frozen declaration. No checker-sufficiency failure found.
SO-SOUND must still prove the eight soundness contracts and their assembly; neither these
contracts nor a passing full-dimensional certificate are proved by SO-DEFS.

Audited HEAD `379c70977a60ff6a0516216474fb672ddf6b1608` against `inp`
`db3ae048633635ee90390cf9d71c092fd30de189` using `git diff inp...HEAD` (entire 583-line
addition: two Lean modules and the handoff). Initial worktree status was clean. Read AGENTS,
PLAN, DECISIONS, the requested package brief, handoff/AUDIT FOCUS, current main-worktree
SOSignatures §G, main-worktree SO-LEAN-DESIGN §1/§4 and F2/F3/F7/F8, track-I statement,
frozen IsoenergeticKam and its definition surface, IG1Body, g1_explicit, and the consumed
certificate-engine contracts. SO has design contracts rather than new I/N/P blueprint nodes;
there are no new N/P declarations to audit. The user-specified absolute report destination
overrides the generic brief's main-worktree destination. Production code was left unchanged.

## Signed surface and frozen fidelity

Compared exact declaration strings with
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean:832-995`:

- `CertParams`, `TorusCertificate`, `.D/.H/.K`, `G1Hyps`, `CertifiedTorus`, and
  `checkTorusCertificate`: byte-identical complete declarations.
- All eight sub-check declaration headers through the text before `:=`: byte-identical.
  Their signed bodies are `sorry` placeholders, so the implemented bodies cannot literally
  be byte-identical; this is the intended implementation task, not a signature change.
- The 13 new helper bodies implement the stated §1/§4 operations, with no extra theorem premises.

A default-heartbeat scratch Lean proof instantiated `g1_explicit` with **every** G1Hyps field
in frozen order, supplied external `IsDiophantine`, and obtained `CertifiedTorus` by applying
`hdisp` to each of the last two bounds. It elaborated successfully. A second proof elaborated
`example : type_of% @KAM.Iso.isoenergetic_kam := ...` using the existential triple of explicit
constants and `g1_explicit`, confirming the IG1Body/frozen carrier and binder identity.
There is no new provider or seal body to probe in this package.

Literal qualification of “exactly the hypotheses”: G1Hyps intentionally omits the external
Diophantine premise and adds `hdisp`, the explicit rational displacement upper bound. It also
specializes τ to a natural and the numeric parameters to rationals, per signed §G. Apart from
these explicit design choices, all standing and IG1Body hypotheses are present without
strengthening or weakening: complex/product max norms, derivative operator norms, Gram and
bordered inverse row sums, realness, primary periodicity, exact reference vector, margins and
pointwise/average error laws are retained. CertifiedTorus retains every output clause and
replaces the two identical explicit C2 bounds by `disp`, as signed. It does not assert graph
invertibility, an embedding property beyond this output, or the lunar confinement theorem.

## Declaration inventory

Names below are in `KAM.Certificate`; locators are in `KAM/Certificate/Defs.lean` unless marked Tests.
“PASS” is scoped to the declaration's role, not a soundness theorem for the whole checker.

| Node / role | Lean declaration (line) | Verdict | Reason |
|---|---|---|---|
| §G / helper | `CertParams` (70) | PASS | Signed exact rational/natural parameter data; no proof fields. |
| §G / helper | `TorusCertificate` (91) | PASS | Signed numerical data and untrusted advice; no conclusion bundled. |
| §G / helper | `TorusCertificate.D` (116) | PASS | Literal open strip × coordinate polydisc domain. |
| §G / helper | `TorusCertificate.H` (119) | PASS | Literal HamExpr denotation, not a substituted model. |
| §G / helper | `TorusCertificate.K` (121) | PASS | Literal primary real Fourier embedding denotation. |
| §G / helper | `freqNormLo` (134) | PASS | Finite maximum with zero base; see norm argument below. |
| §G / helper | `ballMagQ` (138) | PASS | Triangle bound |re| + |im| + radius, on actual slot balls. |
| §G / helper | `slotMagQ` (141) | PASS | Zero default matches program semantics; generated tables only. |
| §G / helper | `sumRangeQ` (144) | PASS | Exact finite rational sum over range k. |
| §G / helper | `hamBoundsOk` (151) | PASS | All five necessary derivative bounds, including third partial rows. |
| §G / helper | `angleModel` (162) | PASS | Optional angle displacement with its signed 2π degree. |
| §G / helper | `actionShiftModel` (166) | PASS | Actual action minus rational domain centre. |
| §G / helper | `angleImOk` (173) | PASS | Either uniform displacement or vertical mean-value bound is sufficient. |
| §G / helper | `dkRowUp` (181) | PASS | All n columns in each actual DK row. |
| §G / helper | `d1Slots` (186) | PASS | Exactly 2n generated first-derivative slot references. |
| §G / helper | `dkFreqModel` (190) | PASS | All n terms of DK(sω); degree conversion and key family 5. |
| §G / helper | `invarianceModel` (198) | PASS | Correct Hamiltonian coordinate swap/sign minus DK(sω). |
| §G / helper | `energyOk` (207) | PASS | Degree-zero mean error including coefficient and model radii. |
| §G / helper | `checkStatic` (220) | PASS | Dimensions, all standing inequalities, weights, π and both ray margins. |
| §G / helper | `checkHamBounds` (237) | PASS | Generated jet ball pass; denominator certification and five bounds. |
| §G / helper | `checkEmbedding` (243) | PASS | Domain ball margin and full DK operator-norm bound. |
| §G / helper | `checkInvariance` (254) | PASS | Successful 2n-slot composition and all residual coordinates. |
| §G / helper | `checkEnergy` (263) | PASS | Exactly singleton composition output; average bound. |
| §G / helper | `checkGram` (270) | PASS | Successful exact-dimensional Gram inverse certificate. |
| §G / helper | `checkTorsion` (275) | PASS | Same successful Gram δβ; literal torsion and n+1 average check. |
| §G / helper | `checkSmallness` (285) | PASS | Conservative rational inequalities in the correct direction. |
| §G / helper | `checkTorusCertificate` (293) | PASS | Exactly the signed conjunction of all eight checks. |
| §G / helper | `G1Hyps` (303) | PASS | Exact signed contract; external Diophantine and extra hdisp as explained. |
| §G / helper | `CertifiedTorus` (356) | PASS | Exact signed full analytic output with explicit disp. |
| Tests | `defsToyW` (Tests:29) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyPi` (Tests:31) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyCfg` (Tests:34) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyCos` (Tests:43) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyK` (Tests:46) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyH` (Tests:49) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyB` (Tests:52) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyWit` (Tests:55) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyBox` (Tests:57) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyCC` (Tests:59) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsToyS` (Tests:62) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsTestCfg` (Tests:65) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsTestParams` (Tests:70) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsTestCert` (Tests:75) | PASS | Exact toy/advice construction; no theorem premise. |
| Tests | `defsTest_ham` (Tests:93) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_ham_fail` (Tests:96) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_emb` (Tests:99) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_emb_fail` (Tests:102) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_inv` (Tests:106) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_inv_fail` (Tests:109) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_energy` (Tests:112) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_energy_fail` (Tests:115) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_gram` (Tests:118) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_torsion` (Tests:121) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |
| Tests | `defsTest_static_fail` (Tests:124) | PASS | Kernel-decided stated Boolean result; see coverage limitation below. |

## Sufficiency: every G1Hyps field and its producer

This is an analytic audit of the implemented conditions, not a claim to have completed SO-SOUND.
All computed-enclosure arguments require `[LawfulCertArith α]` as signed in the soundness
contracts. No validity claim is made for an arbitrary unlawful arithmetic backend.

| G1Hyps fields | Actual checker conjunct(s) / structural source | Required bridge |
|---|---|---|
| hn | Static `decide (2 ≤ n)` | Direct extraction. |
| hτ | Static `n ≤ tau + 1` | Natural arithmetic then real casts gives n−1 ≤ τ; also supplies n−1 ≤ τ in ℕ to Constants. |
| hρinf, hρinfρ | Static positivity/order | Cast; derive 0 < ρ. |
| hM, hσK, hσB, hσT, hμ, hγbar, hσω, hν | Each corresponding Static decide | Cast; hσω is 1 < σω. |
| hωstar | Static box length = n and 0 < freqNormLo; external FreqEncloses | Some real coordinate excludes zero. |
| hopen, htransl | Definition D = certDomain | Structural openness and integer translation. |
| hholo | HamBounds successful balls + Static weightH check | `HamExpr.nonvanishingOn_of_balls`, then contDiffOn on open D. |
| hper, hreal | HamExpr syntax | Structural integer periodicity and realness, including real division. |
| hbd | All five hamBoundsOk conjuncts of HamBounds | Slot balls, jet_d1/d2/d3 and NormBridge; details below. |
| hK, hKp, hKr | Definition K = emb.eval | Unconditional differentiable_eval, isPrimaryOnStrip, isRealOnReals. |
| hball | Embedding angle OR bound and action-centre bounds for all i | Vertical path from Re θ; μ-ball uses product/sup norm. |
| hDK | Embedding row sums for every r < 2n | dkModels_encloses and finite operator norm bound by absolute row sums. |
| hG | Gram isSome | gramCheck_sound with σB−μ, validated weight/π, n≥1. |
| hTu, hTb | Torsion's Gram match, torsionModels match, torsionAvgCheck n | torsionModels_sound gives actual frozen torsion enclosure, continuity and exact n+1 shape; torsionAvgCheck_sound gives inverse unit and row sums. |
| hs1, hsσ | Static 1 < s and s < σω | Cast. |
| hν1, hν2 | Static ν ≤ (s−1)L and ν ≤ (σω−s)L | L ≤ ‖ωstar‖ and both multipliers positive. |
| hγ, hγγbar, he0 | Static 0 < γ, γ ≤ γbar, 0 ≤ err | Cast; err nonnegative is needed when multiplying constant dominance. |
| hE | Invariance successful compose and every residual supBound ≤ err | compose_sound length, jet_d1 at Kθ∈D, signed swap, freqModel for external FreqEncloses, all DK terms. |
| hEn | Energy singleton match and energyOk | jet_v0, actual H∘K enclosure, degree zero, Encloses.average and continuity on the real unit cube. |
| hC1, hdisp | Both Smallness rational inequalities | isoC1_le_isoC1Q / isoC2_le_isoC2Q, nonnegative err, positive denominators and rpow_natCast. |

There is no field left without a sufficient conjunct or structural source. Dependencies are
acyclic: Static → HamBounds/Embedding → Invariance/Energy; Gram feeds Torsion; Smallness
uses Static only. For Torsion, Kθ∈D follows by placing Kθ in its own μ-ball (μ>0); the repeated
Gram call is identical, so the same deterministic δβ is supplied, not arbitrary advice.

For hbd, the five inequalities in Defs:152–160 pay respectively DH (total first-partial sum),
X_H (each first partial), DX_H (each Hessian row), D²X_H (each third-partial double row), and
D²H (total Hessian sum). NormBridge:57,78,143,202 provides exactly these operator bounds;
Hamiltonian coordinate swap is harmless because **every** output row is checked. Local
ContDiffAt through order three follows from nonvanishing on the open domain, not an extra premise.
`2 ≤ n` pays the n≥1 requirement of both vector-field bridges.

For hball, the first angle branch bounds |Im U_i| by |U_i|. The second integrates along
Re θ + it Im θ within Tρ; U_i is real on Re θ, and the bound is ρ times the sum of the
coordinate derivative bounds. Therefore either branch gives |Im K_i| < ρ+room (or ≤ with
strictness supplied by the open μ-ball), hence membership in TρH for each μ-near point.
The action bound uses |A_i−centre_i| ≤ r_i−μ and the strict ball displacement <μ. No positive
radius premise is silently needed: a passing action bound with μ>0 forces enough room.

For freqNormLo, FreqEncloses gives |ω_i−c_i|≤r_i and hence |c_i|−r_i≤|ω_i|≤‖ω‖.
The zero fold base is also ≤‖ω‖. Induction through max and box.length=n proves L≤‖ω‖;
negative radii would make FreqEncloses impossible for that coordinate, never a false certificate
with a real enclosed vector. L>0 proves ω≠0. This uses precisely the Pi sup norm, no Euclidean norm.

For Smallness, `isoC1 ≤ (isoC1Q : ℝ)` and `isoC2 ≤ (isoC2Q : ℝ)`, not the reverse.
Multiplication by err≥0 preserves these inequalities. Static supplies all hypotheses of
Constants:665–705. Since ρ>0 and γ>0, denominators are positive. The rational inequalities
therefore imply the signed strict quotient <1 and non-strict quotient ≤disp. For natural τ,
`4*(τ:ℝ)=((4*τ:ℕ):ℝ)` and similarly for 2, so `Real.rpow_natCast` bridges exactly to Nat powers.
No power/exponent weakening or additional disp-positivity check is needed.

## Definitions, defaults and untrusted advice

All new definitions are classified in the inventory: data structures, literal denotations,
finite arithmetic/model constructors, Boolean sufficient conditions, or the signed output
predicate. Toy definitions are concrete test data only. There is no new recursive declaration,
termination escape, junk-valued theorem substitute, proof-bearing certificate field, or assumed
hard step. The existing finite/list computation machinery remains kernel-reducible.

- The certificate contains a HamExpr, **not** a caller-supplied HamJet or slot-ball table.
  HamExpr.jet (Expr/Diff:332) computes all three tables; jet_d1/d2/d3 (:368/384/410) explicitly
  prove the very nested getD reads used here equal the genuine derivatives, for all phase indices.
  Folded derivatives read slot 0; slpCompile_prefix and zero_slot_val identify that slot as zero.
  Slot balls are recomputed by Slp.balls and have the same length as program values (BallRel).
  Thus an absent slot denotes zero consistently, not an underestimated nonzero derivative.
  None from any denominator/exp ball pass rejects HamBounds. Generated denominator slots
  are retained by the existing compiler's nonvanishingOn_of_balls proof.
- Static checks centre/radius/frequency list lengths. All subsequent coordinate reads i<n are
  present. The embedding lists need no length constraint: their absent polynomial components
  denote literal complex zero and absent degree tags denote integer 0, both in emb.eval and
  realCompModel/compDerivModel. Extra entries beyond n are outside the denoted carrier.
  The DK model producer builds all 2n×n entries, including identity in angle rows; missing
  displacement does not erase that identity.
- Slp.compose_sound (Expr/Compose:452) proves output length = requested length. d1Slots has
  length 2n, and swapNat preserves that range. Thus invarianceModel's zero-model fallback
  cannot hide an absent nonzero requested derivative. Energy requires exactly one output.
- Missing exp/inverse/character witnesses reject composition (Compose:140–167 and character
  resolver), rather than denoting arbitrary zero. Empty witness data can legitimately pass a
  Hamiltonian requiring no such witness. The handoff's blanket “missing data denote 0” should
  be read as applying to embedding components, **not** these nonlinear witnesses.
- Gram and averaged torsion reject wrong witness shapes; torsion checks the certificate's own
  n+1 dimension. Entry enclosure contracts require present actual entries (F2/F7).
- Missing or invalid product advice need not reject: Model/Ops:103–117 uses the **sound crude
  enclosure** with zero polynomial and radius sup(a)·sup(b). It may still pass a generous true
  bound; it cannot remove the true product. Packed claims are rechecked. The `.direct` route
  computes the product itself. This is fail-closed in the required semantic sense, not a claim
  that every malformed advice list causes Boolean false.
- Invariance keys `[5,a,l]` have head 5, so are disjoint from composition `[0,...]`, Gram
  `[3,...]`, torsion `[4,...]`, and witness `[1,...]`/`[2,...]`. Advice lookup cannot introduce
  a cross-family collision. All calls for a given family still verify their claimed operation.

## Tests and notes

All 11 new public theorems use `decide +kernel`; kernel replay succeeded. Positive tests cover
HamBounds, Embedding, Invariance, Energy, Gram and Torsion; tightened-bound negative tests cover
only the first four. Static and the full checker have a negative test (n=1, s=1). There is **no**
positive Static/full-checker test, no Smallness test in either direction, no new negative Gram
or Torsion test, and no new malformed-list test. Existing Tests/Torsion contains separate
negative torsion/shape tests, but that is inherited coverage, not a new SO-DEFS test result.
The handoff Tests claim “positive and fail-closed tests per sub-check” (line 14) and the Tests
module docstring's “each fails closed when its bound is tightened” (lines 16–17) overstate this
coverage. This is a documentation/coverage note, not evidence of an insufficient checker.

Duplicated data were checked against Tests/Torsion with a consistent identifier renaming:
all 11 counterparts W, Pi, Cfg, Cos, K, H, B, Wit, Box, CC, S have identical declaration text after
renaming. defsTestCfg separately appends the new invariance family. The original toy definitions
are not exposed across modules; duplication is the declared deviation, with maintenance drift
risk only. Tests data are not exported as a proved full certificate.

## Independent hygiene and validation

All Lean/Lake invocations below were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No budget override was used. Scratch files were confined to `.lake/abi-scratch/` and deleted
at the end. Lint's ABI subprocess ran after kernel replay completed.

1. Targeted gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sodefs KAM.Certificate.Defs KAM.Certificate.Tests.Defs
   [inp-gate] slot 1 acquired 21:25:43 for KAM.Certificate.Defs KAM.Certificate.Tests.Defs
   Build completed successfully (3250 jobs).
   exit 0
   ```

   Replayed dependency warnings only: Arith/PiHigh:218 unused simp argument Nat.succ_eq_add_one;
   Expr/Basic:85 unused variable hS. No warning in either changed module.

2. Probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOAudit.lean
   exit 0; no errors
   ```

   The probe printed axioms of **all 54 named new declarations** (including all 11 test
   theorems), and elaborated the two bridge examples described above. Exact axiom output:

   ```text
'KAM.Certificate.CertParams' does not depend on any axioms
'KAM.Certificate.TorusCertificate' does not depend on any axioms
'KAM.Certificate.TorusCertificate.D' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.H' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.K' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.freqNormLo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ballMagQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotMagQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumRangeQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hamBoundsOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.angleModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.actionShiftModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.angleImOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dkRowUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.d1Slots' depends on axioms: [propext]
'KAM.Certificate.dkFreqModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.invarianceModel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.energyOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkInvariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkGram' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkSmallness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.G1Hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertifiedTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyPi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyCfg' does not depend on any axioms
'KAM.Certificate.defsToyCos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyK' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyH' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyB' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyWit' does not depend on any axioms
'KAM.Certificate.defsToyBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsToyCC' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.defsToyS' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTestCfg' does not depend on any axioms
'KAM.Certificate.defsTestParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.defsTestCert' depends on axioms: [propext, Classical.choice, Quot.sound]
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
   ```

3. Kernel replay (one invocation):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Defs KAM.Certificate.Tests.Defs
replaying KAM.Certificate.Tests.Defs
replaying KAM.Certificate.Defs
   exit 0
   ```

4. Lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1362 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The only lint failure is the explicitly permitted stale generated root. Module checks,
   frozen guard and all 144 ABI hashes pass. No generated file was regenerated.

5. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   `git diff inp...HEAD --check`: empty, exit 0. Targeted forbidden-token/resource-override scan:
   no matches. File sizes 370 and 128 lines; both have copyright, module, public imports,
   module docstring and public section. Defs uses an exposed section, so checker bodies unfold.
   No production provider/DRAFT_SORRY theorem import was added; frozen imports are definitions.

6. `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sodefs KAM.Certificate.Defs KAM.Certificate.Tests.Defs`:
   `short-name check OK (no reused public short name)`, exit 0.

7. Final report whitespace checked with
   `git diff --no-index --check /dev/null docs/tracks/SO/audits/SO-DEFS-audit-1.md`:
   no output, exit 0. Final status contains only this untracked report.

## Errata candidates, deviations and remaining uncertainty

- No suspected pinned mathematical-source defect was identified in this definition package.
- Documentation candidate SO-DEFS-DOC-1: handoff:14 “positive and fail-closed tests per
  sub-check” and Tests/Defs:16–17 “each fails closed when its bound is tightened” are too broad;
  the exact coverage is listed above. Correct the description or add coverage in a later package.
- Documentation candidate SO-DEFS-DOC-2: AUDIT FOCUS handoff:85 calls
  `KAM.Iso.Apost.g1_explicit` the “sealed frozen theorem” and asks for “no hypothesis ... added”.
  The frozen theorem is `KAM.Iso.isoenergetic_kam`; g1_explicit is the explicit-constant theorem.
  Signed §G deliberately adds hdisp and keeps Diophantine external. The package follows that
  signed distinction and the direct application probe succeeds. No silent statement repair.
- Declared deviation: the 11 duplicated toy-data definitions, verified identical after renaming;
  no new implementation deviation introduced by this audit.
- SO-SOUND proof closure and high-dimensional/full-certificate runtime remain outside SO-DEFS.
  The checker is sufficient by the field-by-field analysis above; this report does not replace
  the required formal soundness proofs. n=1 toy success at individual checks cannot establish
  applicability to the n≥2 black box. Duplicate Gram evaluation is a performance note only.

Only this report is retained as an audit edit. No git mutation, source fix, manifest modification,
root regeneration, provider sealing, ledger edit, or external-source change was performed.
