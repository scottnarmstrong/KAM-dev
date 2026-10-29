# SO-TEST-B independent audit 1

Verdict: **PASS WITH NOTES** for the SO-TEST-B test package. All ten negative-test items and both whole-checker positive controls satisfy the handoff's stated scope. The packed model route and fallback satisfy their stated contracts. The handoff has a false generator instruction about invariance advice keys (finding N1 below). No frozen anchor is provided or sealed by this package; provider/frozen type equality and seal-body probes are not applicable.

## Scope and authority

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/SO/audits/SO-TEST-B-handoff.md`. The user's exact report destination overrides the generic brief's main-worktree destination. Design authority for these tests is `/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md:730-760`, rather than an I/N/P theorem blueprint. No frozen mathematical definition or statement is changed or implemented by these fixtures.

Audited HEAD `49b3661ffcf582668c2f49aa4c7004b0669a24d6`; inp at start `6cc8c0e509fe0f60c41c49ebe065a4a595cb4973`; merge base `302963ff1dda8363f983a5e10f3b24c9f0ba38cb`. Read the full `git diff inp...HEAD`. It contains six files, 888 additions: the two package test modules, their handoff, and inherited SO-GRAPH modules `KAM/SpinOrbit/Graph/Cert.lean`, `KAM/SpinOrbit/Tests/GraphCert.lean` and their handoff. Those inherited graph additions were inspected to establish the full diff scope; this is not an independent SO-GRAPH proof/seal audit. They do not alter the checker or the existing packed tests.

## Declaration results

All names in the following tables are in `KAM.Certificate`. Locators abbreviate `KAM/Certificate/Tests/{Negative,Packed}.lean`.

| Node | Lean declaration | Verdict | Evidence / scope |
|---|---|---|---|
| control | `negBase_passes` (Negative:111) | PASS | Whole checker true; no Diophantine existence claim. |
| §8.1 | `negResidual_fails` (Negative:118) | PASS | checkInvariance false and whole checker false. |
| §8.2 | `negGramZero_fails` (Negative:124) | PASS | B=0: checkGram false and whole checker false. |
| §8.2 | `negGramTwo_fails` (Negative:129) | PASS | B=2I: checkGram false and whole checker false. |
| §8.2 | `negTorsZero_fails` (Negative:134) | PASS | S=0: checkTorsion false and whole checker false. |
| §8.3 | `negMu_fails` (Negative:142) | PASS | μ=0: checkStatic false and whole checker false. |
| §8.4 control | `negExp_control` (Negative:161) | PASS | E=1: checkInvariance true at err=1/1000; sub-check control. |
| §8.4 | `negExp_fails` (Negative:163) | PASS | E=2 at the same err: checkInvariance false and whole checker false; pin mean error is paid as radius. |
| §8.5 | `negWeight_fails` (Negative:170) | PASS | w=1: checkWeight, checkStatic and whole checker false. |
| §8.6 control | `negDiv_passes` (Negative:192) | PASS | Q=2, radius=1/50: whole checker true. |
| §8.6 O2 | `negDivBall_fails` (Negative:196) | PASS | Only radius enlarged to 1: checkHamBounds and whole checker false. |
| §8.6 O2 | `negDivWit_fails` (Negative:202) | PASS | Only Q replaced by zero: checkInvariance and whole checker false. |
| §8.7 F1 | `negBoxZero_fails` (Negative:209) | PASS | Box containing zero: checkStatic and whole checker false. |
| §8.7 F1 | `negRay_fails` (Negative:214) | PASS | nuRay=6/10: checkStatic and whole checker false. |
| §8.8 O3 | `negPi_fails` (Negative:225) | PASS | Narrow enclosure: checkPiEnclosure, checkStatic and whole checker false. |
| §8.9 control | `negOne_torsion` (Negative:298) | PASS | One-angle fixture passes checkTorsion; no whole positive control asserted. |
| §8.9 control | `negPerm3_selfInverse` (Negative:305) | PASS | Explicit rational 3×3 permutation squares to I; imaginary parts all zero. |
| §8.9 F7 | `negPerm3_fails` (Negative:313) | PASS | Only S changed to 3×3: checkTorsion and whole checker false; shape guard is the relevant rejection. |
| §8.10 F10 | `negChar_pin_fails` (Negative:340) | PASS | h=0: compose none, checkInvariance false, whole checker false. |
| §8.10 control | `negChar_pin_passes` (Negative:346) | PASS | Only h changed to 2: compose some and checkInvariance true. |
| packed | `packedTest_model_packed` (Packed:269) | PASS | Nonempty polynomial and rad.m ≤64 (=radius≤4). |
| packed fallback | `packedTest_model_fallback` (Packed:278) | PASS | Bad decoder: empty polynomial and rad.m>64 (=radius>4). |
| packed contract | `packedTest_model_packed_encloses` (Packed:286) | PASS | Instantiates unconditional Encloses.mul on packed route from the two input enclosures. |
| fallback contract | `packedTest_model_fallback_encloses` (Packed:294) | PASS | Same multiplication contract on fallback; no assumed output enclosure. |

Each concrete positive/negative computation uses `decide +kernel`. The two enclosure theorems use `CertModel.Encloses.mul`, with hypotheses on the input functions only. No hard proof step or conclusion is assumed. Whole-checker false is never used alone to establish the intended failure.

Items 4, 9 and 10 use exactly the exceptions expressly allowed by the audit focus. For item 4 the wrong mean increases the pin-error radius, and the invariance bound fails; it need not make the Option-valued exp composition fail. Both witnesses use the same loose residual allowance. For item 9, the unchanged one-angle certificate already fails whole static constraints (s=1); the positive torsion control and the wrong-size witness isolate the intended stage. `Torsion/Average.lean:106-110` checks the exact (n+1)×(n+1) shapes before inverse bounds. For item 10, the composition success/failure itself is included, with the invariance flip at the same error allowance. Nonzero radii/positive err and disp=0 mean these sub-check controls are not whole-checker positive controls. There is no claim of a Diophantine torus from the resonant rational base.

## Definition classification

Every new definition is explicit test data or a fixture constructor on its declared carrier; no new production def/abbrev/structure is introduced. Deliberately invalid witnesses are rejection inputs, not mathematical objects used to bypass a proof. The production crude fallback is the intended sound enclosure, not an unsound junk value.

| Definition | Classification / verdict | Meaning |
|---|---|---|
| `negCfg` (Negative:57) | Test data / PASS | Finite direct-advice fixture; surplus keys are harmless, including unused [5,a,l]. |
| `negK` (Negative:68) | Test data / PASS | Constant-angle-shift/action embedding on the declared two-angle carrier. |
| `negH` (Negative:72) | Test data / PASS | Expression J + p²/2. |
| `negConst` (Negative:75) | Test data / PASS | Two-index zero-mode constant polynomial. |
| `negB` (Negative:78) | Test data / PASS | Explicit two-dimensional cI Gram witness. |
| `negCC` (Negative:81) | Test data / PASS | Entrywise real-to-complex rational data conversion. |
| `negS` (Negative:84) | Test data / PASS | Explicit bordered torsion inverse for this toy. |
| `negParams` (Negative:86) | Test data / PASS | Explicit small-strip parameter record; no theorem premise hidden. |
| `negPi` (Negative:91) | Test data / PASS | Machin enclosure data (5,2). |
| `negBase` (Negative:93) | Test data / PASS | Explicit resonant checker-only certificate; whole checker positive control. |
| `negResidual` (Negative:116) | Test data / PASS | Single frequency-centre mutation of negBase. |
| `negExpH` (Negative:150) | Test data / PASS | Expression J + (p²/2) exp 0. |
| `negExp` (Negative:154) | Test data / PASS | Parameterized witness/error fixture; tested at fixed err=1/1000. |
| `negDivH` (Negative:179) | Test data / PASS | Expression J + (p²/2)(p/p). |
| `negDiv` (Negative:185) | Test data / PASS | Division fixture parameterized by reciprocal polynomial and domain radius; M=150. |
| `negPiNarrow` (Negative:223) | Test data / PASS | Deliberately insufficient enclosure, used only for rejection. |
| `negOneW` (Negative:234) | Test data / PASS | One-angle weight fixture. |
| `negOnePi` (Negative:236) | Test data / PASS | One-angle Machin enclosure fixture. |
| `negOneCfg` (Negative:239) | Test data / PASS | Finite advice configuration for the one-angle torsion fixture. |
| `negOneCos` (Negative:248) | Test data / PASS | One-angle cosine in real half-spectrum format. |
| `negOneK` (Negative:251) | Test data / PASS | Explicit one-angle nonconstant embedding. |
| `negOneH` (Negative:254) | Test data / PASS | Expression I²/2. |
| `negOneB` (Negative:257) | Test data / PASS | Explicit one-angle approximate Gram inverse polynomial. |
| `negOneWit` (Negative:260) | Test data / PASS | Empty nonlinear witness lists. |
| `negOneBox` (Negative:262) | Test data / PASS | One-coordinate rational frequency box. |
| `negOneCC` (Negative:264) | Test data / PASS | Entrywise rational-to-complex conversion. |
| `negOneS` (Negative:267) | Test data / PASS | Explicit 2×2 bordered inverse approximation. |
| `negOneTestCfg` (Negative:270) | Test data / PASS | Extends negOneCfg with redundant scalar-route invariance keys. |
| `negOneTestParams` (Negative:275) | Test data / PASS | Parameterized one-angle data; not claimed to satisfy the whole checker. |
| `negOneTestCert` (Negative:280) | Test data / PASS | One-angle torsion-only fixture with explicit domain default 1/10. |
| `negPerm3` (Negative:302) | Test data / PASS | Deliberately wrong-size 3×3 self-inverse permutation witness. |
| `negCharH` (Negative:322) | Test data / PASS | Expression J+p²/2+cos(2πq)/1000. |
| `negChar` (Negative:328) | Test data / PASS | Quarter-angle pin fixture; only halving count varies between the controls. |
| `negCharCompose` (Negative:336) | Test data / PASS | Exact composition call used by the character invariance stage. |
| `packedTestCfg` (Packed:256) | Test data / PASS | Packed advice under key [9], parameterized by the candidate decoder. |
| `packedTestBadDec` (Packed:261) | Test data / PASS | Deliberately wrong decoder (+1), tested as rejected untrusted data. |
| `packedTestModelA` (Packed:264) | Test data / PASS | Degree-zero fixed-point polynomial model, radius zero. |
| `packedTestModelB` (Packed:266) | Test data / PASS | Degree-zero fixed-point polynomial model, radius zero. |

## Findings and design fidelity

**N1 — Incorrect handoff claim; SO-PYALIGN is correct.** `SO-TEST-B-handoff.md:59-60` says: “The Lean checker needs them for exact products” and “Generators must emit them,” referring to `[5,a,l]`. This is false in this checkout. `Defs.lean:190-194` supplies `freqModel` as the first factor of every such product. `Torsion/Models.lean:84-90` defines this through `ballModel` with the constant polynomial from `constModel`; `Expr/ComposeModels.lean:59-60` gives that polynomial one all-zero key. `Model/Ops.lean:83-95` takes the constant-factor `directItems` route before `adviceLookup`. This holds even for a frequency ball with nonzero radius: its radius contributes cross terms, but does not change the constant polynomial. The same reasoning covers `[4,10,i,j,l]`. Generators need no advice for these products. Keeping surplus direct keys in the tests is harmless. Independent scratch probes copied the fixture definitions into a fresh namespace and proved by `decide +kernel` that **both negBase and negDiv still pass the entire checker when both advice books are empty** (exit 0). Thus even all advice entries are redundant for these two controls, a stronger concrete check than removing only `[5,a,l]`. The locally absent study was read at `/root/code/KAM-inp-sopyalign/docs/tracks/SO/studies/SO-PYALIGN.md`, §1 advice-key table and §6.1; its claim matches the audited Lean bodies.

**N2 — Scope of packed fallback evidence.** The two inputs have nonconstant polynomials, so `polyProduct` reaches the `.packed` advice at `[9]`. The existing `packedTest_wrongDecoder`/packed rejection tests and the new output tests establish rejection of the +1 decoder and selection of the crude branch in `Model/Ops.lean:114-116`. The fixed-point backend is `CertFixed 4`, hence 64 mantissa units are 4. The enclosure contracts hold on both routes. There is no whole CertFixed certificate whose eventual margin fails here; the demonstrated failing margin is the model-radius threshold 4. This is accurately disclosed in the handoff and is accepted at the requested model scope.

**N3 — Landed code integrity.** `git diff inp...HEAD -- KAM/Certificate/Defs.lean KAM/Certificate/Sound KAM/Certificate/Soundness.lean` is empty. A comment/whitespace-masked comparison against `git show inp:KAM/Certificate/Tests/Packed.lean`, after removing only the new import and model-level section, returned exact equality. Packed's prior definitions, theorem statements and proofs are unchanged: the diff adds one import, documentation, and the new model-level block only. No production checker or soundness definition is changed. No new imported provider or DRAFT_SORRY anchor appears in the two test modules.

No suspected defect in a pinned mathematical source was found. N1 is a project handoff/documentation defect, not a published-source erratum. The declared use of a hand-built TR-like base instead of JSON is a scoped test-data deviation. No default-heartbeat design failure was observed.

## Independent checks

All audit-owned Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`; no resource-budget override was used. Scratch fixture copies were used because test definitions are not exposed for downstream unfolding. These copies introduced no production declarations or repository changes.

1. Targeted gate (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sotestb KAM.Certificate.Tests.Packed KAM.Certificate.Tests.Negative
   ```

   Output: `[inp-gate] slot 2 acquired 22:22:14 for KAM.Certificate.Tests.Packed KAM.Certificate.Tests.Negative` and `Build completed successfully (3251 jobs).` Only replayed warnings: PiHigh.lean:218:8 unused simp argument `Nat.succ_eq_add_one`; Expr/Basic.lean:85:5 unused variable `hS`. No warning in the audited test files.

2. Kernel replay, single invocation (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Tests.Negative KAM.Certificate.Tests.Packed
   ```

   Exact output:

   ```text
replaying KAM.Certificate.Tests.Packed
replaying KAM.Certificate.Tests.Negative
   ```

3. Axioms and refutation probes (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/maud-sotestb-1.lean
   ```

   The scratch file imported both audited modules; printed the axioms of all **24** new public theorems (20 Negative, 4 Packed); copied the explicit Negative fixture definitions under a fresh namespace; and checked three `decide +kernel` examples: negBase with both advice books empty passes the whole checker; negDiv with both advice books empty passes the whole checker; `listShapeOk 2 negPerm3 = false`. All three examples elaborated with no diagnostic. Full axiom output:

   ```text
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
'KAM.Certificate.packedTest_model_packed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_model_fallback' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_model_packed_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packedTest_model_fallback_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Source lint (serialized after replay and probes), exit **1**, with only the expressly permitted stale generated-root finding:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exact output:

   ```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1382 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
   ```

   Thus no forbidden proof escape, resource override, size/line-length or module-format violation was reported; the frozen-anchor guard and all 144 elaborated ABI hashes passed. The generated root was not edited.

5. Short-name check (exit **0**):

   ```sh
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sotestb KAM.Certificate.Tests.Negative KAM.Certificate.Tests.Packed
   ```

   Output: `short-name check OK (no reused public short name)`.

6. Integrity: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output. The production-checker/soundness diff in N3 was also empty. `git diff --check inp...HEAD` and `git diff --check` exited **0**, no output. `wc -l` gave Negative **350**, Packed **393** (both below 1500); both have copyright, `module`, public imports, module docstrings and `public section`. Final `git status --short` shows only the untracked requested audit report.


## Limits and disposition

Accept the test code at its stated scope, with the generated-root lint exception allowed by the brief. Correct the handoff's invariance-key instruction before using it to guide generators. Do not infer an existence theorem, seal readiness of an I/N/P anchor, a whole-certificate packed fallback test, or independent SO-GRAPH closure from this receipt. Only this report was edited in tracked repository space; audit probe files were confined to `.lake/abi-scratch/` and removed after checks. No state-changing git command was used.
