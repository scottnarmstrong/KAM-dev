# SO-MALG independent audit 1

Verdict: **PASS WITH NOTES** for the complete SO-MALG signed slice. All six enclosure contracts
PASS with their exact signed types; no mathematical or hygiene blocker was found. The only lint
failure is the explicitly permitted stale generated root. No frozen theorem anchor/provider belongs
to this package, so “seal-ready” here means the signed model-algebra slice is proved and ready for
integration; it does not seal any I/N/P or SO headline theorem.

Audit checkout: `/root/code/KAM-inp-somalg`, branch `inp-somalg`, HEAD
`b0ac8009e4a100a20315dc7b13eb5c0d1a89fcce` (audit-request commit after the handoff's
`78ddce05`). Comparison: `git diff inp...HEAD`, with `inp` observed at
`ea8a898deee18161fdbd255f2c706fbf389dc5ef`, merge base
`b339e88f44efb2e5b0fa342c12afad0850a6cd51`. All three Lean files are additions;
the remaining diff is `docs/tracks/SO/audits/SO-MALG-handoff.md`.

Scope: only `KAM/Certificate/Model/{Terms,Ops}.lean` and
`KAM/Certificate/Tests/Model.lean`. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the handoff including AUDIT FOCUS.
The controlling source is the accepted Revision 7 design
`/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md` §1.5–6, §1.12/16, §2,
§7 SO-MALG and Appendix A §C; exact signatures are
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean:482–555`.
There is no `docs/tracks/SO/statement.md` in this checkout and no I/N/P blueprint node or frozen
provider export is assigned to this SO infrastructure slice. The signed SO design, not unrelated
I/N/P anchors, controls this audit. The only frozen dependency is the SEALED definition
`KAM.complexStrip`, which was read. The explicit user destination overrides the generic brief's
main-worktree destination. Only this report is changed outside ignored scratch/build artifacts.

## Signed surface and proof review

All 12 declarations, fully within `KAM.Certificate`, match the signed source modulo whitespace,
including docstrings and every `ModelConfig` field. The supplied signature checker and a separate
header/field comparison both passed. Fresh declarations copied from the signed source elaborate
with direct applications of the five implemented functions and six implemented contracts. No
implicit standing premise, changed carrier, changed degree, weakened conclusion or wider constant
dependence was found. There is no frozen seal body to test in this package.

| Signed enclosure contract | Verdict | Direct proof application against copied signed header |
|---|---|---|
| `CertModel.Encloses.add` | PASS | `CertModel.Encloses.add hW ha hb hdeg` |
| `CertModel.Encloses.mul` | PASS | `CertModel.Encloses.mul hW cfg key ha hb` |
| `CertModel.Encloses.trim` | PASS | `CertModel.Encloses.trim hW eps ha` |
| `CertModel.Encloses.toDeg` | PASS | `CertModel.Encloses.toDeg hW hpe d ha` |
| `CertModel.Encloses.ofDeriv` | PASS | `CertModel.Encloses.ofDeriv hW j d P` |
| `CertModel.Encloses.average` | PASS | `CertModel.Encloses.average hρ ha hf` |

At `Terms:327–394`, merge soundness preserves all input error budgets and adds coefficient
rounding; it does not require sortedness, uniqueness, a fixed key length or positive input error
fields. `Terms:427–494` handles every row in direct multiplication. `Terms:499–535` transfers
every dropped coefficient norm into its old error budget, including at cutoff zero.
`Ops:241–273` uses this to pay for rounded addition in the correct strip weight.

At `Ops:83–94`, either all-zero-key factor bypasses advice; the second-factor case commutes
the exact product. Soundness uses the full direct-product lemma, so it does not assume that a
“constant” has one stored term. Otherwise direct advice uses the same lemma, and packed advice
uses the landed `CertPoly.mulPacked_sound`. Missing keys and rejected packed checks select the
explicit empty-polynomial bound. At `Ops:332–395`, the proof splits on exactly this computed
option and proves both branches. With `C=(2π)^deg_a`, `D=(2π)^deg_b`, it uses
`XY-CDQ = CD(AB-Q) + CA(Y-DB) + DB(X-CA) + (X-CA)(Y-DB)`.
The successful branch adds truncation/rounding, both polynomial-radius cross terms and the
radius-radius term. The fallback radius is `(norm_a+rad_a)(norm_b+rad_b)` in running symbolic
degree `deg_a+deg_b`. Radius nonnegativity is derived from enclosure at zero on the positive-width
strip, not imposed as an extra input. The `crossUp` shortcut uses `beq_sound`.
No property of the untrusted decoder or advice is assumed.

At `Ops:397–427`, trim partitions the original list by a Boolean predicate and pays the full
weighted norm of the dropped part. Its enclosure theorem is valid for arbitrary thresholds,
including negative ones; it does not rely on a completeness property of backend comparison.

At `Ops:133–174,479–539`, both signs of the integer degree change are enclosed using Machin
bounds strengthened by fixed pi bounds. The lower endpoint is strictly positive even for `(0,0)`
parameters, so inversion for negative powers is sound. For the rounded upper centre `c` and
rounded lower endpoint `lo`, `r` dominates `c-X`, where `X=(2π)^(deg-d)`. The new radius pays
`c*rad + r*norm(P) + scale-rounding`. The supplied `hpe` is retained with exactly the signed type;
its enclosure fact is recorded but is not needed, since the Machin bounds hold for all parameters.
This is stronger internal reasoning, not a changed public statement.

At `Ops:542–644`, differentiation is of the exact polynomial, with coefficient `ik_j c`,
period-one factor `2π`, and degree `d+1`. Zero-extended list access covers every key. The signed
contract takes `j : Fin n`; the total implementation also accepts natural indices. At
`Ops:649–694`, average uses the literal zero Fourier coefficient (summing duplicate or padded
keys), continuous real restrictions and an integral norm bound. Its continuity premise is signed.
No periodicity premise is silently introduced.

## Complete declaration inventory and definition classification

Each explicit new public declaration has one row below (126 total: 64 definitions/data declarations
and 62 theorems). All names have prefix `KAM.Certificate.`. `T`, `O`, `X` mean the exact scoped
files `Model/Terms.lean`, `Model/Ops.lean`, `Tests/Model.lean`. The classification covers every
new `def`, `abbrev` and `structure`; no junk-value proof shortcut was found. In particular, the
crude product fallback is the intended proved enclosure, and optional failure is not treated as
successful packed arithmetic. Unsigned helpers have their own names and retain their ordinary
numeric/typing premises rather than standing in for a stronger source theorem.

| Node / locator | Lean declaration | Verdict | Classification / reason |
|---|---|---|---|
| SO-MALG T:31 (abbrev) | `ErrTerm` | PASS | Data alias: stored key, rounded coefficient, error budget; no invariant hidden. |
| SO-MALG T:34 (def) | `keyDeg` | PASS | Total stored-list l1 degree; overestimates the visible degree of padded keys. |
| SO-MALG T:37 (def) | `keyCmp` | PASS | Total lexicographic comparison, structurally recursive on key lists. |
| SO-MALG T:43 (theorem) | `keyCmp_eq_eq` | PASS | Equality branch implies literal key equality; no converse/order assumption needed. |
| SO-MALG T:57 (def) | `CC.addC` | PASS | Rounded backend complex add; intended on the whole coefficient carrier. |
| SO-MALG T:60 (def) | `CC.addErrC` | PASS | Upward sum of the two certified component error bounds. |
| SO-MALG T:63 (def) | `CC.mulC` | PASS | Rounded backend complex mul; intended on the whole coefficient carrier. |
| SO-MALG T:67 (def) | `CC.mulErrC` | PASS | Upward sum of the two certified component error bounds. |
| SO-MALG T:71 (def) | `CC.scaleC` | PASS | Rounded backend complex scale; intended on the whole coefficient carrier. |
| SO-MALG T:74 (def) | `CC.scaleErrC` | PASS | Upward sum of the two certified component error bounds. |
| SO-MALG T:78 (theorem) | `CC.norm_add_sub_addC` | PASS | Complex component addition errors imply the norm error bound. |
| SO-MALG T:90 (theorem) | `CC.norm_mul_sub_mulC` | PASS | Uses both certified real and imaginary product error bounds. |
| SO-MALG T:101 (theorem) | `CC.norm_scale_sub_scaleC` | PASS | Two component multiplication errors bound real-scalar complex scaling. |
| SO-MALG T:123 (def) | `sumPairsUp` | PASS | Pairwise upward addition, structurally recursive on the list. |
| SO-MALG T:128 (def) | `pairRounds` | PASS | Structurally recursive on the natural number of rounds; no well-founded recursion. |
| SO-MALG T:135 (def) | `sumUp` | PASS | 64 pairwise rounds followed by foldr; total even for lists longer than 2^64. |
| SO-MALG T:139 (def) | `weightTermUp` | PASS | Outward bound abs(error) times the stored-key weight. |
| SO-MALG T:143 (def) | `errRadius` | PASS | Balanced sum of termwise weighted error bounds. |
| SO-MALG T:147 (def) | `CertPoly.supNormUp` | PASS | Balanced weighted coefficient-norm sum; no omitted modes. |
| SO-MALG T:152 (theorem) | `sumPairsUp_ge` | PASS | Pairwise upward sum dominates the original real sum. |
| SO-MALG T:161 (theorem) | `pairRounds_ge` | PASS | Induction on round count preserves domination. |
| SO-MALG T:166 (theorem) | `foldr_upAdd_ge` | PASS | Structural sum domination including the empty list. |
| SO-MALG T:174 (theorem) | `sumUp_ge` | PASS | Composition of pair-round and final fold inequalities. |
| SO-MALG T:180 (theorem) | `norm_character_le_keyDeg` | PASS | Validated strip weight; stored-key l1 degree dominates visible Fin n degree. |
| SO-MALG T:187 (theorem) | `weightTermUp_nonneg` | PASS | Validated positive weight and backend abs imply nonnegative budget. |
| SO-MALG T:198 (theorem) | `weightTermUp_ge` | PASS | Covers arbitrary signed input errors via absolute value and outward rounding. |
| SO-MALG T:216 (theorem) | `sumUp_nonneg` | PASS | Nonnegative summands imply nonnegative outward sum. |
| SO-MALG T:222 (theorem) | `CertPoly.supNormUp_nonneg` | PASS | Applies weighted-budget nonnegativity to every coefficient. |
| SO-MALG T:226 (theorem) | `CertPoly.norm_eval_le_supNormUp` | PASS | Finite-sum triangle inequality, coefficient norm and strip weight. |
| SO-MALG T:249 (def) | `errTermsEval` | PASS | Exact finite Fourier sum of rounded centres; accepts all lists. |
| SO-MALG T:253 (def) | `errTermsErr` | PASS | Exact finite sum of signed error budgets times character norms. |
| SO-MALG T:256 (theorem) | `errTermsEval_nil` | PASS | Exact finite-list denotation identity; no mathematical premise added. |
| SO-MALG T:259 (theorem) | `errTermsEval_cons` | PASS | Exact finite-list denotation identity; no mathematical premise added. |
| SO-MALG T:264 (theorem) | `errTermsErr_nil` | PASS | Exact finite-list denotation identity; no mathematical premise added. |
| SO-MALG T:267 (theorem) | `errTermsErr_cons` | PASS | Exact finite-list denotation identity; no mathematical premise added. |
| SO-MALG T:272 (theorem) | `errTermsEval_append` | PASS | Exact finite-list denotation identity; no mathematical premise added. |
| SO-MALG T:276 (theorem) | `errTermsErr_append` | PASS | Exact finite-list denotation identity; no mathematical premise added. |
| SO-MALG T:280 (theorem) | `errTermsErr_le_errRadius` | PASS | Termwise weighted domination; no sortedness or key-length premise. |
| SO-MALG T:286 (def) | `CertPoly.toErrTerms` | PASS | Attaches backend zero errors to every exact input term. |
| SO-MALG T:289 (theorem) | `CertPoly.errTermsEval_toErrTerms` | PASS | Law-free centre denotation equality. |
| SO-MALG T:293 (theorem) | `CertPoly.errTermsErr_toErrTerms` | PASS | Exact zero-error denotation under backend laws. |
| SO-MALG T:306 (def) | `mergeErrPair` | PASS | Combines same-key coefficients, both prior errors and addition rounding. |
| SO-MALG T:310 (def) | `mergeErrInsert` | PASS | Structural list insertion/merge step; arbitrary-order soundness. |
| SO-MALG T:321 (def) | `mergeErrTerms` | PASS | Structural outer-list recursion; no sorting premise for enclosure. |
| SO-MALG T:327 (theorem) | `mergeErrPair_spec` | PASS | Pays both old errors and addition error; explicit same-key premise is local typing data. |
| SO-MALG T:348 (theorem) | `mergeErrTerms_spec` | PASS | All lists, including duplicates/unsorted keys; simultaneous centre and error accounting. |
| SO-MALG T:406 (def) | `rowItems` | PASS | All pair products in one row; exact zero-extended key addition, rounded coefficients. |
| SO-MALG T:411 (def) | `directItems` | PASS | Structural fold over all product rows, with merge error accounting. |
| SO-MALG T:415 (def) | `truncKeep` | PASS | Literal stored degree <= cutoff; zero keeps degree-zero terms. |
| SO-MALG T:418 (def) | `truncErr` | PASS | Dropped coefficient norm is added to its existing rounding error. |
| SO-MALG T:422 (def) | `truncPoly` | PASS | Filters kept terms and projects their rounded centres. |
| SO-MALG T:427 (theorem) | `rowItems_spec` | PASS | Character multiplication and certified complex coefficient product. |
| SO-MALG T:457 (theorem) | `directItems_spec` | PASS | Fold invariant plus row and merge estimates; all input lists. |
| SO-MALG T:499 (theorem) | `truncPoly_spec` | PASS | Pays lost centres and retains pre-existing errors, for every natural cutoff. |
| SO-MALG O:46 (structure) | `ModelConfig` | PASS | Exact signed data structure: cutoff, real Taylor controls, untrusted decoder and advice. |
| SO-MALG O:60 (def) | `adviceLookup` | PASS | Total first-match lookup; missing key returns none, duplicate keys choose the first. |
| SO-MALG O:70 (def) | `itemsPoly` | PASS | Projects term centres; caller retains the error in the radius. |
| SO-MALG O:73 (def) | `CertPoly.isConst` | PASS | All stored key entries zero, including empty polynomial; conservative for extra coordinates. |
| SO-MALG O:75 (def) | `CertModel.add` | PASS | Same-degree rounded merge plus original radii and weighted merge errors. |
| SO-MALG O:83 (def) | `CertModel.polyProduct` | PASS | Scalar/direct/checked-packed routing; failure is explicit none, handled by mul. |
| SO-MALG O:98 (def) | `crossUp` | PASS | Zero shortcut requires sound backend equality; otherwise upward multiplication. |
| SO-MALG O:106 (def) | `CertModel.mul` | PASS | Degree sum; truncation and all cross errors, or a proved crude enclosure on failure. |
| SO-MALG O:119 (def) | `trimDrop` | PASS | Sound backend comparison against the same outward weighted size used for accounting. |
| SO-MALG O:123 (def) | `CertModel.trim` | PASS | Complementary term filters; whole dropped polynomial norm added to radius. |
| SO-MALG O:133 (def) | `piLowPos` | PASS | Maximum of two valid lower pi bounds; fixed positive piLoQ covers degenerate parameters. |
| SO-MALG O:136 (def) | `piUpMin` | PASS | Minimum of two valid upper pi bounds. |
| SO-MALG O:139 (def) | `twoPiZpowLo` | PASS | Positive powers use lower endpoint; negative powers invert the upper endpoint. |
| SO-MALG O:143 (def) | `twoPiZpowHi` | PASS | Positive powers use upper endpoint; negative powers invert the positive lower endpoint. |
| SO-MALG O:146 (theorem) | `twoPiZpow_mem` | PASS | Both exponent signs, arbitrary Machin parameters; positive lower endpoint proved. |
| SO-MALG O:180 (def) | `scaleItems` | PASS | Rounded real scaling with one multiplication error for each coefficient component. |
| SO-MALG O:184 (def) | `CertModel.toDeg` | PASS | Identity at equal degree; otherwise Machin-based scaling with all rounding paid. |
| SO-MALG O:195 (def) | `derivItem` | PASS | Total zero-extended coordinate access; drops zero multipliers and pays both component errors. |
| SO-MALG O:202 (def) | `CertModel.ofDeriv` | PASS | Derivative of exact P at degree d+1; no claim to differentiate an arbitrary remainder. |
| SO-MALG O:215 (theorem) | `itemsPoly_eval` | PASS | Projection preserves the exact centre sum. |
| SO-MALG O:219 (theorem) | `two_pi_zpow_ofReal` | PASS | Integer-power compatibility of real-to-complex embedding. |
| SO-MALG O:223 (theorem) | `norm_two_pi_zpow` | PASS | Positive real 2pi gives its exact norm at every integer degree. |
| SO-MALG O:226 (theorem) | `CertModel.Encloses.rad_nonneg` | PASS | Nonempty positive-width strip supplies a real point; no radius premise added. |
| SO-MALG O:234 (theorem) | `crossUp_ge` | PASS | Sound zero test or upward product, with ordinary nonnegativity premises. |
| SO-MALG O:241 (theorem) | `CertModel.Encloses.add` | PASS | Exact signed contract; equal degree is the original signed premise. |
| SO-MALG O:276 (theorem) | `norm_mul_sub_le_core` | PASS | Algebraic error decomposition and norm estimates; genuinely conditional arithmetic helper. |
| SO-MALG O:306 (theorem) | `CertModel.polyProduct_sound` | PASS | Every successful scalar/direct/packed result; no valid-advice premise. |
| SO-MALG O:332 (theorem) | `CertModel.Encloses.mul` | PASS | Exact signed unconditional config/key contract; both success and fallback branches. |
| SO-MALG O:397 (theorem) | `CertModel.Encloses.trim` | PASS | Exact signed contract; partition and dropped-polynomial bound. |
| SO-MALG O:429 (theorem) | `scaleItems_spec` | PASS | Finite-sum bound for rounded real scaling. |
| SO-MALG O:454 (theorem) | `norm_toDeg_sub_le_core` | PASS | Conditional numeric scaling estimate; not substituted for an unconditional source theorem. |
| SO-MALG O:479 (theorem) | `CertModel.Encloses.toDeg` | PASS | Exact signed contract; Machin bounds suffice independently of pe centre/radius. |
| SO-MALG O:542 (theorem) | `norm_deriv_coeff_sub` | PASS | Rounded ik_j coefficient, with exact negation and both multiplication errors. |
| SO-MALG O:563 (theorem) | `derivItems_spec` | PASS | Zero coordinate omitted; all other coefficient errors retained. |
| SO-MALG O:606 (theorem) | `hasFDerivAt_termSum` | PASS | Law-free finite-sum Frechet derivative, with the period-one 2pi factor. |
| SO-MALG O:621 (theorem) | `CertModel.Encloses.ofDeriv` | PASS | Exact signed derivative contract, including symbolic degree shift. |
| SO-MALG O:649 (theorem) | `CertPoly.torusAverage_eval` | PASS | Law-free finite Fourier average; coefficients sum duplicate/padded zero modes. |
| SO-MALG O:674 (theorem) | `CertModel.Encloses.average` | PASS | Exact signed contract; signed continuity premise supplies integrability. |
| SO-MALG X:38 (def) | `modelTestLay` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:41 (def) | `modelTestTarget` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:43 (def) | `modelTestA2` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:46 (def) | `modelTestB2` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:50 (def) | `modelTestAdv` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:56 (def) | `modelTestAdvOff` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:62 (def) | `modelTestBogus` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:65 (def) | `modelTestW` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:67 (theorem) | `modelTest_weight` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:70 (def) | `modelTestRe` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:74 (def) | `modelTestCfg` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:78 (def) | `modelTestBook` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:82 (def) | `modelTestA` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:84 (def) | `modelTestB` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:87 (def) | `modelTestConst` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:89 (def) | `modelTestZero` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:92 (def) | `modelTestView` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:96 (theorem) | `modelTest_mul_packed` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:107 (theorem) | `modelTest_mul_missing` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:113 (theorem) | `modelTest_mul_failing` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:120 (theorem) | `modelTest_mul_scalar` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:130 (theorem) | `modelTest_mul_scalar_coeff` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:137 (theorem) | `modelTest_mul_zero` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:143 (theorem) | `modelTest_mul_encloses` | PASS | Packed-route instance of the general signed contract; enclosure inputs are explicit. |
| SO-MALG X:152 (def) | `modelTestQ` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:155 (def) | `modelTestViewQ` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:158 (def) | `modelTestCfgQ` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:161 (theorem) | `modelTest_mul_direct` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:168 (theorem) | `modelTest_add` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:177 (theorem) | `modelTest_trim` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:185 (theorem) | `modelTest_ofDeriv` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:193 (def) | `modelTestPi` | PASS | Finite test fixture/view only; no bundled proof assumptions or production fallback. |
| SO-MALG X:195 (theorem) | `modelTest_pi` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |
| SO-MALG X:199 (theorem) | `modelTest_toDeg` | PASS | Concrete equality/Boolean check by decide +kernel; independently kernel-replayed. |

## Independent validation receipts

All Lean/Lake commands were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The build gate itself invokes `nice -n 5 lake build`. No clean, update, cache fetch, source fix,
generated-root regeneration, protected-path edit or state-changing git command was run.

Targeted build (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-somalg KAM.Certificate.Model.Terms KAM.Certificate.Model.Ops KAM.Certificate.Tests.Model
```

```text
[inp-gate] slot 1 acquired 18:43:46 for KAM.Certificate.Model.Terms KAM.Certificate.Model.Ops KAM.Certificate.Tests.Model
⚠ [2840/2915] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
Build completed successfully (2915 jobs).
```

The only displayed warning is the inherited unused simp argument in `Arith/PiHigh`; no scoped
module warning appeared. The warning's generic suggestion about a linter setting was not applied.

Kernel replay, one invocation for all three modules (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Model.Terms KAM.Certificate.Model.Ops KAM.Certificate.Tests.Model > .lake/abi-scratch/SO-MALG-leanchecker.log 2>&1
```

```text
replaying KAM.Certificate.Tests.Model
replaying KAM.Certificate.Model.Ops
replaying KAM.Certificate.Model.Terms
```

The 13 concrete test theorems use `decide +kernel`; `modelTest_mul_encloses` is an ordinary
contract application, not a computation. The handoff's phrase “all decide +kernel” should be read
with that stated contract-instance exception. Kernel replay validates all their proof bodies.
The packed/missing/rejected/scalar/both-sides/zero/direct cases are present, as are add, trim,
ofDeriv, pi validation and toDeg. No native evaluator is used.

Fresh signed-type/application and axiom probe (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SO-MALG-probe.lean > .lake/abi-scratch/SO-MALG-probe.log 2>&1
```

The probe imports `KAM.Certificate.Tests.Model`, opens the existing KAM namespaces, and copies
the five signed function headers plus six signed theorem headers under fresh names. Each body is
a direct application of the original declaration to exactly its explicit binders, in order.
Function applications are respectively `W a b`, `W cfg key a b`, `W eps a`, `W pe d a`,
`W j d P`; theorem applications are listed in the signed-contract table. The structure is checked
textually including all fields/docstrings. The probe also includes these independent reductions
with private rational fixtures, avoiding reliance on unexported test-data bodies:

```lean
namespace KAM.Certificate.AuditSO_MALG
private def w : CertWeight := ⟨1/100, 11/10⟩
private def cfg : ModelConfig ℚ := ⟨0, 0, 0, fun _ _ => none, [([], .direct)]⟩
private def mode : CertModel ℚ := ⟨0, ⟨[([1], ⟨1, 0⟩)]⟩, 0⟩
example : (CertModel.mul w cfg [] mode mode).poly.terms = [] ∧
    (CertModel.mul w cfg [] mode mode).rad = 121/100 := by decide +kernel
example : 0 < twoPiZpowLo 0 0 (-1) ∧
    twoPiZpowLo 0 0 (-1) ≤ twoPiZpowHi 0 0 (-1) := by decide +kernel
end KAM.Certificate.AuditSO_MALG
```

There were no errors or warnings. Exact `#print axioms` output for every new public theorem
(each command was `#print axioms <the fully qualified name printed below>`):

```text
'KAM.Certificate.keyCmp_eq_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.CC.norm_add_sub_addC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CC.norm_mul_sub_mulC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CC.norm_scale_sub_scaleC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumPairsUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.pairRounds_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.foldr_upAdd_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_character_le_keyDeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.weightTermUp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.weightTermUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumUp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.supNormUp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.norm_eval_le_supNormUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsEval_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsEval_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsErr_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsErr_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsEval_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsErr_append' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.errTermsErr_le_errRadius' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.errTermsEval_toErrTerms' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.errTermsErr_toErrTerms' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mergeErrPair_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mergeErrTerms_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.rowItems_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.directItems_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.truncPoly_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.twoPiZpow_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.itemsPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.two_pi_zpow_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_two_pi_zpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.rad_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.crossUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_mul_sub_le_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.polyProduct_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.trim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.scaleItems_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_toDeg_sub_le_core' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.toDeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_deriv_coeff_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.derivItems_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hasFDerivAt_termSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.ofDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.torusAverage_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.average' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_packed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_missing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_failing' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_scalar_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_mul_direct' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_trim' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_ofDeriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.modelTest_toDeg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus every result uses a subset of `{propext, Classical.choice, Quot.sound}`; no `sorryAx` or
other axiom occurs. The only smaller set is `keyCmp_eq_eq`, which does not use `Classical.choice`.

Signed text comparison (exit 0):

```sh
python3 .drafts/SO-MALG/sigcheck.py KAM/Certificate/Model/Ops.lean
```

```text
OK  ModelConfig
OK  CertModel.add
OK  CertModel.mul
OK  CertModel.trim
OK  CertModel.toDeg
OK  CertModel.ofDeriv
OK  CertModel.Encloses.ofDeriv
OK  CertModel.Encloses.add
OK  CertModel.Encloses.mul
OK  CertModel.Encloses.trim
OK  CertModel.Encloses.toDeg
OK  CertModel.Encloses.average
checked 12 bad 0
```

A separate Python comparison extracted each `def`/`theorem` header up to `:=` and the entire
structure field block from the signed source and implementation, normalized whitespace and tested
equality, rather than relying only on the supplied checker's substring test. Output:

```text
Independent signed-type probes: 11 Public theorem axiom probes: 62 All explicit declarations: 126
Independent head/field comparison: 12/12 exact modulo whitespace
```

Public short names (exit 0; checker includes Mathlib/KAM last components and signed-name exceptions):

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-somalg KAM.Certificate.Model.Terms KAM.Certificate.Model.Ops KAM.Certificate.Tests.Model
```

```text
short-name check OK (no reused public short name)
```

All explicit declarations remain in `KAM.Certificate`; no harmful root declaration is introduced.
The `_root_.add_apply` / `_root_.smul_apply` at `Ops:617` are references resolving names, not
root declarations. The approved signed names remain exact.

Full lint (exit 1, solely the allowed generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/SO-MALG-lint.log 2>&1
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1346 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Source scans found no forbidden proof escape, resource override, `EuclideanSpace`,
`native_decide`, `implemented_by`, `ofReduceBool`, `WellFounded`, `termination_by` or
`decreasing_by` in the scoped files. Inspection of every recursive body found structural recursion
on `List` or `ℕ` (and ordinary list folds/maps/filters). The 64-round sum has an explicit final
fold for any leftover entries, so its mathematical correctness has no hidden length bound.
All files have copyright, `module`, public imports, a module docstring and public section.
The implementation sections carry `@[expose]`; test-only data bodies need not be exported.
Measured lengths / maximum Unicode columns: Terms **539 / 99**, Ops **698 / 99**, Tests **211 / 99**.

A recursive local import scan reached 31 local modules. It found no provider and no frozen
theorem import. Its sole frozen dependency is `KAM/Frozen/Defs/ComplexStrip.lean`, manifest
entry `kam.complexStrip.v1`, state **SEALED**. No DRAFT_SORRY anchor enters the package.

Protected paths and diff whitespace (both exit 0, no output):

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

## Notes, uncertainty and source/blueprint defects

No suspected mathematical defect in the controlling SO design/signatures or the frozen strip
definition was found. No source statement was repaired, weakened, or given additional premises.
No deviation was introduced by this audit. This is a package soundness audit, not an independent
reproduction of the handoff's lunar-size timings, a proof that the lunar margins succeed, or a
re-audit of SO-POLY-B's implementation. Its landed soundness theorem is a normal checked dependency;
all new theorem axiom closures were checked independently.

The following integration notes do not block this signed slice:

- `cutoff = 0` literally keeps only degree-zero stored keys (`Ops:110`, `Terms:415` and the signed
  `ModelConfig.cutoff` field). It does not mean “unlimited”. The handoff flags a generator table
  convention mismatch; that external generator is outside this audit. A producer using zero as
  an unlimited sentinel would remain sound but could lose its margins. The scratch cutoff-zero
  test above confirms the full dropped weight enters the radius.
- `toDeg` reads the Machin parameters rather than the backend centre/radius of `pe`. The signed
  contract is still exact and proved. No quantitative claim that its computed radius is always
  narrower than another implementation's rounded ball was needed or independently established.
- `isConst` accepts multiple all-zero-key terms. Soundness holds for them, but the scalar route
  is then multiple direct rows, rather than the handoff's “one row” description for a canonical
  one-term constant. Likewise sortedness helps size/completeness, not theorem applicability.
- The stored-key degree may overestimate the visible `Fin n` degree for extra coordinates;
  this makes the bound conservative. Empty, duplicate, unsorted or padded keys are not excluded
  by any added premise in these proofs.
- The direct product may be expensive, and the 64-round summation's logarithmic-depth performance
  description presumes an ordinary-size list. Correctness remains total for every finite list.
  Lunar-size timings and asymptotic performance claims were not rerun under the tight-memory request.
- The accepted design's §1.12 phrase “structural only, over List” is implemented using structural
  natural recursion as well (`pairRounds`, Terms:128). This is explicitly disclosed by the handoff,
  introduces no well-founded recursion, and does not alter any signed statement or owner hard rule.
- `Tests/Model:199–208` compares the toDeg coefficient against the rational proxy
  `2 * 314159265 / 10^8`; it is not a direct computational comparison with transcendental `2π`.
  The signed enclosure theorem separately provides the real `2π` guarantee.

No unrelated track headline or frozen anchor is claimed closed. The generated root is left to the
orchestrator exactly as required by the brief and rule 10. Audit scratch probes and captured logs
were removed after embedding these receipts; the final working-tree change is this report alone.
