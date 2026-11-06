Audited initial HEAD `4afebe84d4cd0fd012de56b2d559855f926c85e1`; final HEAD (`git rev-parse HEAD`) `3cb54d880fe4685e168b8643ac66ad1e90c1fd80`;  launch/package commit `4afebe84d4cd0fd012de56b2d559855f926c85e1`; SHA256: `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst.lean` = `12f13a343f0a3031ebf3740e84b57a6c165078cec317a530ea26a32b94c496a3`; `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst/Bdat.lean` = `15484350b5a9dd78fef3696016dea0f309821ce4e1c3925c32c915c8f4615815`; `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst/Groups.lean` = `14300c2b861a070700093e64904c9f01812e71bb9a8d2c69d37a3a3dd41e46a4`; `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst/HwGroups.lean` = `7e23e88211b70a527b5ba1cbbb9caaad8a460dfc10517851ef6dfc8209b119e0`; `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst/Tdat0.lean` = `13697873701e4170c2c2725f55456cc52c90e87c4a1df632e1abec495fe6914e`; `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst/Tdat1.lean` = `1d9a54029d57556062524c4f63e0190f898741d59a236e1d82441772ffb0000b`; `KAM/EffectiveStability/SJSU/Ham/HtBridgeInst/Tdat2.lean` = `5662ee600c5062d89207e0da436174b36b460ebc74c035be753a445c25f704f9`.

**Verdict: PASS WITH NOTES — N5a-2 instance (N5a2i), audit 1.**

The actual ledger's Horner sum is identified with the required Taylor coefficient,
with no external logical hypothesis. All seven module targets, all 120 axiom queries
and the exact-type/consumer-composition examples pass. Prior finding N1 is resolved.
The notes are stale handoff wording, a repository lint failure for generated roots,
and the shared-worktree dependency provenance described below. This verdict certifies
the bridge at the pinned bytes; it does not certify production ledger checks, a
bracket-rate bound, or T2-CONF closure.

**Scope and authority.** Independent refute-first audit of the seven files named by
`.drafts/g2/AUDIT-N5a2i-launch.md`, following `AUDIT-PKG-brief.md`, `BRIEF-N5a2-HtBridge.md`,
AGENTS, PLAN, DECISIONS, WORKER-RULES, the N5a-2 handoff and prior N7b-N5a2 audit.
The `lean-statement-audit` methodology is applied to the actual ordinary exports;
there is no frozen declaration or manifest seal in this package. Definitions and
consumer interfaces outside these seven files were read only as needed to establish
meaning and use, rather than re-audited as new deliverables. No delegation was used.

Only this report is edited by the auditor. To respect the user's report-only instruction,
the Lean probe below is extracted from this report and supplied to `g2lake env lean --stdin`;
no scratch source or log is created. This replaces the audit template's scratch-file
location without dropping its checks. Targeted builds use the prescribed foreground
`g2lake` command and shared lock; no direct lake/lean invocation, clean, whole-library
build, production job, generated-root edit, commit, branch change or source repair.
The wrapper's own configuration is nice 5, 6 GiB, no swap, `LEAN_NUM_THREADS=2`.

**Findings and prior-note disposition.**

- **N1 from N7b-N5a2-AUDIT-1: resolved in substance.** The handoff now has the status,
  exact statements, line counts, build and axiom receipts, design signals and scope
  separation. All six literal template tokens named in N1 are absent. It explicitly
  separates the previously audited generic part from this instance (handoff:7–12,
  19–24, 97–127, 157–164). The generic audit's nonblocking N1 is not a mathematical gap.
- **I1 — stale commit wording (documentation only).**
  `docs/explorations/sjsu-g2-handoffs/N5a2-HtBridge.md:10` says the instance is
  "new and uncommitted", although launch commit `4afebe84d` contains all seven instance
  files and that handoff. This does not change any theorem. Suggested fix by the owner:
  replace that phrase with its commit and link this report after acceptance. The line
  "The instance is unaudited" at handoff:164 describes its pre-audit status and must not
  be read as claiming that the earlier generic audit certified it.

No mathematical blocker or conclusion-shaped hypothesis was found in the scoped source review.
No suspected defect in a pinned mathematical source and no mathematical deviation introduced.

**Exact statement and binder audit: PASS.**

```lean
sjsuHD_Ht_eq_hCoef (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
  sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m φ =
    hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ
```

At `HtBridgeInst.lean:59–64` there are no implicit logical, instance or bundled
hypotheses in addition to these two explicit arguments. The definitions in the
conclusion are concrete, not locally substituted aliases or arbitrary stand-in data.

| Expanded binder | Classification | Authority/meaning |
|---|---|---|
| `m : ℕ × ℕ × ℕ` | TYPING | N5a-2 target (2), all Taylor multiindices, mode order 0,1,2 |
| `φ : Fin 2 → ℝ` | TYPING | N5a-2 target (2), the two real reduced angles |

Counts: SOURCE 0; STANDING 0; TYPING 2; RULED 0; EXCESS 0. No section variable
adds a hidden premise. Global data and all needed properties are supplied in the proof.
In particular the result does not assume a ledger equality, row membership, positivity,
Nodup, a degree restriction, a certificate, or the desired identity.

The proof applies `Tube.HData.Ht_eq_hCoef` (`Tube/Poly/HtBridge.lean:311–347`) to
**the actual** `SJSU.sjsuHD`, imported from `SJSU/Ledger/H/HData.lean`. Its exposed
fields are `CT=9`, `CP=30`, `M=9`, `Nmax=18`, `ns=sjsuNs`, `Tdat=sjsuTdat`,
`Bdat=sjsuBdat`. `Engine/Powers.lean:36–42` defines `Tt` and `Bt` by those dense
lists and `Pt` as the integer power of the positive square root of `Bt`.
`HtBridgeInst.lean:52–56` unfolds these very definitions with `simp only`.
No alternative `HData` value is constructed. The generic bridge's premises are paid as follows:

| Generic obligation | Actual supplier in this instance |
|---|---|
| distinct group list | `sjsuNs_nodup` |
| each component at most `D.Nmax` | `sjsuNs_bound`, definitionally `Nmax=18` |
| `D.Tt n = Tn ... (ofTriple n)` on every group | `sjsuHD_Tt_eq`, `sjsuTdat_eq`, `sjsuTn_eq_denseCos` |
| `D.Bt j = fun φ => sjsuB φ j` for `j : Fin 3` | `sjsuHD_Bt_eq`, `eq_of_listBEq (sjsuBdat_check j)`, `sjsuB_eq_denseCos` |
| strict positive centre for all angles/components | `sjsuB_pos`, proved in the previously audited generic SJSU module |
| every Hamiltonian row exponent belongs to the groups | `sjsuHwAll_groups` |

The three generic source modules and `HTilde.lean` retain exactly the hashes recorded
by N7b-N5a2-AUDIT-1. Their literal formula for `hCoef` is the finite sum over actual row
exponents of `T_n ∏_j gbinom(n_j/2,m_j) B_j^(n_j/2-m_j)` (`HTilde.lean:55–70`).
The parameter order and carriers match. `ofTriple (a,b,c)=![a,b,c]` agrees definitionally
with N9's `monOf` (`Tube/Obs/ListObs.lean:34`). N9's `hbr` premise in
`Tube/Check/HSplit.lean:111` is exactly supplied with `hc t := sjsuHD.Ht ... t`;
the probe checks this function identity and transports an `hBlock_sound` certificate
to the same `hCoef` function. The certificate transport is explicitly conditional on
that earlier stage's actual check and operand certificates, not a claim that the
production checks have been run by this audit.

This bridge is available for **every** natural triple and real angle, including
`m=(0,0,0)`, boundary degree 9 and indices beyond degree 9. It therefore has the full
scope N9 needs without a `|m|≤9` side premise. Negative exponents remain integer
subtractions before conversion to real half-powers; they are not Nat subtraction.
The inherited identity uses strict `B>0`, established for this literal centre, so
no zero or negative base branch is silently used. This theorem involves neither
Cartesian zero-action points nor `Complex.arg`; their separate chart obligations
are not asserted here. Cosines use radian angles in both series representations.

An independent sign/index check: a row `b=(1,0,0)`, `b'=(0,1,0)` has reduced mode
`(1,-1)` and exponent `(1,1,0)`; its term has the sign of its rational coefficient
multiplying `cos(φ₀-φ₁)`. For one odd action exponent and Taylor index 2,
`gbQ 1 2=(1/2)(-1/2)/2=-1/8`, with power `B^(-3/2)`; no absolute value or sign
change belongs in this identity. The asymmetric box mode `(1,-2)` has index
`10+19*7=143` at `C=9`, agreeing with the dense convention.

**Replacement encodings: PASS.**

1. `Groups.lean:28–37`: the kernel proves that the mapped keys are a strict chain.
   On naturals, `<` is transitive, so `List.isChain_iff_pairwise` yields pairwise
   distinct keys. `List.Nodup.of_map` then proves the original triples are distinct:
   any duplicate triple would force a duplicate mapped key. This direction needs
   no global injectivity assumption about base-32 packing. Bounds and the coverage
   length are separate closed kernel proofs; no truncation argument replaces them.
2. `HwGroups.lean:26–67`: `keyMask` uses bitwise OR of `1 <<< nsKey n`, not integer
   addition, so duplicate keys cannot carry into another bit. The inductive
   `exists_of_testBit_keyMask` uses `Nat.testBit_or` and the one-bit shift identity
   to recover an actual list member with the requested key. The generic `nsKey_inj`
   requires **all three** components of both triples to be `<32`; these guards
   prevent packing collisions. `mem_of_rowGroupOk` obtains row bounds from the
   Boolean conjunction and group bounds from the closed `≤18` theorem before
   identifying the triples. The 10 degree checks include the empty degree-0 list;
   `List.all_append` covers the whole of `sjsuHwAll`, preserving actual membership.
   For the strictly distinct group keys the handoff's sum-of-powers description
   also agrees with this OR mask, but the proof does not depend on that description.
3. `Tdat0/1/2.lean:24–147` and `HtBridgeInst.lean:34–47`: the 90 distinct declarations
   cover exactly block indices 0–89 (checked mechanically, no duplicate or missing
   number). Their interval aggregators cover `[0,30)`, `[30,60)`, `[60,90)`.
   `sjsuNs_length` proves `length≤8*90`; `all_of_blocks` uses Euclidean quotient/remainder
   to place every valid list index in a checked block. An independent Python literal parse of the 18 `sjsuNs` parts also found 714
   distinct triples with strictly increasing keys and maximum component 18. Block 89
   has two entries. The final partly filled block is covered by `take`, with no assumption that the list length is a multiple of 8.
   Explicit `(c := 8) (K := 90)` only resolves elaboration metavariables; it changes
   no quantifier or mathematical premise. `tdatOk` tests complete rational list
   equality, and `eq_of_listBEq` yields that equality rather than a hash comparison.
4. `Bdat.lean:24–46`: three complete rational list equalities are checked and selected
   by exhaustive `fin_cases j : Fin 3`. They compare the actual ledger `sjsuBdat`
   with all 3721 scatter slots. No component is omitted. The source-level centre
   identification retains `-modeK*σ`, the `Ibar` centre term and box width 30 from
   the generic theorem. Sparse defaults in the ledger cannot bypass these full-list checks.

For helper binders, every logical input expands as follows. Bounds/equalities in this
table are structural premises of explicitly generic decoding lemmas; the concrete
final theorem proves and discharges them.

| Helper | Expanded input | Bin |
|---|---|---|
| `sjsuTdat_blocks` | `k : ℕ`; `k<90` | TYPING; SOURCE selector |
| `sjsuTdat_eq` | `{n : ℕ³}`; `hn : n∈sjsuNs` | TYPING; SOURCE selector |
| `sjsuHD_Tt_eq` | `n : ℕ³` | TYPING |
| `sjsuHD_Bt_eq`, `sjsuBdat_check` | `j : Fin 3` | TYPING |
| `sjsuTdat_blocks0/1/2` | `k : ℕ`; lower bound; upper bound | TYPING; SOURCE selector each |
| `nsKey_inj` | `{a : ℕ³}`, `{b : ℕ³}` | TYPING each |
| `nsKey_inj.ha` | `a.1<32`, `a.2.1<32`, `a.2.2<32` | SOURCE structural, each of 3 |
| `nsKey_inj.hb` | `b.1<32`, `b.2.1<32`, `b.2.2<32` | SOURCE structural, each of 3 |
| `nsKey_inj.h` | equality of packed keys | SOURCE structural |
| `exists_of_testBit_keyMask` | `{l : List ℕ³}`, `{k : ℕ}`; set-bit check | TYPING each; SOURCE structural |
| `mem_of_rowGroupOk` | `{e : (Mon×Mon)×ℤ}`; `rowGroupOk e=true` | TYPING; SOURCE structural |
| `sjsuHwAll_groups` | `e`; `e∈sjsuHwAll` | TYPING; SOURCE selector |
| `sjsuNs_bound` | `n : ℕ³`; `n∈sjsuNs` | TYPING; SOURCE selector |
| all 90 fixed blocks, 10 fixed degree checks, 3 fixed B checks, group chain/Nodup/length | no external logical input | closed facts |

No STANDING/RULED/EXCESS helper input is hidden. `rowGroupOk` expands into exactly
three `<32` decisions and one set-bit check; `tdatOk` into complete rational list
comparison. Neither assumes `Ht=hCoef` or an analytical estimate.

Meaning-carrying definitions `tdatOk`, `nsKey`, `keyMask`, `sjsuNsMask`, `rowGroupOk`
are literal computation on their advertised carriers, all exposed for reduction.
`nsKey` is defined on all triples but only claimed injective under its stated bounds;
`keyMask` correctly handles arbitrary lists, including empty and duplicate inputs.
No choice-defined object or unproved existence/uniqueness is introduced.
BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.

**Hygiene and integrity.** All seven files exactly match launch commit `4afebe84d`.
Every file has the required copyright, `module`, `public import`, module docstring
and exposed public section (noncomputable where appropriate). Scoped scans found
no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `native_decide`,
`sorryAx`, or `EuclideanSpace`. Line counts in order facade/Groups/Tdat0/Tdat1/Tdat2/
Bdat/HwGroups are 68/45/151/151/151/50/108. Maximum line width is 100; no file is
near 1500 lines. The 120 theorem declarations are all queried below.

The imported ledger is present in the shared worktree but was untracked at audit start;
this report does not certify a standalone checkout of the package commit without that
ledger. Context SHA256, outside the seven-file verdict:

| Context path | SHA256 |
|---|---|
| `Tube/Poly/HtBridge.lean` | `65a4dc378afa69f40a3051a67a266a403c740e0c496b4abfc579926062c854a3` |
| `Tube/Poly/HtDense.lean` | `97647e40191cc79b9e5295da7cc191995dafcf1f3c03ab4b7e2cfc414401008b` |
| `SJSU/Ham/HtBridge.lean` | `6eb38b6130de91abf644c06053ec9bc5c8222d75bb47613ee5eb02add5ac7773` |
| `Tube/Poly/HTilde.lean` | `ca3bfd7407c72dd586e1bf2abad568a94f5cee213f3772036635fc4eb281afac` |
| `SJSU/Ledger/H/HData.lean` | `7527fed6fcf57b5aef4055472a813c0cd272be3a8cac670a6e7f4764c100834a` |
| `SJSU/Ledger/H/Inputs89.lean` | `4b491292e78f521436d436590dd2bddc6f212e49cbc4ffbebb42f86caa72b8d9` |
| `SJSU/Ledger/H/Inputs99.lean` | `1144eafc9e51202f95a7099e1f7535d123c1396aa0a5a746a91d2ac9d0377ee9` |

Prefixes in this table are `KAM/EffectiveStability/`. These are interface/data-container
pins, not hashes of the full generated ledger. Additionally, the 100
`Ledger/H/Inputs*.lean` files carrying the literal T/B data have aggregate SHA256
`953a03ae8bf87bd6e6e1fbdb06b675a917b24ffd10acfaba354da53c5c3f1f97`: hash the UTF-8 concatenation of `sha256(file)`, two spaces,
repository-relative path and LF, with paths sorted lexicographically. This is a byte
identity pin only, not a review of those 100 generated files. The package build's import closure
checks the data it actually imports; provenance and all production certificate checks
remain the ledger owner's scope. Any changed ledger inputs require rebuilding this bridge.

**Verification receipts.**

- `.drafts/g2/g2lake build KAM.EffectiveStability.SJSU.Ham.HtBridgeInst`:
  **exit 0**, `Build completed successfully (4577 jobs)`. This named target includes
  all six audited part modules through its public imports. It completed after waiting
  for the production lock; cached imports were reused. This is not a forced rebuild,
  independent full kernel replay or new CPU/RSS benchmark. No warning names any of
  the seven audited files. Replayed warnings come from imported `PiHigh`, `Trig.Packed`,
  `Trig.Trunc`, `Engine.Step`, `Algebra.Bounds`, `Trig.Tube`, `Engine.Exact`, `Engine.Block`
  and `Engine.Witness`: unused simp/tactic/variable notices and deprecations.
- `.drafts/g2/g2lake env lean --stdin`: **exit 0**, completed after the successful
  build and the next production lock wait. All **120** scoped theorem queries pass:
  106 use `[propext, Classical.choice, Quot.sound]`; 1 uses `[propext, Quot.sound]`;
  10 use `[propext]`; 3 are axiom-free. No unexpected axiom occurs. The main
  `sjsuHD_Ht_eq_hCoef` uses exactly `[propext, Classical.choice, Quot.sound]`.
  The same invocation verifies its fully qualified type, its function equality,
  N9's `monOf` interface, conversion from a `Fin 3 → ℕ` index, and transport of the
  actual `hBlock_sound` certificate to `hCoef`. All seven small encoding/sign
  checks also pass. The exact probe and full output are reproduced below.
- `.drafts/g2/lint_noabi.sh`: **exit 1**, completed once. `abi_hashes` was skipped as
  WORKER-RULES explicitly requires; the full lint was not invoked because its ABI
  step calls lake outside `g2lake`. Exact substantive output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (18636 Lean files, 0 comparator configurations)
Ran 29 tests in 4.360s
OK
Ran 8 tests in 0.008s
OK
FROZEN-ANCHOR GUARD OK
```

The root-check line additionally names the affected generated files:
`KAM/Root/EffectiveStability.lean`, `KAMSJSU/EffectiveStability/SJSU/{Check,Confinement,Ecc,Ham,Initial}.lean`,
`KAMSJSU/EffectiveStability/SJSU/Ledger/{Br/Top0,Br/Top1,Br/Top2,F,H/Top0,H/Top1,H/Top2,Top}.lean`,
`KAMSJSU/EffectiveStability/SJSU/{Model,Obs}.lean`, `KAMSJSU.lean`,
`KAMSJSU/EffectiveStability.lean`. Braced paths here abbreviate the full list printed by
that one check. No forbidden-token, width, module-format, anchor, errata or test
failure was reported. **Repository lint is not green.** Generated roots are outside
this report-only audit's edit scope. Suggested disposition: the orchestrator regenerates
roots and reruns the landing gate after the shared work is stable. This is a repository
integration note, not an in-scope proof failure.

**Reproducible Lean probe.** Extract the following single fenced `lean` block and run
its bytes with `.drafts/g2/g2lake env lean --stdin` (no output artifact option).

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module
public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst
public import KAM.EffectiveStability.Tube.Obs.ListObs
/-! Read-only audit probe of the actual bridge and consumer attachment. -/
public noncomputable section
open KAM.EffectiveStability.Tube KAM.EffectiveStability.SJSU
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_blocks
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_eq
#print axioms KAM.EffectiveStability.SJSU.sjsuHD_Tt_eq
#print axioms KAM.EffectiveStability.SJSU.sjsuHD_Bt_eq
#print axioms KAM.EffectiveStability.SJSU.sjsuHD_Ht_eq_hCoef
#print axioms KAM.EffectiveStability.SJSU.sjsuBdat_check0
#print axioms KAM.EffectiveStability.SJSU.sjsuBdat_check1
#print axioms KAM.EffectiveStability.SJSU.sjsuBdat_check2
#print axioms KAM.EffectiveStability.SJSU.sjsuBdat_check
#print axioms KAM.EffectiveStability.SJSU.sjsuNs_key_chain
#print axioms KAM.EffectiveStability.SJSU.sjsuNs_nodup
#print axioms KAM.EffectiveStability.SJSU.sjsuNs_bound
#print axioms KAM.EffectiveStability.SJSU.sjsuNs_length
#print axioms KAM.EffectiveStability.SJSU.nsKey_inj
#print axioms KAM.EffectiveStability.SJSU.exists_of_testBit_keyMask
#print axioms KAM.EffectiveStability.SJSU.mem_of_rowGroupOk
#print axioms KAM.EffectiveStability.SJSU.sjsuHw0_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw1_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw2_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw3_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw4_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw5_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw6_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw7_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw8_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHw9_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuHwAll_groups
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block0
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block1
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block2
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block3
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block4
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block5
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block6
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block7
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block8
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block9
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block10
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block11
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block12
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block13
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block14
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block15
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block16
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block17
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block18
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block19
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block20
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block21
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block22
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block23
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block24
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block25
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block26
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block27
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block28
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block29
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_blocks0
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block30
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block31
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block32
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block33
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block34
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block35
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block36
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block37
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block38
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block39
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block40
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block41
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block42
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block43
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block44
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block45
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block46
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block47
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block48
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block49
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block50
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block51
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block52
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block53
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block54
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block55
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block56
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block57
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block58
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block59
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_blocks1
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block60
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block61
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block62
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block63
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block64
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block65
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block66
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block67
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block68
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block69
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block70
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block71
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block72
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block73
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block74
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block75
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block76
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block77
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block78
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block79
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block80
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block81
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block82
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block83
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block84
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block85
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block86
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block87
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block88
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_block89
#print axioms KAM.EffectiveStability.SJSU.sjsuTdat_blocks2

#check @KAM.EffectiveStability.SJSU.sjsuHD_Ht_eq_hCoef

example (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m φ =
      hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ :=
  sjsuHD_Ht_eq_hCoef m φ

example (m : ℕ × ℕ × ℕ) :
    sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m =
      fun φ => hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ :=
  funext (sjsuHD_Ht_eq_hCoef m)

example (l : List (ℕ × ℕ × ℕ)) : ∀ t ∈ l, ∀ φ,
    sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt t φ =
      hCoef sjsuE sjsuN sjsuHwAll sjsuB (monOf t) φ := by
  intro t _ φ
  exact sjsuHD_Ht_eq_hCoef t φ

example (m : Fin 3 → ℕ) (φ : Fin 2 → ℝ) :
    sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt (m 0, m 1, m 2) φ =
      hCoef sjsuE sjsuN sjsuHwAll sjsuB m φ := by
  have ht : ofTriple (m 0, m 1, m 2) = m := by
    funext j
    fin_cases j <;> rfl
  simpa only [ht] using sjsuHD_Ht_eq_hCoef (m 0, m 1, m 2) φ

example {m : ℕ × ℕ × ℕ} {o : OPrm} (h : sjsuHD.hBlock m o = true)
    (hV : sjsuHD.VCerts sjsuHD.Tt sjsuHD.Pt)
    (hP : sjsuHD.PCerts sjsuHD.Pt) :
    ((sjsuHD.H m).opd sjsuHD.P).Cert sjsuHD.P.w sjsuHD.P.S
      (fun φ => hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ)
      (sjsuHD.Hc m).e₀ (sjsuHD.Hc m).e₁ (sjsuHD.Hc m).n := by
  have out := sjsuHD.hBlock_sound sjsuHD.Tt sjsuHD.Pt h hV hP
  have heq := funext (sjsuHD_Ht_eq_hCoef m)
  rw [heq] at out
  exact out

example : nsKey (0, 1, 0) = nsKey (0, 0, 32) := by decide +kernel
example : (keyMask [(0, 1, 0), (0, 1, 0)]).testBit 32 = true := by decide +kernel
example : (keyMask [(0, 1, 0), (0, 1, 0)]).testBit 64 = false := by decide +kernel
example : (keyMask []).testBit 0 = false := by decide +kernel
example : listBEq ([1, -1] : List ℚ) [1, 1] = false := by decide +kernel
example : boxIdx 9 (1, -2) = 143 := by decide +kernel
example : gbQ 1 2 = -(1 / 8 : ℚ) := by decide +kernel
end
```

**Lean probe receipt.** Command: `.drafts/g2/g2lake env lean --stdin`; exit 0.
Probe bytes SHA256: `de86d0201681391e13daea956e9847739a3f3e07a168ffbadbc690409acc9d30`.

```text
'KAM.EffectiveStability.SJSU.sjsuTdat_blocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuHD_Tt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuHD_Bt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuHD_Ht_eq_hCoef' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuBdat_check0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuBdat_check1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuBdat_check2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuBdat_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuNs_key_chain' does not depend on any axioms
'KAM.EffectiveStability.SJSU.sjsuNs_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuNs_bound' does not depend on any axioms
'KAM.EffectiveStability.SJSU.sjsuNs_length' does not depend on any axioms
'KAM.EffectiveStability.SJSU.nsKey_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.exists_of_testBit_keyMask' depends on axioms: [propext, Quot.sound]
'KAM.EffectiveStability.SJSU.mem_of_rowGroupOk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuHw0_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw1_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw2_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw3_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw4_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw5_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw6_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw7_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw8_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHw9_groups' depends on axioms: [propext]
'KAM.EffectiveStability.SJSU.sjsuHwAll_groups' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block4' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block5' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block6' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block7' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block8' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block9' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block10' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block11' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block12' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block13' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block14' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block15' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block16' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block17' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block18' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block19' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block20' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block21' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block22' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block23' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block24' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block25' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block26' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block27' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block28' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block29' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_blocks0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block30' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block31' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block32' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block33' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block34' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block35' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block36' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block37' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block38' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block39' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block40' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block41' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block42' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block43' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block44' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block45' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block46' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block47' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block48' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block49' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block50' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block51' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block52' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block53' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block54' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block55' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block56' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block57' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block58' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block59' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_blocks1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block60' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block61' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block62' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block63' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block64' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block65' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block66' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block67' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block68' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block69' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block70' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block71' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block72' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block73' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block74' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block75' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block76' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block77' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block78' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block79' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block80' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block81' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block82' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block83' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block84' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block85' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block86' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block87' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block88' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_block89' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.SJSU.sjsuTdat_blocks2' depends on axioms: [propext, Classical.choice, Quot.sound]
sjsuHD_Ht_eq_hCoef : ∀ (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ),
  sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m φ = hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ
```

**Final integrity and closeout.** The seven audited sources still match the first-line
SHA256 values and launch commit `4afebe84d` byte for byte. All seven contextual
interface/container hashes and the aggregate fingerprint of the 100 input files
also remain unchanged. Another worker advanced HEAD during the lock wait; the final
revision is recorded on the first line and does not change this audit's seven files.
The scoped `git diff HEAD` is empty. Only this report was edited by this auditor;
no scratch source, source repair, generated-root edit or commit was made. All audit
commands have returned; no audit-owned Lean/Lake process remains.

No uncertainty remains about the bridge's type, encoding soundness or the checked
producer-to-coefficient attachment. Production certificate validity and downstream
confinement remain outside this seven-file verdict. No suspected source erratum or
mathematical deviation was found. The procedural use of report-contained stdin in
place of a scratch file is disclosed above.

READY g2-audit-n5a2i-1
