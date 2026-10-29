# SO-POLY-A independent audit 1

Verdict: **PASS WITH NOTES** for the requested SO-POLY-A infrastructure slice. All 18 signed declarations pass exact header comparison (ignoring whitespace) and fresh fully qualified Lean type probes; all 34 new named public declarations were reviewed. The slice is complete. No frozen theorem is sealed or claimed seal-ready by this infrastructure package, and no SO-POLY-B consumer is certified by this report.

Audited 2026-10-29 in `/root/code/KAM-inp-sopolya`, HEAD `a25e06e8d64b1f42c0b409c2bb21375484c7baaf`, comparison ref `inp` = `c97c960083d7c8900659d434e5c759ebff9e1a3e`. The full `git diff inp...HEAD` adds only `KAM/Certificate/Arith/Mantissa.lean` and `KAM/Certificate/Poly/Packed.lean` (510 lines). The existing untracked handoff was read and left untouched. The user's explicit absolute report destination overrides the generic brief's main-worktree destination.

Authority read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, this worktree's `docs/tracks/SO/audits/SO-POLY-A-handoff.md`, `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §A and the SO-POLY-A portion of §B′, and `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` Revision 6 (§1.16, §7, Addendum 6 and the matching Appendix signatures). The SO-specific signed surface controls this audit, rather than unrelated I/N/P theorem statements. The imported frozen definition `KAM/Frozen/Defs/ComplexStrip.lean` was also read and its manifest state checked.

## Declaration review

Every name below has prefix `KAM.Certificate.`. Locations are line numbers in Mantissa (A) or Packed (B). Each row is PASS; the package-level notes concern integration scope and permitted generated-root staleness. Helpers have distinct names and genuine algebraic premises; none assumes a hard proof step or adds a premise to a signed result.

| Node | Declaration | Line | Verdict | Reason |
|---|---|---:|---|---|
| A: mantissa | `mantCheck` | 28 | PASS | Backend equality against both outward rational conversions. |
| A: mantissa | `mantCheck_sound` | 31 | PASS | Exactly the signed lawful-backend soundness contract. |
| A: dyadic | `ofDyadic` | 44 | PASS | Returns the rounded candidate only after exactness check. |
| A: dyadic | `ofDyadic_sound` | 48 | PASS | Success alone gives exact denotation; no extra premise. |
| A: backend | `CertFixed.toMant` | 59 | PASS | Matching precision returns the actual integer field; otherwise none. |
| A: backend | `CertFixed.mantCheck_m` | 65 | PASS | All natural precisions, including zero; exact floor/ceiling on grid. |
| B: packing | `packSum` | 28 | PASS | Signed geometric evaluation, zero for empty list. |
| B: helper | `packSum_nil` | 31 | PASS | Empty evaluation identity. |
| B: helper | `sum_map_range_eq` | 33 | PASS | List sum equals corresponding finite sum. |
| B: helper | `packSum_cons` | 41 | PASS | Head/tail recurrence with base 2^w. |
| B: helper | `packSum_append` | 53 | PASS | Append shifts by exactly the first length. |
| B: helper | `packSum_eq_sum` | 63 | PASS | Equivalent finite geometric sum. |
| B: helper | `packShiftAux` | 75 | PASS | Structural list recursion, shift offset and signed accumulators. |
| B: packing | `packShift` | 83 | PASS | Shift loop initialized at zero; kernel reducible. |
| B: helper | `packShiftAux_eq` | 85 | PASS | Accumulator invariant for every offset and accumulator. |
| B: packing | `packShift_eq` | 105 | PASS | Unconditional packing correctness, including w = 0. |
| B: injectivity | `SlotsBounded` | 110 | PASS | Strict signed bound 2|c| < 2^w, unchanged. |
| B: injectivity | `packSum_injective` | 113 | PASS | BOTH slot bounds, equal lengths and equal packing retained. |
| B: convolution | `listConv` | 141 | PASS | Exact zero-extended Cauchy product; empty if either factor empty. |
| B: helper | `sum_mul_sum_range_cauchy` | 148 | PASS | Finite Cauchy identity, explicit vanishing tails; handles zero lengths. |
| B: convolution | `packSum_listConv` | 207 | PASS | Exact integer identity, no width or size premise. |
| B: helper | `maxAbs` | 233 | PASS | Maximum natural absolute value, empty maximum zero. |
| B: helper | `natAbs_le_maxAbs` | 235 | PASS | Membership bound for that maximum. |
| B: helper | `abs_getD_le` | 244 | PASS | Bound includes zero-default out-of-range entries. |
| B: convolution | `convFits` | 254 | PASS | Decidable sufficient min-length times maxima strict bound. |
| B: helper | `abs_conv_entry_le` | 258 | PASS | Counts at most min(length a, length b) nonzero pairs. |
| B: convolution | `slotsBounded_listConv` | 306 | PASS | Passing concrete check implies strict signed slot bound. |
| B: helper | `packSum_flatten` | 323 | PASS | Equal block lengths give exact block-base evaluation. |
| B: shards | `packSum_flatten_mul_shards` | 339 | PASS | Exact signed shard identity; only signed block-length premises. |
| B: helper | `slotRep` | 353 | PASS | Centered residue representative, choosing negative at the tie. |
| B: helper | `intSlotsBoundAux` | 356 | PASS | Structural natural-length recursion, checks each digit and zero remainder. |
| B: decoding | `intSlotsBound` | 365 | PASS | Starts decoding at slot zero. |
| B: helper | `intSlotsBoundAux_sound` | 367 | PASS | Existence, length, offset bounds and exact reassembly; no injectivity claim. |
| B: decoding | `intSlotsBound_sound` | 409 | PASS | Exactly the signed existential per-slot guarantee. |

## Definition classification and soundness

All 13 definitions implement their intended total objects; there are no new structures, abbreviations or bundled proof fields. `mantCheck`, `ofDyadic`, `CertFixed.toMant`, `packSum` and `SlotsBounded` have the specified concrete bodies. `packShiftAux`/`packShift` use natural shifts on separate positive/negative accumulators, increasing the offset by addition of `w`, with a single integer subtraction at termination. The implementation does not multiply by a large power in each packing iteration. `listConv` is mathematical convolution, not a production fallback or advice assertion. `maxAbs` and `convFits` use actual list contents. `slotRep`, `intSlotsBoundAux` and `intSlotsBound` peel centered signed residues using integer remainder/division and reject a nonzero terminal remainder.

The empty-list and out-of-range defaults are the intended zero extensions, not junk values used to bypass a claim. The decoder terminates even at width zero because length decreases. It can reject representations outside its chosen centered range; its theorem requires only soundness on success, not completeness for every possible log budget. No positivity, anti-carry, nonempty-list, or scale assumption was silently added.

The injectivity proof uses the two strict signed bounds to force the first digit difference below one base, then recurses on tails. The exact product and shard identities follow polynomial evaluation/Cauchy regrouping, including empty factors and zero block lengths. The convolution bound counts the nonzero index set using injectivity of `i ↦ k-i` on `i ≤ k`. Decoder soundness proves divisibility before reassembly and keeps the exact terminal remainder condition. Mantissa soundness sandwiches the denotation between the two outward conversions; fixed-backend completeness proves floor and ceiling exact on the dyadic grid.

## Checks and exact outputs

All Lean/Lake commands below ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5` (the compile-gate script supplies nice for the build). No heartbeat, recursion-depth or synthesis overrides were used. Probe files were confined to `.lake/abi-scratch/` and removed after their results were copied here.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sopolya KAM.Certificate.Arith.Mantissa KAM.Certificate.Poly.Packed
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 15:17:26 for KAM.Certificate.Arith.Mantissa KAM.Certificate.Poly.Packed
⚠ [2840/2903] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
Build completed successfully (2903 jobs).
```

The replayed PiHigh warning is in an unchanged dependency; there were no warnings in the audited files. The job count includes replayed cached dependencies; no clean or from-scratch library rebuild was requested.

2. Signature/body review and type/axiom probe:

A scratch Python script extracted each signed declaration header and checked equality after whitespace removal against SOSignatures. It also scanned other KAM and Mathlib source declarations for matching short names. Output:

```text
SIGNED headers exact ignoring whitespace: 18/18
New named declarations: 34; theorems: 21
KAM/Certificate/Arith/Mantissa.lean: lines=90 maxLine=98
KAM/Certificate/Poly/Packed.lean: lines=420 maxLine=99
Other KAM/Mathlib declaration short-name matches: []
```

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOPolyaAudit.lean
```

Final exit 0. For each signed declaration the probe independently stated its complete signature as a `∀`-type and assigned `@KAM.Certificate.<name>` to it, preserving implicit/explicit binders and their order. Concrete signed bodies were compared directly with the draft. The probe also printed axioms for every new named theorem and ran the boundary examples described below. It emitted only unused-binder warnings from anonymous signature probes. There is no provider/frozen-theorem type or seal-body probe to perform: this package introduces no provider or frozen theorem.

Exact `#print axioms` output:

```text
'KAM.Certificate.mantCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ofDyadic_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.mantCheck_m' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_nil' depends on axioms: [propext]
'KAM.Certificate.sum_map_range_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_cons' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packSum_append' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packSum_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packShiftAux_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packShift_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packSum_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_mul_sum_range_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_listConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.natAbs_le_maxAbs' depends on axioms: [propext]
'KAM.Certificate.abs_getD_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.abs_conv_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotsBounded_listConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_flatten' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_flatten_mul_shards' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intSlotsBoundAux_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intSlotsBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Arith.Mantissa KAM.Certificate.Poly.Packed
```

Exit 0. Exact output:

```text
replaying KAM.Certificate.Poly.Packed
replaying KAM.Certificate.Arith.Mantissa
```

4. Full source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the explicitly permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1315 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All substantive lint gates passed. The generated root was not regenerated.

5. Additional read-only checks:

`git diff --check inp...HEAD` exited 0, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0, empty. Scans of both audited files found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `native_decide`, `EuclideanSpace`, `implemented_by`, `extern`, `ofReduceBool` or partial recursion. Both files have copyright, `module`, public imports, module documentation and `@[expose] public section`; all declarations remain inside `KAM.Certificate` (or its `CertFixed` namespace), with no root declaration shadowing. Every file is below 1500 lines and every line below 101 characters.

A recursive KAM import-source walk visited 20 modules. Its only frozen dependency is `KAM.Frozen.Defs.ComplexStrip`, manifest state `SEALED`; no provider or DRAFT_SORRY theorem is imported. There are no newly introduced hypotheses hidden in instances or fields.

## Notes, refutation attempts and defects

- **F12 boundary retained.** `intSlotsBound_sound` (Packed:409–413) gives a list of the requested length, bounds `|e_i| ≤ 2^(logs i)` and exact packing. It does not give `SlotsBounded`, uniqueness or equality with an externally supplied convolution. A fresh kernel example accepts `intSlotsBound 4 1 (fun _ => 3) (-8)`, while `¬ SlotsBounded 4 [-8]` follows by simplification. Thus a successful decode really can reach the excluded half-base boundary. Another kernel example confirms `packSum 4 [16,-1,0] = 0`. Neither invalidates the signed claims; both prevent interpreting them as an unconditional slot reconstruction theorem. POLY-B must establish the exact-side and reconstructed-advice-side bounds before injectivity; a bound on decoded residual digits alone does not bound reconstructed advice.
- **F13 remains downstream.** This slice has no `scale` argument, overlap-add or packed-product acceptance theorem. Natural subtraction at `scale = 0` cannot encode a half-unit budget. Revision 6's positive-scale guards and reconstruction checks belong to POLY-B and are not audited here.
- **Kernel reduction checks.** In addition to the three landed kernel examples, the scratch probe checked zero-width signed packing, empty convolution, `[-2,3] * [4,-5] = [-8,22,-15]`, zero-length/zero-width decoding, nonzero remainder rejection, the negative tie representative and carry cancellation. An initial auditor-written example incorrectly expected positive `8` to pass a one-slot centered decode; it correctly failed because decoding chooses `-8` and leaves a nonzero remainder. That test was corrected to input `-8`. A second initial probe needed `SlotsBounded` unfolded to synthesize its decision. Neither initial probe failure was a package defect; the final probe passed.
- **Metadata only.** The handoff calls Packed 418 lines; the committed file is 420 lines. This does not affect any cap or declaration.

No suspected mathematical defect in the audited signed surface or its Revision 6 blueprint was found. No external pinned mathematical source was changed or independently re-audited: these results are elementary certificate arithmetic specified by the local signed design. No implementation deviation was introduced. Report-only edits and temporary scratch probes were the auditor's sole writes; generated files, manifest and frozen sources were left untouched. Remaining uncertainty is consumer correctness and production-scale replay performance, outside SO-POLY-A's specified slice.
