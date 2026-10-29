# SO-AIF independent audit 1

Date: 2026-10-29. Verdict: **PASS WITH NOTES** for the explicitly scoped four-module slice, under the ruling in `SO-AIF-handoff.md:45`. No proof defect, unruled extra premise, signature mismatch, or missing declaration within this slice was found. This is infrastructure acceptance, not a frozen-anchor seal, certificate-checker soundness, or lunar confinement theorem.

## Scope and authority

Reviewed `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the local handoff with its AUDIT FOCUS. The user's exact report destination overrides the generic brief's MAIN-worktree destination. Source contracts are `/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §A, `/root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md` Revision 3 §§5,7 and Appendix A, and `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`.

Audited HEAD `1d59185ccfde6035c5d20ebdca061d77a69fc3df`; `inp` and the merge base were both `8aa7e422c350037616af06004f80f76bc5087771`. The complete `git diff inp...HEAD` contains precisely these new files (586 added lines):

| File under `KAM/Certificate/Arith/` | Lines | Maximum line width |
|---|---:|---:|
| Interface.lean | 89 | 98 |
| PiEnclosure.lean | 63 | 98 |
| Transcendental.lean | 71 | 96 |
| Roots.lean | 363 | 100 |

No provider or frozen theorem is introduced or sealed; frozen-provider type equality and seal-body tests are therefore inapplicable. These modules import neither providers nor frozen theorem anchors. I/N/P blueprint-node and headline comparisons are superseded here by the handoff's explicit SO arithmetic focus. `PiHigh` is a pre-existing dependency, not an additional audited file.

## Declaration-by-declaration review

All names are under `KAM.Certificate`. Locations below are relative to `KAM/Certificate/Arith/`. “Signed” means the declaration appears in the draft §A. Every one of the 16 unchanged signed headers matched byte-for-byte, preserving all explicit/implicit binders, laws, quantifier order, carriers and conclusions. The non-placeholder bodies of `CC.toC`, `CC.conj`, and `checkRootEnclosure` also matched byte-for-byte. Placeholder bodies were reviewed against the specified semantics.

| Node/location | Lean declaration | Verdict | Reason |
|---|---|---|---|
| Interface:31 | `CertArith` | PASS | Signed data class and all fields match, including outward rational conversions. |
| Interface:50 | `LawfulCertArith` | PASS | Signed law class matches in full; ordinary backend laws, no packaged target conclusion. |
| Interface:70 | `CC` | PASS | Signed real/imaginary data fields match. |
| Interface:75 | `CC.toC` | PASS | Signed type and body match; exact denotation. |
| Interface:78 | `CC.conj` | PASS | Signed type and body match; exact backend negation. |
| Interface:80 | `CC.toC_conj` | PASS | Signed; uses `val_neg`. |
| Interface:85 | `CC.toC_zero` | PASS | Signed; uses `val_ofInt`. |
| PiEnclosure:29 | `PiEnclosure` | PASS | Signed fields match; data, not a hidden proof assumption. |
| PiEnclosure:37 | `checkPiEnclosure` | PASS | Signed; both endpoint tests conservatively account for rounding. |
| PiEnclosure:43 | `checkPiEnclosure_sound` | PASS | Signed; Machin bounds, outward conversions, and rounding laws imply the exact radius claim. |
| Transcendental:27 | `ratExpUp` | PASS | Signed; rational halving/Taylor/squaring, with valid coarse fallback. |
| Transcendental:33 | `sqIter_cast` | PASS | Additional algebra helper; iteration equals the indicated power for every rational input. |
| Transcendental:42 | `exp_le_ratExpUp` | PASS | Signed, including only the original `0 ≤ q` premise. Handles every `s,N`. |
| Roots:39 | `checkRootEnclosure` | PASS | Signed body matches, including endpoint nonnegativity. |
| Roots:42 | `rpow_mem_of_checkRootEnclosure` | PASS | Signed; positive degree permits monotone inverse real power. |
| Roots:62 | `sqrt_mem_of_checkRootEnclosure` | PASS | Signed specialization at degree 2. |
| Roots:72 | `CertBall` | PASS | Supporting centre/radius data. |
| Roots:77 | `CertBall.Mem` | PASS | Exact complex norm-ball membership. |
| Roots:81 | `CC.normUp` | PASS | Upward L1 norm bound. |
| Roots:83 | `CC.norm_le_normUp` | PASS | Triangle/L1 estimate and exact absolute-value law. |
| Roots:89 | `CC.normUp_nonneg` | PASS | Follows from the norm bound. |
| Roots:92 | `norm_le_of_re_im` | PASS | Coordinate absolute bounds imply the complex norm bound. |
| Roots:101 | `CertBall.ofRat` | PASS | Outward rational conversion gap bounds constant-centre error. |
| Roots:106 | `CertBall.oneBall` | PASS | Exact unit ball; approved rename avoids the previous `one` clash. |
| Roots:109 | `CertBall.plus` | PASS | Sum radii plus both centre-rounding errors. |
| Roots:114 | `CertBall.mulReErr` | PASS | Real centre-product error includes two multiplications and the rounded subtraction. |
| Roots:118 | `CertBall.mulImErr` | PASS | Imaginary centre-product error includes two multiplications and rounded addition. |
| Roots:122 | `CertBall.times` | PASS | Includes both linear radius terms, the radius product, and centre-rounding errors. |
| Roots:134 | `CertBall.mem_ofRat` | PASS | Sound enclosure of each rational constant. |
| Roots:148 | `CertBall.mem_one` | PASS | Unit centre denotes 1 and radius denotes 0. |
| Roots:155 | `CertBall.mem_plus` | PASS | Only input membership and standing backend laws. |
| Roots:182 | `CertBall.mulReErr_bound` | PASS | Derived error bound, not a new assumed arithmetic law. |
| Roots:198 | `CertBall.mulImErr_bound` | PASS | Derived error bound, not a new assumed arithmetic law. |
| Roots:212 | `CertBall.mem_times` | PASS | Proves input radii and upward multiplier operands nonnegative before invoking `upMul_ge`. |
| Roots:267 | `CertBall.expAux` | PASS | Natural recursion computes term and partial-sum balls. |
| Roots:273 | `CertBall.expAux_mem` | PASS | Simultaneously proves term and sum enclosure, including order zero. |
| Roots:303 | `certCExp` | PASS WITH NOTES | Signed type matches; correctness is restricted to unit-disc input balls under the accepted ruling. |
| Roots:308 | `certCExpSmall` | PASS | Computational sufficient test, using L1 norm overestimate and upward addition. |
| Roots:311 | `certCExpSmall_sound` | PASS | Backend comparison implies `‖z.toC‖ + val zRad ≤ 1`. |
| Roots:323 | `certCExp_sound_of_small` | PASS WITH NOTES | Accepted replacement for signed `certCExp_sound`; no other extra premise. |

The 19 public theorems all have only the three permitted axioms, independently checked below. Additional helpers do not replace an unsigned source theorem or a frozen result.

## Definition classification and proof review

- `CertArith`, `CC`, `PiEnclosure`, and `CertBall` are honest data interfaces. `LawfulCertArith` contains the signed standing arithmetic laws. No theorem conclusion is smuggled into a field or typeclass.
- `CC.toC`, `CC.conj`, and `CertBall.Mem` are the intended denotation, conjugation and metric-ball predicate on their whole carriers. `CC.normUp` is a conservative computed norm bound under the signed laws.
- `checkPiEnclosure` compares an upper bound for `centre - rad` against the rational lower endpoint, and compares an upper bound for `hi + addErr centre rad` against the computed sum. Thus the second test implies `hi ≤ centre + rad` despite rounded addition. Its success implies radius nonnegativity; it does not assume it.
- `ratExpUp` uses a Taylor estimate only when `q / 2^s ≤ 1` and `N > 0`; with the signed premise `q ≥ 0`, this is exactly the real exponential-bound domain. Repeated squaring raises the bound to `2^s`. The fallback `3^⌈q⌉₊` is mathematically valid for every nonnegative `q`, since `exp 1 < 3`; it is not a junk value used to escape a case. The definition has no certified upper-bound claim for negative `q`, as in the signature.
- `checkRootEnclosure` is exactly the signed rational test. Its degree-zero behavior is total but unused by the general root theorem, which explicitly and originally requires `m > 0`. No silent positivity premise was added.
- `CertBall.ofRat`, `oneBall`, `plus`, `mulReErr`, `mulImErr`, and `times` are genuine outward ball constructions. A raw `CertBall` may carry a negative radius, representing an empty ball; the soundness implications then have no input member. For multiplication the proof obtains nonnegative radii from actual membership, so no unjustified use of `upMul_ge` occurs. The product radius bounds `r₁(‖c₂‖ + r₂) + ‖c₁‖r₂` plus the two centre errors.
- `CertBall.expAux` computes `w^m/m!` and the sum through degree `m`. `certCExp` uses the sum through degree `N`, i.e. `N+1` terms, and adds the outward rational `eRem (N+1)`. Hence `N=0` needs no added positivity premise. `Complex.exp_bound` is invoked with positive remainder order `N+1` and `‖w‖ ≤ 1`, derived from the input-ball hypothesis and `hsmall`.
- `certCExpSmall` is a sufficient guard, not a complete decision procedure for Euclidean unit-ball containment. The signed comparison laws are one-sided, so false negatives are permitted. Under the soundness theorem, a successful guard supplies the legitimate domain restriction; it does not assume exponential correctness.

## Completeness, deviations and limitations

Within the four named modules the signed slice is complete, modulo precisely the ruled replacement of `certCExp_sound`. Revision 3 §7:401 also assigns `Arith/Rat` to SO-AIF and Appendix A / draft lines 131–133 declare the two rational backend instances. The explicit handoff ruling at line 45 excludes their late addition from this audit and assigns it to follow-up. Their absence is therefore **not a finding** here; broader Revision 3 package completion must still supply them.

Accepted deviation: draft `SOSignatures.lean:232–234` states `certCExp_sound` without a size restriction. The implementation exports `certCExp_sound_of_small` instead. `Roots.lean:323–327` adds only `‖z.toC‖ + val zRad ≤ 1`, a domain bound, with `certCExpSmall_sound` providing a checkable sufficient condition. The implementation is sound under that contract. Downstream uses must invoke this guarded theorem or separately perform justified argument reduction; an unconditional theorem is not supplied by this audit.

A direct mathematical counterexample to the old theorem for this implementation is the exact rational backend with `z=0`, `zRad=2`, `N=0`, and `w=2`: the computed centre is 1 and the output radius is `eRem 1 = 2`, but `|exp 2 - 1| > 2`. This is an analytic calculation, not a claim of an independently replayed concrete-backend test. It confirms the need for the ruled restriction. The stronger prose claim in `Roots.lean:22–25` about impossibility for *any* interface implementation is not needed for acceptance; this audit establishes the limitation of this algorithm and the validity of the replacement.

No new pinned-source erratum was found. The unrestricted draft contract and its accepted domain repair are the design defect/deviation to retain; `Complex.exp_bound` itself is used with its correct hypotheses. No changes to definitions, laws, frozen files, or signatures were made by this auditor. No production backend, actual numerical certificate, replay-performance guarantee, or downstream consumer integration is certified here.

## Independent validation

All Lean/Lake commands initiated by this audit were serialized and used `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth, or synthesis overrides were used. No source files were edited. Scratch probes/logs were kept under this worktree's `.lake/abi-scratch/` and removed after recording their results.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soaif KAM.Certificate.Arith.Interface KAM.Certificate.Arith.PiEnclosure KAM.Certificate.Arith.Transcendental KAM.Certificate.Arith.Roots
```

Exit 0. The gate runs `nice -n 5 lake build` internally. Output:

```text
[inp-gate] slot 1 acquired 12:09:13 for KAM.Certificate.Arith.Interface KAM.Certificate.Arith.PiEnclosure KAM.Certificate.Arith.Transcendental KAM.Certificate.Arith.Roots
⚠ [2840/2844] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
Build completed successfully (2844 jobs).
```

The sole warning is in pre-existing `PiHigh`, outside the audit slice.

### Draft-type and axiom probe

A Python source comparison checked all 16 unchanged signed headers exactly, the entire three non-placeholder signed definition bodies exactly, and both signed class field lists plus the signed data structure fields exactly. An independent Lean probe copied every signed function/theorem header from the draft under a fresh `audit_...` name and discharged it with the actual export applied to its original explicit binders. For classes/structures, the full field text comparison supplies the equality check; no frozen sealing is involved.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOAIFAudit.lean
```

Final exit 0; complete theorem axiom output:

```text
'KAM.Certificate.CC.toC_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CC.toC_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkPiEnclosure_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqIter_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.exp_le_ratExpUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.rpow_mem_of_checkRootEnclosure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqrt_mem_of_checkRootEnclosure' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CC.norm_le_normUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CC.normUp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_le_of_re_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_ofRat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_plus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mulReErr_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mulImErr_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_times' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.expAux_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpSmall_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certCExp_sound_of_small' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The initial scratch harness mistakenly supplied bare `@export` terms to already-bound declarations and exited 1 with type mismatches. This was a probe-construction error; correcting applications to the original binders produced the clean final result above. No package source was changed.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Arith.Interface KAM.Certificate.Arith.PiEnclosure KAM.Certificate.Arith.Transcendental KAM.Certificate.Arith.Roots
```

Exit 0. Exact output:

```text
replaying KAM.Certificate.Arith.Roots
replaying KAM.Certificate.Arith.Transcendental
replaying KAM.Certificate.Arith.PiEnclosure
replaying KAM.Certificate.Arith.Interface
```

### Source hygiene and protected paths

Masked-code scan of all four files found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `EuclideanSpace`, or `set_option`. Each has the required copyright, `module`, public imports, module docstring and `@[expose] public section`. All declarations are inside `KAM.Certificate` or its `CC`/`CertBall` namespaces; no root declaration is introduced. A scan of declaration basenames across existing `KAM/**/*.lean` found no reused short name among the 24 additional public helpers. The `oneBall` rename is present. File sizes and widths are listed above.

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exited 0 with empty output. Frozen files, manifest and generated files are unchanged.

### Repository lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the explicitly permitted generated-root notice. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1294 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module check, frozen-anchor guard and all 144 elaborated ABI hashes pass. The generated root was not regenerated, as required by the audit brief.

## Handoff

The four-module arithmetic slice passes with the accepted guarded-exponential deviation and the brief's generated-root exception. The rational backend remains the explicitly excluded follow-up. No frozen I/N/P anchor is claimed seal-ready by this report. The only repository file written by the audit is this exact report; scratch files were removed and no state-changing git command was run.
