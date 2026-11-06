Audited HEAD 1043ebed2e99f21abf228fb663b4501a8820d7a3; package commit 8980710d5; SHA256: KAM/EffectiveStability/Tube/Algebra/Bounds.lean=961dee1903e9c538e0769da2d13bd59d2c812f818adb46f9d782f34d4b6923d3; KAM/EffectiveStability/Tube/Algebra/C1.lean=5b8b6d43d581c8a99e84e131012586188e683050a744872b8133a9cc936cc316; KAM/EffectiveStability/Tube/Trig/Literal.lean=573911745df70d9798596e4e63a24664049b824165ea4356a79c64104a4e10bd; KAM/EffectiveStability/Tube/Trig/Model.lean=7d0b81a5a65bfda09d5852b86f58a0e03647041b265f0008daca57e889700c3e; KAM/EffectiveStability/Tube/Trig/Packed.lean=dbd0036ab46b4ba7cbc252d1d06466f740d87809d709d2797c833902e9e83498; KAM/EffectiveStability/Tube/Trig/Poly.lean=5b7aa531b933b76ad6adf93db9ea1e6d71ae3fba87ec81c84edcb335041cbdd1; KAM/EffectiveStability/Tube/Trig/Product.lean=9957e8147d234ce829d1dddc199cf81fe26c6e9a4984ebad9d965c328797f22e; KAM/EffectiveStability/Tube/Trig/Trunc.lean=9dcee0d27d2d657ad0ba95dfb4e87c8d6f3144ea94c15f6fbb3bda0d5bb08de8; KAM/EffectiveStability/Tube/Trig/Tube.lean=88c8ed014dfadf04973b4438f101c57b708db819ef8369d2ff47ab5e091c2826; KAM/EffectiveStability/Tube/Trig/TubeClose.lean=32f6588b827335913eaa5233b405e5fe0e898814d6a092c6e2c562061c075db2.

**Verdict: PASS WITH NOTES.** No blocking proof, statement, overflow, sign, rounding, or whitening
soundness defect was found in the ten N3 files. The notes below concern the consumer interface and
repository-wide validation, rather than a false exported theorem. This verdict covers the assigned
N3 brief; it does not certify N5, certificate data, or the T2-CONF confinement theorem.

Audit 1, 6 November 2026. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`.drafts/g2/{AUDIT-PKG-brief,WORKER-RULES,BRIEF-N3-Trig}.md`, the N3 handoff,
`sjs-rigor-plan.md` §§1.1/2.2/3.5, the SR gates (especially SR-4/SR-6), the phase-1
`ballft.py` conventions, and the `ApproxIntegral.lean` consumer. Reviewed the reused signed
packing/rounding primitives and compared the byte decoder to `LockN65/ZCodeX.lean`.

The ten files are byte-identical to commit `8980710d5`, including against the later shared HEAD
named above. `git diff inp...HEAD -- <owned directories>` is exactly these ten additions,
2,425 lines; `git diff 8980710d5 -- <owned directories>` is empty. The shared checkout had other
workers' changes before this audit and advanced during it. No package or other production file
was edited. The only retained audit edit is this report; an explicitly authorized scratch probe
was used under `.drafts/g2/scratch/audit/` and removed after validation.

| Audited file (relative to `KAM/EffectiveStability/Tube/`) | Lines | Brief attachment |
|---|---:|---|
| `Algebra/Bounds.lean` | 93 | scalar value and Leibniz error inequalities |
| `Algebra/C1.lean` | 259 | `C1Close` algebra, including six-term product derivative error |
| `Trig/Literal.lean` | 216 | packed-natural XOR inverse and byte-row whitening decode |
| `Trig/Model.lean` | 137 | binary scale, derivative, multiplication, truncation of `TP` |
| `Trig/Packed.lean` | 218 | signed round trip, `convFitsL1`, convolution decode, evaluation bridge |
| `Trig/Poly.lean` | 396 | finite trig semantics, derivative, norms, positivity, layouts |
| `Trig/Product.lean` | 262 | reflection, symmetry, Kronecker identity and product sign |
| `Trig/Trunc.lean` | 296 | hexagon, sub-layouts, rounding and full value/derivative error |
| `Trig/Tube.lean` | 309 | action monomials, derivatives, products, split and degree profiles |
| `Trig/TubeClose.lean` | 239 | value, two angle and three action partial-error semantics/algebra |

**Packed decoding and no overflow: PASS.** At `Trig/Packed.lean:164-178`, the actual guard is
`decide (2 * l1 a * (Mb : ℤ) < 2 ^ w) && b.all fun c => decide (c.natAbs ≤ Mb)`.
Here `Mb : ℕ`, and `l1` is proved equal to the sum of absolute values, not a signed sum.
For every convolution slot,

```
|(a*b)_m| ≤ Σ_i |a_i| |b_(m-i)| ≤ l1(a) maxAbs(b) ≤ l1(a) Mb.
```

Consequently `2 |(a*b)_m| < 2^w`, exactly the imported `SlotsBounded` condition. There is
no missing number-of-slots factor: the sum over `a` already counts all summands. Empty lists,
out-of-range reads, zero coefficients and `Mb = 0` are covered in the proof of
`abs_listConv_getD_le` (`:125-160`). The condition is sufficient and conservative, not necessary.

`unpackSlots_mul` (`:182-193`) additionally requires `w > 0`, positive input lengths, and both
`packOk` checks. The latter constrain the offset integer before `.toNat`, preventing negative
clamping or high-digit loss. `packSum_unpackSlots` reconstructs each actual packed operand;
`packSum_listConv` is the unconditional polynomial-evaluation identity; and the strictly bounded
convolution is decoded with `unpackSlots_packSum`. Thus no separate hypothesis that the product
passes `packOk` is missing. Negative packed integers and borrows between slots are legitimate.
The signed decoder accepts the endpoint `-2^(w-1)` on input, whereas `SlotsBounded` excludes both
half-width endpoints on output; that difference is harmless and only makes the supplier conservative.
Zero input lengths are deliberately excluded from the product theorem (the separate length decoder
still handles length zero); width zero is deliberately excluded from its inverse theorem.

`evalK_unpackSlots_mul` (`:199-214`) also requires `2*(Ca+Cb) < S`, zero padding for **both**
inputs, and full-layout symmetry for the second. `Layout.len` gives exactly `Na+Nb-1` product
slots. Digit overflow and Kronecker row wrap are separate obligations and both are present.
All these hypotheses are structural/numerical guards, not an assumed evaluation identity.
`hfit` is discharged by the proved `slotsBounded_listConv_of_l1` or the existing `convFits`
supplier; it is not a hidden conclusion-shaped premise.

Independent kernel probes verified signed convolution `[-3,2]*[4,-1]=[-12,11,-2]`, width-one
zero data, zero-length decoding and the negative half-width input. They also verified the
rejected-overflow example `w=4, a=b=[7]`: both inputs pass `packOk`, but the product decodes to
`[1]`, not `[49]`, and `convFitsL1` is false. A short-stride example independently shows the row
carry: for `Ca=Cb=1,S=4,i=j=6`, the product key is `(-2,1)` while the sum of input keys is `(2,0)`;
the exported strict stride guard rejects this case.

**Parity, symmetry and normalization: PASS, with interface note N1.** `Poly.lean:43-61` uses
`cos` for even and `-sin` for odd, with derivative sign `psgn false=1`, `psgn true=-1`.
`dlist` multiplies each slot by `psgn p * k_a`, then changes parity. The angle variables are
radians, exactly as in `ballft.py`; the global period-one KAM Fourier normalization is not being
silently applied to these application coordinates.

An independent one-mode computation fixes the normalization: put coefficient `1` at each of
`±k` for an even list, and coefficients `(1,-1)` at `(k,-k)` for an odd list. Their evaluations
are `2 cos θ` and `-2 sin θ`, respectively. Their derivatives are `-2 k_a sin θ` and
`-2 k_a cos θ`, agreeing with `dlist`. The odd list convolved with itself has coefficients
`1,-2,1` at `2k,0,-2k`, whose even evaluation is `2 cos(2θ)-2=-4 sin²θ`. The desired square is
`+4 sin²θ`, so the external minus sign in the odd–odd case is necessary. All four parity cases
are captured by `omega_mul` and `psgn (p && q)`; there is no missing factor of two.

`Product.lean:65-92` proves reversal is mode negation under the actual stride, length and
nonzero-column conditions. `symOk` is list equality, not a probabilistic/hash check. Only one
factor must have real complex semantics: `Re(A)*B=Re(A*B)` for real `B`, explaining why the
first factor need not have a symmetry/length hypothesis. No conclusion is lost by that generality.

**Truncation/rounding error: PASS.** `Trunc.lean:40-51` uses precisely
`|k1|+|k2|+|k1+k2|`, including the correct sign in the last term. The sub-layout shift is
`(C-C')*(S+1)` with `C'≤C` and `C+C'<S`. Padding columns of the truncated list are explicitly
zeroed. `rndS` (`:147-181`) rounds ties away from zero, is odd (including zero by `rndS_zero`),
is exact for `s=0`, and has integer residual at most `2^(s-1)` for `s>0`.

`truncRound_err_le` (`:253-273`) charges half an ulp for kept slots and the full `|c_i|` for
every dropped slot. The zero-padded `lsub` runs to the **maximum** input/embed length, so it
also charges modes outside the retained slice and handles short lists without losing error.
`l1_truncRound_le` sums these bounds; `wl1_truncRound_le` multiplies the same residuals by
`|k_a|` on the original layout. `c1Close_truncRound` and `TP.c1Close_trunc` give actual function
and partial-derivative closeness, not merely a coefficient-level assertion. The latter changes
`e` to `e-s` and scales both residual bounds by `2^(-e)`; its retained coefficient factor is
`2^s`. Hence both the dyadic scale and half-ulp accounting are consistent. Kernel probes covered
positive and negative ties, zero mantissas and `s=0`.

The angle product rule has exactly the six derivative terms
`P1*d0 + P0*d1 + Q1*e0 + Q0*e1 + e1*d0 + e0*d1`, from differentiating
`p*(g-q)+q*(f-p)+(f-p)*(g-q)`. Both differentiated remainder cross terms are present.
The tube version repeats this independently for its angle and action derivative families.

**Tube degrees and derivatives: PASS, with note N2.** Monomial differentiation is polynomial,
with no division by an action coordinate; zero actions and degree zero are covered.
`InBox r u` implies `r≥0` whenever used; a negative-radius box is empty, rather than an
unusable premise on the positive-radius intended application. Natural subtraction in the degree-zero
bound is harmless because its prefactor is zero, including at `r=0` (`0^0=1`). The generic finite
index set is more general than a degree-bounded datatype; degree bounds are supplied explicitly
where the profile regrouping needs them. `tmEval_mul`, `tmEval_split` and `tmEval_regroup`
retain the complete product before discarding any degrees.

**Whitening decode: PASS.** `Literal.lean:57-58` proves `unwhiten_whiten` for all salts, widths,
chunk counts and naturals by XOR cancellation; key quality and lack of chunk carries are performance
properties, not logical prerequisites. The stated chunk description is valid for the intended
`b=288,n≤8028`, since `(n+1)*2^64 < 2^288`.

The core `zkey`, `zvarX`, `zdecX`, `zdecsXAux`, `zdecsX` agree with the lock decoder and have no
application import. At `Literal.lean:152-184`, `zvarX_zwhiten` keeps the remaining bytes **and**
the next byte position synchronized, with enough whitening bytes for the bytes actually read.
`zdecX_zwhiten` consumes this count entry by entry; `zdecsX_zwhitenRows` (`:194-206`) advances
the row index as well. Its explicit `zdecC k n ≤ L` premise is necessary, checkable and adequate.

The independent nonzero-salt, multi-row probe used a multi-byte varint plus a trailing zero
entry. An initial audit fixture allotted three bytes although `zdecC 2 0x018180 = 4`, and its
claimed equality failed. With four whitened bytes it passes. A separate zero-byte-budget probe
also proves unequal decoding when the premise is omitted. This confirms that implicit trailing
zero bytes are not erroneously counted as free. The theorem equates the actual capped plain
and whitened decoders; it does not claim every arbitrary byte string is a canonical encoding,
or recover unbounded integers beyond the decoder's 24-byte/168-payload-bit cap.

**Nonblocking findings and suggested consumer safeguards.**

- **N1 — signed product and invariant preservation** (`Trig/Model.lean:55-64`,
  `Trig/Product.lean:236-249`; handoff lines 206-208). Quote:
  “The exact product (without the sign `psgn (p ∧ q)`, see `eval_mul`)”. `TP.mul` stores raw
  convolution. Treating it as an ordinary semantic multiplication for two odd operands would be
  wrong, as the one-mode calculation above shows. The statement and local docstring are explicit;
  this is an interface caveat, not a false theorem. Suggested safeguard: name the raw operation
  accordingly or expose a sign-corrected operation before using it as a generic checker primitive.
  No `ok`/`symOk` preservation theorem is exported for multiplication, derivative or truncation;
  N5 must recheck the relevant guards or obtain those lemmas. The brief permits these decidable
  structural checks, so this does not block the package.

- **N2 — assemble the full dropped-product derivative budget** (`Trig/Tube.lean:201-206,
  :253-292`; handoff lines 211-213). Quote: “The dropped degrees of a product … is at most
  `Σ_{d + e > L} A_d B_e r^{d + e}`”. `abs_dropped_le` itself is a value inequality. It would be
  wrong to reuse that scalar as both derivative errors. The full `TubeClose` result is available
  by composing the supplied split, zero-model, sum and profile lemmas: if angle-derivative profiles
  are `A1_d,B1_e`, the angle budget is
  `Σ_{d+e>L}(A1_d*B_e+A_d*B1_e)*r^(d+e)`, and the action budget is
  `Σ_{d+e>L}(d+e)*A_d*B_e*r^(d+e-1)`.
  Suggested safeguard: package that composition for N5, or retain these three explicit budgets in
  its proof. The handoff accurately discloses the missing convenience theorem; no missing
  analytic estimate was found. `TP` coefficient bounds instantiate the generic tube coefficient
  bounds directly.

- **N3 — slice regularity is the exported scope** (`Trig/TubeClose.lean:39-53`;
  handoff lines 214-215). Quote: `diffu_left : ∀ u, InBox r u → ∀ φ,
  DifferentiableAt ℝ (fun v => F v φ) u`. This does not assert joint differentiability or
  continuity of derivatives. Reading “C¹-close” as such a theorem would be wrong. The brief's
  partial-error semantics and shared `C1Close` interface require the weaker data actually proved.
  Suggested safeguard: N5's chain-rule attachment must supply the true functions' joint
  regularity independently; it cannot extract it from this predicate. The handoff already warns
  about this, so no overclaim of joint regularity is accepted here.

**Independent validation receipts.** All commands ran from the requested worktree. Lean/Lake
commands used `.drafts/g2/g2lake`, with no options and no direct Lean/Lake invocation. Its live
wrapper fixes `LEAN_NUM_THREADS=2`, nice 5, a 6 GiB memory cap and a shared lock; that prescribed
wrapper was used without modification. Builds/checks were serialized by it. No bare/full-library
build or application build was launched.

Every module in the table was built once with `.drafts/g2/g2lake build <Module>`, exit 0:
`Algebra.Bounds` 1.35 s; `Algebra.C1` 1.79 s; `Trig.Literal` 2.01 s; `Trig.Model` 2.19 s;
`Trig.Packed` 2.23 s; `Trig.Poly` 1.96 s; `Trig.Product` 2.23 s; `Trig.Trunc` 2.24 s;
`Trig.Tube` 2.00 s; `Trig.TubeClose` 2.00 s. Each printed `Build completed successfully`.
These were up-to-date/replayed builds, not forced recompilations. Warnings were deprecations
and unused simplifier/tactic warnings; no elaboration or heartbeat failure occurred.

One scratch file imported all ten modules and ran `#print axioms` for **every one of their 172
theorems**, plus 15 independent edge probes. Final command:
`.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N3TrigAudit1.lean`, exit 0, no errors.
Exact output classes: 153 declarations `[propext, Classical.choice, Quot.sound]`,
11 `[propext]`, 8 `[propext, Quot.sound]`. In particular `convFits_of_le`,
`slotsBounded_listConv_of_l1`, `packSum_unpackSlots`, `unpackSlots_mul`,
`evalK_unpackSlots_mul`, `pderiv_evalK`, `evalK_mul`, `c1Close_truncRound`,
`TP.c1Close_trunc`, `C1Close.mul`, `TubeClose.mul`, `tubeClose_tmEval_zero`,
`abs_dropped_le`, `sum_pairs_deg_eq` and `zdecsX_zwhitenRows` use only the three allowed
axioms; `unwhiten_whiten` uses `[propext, Quot.sound]`.

Supplemental replay: `.drafts/g2/g2lake env leanchecker --verbose` followed by the ten fully
qualified module names from the table, exit 0. Output was `replaying` for each of the ten modules;
this rechecks their declarations against imported environments, not a `--fresh` replay of Mathlib.
An initial `leanchecker --help` discovery attempt exited 1 (`Could not find any oleans for: Kam`):
this tool has no help flag and inferred a default target. The subsequent explicit-module replay
above succeeded.

The mandatory lint was run as `bash .drafts/g2/lint_noabi.sh`, following the worker rules'
15:25 update that explicitly replaces the full `scripts/lint_sources.sh` invocation and skips
`abi_hashes.py` (which would invoke Lake outside the required wrapper). ABI hashes were skipped.
Lint completed with **exit 1**: 1012 over-100-character lines in 28 files outside the two
owned directories, plus the stale generated-root check:
`KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)`.
Examples of the external width findings are `Tube/Check/Confine.lean:23`,
`Tube/Ecc/Sound.lean:86` and `Tube/Poly/Compose.lean:20`; these are recorded only as validation
context, not audited or repaired. No N3 width or forbidden-pattern finding appeared.
Exact successful output included `check_lean_modules: PASS (18386 Lean files, 0 comparator
configurations)`, `Ran 29 tests ... OK`, `Ran 8 tests ... OK`, and
`FROZEN-ANCHOR GUARD OK`. The errata renderer's check emitted no failure. This is a package-scoped
PASS WITH NOTES, **not** a clean repository-wide lint receipt. Generated roots were not rewritten.

A separate package-only masked-code scan checked all ten files for forbidden proof escapes,
all `set_option` directives, provider/root/application-data imports and `EuclideanSpace`:
zero findings. Every file has the copyright header, `module`, public imports, module docstring,
`@[expose] public section`, and at most 396 lines. No line exceeds 100 characters. The ambient
variables are `Fin 2 → ℝ` and `Fin 3 → ℝ`; mode pairs are exactly the representation requested
by the package brief. `git diff --check -- <owned directories>` passed.

**Performance evidence scope.** Reviewed, without rerunning the expensive numerical producer
or performance benchmark, the scratch generator, `info.json`, benchmark sources and existing
exit-0 `.out` receipts. The source has 40 separate `decide +kernel` product declarations and no
resource options; data definitions are identical to the base file. There are 65 literal
sub-definitions, at most 256 leaves each, with numerals at most 288 bits. Product-source SHA256:
`a4dd4e44e92a8ea841e931025157355cefe1439fd977aeadc440e6a3ff129b14`.
Operands have 6,101 and 7,321 slots, with 13,421 product slots, `w=173,S=121,Ca=25,Cb=30`.
The stored receipts give CPU `(14.87+2.81)-(9.68+2.46)=5.54` s over base for 40 declarations,
namely **0.1385 s/declaration**, consistent with the handoff's rounded ≈0.13 s and target ≤0.2 s.
The source and successful existing `K_fit.out` check the actual decoded operands with
`convFitsL1 173 826522765211252138442752`; existing symmetry/column/packOk receipts also pass.
These timings are reviewed worker evidence, not an independent timing measurement in this audit.
The handoff's multi-second slot-decoding caveat remains material to N5 scalability.

**Uncertainties, errata and deviations.** No suspected pinned-source mathematical erratum and
no production deviation introduced by this audit. The handoff's unsigned-raw-model product sign,
checked invariants, weaker slice regularity, compositional dropped derivative bounds and alternate
packed-natural whitening key are explicitly retained above. No repair, generated-root update,
frozen-file edit, manifest edit, commit or push was made.

READY g2-audit-n3-1
