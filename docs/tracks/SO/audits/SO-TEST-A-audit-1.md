# SO-TEST-A independent audit 1

Overall verdict: **PASS WITH NOTES** for this round. T2 and T3 establish genuine,
unconditional `CertifiedTorus` conclusions; TR establishes checker acceptance only.
T2d establishes exactly five light sub-checks and its frequency enclosure. Its full
acceptance and torus results remain **unproved**, explicitly permitted by AUDIT FOCUS.
No frozen anchor is introduced or sealed by this package, so a provider/seal-body
probe is not applicable. The signed §J exports were checked directly instead.

## Scope and comparison

Audited worktree: `/root/code/KAM-inp-sotesta`, branch `inp-sotesta`, HEAD
`26f45b6f70fddafa5c68c5b8ada654e0cdc533bf`. The compared `inp` tip at inspection was
`3ed3e6e75e3dd406df76c3f20bce83c542037ce9`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the specified package-audit brief,
SO-TEST-A-handoff.md including AUDIT FOCUS, the original SO-TEST brief, the signed
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` §J:1120–1170, SO-LEAN-DESIGN §8,
SO-PYALIGN (especially §6), track I statement and the I-G1 frozen statement and
relevant definitions. There is no `docs/tracks/SO/statement.md`; the signed SO design
is the local statement authority. This package implements SO §8/§J, not a new
blueprint-I/N/P theorem node. The inherited `g1_explicit` implements `bpI:p2:g1`.

Ran the required **full** `git diff inp...HEAD` comparison: 27 files, 4510 insertions.
Git reports multiple merge bases, selecting
`2284e9f4863da6cd53e6b4b7f51756dbffe1cd42`; the other base is
`def80c79e1a747ae2e10e11ee41d50bb4e57f707`. This warning is retained, not silently
replaced with a different comparison. The diff includes inherited SO-SOUND-A/B
and SO-GRAPH code and their handoffs/audits. SO-TEST-A's actual implementation
commit `5496a462` adds precisely the eight toy modules and the emitter (9 files,
1945 insertions). The inherited contracts and their use were inspected; their
prior independent reports remain the provenance for the broader analytic packages.
Fresh axioms were also checked for all 40 inherited public theorems in this diff.
The toy verdict is not a new full statement audit of those inherited packages.

The user's explicit output path overrides the generic brief's main-worktree
output convention. Only this report is retained as a repository change.

## Results per signed target

| Target | Verdict | Established result / limit |
|---|---|---|
| T2 / `toyCert2` | PASS WITH NOTES | Signed data type, whole-checker acceptance, exact reference frequency enclosure, unconditional `toyCert2_torus`; generated-root lint note only. |
| T3 / `toyCert3` | PASS WITH NOTES | Signed Hamiltonian identity, positive residual, whole acceptance, frequency enclosure and unconditional `toyCert3_torus`; generated-root lint note only. |
| TR / `toyRatCert` | PASS WITH NOTES | Signed checker-only result. Reference `(1/4,1/2)` is resonant; no torus theorem is claimed. |
| T2d / `toyCert2d` | PASS WITH NOTES (partial only) | Exact data, five named sub-checks and enclosure. `toyCert2d_passes` and `toyCert2d_torus` are absent and remain unpaid; permitted for this round. |
| Rotated T2 | Not supplied | No rotated toy data in `certificates/so-toys/`; original brief makes this conditional on data existing. |

## Declaration-by-declaration review

All names below are in `KAM.Certificate`. “Exact data” means the emitted body,
all record fields, and literal encoding were checked as described below; it does
not mean that an arbitrary certificate or an unfinished T2d check passes.

| Node / file | Lean declaration | Verdict | Reason / classification |
|---|---|---|---|
| SO §8/§J; ToyLit:25 | `toyNat` | PASS | Total base-10^90 fold; canonical decimal chunks are used by the emitter. |
| SO §8/§J; ToyLit:28 | `toyPos` | PASS | Exact integer cast of toyNat. |
| SO §8/§J; ToyLit:31 | `toyNeg` | PASS | Exact negation of toyNat. |
| SO §8/§J; ToyLit:34 | `toyQ` | PASS | mkRat; positive emitted denominators, exact rational normalization. |
| SO §8/§J; ToyLit:37 | `toyScaledPoly` | PASS | Maps ordered keys and integer pairs to coefficients over the common denominator. |
| SO §8/§J; ToyLit:40 | `toyNat_test` | PASS | Kernel evaluation of the two-chunk radix identity. |
| SO §8/§J; Toy2Data:21 | `toyT2Params` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:27 | `toyT2Ham` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:30 | `toyT2WeightH` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:33 | `toyT2Weight` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:36 | `toyT2Centre` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:42 | `toyT2Radius` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:45 | `toyT2Box` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:50 | `toyT2Emb` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:56 | `toyT2Wit` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:59 | `toyT2GramInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:62 | `toyT2TorsInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:71 | `toyT2CfgFull` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:74 | `toyT2CfgLow` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:77 | `toyT2Pi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:84 | `toyT2RootLo` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:88 | `toyT2RootHi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:91 | `toyT2AlgCoeffs` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2Data:95 | `toyT2Cert` | PASS | Whole concrete record assembled from the audited data, including expHalvings/expOrder. |
| SO §8/§J; Toy2dData:21 | `toyT2dParams` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:30 | `toyT2dHam` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:34 | `toyT2dWeightH` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:37 | `toyT2dWeight` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:40 | `toyT2dCentre` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:58 | `toyT2dRadius` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:61 | `toyT2dBox` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:73 | `toyT2dEmb` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:92 | `toyT2dWitTerms1` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:111 | `toyT2dWitTerms2` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:151 | `toyT2dWitTerms3` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:216 | `toyT2dWitTerms4` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:298 | `toyT2dWitTerms5` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:380 | `toyT2dWitTerms6` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:488 | `toyT2dWitTerms7` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:610 | `toyT2dWitTerms8` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:727 | `toyT2dWitTerms9` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:809 | `toyT2dWitTerms10` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:891 | `toyT2dWitTerms11` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:966 | `toyT2dWitTerms12` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:1009 | `toyT2dWitTerms13` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:1033 | `toyT2dWitTerms14` | PASS | Exact ordered reciprocal-witness chunk; 40 terms, except Terms14 has 11. |
| SO §8/§J; Toy2dData:1038 | `toyT2dWit` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1047 | `toyT2dGramInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1050 | `toyT2dTorsInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1081 | `toyT2dCfgFull` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1091 | `toyT2dCfgLow` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1101 | `toyT2dPi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1108 | `toyT2dRootLo` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1117 | `toyT2dRootHi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1125 | `toyT2dAlgCoeffs` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy2dData:1129 | `toyT2dCert` | PASS | Whole concrete record assembled from the audited data, including expHalvings/expOrder. |
| SO §8/§J; Toy3Data:21 | `toyT3Params` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:29 | `toyT3Ham` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:33 | `toyT3WeightH` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:36 | `toyT3Weight` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:39 | `toyT3Centre` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:53 | `toyT3Radius` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:56 | `toyT3Box` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:69 | `toyT3Emb` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:85 | `toyT3Wit` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:88 | `toyT3GramInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:92 | `toyT3TorsInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:114 | `toyT3CfgFull` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:117 | `toyT3CfgLow` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:120 | `toyT3Pi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:127 | `toyT3RootLo` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:132 | `toyT3RootHi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:136 | `toyT3AlgCoeffs` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; Toy3Data:140 | `toyT3Cert` | PASS | Whole concrete record assembled from the audited data, including expHalvings/expOrder. |
| SO §8/§J; RatData:21 | `toyTRParams` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:26 | `toyTRHam` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:29 | `toyTRWeightH` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:32 | `toyTRWeight` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:35 | `toyTRCentre` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:38 | `toyTRRadius` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:41 | `toyTRBox` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:44 | `toyTREmb` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:47 | `toyTRWit` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:50 | `toyTRGramInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:53 | `toyTRTorsInv` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:57 | `toyTRCfgFull` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:60 | `toyTRCfgLow` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:63 | `toyTRPi` | PASS | Exact data; concrete finite literal, no choice or fallback. |
| SO §8/§J; RatData:70 | `toyTRCert` | PASS | Whole concrete record assembled from the audited data, including expHalvings/expOrder. |
| SO §8/§J; Toy2:37 | `toyCert2` | PASS | Exact alias of toyT2Cert; signed TorusCertificate 2 ℚ. |
| SO §8/§J; Toy2:40 | `toyCert2d` | PASS | Exact alias of toyT2dCert; signed type; no whole-checker claim. |
| SO §8/§J; Toy2:42 | `toyCert2_passes` | PASS | Exact signed type; decide +kernel on all eight checks. |
| SO §8/§J; Toy2:48 | `toyCert2d_static` | PASS | Exactly static = true for the named check; decide +kernel, no extra premises. |
| SO §8/§J; Toy2:50 | `toyCert2d_hamBounds` | PASS | Exactly hamBounds = true for the named check; decide +kernel, no extra premises. |
| SO §8/§J; Toy2:52 | `toyCert2d_embedding` | PASS | Exactly embedding = true for the named check; decide +kernel, no extra premises. |
| SO §8/§J; Toy2:54 | `toyCert2d_gram` | PASS | Exactly gram = true for the named check; decide +kernel, no extra premises. |
| SO §8/§J; Toy2:56 | `toyCert2d_smallness` | PASS | Exactly smallness = true for the named check; decide +kernel, no extra premises. |
| SO §8/§J; Toy2:59 | `toyLunarFreq_eq_algFreq` | PASS | Polynomial identity under the explicit coefficient-list equality; not an assumed enclosure. |
| SO §8/§J; Toy2:68 | `toyCert2_freq` | PASS | Certified sqrt(5), alg box, and landed lunarNuMinus identity. |
| SO §8/§J; Toy2:76 | `toyCert2d_freq` | PASS | Certified sqrt(5), alg box, and landed lunarNuMinus identity; no T2d acceptance inferred. |
| SO §8/§J; Toy2:84 | `toyCert2_torus` | PASS | Exact signed type; unconditional black-box application. |
| SO §8/§J; Toy3:27 | `toyHam3` | PASS | Literal signed Hamiltonian syntax, identical to §J. |
| SO §8/§J; Toy3:32 | `toyCert3` | PASS | Exact alias of toyT3Cert; signed TorusCertificate 3 ℚ. |
| SO §8/§J; Toy3:34 | `toyCert3_ham` | PASS | Exact signed identity; rfl. |
| SO §8/§J; Toy3:36 | `toyCert3_err_pos` | PASS | Exact signed strict positivity; decide +kernel. |
| SO §8/§J; Toy3:38 | `toyCert3_passes` | PASS | Exact signed type; decide +kernel on all eight checks. |
| SO §8/§J; Toy3:40 | `toyCert3_freq` | PASS | Exact signed box enclosure of cubicFreq; certified cube root and alg box. |
| SO §8/§J; Toy3:53 | `toyCert3_torus` | PASS | Exact signed type; unconditional black-box application. |
| SO §8/§J; Rat:23 | `toyRatCert` | PASS | Exact alias of toyTRCert; signed TorusCertificate 2 ℚ. |
| SO §8/§J; Rat:25 | `toyRatCert_passes` | PASS | Exact signed checker-only statement; decide +kernel. |
| SO §J | `toyCert2d_passes` | ABSENT, accepted limit | Full T2d check not proved. |
| SO §J | `toyCert2d_torus` | ABSENT, accepted limit | No acceptance-to-torus application for T2d. |

## Definitions and data fidelity

The eight modules contain no new `abbrev` or `structure`. The five ToyLit helpers
are transparent, computable definitions in an exposed section. `toyNat` is a radix
fold on its whole list carrier (an empty list gives zero); decimal concatenation
is the interpretation for canonical emitted chunks. `toyQ` inherits `mkRat`'s
total convention at denominator zero, but every denominator emitted here is
strictly positive. `toyScaledPoly` preserves key order and divides both integer
components by the same denominator. No theorem depends on junk data, a guessed
witness, or a choose/default fallback in these helpers.

All four certificates are concrete finite records. Their data fields are literal
rational numbers, lists, polynomial syntax, witnesses, bounds and configurations.
The `fun _ _ => none` mantissa callback is deliberate direct-route configuration;
it is not a missing proof. Books contain `.direct` advice only. T2/T3/TR have empty
books; T2d has 34 keys in each book, `[2,0]` and 33 `[0,slot]` entries. Its full cutoff
is 1,000,000 and low cutoff is 30. These were not altered by the package or auditor.

Executed `python3 .lake/abi-scratch/data_audit.py` (exit 0). The scratch checker:

1. Imported the emitter without writing bytecode and regenerated every declaration
   from each JSON. All generated declaration bodies match the checked-in Lean,
   modulo whitespace; every whole-certificate field and both exponential controls
   were separately matched. Counts excluding the final whole-record definition:
   T2 17, T2d 31, T3 17, TR 14.
2. Independently decoded all decimal chunks with the radix recurrence and parsed
   rational division without calling the emitter's rational functions. Every
   parameter, both π enclosure rationals, and every root endpoint matches JSON.
3. Independently decoded the 14 T2d witness chunks, checked every ordered key and
   both rational components against JSON using the common denominator, and got
   `[40,40,40,40,40,40,40,40,40,40,40,40,40,11]`, total 531. Concatenation preserves
   exactly the original order and coefficients.

Representative independent literal checks include T2's
`err = 1/3118000000000000000000000000000000000000000`, `γ = 1/42`, `τ = 1`;
T3's 63-digit numerator in `err`, reconstructed from its positive integer and
multi-chunk denominator, `γ = 1/12`, `τ = 2`; TR's `err = disp = 0` and exact
`(1/4,1/2)` reference box; and both T2d root endpoints and its common-denominator
reciprocal coefficients. Final independent decoder output:

```text
T2: independent rational decode PASS for every parameter, pi centre/radius and root endpoints
T2d: independent rational decode PASS for every parameter, pi centre/radius and root endpoints
T3: independent rational decode PASS for every parameter, pi centre/radius and root endpoints
TR: independent rational decode PASS for every parameter, pi centre/radius and root endpoints
```

Emitter review (`scripts/spin_orbit/toy_lean_cert.py:30–43,101–124,167–210`):
`Fraction` parses rational strings exactly; the polynomial denominator is an lcm,
so conversion by `int(a)`/`int(b)` acts on integers and discards no fractional
part. Decimal chunking changes presentation only. No floating-point arithmetic
or rounding is introduced. Hamiltonian syntax is copied from each JSON's `ham.lean`
and matches the intended T2/T2d/T3/TR Hamiltonian. Verification metadata is not
trusted or read into the certificates. The emitter itself is untrusted tooling;
the Lean proofs check the resulting exact data independently.

## Signed statements and black-box chain

The scratch probe imports Toy2, Toy3 and Rat and reconstructs the signed types
for `toyHam3`, the four certificate definitions, and all eight proved §J theorems.
For each reconstructed type it elaborates the declaration application, plus
`example : type_of% @signed_export := @KAM.Certificate.export` and the reverse.
That is 26 type-equality directions for 13 exports, with no extra binders. The
fresh zero-binder copies apply `KAM.Certificate.export` directly; there is no
frozen seal to install. `toyCert3_ham` also identifies the actual data Hamiltonian
with the signed expression by `rfl`.

`Toy2.lean:68–92` proves the enclosure from `checkRootEnclosure 2 5`,
`sqrt_mem_of_checkRootEnclosure`, `checkAlgBox`, `algFreq_encloses` and the exact
`lunarNuMinus_eq` identity. It instantiates soundness at γ=1/42, τ=1 and discharges
the last premise with `lunarNuMinus_half_isDiophantine`. The T2d enclosure has the
same construction on T2d's distinct rational root bounds.

`Toy3.lean:40–60` uses `checkRootEnclosure 3 2`,
`rpow_mem_of_checkRootEnclosure`, `cubicFreq_eq_algFreq`, and `checkAlgBox` to
establish the signed enclosure. It instantiates soundness at γ=1/12, τ=2 and
supplies `cubicFreq_isDiophantine`. Neither torus theorem has any hypotheses.

`Soundness.lean:56–74` applies `KAM.Iso.Apost.g1_explicit`, after assembling all
G1 hypotheses from the checks. `CertifiedTorus` (Defs.lean:356–370) is an actual
existence conclusion: holomorphic, primary and real K∞, invariance at s∞ω*, exact
energy, domain and derivative margins, displacement and frequency bounds. It is
not a Boolean success synonym. The frozen I-G1 and its extended torsion/average,
energy, invariance and Diophantine definitions were checked for this attachment.
The implementation theorem's axioms are clean; no frozen statement is modified.

Fresh recursive import walk: **157 KAM modules, 19 frozen modules, all SEALED;
zero provider edges and zero DRAFT_SORRY imports**. The frozen theorem file was
read for comparison; the toy chain uses the proved explicit implementation.

The `[5,a,l]` claim is confirmed structurally: Defs.lean:190–194 passes `freqModel`
as a factor; Torsion/Models.lean:89–90 makes that a constant polynomial ball;
Model/Ops.lean:83–94 takes the constant-factor route before advice lookup. Thus
an empty book in T2/T3 is consistent with successful kernel checking. No key was
silently added to T2d. This does not establish T2d's unfinished invariance check.

## Independent validation receipts

All Lean/Lake commands were serial and used `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override was used; no failed heavy T2d check was rerun. Scratch files
were confined to `.lake/abi-scratch/` and removed after recording these receipts.

### Targeted compile gate

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sotesta KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Rat
```

Exit 0. Output began with gate acquisition and ended:

```text
[inp-gate] slot 1 acquired 22:51:45 for KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Rat
Build completed successfully (3312 jobs).
```

Replayed dependency warnings: unused simp argument `Nat.succ_eq_add_one` in
Arith/PiHigh:218; unused `hS` in Expr/Basic:85; unused section instances in
Sound/Static:99,152 and Sound/Ham:68. No warning in the eight toy modules.
The build reused existing artifacts, so this is not a fresh timing measurement
of each `decide +kernel` proof. Kernel replay below independently checks them.

### Signature and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOTestAudit.lean
```

Exit 0. Type probes all elaborated. Scratch-only `defProp` warnings arose because
the first probe used `def` for the copied propositions; no production declaration
is implicated. The complete axiom output for all 17 new public theorems and the
two black-box implementation results is:

```text
'KAM.Certificate.toyCert3_ham' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_err_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyNat_test' depends on axioms: [propext]
'KAM.Certificate.toyCert2_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_static' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_hamBounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_embedding' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_gram' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_smallness' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyLunarFreq_eq_algFreq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toyRatCert_passes' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Apost.g1_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Inherited full-diff axiom command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/InheritedAudit.lean
```

Exit 0; imports Toy2 and SpinOrbit.Tests.GraphCert, then prints all 40 inherited
public theorem axioms. Complete output:

```text
'KAM.Certificate.sum_finRange_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.angleImOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEmbedding_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEnergy_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEnergy_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkGram_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumRangeQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_phaseNat_eq_sumRangeQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_sum_phaseNat_eq_sumRangeQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_le_ballMagQ_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.norm_val_le_slotMagQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.ham_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumVec_hamiltonianVectorFieldℂ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumVec_fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dkFreqModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkInvariance_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkInvariance_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkSmallness_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.freqNormLo_le_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.freqNormLo_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.emb_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_fst_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_snd_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.realPt_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_deriv_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.checkSoGraph_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_exactTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_pass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_mono_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_range_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.graphTest_margin_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Rat KAM.Certificate.Tests.ToyLit KAM.Certificate.Tests.Toy2Data KAM.Certificate.Tests.Toy2dData KAM.Certificate.Tests.Toy3Data KAM.Certificate.Tests.RatData
```

Exit **0**, one invocation for all eight package modules. Complete output:

```text
replaying KAM.Certificate.Tests.RatData
replaying KAM.Certificate.Tests.Toy3Data
replaying KAM.Certificate.Tests.Toy2dData
replaying KAM.Certificate.Tests.Toy2Data
replaying KAM.Certificate.Tests.ToyLit
replaying KAM.Certificate.Tests.Rat
replaying KAM.Certificate.Tests.Toy3
replaying KAM.Certificate.Tests.Toy2
```

This rechecks the compiled proofs, including `decide +kernel` results. It does
not evaluate any absent T2d theorem. Prior handoff sub-check times and peak memory
figures are prover observations, not independently reproduced measurements here.

### Lint, naming, protected paths and size

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1389 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All forbidden-token, proof-escape, carrier, resource-limit, module, line-length,
frozen-anchor and ABI checks otherwise pass. The generated root was left untouched.

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sotesta KAM.Certificate.Tests.ToyLit KAM.Certificate.Tests.Toy2Data KAM.Certificate.Tests.Toy2dData KAM.Certificate.Tests.Toy3Data KAM.Certificate.Tests.RatData KAM.Certificate.Tests.Toy2 KAM.Certificate.Tests.Toy3 KAM.Certificate.Tests.Rat
```

Exit 0: `short-name check OK (no reused public short name)`.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit 0, with no diff or whitespace error. Both emit only Git's multiple-merge-base
warning already recorded above. No protected path has a patch in the required
three-dot comparison. The moving `inp` tip's later changes are not edits by this package.

All eight toy files have the copyright/author header, `module`, public imports,
module docstring and public section. Definitions intended to unfold are exposed.
No file exceeds 1500 physical lines and no line exceeds 100 Unicode characters:

| File under KAM/Certificate/Tests | Lines | Maximum columns |
|---|---:|---:|
| ToyLit.lean | 42 | 97 |
| Toy2Data.lean | 113 | 99 |
| Toy2dData.lean | 1147 | 99 |
| Toy3Data.lean | 158 | 99 |
| RatData.lean | 88 | 97 |
| Toy2.lean | 93 | 99 |
| Toy3.lean | 62 | 95 |
| Rat.lean | 27 | 96 |

## Inherited declarations visible in the full comparison

These are not attributed to SO-TEST-A. The source inspection confirms the stated
composition route and no new assumption in the toy clients; the table records
that limited review plus the fresh axiom checks above, not a replacement of the
prior analytic audits. Namespace is KAM.Certificate for Sound/* and Soundness,
and KAM.SpinOrbit for Graph/Cert and Tests/GraphCert.

| Node / file | Declaration | Verdict within this audit | Reason / definition classification |
|---|---|---|---|
| inherited KAM/Certificate/Sound/Embedding.lean:37 | `sum_finRange_map_eq` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Embedding.lean:44 | `angleImOk_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Embedding.lean:96 | `checkEmbedding_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Energy.lean:31 | `checkEnergy_sound_of` | CHECKED (inherited) | Distinct conditional helper; Hamiltonian/embedding conclusions are discharged by the public sound wrapper. |
| inherited KAM/Certificate/Sound/Energy.lean:104 | `checkEnergy_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Gram.lean:27 | `checkGram_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:30 | `sumRangeQ_eq` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:38 | `sum_phaseNat_eq_sumRangeQ` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:45 | `sum_sum_phaseNat_eq_sumRangeQ` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:52 | `norm_le_ballMagQ_of_mem` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:60 | `Slp.norm_val_le_slotMagQ` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:68 | `TorusCertificate.ham_structural` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Ham.lean:81 | `checkHamBounds_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Invariance.lean:30 | `sumVec_hamiltonianVectorFieldℂ` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Invariance.lean:38 | `sumVec_fderiv_apply` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Invariance.lean:47 | `dkFreqModel_encloses` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Invariance.lean:74 | `checkInvariance_sound_of` | CHECKED (inherited) | Distinct conditional helper; Hamiltonian/embedding conclusions are discharged by the public sound wrapper. |
| inherited KAM/Certificate/Sound/Invariance.lean:142 | `checkInvariance_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Smallness.lean:26 | `checkSmallness_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Static.lean:28 | `StaticFacts` | CHECKED (inherited) | Proposition record of static consequences; checkStatic_sound constructs it from success. |
| inherited KAM/Certificate/Sound/Static.lean:52 | `freqNormLo_le_of_forall` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Static.lean:66 | `freqNormLo_le_norm` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Static.lean:99 | `checkStatic_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Static.lean:130 | `checkStatic_freq` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Static.lean:152 | `TorusCertificate.emb_structural` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Sound/Torsion.lean:32 | `checkTorsion_sound_of` | CHECKED (inherited) | Distinct conditional helper; Hamiltonian/embedding conclusions are discharged by the public sound wrapper. |
| inherited KAM/Certificate/Sound/Torsion.lean:68 | `checkTorsion_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/Certificate/Soundness.lean:33 | `checkTorusCertificate_hyps` | CHECKED (inherited) | Assembles all checks; explicit G1 application; no undischarged bundle in the toy results. |
| inherited KAM/Certificate/Soundness.lean:62 | `checkTorusCertificate_sound` | CHECKED (inherited) | Assembles all checks; explicit G1 application; no undischarged bundle in the toy results. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:40 | `SoGraphCert` | CHECKED (inherited) | Concrete graph advice plus base certificate; contains no proof assumption. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:55 | `soGraphMonoModel` | CHECKED (inherited) | Intended model/check composition; defaults are inherited enclosure conventions, success is required by the soundness theorem. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:60 | `soGraphActionModel` | CHECKED (inherited) | Intended model/check composition; defaults are inherited enclosure conventions, success is required by the soundness theorem. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:66 | `checkSoGraph` | CHECKED (inherited) | Intended model/check composition; defaults are inherited enclosure conventions, success is required by the soundness theorem. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:77 | `norm_fst_apply_sub_le` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:81 | `norm_snd_apply_sub_le` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:85 | `realPt_one_zero` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:90 | `soGraph_deriv_transfer` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:133 | `checkSoGraph_sound` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:162 | `soGraph_exactTorus` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:215 | `soBarrier_of_cert` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Graph/Cert.lean:235 | `soRotBarrier_of_cert` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:28 | `graphToyW` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:30 | `graphToyPi` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:32 | `graphToyCfg` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:35 | `graphToyCos` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:37 | `graphToyK` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:40 | `graphToyParams` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:44 | `graphToyBase` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:62 | `graphToy` | CHECKED (inherited) | Explicit graph-only test data; whole-certificate placeholder fields are not used to claim torus acceptance. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:74 | `graphTest_pass` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:78 | `graphTest_mono_fail` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:82 | `graphTest_range_fail` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |
| inherited KAM/SpinOrbit/Tests/GraphCert.lean:88 | `graphTest_margin_fail` | CHECKED (inherited) | Inspected inherited proof/contract; fresh axioms standard three; broader source fidelity belongs to the inherited package audit. |

## Findings, uncertainties, errata and deviations

1. **Accepted incomplete T2d deliverable.** `Toy2.lean:44–46` expressly leaves
   invariance, energy and torsion unfinished. Only static, Hamiltonian bounds,
   embedding, Gram and smallness have exported kernel proofs. There is no
   `toyCert2d_passes` or `toyCert2d_torus` declaration, and this audit does not
   infer either from Python acceptance or the five partial results. The focus
   expressly accepts this resource design signal. Handoff energy success in an
   uncapped probe is not an exported theorem and was not reproduced here.
2. **No rotated-frame test.** The four available toy JSONs are T2, T2d, T3 and TR.
   The conditional rotated-client exercise remains untested, as reported.
3. **Generated root.** The allowed stale-KAM.lean exception is kept separate from
   mathematical and kernel validation. It must be regenerated by the orchestrator
   during integration; the auditor did not edit it.
4. **Design cost wording needs qualification.** SO-LEAN-DESIGN.md:725–726 says
   “rationals of any size are cheap.” Taken as an operational claim for these
   kernel-evaluated list convolutions, this is unsupported: the reported T2d
   failure and the 531-term, large-denominator witness show why bit size and
   product count matter. This is a design/performance caveat, not a false Lean
   statement or a suspected defect in a pinned mathematical source. The claimed
   detailed time/RSS attribution remains handoff evidence.
5. The design's T2d result (SO-LEAN-DESIGN.md:720–721; SOSignatures.lean §J) remains
   an outstanding validation target. The round-specific exception does not close
   it or revise its signed type. Likewise these simple direct-route toys do not
   settle packed products, demanding nonzero-degree Machin-gap cases, a lunar
   candidate certificate, or the final 3.3% confinement claim.

No conclusion-shaped hypothesis is added to any completed §J theorem; no
mathematical source or frozen-statement defect was found in this scope. No
mathematical deviation or source change was introduced by this audit. The only
persistent auditor file is this exact report; all auditor-created scratch
probes, helper scripts and logs were removed after their receipts were recorded.
