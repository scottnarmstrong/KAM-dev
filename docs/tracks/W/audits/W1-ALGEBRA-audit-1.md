# W1-ALGEBRA independent audit 1

**Verdict: PASS WITH NOTES — off-frontier infrastructure only.** No provider, frozen theorem seal, W1 selection/trilinear theorem, W3 majorant theorem, or W-NLW2 closure is certified. Audit item 1 is N/A under the handoff's AUDIT FOCUS. All four modules build, kernel replay passes, and all 74 new public theorems have permitted axiom closure. The notes concern representation/consumer packaging and a blueprint wording ambiguity, not a detected false Lean theorem.

## Scope, authority and frozen inputs

Auditor: Codex; date: 2026-10-30 UTC. Focused tier-2 source-correspondence/refutation audit. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md (including D30, D41 and D43), `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/W/audits/W1-ALGEBRA-handoff.md`. Applied lean-statement-audit's semantic/binder checks and manuscript-audit's frozen-input, refutation and evidence discipline; no frozen statement is being promoted.

Permission envelope: report-only repository edits; temporary probes in `.lake/abi-scratch/`; no git mutation, source repair, root regeneration or external communication. The user's exact worktree report path overrides the generic brief's main-worktree destination. The handoff requires the SLIM lint wrapper and authorizes the existing regenerated root delta. All audit Lean/Lake invocations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5` (the compile gate/wrapper supplies nice for build/lint). Other campaigns' processes are outside this audit's control.

Frozen-v1: HEAD `f2c8a5d2f030cc04a80c7088d06c2b3b5a68691f`; comparison ref `inp` = `61492b48a7ea44aa721043ee40897f3625c10095`. Initial working tree clean. Reviewed the full `git diff inp...HEAD`: four new Lean modules, the handoff, and exactly four public imports added to `KAM/Root/Wave.lean`. No other changes. The source locators below refer to this HEAD and the following hashes.

| File | SHA-256 |
|---|---|
| `KAM/Wave/Algebra/Algebra.lean` | `8477cbb9b5cbb2be856d2700b452577031fb20c6ed85e9e0308b0b2bb596adbf` |
| `KAM/Wave/Algebra/Extension.lean` | `c4aaee74111ac8635e28b65f7605aeb176a3c5d8b484b6d40418d8234e9a21fc` |
| `KAM/Wave/Algebra/TwoSided.lean` | `3faa29fc1a0d9ddafb503c6408346108590bb600b42d7e205769cdf2c46e606f` |
| `KAM/Wave/Algebra/Young.lean` | `bba85a385fca9fe1edc5ebd75160782f78e6a1d37f0affbbf37fb956ac2f5c44` |
| `blueprint-W/parts/w0-conventions.tex` | `1c8be225befe013fb4b18db8ea62dd8c154f2c3d8e231739569209902645310c` |
| `blueprint-W/parts/w0-normalization.tex` | `83f7f2ebcbf97613e30433401435e374f2731749fd9ef8b44ba2ac9b7697505b` |
| `blueprint-W/parts/w1-sequences.tex` | `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` |
| `blueprint-W/parts/w3-birkhoff.tex` | `d7150c6133cfe2c26eb7c66255fefbddce4d2ffc5c35992aa237e19a8a7af1bf` |
| `KAM/Frozen/Wave/Defs/EllWeight.lean` | `88c0329883e40f8c1c852233a39eaa92482bf4b3a99041e5595e9b277d7e8722` |
| `KAM/Frozen/Wave/Defs/Lam.lean` | `097b70740bbedd0463d2e0ffb98e99bf508f81207b8370ac05ddc91aa3e05f81` |

The two imported frozen definitions have manifest IDs `wave.ellWeight.v1` and `wave.lam.v1`, both SEALED. No frozen theorem/provider is imported. The canonical local track statement is `docs/tracks/W/W-STATEMENTS.md` (there is no `docs/tracks/W/statement.md`); its stale draft banner is superseded by D41 and the manifest, without any auditor edit.

## Statement and proof assessment

Source reconstruction: `w0-conventions.tex:66–75` fixes ⟨l⟩ = max(1, |l|), including the weight 1 at zero; convolution has absolute convergence for a,s ≥ 0. `w1-sequences.tex:297–339` fixes the weighted lp transport, E±, restriction and independent-variable pairing J. Lines 341–383 fix Young (i)–(iii), ζ(2s), and the algebra constant. `w0-normalization.tex:95–113` independently gives the weight split and K_s. The formal squared weight `(⟨l⟩^s exp(a|l|) |c_l|)^2` agrees exactly with the printed norm.

Main binders have no EXCESS inputs: a,s,p and sequence/index variables are TYPING; membership/summability and nonnegativity conditions are SOURCE conditions of the corresponding sequence estimate; m>0 is STANDING (`bpW:w0:mass`); the generalized phase condition ‖σ‖=1 is SOURCE for the explicitly generalized Eσ estimate and is discharged at σ=±1. No RULED logical premise is needed. In particular, no convolution estimate, output membership, continuity, convergence or algebra conclusion is assumed in `wave_algebra`, `wave_algebra_three`, `wave_ext_mem`, `wave_restr_mem`, or `wave_J_norm_sq`. Generic summation helpers take the summability conditions of their stated helper domains, not missing conclusions of the main theorem. All project predicates expand to literal Summable conditions, with no hidden result fields.

The proof spine follows Cauchy–Schwarz, Young, the polynomial/exponential weight split and ℓ² triangle. Weighted ℓ¹ control proves convergence before the algebra compares tsums; membership of the output is proved by a summable square majorant. K_s depends only on s, and K_s² in the three-factor theorem has no mass, a, or input dependence. The theorem handles s=1 and a=0. The generalizations to all real a for weighted ℓ¹/extension/restriction/pairing and to any unit complex phase are mathematically stronger and sound. No claim is made for the expressly unplanned 1/2<s<1 extension (`w1-sequences.tex:385–389`).

### Per-declaration ledger

All names below are in `KAM.Wave`. Source labels are under `bpW:` unless prefixed `stepW:`. Each row is one declaration; generic local helpers are mapped to the source proof step they support. P = PASS; PN = PASS WITH NOTES (see notes below). There are 88 rows: 14 definitions and 74 theorems.

| Node / source | Declaration (file:line) | Verdict | Assessment |
|---|---|---|---|
| `w1:algebra / w0n:algebra` | `wave_add_rpow_le` (Algebra:29) | P | Valid weight/ℓ² helper; hypotheses are its source domain. |
| `w1:algebra / w0n:algebra` | `waveJap_sub_le` (Algebra:36) | P | Valid weight/ℓ² helper; hypotheses are its source domain. |
| `w1:algebra / w0n:algebra` | `wave_weight_ineq` (Algebra:48) | P | Valid weight/ℓ² helper; hypotheses are its source domain. |
| `w1:algebra / w0n:algebra` | `wave_sqrt_tsum_smul` (Algebra:72) | P | Valid weight/ℓ² helper; hypotheses are its source domain. |
| `w1:algebra / w0n:algebra` | `wave_algebra` (Algebra:82) | P | Exact K_s bound with output membership and absolute convergence. |
| `w1:algebra / w0n:algebra` | `wave_algebra_three` (Algebra:192) | P | Iterated estimate with K_s² and left association. |
| `w0:ellap / w1:twosided` | `WaveOneMem` (Extension:32) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w0:ellap / w1:twosided` | `waveOneNorm` (Extension:36) | PN | Literal one-sided square-sum formula; N1. |
| `w0:ellap / w1:twosided` | `waveOneNorm_nonneg` (Extension:39) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wavePosOf` (Extension:42) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wavePosOf_pos` (Extension:44) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wavePosOf_neg` (Extension:47) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_hasSum_fold2` (Extension:51) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_hasSum_fold` (Extension:74) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (iii)` | `waveJap_pnat` (Extension:80) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (i) / proof helpers` | `waveTwoWeight_pnat` (Extension:86) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveTwoWeight_neg_pnat` (Extension:92) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_ellWeight_sq_succ` (Extension:99) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_le_lam` (Extension:109) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_lam_pos` (Extension:114) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt` (Extension:119) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_zero` (Extension:123) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_pos` (Extension:126) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_neg` (Extension:132) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_add` (Extension:138) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_smul` (Extension:145) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_norm_pos` (Extension:152) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveExt_norm_neg` (Extension:157) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_ext_mem` (Extension:164) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveEvenMaj` (Extension:196) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveEvenMaj_zero` (Extension:199) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveEvenMaj_norm_pos` (Extension:201) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `waveEvenMaj_norm_neg` (Extension:207) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (i) / proof helpers` | `wave_evenMaj_norm_sq` (Extension:215) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (ii)` | `waveRestr` (Extension:237) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (ii)` | `wavePnatCast_injective` (Extension:244) | P | Literal sequence formula or valid folding/weight/extension helper. |
| `w1:twosided (ii)` | `wave_restr_mem` (Extension:247) | P | Restriction gains 1/2; partial-sum and evenness bounds exact. |
| `w1:twosided (iii)` | `waveJ` (Extension:300) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `waveJ_zero` (Extension:303) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `waveJ_pos` (Extension:305) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `waveJ_neg` (Extension:310) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `waveJ_add` (Extension:315) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `waveJ_smul` (Extension:322) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `wave_J_norm_sq` (Extension:330) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `wave_J_norm_le` (Extension:349) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w1:twosided (iii)` | `wave_J_surj` (Extension:362) | P | Independent-variable pairing: literal coordinates, linearity, norm or surjectivity. |
| `w0:twosided / w1:twosided-transport` | `waveJap` (TwoSided:36) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveJap_pos` (TwoSided:38) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `one_le_waveJap` (TwoSided:40) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveJap_neg` (TwoSided:42) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveJap_nat_succ` (TwoSided:44) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveJap_neg_nat_succ` (TwoSided:50) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveJap_zero` (TwoSided:53) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w1:young (ii)` | `wave_jap_hasSum` (TwoSided:56) | P | Exact ζ sum / ℓ¹ estimate; weighted version valid for all real a. |
| `w0:twosided / w1:twosided-transport` | `waveTwoWeight` (TwoSided:82) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoWeight_pos` (TwoSided:85) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `one_le_waveTwoWeight` (TwoSided:88) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `WaveTwoMem` (TwoSided:94) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoNorm` (TwoSided:98) | PN | Literal weighted square-sum formula; N1. |
| `w0:twosided / w1:twosided-transport` | `waveTwoNorm_nonneg` (TwoSided:101) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoNorm_sq` (TwoSided:103) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoMemlp` (TwoSided:107) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoToLp` (TwoSided:115) | PN | Weighted lp element with membership proof; N2. |
| `w0:twosided / w1:twosided-transport` | `waveTwoToLp_norm` (TwoSided:119) | PN | Exact norm preservation; inverse membership and probe establish transport; N2. |
| `w0:twosided / w1:twosided-transport` | `waveTwoMem_of_lp` (TwoSided:127) | PN | Division by strictly positive weight; inverse membership, N2. |
| `w1:young (ii)` | `wave_jap_hasSum_zeta` (TwoSided:138) | P | Exact ζ sum / ℓ¹ estimate; weighted version valid for all real a. |
| `w0:twosided / w1:twosided-transport` | `waveAlgConst` (TwoSided:154) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveAlgConst_nonneg` (TwoSided:157) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoWeight_zero_left` (TwoSided:160) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoWeight_mono` (TwoSided:163) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `WaveTwoMem.of_weight_le` (TwoSided:169) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w0:twosided / w1:twosided-transport` | `waveTwoNorm_mono` (TwoSided:176) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w1:young (ii)` | `wave_expl1_le` (TwoSided:187) | P | Exact ζ sum / ℓ¹ estimate; weighted version valid for all real a. |
| `w1:young (ii)` | `wave_l1_le_of_mem` (TwoSided:231) | P | Exact ζ sum / ℓ¹ estimate; weighted version valid for all real a. |
| `w0:twosided / w1:twosided-transport` | `WaveTwoMem.summable_sq` (TwoSided:243) | PN | Proves square summability; docstring also mentions the norm comparison (N4). |
| `w0:twosided / w1:twosided-transport` | `wave_conv_summable` (TwoSided:251) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w1:young (iii)` | `wave_conv_assoc_of_mem` (TwoSided:261) | P | Literal weight, transport, membership or valid comparison/convergence helper. |
| `w1:young (i)` | `wave_tsum_mul_sq_le` (Young:31) | P | Valid summation, rearrangement or ℓ² proof helper; no conclusion assumed. |
| `w1:twosided-transport` | `waveConv` (Young:51) | PN | Literal guarded tsum helper; domain caveat N1. |
| `w1:young (i)` | `wave_young_real` (Young:56) | P | Exact Young/convergence bound (real helper is nonnegative). |
| `w1:young (i)` | `wave_young` (Young:111) | P | Exact Young/convergence bound (real helper is nonnegative). |
| `w1:young (i)` | `wave_young_sqrt_le` (Young:129) | P | Exact Young/convergence bound (real helper is nonnegative). |
| `w1:young (iii) / proof helpers` | `wave_l2_add` (Young:139) | P | Valid summation, rearrangement or ℓ² proof helper; no conclusion assumed. |
| `w1:young (iii) / proof helpers` | `waveConv_comm` (Young:169) | P | Valid summation, rearrangement or ℓ² proof helper; no conclusion assumed. |
| `w1:young (iii) / proof helpers` | `waveConv_summable_comm` (Young:177) | P | Valid summation, rearrangement or ℓ² proof helper; no conclusion assumed. |
| `w1:young (iii) / proof helpers` | `waveConv_mono` (Young:184) | PN | Exact termwise inequality under both summability conditions; N3. |
| `w1:young (iii) / proof helpers` | `norm_waveConv_le` (Young:191) | P | Valid summation, rearrangement or ℓ² proof helper; no conclusion assumed. |
| `w1:young (iii) / proof helpers` | `waveConv_assoc_l1` (Young:199) | P | Valid summation, rearrangement or ℓ² proof helper; no conclusion assumed. |

## Definition classification and whole-carrier review

All 14 definitions are literal formulas or a proof-bearing transport, not characterization-defined choices. There are no new abbrevs, structures, instances or arbitrary selected witnesses.

| Definitions | Body/carrier assessment |
|---|---|
| `waveJap`, `waveTwoWeight`, `waveAlgConst` | Exact max/rpow/exp and K_s formulas. The ζ constant has its source algebra interpretation only for s≥1 (ζ series identity for s>1/2); no estimate uses off-domain analytic continuation. |
| `WaveTwoMem`, `WaveOneMem` | Literal weighted square-summability predicates; genuine space membership, no theorem-shaped obligation bundle. Extending parameters to real a is sound. |
| `waveTwoNorm`, `waveOneNorm` | Literal square-root-of-tsum helpers, mathematically norms on the corresponding membership locus; see N1. |
| `waveTwoToLp` | Actual weighted coefficients, with proved `Memℓp`; no fallback, no choice. Strict positivity makes inverse division valid for every a,s,l. |
| `waveConv` | Literal convolution tsum on an ambient function type; its mathematical convolution domain is supplied by convergence proofs, as explicitly prescribed by the blueprint. N1 records the totalization boundary. |
| `wavePosOf` | natAbs as a positive integer with input proof l≠0; no zero masquerading as a positive index. |
| `waveExt`, `waveEvenMaj` | Zero at l=0 is the source's specified value, not a fallback. Positive and negative branches implement exactly the two halves. Denominators √λ_j and √j are strictly positive. Arbitrary σ is an honest phase-parameterized formula; the norm estimate requires ‖σ‖=1. |
| `waveRestr` | Positive half divided by √λ_j; m>0 built into the carrier. |
| `waveJ` | Literal zero/positive/negative halves; second input is independent, not complex conjugation. |

BODY_MATCH: OK for all 14. PUBLIC_CARRIER: OK as the explicitly guarded formula-helper API; these are not exported as normed structures on all functions. WELL_DEFINEDNESS: N/A_LITERAL except `waveTwoToLp`, whose lp membership is proved. CHARACTERIZATION: N/A_LITERAL. CHOICE_INDEPENDENCE: N/A (no selected witness). DEFINITION_VERDICT: PASS WITH NOTES (N1/N2).

### N1 — Total tsum helpers are guarded, not global norms/convolutions

`TwoSided.lean:97` explicitly says the norm is “meaningful when `WaveTwoMem a s c`”; `Young.lean:48–50` says convolution is “a `tsum`, guarded by the summability proved before each use.” This matches `w1-sequences.tex:301–303`, “a tsum guarded by the summability proved before each use.” On arbitrary nonmembers the raw norm may be zero because of Mathlib's tsum totalization; similarly a divergent convolution has no analytic convolution meaning. No production theorem here exploits such a value to claim a norm or convolution estimate. Unconditional commutativity is a reindexing identity of the total formula (valid even off-domain); nonnegativity and the square identity are likewise formal formula facts. Associativity requires ℓ¹, monotonicity requires both sums, and absolute-value comparison requires norm summability. The numerical estimates/membership theorems require input membership and prove convergence. Thus the attempted junk-value refutation does not refute the stated package. Future consumers must preserve these guards.

### N2 — Function API is adequate infrastructure; bundling is not yet supplied

E± has add/smul laws and the exact √2 bound; J has add/smul, norm-square, max-norm bound and surjectivity. An independent probe derives J injectivity from its positive and negative coordinate formulas. The weighted lp transport has exact norm preservation, inverse membership, and a probe verifies its inverse round trip by positivity. A second probe verifies that taking the pointwise complex norm preserves membership and norm, covering the extension majorant.

These facts suffice for the coordinate estimates in W1 selection and W3 majorants (`w1-sequences.tex:398–439`, `w3-birkhoff.tex:232–245`). The s=p+1/2≥1 algebra and the √2 half-lattice restriction factors are present. To finish W1 trilinear analyticity or W3 analytic coordinates, a consumer must still assemble continuous linear/multilinear maps in its actual lp carriers and prove its selection/real-structure identities. This package supplies no such finished consumer theorem. No production module outside these four files uses the new API in this snapshot (apart from the generated root imports). This is a packaging boundary, not a hidden conclusion premise or a closure claim.

### N3 — Blueprint monotonicity needs an explicit domain for X′

Frozen-v1 `w1-sequences.tex:348–350` says: “For nonnegative sequences X,Y,Z with X,Y,Z∈ℓ^{0,s}_b, s>1/2 ... monotone: 0≤X≤X′ pointwise implies X*Y≤X′*Y.” X′ is not explicitly required to belong to a summability domain. Literal unrestricted X′ can make the upper convolution diverge: at s=1, take X=δ₀, Y_i=exp(-|i|), Z=0 and X′_i=exp(|i|). X,Y,Z belong to the stated space and X≤X′, but at l=0 the upper summands are all 1. For the total tsum convention the purported upper value would be 0, while (X*Y)_0=1.

Adversarial re-reading resolves the intended mathematical domain: the proof at lines 366–370 explicitly says “all sequences involved are in ℓ¹∩ℓ²”, so X′ was evidently intended to be among them. Accordingly this is a source wording clarification, not a finding that the intended lemma is false or that Lean introduced an unpaid analytical premise. `waveConv_mono` correctly requires both summabilities; on weighted inputs including X′ these follow by the package's Cauchy–Schwarz convergence lemma. Proposed clarification only: include X′ in the source domain or state the upper sum's convergence. No source edited. No additional pinned-PDF defect was discovered or re-audited.

### N4 — Small documentation mismatch

`TwoSided.lean:241–245` describes `WaveTwoMem.summable_sq` as including “‖c‖_ℓ² ≤ ‖c‖_{a,s}”, but its conclusion exports only `Summable fun l => ‖c l‖^2`. Its proof has the pointwise domination needed for that inequality, so this is not a false mathematical claim; it is not a separately exported norm-comparison theorem. The convolution convergence required by the focus is exported by `wave_conv_summable`. Similarly `TwoSided.lean:21` mentions `waveTwoOfLp`, a name not defined in the file; the actual inverse-membership theorem is `waveTwoMem_of_lp` at line 127. Handoff file sizes are approximate/outdated; actual counts are recorded below. These are nonblocking documentation notes.

## Verification evidence

All commands ran from `/root/code/KAM-inp-wpf`. No source changes or resource overrides were made. Serial verification order: targeted build → kernel replay → theorem axiom/consumer probe → SLIM lint. No Lean/Lake verification phases overlapped.

1. Targeted build (exit 0):

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpf KAM.Wave.Algebra.Young KAM.Wave.Algebra.TwoSided KAM.Wave.Algebra.Extension KAM.Wave.Algebra.Algebra
```

```text
[inp-gate] slot 3 acquired 18:30:13 for KAM.Wave.Algebra.Young KAM.Wave.Algebra.TwoSided KAM.Wave.Algebra.Extension KAM.Wave.Algebra.Algebra
Build completed successfully (3255 jobs).
```

This is a targeted incremental build against the shared dependency snapshot, not a clean reconstruction of dependencies. No lake clean/update/cache-get was run.

2. Kernel replay (one invocation, exit 0):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Algebra.Young KAM.Wave.Algebra.TwoSided KAM.Wave.Algebra.Extension KAM.Wave.Algebra.Algebra
```

```text
replaying KAM.Wave.Algebra.Algebra
replaying KAM.Wave.Algebra.Extension
replaying KAM.Wave.Algebra.TwoSided
replaying KAM.Wave.Algebra.Young
```

3. Untracked probe `.lake/abi-scratch/W1Audit.lean` imported Algebra and Extension, then generated `#print axioms KAM.Wave.<name>` for every `^theorem` declaration in all four modules. Command (exit 0):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1Audit.lean
```

74 theorem reports: 73 exactly `[propext, Classical.choice, Quot.sound]`; `wavePnatCast_injective` exactly `[propext]`. No sorryAx or project axiom. Representative exact output:

```text
'KAM.Wave.wave_algebra' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_algebra_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_ext_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_restr_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_J_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wave_J_surj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.wavePnatCast_injective' depends on axioms: [propext]
```

The same probe elaborated six independent applications: exact algebra type with K_s expanded; associativity at arbitrary a≥0 via proved weakening to a=0; odd extension at σ=-1; injectivity of J; inverse round-trip of the lp transport; and norm/membership preservation of the pointwise absolute-value sequence. All passed. Only two unused-variable warnings for probe-local a,p occurred in the J injectivity example; production code was not changed and no linter option was set. Full probe text is recorded below for reproducibility; the scratch source is removed after the audit.

```lean
-- Independent exact applications and consumer compositions.
example {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {c d : ℤ → ℂ}
    (hc : WaveTwoMem a s c) (hd : WaveTwoMem a s d) :
    (∀ l, Summable fun i => ‖c i‖ * ‖d (l-i)‖) ∧
    WaveTwoMem a s (waveConv c d) ∧
    waveTwoNorm a s (waveConv c d) ≤
      (2 ^ s * Real.sqrt (1 + 2 * (riemannZeta ((2*s : ℝ) : ℂ)).re)) *
        waveTwoNorm a s c * waveTwoNorm a s d := wave_algebra ha hs hc hd
example {a s : ℝ} (ha : 0 ≤ a) (hs : 1 ≤ s) {c d e : ℤ → ℂ}
    (hc : WaveTwoMem a s c) (hd : WaveTwoMem a s d) (he : WaveTwoMem a s e) (l : ℤ) :
    waveConv (waveConv c d) e l = waveConv c (waveConv d e) l := by
  exact wave_conv_assoc_of_mem (by linarith) (hc.of_weight_le ha)
    (hd.of_weight_le ha) (he.of_weight_le ha) l
example (m : ℝ) (hm : 0 < m) {a p : ℝ} {q : ℕ+ → ℂ} (hq : WaveOneMem a p q) :
    WaveTwoMem a (p + 1/2) (waveExt m hm (-1) q) ∧
    waveTwoNorm a (p + 1/2) (waveExt m hm (-1) q) ≤ Real.sqrt 2 * waveOneNorm a p q :=
  wave_ext_mem m hm (by norm_num) hq
example {a p : ℝ} {z zb z' zb' : ℕ+ → ℂ}
    (h : waveJ z zb = waveJ z' zb') : z = z' ∧ zb = zb' := by
  constructor
  · funext j
    have hh := congrFun h ((j : ℕ) : ℤ)
    simpa only [waveJ_pos] using hh
  · funext j
    have hh := congrFun h (-((j : ℕ) : ℤ))
    simpa only [waveJ_neg] using hh
example {a s : ℝ} {c : ℤ → ℂ} (hc : WaveTwoMem a s c) :
    (fun l => waveTwoToLp hc l / (waveTwoWeight a s l : ℂ)) = c := by
  funext l
  change (waveTwoWeight a s l : ℂ) * c l / (waveTwoWeight a s l : ℂ) = c l
  have hw : (waveTwoWeight a s l : ℂ) ≠ 0 := by
    exact_mod_cast (waveTwoWeight_pos a s l).ne'
  field_simp
example {a s : ℝ} {c : ℤ → ℂ} (hc : WaveTwoMem a s c) :
    WaveTwoMem a s (fun l => (‖c l‖ : ℂ)) ∧
    waveTwoNorm a s (fun l => (‖c l‖ : ℂ)) = waveTwoNorm a s c := by
  have hn : ∀ l, ‖(‖c l‖ : ℂ)‖ = ‖c l‖ := fun l => by simp
  constructor
  · simpa only [WaveTwoMem, hn] using hc
  · simp only [waveTwoNorm, hn]

```

4. Required SLIM lint (exit 0):

```sh
env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpf
```

```text
check_lean_modules: PASS (1644 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

The wrapper ran `nice -n 5 sh scripts/lint_sources.sh` with a temporary overlay for the main-worktree frozen artifacts. It passed outright; no generated-root exception was needed. The auditor did not invoke the bare lint script or regenerate roots.

5. Static/protected-path checks:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
rg -n '^(public import|import)|set_option|sorry|admit|axiom|unsafe|opaque' KAM/Wave/Algebra/*.lean
wc -l KAM/Wave/Algebra/*.lean
```

Diff checks: exit 0, no output. The rg output contained only the reviewed public imports (Mathlib, package-local modules, EllWeight and Lam); no forbidden token or option override appeared. All four files have copyright, `module`, public imports, module docstrings and exposed public noncomputable sections. No provider, draft theorem, generated root or root part is imported by these modules. File counts: Algebra 207, Extension 385, TwoSided 267, Young 232 (1091 total), all below 1500. The authorized existing `KAM/Root/Wave.lean` delta adds exactly these four public imports and nothing else.

## Closeout and limitations

The full delta was read; every new declaration is classified; all 14 definitions have been reviewed; main estimates and consumers' parameter ranges/constants match the blueprint; no conclusion-shaped premise or junk-value proof dependency was found. Refutation attempts covered zero/negative parameters, zero mode, independent versus conjugate J inputs, squared versus max product norm, summability before inequalities/rearrangement, and constant dependence. N3 is a local wording clarification under the intended reading; N4 is documentation only. No unresolved mathematical blocker was found in this package.

This audit compares to the pinned local blueprint and frozen definitions, not a fresh audit of every cited P96-W/KP96 PDF. It does not certify the remaining consumer proofs, a bundled Banach-space interface, the dependency graph (still being built), or any frozen theorem closure. No Lean/source/manifest/root/README file was edited, and no source erratum was repaired. No resource-budget design failure arose in the completed checks. The only audit artifact is this report; scratch probes/logs are removed after recording their evidence.
