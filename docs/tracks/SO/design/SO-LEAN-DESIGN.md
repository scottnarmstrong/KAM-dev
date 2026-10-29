# Lean design: the general torus-certificate black box and its lunar client (track SO)

Design SO-DESIGN, **Revision 6**, 2026-10-29, branch `inp-design-so` (Revision 1: `628569c9`; Revision 2:
`d2352a2d`, audited FAIL in `docs/tracks/SO/audits/SO-DESIGN-audit-2.md`; Revision 3: `b442a912`, audited
FAIL in `docs/tracks/SO/audits/SO-DESIGN-audit-3.md`; Revision 4: `5767956a`, audited PASS WITH NOTES in
`docs/tracks/SO/audits/SO-DESIGN-audit-4.md`; Revision 5: `8a08ba30`, audited FAIL (F12, F13) in
`docs/tracks/SO/audits/SO-DESIGN-audit-5.md`). This is planning evidence only. It claims no proof,
touches no frozen file and freezes nothing. Appendix A (the exact draft signatures, two files since
Revision 5: engine "A-E" and lunar client "A-L") elaborates against the shared `inp` build with `sorry`
bodies only (§9).

Scope (owner, 2026-10-29, D30 and the scope decision in `SPIN-ORBIT-PLAN.md`): a fully general checker
`checkTorusCertificate` with its soundness theorem, derived through the sealed isoenergetic theorem
`KAM.Iso.Apost.g1_explicit`. It covers any `n ≥ 2` and any rationally independent reference vector (the
Diophantine membership is the external input). Hamiltonians are finite expressions with division by
certified nonvanishing expressions; embeddings are Fourier data in all coordinates. The lunar spin–orbit
system (band `|p − 1| ≤ 33/1000`) is the first client, in the rotated frame of owner ruling O5 (Revision 5). A genuine `n = 3` nonresonant toy is part of the
validation.

### Input pins

Revision 2 base: `inp-design-so` at `ad56e402` (Revision 1 plus audit 1). `inp` read at `ae496996`, which
includes the landed SO-MODEL, SO-DIO and SO-CLOCK. Running siblings were read at: SO-PI `inp-sopi`
`779c9632`, SO-REPLAY `inp-soreplay` `b3c96def` (prototype only, no measurements), and SO-GEN `inp-sogen`
`c281945d` (work in progress). SO-CONST has no commits yet.

| Input | SHA-256 |
|---|---|
| `KAM:docs/campaign/design/SPIN-ORBIT-PLAN.md` (with owner rulings O1–O4) | `3998c99a574d101e4d407f4f13b171ad522a7f50c4aa163d5b43ccd2d533a957` |
| `docs/tracks/SO/audits/SO-DESIGN-audit-1.md` | `ebc2d1f535242dddbc45718ad9c1cd942baf6ec4dd3e0269a015f625de0784f2` |
| `KAM:docs/explorations/lunar-spin-orbit-certificate-proposal.md` | `67227392977b384340c8ae7fdd2010b88fb5aeadd05672c53bab79ded2ea3d0a` |
| `KAM:docs/explorations/lunar-spin-orbit-feasibility-report.md` | `9c333266c380a96172125ffcca3ecf5aedde2d59056a3cedaeaef7a318697241` |
| `KAM/Iso/Apost/G1.lean` | `202ba7ef0fe5c215ece86970a40a8265d508243f303c2c417ce2f71250b57f40` |
| `KAM/Iso/Charts/Inputs.lean` (`IG1Body`) | `a8f405840e6a94be71deeb6632aba601e237961933f3d4e26e81e5bb21ad3bfe` |
| `KAM/Iso/Apost/Defs.lean` (`isoC1`, `isoC2`) | `bfe66bba3354dbcd66b5bbaa2dab630018b6fb44259e31cad47a319032bb8163` |
| `inp-sopi:KAM/Certificate/Arith/PiHigh.lean` | `0ee583ddcb69816240e0a38376de2819c71688941cc990f97f1dd00a1e907880` |
| `inp:KAM/Certificate/Clock.lean` | `a3c36e266fa80bb5bcf863db553398e443b21e159719faf6eb11458f0fcf9bf1` |
| `inp:KAM/Certificate/QuadraticDiophantine.lean` | `511dafebbd09f98e74dcdf9f7cb95401186269e1c04efe2d5f55ab5aa14af632` |
| `inp:KAM/SpinOrbit/Model.lean` | `d9b99918c48809dd7713fcd0560a58b0c347a99bb603bea05d316aef22f8d46f` |
| `inp:KAM/SpinOrbit/Hamiltonian.lean` | `586af68ee2cc4d5bdefbabc9d40aa7950d24c2970ea026d3d9d69e63e6bb295e` |

Revision 5 inputs (base `inp-design-so` `79ec938c`; `inp` read at `f8405551`, KAM `main` at
`00841c89`; SO-GRAPHM read on `inp-sographm` `a5d3d058`, identical to the landed file):

| Input | SHA-256 |
|---|---|
| `KAM:docs/campaign/design/SPIN-ORBIT-PLAN.md` (with owner ruling O5) | `373fb66cbd48fb3c4fb144d43b27eaa6356d735a65909c2984dd6ae91b09393f` |
| `KAM:docs/tracks/SO/studies/CONSTANTS-STUDY.md` | `85958425fe164cbb813503bd61fdc883c4f07dcbdcc9a701c2c75ac335ce7102` |
| `KAM:docs/tracks/SO/studies/SO-REPLAY2-advice-sharded-products.md` | `02139866821786478ff5370658b06eab77f6c0289fc9044ff8929c7046d857dc` |
| `docs/tracks/SO/audits/SO-DESIGN-audit-4.md` | `c6159920ddd9aaed6e97cc0fc52b11c4d1b9db782d34e60bba156720201e4668` |
| brief `SO-DESIGN-R5.md` (with addenda 1 and 2, items 6 and 7) | `7cfbe26b57ac614891ca01c96b96da57ad6fbca572db95073930d411ac7d1abb` |
| brief `SO-ROTDIO.md` (fixed rotated-frame Diophantine signatures) | `c486f6e4cb2cb4a487a0a2b1046a7892da168100f0e6765ad6acbd3d8cc70806` |
| `inp:KAM/SpinOrbit/HamExpr.lean` | `99536c0913f7d6f3b357231e908c14c60ef656ba26eb311ce19e2570b99b56bd` |
| `inp:KAM/SpinOrbit/Barrier.lean` | `00f503637bedfa82a842a37367485868b1a5ce9ccd9014735dde2ed6c1d2d04e` |
| `inp:KAM/SpinOrbit/Freq.lean` | `d1a484c49408f7cb5ab8dfd8f26e836ea9a7dbccb113459b0f9c2b9c74f5c888` |
| `inp:KAM/SpinOrbit/Graph/Inverse.lean` | `95424081dce4d7956bf865bfffce9816d658b9506809cdccf27e60749a7d83fa` |
| `inp:KAM/Certificate/QuadraticDiophantine.lean` | `511dafebbd09f98e74dcdf9f7cb95401186269e1c04efe2d5f55ab5aa14af632` |
| `inp:KAM/Certificate/Clock.lean` | `a3c36e266fa80bb5bcf863db553398e443b21e159719faf6eb11458f0fcf9bf1` |
| `inp:KAM/Certificate/Arith/Interface.lean` | `ad54915c379aa1cea665672e250298fbcc6ca496e846a92d28d7e8b2e44287e0` |
| `inp:KAM/Certificate/MatrixInv.lean` | `d5e94c5d279b356aed5aa6a02095772895051224416141c90b7e5e3652cec3cc` |
| `inp:KAM/Certificate/Arith/Fixed.lean` | `c2896ac698f4f087981ff826da068ed3846ead29466dfaf3ce7c9fe2b9815a47` |

## Revision 6

Revision 6 is a targeted revision (base `fc1231d2`, audit 5 FAIL with F12 HIGH and F13 MEDIUM on the
packed-product contract) that also replaces the R1 projections by SO-GEN2's measured numbers. Every other
Revision 2–5 contract is unchanged. Inputs:

| Input | SHA-256 |
|---|---|
| `docs/tracks/SO/audits/SO-DESIGN-audit-5.md` | `115bdb9ed25598f5d7fc4ea3ead64fde95ebccc633649c6b3dd9ee196d5b0abd` |
| brief `SO-DESIGN-R6.md` | `44c59d2b9291c5ee75ab12b6e4ea5a43beaba2cb6cb687aded366dc35018542a` |
| `inp-sogen2:docs/tracks/SO/studies/SO-GEN2-rotated-frame-candidates.md` (`5d18380a`) | `5b61190362c9a6ee18bc82361b3ef6547cbb2b792cbc45c26641b1731f0f18ec` |

| Item | Change | Where |
|---|---|---|
| **F12** (HIGH) anti-carry | The untrusted advice is now validated explicitly. New A-E §B′ "Untrusted-advice validation": `reconSlots` (`2^scale·r + e` slotwise) with `packSum_reconSlots`; the runtime guard **`reconFits w scale logs r`** (concrete, decidable: `2(2^scale|r_i| + 2^(logs i)) < 2^w` on every advice slot), with `slotsBounded_reconSlots`; the exact shard convolution `shardConv L A B s` (`shardConv_length`, `packSum_shardConv`) and its fit test `shardFits` (`slotsBounded_shardConv`); and **`shard_reconstruct`**, whose premises are only checkable guards (block lengths, `shardFits`, `reconFits`, advice length, a passing `intSlotsBound`): BOTH the exact shard convolution and the reconstruction lie in the injective range, so `packSum_injective` gives slotwise `|conv_i − 2^scale r_i| ≤ 2^(logs i)`. `PackedAdvice.{blockLen, cut, cut_length, shardLogs}` name the blocks and per-slot logs; **`PackedAdvice.shapeOK`** (decidable) checks positive width and `blockRows`, `compat`, equal widths, the target a sub-box of the product window, advice window lengths `2·blockLen − 1`, and **zero advice outside the target box and beyond the product window** (no unchecked high slots). `checkShard` now contains the length checks, `shardFits`, `reconFits` and the decode; **`checkShard_sound`** has the check as its only premise. **`checkPackedProduct_guards`** exports `1 ≤ scale`, `shapeOK`, `0 < blockLen`, the shard count and every `checkShard` from success. `checkPackedProduct_sound` is unchanged in statement (its only premise was and is the check), now with an explicit route. Audit 5's counterexample is §8 negative test P2: `packSum_audit5_cancel : packSum 4 [16, -1, 0] = 0` and `reconFits_audit5_rejects : reconFits 4 1 (fun _ => 0) [16, -1, 0] = false`, both **proved by `decide`** in the draft. | §1.16, §5, §8; A-E §B′ |
| **F13** (MEDIUM) `scale = 0` | `shapeOK` (hence `checkPackedProduct`) requires `1 ≤ scale`; exported by `checkPackedProduct_guards`; contract `checkPackedProduct_scale_zero` (`scale = 0 ⇒ false`, any data). The public theorems stay unconditional in the data. §8 adds the positive-scale overlap test (P3) and the scale-0 test (P4, audit 5's blocks). | §1.16, §8; A-E §B′ |
| SO-POLY-A stability | **No SO-POLY-A signature changes.** `packSum`, `packShift`, `packShift_eq`, `SlotsBounded`, `packSum_injective`, `listConv`, `packSum_listConv`, `convFits`, `slotsBounded_listConv`, `packSum_flatten_mul_shards`, `intSlotsBound`, `intSlotsBound_sound` and the `PackLayout`/`PackedAdvice` structures are byte-identical to Revision 5. Every new declaration above belongs to SO-POLY-B. Changed in SO-POLY-B: only docstrings of `checkShard`, `checkPackedProduct`, `checkPackedProduct_sound` (types unchanged). | §7; A-E §B′ |
| **SO-GEN2** R1 measured | `c = 237/125` (was `7/4`), `𝔪 = M = σK = σB = σT = 1987/1000` (was `39/20`; binding `σB`: the checker's weighted-ℓ¹ Gram inverse bound `1.97994`, not the projected sup ×1.05), `γ = κ/42 = 316000/7000007 = 79/(1750 s)`, enclosed threshold `10^{−74.669}`, `L = 88`, 318 bits; `e± = 4.03e-78 / 7.84e-78` (≈ 2·c·η), domain `ρ_H = 257/10000`, `P₀` disc `48769/50000 ± 191/12500` (upper torus `51231/50000 ± 1529/100000`), `P₁` disc `24983/50000 ± 127/20000`; one character witness for all seven keys with `pinHalvings = 0`, `pinOrder = 1`; torsion witness in the bordered `3×3` form (its `T` block is nearly singular). G-J: met except `B₂ ≤ 10⁻⁹⁰`, which is withdrawn (norms are enclosed on `K̃` itself). | §6; A-L §I.2, §I.4 |
| Grid-sup Gram sub-check | NOT adopted (orchestrator decision, 15:06). Possible later improvement: package R1grid (`c = 1757/1000`, `𝔪 = 1841/1000`, `10^{−73.588}`, about one order of threshold). | §6, §11 |
| **Addendum 5** naming | The signed lunar `isDiophantine_smul` is renamed **`soIsDiophantine_smul`** (it clashed with `KAM.Iso.Linear.isDiophantine_smul`, KAM/Iso/Linear/Tools.lean:38; SO-RFREQ audit 1); all mentions updated. Every signed name of A-E and A-L was checked against `.mathlib_shortnames.txt` and a KAM declaration grep: no Revision 6 name collides; the only Mathlib short-name hits are last components of namespaced names (`CertPoly.add/mul/eval/shift`, `PackLayout.dense`, `CertPoly.trim`, `average`, fields `D/H/K`), and KAM hits are the landed declarations themselves or differently namespaced names. | A-L §I.3, §I.5 |
| **Addendum 6** SO-POLY-A (finished, `inp-sopolya`) | Its handoff confirms F12 (`intSlotsBound_sound` gives only `|e_i| ≤ 2^(logs i)`, not `SlotsBounded w e`) and F13. **No SO-POLY-A declaration changes** (its 12 signed declarations and its helpers `packSum_{nil,cons,append,eq_sum}`, `packShiftAux(_eq)`, `maxAbs`, `natAbs_le_maxAbs`, `abs_getD_le`, `abs_conv_entry_le`, `packSum_flatten`, `slotRep`, `intSlotsBoundAux(_sound)`, `sum_mul_sum_range_cauchy` stay). The repair is built on them: `reconFits` implies `logs i + 1 < w` and bounds the reconstruction for `packSum_injective`; `packSum_reconSlots` from `packSum_eq_sum`; `shardFits` should use `maxAbs` with `abs_conv_entry_le`; `packSum_shardConv` from `packSum_listConv`/`sum_mul_sum_range_cauchy`; `shard_reconstruct` = `intSlotsBound_sound` + both bounds + `packSum_injective`. No reconciliation of the branch is needed. | §7; A-E §B′ |
| Landed since R5 | `HamExpr.jet_d3` landed verbatim (SO-EXPR-B2); its draft copy is removed. | A-E §D |

## Revision 5

Revision 5 is a targeted revision for owner ruling **O5** (2026-10-29, 14:20: the lunar client in the
rotated frame, parameter package R1, replay gate GO), the orchestrator's item 6 (the advice-checked
product architecture of SO-REPLAY2), item 7 (SO-ROTDIO's fixed rotated-frame Diophantine signatures,
adopted verbatim), the split of the signature file, and audit 4's documentation
finding F11 (base `79ec938c`, audit 4 PASS WITH NOTES). The general black box, its theorem and every
Revision 2–4 contract are unchanged except where this table says so. Several packages landed on `inp`
during the revision (NormBridge, CubicDiophantine, Expr/Slp/Diff, SpinOrbit/HamExpr, Graph/Inverse,
Arith/Fixed); the signature files now import them (`inp` read at `f8405551`).

| Item | Change | Where |
|---|---|---|
| **O5** frame | The lunar client works in the data's own angles: `Q₀ = q − φ`, `Q₁ = φ`, `P₀ = p`, `P₁ = p + J`. `soRotMap` (rotated → original), `soRotMapInv`, the two inverse identities and `soRotMap_symplectic` (`AᵀB = I`). `soRotHC := soHC ∘ soRotMap` and `hamiltonianVectorFieldℂ_soRotHC` (`X_{H∘L} = L⁻¹ X_H ∘ L`). | §6; A-L §I.2 |
| **O5** `H'` | `soRotHamExpr : HamExpr 2 = P₁ + (P₀²/2 − P₀) + Σ_m (−ε A_m) cos 2π(2Q₀ + (2 − m)Q₁)` (modes `(2, 2 − m)`, division-free); `soRotHamExpr_eval : eval = soRotHC` (against the landed `soHC`); `soRotHamExpr_clock : ∂_{inr 1} = 1`. Time scale (R1, `c = 7/4`): `soRotHamExprScaled c = c · H'` with `_eval`, `_clock` (`= c`) and the general `invarianceError_const_mul`. The landed original-frame `soHamExpr` (SO-HAMX) is untouched and stays valid. | §6; A-L §I.2 |
| **O5** frequencies | `lunarRotFreq ν κ = κ (ν − 1, 1)`, `κ = c/s`; exact `ℚ(√5)` instances `lunarRotFreq{Minus,Plus}_eq` (`ν₋ − 1 = (−79 + √5)/3118`, `ν₊ − 1 = (79 − √5)/3118`). Diophantine: **SO-ROTDIO's orchestrator-fixed signatures adopted verbatim** (addendum 2; `KAM/Certificate/DiophantineTransfer.lean`, proving; A-L §I.0b): the generic `isDiophantine_of_index_map` (any `n, m`; constant `γ / C^τ`) and `lunarNu{Minus,Plus}_rot_isDiophantine : IsDiophantine (1/42) 1 ![ν± − 1, 1]`, `lunarNu{Minus,Plus}_rot_half_isDiophantine` (`1/84`), from the landed SO-DIO with `T k = (k₀, k₁ − k₀)`, `C = 2`. The client scales by `κ` (`soIsDiophantine_smul`): **`IsDiophantine (κ/42) 1 (lunarRotFreq ν± κ)`**. The withdrawn draft `isDiophantine_rot` is replaced by SO-ROTDIO. At R1, `κ/42 = 125000/3000003 = 1/(24 s)`. | §6; A-L §I.3 |
| **O5** barrier wrapper | `SoGraph.torus_of_rot`: the shear `(x, y) ↦ (x − y, y)` turns rotated real data (flow `(ν − 1, 1)`, `Q̃ = Q₀`, `P̃ = P₀`) into the LANDED generic core `SoGraph.Torus … ν c m` with `Q = Q₀ + Q₁ = q`. `soBarrier_of_exact_rotTorus` (exact torus of `c·H'` ⇒ `SoBarrier`) via `invarianceError_const_mul`, `soIsDiophantine_smul`, the landed `clock_frequency`, `hamiltonianVectorFieldℂ_soRotHC`, `torus_of_rot`, `soBarrier_of_torus`. `soRotBarrier_of_cert` (certificate ⇒ barrier). `checkSoGraph`/`SoGraphCert` are frame-free (they read components `.1 0` and `.2 0`; `P₀ = p`). | §6; A-L §I.5 |
| **O5** final statements | `lunar_barriers` and `lunar_spin_confinement` are **unchanged** (`|p(t) − 1| ≤ 33/1000`, window O1); the certificates are rotated: `lunar{Lower,Upper}Cert_ham = soRotHamExprScaled lunarR1TimeScale`, `_params = lunarR1 err disp`, `_freq` at `lunarRotFreq ν± lunarR1Kappa`. `SoBackend := CertFixed soPrecision` (landed SO-ABK; `soPrecision` a named placeholder). | §6; A-L §I.6 |
| **O5** R1 | `lunarR1 err disp : CertParams`: `τ = 1`, `ρ = 1/70`, `ρ∞ = 1/70000`, `μ = 1/160`, `M = σK = σB = σT = 39/20`, `σω = 2`, `ν = 10⁻⁶`, `s = 1 + 10⁻⁶`, `γ = γ̄ = κ/42`, `E₀ = 0`; `lunarR1TimeScale = 7/4`, `lunarR1Scalar`, `lunarR1Kappa`. `err`/`disp` per torus are named placeholders (`lunar{Lower,Upper}{Err,Disp}`) filled by SO-DATA. | §6; A-L §I.4 |
| **O5** G-J | Restated in the rotated, time-scaled frame with named budgets (`B₀, B₁, B₂, B_r, B_q, B_c`, `e±`, `β₂`) that SO-GEN2 fills; under the pilot identities the `P₁` row is `c (p − 1) r` (a factor ≈ 0.03 below the original `p r`). | §6 |
| **Item 6** products | New §B′ `Poly/Packed` (SO-POLY): Kronecker packing `packSum`/`packShift` with `packShift_eq` (packing correctness), `packSum_injective` (slot bound), `packSum_listConv` (Kronecker substitution), `packSum_flatten_mul_shards` (shard decomposition), `intSlotsBound_sound` (slot decoding), `PackLayout` (dense box layout, `compat` no-wrap) with `PackLayout.intEval_mul`, design-B `PackedAdvice`, `checkShard`, `checkPackedProduct_sound` (rounding/remainder glue in slots), `CertPoly.toMants(_sound)`, `CertPoly.mulPacked(_sound)` (strip enclosure of the EXACT product). `ProductAdvice` (`packed` or `direct`), `ProductKey`, `AdviceBook`. | §1.16, §5; A-E §B′ |
| **Item 6** models | `ModelConfig α` now carries the advice book and an UNTRUSTED mantissa decoder `toMant` (production `CertFixed.toMant`); every decoded mantissa is re-verified by `mantCheck` (law-free; sound from `LawfulCertArith` alone). `CertModel.mul W cfg key a b`: packed/direct by `cfg.advice` at `key`, crude-but-sound fallback; **`CertModel.Encloses.mul` is unchanged in meaning** (gains the `key` argument). Every other contract only changes `ModelConfig` to `ModelConfig α`. **No change to the landed §A interface**; SO-ABK's landed instance already makes `mantCheck` complete (`CertFixed.mantCheck_m`). | §1.16; A-E §A, §C |
| **Split** | `SOSignatures.lean` (engine, 1049 lines, imports every landed SO module instead of restating it) and `SOSignaturesLunar.lean` (lunar client, 539 lines). The lunar file imports the landed client modules and keeps two verbatim stand-in blocks: the 20 unlanded engine declarations (checked byte for byte by `docs/tracks/SO/design/check_so_standins.py`) and SO-ROTDIO's 5 fixed declarations. Both elaborate on their own. | §9; App. A |
| **Data packaging** | Counts at R1 scale and three packaging options (chunked lint-clean modules; a line-width exemption for generated data; out-of-tree data through an elaborator). **Owner decision**, not decided here. | §7.2, §11 |
| **F11** | The Revision 4 handoff's warning that the draft `CertArith` lacks `abs`/`upMul` is obsolete (both the draft and the landed interface have them, with laws). Historical statuses are now labelled with their snapshot (§3, §9, Revision 4 table); the current statuses are in §3 at `inp` `f8405551`. | §3, §9 |
| Packages | New pre-gate: SO-ROT 300, SO-ROTDIO 150 (orchestrator, proving), SO-RFREQ 100, SO-GRAPHR 300. Changed post-gate: SO-POLY 650 → 1150 (A 550 + B 600), SO-MALG 650 → 750, SO-EMB/SO-MAT/SO-TORS +100 in all (product keys), SO-GRAPH 400 → 500, SO-DATA hand-written glue 150. Totals: pre 8,700, post 9,600, **18,300**. | §7 |

## Revision 4

*(Historical snapshot, F11: statuses in this table — e.g. SO-CEXP "proves exactly them", running at the time — refer to `inp` at Revision 4; SO-CEXP has since landed. Current statuses: §3.)*

Revision 4 is a targeted repair of the single blocking finding of the independent design audit 3 (verdict
FAIL, base `b442a912`): **F10**, the unrestricted scalar complex exponential. Nothing else changes; the
Revision 3 and Revision 2 tables below stay valid except where this table supersedes them. The general
primitive and its signatures are the orchestrator's (2026-10-29, 12:25); SO-CEXP proves exactly them in
`KAM/Certificate/Arith/ComplexExp.lean`. The real route (`ratExpUp`, `checkWeight`, the factors `exp(2B)`,
`exp(B)`, `exp(η) − 1`, `ModelConfig.taylorN/halvings`, `TorusCertificate.expHalvings/expOrder`) is
unchanged.

| Item (audit 3 consumer table) | Change | Where |
|---|---|---|
| **F10** contract | The draft's unrestricted `certCExp_sound` is **withdrawn** (false for the Taylor implementation: `z = 2`, `zRad = 0`, `N = 0` would give `|e² − 1| ≤ 2`). A §A now restates the LANDED SO-AIF `Roots.lean` declarations verbatim: `certCExp`, `certCExpSmall`, `certCExpSmall_sound` (`‖z‖ + zRad ≤ 1`), `certCExp_sound_of_small` (with `hsmall`), and the ball primitives they and the wrapper use (`CertBall`, `CertBall.Mem`, `CC.normUp`, `CertBall.ofRat`, `CertBall.times`, `mem_ofRat`, `mem_times`). No consumer calls `certCExp` directly. | §1.4, §1.7; A §A |
| **F10** general primitive | New subsection `Arith/ComplexExp` (package **SO-CEXP**, pre-gate, ~150 lines, depends on SO-AIF): `certCExpReduced z zRad s N : Option (CC α × α)` scales the ball by `2^(−s)` (ball product with `CertBall.ofRat (1/2^s)`), returns `none` unless the **rounded** reduced ball passes `certCExpSmall`, applies `certCExp` of order `N`, and squares `s` times with `CertBall.times`; `certCExpReduced_sound` holds on every successful call with no side condition. Every contribution (scaling rounding, Taylor remainder and sum rounding, each squaring's growth `r(2|c| + r)` and rounding) is inside the returned radius. Structural recursion on `s`; `s = 0` is the guarded small call. | §1.4, §1.7, §7; A §A |
| **F10** `Slp.balls` (general `HamExpr.exp`, compiled `sin`/`cos`) | Every `exp` slot (hence also `sin`, `cos`, compiled through `exp`) calls `certCExpReduced c r (cexpHalvings c r) taylorN` on its operand ball. The count `cexpHalvings c r = log₂⌈2(|re| + |im| + r)⌉ + 1` is **computed from the ball** (never a caller hypothesis); `taylorN` is certificate data (`expOrder`). A `none` makes `Slp.balls` return `none` (fail closed, so `checkHamBounds = false`). `Slp.val_mem_ball` and `nonvanishingOn_of_balls` are stated on the successful call, unchanged. Over the exact backend `certCExpReduced_cexpHalvings_isSome` (SO-BALL) shows the computed count never fails: `.exp (.const 2)`, large action balls and `exp` of a cosine mode with radius `> 1` are all handled. | §1.4, §8; A §A, §D |
| **F10** scalar pin in `expWitnessRadius` | Exp witnesses become `ExpWitness α = (poly, pinHalvings, pinOrder)`: the pin's halving count and order are **certificate data** per witness. `expPinBall g` encloses `g₀(0)` (sum of coefficients, rounding in the radius; `expPinBall_sound`). Then `out := certCExpReduced (expPinBall g) pinHalvings pinOrder`; `none` ⇒ `expWitnessRadius = none`. The pin error is `ε₀ := upAdd(|E(0) − out.1|↑, out.2)`, so `ε₀` pays input rounding, scaling, Taylor remainder, Taylor-sum rounding, the `s` squarings and the final subtraction. New contract `expWitnessRadius_pin` (successful call ⇒ the reduced call succeeded and encloses `exp g₀(0)`). `expWitness_sound` is otherwise unchanged (statement on success; `E.poly` for `E`). No unit-size hypothesis anywhere. | §1.7; A §C |
| **F10** character witnesses in `Slp.compose` | `Witnesses.expWit : List (ExpWitness α)` and `charWit : List (CertKey × ExpWitness α)`: each character witness `≈ exp(2πi k·U)` uses the same repaired pin path with its own count (for `|2π k·U(0)|` of any size). A failed reduction makes `Slp.compose` return `none` (fail closed); `Slp.compose_sound` is stated on success, unchanged. The whole-witness halving rewrite `exp a ↦ (exp(a/2))²` is not used for pins. | §1.7; A §D |
| **F10** real bounds (`exp(2B)`, `exp(B)`, `exp(η) − 1`, weights) | Unchanged: they stay on `ratExpUp` (rational upper bounds with SO-AIF's halving and coarse `3^⌈q⌉` fallback). `ModelConfig.taylorN/halvings` are now documented as real-route parameters only. | §1.7; A §C |
| **F10** lunar pins / D balls | No smallness is inferred from tiny residuals. The lunar Hamiltonian has no `exp` slot (balls unaffected); every lunar character pin (`2πi k·U(0) = i k_q v(0)`) carries its own `pinHalvings`, chosen by SO-GEN, and gate G-J now reports them and the resulting `ε₀` (§6). | §6 |
| **F10** tests and replay | New tests (SO-CEXP, `Tests/ComplexExp`): `s = 0` small (pass) and large (reject), the audit's `z = 2` rejected at `s = 0` and accepted at `s = 2`, a large imaginary pin at `s = 5`; negative test 10 (a pin with too few halvings fails composition, hence `checkTorusCertificate`); ball test 11 (`.exp (.const 2)` passes `Slp.balls`). SO-REPLAY item 7: cost of one `certCExpReduced` at the intended precision. | §5, §8; A §J |
| Packages | SO-CEXP added (pre, 150, after SO-AIF). SO-BALL 450 → 500 (`cexpHalvings`, completeness), SO-EXPW 800 → 850 (`ExpWitness`, `expPinBall`, pin contract); both now depend on SO-CEXP. Totals: pre 7,850, post 8,650, 16,500. | §7 |

## Revision 3

Revision 3 is a small, targeted repair of the three new findings of the independent design audit 2
(verdict FAIL, base `0cb95879`) and of the residual items it lists under F3 and F6. Nothing else changes;
the Revision 2 table below stays valid except where this table supersedes it.

| Item | Change | Where |
|---|---|---|
| **F7** (HIGH) averaged torsion not attached to the dimension | `torsionAvgCheck` now takes `n` and **first** checks the exact shapes `ModelMatrix.HasShape (n + 1) T` and `HasShape (n + 1) S` (decidable list-length tests: `n + 1` rows, each of length `n + 1`); it rejects otherwise, and all its matrix arithmetic is on `(n+1) × (n+1)` arrays. New law-free contract `torsionAvgCheck_shape` (pass ⇒ both shapes; this also states the F7 negative test). `torsionAvgCheck_sound` is stated for that same `n` (`h : torsionAvgCheck n T S σTμ = true`). Because `torsionIdx n` is a bijection onto `{0, …, n}`, `HasShape (n+1) T` plus `T.Encloses n (torsionIdx n) ρ F` makes the checked list matrix exactly the denoted bordered matrix, so the audit's `3×3` matrix `A` with singular leading block can no longer certify the `n = 1` average. The producer now also exports the shape: `torsionModels_sound` concludes `HasShape (n + 1) T ∧ T.Encloses … ∧ continuity`. `checkTorsion` calls `torsionAvgCheck n` with `c.torsInv`, and `checkTorsion_sound` assembles at the certificate's own `n`. The general inverse test is not restricted (no principal-block condition, no `2 ≤ n` substitute). New negative test 9 (§8). | §1.9, §4, §8; A §F, §G |
| **F8** (MEDIUM) norm bounds false at `n = 0` | `norm_fderiv_hamiltonianVectorFieldℂ_le` and `norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` take `(hn : 1 ≤ n)`; the row-sum premise is then nonvacuous and forces `0 ≤ B`. The checker derives `1 ≤ n` from `StaticFacts.hn : 2 ≤ n` in `checkHamBounds_sound`. | §1.3, §4; A §E |
| **F9** (MEDIUM) lunar `J`-row identity | Corrected. Since `H` is affine in `J` with `∂_J H ≡ 1` and the other partials independent of `J`, `X_H(K̃) = X_H(K₀)`, so `E(K̃) = E(K₀) − (0, 0, 0, D_{sω*}ΔJ)`: **`E(K̃)_J = E(K₀)_J − D_{sω*}ΔJ`**, which is `p r − D_{sω*}ΔJ` under the scalar pilot identities (and only then). Gate G-J now budgets the **sum**: `B_r + B₁ + B_c ≤ e/2`, where `B_r = sup|E(K₀)_J|` (`= sup|p r|` under the pilot identities), `B₁ = sup|D_{sω*}ΔJ|`, and `B_c` bounds every other candidate-replacement error (finite Fourier `q, φ, p` data differing from the pilot's scalar embedding, coefficient rounding/truncation), with the `q, φ, p` rows `≤ e/2` likewise. The previous stand-alone target `B₁ ≤ e/4` is withdrawn. The mandatory recomputation of the **actual full residual** of `K̃` by the checker (and by SO-GEN's exact evaluator) is unchanged; no identity is used in soundness. | §6, §10 |
| **F3** residual (torsion/sub-check contract) | Closed by F7: the producer→consumer pair `torsionModels_sound` → `torsionAvgCheck_sound` now matches on `n`, shape, enclosure and continuity, with no unstated premise. Also from the audit's soundness notes: `CertPoly.add` is **exact list concatenation** (law-free, no error term) with `eval_add` an equality, because a uniform bound for all complex `θ` cannot hold for rounded nonzero modes; rounded coefficient merging lives only in the strip-weighted `CertModel.add`. Implementation obligations recorded for SO-EXPR/SO-BALL: jet compilation/pruning must keep every denominator-validation slot (folding `0 * (1/0)` to `0`, or `.pow a 0` to `1`, must not drop a denominator that `NonvanishingOn` requires). | §1.4, §4, §7; A §B |
| **F6** residual (SO-BALL's dependence on `CertArith ℚ`) | The trivial exact instance `instCertArithRat` / `instLawfulCertArithRat` (`val = cast`, zero errors) moves to the **pre-gate** SO-AIF (`Arith/Rat.lean`); SO-BALL imports it. SO-ABK (post-gate) keeps only `Arith/Fixed` and the production-backend choice. Lines move from SO-ABK to SO-AIF; totals are unchanged. | §5, §7; A §A |

## Revision 2

Revision 2 answers every finding of the independent design audit 1 (verdict FAIL) and the owner rulings
O1–O4. The table lists each change and where it lives. "A §X" means section X of Appendix A.

| Item | Change | Where |
|---|---|---|
| **F1** (BLOCKING) frequencies | The single-`ℚ(√d)` carrier `CertFreq` is **removed**. The certificate carries only a rational box `freqBox : FreqBox` (centre and radius per coordinate). The black box quantifies over an **exact real vector** `ωstar : Fin n → ℝ` and takes two proved facts about it: `hω : FreqEncloses n c.freqBox ωstar` (its denotation lies in the box) and the external input `hdio : IsDiophantine γ τ ωstar`. Every sub-check is uniform over the box. Any rationally independent `n`-tuple is therefore admissible. A provider `algFreq`/`algFreq_encloses` covers coordinates in `ℚ(x)` for a certified real `x` (`checkRootEnclosure`, any `m`-th root). The lunar `n = 2` case keeps its exact `ℚ(√5)` instance (`lunarFreq{Minus,Plus}_eq`, then `lunar{Lower,Upper}Cert_freq`). The genuine `n = 3` example is `cubicFreq = (∛2/2, ∛4/2, 1/2)`, which is `(1/12, 2)`-Diophantine by the norm form of `ℚ(∛2)`; it comes with a positive-residual toy, `toyCert3_torus`. Diophantine membership stays external and is not weakened, and the headline is not restricted to `n = 2`. | §1.10, §4, §8; A §G "Exact frequencies", §J |
| **F2** (HIGH) arithmetic laws | Option "restructure". (a) Real data has a **law-free direct denotation** `CertRealPoly.eval` (constant `val zero` plus the sum of `c χ_k + c̄ χ_{−k}`). `CertEmbedding.eval` uses it, and a missing component denotes `0` rather than a backend `ofInt 0`. Reality of `K` (`isRealOnReals`), differentiability and periodicity are law-free and unconditional; the audit's `α = Unit` carrier is harmless for them. (b) Every theorem about a *computed* object assumes `[LawfulCertArith α]`: `eval_toPoly` (the explicit "constant plus conjugate-pair sum" denotation theorem), `conjugateSymmetric`, `CC.toC_conj`, `CC.toC_zero`, `eval_add`, `eval_conjReflect`, the model and witness theorems, and all sub-check contracts. (c) Backend default values were rechecked. `ModelMatrix.Encloses` requires every entry to be present, `polyMatrix` and `CertEmbedding.eval` default to `0`, and `compose_sound` states `ms.length = wanted.length` and indexes without a default. | §2; A §A, §B, §D, §F |
| **F3** (MEDIUM) torsion contract | `torsionModels_sound` is stated. Its inputs are the validated weight and `π`, a successful `gramCheck` whose certified `(δ, β)` is passed into `torsionModels`, successful construction, the frequency box with `FreqEncloses` of the exact `ω`, the scalar `s`, `K` mapping the strip into an open `D`, and `e.NonvanishingOn D`. Its conclusion is the entrywise enclosure of the **literal frozen** `extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)` (the `torsion` block with `DN[sω]`, the border column `sω`, and the last row `DH(K) N`) together with its continuity. `gramCheck_sound` now also exports `‖G⁻¹ − B‖ ≤ δβ/(1−δ)`. All eight sub-check contracts are stated, with an acyclic assembly route to every `G1Hyps` field (§4). `hT`, Gram invertibility and torsion continuity are derived, never assumed. | §1.9, §4; A §F, §G "Sub-check contracts" |
| **F4** (MEDIUM) toy | Revision 1's zero-error `ℚ(√5)` toy was unrepresentable and is replaced. **T2**: `H = J + p²/2`, `K = (θ, (ν̃, −ν̃²/2))` with **rational** `ν̃ ≈ ν₋`, reference vector `(ν₋/2, 1/2)` from SO-DIO, `s = 2`, and a **positive** residual budget `err ≥ |ν̃ − ν₋|`. **T2d** is T2 with a division in `H`, to exercise O2. **T3** is the `n = 3` analogue with `cubicFreq`. All three discharge the Diophantine premise (`toyCert{2,2d,3}_torus`). A separate checker-only test **TR** keeps exact rational `ν = 1/2` and zero error, and is labelled as having no Diophantine premise (its vector is resonant). | §8; A §J |
| **F5** (MEDIUM) Fourier `J` | Both remedies apply. (a) The checker evaluates **every** sub-check on the actual four-component candidate `K̃ = (q, φ, p, J̃)`: invariance, energy, `DK`, Gram, torsion and graph checks all read `J̃`'s data. No pilot identity (`H(K) = E₀`, zero energy error) is used anywhere in soundness. (b) Feasibility gate **G-J** applies before SO-DATA. SO-GEN must deliver exact finite data plus explicit strip-weighted budgets for `ΔJ := J̃ − J₀`, where `J₀ = E₀ − p²/2 − V(q, φ)` is the exact energy lift and `H(K̃) − E₀ = ΔJ` holds identically. The budgets are `B₀ = sup_{T_ρ}|ΔJ|`, `B₁ = sup_{T_ρ}|D_{sω*}ΔJ|`, and `B₂ = max(sup|∂ΔJ|, sup|∂²ΔJ|)`, with targets `B₀, B₁ ≤ e/4` and `B₂ ≤ 10⁻⁹⁰`. SO-GEN must also recompute every sub-check margin on `K̃` independently of the scalar pilot. *(Revision 3, F9: the `J`-row identity and the G-J targets are corrected; see the Revision 3 table.)* | §6, §7 (gate G-J) |
| **F6** (MEDIUM) gating | Packages are split into a **pre-gate** set (backend-neutral interfaces, ℚ-only mathematics, structural semantics) and a **post-gate** set (backend instances, performance-sensitive algorithms, data), which waits for the SO-REPLAY verdict. SO-ARITH is split into SO-AIF (interface, pre-gate) and SO-ABK (backends, post-gate). SO-CONST and SO-PI are running pre-gate, and SO-CLOCK has **landed** (`inp` `092a9d11`). `phaseBasis` lives in the shared basic module `KAM/Certificate/PhaseBasis.lean` (landed), which `Expr/Diff`, `NormBridge` and `Clock` import. The line totals are recomputed. | §7 |
| **O1** momentum window | Kept: the headline initial region is the constant window `lunarPLo < p₀ < lunarPHi` (about `(0.9819, 1.0181)`), and graph-error transport is deferred. Literal rational endpoints replace the names before the freeze. | §6 |
| **O2** division | `HamExpr.div` and `SlpOp.inv` are added; `HamExpr.eval` uses `/`. `HamExpr.NonvanishingOn` (recursive, concrete) states that every denominator is nonzero on a set. Holomorphy is structural on open sets where it holds (`contDiffOn_eval`), and the jets need it (`jet_d1/d2/d3`). Periodicity and reality stay unconditional. Nonvanishing on `D` is **certified** by the new ℚ ball arithmetic `Slp.balls`, which fails on any `inv` whose operand ball contains `0` (`nonvanishingOn_of_balls`, part of `checkHamBounds`). Along `K`, a reciprocal **a-posteriori witness** (`invWitness_sound`, scalar Neumann series) certifies nonvanishing on the strip and encloses `1/b`, with no lower-bound data. The norm bridges take local `ContDiffAt`. | §1.1, §1.4, §1.7; A §C, §D, §E |
| **O3** SO-PI now | SO-PI (`KAM/Certificate/Arith/PiHigh.lean`, running, backend-independent) provides `piLoQ/piUpQ`, Machin `piLowRat/piUpRat` (width `≤ 10⁻¹⁴⁰`) and `eLowRat/eUpRat`. `PiEnclosure` carries its Machin parameters, and `checkPiEnclosure` validates the backend ball against them. `supBound` uses lower `π` bounds for negative degrees. `cRUpQ` uses `eLowRat`. | §1.6; A §A |
| **O4** analytic graphs | Kept out of the first freeze (later corollary). | §11 |

Further audit notes were adopted. `checkWeight` requires `0 < ρ` (positive width), and `checkStatic`
checks `weight.rho = params.rho`. The exp-witness radius formula is now explicit (A §C). The SOS check pays
its residual (`m ≤ m₀ − r`, with `m₀` as certificate data). The graph check requires a strict remaining
monotonicity margin `mono > disp/ρ∞`. `so_confinement` uses the global Lipschitz bound of `soField`, not
the lunar range. The upper-certificate companions (`lunarUpperCert_ham/_passes`, `lunarUpperGraph_passes`)
are stated. The `exp` halving fallback is the syntactic rewrite `exp a ↦ (exp (a/2))²` in the jet compiler
(`Complex.exp_add`) and needs no interface change. The client now imports the **real** SO-MODEL and SO-DIO
modules: `soHC`, `soField`, `soEpsQ`, `soAQ`, `KAM.Certificate.lunarNu*`. There are no stand-ins for them.

## 1. Decisions

1. **Expression language (`HamExpr n`).** The constructors are: rational constant, `π`, action coordinate
   `I_j`, period-one modes `cos(2π k·θ)` and `sin(2π k·θ)` (`k ∈ ℤⁿ`), `+`, `×`, **`/`** (O2), natural
   power, `exp`, `sin` and `cos`. Every constructor maps real points to reals, and angles enter only
   through integer modes. **Periodicity, translation invariance and reality are therefore structural and
   unconditional** (`eval_add_int`, `eval_real`; `x/0 = 0` keeps both true even off the certified set).
   **Holomorphy is structural on any open set where `NonvanishingOn` holds** (`contDiffOn_eval`). The
   checker certifies `NonvanishingOn D` by ball arithmetic on `D` (decision 4). Complex exponentials
   `e^{2πik·θ}` are internal to the straight-line program, not user syntax, so reality stays structural.
2. **Domain.** `D = T_{ρ_H} × Π_i {|I_i − c_i| < r_i}` (`certDomain`) with rational `ρ_H > 0`, centre `c`
   and radii `r`. It is open and translation invariant by construction. The checker certifies
   `ball(K θ, μ) ⊆ D` on `T_ρ` by `ρ + ι_i + μ ≤ ρ_H` and `sup|A_i − c_i| + μ ≤ r_i`, where
   `ι_i = min(sup|U_i|, ρ Σ_j sup|∂_j U_i|)`. The second form of `ι_i` is the mean value inequality from
   the real point, where `Im U_i = 0`.
3. **Norms.** These are exactly the existing API: max norms on `Fin n → ℂ` and on the product; operator
   norms of `fderiv` and `iteratedFDeriv`; the matrix row-sum norm via `open scoped Matrix.Norms.Operator`.
   New bridges (A §E) bound `‖DH‖`, `‖D²H‖`, `‖DX_H‖` and `‖D²X_H‖` by sums of partials along
   `phaseBasis a`, assuming **local** `ContDiffAt` (division). The two `X_H` bridges also take
   `1 ≤ n` (Revision 3, F8: at `n = 0` the row-sum premise is vacuous and a negative `B` would make
   them false); the checker supplies it from `2 ≤ n`.
4. **Derivatives: the checker differentiates symbolically.** The certificate carries no derivative data.
   `HamExpr` is compiled to a straight-line program (`Slp`) whose ops are const with `2π`-degree, action,
   character, add, mul, exp and **inv**. `HamExpr.jet` appends forward-mode derivative slots up to order 3
   (`(x⁻¹)' = −x⁻¹x⁻¹x'`). `jet_d1/d2/d3` hold at every point of an open set where `NonvanishingOn`
   holds. On `D`, all slots are evaluated by **ℚ ball arithmetic** (`Slp.balls`: centre and radius, with
   `exp`, and the compiled `sin`/`cos`, via the range-reduced `certCExpReduced` at the halving count
   `cexpHalvings` computed from the operand ball; a `none` fails closed. Revision 4, F10). Balls replace Revision 1's majorants (majorant = `|centre| + radius`) and also
   certify every `inv` operand away from `0`. Cauchy-only bounds remain rejected (a factor of about 6 in
   `M`, about `6^{30}` in the constants). Derivatives of `K` are exact Fourier multipliers on its data
   (`CertModel.ofDeriv`). Implementation obligation (audit 2, Revision 3): constant folding and pruning
   in the jet compiler must preserve every denominator-validation slot that `NonvanishingOn` of the
   source expression needs (`0 * (1/0)` folded to `0`, or `.pow a 0` to `1`, keeps its `inv` operand in
   the ball pass), so a successful ball evaluation always certifies the syntactic expression.
5. **Enclosure semantics: Fourier models in the sup norm on the open strip.** A model `(deg, P, r)`
   denotes `(2π)^deg (P + T)`, where `P` is a finite polynomial and `sup_{T_ρ}|T| ≤ r`
   (`CertModel.Encloses`). Truncation and rounding move `|c_k| w^{|k|₁}` into `r`, where `w ≥ e^{2πρ}` is
   validated once by `checkWeight` (which requires `ρ > 0`).
6. **`2π`-degree tagging.** Model coefficients never contain `π`; the factor `(2π)^deg` is symbolic. Mixed
   degrees use `CertModel.toDeg` with a validated `PiEnclosure`. Validation is against SO-PI's Machin
   bounds at the certificate's parameters `(machinK, machinJ)`, so widths down to `10⁻¹⁴⁰` are available
   (O3). Upper bounds of `(2π)^deg` use `piUpQ` for `deg ≥ 0` and `piLoQ` for `deg < 0`. In the lunar
   problem every cancelling sum is degree-homogeneous (`angleDeg = −1`).
7. **Nonlinear composition: a-posteriori witnesses, not Taylor series.**
   - *`exp`:* the witness `E ≈ exp g₀`, where `g₀` is the degree-zero polynomial part. With `|g₀| ≤ B`, pin
     error `ε₀` and residuals `r_j ≥ sup|∂_jE − (∂_j g₀)E|`, the radius is
     `exp(2B)(ε₀ + Σ_j(1/2 + ρ)r_j) + exp(B)(exp η − 1)`, where `η` is the radius of `g`.
     *Pin (Revision 4, F10):* `ε₀ := upAdd(|E(0) − out.1|↑, out.2)` with
     `out = certCExpReduced (expPinBall g) pinHalvings pinOrder` (per-witness certificate data;
     `none` ⇒ the witness fails). `ε₀` therefore contains the rounding of `g₀(0)`, the scaling, the
     Taylor remainder and sum rounding, all `s` squarings and the final subtraction. The real factors
     stay on `ratExpUp`.
   - *Characters:* `χ_k∘K = χ_k · exp(2πi k·U)`, with witnesses keyed by the normalized index; each
     is an `ExpWitness` and its pin `exp(2πi k·U(0))` uses the same reduced path.
   - *Reciprocal (O2):* the witness `Q ≈ 1/(P + T)`. From `δ ≥ sup|1 − Q(P + T)|` and `δ < 1` it follows
     that `b ≠ 0` on `T_ρ` and `|1/(P + T) − Q| ≤ sup|Q| δ/(1 − δ)` (`invWitness_sound`). It needs one
     product and no lower-bound data.
   - *Halving fallback:* `exp a ↦ (exp(a/2))²`, a syntactic rewrite of the whole witness (for the
     `e^{2B}` factor only; the scalar pin uses `certCExpReduced`, not this rewrite).
8. **Gram inverse on the complex strip (bilinear `DKᵀDK`).** This is unchanged. The certificate supplies a
   polynomial matrix `B(θ)`, and the checker certifies `δ = sup‖I − BG‖ < 1`, `β ≥ sup‖B‖` and
   `β/(1 − δ) ≤ σB − μ`. `gramCheck_sound` exports invertibility, the row-sum bound **and**
   `‖G⁻¹ − B‖ ≤ δβ/(1 − δ)`. The torsion models consume the last bound.
9. **Averaged bordered torsion (contract `torsionModels_sound`).** The entry models of the literal frozen
   `extendedTorsion H K (sω)` are built for every `ω` in the box:
   - the `torsion` block, from `DX_H∘K` (jet `d2` composed with `K`) and `N = Ω₀ DK B` with the radius
     from decision 8;
   - `DN[sω] = Ω₀(D²K[sω] G⁻¹ + DK D(G⁻¹)[sω])` with `D(G⁻¹)[sω] = −G⁻¹(DG[sω])G⁻¹`
     (`KAM.fderiv_matrix_inv_apply`);
   - the border column `sω` (a ball from the box);
   - the last row `DH(K)N` (jet `d1` composed with `K`).

   The average is the zero mode ± radius. A constant witness `S` gives
   `δ_T = ‖I − SC‖ + ‖S‖‖R‖ < 1`. **(Revision 3, F7.)** `torsionAvgCheck n` first checks that `T`
   and `S` have exactly `n + 1` rows of length `n + 1` (`ModelMatrix.HasShape`), and
   `torsionModels_sound` exports that shape for the producer's output, so the certified inverse is the
   inverse of the whole `(n+1) × (n+1)` average and never of a larger matrix containing it.
10. **Frequencies (F1).** The certificate carries a rational box, and the theorem takes the exact
    `ωstar : Fin n → ℝ` with `FreqEncloses` and `IsDiophantine`. `ω* ≠ 0`, the ray margins
    `ν ≤ (s−1)‖ω*‖`, `ν ≤ (σω−s)‖ω*‖` and every `sω`-dependent model use only the box. The box fact is
    proved outside the checker by a provider:
    - `algFreq_encloses` with `checkRootEnclosure` for algebraic coordinates (lunar: `ℚ(√5)`; toy:
      `ℚ(∛2)`);
    - a user-specific lemma for any other exact vector.

    Box radii are `≤ 10⁻¹¹⁰` in the lunar certificates (rationals with large denominators).
11. **Constants.** `τ ∈ ℕ`. `cRUpQ` bounds `c_R` from `piLoQ` and `eLowRat`. The rational mirrors `isoC1Q`
    and `isoC2Q` dominate the real constants (SO-CONST, running).
12. **Trust boundary: the kernel only.** Sub-checks are `Bool` functions proved `= true` by
    `decide +kernel`. Never `native_decide`, `Lean.ofReduceBool`, axioms or `implemented_by`. Recursion is
    structural only, over `List`.
13. **Staging.** `checkTorusCertificate` is the conjunction of eight named sub-checks, each with its own
    soundness contract (A §G); data modules prove each `= true` separately. A check that would need a
    recursion-depth or heartbeat override is a design signal (rule 1), to be reported and never masked.
14. **Lunar headline (O1).** The barriers are continuous invariant graphs. The initial region is a
    constant momentum window `lunarPLo < p₀ < lunarPHi` (any `q₀, φ₀`), certified by SOS bounds of `p` on
    the two real tori plus the displacement bound.
15. **Certificates are pure data.** `TorusCertificate` contains no proof and no real number. Every real
    object (the exact `ω*`, the exact torus) enters only through the soundness theorem's binders.
16. **Products are advice-checked (Revision 5, item 6; SO-REPLAY2).** Every product the checker
    needs is one `CertModel.mul W cfg key a b`. Its polynomial part is never multiplied out pairwise in
    the kernel: the certificate carries, under the product's `key`, design-B advice (the rounded in-box
    result per output shard and a log-bound for the other slots). The checker decodes the factors'
    integer mantissas (untrusted decoder `cfg.toMant`, each value re-verified by `mantCheck`), packs
    them by shifts into one integer per block of 32 rows (`w = 2·bits + 16`), and checks every shard
    with one kernel multiplication per block pair: `Σ_{i+j=s} pack(A_i) pack(B_j) − 2^scale pack(r_s)`
    must decode to bounded slots. **Revision 6 (F12, F13):** the advice is untrusted, so each shard also
    checks `shardFits` (exact side) and `reconFits` (advice side, `2^scale·r + e`) to put both lists in
    the injective range, and `shapeOK` checks `1 ≤ scale`, layouts, advice lengths and zero advice off
    the target; all are exported from success (`checkShard_sound`, `checkPackedProduct_guards`).
    Soundness chain: `packShift_eq` → `packSum_listConv` (Kronecker) and
    `packSum_flatten_mul_shards` (shards) → `intSlotsBound_sound` + `shard_reconstruct` (decoding) →
    `checkPackedProduct_sound` (slot remainders) → `PackLayout.intEval_mul` + `toMants_sound` +
    `ofDyadic_sound` → `CertPoly.mulPacked_sound` (strip enclosure of the exact product) →
    `CertModel.Encloses.mul` (unchanged meaning). A missing or failing advice falls back to the crude
    enclosure `sup|a|·sup|b|` (sound; later margins fail), so no contract gains a premise. The
    `direct` advice keeps the Revision 4 product for the `ℚ` toys and tests.

## 2. Carriers and conventions

- Ambient types are `Fin n → ℝ` and `Fin n → ℂ`; indices are `Fin n → ℤ`. Phase points are
  `(Fin n → ℂ) × (Fin n → ℂ)` (angles first), and phase indices `Fin n ⊕ Fin n` follow
  `KAM.Torus.sumVec` order. Never `EuclideanSpace`.
- Keys are `CertKey = List ℤ`, denoted by `certKeyFun n` (missing entries are `0`). Lists may hold
  duplicate or padded keys; the exact sums handle these. Optimized algorithms validate and canonicalize
  key shapes before relying on them.
- **Denotations are law-free; correctness theorems carry `[LawfulCertArith α]`** (F2).
  - `CertPoly.eval` and `CertRealPoly.eval` are direct.
  - `CertRealPoly.toPoly` (computed, with `CC.conj`) agrees with the direct denotation under the laws
    (`eval_toPoly`), and its coefficients are conjugate symmetric (`conjugateSymmetric`).
  - `CertPoly.eval_eq_fourierSum` bridges to `KAM.fourierSum`.
- `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))`. It is primary, real and entire by construction,
  with law-free proofs.
- Parameters of `g1_explicit` are exact rationals in `CertParams`. The theorem's `ν` is `nuRay`.
- Backend numbers are `α` with `CertArith α` (data) and `LawfulCertArith α` (laws, proved once per
  backend); complex backend numbers are `CC α`. Ball arithmetic on `D` and frequency boxes are always
  in `ℚ`.

## 3. Reuse map and upstream interfaces

| Need | Existing declaration (reused, read-only) |
|---|---|
| sealed theorem | `KAM.Iso.Apost.g1_explicit`, body `KAM.Iso.Charts.IG1Body` |
| constants | `KAM.Iso.Apost.isoC1`, `isoC2`, `hatcStar`, `hatCDelta`; `KAM.Apost.cR`, `delta0`, `aExp` |
| characters, series | `KAM.character`, `fourierSum`, `norm_character_le`, `norm_fourierSum_le`, `torusAverage`, `torusAverage_character`, `differentiableOn_fourierSum` |
| reality | `Fourier.ConjugateSymmetric`, `fourierSum_im_eq_zero` |
| matrices | `KAM.norm_le_iff_forall_rowSum`, `matrix_neumann_uniform`, `fderiv_matrix_inv_apply`, `KAM.Torus.sumVec`, `colMat`, `sqMat`, `norm_colMat`, `norm_sqMat`, `Apost.tangentMat`, `norm_tangentMat` |
| Cauchy (graph) | `norm_coordinate_fderiv_le_of_mem_complexStrip`, `torusCoeff_fderiv_real`, `eq_zero_of_torusCoeff_eq_zero` |
| ODE | `KAM.ODE.IsSolutionIn`, `IsInvariantSet`, `gen_barrier`, `gen_uniqueness`, `gen_local`, `IsMaximalSolution`, `gen_continuation` |
| transcendental bounds | Mathlib `Real.exp_bound`, `Complex.exp_bound`; SO-PI `piLowRat_lt_pi`, `pi_lt_piUpRat`, `eLowRat_lt_exp_one` |

**Upstream interfaces (current, `inp` `f8405551`, Revision 5).** Landed and imported by the
signature files: SO-MODEL, SO-DIO, SO-CLOCK, SO-PI, SO-AIF, SO-RAT, SO-CEXP, SO-PBASE (`Poly/Basic`,
`Model/Basic`), SO-FREQ (`Freq`, `SpinOrbit/Freq`), SO-EXPR-A/B1 (`Expr/{Basic,Slp,Diff}`), SO-NORM,
SO-MINV, SO-CONST, SO-DIO3, SO-HAMX (`SpinOrbit/HamExpr`), SO-CONF (`SpinOrbit/Barrier`), SO-GRAPHM
(`SpinOrbit/Graph/Inverse`), SO-ABK (`Arith/Fixed`). In audit or running at this snapshot: SO-BALL,
SO-EXPR-B2 (`jet_d3`), SO-GEN2 (rotated-frame candidates and norm enclosures).

The table below is **historical** (status at `inp` `ae496996`, Revision 2), kept for provenance.

| Owner | Name | Status / shape consumed |
|---|---|---|
| SO-MODEL | `KAM.SpinOrbit.soField`, `soHC`, `soV`, `soVC`, `soEpsQ`, `soAQ` | landed; imported (`soHamExpr_eval : soHamExpr.eval z = soHC z`) |
| SO-DIO | `KAM.Certificate.lunarNu{Minus,Plus}`, `_eq`, `_half_isDiophantine` | landed; imported (`IsDiophantine (1/42) 1 ![ν/2, 1/2]`) |
| SO-CLOCK | `KAM.Certificate.phaseBasis`, `clock_frequency` | landed (092a9d11), statement identical to A §H; stand-in in A only because the shared build predates it |
| SO-PI | `piLoQ`, `piUpQ`, `atanS`, `piLowRat`, `piUpRat`, `PiHighCert`, `eLowRat`, `eUpRat` | running (`inp-sopi` 779c9632); verbatim stand-in block in A §A |
| SO-CONST | `cRUpQ`, `isoC1Q`, `isoC2Q`, dominance theorems | running (no commits yet); A §F signatures |
| SO-GEN | Lean data emitter; budgets `B₀, B₁, B₂` (gate G-J) | in progress |
| SO-REPLAY | backend choice, shard sizes | prototype only; gate for post-gate packages |

SO-MODEL's `ScalarEmbedding` identities are not on the black-box path. They remain a generator tool:
the generator's `J₀` is exactly the scalar lift.

## 4. The black box: every hypothesis of `g1_explicit`

```
checkTorusCertificate_sound (h : checkTorusCertificate c = true) {ωstar}
  (hω : FreqEncloses n c.freqBox ωstar) (hdio : IsDiophantine γ τ ωstar) : CertifiedTorus c ωstar
```

applies

```
KAM.Iso.Apost.g1_explicit (n := n) hn (τ := (c.params.tau : ℝ)) hτ
  (ρ := c.params.rho) (ρinf := c.params.rhoInf) hρinf hρinfρ
  (M := c.params.M) (σK := c.params.σK) (σB := c.params.σB) (σT := c.params.σT)
  (μ := c.params.μ) (γbar := c.params.γbar) (σω := c.params.σω) (ν := c.params.nuRay)
  hM hσK hσB hσT hμ hγbar hσω hν ωstar hωstar
```

and feeds `.2.2.2` the arguments `(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.params.s, c.params.γ,
c.params.err, c.params.E0)` and the fields of `G1Hyps c ωstar`, in the frozen order. It then replaces
`isoC2 · e/(γ²ρ^{2τ})` by `disp` (`hdisp`). Audit 1 replayed this bridge for Revision 1 with no
placeholder in the bridge proof itself. Revision 2 changes only the provenance of `ωstar` (a binder
instead of a projection).

**Assembly route (acyclic).** Each `G1Hyps` field comes from exactly one contract:

| `G1Hyps` fields | contract | depends on |
|---|---|---|
| `hn hτ hρinf hρinfρ hM hσK hσB hσT hμ hγbar hσω hν hs1 hsσ hγ hγγbar he0` | `checkStatic_sound` (`StaticFacts`) | — |
| `hωstar hν1 hν2` | `checkStatic_freq` | Static, `hω` |
| `hK hKp hKr` | `TorusCertificate.emb_structural` (law-free) | — |
| `hbd`, plus `NonvanishingOn D` | `checkHamBounds_sound` (balls + jets + §E bridges) | Static (weights) |
| `hopen htransl hholo hper hreal` | `TorusCertificate.ham_structural` | `NonvanishingOn D` |
| `hball hDK` | `checkEmbedding_sound` | Static |
| `hG` | `checkGram_sound` (from `gramCheck_sound`) | Static |
| `hE` | `checkInvariance_sound` (`compose_sound`, `jet_d1` at `K θ ∈ D`, box) | Static, HamBounds, Embedding, `hω` |
| `hEn` | `checkEnergy_sound` (`Encloses.average`) | Static, HamBounds, Embedding |
| `hTu hTb` | `checkTorsion_sound` = `torsionModels_sound` + `torsionAvgCheck_sound` | Static, HamBounds, Embedding, Gram, `hω` |
| `hC1 hdisp` | `checkSmallness_sound` (SO-CONST dominance) | Static |

Notes on the table:
- `K θ ∈ D` follows from `hball` with `μ > 0`.
- The continuity premise of `torsionAvgCheck_sound` is the last conjunct of `torsionModels_sound`; its
  enclosure premise is the middle conjunct, at the same `n`; the exact shape (first conjunct, and
  `torsionAvgCheck_shape`) ties the checked list dimension to `n + 1` (Revision 3, F7).
- `checkHamBounds_sound` passes `1 ≤ n` (from `StaticFacts.hn`) to the two §E norm bridges (F8).
- `CertifiedTorus c ωstar` is the `IG1Body` conclusion verbatim, with `disp` as the closeness bound. It
  is never a hypothesis (rule 6). `hω` is a typing fact about the input vector, of the same kind as
  `hdio`, and is supplied by a provider.

## 5. Arithmetic layer and the replay gate

The checker is generic in `α` with `[CertArith α]`; soundness needs `[LawfulCertArith α]`. Two instances
are planned:
- `ℚ`: exact, with zero error terms; trivial, hence **pre-gate** in SO-AIF (`Arith/Rat.lean`), because the
  pre-gate ball arithmetic (SO-BALL) denotes its `CC ℚ` balls through it (Revision 3, F6);
- `CertFixed P`: floor rounding, with ulp errors carried in `mulErr`/`addErr`.

Data numbers are exact in both; only computed centres round. Ball arithmetic on `D`, frequency boxes,
root enclosures, `π` and `e` are always computed in `ℚ`, independently of the backend.

SO-REPLAY must report the following (decision rule unchanged from Revision 1):
1. Kernel time and memory of one product of two polynomials of the SO-GEN support at about 450-bit
   coefficients, for both backends (including `Nat.gcd` normalization for `ℚ`), and the recursion depth
   on lists of that length. Choose `ℚ` if a full stage replays in under about 1 h and 16 GB per torus and
   within 3× of fixed point.
2. For fixed point, the accumulated ulp radius after a stage, which must stay `< 10⁻¹¹⁰`.
3. The largest list one `decide +kernel` carries without a depth override (this sets the `List.all`
   split size).
4. The elaboration time of a 1500-line data shard.

Additions for Revision 2:
5. One reciprocal-witness check (one product), for a client with division.
6. One `checkPiEnclosure` at `(50, 15)`.

Addition for Revision 4 (F10):
7. One `certCExpReduced` at the intended precision (backend precision of the pins, `s` up to the
   lunar maximum reported by SO-GEN, `N` at the pin order), and one ℚ `Slp.balls` `exp` slot at
   `cexpHalvings`: time, memory and the growth of rational sizes over the `s` squarings.

If nothing fits, the levers are those of the plan (sharper `n = 2`, `τ = 1` constants), never
overrides.

**Revision 5: the gate's verdict and the product architecture.** The replay gate is **GO** (owner,
14:20). SO-REPLAY measured naive sparse products at about 2.3 ms and 190 KB per coefficient pair in
the kernel, hopeless at the lunar scale; SO-REPLAY2 measured Kronecker-packed shards checked against
supplied advice at 2.0–8.6 s kernel and ≤ 2.4–3.8 GB per 32-row shard (1e-130 data). The design adopts
it as the ONLY product route (decision 16, A-E §B′):
- production backend **fixed point** `CertFixed P` (landed SO-ABK); `P` from SO-GEN2's precision
  (about 300 bits at R1, plus guard bits); slot width `w = 2P + 16`;
- factors laid out densely on a key box (`PackLayout`, no-wrap strides), cut into blocks of
  `blockRows = 32` rows (8192 slots at 256 columns); packing by shifts (`packShift`);
- design B advice per real product: the rounded in-box result per shard window and a log-bound for
  out-of-box slots; four real products per complex model product;
- every shard is one declaration `checkShard … = true` by `decide +kernel` (the elaborator's list
  limits — ≥ 64 outer rows or ≥ 4096 flat elements fail — fix the 32-row grouping; data defs are
  `noncomputable def`, one per group);
- the `direct` route remains for the `ℚ` toys.

Remaining measurements (SO-POLY, before SO-DATA): the end-to-end design-B shard with the rounding glue,
complex (re/im) products, and the 128-row middle size; none of them changes a signature.

## 6. The lunar client

**Revision 5 (owner ruling O5): the rotated frame.** The client works in the data's own angles. Its
Lean surface is A-L (`SOSignaturesLunar.lean`); the original-frame declarations remain valid (the
landed `soHamExpr`, `soHamExpr_eval`, `soHamExpr_clock`; the design `soBarrier_of_cert`) but are not
on the headline route.

- **Change of variables.** `L : (Q₀, Q₁, P₀, P₁) ↦ (q, φ, p, J) = (Q₀ + Q₁, Q₁, P₀, P₁ − P₀)`
  (`soRotMap`; inverse `soRotMapInv`). Angle block `A = [[1, 1], [0, 1]]`, action block
  `B = [[1, 0], [−1, 1]]`, `AᵀB = I`: linear, symplectic (`soRotMap_symplectic`) and unimodular, so
  `ℤ²`-periodicity, primarity and reality are preserved and `X_{H∘L} = L⁻¹ X_H ∘ L`
  (`hamiltonianVectorFieldℂ_soRotHC`).
- **Hamiltonian.** `H' = soHC ∘ L = P₀²/2 − P₀ + P₁ + V(Q₀ + Q₁, Q₁)`, i.e.
  `soRotHamExpr = P₁ + (P₀²/2 − P₀) + Σ_{m=1}^{7} (−ε A_m) cos 2π(2Q₀ + (2 − m)Q₁)` (modes
  `(2, 2 − m)`; the `m = 2` mode does not depend on `Q₁`), division-free, `soRotHamExpr_eval`
  against the landed `soHC`, clock `∂_{P₁} H' ≡ 1` (`soRotHamExpr_clock`, direction `inr 1`). R1's
  time scale `c = 237/125` (SO-GEN2, measured; Revision 5 projected `7/4`) enters as `soRotHamExprScaled c = c · H'` (clock
  derivative `c`); `invarianceError_const_mul` moves an exact torus of `c·H'` at `s∞ ω*` to one of
  `H'` at `(s∞/c) ω*`.
- **Frequencies.** `ω*± = κ (ν± − 1, 1)` with `κ = c/s` (`lunarRotFreq`), so the candidate's torus
  frequency is `s ω* = c (ν± − 1, 1)` and the clock gives `s∞ = s`. Exact `ℚ(√5)` instances
  `lunarRotFreq{Minus,Plus}_eq` with coefficients `[[∓79κ/3118, ±κ/3118], [κ]]` feed the landed
  `algFreq_encloses` (box radius `≤ 10⁻¹¹⁰` as before). Diophantine (SO-ROTDIO, signatures fixed by
  the orchestrator and adopted verbatim): `isDiophantine_of_index_map` with `T k = (k₀, k₁ − k₀)`,
  `C = 2` (`|k₀| + |k₁ − k₀| ≤ 2|k|₁`) applied to the landed SO-DIO gives
  `lunarNu±_rot_isDiophantine : IsDiophantine (1/42) 1 ![ν± − 1, 1]` (and `1/84` for the half
  vectors, unused by R1), and scaling by `κ` gives
  **`IsDiophantine (κ/42) 1 ω*±`** (`soIsDiophantine_smul`, `lunarRotFreq{Minus,Plus}_isDiophantine`).
  The constant is `κ/42 = 316000/7000007 = 79/(1750 s)` at R1 (Revision 6) (CONSTANTS-STUDY: numerical infimum
  `α = 0.02462` at `k = (1, 0)`, proved `1/42`, −1.20 orders against `1/21`).
- **Parameter package R1** (`lunarR1 err disp`, rationals): `n = 2`, `τ = 1`, `ρ = 1/70`,
  `ρ∞ = 1/70000`, `μ = 1/160`, `M = σK = σB = σT = 1987/1000` (= 𝔪, Revision 6: SO-GEN2's
  certified majorants; binding `σB − μ ≥ 1.97994`, the weighted-ℓ¹ Gram inverse; also `M ≥ c·M₁ =
  1.98625`, `σK − μ ≥ 1.3604`, `σT − μ ≥ 1.0225/c`), `σω = 2`, `ν = 10⁻⁶`, `s = 1 + 10⁻⁶`,
  `γ = γ̄ = κ/42`, `E₀ = 0`, time scale `237/125`. Ray margins: `ν ≤ (s − 1)‖ω*‖` and
  `ν ≤ (σω − s)‖ω*‖` hold with `‖ω*‖ = κ ≈ 1.896`. Enclosed threshold `10^{−74.669}` (both tori; the
  Revision 5 projection was `10^{−74.51}` at `𝔪 = 39/20`, `c = 7/4`). SO-GEN2 measured, at `L = 88`
  (318 bits): `c·η = 2.010e-78 / 3.919e-78`, chosen `e± = 4.03e-78 / 7.84e-78`, smallness
  `C₁e/(γ⁴ρ⁴) = 1.9e-3 / 3.7e-3`; minimum feasible `L = 86`. `err` and `disp` per torus are named
  placeholders (`lunar{Lower,Upper}{Err,Disp}`); SO-GEN2 regenerates the candidates in this frame and
  encloses the norms before anything is frozen (O5).
- **Candidate.** `K' = (ψ + u, φ, p, P̃₁)` with `U = (u/2π, 0)`, `angleDeg = −1`, primary, keys
  `(2, 2 − m)`. `D` (SO-GEN2, Revision 6): `T_{ρ_H}` with `ρ_H = 257/10000`, times the `P₀` disc
  `48769/50000 ± 191/12500` (upper torus `51231/50000 ± 1529/100000`) and the `P₁ = p + J` disc
  `24983/50000 ± 127/20000`. **One character witness** `E ≈ exp(2iv)` serves all seven keys (normalized
  index `k·U = 2U₀`); its pin is `exp(2iv(0)) = 1` exactly (`v` odd), so **`pinHalvings = 0`**,
  `pinOrder = 1`, `ε₀ = 6.0e-88 / 2.9e-87`. The Gram inverse is certified by the designed weighted-ℓ¹
  row sums of a Fourier approximate inverse with a Neumann check (`δ = 2.48e-12`, `‖G⁻¹‖ ≤ 1.97994`);
  this, not the projected sup ≈ 1.83, sets `𝔪 = 1987/1000`. A grid-sup sub-check (maximum principle on
  the distinguished boundary, `4096 × 1024` grid, Lipschitz remainder) would give `1.8347` and package
  R1grid (`c = 1757/1000`, `𝔪 = 1841/1000`, `10^{−73.588}`); it is **not adopted** (orchestrator
  decision, 15:06) and is recorded as a possible later improvement. **Torsion witness:** the average is
  ≈ `[[1.12148, 0, −0.02462], [0, 0, 1], [−0.02462, 1, 0]]`; its `T` block is nearly singular
  (`T₁₁ ≈ 0`, `T₀₁ ≈ 1e-15`) and invertible only through the border, so the `3 × 3` witness `S` is
  computed in exactly the bordered form (`δ_T = 5.7e-11 / 8.0e-11`, `‖avg⁻¹‖ ≤ 1.022493` at `c = 1`);
  `torsionAvgCheck` already inverts the full bordered `(n+1) × (n+1)` matrix, so nothing changes.
- **Gate G-J restated (rotated, time-scaled; SO-GEN2 fills every named number).** Let
  `P₁⁰ = −(P₀²/2 − P₀) − V(Q₀ + Q₁, Q₁)` (the exact energy lift at `E₀ = 0`) and `ΔP₁ = P̃₁ − P₁⁰`
  (finite Fourier data). Exactly, `c·H'(K̃) − E₀ = c ΔP₁`. `H'` is affine in `P₁` with `∂_{P₁} H' ≡ 1`
  and its other partials independent of `P₁`, so `X_{cH'}(K̃) = X_{cH'}(K₀)` and
  `E(K̃) = E(K₀) − (0, 0, 0, D_{sω*} ΔP₁)`, `sω* = c(ν − 1, 1)`. Under the scalar pilot identities
  `E(K₀) = c·(0, 0, −r, (p − 1) r)` (CONSTANTS-STUDY §2.2); in general only the difference formula and
  the actual full residual apply. Budgets on `T_{1/70}`:

  | Name | Definition | Target |
  |---|---|---|
  | `e±` | residual budget of the lower/upper torus (`lunar{Lower,Upper}Err`) | `isoC1Q e < γ⁴ρ⁴` (projected `e < 10^{−74.5}`; size the truncation with 2 orders headroom) |
  | `B_r` | `sup |E(K₀)_{P₁}|` (`= c sup|(p − 1) r|` under the pilot identities) | `B_r + B₁ + B_c ≤ e/2` |
  | `B₁` | `sup |D_{sω*} ΔP₁|` | (with `B_r`) |
  | `B_q` | `sup` of the `Q₀, Q₁, P₀` rows of `E(K₀)` (`= c sup|r|` in the `P₀` row under the identities) | `B_q + B_c ≤ e/2` |
  | `B_c` | every other candidate-replacement error (Fourier `Q, P₀` data versus the scalar embedding, rounding, truncation) | as above |
  | `B₀` | `c · sup |ΔP₁|` | `B₀ ≤ e/4` (energy) |
  | `B₂` | `max(sup|∂ΔP₁|, sup|∂²ΔP₁|)` | **withdrawn (Revision 6)**: every norm (DK, Gram, torsion) is enclosed on the actual `K̃` including `J̃`; measured `8.1e-75 / 1.6e-74` |

  **SO-GEN2's measured G-J (Revision 6, package R1):** `B₀ = 1.25e-80 / 2.29e-80 ≤ e/4`;
  `B₁ = 5.22e-79 / 8.62e-79`, `B_r = 6.8e-80 / 1.3e-79`, `B_c = c·η_{Q₀} = 4.3e-88 / 8.9e-88`, with
  `B_r + B₁ + B_c ≤ e/2`; the `Q₀, Q₁, P₀` rows plus `B_c` are `≤ e/2`, which is why **`e ≈ 2·c·η`**
  (the direct `P₁`-row enclosure is `c·η₄ = 5.6e-79 / 9.7e-79`). The gate passes.

  SO-GEN2 also reports every sub-check margin on `K̃` by its exact evaluator (invariance, energy, `DK`,
  ball, Gram `δ`, torsion `δ_T`, smallness, graph `mono`, `p` range), every character pin's
  `pinHalvings`, `pinOrder` and `ε₀` (Revision 4), and the R1 majorants it certifies. These are
  feasibility targets only: the checker recomputes the actual full residual.
- **Clock** (landed `clock_frequency`): applied to `H'` at `(s∞/c) ω*` (`soRotHamExpr_clock`), it gives
  `(s∞/c) ω*₁ = 1`, hence `s∞ = s`, and `Q₁ = θ₁ + c₀` on reals.
- **Graph** (`soBarrier_of_exact_rotTorus`, on the landed SO-GRAPHM core). On the real torus,
  `Q₀(x, y) = x + u` and `P₀ = p`; the Hamilton equations of `H'` (from `X_{H∘L} = L⁻¹X_H∘L`) give
  `d/dt Q₀ = P₀ − 1`, `d/dt P₀ = −∂_qV(Q₀ + Q₁, Q₁)` along `(x + t(ν − 1), y + t)`. The shear
  `(x, y) ↦ (x − y, y)` (`SoGraph.torus_of_rot`) yields the core's data with `Q = Q₀ + Q₁ = q`,
  frequency `(ν, 1)` and the same monotonicity `∂_x Q = ∂_{θ₀} Q₀ ≥ m`; `soBarrier_of_torus` then gives
  the continuous doubly periodic barrier `p = P(q, φ)`. The certificate side is frame-free:
  `checkSoGraph` bounds `∂_{θ₀}` of component `.1 0` (`Q₀` here) from below with a paid SOS residual
  and transfers it by Cauchy on `T_{ρ∞}` (needs `mono > disp/ρ∞`; with `ρ∞ = 1/70000` the margin is
  `disp · 70000`, which SO-GEN2 must report), and bounds component `.2 0` (`P₀ = p`).
- **Barrier and final theorems** (unchanged). `so_confinement` (landed SO-CONF) and the final
  `lunar_barriers`, `lunar_spin_confinement` (`|p(t) − 1| ≤ 33/1000`, window O1): the map back to
  `(q, p, φ)` is built into `soBarrier_of_exact_rotTorus` (`q = Q₀ + Q₁`, `p = P₀`, `φ = Q₁`), so the
  final statements do not mention the frame. `lunarPLo`, `lunarPHi` become literal rationals before the
  freeze (O1).

*Historical (Revisions 1–4, original frame, superseded on the headline route):* `soHamExpr` with
`ω* = (ν±/2, 1/2)`, `s = 2`, `ρ = 1/200`, `ρ∞ = 1/400`, `μ = 1/1000`, `M = σK = σB = σT = 4`, `σω = 3`,
`γ = γ̄ = 1/42`, `e ≈ 10⁻¹⁰³`; the G-J of Revision 3 (`E(K̃)_J = E(K₀)_J − D_{sω*}ΔJ`). The four-component
argument is the same in both frames.

## 7. Modules, import DAG and packages

All paths are new unless marked landed (status at `inp` `f8405551`). Every file is < 1500 lines
(target ≤ 800). `→` means "imports".

```
Certificate/PhaseBasis, Clock                  (landed, SO-CLOCK)
Certificate/Arith/{PiHigh,Interface,PiEnclosure,Roots,Transcendental,Rat,ComplexExp}   (landed)
Certificate/Arith/Fixed                        (landed, SO-ABK)    → Arith/Interface
Certificate/Arith/Mantissa                     (post, SO-POLY-A)   → Arith/Interface (mantCheck, ofDyadic)
Certificate/Freq, QuadraticDiophantine, CubicDiophantine           (landed)
Certificate/Poly/Basic, Model/Basic            (landed, SO-PBASE)
Certificate/Poly/Packed                        (post, SO-POLY-A/B) → Arith/Mantissa, Poly/Basic, Model/Basic
Certificate/Poly/Ops                           (post, SO-POLY-B)   → Poly/Packed
Certificate/Model/Ops                          (post, SO-MALG)     → Model/Basic, Poly/Ops, Arith/PiEnclosure
Certificate/Model/{Exp,Inv}                    (post, SO-EXPW)     → Model/Ops, Arith/ComplexExp
Certificate/Expr/{Basic,Slp,Diff*}             (landed, SO-EXPR-A/B1; B2 `jet_d3` pending)
Certificate/Expr/Ball                          (pre, SO-BALL)      → Expr/Slp, Model/Basic, Arith/{Rat,ComplexExp}
Certificate/NormBridge, MatrixInv, Constants   (landed)
Certificate/Embedding, Expr/Compose            (post, SO-EMB)      → Poly/*, Model/{Ops,Exp,Inv}
Certificate/Gram                               (post, SO-MAT)      → Model/Ops, MatrixInv, Embedding
Certificate/Torsion/{Frame,Models}             (post, SO-TORS)     → Gram, Expr/Compose, Freq
Certificate/Positivity                         (post, SO-POS)      → Model/Ops
Certificate/Defs                               (post, SO-DEFS)     → all of the above
Certificate/Sound/{Static,Ham,Embedding,Invariance,Energy,Gram,Torsion,Smallness} → Defs, NormBridge
Certificate/Soundness                          → Sound/*, Iso/Apost/G1
Certificate/Tests/{Toy2,Toy3,Rat,Negative,Packed}  → Soundness, CubicDiophantine, QuadraticDiophantine
SpinOrbit/{Model,PeriodOne,Hamiltonian,ScalarEmbedding,HamExpr,Freq,Barrier,Graph/Inverse} (landed)
SpinOrbit/Rotated                              (pre, SO-ROT)       → SpinOrbit/HamExpr, Clock
Certificate/DiophantineTransfer                (pre, SO-ROTDIO, proving) → QuadraticDiophantine
SpinOrbit/RotFreq                              (pre, SO-RFREQ)     → Freq, DiophantineTransfer
SpinOrbit/Graph/Rot                            (pre, SO-GRAPHR)    → Graph/Inverse, Rotated
SpinOrbit/Graph/Cert                           (post, SO-GRAPH)    → Soundness, Positivity, Graph/{Inverse,Rot}
SpinOrbit/Data/{Lower,Upper}/{Emb,Wit,Adv/*}   (post + G-J, generated, §7.2) → Defs
SpinOrbit/Lunar{Lower,Upper}Passes             → Data, Defs      (decide +kernel per sub-check / shard)
SpinOrbit/LunarConfinement                     → all SpinOrbit
```

`lunarR1` (a `CertParams`) needs `Defs`; SO-RFREQ therefore splits into `RotFreq` (pre-gate: frequency,
`ℚ(√5)` instances, `κ`-scaled Diophantine from SO-ROTDIO) and `LunarParams` (post-gate, 60 lines, with SO-LUNAR). No module
imports a provider or a frozen theorem anchor.

**Gate.** The replay gate is **GO** (Revision 5); post-gate packages may be briefed in DAG order with
the §5 product architecture. SO-DATA additionally waits for gate **G-J** (§6) and for the owner's
packaging decision (§7.2).

| Package | Gate | Modules | Lines (est.) | Inputs |
|---|---|---|---|---|
| SO-CLOCK | landed | PhaseBasis, Clock | (400, done) | — |
| SO-PI | landed | Arith/PiHigh | 500 | — |
| SO-CONST | landed | Constants | 700 | SO-PI |
| SO-AIF | landed | Arith/{Interface,PiEnclosure,Roots,Transcendental,Rat} | 700 | SO-PI |
| SO-CEXP | landed | Arith/ComplexExp, Tests/ComplexExp | 150 | SO-AIF |
| SO-FREQ | landed | Freq, SpinOrbit/Freq | 350 | SO-AIF |
| SO-DIO3 | landed | CubicDiophantine | 350 | SO-FREQ |
| SO-PBASE | landed | Poly/Basic, Model/Basic | 800 | SO-AIF |
| SO-EXPR | A, B1 landed; B2 pending | Expr/{Basic,Slp,Diff*} | 1700 | SO-PBASE |
| SO-BALL | pre (in audit) | Expr/Ball | 500 | SO-EXPR, SO-AIF, SO-CEXP |
| SO-NORM | landed | NormBridge | 400 | — |
| SO-MINV | landed | MatrixInv | 300 | — |
| SO-HAMX | landed | SpinOrbit/HamExpr | 200 | SO-EXPR |
| SO-CONF | landed | SpinOrbit/Barrier | 600 | — |
| SO-GRAPHM | landed | SpinOrbit/Graph/Inverse | 600 | SO-CONF |
| **SO-ROT** | pre (new, R5) | SpinOrbit/Rotated | 300 | SO-HAMX, SO-CLOCK |
| **SO-ROTDIO** | pre (orchestrator, proving) | Certificate/DiophantineTransfer | 150 | SO-DIO |
| **SO-RFREQ** | pre (new, R5) | SpinOrbit/RotFreq | 100 | SO-FREQ, SO-ROTDIO |
| **SO-GRAPHR** | pre (new, R5) | SpinOrbit/Graph/Rot | 300 | SO-GRAPHM, SO-ROT |
| SO-ABK | landed | Arith/Fixed | 500 | SO-AIF |
| **SO-POLY-A** | post (R5) | Arith/Mantissa, Poly/Packed (packing, injectivity, Kronecker, shards, slot decoding) | 550 | SO-PBASE, SO-ABK |
| **SO-POLY-B** | post (R5; R6 +100) | Poly/Packed (layout, advice, anti-carry guards `reconFits`/`shardFits`/`shapeOK`, `shard_reconstruct`, `checkPackedProduct`, `toMants`, `mulPacked` glue), Poly/Ops | 700 | SO-POLY-A |
| SO-MALG | post | Model/Ops (`ModelConfig α`, advice lookup, fallback) | 750 | SO-POLY-B |
| SO-EXPW | post | Model/{Exp,Inv} | 850 | SO-MALG, SO-CEXP |
| SO-EMB | post | Embedding, Expr/Compose | 830 | SO-EXPW, SO-EXPR |
| SO-MAT | post | Gram | 630 | SO-MALG, SO-EMB, SO-MINV |
| SO-TORS | post | Torsion/{Frame,Models} | 1040 (two packages) | SO-MAT, SO-EMB, SO-FREQ |
| SO-POS | post | Positivity | 350 | SO-MALG |
| SO-DEFS | post | Defs | 600 | all of the above |
| SO-SOUND | post | Sound/*, Soundness | 1400 (A 700; B 700) | SO-DEFS, SO-TORS, SO-NORM, SO-BALL |
| SO-TEST | post | Tests/{Toy2,Toy3,Rat,Negative,Packed} | 450 | SO-SOUND, SO-DIO3 |
| SO-GRAPH | post | SpinOrbit/Graph/Cert (both frames) | 500 | SO-SOUND, SO-POS, SO-GRAPHR |
| SO-DATA | post + G-J + §7.2 | generator and advice emitter (Python), Data shards (generated), hand-written assembly 150 | 150 + generated | SO-GEN2, SO-DEFS, SO-POLY-B |
| SO-LUNAR | post | LunarParams, Lunar*Passes, LunarConfinement | 400 | all |

**Totals (Revision 5; landed packages still counted at their estimates for comparability).**
- Pre-gate: Revision 4's 7,850 + SO-ROT 300 + SO-ROTDIO 150 + SO-RFREQ 100 + SO-GRAPHR 300 = **8,700**.
- Post-gate: Revision 4's 8,650 + SO-POLY 500 + SO-MALG 100 + SO-EMB/MAT/TORS 100 + SO-GRAPH 100 +
  SO-DATA glue 150 = **9,600**.
- Revision 6: SO-POLY-B +100 (the anti-carry guards and reconstruction), post-gate **9,700**, total
  **18,400**.
- Hand-written total (Revision 5) **18,300**; with wave 0 and SO-CLOCK, about 20,200. With a 30–40% overrun on the
  18,300: 23.8k–25.6k new lines, about 25.7–27.5k overall, inside the plan's 21–37k.

The estimate risks (third-order jets, fixed-point error accounting, the complex path argument, torsion
derivative models, graph inversion) now include the packed-product glue (layout bijection, overlap-add
of shard windows, complex splitting).

### 7.2 Certificate data packaging (SO-REPLAY2 design signal; OWNER decision)

The owner's hard rule caps every Lean file at 1500 lines. The repository lint additionally caps lines at
100 characters (generated `KAM.lean` and `.drafts` excepted). The data that must enter Lean is, per
torus: the embedding and witnesses (`K̃` in four components, exp/character/reciprocal witnesses, the
Gram witness), and the product advice of every checker product (design B).

**Counts at the R1 scale** (CONSTANTS-STUDY §2.3 and SO-REPLAY2's model; ±30%):

| Quantity | 1e-130 data (SO-REPLAY2) | R1 (`L ≈ 87`, about 299 bits) |
|---|---:|---:|
| `E` terms per factor | 18.7k | 8.1k |
| slot width `w` | 896 | 614 |
| in-box advice slots per real product | 65k | ≈ 28k |
| decimal digits per slot / hex digits | 133 / 110 | 90 / 75 |
| advice source per real product | 8–9 MB | ≈ 2.6 MB (decimal) / 2.2 MB (hex) |
| per torus, 30 real products | ≈ 260 MB | ≈ 66–78 MB |
| per torus, 120 real products (complex ×4) | ≈ 1 GB | ≈ 260–310 MB |
| embedding and witnesses per torus | — | ≈ 5–10 MB |
| elaboration at ≈ 18 s/MB, per torus | 1.3 h (30) | 20–25 min (30) / 1.3–1.6 h (120) |
| kernel, per torus | 0.75–1.5 CPU-h (30) | ≈ 0.3–0.5 CPU-h (30; 0.35× pairs) |

Both tori double the volumes. The number of real products per torus (30 to 120) is SO-GEN2's to report;
it is the dominant uncertainty.

**Lean shape, common to all options.** Data are `noncomputable def`s of at most 32 rows (≤ 4096 flat
elements) each, the elaborator limit SO-REPLAY2 measured; big literals are chunked (2^14 bits) because
hex parsing is quadratic; each shard's check is its own theorem `checkShard adv A B s = true` by
`decide +kernel`, and the passes modules combine them. No recursion-depth or heartbeat override.

**Options (not decided here):**

| Option | What | Files at R1 (both tori) | Rule/lint status | Costs and risks |
|---|---|---|---|---|
| **A. Lint-clean chunked modules** | One coefficient per line (90 decimal or 75 hex digits fit in 100 columns), ≤ ~1,450 data lines per file, generated directories `KAM/SpinOrbit/Data/{Lower,Upper}/Adv/P<k>/S<j>.lean` | ≈ 1,000–4,800 | Fully compliant, no exemption | Very many modules (import graph, Lake overhead per module of a few seconds); precision above ≈ 95 digits would need limb splitting (`a·10^k + b`, one more kernel step per slot) |
| **B. Line-width exemption for generated data** | Same files ≤ 1500 lines, but long lines (e.g. 4 KB, ≈ 45 coefficients) in an exempted directory; the lint keeps the 1500-line check everywhere | ≈ 25–105 | Needs an owner exemption of the 100-column lint for `KAM/SpinOrbit/Data/**` only (the 1500-line hard rule is untouched) | ≈ 6 MB and ≈ 2 min elaboration per file, memory per file higher; reviewers cannot read the data anyway |
| **C. Out-of-tree data** | Data in non-Lean files (hex text), read at elaboration time by a small meta-program that builds the same `noncomputable def` terms (`include_str` plus a parser, ≈ 200 lines) | ≈ 30 Lean modules + data files | No Lean file is large; the lint and the 1500-line rule do not apply to data files | The kernel still checks every term, so soundness is unaffected, but a meta-program enters the build path and Lake must track the data files as dependencies; provenance of non-Lean data must be audited |

Volume levers independent of the choice: hex instead of decimal (−17%); design B rather than A (≈ 8×
less than shipping `T_s`); SO-GEN2 sizing the truncation to the threshold (R1) rather than 1e-130
(about 3.5× less volume per product). If the volume is still unacceptable, the owner's recorded
fallback is the sharper theorem (HL19 torsion route plus Parseval, about 1e-52, 3–4k lines).

## 8. Validation plan

- **Positive toys with the external premise discharged (F4, F1):**
  - **T2**: `H = J + p²/2`, `K = (θ, (ν̃, −ν̃²/2))`, rational `ν̃` with `|ν̃ − ν₋| ≤ 10^{−N}`, reference
    vector `(ν₋/2, 1/2)` (SO-DIO), `s = 2`, `err ≥ |ν̃ − ν₋|`, positive. Result: `toyCert2_torus`.
  - **T2d**: T2 with `H = J + (p²/2)·((3 + cos 2πq)/(3 + cos 2πq))`, which exercises `div`, balls and a
    reciprocal witness. Result: `toyCert2d_torus`.
  - **T3** (`n = 3`, `τ = 2`): `H = I₂ + I₀²/2 + I₁²/2`, `K = (θ, (a, b, −(a² + b²)/2))` with rational
    `a ≈ ∛2`, `b ≈ ∛4`, `ω* = cubicFreq` (`IsDiophantine (1/12) 2`, norm-form proof), positive residual.
    Result: `toyCert3_torus`.
  - `N` is fixed by `isoC1Q` at the toy's `(n, τ, ρ)`; SO-TEST computes it, and rationals of any size are
    cheap.
- **Checker-only test TR** (labelled: no Diophantine premise). Exact rational `ν = 1/2`, zero error,
  resonant vector `(1/4, 1/2)`. Only `toyRatCert_passes`.
- **Negative tests** (`checkTorusCertificate c = false` by `decide +kernel`, each failing in its intended
  sub-check):
  1. a false residual bound fails `checkInvariance`;
  2. Gram witness `B = 0` or `δ ≥ 1` fails `checkGram`, and an invalid torsion witness fails
     `checkTorsion`;
  3. `μ = 0` fails `checkStatic`;
  4. an exp witness with a wrong mean fails the pin;
  5. `w < e^{2πρ}` fails `checkWeight`;
  6. **(O2)** a division whose denominator ball contains `0` on `D` fails `checkHamBounds`, and a
     reciprocal witness with `δ ≥ 1` fails composition;
  7. **(F1)** a box that does not exclude `0`, or that violates a ray margin, fails `checkStatic`;
  8. **(O3)** a `PiEnclosure` narrower than the Machin bounds fails `checkPiEnclosure`;
  9. **(F7)** at `n = 1`, a torsion model matrix or witness `S` with `3` rows (or a row of length `≠ 2`),
     e.g. the audit's self-inverse `A = [1 0 0; 0 0 1; 0 1 0]`, fails `torsionAvgCheck 1` and hence
     `checkTorsion`, although `A` is a valid inverse pair with zero defect.
  10. **(F10)** a character witness whose pin `exp(2πi k·U(0))` has `|2π k·U(0)| > 1` and `pinHalvings = 0`
      (rounded reduced ball fails `certCExpSmall`) fails `Slp.compose`, hence `checkTorusCertificate`;
      the same certificate with a sufficient count passes that pin.
- **Range-reduction tests (F10, SO-CEXP `Tests/ComplexExp`, A §J):** `cexpTest_zero_small` (`s = 0`, small
  ball, success), `cexpTest_zero_large` (`s = 0`, `‖z‖ + r = 3/2`, `none`), `cexpTest_two_rejected` /
  `cexpTest_two_reduced` (the audit's `z = 2`: `none` at `s = 0`, success at `s = 2`), `cexpTest_large_pin`
  (`19i`, `s = 5`). Each success is paired with `certCExpReduced_sound` (radius contains `exp`).
- **Ball test 11 (F10, SO-BALL):** `Slp.balls` on `.exp (.const 2)`, on `exp` of a cosine mode with ball
  radius `> 1`, and on `cos` of a large action ball returns `some` (count `cexpHalvings`) and its
  `exp`-slot ball contains the exact value.
- **Packed products (Revision 5, SO-POLY, `Tests/Packed`).** Positive: a small 2-D product (both
  `n = 2` and `n = 3` layouts) with correct design-B advice passes `checkPackedProduct`, and
  `CertPoly.mulPacked` returns `some`; a multi-shard product (three blocks per factor) exercises the
  overlap-add. Negative (each `= false` by `decide +kernel`): an advice slot off by `+2` (SO-REPLAY2's
  control); an advice that is correct modulo `2^w` but violates the slot bound (injectivity is
  essential); a layout whose stride wraps (`compat = false`); a mantissa decoder returning a wrong
  integer (`mantCheck` rejects, and `CertModel.mul` falls back: a certificate relying on that product
  then fails its margin); a missing key. Model level: `CertModel.Encloses.mul` on the packed route and
  on the fallback.
  **Revision 6 (audit 5).** P2 (F12): audit 5's carry-cancelling advice: radix `2^4`, `scale = 1`, factors
  `[0, 0]`, advice `[16, −1, 0]` (`packSum 4 [16, −1, 0] = 0`, so the packed residual is zero) is rejected
  by `reconFits` (`2(2·16 + 1) = 66 ≥ 16`), hence by `checkShard` and `checkPackedProduct`
  (`packSum_audit5_cancel` and `reconFits_audit5_rejects` are already proved by `decide` in A-E; the
  whole-product test is SO-TEST's). P3 (F13, positive): a multi-shard product at `scale ≥ 1` whose
  target slot receives two overlapping windows, each error `2^(scale−1)`, passes, with combined error
  `= 2^scale` (the bound is attained). P4 (F13, negative): audit 5's blocks `A₀ = [1,1], A₁ = [0,0]`,
  `B₀ = [1,1], B₁ = [1,0]` at `scale = 0`, `w = 8`, advice `[1,2,0], [0,1,0], [0,0,0]`, fails
  `checkPackedProduct` (`checkPackedProduct_scale_zero`), although each window meets `2^(0−1) = 1`.
- **Rotated client (Revision 5).** `soRotHamExpr_eval`, `soRotHamExpr_clock`, the two
  `lunarRotFreq*_eq` and `*_isDiophantine` are proved outright (no data). T2 is restated in the rotated
  frame as a second positive toy (`H = c(P₁ + P₀²/2 − P₀)`, `K = (θ, (ν̃, ν̃ − ν̃²/2))` with
  rational `ν̃ ≈ ν₋`, reference `lunarRotFreq ν₋ κ`), so `soRotBarrier_of_cert`'s hypotheses are
  exercised before SO-DATA.
- **Axiom audit.** `#print axioms` of `checkTorusCertificate_sound`, every `*Passes` and `*_torus` theorem
  and the two lunar theorems shows only `propext`, `Classical.choice` and `Quot.sound`.
- **Cross-check.** SO-GEN's exact evaluator recomputes every sub-check margin from the same data (gate
  G-J).

## 9. Elaboration of Appendix A

Commands (gated, `LEAN_NUM_THREADS=1`, one process at a time):

```
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-so .drafts/design/SOSignaturesLunar.lean
python3 -I docs/tracks/SO/design/check_so_standins.py \
  .drafts/design/SOSignatures.lean .drafts/design/SOSignaturesLunar.lean
```

Result on Revision 6 (shared build of `inp` `074bd0c5`): engine **exit 0, 125 warnings, all
`declaration uses 'sorry'`, no error** (1152 lines; the two F12 controls are proved by `decide`);
lunar client **exit 0, 54 warnings, all `declaration uses 'sorry'`, no error** (540 lines); stand-in
check **PASS** (20 stand-ins verbatim, no line over 100 characters).

*Historical:* Result on Revision 5 (shared build of `inp` `f8405551`): engine **exit 0, 110 warnings, all
`declaration uses 'sorry'`, no error** (1049 lines); lunar client **exit 0, 54 warnings, all
`declaration uses 'sorry'`, no error** (539 lines); stand-in check **PASS** (20 engine stand-ins
verbatim, no line over 100 characters). This establishes elaboration only.

The engine imports every landed SO module and no longer restates any of them (Revision 4 restated
about 540 lines of landed declarations; the warning count fell accordingly). The lunar file imports
the landed client modules (`SpinOrbit/{Model,Hamiltonian,HamExpr,Freq,Barrier,Graph/Inverse}`,
`Certificate/{Clock,Freq,QuadraticDiophantine,Arith/Fixed}`) and restates only the 20 unlanded engine
declarations it names and SO-ROTDIO's 5 fixed declarations (verbatim from the orchestrator's brief).

*Historical:* Revision 4: exit 0, 174 warnings, 1494 lines, single file, with stand-ins for SO-PI and
SO-CLOCK (both landed since); Revision 3: 156 warnings, 1360 lines; Revision 2: 156, 1337 lines.

## 10. Risks

| Risk | Signal | Response |
|---|---|---|
| Kernel replay too slow or too deep | SO-REPLAY; a stage needs an override | shard with `List.all`; fixed point; sharper `n = 2` constants (plan lever); never an override |
| Ball arithmetic on `D` exceeds `M = 4` | `checkHamBounds` margin | per-coordinate radii, smaller `ρ_H`; the pilot majorant 2.69 leaves room |
| Witness pin radius dominated by `e^{2B}` | `checkInvariance` margin | halving rewrite `exp a ↦ (exp(a/2))²` |
| Reduced pin radius amplified by `s` squarings (`≈ 2^s |exp|` relative) | `ε₀` vs residual budget | per-witness `pinHalvings` (minimal `s`), higher `pinOrder` and pin precision; SO-REPLAY item 7 |
| `B_r + B₁ + B_c` exceeds `e/2` | gate G-J | raise the SO-GEN truncation threshold for `J̃`; `J̃` is cheap (no witness) |
| Gram/torsion witnesses weak | `δ`, `δ_T` near 1 | Fourier-model `B`; Newton-refined `B` from the generator |
| Toy T3 constants (`n = 3`, `τ = 2`) huge | `isoC1Q` | larger `N` (rational size only), larger `ρ` (the toy is entire) |
| Coarse balls for a division client | inv fails on `D` | smaller `D`, or split the denominator's constant part |
| Jet size for large `n` | elaboration/replay | order-3 slots only on `D`, never composed; pruning |
| Data volume (§7.2) unacceptable even with the chosen packaging | SO-GEN2 product count × 2.2–2.6 MB | hex, truncation sized to the threshold; else the sharper theorem (owner fallback) |
| Packed glue (layout bijection, overlap-add, complex split) longer than estimated | SO-POLY-B overrun | split `Poly/Packed` into layout and glue modules (each < 1500 lines) |
| `mono > disp/ρ∞` at `ρ∞ = ρ'/1000` | graph margin | `disp ≈ C₂e/(γ²ρ²)` is tiny at `e < 10^{−74}`; SO-GEN2 reports the margin; raise `ρ∞` if needed (costs ≈ 4.8 orders per ×1000) |
| R1 majorants not certified | SO-GEN2 enclosures | **resolved (Revision 6):** certified at `𝔪 = 1987/1000`, `c = 237/125`, `10^{−74.669}`; R2 not needed |

## 11. Owner rulings and open points

- **O1** (constant momentum window): adopted (§6). Graph-error transport is deferred.
- **O2** (division in v1): adopted (§1.1, §1.4, §1.7, A-E §C/§D).
- **O3** (SO-PI now): adopted; SO-PI has landed.
- **O4** (analytic graphs and conjugacy later): adopted. They are outside the first freeze.
- **O5** (2026-10-29, 14:20: rotated frame, R1, replay gate GO): adopted in Revision 5 (§5, §6, §7).

Open for the owner:
1. **Data packaging (§7.2):** option A (lint-clean, about 1,000–4,800 files), B (a 100-column lint
   exemption for generated data only, about 25–105 files) or C (out-of-tree data read by an elaborator).
   The design does not choose.

- **Orchestrator decision 15:06** (Revision 6): SO-GEN2's grid-sup Gram sub-check is not adopted;
  a possible later improvement (about one order of threshold).

Remaining items for the freeze: the literal rational window endpoints, `err`/`disp` per torus,
`soPrecision` (from SO-GEN2/SO-DATA).

## 12. Hard rules for every Lean brief (verbatim)

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat
   elaboration failure is a design signal to refactor or split the proof, not something to mask with a
   larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused
   modules, preserving public import paths as cheap facades.

Also: never use the identifier `EuclideanSpace`. Never use `native_decide`, `Lean.ofReduceBool`, `axiom`,
`admit`, `unsafe`, `opaque` or `implemented_by`. Every file is a Lean module. Run one Lean process at a
time, through the compile gate.

## Appendix A. Exact signatures

Since Revision 5 two files, each elaborating on its own (§9): **A-E**, the engine,
`.drafts/design/SOSignatures.lean`; **A-L**, the lunar client, `.drafts/design/SOSignaturesLunar.lean`
(copies at `/root/code/KAM-inp/.drafts/design/`). "A §X" in Revisions 2–4 refers to the single
Revision 4 file; its sections §A–§H, §J are in A-E, its §I is A-L.

### A-E. `SOSignatures.lean` (engine), verbatim

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Apost.G1
public import KAM.Strip.FourierSeries
public import KAM.Strip.Averages
public import KAM.Diophantine.SolverAlgebra
public import KAM.Matrix.Neumann
public import KAM.Matrix.Inverse
public import KAM.Torus.Basic
public import KAM.Certificate.Arith.Rat
public import KAM.Certificate.Arith.Fixed
public import KAM.Certificate.Arith.ComplexExp
public import KAM.Certificate.Arith.PiEnclosure
public import KAM.Certificate.Model.Basic
public import KAM.Certificate.Expr.Diff
public import KAM.Certificate.NormBridge
public import KAM.Certificate.MatrixInv
public import KAM.Certificate.Constants
public import KAM.Certificate.Freq
public import KAM.Certificate.Clock
public import KAM.Certificate.CubicDiophantine
public import KAM.Certificate.QuadraticDiophantine

/-!
# SO-DESIGN Revision 5: exact draft signatures, engine part (track SO)

Design document: `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (Appendix A is this file together with
`SOSignaturesLunar.lean`). Every proof and every non-trivial definition body is `sorry`: this
file only fixes the Lean surface. It is a transient elaboration check against the shared `inp`
build; it is never imported.

Revision 5 split the Revision 4 file (1494 lines) into this ENGINE file (the general checker and
its black box) and the LUNAR-CLIENT file `SOSignaturesLunar.lean`. Both elaborate on their own.
This file now IMPORTS every landed SO module instead of restating it (the Revision 4 file restated
them with `sorry` bodies); each section names the landed declarations it consumes.

Sections mirror the planned modules (§7 of the design):

* §A `Arith/*` (LANDED: interface, `ℚ` and fixed-point instances, transcendental bounds, SO-PI,
  `π` enclosure, roots, complex balls, small-ball and range-reduced complex exponential); new
  here: the mantissa check `mantCheck` (Revision 5, no change to the landed interface).
* §B `Poly/*`: exact finite Fourier data (LANDED `Poly/Basic`); exact shifts and reflections;
  §B′ `Poly/Packed` (Revision 5, item 6): Kronecker-packed, advice-checked products (SO-REPLAY2).
* §C `Model/*`: Fourier models (LANDED `Model/Basic`); model operations whose products are
  advice-checked (`ModelConfig α` carries the advice book); `exp` and reciprocal witnesses.
* §D `Expr/*`: the expression language, straight-line program and jets (LANDED `Expr/{Basic,Slp,
  Diff}`); ball arithmetic on the domain; the embedding; composition with `K`.
* §E `NormBridge` (LANDED).
* §F `{Gram,Torsion,Constants,Positivity}` (LANDED `MatrixInv`, `Constants`).
* §G `{Freq,Defs,Sound/*,Soundness}`: the certificate, the sub-check contracts, the black box
  (LANDED `Freq`).
* §H `Clock` (LANDED, imported). §J toys and tests (LANDED `CubicDiophantine`).
* The lunar client (former §I) is in `SOSignaturesLunar.lean`.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus

/-! ## §A. Certified arithmetic (`KAM/Certificate/Arith/*`)

LANDED and imported (SO-AIF, SO-PI, SO-RAT, SO-CEXP, SO-ABK): `CertArith`, `LawfulCertArith`,
`CC`, `CC.toC`, `CC.conj`, `CC.toC_conj`, `CC.toC_zero`; `instCertArithRat`,
`instLawfulCertArithRat`; `CertFixed`, `instCertArithFixed`, `instLawfulCertArithFixed`;
`ratExpUp`, `exp_le_ratExpUp`; `piLoQ`, `piUpQ`, `piLowRat`, `piUpRat`, `eLowRat`, `eUpRat` and
their bounds; `PiEnclosure`, `checkPiEnclosure`, `checkPiEnclosure_sound`; `checkRootEnclosure`,
`rpow_mem_of_checkRootEnclosure`, `sqrt_mem_of_checkRootEnclosure`; `CertBall`, `CertBall.Mem`,
`CC.normUp`, `CertBall.ofRat`, `CertBall.times`, `CertBall.mem_ofRat`, `CertBall.mem_times`;
`certCExp`, `certCExpSmall`, `certCExpSmall_sound`, `certCExp_sound_of_small` (the unrestricted
`certCExp_sound` stays WITHDRAWN, Revision 4); `certCExpReduced`, `certCExpReduced_sound`.

Revision 5 needs NO change to the landed interface: the packed products of §B′ read integer
mantissas through a certificate-supplied decoder (`ModelConfig.toMant`), and every decoded
mantissa is re-verified by `mantCheck` with the interface's own `beq`, `ofRatUp`, `ofRatDown`. -/

open CertArith

-- Backend 2, the production backend (SO-REPLAY): `CertFixed P`, `instCertArithFixed`,
-- `instLawfulCertArithFixed` are LANDED (`Arith/Fixed.lean`, SO-ABK, `inp` 57b274bd).

/-- A mantissa claim `val a = z / 2^P`, tested with the backend's own outward conversions and
equality test. Law-free; its soundness needs only `LawfulCertArith` (`beq_sound`, `ofRatUp_ge`,
`ofRatDown_le`). -/
def mantCheck {α : Type} [CertArith α] (P : ℕ) (a : α) (z : ℤ) : Bool :=
  beq a (ofRatUp ((z : ℚ) / 2 ^ P)) && beq a (ofRatDown ((z : ℚ) / 2 ^ P))

theorem mantCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {P : ℕ} {a : α} {z : ℤ}
    (h : mantCheck P a z = true) : val a = (z : ℝ) / 2 ^ P := sorry

/-- The exact backend value `z / 2^P`, or `none` if the backend cannot represent it exactly
(checked by `mantCheck`; fail closed). -/
def ofDyadic {α : Type} [CertArith α] (P : ℕ) (z : ℤ) : Option α :=
  let a : α := ofRatDown ((z : ℚ) / 2 ^ P)
  if mantCheck P a z then some a else none

theorem ofDyadic_sound {α : Type} [CertArith α] [LawfulCertArith α] {P : ℕ} {z : ℤ} {a : α}
    (h : ofDyadic P z = some a) : val a = (z : ℝ) / 2 ^ P := sorry

/-- The mantissa decoder the production certificate supplies (untrusted data: `mantCheck`
re-verifies each value). -/
def CertFixed.toMant (P : ℕ) : ℕ → CertFixed P → Option ℤ :=
  fun P' a => if P' = P then some a.m else none

/-- Completeness (not soundness): the landed fixed-point `ofRatUp`/`ofRatDown` are exact on the
grid `ℤ/2^P` and `beq` compares mantissas, so `mantCheck` accepts the true mantissa and the
packed route never falls back (part of SO-POLY-A, against the landed instance). -/
theorem CertFixed.mantCheck_m (P : ℕ) (a : CertFixed P) : mantCheck P a a.m = true := sorry

/-! ### Range-reduced complex exponential: the halving count (SO-BALL)

`certCExpReduced` and `certCExpReduced_sound` are LANDED (`Arith/ComplexExp.lean`, SO-CEXP). -/

/-- The halving count computed from a rational ball (used by `Slp.balls`, never a caller-side
hypothesis): `2^s > 2 (|re| + |im| + r)`, so the exact reduced ball has `normUp + radius ≤ 1/2`. -/
def cexpHalvings (z : CC ℚ) (r : ℚ) : ℕ :=
  Nat.log2 ⌈2 * (|z.re| + |z.im| + r)⌉₊ + 1

/-- Completeness over the exact backend (SO-BALL): with the computed count the reduction never
fails, so `Slp.balls` returns `none` at an `exp` slot only on a malformed program. -/
theorem certCExpReduced_cexpHalvings_isSome (z : CC ℚ) {r : ℚ} (hr : 0 ≤ r) (N : ℕ) :
    (certCExpReduced z r (cexpHalvings z r) N).isSome = true := sorry

/-! ## §B. Exact finite Fourier data (`KAM/Certificate/Poly/{Basic,Ops}.lean`)

LANDED (`Poly/Basic`, SO-PBASE): `CertKey`, `certKeyFun`, `CertPoly`, `CertPoly.eval`,
`CertPoly.coeff`, `CertPoly.eval_eq_fourierSum`, `CertPoly.differentiable_eval`,
`CertPoly.eval_add_int`, `CertRealPoly` and its law-free denotation, reality, differentiability
and periodicity, `CertRealPoly.toPoly`, `eval_toPoly`, `conjugateSymmetric`, and the exact
concatenation `CertPoly.add` / `eval_add`. -/

/-- Multiplication by the character `χ_m` (index shift; exact, law-free). -/
def CertPoly.shift {α : Type} [CertArith α] (m : CertKey) (P : CertPoly α) : CertPoly α := sorry

theorem CertPoly.eval_shift {α : Type} [CertArith α] (n : ℕ) (m : CertKey) (P : CertPoly α)
    (hm : m.length = n) (θ : Fin n → ℂ) :
    (P.shift m).eval n θ = character (certKeyFun n m) θ * P.eval n θ := sorry

/-- `P ↦ P*(θ) := conj (P (conj θ))`: coefficients `c_k ↦ conj c_{-k}` (exact; uses `neg`). -/
def CertPoly.conjReflect {α : Type} [CertArith α] (P : CertPoly α) : CertPoly α := sorry

theorem CertPoly.eval_conjReflect {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (P : CertPoly α) (θ : Fin n → ℂ) :
    P.conjReflect.eval n θ = (starRingEnd ℂ) (P.eval n fun i => (starRingEnd ℂ) (θ i)) := sorry

/-! ## §B′. Advice-checked packed products (`KAM/Certificate/Poly/Packed.lean`, SO-POLY)

Revision 5, orchestrator item 6. SO-REPLAY2 measured the only feasible kernel route for the
products of the checker: signed integer coefficients are Kronecker-packed into one big integer
(slot width `w = 2·bits + 16`), the factors are cut into blocks of `blockRows` (= 32) rows of a
dense box layout, and every output shard `s` is checked against SUPPLIED ADVICE by one kernel
multiplication per block pair `i + j = s`. Packing uses shifts, never a big multiplication per
slot. The advice is SO-REPLAY2's design B: the rounded in-box result `r` (multiples of
`2^scale` in units `2^(-2P)`), with every remaining slot certified small by a slot-bound
decoding (`intSlotsBound`). The kernel never multiplies coefficient pairs.

Soundness lemmas the replay report lists as not done, stated here: `packShift_eq` (the kernel
packing is the mathematical packing), `packSum_injective` (injectivity under the slot bound),
`packSum_listConv` (Kronecker substitution), `packSum_flatten_mul_shards` (the shard
decomposition), `intSlotsBound_sound` (slot decoding), `checkPackedProduct_sound` and
`CertPoly.mulPacked_sound` (the rounding/remainder glue up to the strip enclosure). -/

/-- The mathematical Kronecker packing `Σ_i c_i 2^{w i}` of signed slots. -/
def packSum (w : ℕ) (cs : List ℤ) : ℤ :=
  ((List.range cs.length).map fun i => cs.getD i 0 * 2 ^ (w * i)).sum

/-- The kernel packing (SO-REPLAY2 `soShLoop`): positive and negative parts accumulated
separately as `Nat`s with `Nat.shiftLeft`, one subtraction at the end. -/
def packShift (w : ℕ) (cs : List ℤ) : ℤ := sorry

/-- **Packing correctness.** -/
theorem packShift_eq (w : ℕ) (cs : List ℤ) : packShift w cs = packSum w cs := sorry

/-- Every slot fits a signed `w`-bit slot. -/
def SlotsBounded (w : ℕ) (cs : List ℤ) : Prop := ∀ c ∈ cs, 2 * |c| < 2 ^ w

/-- **Injectivity under the slot bound** (borrows between signed slots are harmless). -/
theorem packSum_injective {w : ℕ} {cs ds : List ℤ} (hc : SlotsBounded w cs)
    (hd : SlotsBounded w ds) (hl : cs.length = ds.length) (h : packSum w cs = packSum w ds) :
    cs = ds := sorry

/-- One-dimensional convolution, length `|a| + |b| - 1` (empty if a factor is empty). -/
def listConv (a b : List ℤ) : List ℤ := sorry

/-- **Kronecker substitution**: packing turns convolution into ONE integer product (it is
polynomial evaluation at `2^w`; no bound is needed). -/
theorem packSum_listConv (w : ℕ) (a b : List ℤ) :
    packSum w (listConv a b) = packSum w a * packSum w b := sorry

/-- Cheap sufficient test that the exact convolution fits the slots:
`2 · min(|a|, |b|) · max|a_i| · max|b_j| < 2^w`. -/
def convFits (w : ℕ) (a b : List ℤ) : Bool := sorry

theorem slotsBounded_listConv {w : ℕ} {a b : List ℤ} (h : convFits w a b = true) :
    SlotsBounded w (listConv a b) := sorry

/-- **Shard decomposition**: with both factors cut into blocks of `L` slots, the packed product
is the shifted sum of the shard sums `Σ_{i+j=s} pack(A_i)·pack(B_j)`. -/
theorem packSum_flatten_mul_shards (w L : ℕ) (A B : List (List ℤ))
    (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L) :
    packSum w A.flatten * packSum w B.flatten =
      ∑ s ∈ Finset.range (A.length + B.length - 1), 2 ^ (w * L * s) *
        ∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) []) :=
  sorry

/-- Slot decoding by bounds (SO-REPLAY2 `soIntSlotsBound`): decode `len` signed slots of `X`
(width `w`) and test `|e_i| ≤ 2^(logs i)` and that nothing is left over. -/
def intSlotsBound (w len : ℕ) (logs : ℕ → ℕ) (X : ℤ) : Bool := sorry

theorem intSlotsBound_sound {w len : ℕ} {logs : ℕ → ℕ} {X : ℤ}
    (h : intSlotsBound w len logs X = true) :
    ∃ e : List ℤ, e.length = len ∧ (∀ i < len, |e.getD i 0| ≤ 2 ^ logs i) ∧ X = packSum w e :=
  sorry

/-- A dense box layout of Fourier keys `lo ≤ k < lo + dims` (mixed radix, row-major with the
row strides `stride`), slot width `width` and shard block size `blockRows` (rows). -/
structure PackLayout where
  lo : CertKey
  dims : List ℕ
  stride : List ℕ
  width : ℕ
  blockRows : ℕ

/-- The slot of a key (`none` outside the box). -/
def PackLayout.slot (L : PackLayout) (k : CertKey) : Option ℕ := sorry

/-- Dense slot list of integer Fourier data (`none` on an out-of-box key; repeated keys add). -/
def PackLayout.dense (L : PackLayout) (cs : List (CertKey × ℤ)) : Option (List ℤ) := sorry

/-- The key carried by slot `i` of the product window of two layouts. -/
def PackLayout.prodKey (La Lb : PackLayout) (i : ℕ) : CertKey := sorry

/-- Compatibility at dimension `n` (decidable): `n` axes, equal widths and strides, and NO WRAP
(each stride at least the sum of the two factor extents minus one). -/
def PackLayout.compat (n : ℕ) (La Lb : PackLayout) : Bool := sorry

/-- `Σ c χ_k(θ)` for integer Fourier data. -/
def intEval (n : ℕ) (cs : List (CertKey × ℤ)) (θ : Fin n → ℂ) : ℂ :=
  (cs.map fun t => (t.2 : ℂ) * character (certKeyFun n t.1) θ).sum

/-- **Kronecker for Fourier data**: under `compat`, the product polynomial is the laid-out
convolution of the dense slot lists. -/
theorem PackLayout.intEval_mul {n : ℕ} {La Lb : PackLayout} (hc : PackLayout.compat n La Lb = true)
    {a b : List (CertKey × ℤ)} {da db : List ℤ} (ha : La.dense a = some da)
    (hb : Lb.dense b = some db) (θ : Fin n → ℂ) :
    intEval n a θ * intEval n b θ =
      ((List.range (listConv da db).length).map fun i =>
        ((listConv da db).getD i 0 : ℂ) * character (certKeyFun n (La.prodKey Lb i)) θ).sum :=
  sorry

/-- Design-B advice for ONE real product (integers only): the two factor layouts, the result
box (`target`, a sub-box of the product window), the rounding scale, the rounded in-box result
of each output shard window (in units `2^scale`), and the log-bound of out-of-box slots. -/
structure PackedAdvice where
  la : PackLayout
  lb : PackLayout
  target : PackLayout
  scale : ℕ
  rounded : List (List ℤ)
  outLog : ℕ

/-! ### Untrusted-advice validation (Revision 6, audit 5 F12 and F13)

`intSlotsBound` alone only exports SOME bounded residual digit list; `packSum_injective` needs
BOTH compared lists in the signed-slot range. The exact side is bounded by `shardFits`; the
advice side by the runtime guard `reconFits` on `2^scale · r + e`. Without the latter, advice
`[16, -1, 0]` at `w = 4`, `scale = 1` cancels a carry (`packSum 4 [16, -1, 0] = 0`) against the
zero product (audit 5, F12). `1 ≤ scale` is a guard (F13: at `scale = 0` two overlapping windows
with per-window bound `2^(0-1) = 1` would exceed `2^0`). -/

/-- Slotwise reconstruction `2^scale · r_i + e_i` of a shard from advice and residual digits. -/
def reconSlots (scale : ℕ) (r e : List ℤ) : List ℤ :=
  List.zipWith (fun a b => 2 ^ scale * a + b) r e

theorem packSum_reconSlots (w scale : ℕ) {r e : List ℤ} (hl : r.length = e.length) :
    packSum w (reconSlots scale r e) = 2 ^ scale * packSum w r + packSum w e := sorry

/-- **Anti-carry guard on untrusted advice (F12).** Every advice slot plus its residual budget
stays in the signed slot range: `2 · (2^scale |r_i| + 2^(logs i)) < 2^w`. -/
def reconFits (w scale : ℕ) (logs : ℕ → ℕ) (r : List ℤ) : Bool :=
  (List.range r.length).all fun i => decide (2 * (2 ^ scale * |r.getD i 0| + 2 ^ logs i) < 2 ^ w)

theorem slotsBounded_reconSlots {w scale : ℕ} {logs : ℕ → ℕ} {r e : List ℤ}
    (h : reconFits w scale logs r = true) (hl : e.length = r.length)
    (he : ∀ i < r.length, |e.getD i 0| ≤ 2 ^ logs i) :
    SlotsBounded w (reconSlots scale r e) := sorry

/-- The exact local convolution of shard `s` (blocks of `L` slots): `Σ_{i+j=s} A_i * B_j`,
zero-padded to `2L - 1` slots. -/
def shardConv (L : ℕ) (A B : List (List ℤ)) (s : ℕ) : List ℤ := sorry

theorem shardConv_length (L : ℕ) (A B : List (List ℤ)) (s : ℕ) :
    (shardConv L A B s).length = 2 * L - 1 := sorry

/-- Kronecker substitution for one shard (factor blocks of length `L`). -/
theorem packSum_shardConv (w L : ℕ) (A B : List (List ℤ))
    (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L) (s : ℕ) :
    packSum w (shardConv L A B s) =
      ∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) []) :=
  sorry

/-- Cheap sufficient test that the exact shard convolution fits the slots:
`2 · (s + 1) · L · max|A| · max|B| < 2^w`. -/
def shardFits (w L : ℕ) (A B : List (List ℤ)) (s : ℕ) : Bool := sorry

theorem slotsBounded_shardConv {w L : ℕ} {A B : List (List ℤ)} {s : ℕ}
    (h : shardFits w L A B s = true) : SlotsBounded w (shardConv L A B s) := sorry

/-- **Shard reconstruction (F12).** Premises are checkable guards only: block lengths, the exact
side fits (`shardFits`), the advice side fits (`reconFits`), the advice length and a passing slot
decode of the packed residual. Then the exact shard convolution is slotwise within `2^(logs i)`
of `2^scale · r` (both lists in the injective range, so `packSum_injective` applies). -/
theorem shard_reconstruct {w scale L : ℕ} {logs : ℕ → ℕ} {A B : List (List ℤ)} {s : ℕ}
    {r : List ℤ} (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L)
    (hfit : shardFits w L A B s = true) (hrec : reconFits w scale logs r = true)
    (hlen : r.length = 2 * L - 1)
    (hdec : intSlotsBound w (2 * L - 1) logs
      ((∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) [])) -
        2 ^ scale * packSum w r) = true) :
    ∀ i < 2 * L - 1, |(shardConv L A B s).getD i 0 - 2 ^ scale * r.getD i 0| ≤ 2 ^ logs i :=
  sorry

/-- Slots per factor block (`blockRows` rows of the factor layout). -/
def PackedAdvice.blockLen (adv : PackedAdvice) : ℕ := sorry

/-- A dense factor cut into blocks of `blockLen` slots, the last one zero-padded. -/
def PackedAdvice.cut (adv : PackedAdvice) (d : List ℤ) : List (List ℤ) := sorry

theorem PackedAdvice.cut_length {adv : PackedAdvice} {d : List ℤ} :
    ∀ x ∈ adv.cut d, x.length = adv.blockLen := sorry

/-- Per-slot log-bounds of shard `s`: `scale - 1` on target slots, `outLog` elsewhere. -/
def PackedAdvice.shardLogs (adv : PackedAdvice) (s : ℕ) : ℕ → ℕ := sorry

/-- Overlap-add of the shard windows: the combined rounded result, one entry per product slot. -/
def PackedAdvice.combined (adv : PackedAdvice) : List ℤ := sorry

/-- Whether product slot `i` lies in the target box. -/
def PackedAdvice.inBox (adv : PackedAdvice) (i : ℕ) : Bool := sorry

/-- **Structural guards (F12, F13)**, decidable: `1 ≤ scale`; positive `width` and `blockRows`;
`compat` at `la.dims.length` with equal widths for `la`, `lb`, `target`; `target` a sub-box of
the product window; `blockLen` divides the row layout; every advice window `rounded[s]` has
length `2·blockLen - 1`; advice is ZERO on every slot outside the target box and beyond the
product window (no unchecked high slots). -/
def PackedAdvice.shapeOK (adv : PackedAdvice) : Bool := sorry

/-- One shard `s`, all guards inside: the blocks of `A`, `B` have length `blockLen`, the advice
window has length `2·blockLen - 1`, `shardFits`, `reconFits` with `shardLogs s`, and
`Σ_{i+j=s} packShift(A_i)·packShift(B_j) - 2^scale · packShift(r_s)` passes `intSlotsBound`
with `shardLogs s`. -/
def checkShard (adv : PackedAdvice) (A B : List (List ℤ)) (s : ℕ) : Bool := sorry

/-- **Shard soundness** (premise: the check only). -/
theorem checkShard_sound {adv : PackedAdvice} {A B : List (List ℤ)} {s : ℕ}
    (h : checkShard adv A B s = true) :
    (adv.rounded.getD s []).length = 2 * adv.blockLen - 1 ∧
      ∀ i < 2 * adv.blockLen - 1,
        |(shardConv adv.blockLen A B s).getD i 0 - 2 ^ adv.scale * (adv.rounded.getD s []).getD i 0|
          ≤ 2 ^ adv.shardLogs s i := sorry

/-- The whole product: `shapeOK` (with `1 ≤ scale`), the dense factors cut by `cut`, and
`checkShard` on every shard `s < (cut da).length + (cut db).length - 1`. -/
def checkPackedProduct (adv : PackedAdvice) (da db : List ℤ) : Bool := sorry

/-- **Guards exported from success** (F12, F13): no premise but the check. -/
theorem checkPackedProduct_guards {adv : PackedAdvice} {da db : List ℤ}
    (h : checkPackedProduct adv da db = true) :
    1 ≤ adv.scale ∧ adv.shapeOK = true ∧ 0 < adv.blockLen ∧
      adv.rounded.length = (adv.cut da).length + (adv.cut db).length - 1 ∧
      ∀ s < (adv.cut da).length + (adv.cut db).length - 1,
        checkShard adv (adv.cut da) (adv.cut db) s = true := sorry

/-- F13 negative contract: scale zero is rejected (whatever the data). -/
theorem checkPackedProduct_scale_zero {adv : PackedAdvice} (h0 : adv.scale = 0)
    (da db : List ℤ) : checkPackedProduct adv da db = false := sorry

/-- **Rounding/remainder glue (slots).** A passing check (the ONLY premise) gives, slot by slot of
the exact convolution, `|conv_i - 2^scale r_i| ≤ 2^scale` on the target box (at most two
overlapping shard windows, each `≤ 2^(scale-1)`, and `1 ≤ scale` from the guards) and
`|conv_i| ≤ 2^(outLog+1)` elsewhere (advice zero there). Route: `checkPackedProduct_guards`,
`checkShard_sound` (via `shard_reconstruct`), `packSum_flatten_mul_shards`, overlap-add. -/
theorem checkPackedProduct_sound {adv : PackedAdvice} {da db : List ℤ}
    (h : checkPackedProduct adv da db = true) :
    adv.combined.length = (listConv da db).length ∧ ∀ i < (listConv da db).length,
      (adv.inBox i = true →
        |(listConv da db).getD i 0 - 2 ^ adv.scale * adv.combined.getD i 0| ≤ 2 ^ adv.scale) ∧
      (adv.inBox i = false → |(listConv da db).getD i 0| ≤ 2 ^ (adv.outLog + 1)) := sorry

/-- §8 negative test (audit 5, F12): the carry-cancelling advice `[16, -1, 0]` packs to `0` at
`w = 4` but fails the anti-carry guard (decided now; the guard body is concrete). -/
theorem packSum_audit5_cancel : packSum 4 [16, -1, 0] = 0 := by decide

theorem reconFits_audit5_rejects : reconFits 4 1 (fun _ => 0) [16, -1, 0] = false := by decide

/-- Integer mantissas `(re, im)` of a backend polynomial at scale `P`, read with the decoder
`dec` and each verified by `mantCheck` (`none` on any failure: fail closed). -/
def CertPoly.toMants {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (P : ℕ)
    (p : CertPoly α) : Option (List (CertKey × ℤ) × List (CertKey × ℤ)) := sorry

theorem CertPoly.toMants_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {P : ℕ} {p : CertPoly α}
    {m : List (CertKey × ℤ) × List (CertKey × ℤ)} (h : p.toMants dec P = some m)
    (θ : Fin n → ℂ) :
    p.eval n θ = (intEval n m.1 θ + Complex.I * intEval n m.2 θ) / 2 ^ P := sorry

/-- The polynomial part of one advice-checked complex product: four real packed products
(`re·re`, `im·im`, `re·im`, `im·re`) at mantissa scale `P`; the result coefficients are the
combined rounded target slots, made exact in the backend by `ofDyadic`; the radius bounds the
remainder `Σ_k e_k χ_k` on `T_ρ` (target slots `2^(scale-2P)`, other slots `2^(outLog+1-2P)`,
times `w^{|k|₁}`, upward). `none` on any failed decode, layout, shard or exactness check. -/
def CertPoly.mulPacked {α : Type} [CertArith α] (dec : ℕ → α → Option ℤ) (W : CertWeight)
    (P : ℕ) (rr ii ri ir : PackedAdvice) (a b : CertPoly α) : Option (CertPoly α × α) := sorry

/-- **Packed product contract**: the enclosure of the EXACT product on the strip. -/
theorem CertPoly.mulPacked_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {dec : ℕ → α → Option ℤ} {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    {P : ℕ} {rr ii ri ir : PackedAdvice} {a b : CertPoly α} {out : CertPoly α × α}
    (h : CertPoly.mulPacked dec W P rr ii ri ir a b = some out) :
    ∀ θ ∈ complexStrip n W.rho, ‖a.eval n θ * b.eval n θ - out.1.eval n θ‖ ≤ val out.2 :=
  sorry

/-- Advice for one model product: `packed` (four real packed products at mantissa scale `P`) or
`direct` (the direct product of Revision 4; tests and the `ℚ` toys). -/
inductive ProductAdvice : Type
  | direct
  | packed (P : ℕ) (rr ii ri ir : PackedAdvice)

/-- The checker's name of a product: `[site, i, j, …]`, assigned deterministically by the call
site (§7: compose 0, exp witnesses 1, reciprocal witnesses 2, Gram 3, torsion 4, invariance 5,
energy 6, SOS 7, graph 8). The generator emits the advice under the same keys. -/
abbrev ProductKey : Type := List ℕ

abbrev AdviceBook : Type := List (ProductKey × ProductAdvice)

/-! ## §C. Fourier models (`KAM/Certificate/Model/{Basic,Ops,Exp,Inv}.lean`)

LANDED (`Model/Basic`, SO-PBASE): `CertWeight`, `checkWeight`, `norm_character_le_weight`,
`CertModel`, `CertModel.Encloses`, `CertModel.supBound`, `CertModel.norm_le_supBound`. -/

/-- Truncation/precision controls and the product advice (Revision 5: indexed by the backend
for the mantissa decoder). -/
structure ModelConfig (α : Type) where
  /-- keep only product terms with `|k|₁ ≤ cutoff` -/
  cutoff : ℕ
  /-- Taylor order and halvings of the REAL upper bounds `ratExpUp` (`exp(2B)`, `exp(B)`,
  `exp(η) - 1`); complex pins carry their own counts (`ExpWitness`, Revision 4) -/
  taylorN : ℕ
  halvings : ℕ
  /-- untrusted mantissa decoder (`CertFixed.toMant P` in production); every value it returns is
  re-verified by `mantCheck` -/
  toMant : ℕ → α → Option ℤ
  /-- the advice of every product of the stage this configuration drives (§B′) -/
  advice : AdviceBook

def CertModel.add {α : Type} [CertArith α] (W : CertWeight) (a b : CertModel α) :
    CertModel α := sorry

/-- Model product (Revision 5). The polynomial part comes from `cfg.advice` at `key`:
`packed` ⇒ `CertPoly.mulPacked` (kernel: one multiplication per shard block pair); `direct` ⇒
the direct product. The radius adds the packed remainder and the cross terms
`sup|a| rad_b + sup|b| rad_a + rad_a rad_b`. A missing key or a failed packed check yields the
crude enclosure `⟨deg_a + deg_b, 0, sup|a| · sup|b|⟩` (sound; later margins then fail), so the
contract `CertModel.Encloses.mul` is unconditional and unchanged in meaning. -/
def CertModel.mul {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig α)
    (key : ProductKey) (a b : CertModel α) : CertModel α := sorry

/-- Drop terms of weighted size `≤ eps` into the radius (precision reduction). -/
def CertModel.trim {α : Type} [CertArith α] (W : CertWeight) (eps : α) (a : CertModel α) :
    CertModel α := sorry

/-- Re-express a model at another `2π`-degree (validated `π` enclosure `pe`). -/
def CertModel.toDeg {α : Type} [CertArith α] (W : CertWeight) (pe : PiEnclosure α) (d : ℤ)
    (a : CertModel α) : CertModel α := sorry

/-- The model of `∂_j P` for exact data `P` at degree `d`: coefficients `i k_j c_k` (backend
products, their errors in the radius) at degree `d + 1`. -/
def CertModel.ofDeriv {α : Type} [CertArith α] (W : CertWeight) (j : ℕ) (d : ℤ)
    (P : CertPoly α) : CertModel α := sorry

theorem CertModel.Encloses.ofDeriv {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (j : Fin n) (d : ℤ)
    (P : CertPoly α) : (CertModel.ofDeriv W j.val d P).Encloses n W.rho
      (fun θ => (2 * (Real.pi : ℂ)) ^ d * fderiv ℂ (P.eval n) θ (Pi.single j 1)) := sorry

theorem CertModel.Encloses.add {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {a b : CertModel α}
    {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) (hb : b.Encloses n W.rho g)
    (hdeg : a.deg = b.deg) : (CertModel.add W a b).Encloses n W.rho (f + g) := sorry

theorem CertModel.Encloses.mul {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    (key : ProductKey) {a b : CertModel α} {f g : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f)
    (hb : b.Encloses n W.rho g) : (CertModel.mul W cfg key a b).Encloses n W.rho (f * g) :=
  sorry

theorem CertModel.Encloses.trim {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (eps : α) {a : CertModel α}
    {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n W.rho f) :
    (CertModel.trim W eps a).Encloses n W.rho f := sorry

theorem CertModel.Encloses.toDeg {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (d : ℤ) {a : CertModel α} {f : (Fin n → ℂ) → ℂ}
    (ha : a.Encloses n W.rho f) : (CertModel.toDeg W pe d a).Encloses n W.rho f := sorry

/-- The real-torus average of an enclosed function is the zero coefficient up to the radius. -/
theorem CertModel.Encloses.average {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {ρ : ℝ} (hρ : 0 < ρ) {a : CertModel α} {f : (Fin n → ℂ) → ℂ} (ha : a.Encloses n ρ f)
    (hf : ContinuousOn f (complexStrip n ρ)) :
    ‖torusAverage (fun x : Fin n → ℝ => f fun i => (x i : ℂ)) -
        (2 * (Real.pi : ℂ)) ^ a.deg * a.poly.coeff n 0‖ ≤ (2 * Real.pi) ^ a.deg * val a.rad :=
  sorry

/-! ### A-posteriori witnesses (`KAM/Certificate/Model/{Exp,Inv}.lean`)

`exp`: the witness `E ≈ exp g₀` for the degree-zero POLYNOMIAL part `g₀` of `g` (exact
derivative). With `|g₀| ≤ B`, pin error `ε₀ ≥ |E(0) - exp g₀(0)|` and residual bounds
`r_j ≥ sup |∂_j E - (∂_j g₀) E|`, the certified radius is
`exp(2B) (ε₀ + Σ_j (1/2 + ρ) r_j) + exp(B) (exp(η) - 1)`, `η` the radius of `g`.
Pin (Revision 4, F10): `expPinBall g` is a ball `(c, rc)` enclosing `g₀(0) = Σ_k ĝ₀(k)`, the
rounding of that sum paid in `rc`; then `out := certCExpReduced c rc E.pinHalvings E.pinOrder`
(`none` ⇒ `expWitnessRadius = none`), and `ε₀ := upAdd (|E(0) - out.1|↑) out.2`, where `|·|↑`
is the outward `normUp` of the rounded difference `E(0) - out.1` plus its rounding. Thus `ε₀`
pays input rounding, scaling, Taylor remainder, Taylor-sum rounding, the `s` squarings and the
final subtraction. The real factors `exp(2B)`, `exp(B)`, `exp(η) - 1` stay on the `ratExpUp`
route (unchanged). Pin counts are certificate data, per witness; no smallness of `g₀(0)` is
assumed anywhere.
Reciprocal (ruling O2): the witness `Q ≈ 1/b` for a model `b = (2π)^d (P + T)`; with
`δ ≥ sup |1 - Q (P + T)|` (one product) and `δ < 1`, `b` has no zero on `T_ρ` and
`|1/(P + T) - Q| ≤ sup|Q| δ/(1 - δ)` (scalar Neumann series); no lower bound is assumed. -/

/-- An exp witness: the polynomial `E ≈ exp g₀` and the pin's halving count and Taylor order
(certificate data, chosen by the generator from the size of `g₀(0)`). -/
structure ExpWitness (α : Type) where
  poly : CertPoly α
  pinHalvings : ℕ
  pinOrder : ℕ

/-- A ball enclosing `g₀(0)`, the value at `θ = 0` of the polynomial part (sum of coefficients,
rounding in the radius). -/
def expPinBall {α : Type} [CertArith α] (g : CertModel α) : CC α × α := sorry

theorem expPinBall_sound {α : Type} [CertArith α] [LawfulCertArith α] (n : ℕ)
    (g : CertModel α) :
    ‖g.poly.eval n 0 - (expPinBall g).1.toC‖ ≤ val (expPinBall g).2 := sorry

/-- The radius certified for `exp g` by the witness `E` (or `none` if a check fails, including
a failed range reduction of the pin). -/
def expWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (g : CertModel α) (E : ExpWitness α) : Option α := sorry

/-- The pin contract on a successful call: the reduced exponential succeeded on `expPinBall g`
and encloses `exp g₀(0)` (all reduction, rounding and squaring errors inside `out.2`). -/
theorem expWitnessRadius_pin {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {cfg : ModelConfig α} {g : CertModel α} {E : ExpWitness α} {r : α}
    (hE : expWitnessRadius n W cfg g E = some r) :
    ∃ out, certCExpReduced (expPinBall g).1 (expPinBall g).2 E.pinHalvings E.pinOrder = some out ∧
      ‖Complex.exp (g.poly.eval n 0) - out.1.toC‖ ≤ val out.2 := sorry

theorem expWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {g : CertModel α} {gf : (Fin n → ℂ) → ℂ} (hg : g.Encloses n W.rho gf) (hdeg : g.deg = 0)
    {E : ExpWitness α} {r : α}
    (hE : expWitnessRadius n W cfg g E = some r) :
    (⟨0, E.poly, r⟩ : CertModel α).Encloses n W.rho (fun θ => Complex.exp (gf θ)) := sorry

/-- The radius certified for `1/b` by the witness `Q` (or `none` if `δ < 1` fails). -/
def invWitnessRadius {α : Type} [CertArith α] (n : ℕ) (W : CertWeight) (cfg : ModelConfig α)
    (b : CertModel α) (Q : CertPoly α) : Option α := sorry

theorem invWitness_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {b : CertModel α} {bf : (Fin n → ℂ) → ℂ} (hb : b.Encloses n W.rho bf)
    {Q : CertPoly α} {r : α} (hQ : invWitnessRadius n W cfg b Q = some r) :
    (∀ θ ∈ complexStrip n W.rho, bf θ ≠ 0) ∧
      (⟨-b.deg, Q, r⟩ : CertModel α).Encloses n W.rho (fun θ => (bf θ)⁻¹) := sorry

/-! ## §D. The Hamiltonian language (`KAM/Certificate/{PhaseBasis,Expr/*}`)

LANDED (SO-CLOCK, SO-EXPR-A/B1/B2): `phaseBasis`; `HamExpr`, `modePhase`, `HamExpr.eval`,
`HamExpr.NonvanishingOn`, `contDiffOn_eval`, `eval_add_int`, `eval_real`, `certDomain`,
`isOpen_certDomain`, `certDomain_add_int`; `SlpOp`, `Slp`, `Slp.val`, `HamJet`, `phaseNat`,
`HamExpr.jet`, `jet_v0`, `jet_d1`, `jet_d2`, `jet_d3` (landed verbatim). Pending: `Slp.balls`
(SO-BALL), the embedding and composition (SO-EMB). -/

/-- Ball arithmetic of every slot on `D` (no embedding), in `ℚ`: `(centre, radius)` with
`|slot - centre| ≤ radius` on `D`. Constants exact; actions `(c_j, r_j)`; characters
`(0, w_H^{|k|₁})` (`k ≠ 0`); sums and products; `exp` (also the compiled `sin`, `cos`) via
`certCExpReduced c r (cexpHalvings c r) taylorN` on the operand ball `(c, r)` (Revision 4, F10:
range reduction with the count computed from the ball; a `none` from it makes `Slp.balls` return
`none`, fail closed; `taylorN` is certificate data); `inv` fails (`none`) unless
the operand ball excludes `0`, i.e. `radius < max(|re|, |im|)` of its centre (O2). -/
def Slp.balls (n : ℕ) (p : Slp) (WH : CertWeight) (centre radius : List ℚ) (taylorN : ℕ) :
    Option (List (CC ℚ × ℚ)) := sorry

theorem Slp.val_mem_ball {n : ℕ} (p : Slp) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : p.balls n WH centre radius taylorN = some bs)
    {z : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ certDomain n WH.rho centre radius) (i : ℕ)
    (hi : i < bs.length) :
    ‖p.val n z i - (bs.getD i (⟨0, 0⟩, 0)).1.toC‖ ≤ (bs.getD i (⟨0, 0⟩, 0)).2 := sorry

/-- Successful ball arithmetic on the jet program certifies every denominator on `D`. -/
theorem HamExpr.nonvanishingOn_of_balls {n : ℕ} (e : HamExpr n) {WH : CertWeight} {s N : ℕ}
    (hW : checkWeight WH s N = true) {centre radius : List ℚ} {taylorN : ℕ}
    {bs : List (CC ℚ × ℚ)} (h : e.jet.prog.balls n WH centre radius taylorN = some bs) :
    e.NonvanishingOn (certDomain n WH.rho centre radius) := sorry

/-- The embedding `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` from real Fourier data;
a missing component denotes `0` (no backend default value is used, finding F2). -/
structure CertEmbedding (α : Type) where
  angleDeg : List ℤ
  angle : List (CertRealPoly α)
  actionDeg : List ℤ
  action : List (CertRealPoly α)

def CertEmbedding.eval {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (θ : Fin n → ℂ) : (Fin n → ℂ) × (Fin n → ℂ) :=
  (fun i => θ i + (2 * (Real.pi : ℂ)) ^ (K.angleDeg.getD i.val 0) *
      ((K.angle[i.val]?.map fun P => P.eval n θ).getD 0),
    fun i => (2 * (Real.pi : ℂ)) ^ (K.actionDeg.getD i.val 0) *
      ((K.action[i.val]?.map fun P => P.eval n θ).getD 0))

theorem CertEmbedding.differentiable_eval {α : Type} [CertArith α] (n : ℕ)
    (K : CertEmbedding α) : Differentiable ℂ (K.eval n) := sorry

theorem CertEmbedding.isPrimaryOnStrip {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α)
    (ρ : ℝ) : IsPrimaryOnStrip (K.eval n) ρ := sorry

/-- Law-free (finding F2): `CertRealPoly.eval_real` and the `0` default. -/
theorem CertEmbedding.isRealOnReals {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) :
    IsRealOnReals (K.eval n) := sorry

/-- Witnesses: one per `exp` slot and one per `inv` slot of the jet program (slot order), and
the character table keyed by the normalized index (coordinates with syntactically zero `U_j`
zeroed; `-k` uses `conjReflect`). Exp and character witnesses are `ExpWitness`es: each carries
its own pin halving count and order, and its pin `exp(2πi k·U(0))` (characters) or
`exp g₀(0)` goes through `certCExpReduced` (Revision 4, F10). -/
structure Witnesses (α : Type) where
  expWit : List (ExpWitness α)
  invWit : List (CertPoly α)
  charWit : List (CertKey × ExpWitness α)

/-- Composition of the jet slots with `K`: one model per requested slot, or `none` if a witness
check fails (including a failed range reduction of an exp or character pin: fail closed). -/
def Slp.compose {α : Type} [CertArith α] (n : ℕ) (p : Slp) (K : CertEmbedding α)
    (wit : Witnesses α) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α)
    (wanted : List ℕ) : Option (List (CertModel α)) := sorry

/-- Unconditional in the domain: reciprocal witnesses certify their own nonvanishing. -/
theorem Slp.compose_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (p : Slp)
    (K : CertEmbedding α) (wit : Witnesses α) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (wanted : List ℕ) {ms : List (CertModel α)}
    (h : Slp.compose n p K wit W cfg pe wanted = some ms) :
    ms.length = wanted.length ∧ ∀ idx (hidx : idx < ms.length), ms[idx].Encloses n W.rho
      (fun θ => p.val n (K.eval n θ) (wanted.getD idx 0)) := sorry

/-! ## §E. Norms on `ℂⁿ × ℂⁿ` from partial derivatives: LANDED (`KAM/Certificate/NormBridge.lean`,
SO-NORM: `norm_fderiv_le_sum_partials`, `norm_iteratedFDeriv_two_le_sum_partials`,
`hamiltonianVectorFieldℂ_sumVec`, and the two `X_H` bounds with `1 ≤ n`, F8). -/

/-! ## §F. Matrix certificates, Gram, torsion, constants, positivity

LANDED: `matrix_inv_of_approx_inverse` (`MatrixInv`, SO-MINV); `cRUpQ`, `cR_le_cRUpQ`, `isoC1Q`,
`isoC2Q`, `isoC1_le_isoC1Q`, `isoC2_le_isoC2Q` (`Constants`, SO-CONST). -/

/-- A matrix of models (row-major), e.g. the Gram matrix or its approximate inverse. -/
abbrev ModelMatrix (α : Type) : Type := List (List (CertModel α))

/-- Entrywise enclosure of a matrix-valued function on `T_ρ`; every entry must be present (no
backend default model, finding F2). -/
def ModelMatrix.Encloses {α : Type} [CertArith α] (n : ℕ) {ι : Type*} (idx : ι → ℕ) (ρ : ℝ)
    (M : ModelMatrix α) (F : (Fin n → ℂ) → Matrix ι ι ℂ) : Prop :=
  ∀ i j, ∃ m : CertModel α, (M[idx i]?.bind fun r => r[idx j]?) = some m ∧
    m.Encloses n ρ (fun θ => F θ i j)

-- `ModelMatrix.HasShape` (exact `k × k` list shape, audit 2 F7) is LANDED in `MatrixInv`.

/-- The matrix of a polynomial-matrix witness (missing entries `0`). -/
def polyMatrix {α : Type} [CertArith α] (n : ℕ) (B : List (List (CertPoly α))) (θ : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (((B[i.val]?).bind fun r => r[j.val]?).map fun P => P.eval n θ).getD 0

/-- The Gram models `DKᵀ DK` (bilinear, `dotℂ`), computed at reduced precision. -/
def gramModels {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (W : CertWeight)
    (cfg : ModelConfig α) (pe : PiEnclosure α) : ModelMatrix α := sorry

theorem gramModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    (K : CertEmbedding α) {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true)
    (cfg : ModelConfig α) {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) :
    (gramModels n K W cfg pe).Encloses n (fun i : Fin n => i.val) W.rho
      (gramMatrix (K.eval n)) := sorry

/-- Gram check: with the witness `B ≈ G⁻¹`, `sup_{T_ρ}` row sums of `I - B G` give `δ < 1`,
`β ≥ sup ‖B‖`, and `β/(1 - δ) ≤ σB - μ`. Returns the certified `(δ, β)`. -/
def gramCheck {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (Binv : List (List
    (CertPoly α))) (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (σBμ : ℚ) :
    Option (α × α) := sorry

theorem gramCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (hn : 1 ≤ n)
    (K : CertEmbedding α) (Binv : List (List (CertPoly α))) {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (cfg : ModelConfig α) {pe : PiEnclosure α}
    (hpe : checkPiEnclosure pe = true) (σBμ : ℚ) {δβ : α × α}
    (h : gramCheck n K Binv W cfg pe σBμ = some δβ) :
    val δβ.1 < 1 ∧ ∀ θ ∈ complexStrip n W.rho, IsUnit (gramMatrix (K.eval n) θ).det ∧
      (∀ i, ∑ j, ‖(gramMatrix (K.eval n) θ)⁻¹ i j‖ ≤ σBμ) ∧
      ‖(gramMatrix (K.eval n) θ)⁻¹ - polyMatrix n Binv θ‖ ≤
        val δβ.1 * val δβ.2 / (1 - val δβ.1) := sorry

/-- Row/column index of the bordered torsion: `inl i ↦ i`, `inr () ↦ n`. -/
def torsionIdx (n : ℕ) : Fin n ⊕ Unit → ℕ := Sum.elim (fun i => i.val) (fun _ => n)

/-- Entrywise models of `extendedTorsion H K (s ω)` on `T_ρ` for EVERY `ω` in the box: the block
`torsion` from `DX_H ∘ K` (jet `d2` composed with `K`), the normal frame `N = Ω₀ DK B` with the
Gram witness `B` and the certified radius `δβ/(1 - δ)`, `DN[sω] = Ω₀ (D²K[sω] G⁻¹ + DK D(G⁻¹)[sω])`
with `D(G⁻¹)[sω] = -G⁻¹ (DG[sω]) G⁻¹`; the border column `s ω` from the box (ball); the last row
`DH(K) N` (jet `d1` composed with `K`). -/
def torsionModels {α : Type} [CertArith α] (n : ℕ) (e : HamExpr n) (K : CertEmbedding α)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (δβ : α × α) (box : FreqBox) (s : ℚ)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) : Option (ModelMatrix α) :=
  sorry

/-- **Torsion producer contract (finding F3).** Validated weight and `π`, a successful Gram
certificate (its `(δ, β)` passed on), successful construction, a frequency in the box, and `K`
mapping the strip into an open set where `e` has no vanishing denominator give the enclosure
of the LITERAL frozen `extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)`, and its continuity. -/
theorem torsionModels_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ} (hn : 1 ≤ n)
    {e : HamExpr n} {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D)
    (hnv : e.NonvanishingOn D) {K : CertEmbedding α} {W : CertWeight} {sw Nw : ℕ}
    (hW : checkWeight W sw Nw = true) (hKD : ∀ θ ∈ complexStrip n W.rho, K.eval n θ ∈ D)
    (wit : Witnesses α) (Binv : List (List (CertPoly α))) (cfg : ModelConfig α)
    {pe : PiEnclosure α} (hpe : checkPiEnclosure pe = true) {σBμ : ℚ} {δβ : α × α}
    (hG : gramCheck n K Binv W cfg pe σBμ = some δβ) (box : FreqBox) (s : ℚ)
    {T : ModelMatrix α} (hT : torsionModels n e K wit Binv δβ box s W cfg pe = some T)
    {ω : Fin n → ℝ} (hω : FreqEncloses n box ω) :
    ModelMatrix.HasShape (n + 1) T ∧ T.Encloses n (torsionIdx n) W.rho
        (KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω)) ∧
      ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion e.eval (K.eval n) ((s : ℝ) • ω) θ a b)
        (complexStrip n W.rho) := sorry

/-- The averaged bordered torsion check at dimension `n` (audit 2 F7). It FIRST checks the exact
shapes `HasShape (n + 1) T` and `HasShape (n + 1) S` (decidable list-length tests) and rejects
otherwise; then centre `C` = zero modes, radius matrix `R`; with the constant witness `S`,
`‖I - S C‖ + ‖S‖ ‖R‖ =: δ_T < 1` and `‖S‖/(1-δ_T) ≤ σT - μ`, all on `(n+1) × (n+1)` arrays. -/
def torsionAvgCheck {α : Type} [CertArith α] (n : ℕ) (T : ModelMatrix α)
    (S : List (List (CC α))) (σTμ : ℚ) : Bool := sorry

/-- A passing averaging check has exact `(n+1) × (n+1)` inputs (law-free; F7 negative tests). -/
theorem torsionAvgCheck_shape {α : Type} [CertArith α] {n : ℕ} {T : ModelMatrix α}
    {S : List (List (CC α))} {σTμ : ℚ} (h : torsionAvgCheck n T S σTμ = true) :
    ModelMatrix.HasShape (n + 1) T ∧ ModelMatrix.HasShape (n + 1) S := sorry

theorem torsionAvgCheck_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    {ω : Fin n → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {T : ModelMatrix α}
    (hT : T.Encloses n (torsionIdx n) ρ (KAM.Iso.extendedTorsion H K ω))
    (hcont : ∀ a b, ContinuousOn (fun θ => KAM.Iso.extendedTorsion H K ω θ a b)
      (complexStrip n ρ))
    (S : List (List (CC α))) (σTμ : ℚ) (h : torsionAvgCheck n T S σTμ = true) :
    IsUnit (KAM.Iso.extendedTorsionAverage H K ω).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage H K ω)⁻¹ i j‖ ≤ σTμ := sorry

/-- Sum-of-squares lower bound on the real torus. The check forms the model of
`Re-part f - m₀ - g g*` (`g* = conjReflect g`), bounds its sup by `r`, and requires
`m ≤ m₀ - r` (the residual is PAID; a small `r` without that slack is rejected). -/
def checkRealLowerBound {α : Type} [CertArith α] (W : CertWeight) (cfg : ModelConfig α)
    (f : CertModel α) (m₀ m : ℚ) (g : CertPoly α) : Bool := sorry

theorem checkRealLowerBound_sound {α : Type} [CertArith α] [LawfulCertArith α] {n : ℕ}
    {W : CertWeight} {s N : ℕ} (hW : checkWeight W s N = true) (cfg : ModelConfig α)
    {f : CertModel α} {ff : (Fin n → ℂ) → ℂ} (hf : f.Encloses n W.rho ff) {m₀ m : ℚ}
    {g : CertPoly α} (h : checkRealLowerBound W cfg f m₀ m g = true) (x : Fin n → ℝ) :
    (m : ℝ) ≤ (ff fun i => (x i : ℂ)).re := sorry

/-! ## §G. Frequencies, the certificate, the checker and the black box -/

/-! ### Exact frequencies (`KAM/Certificate/Freq.lean`, finding F1)

The black box takes the EXACT reference vector `ω* : Fin n → ℝ` as a real vector, with two proved
facts about it: `FreqEncloses n c.freqBox ω*` (the certificate's rational box, which is all the
checker reads) and `IsDiophantine γ τ ω*` (the external input). Every sub-check is uniform over
the box. Any rationally independent `n`-tuple is admissible. LANDED (`Freq`, SO-FREQ): `FreqBox`,
`FreqEncloses`, `algFreq`, `checkAlgBox`, `algFreq_encloses` (coordinates in `ℚ(x)` for a
certified real `x`, e.g. `√5`, `∛2`). -/

/-! ### The certificate (`KAM/Certificate/Defs.lean`) -/

/-- Parameters of `g1_explicit` (exact rationals; `τ ∈ ℕ`). `nuRay` is the theorem's `ν`. -/
structure CertParams where
  tau : ℕ
  rho : ℚ
  rhoInf : ℚ
  M : ℚ
  σK : ℚ
  σB : ℚ
  σT : ℚ
  μ : ℚ
  γbar : ℚ
  σω : ℚ
  nuRay : ℚ
  γ : ℚ
  s : ℚ
  err : ℚ
  E0 : ℚ
  /-- claimed explicit displacement bound, checked `≥ isoC2Q e / (γ² ρ^{2τ})` -/
  disp : ℚ

/-- The certificate: problem data, numerical witnesses and controls (data only; no proofs, no
real numbers). -/
structure TorusCertificate (n : ℕ) (α : Type) where
  params : CertParams
  ham : HamExpr n
  /-- `D = T_{ρ_H} × polydisc(centre, radius)` -/
  weightH : CertWeight
  centre : List ℚ
  radius : List ℚ
  /-- rational box of the reference vector `ω*` -/
  freqBox : FreqBox
  emb : CertEmbedding α
  /-- weight of the strip `T_ρ` (its `rho` must equal `params.rho`) -/
  weight : CertWeight
  wit : Witnesses α
  gramInv : List (List (CertPoly α))
  torsInv : List (List (CC α))
  cfgFull : ModelConfig α
  cfgLow : ModelConfig α
  piEnc : PiEnclosure α
  expHalvings : ℕ
  expOrder : ℕ

section Denotation

variable {n : ℕ} {α : Type} [CertArith α]

def TorusCertificate.D (c : TorusCertificate n α) : Set ((Fin n → ℂ) × (Fin n → ℂ)) :=
  certDomain n c.weightH.rho c.centre c.radius

def TorusCertificate.H (c : TorusCertificate n α) : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := c.ham.eval

def TorusCertificate.K (c : TorusCertificate n α) :
    (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ) := c.emb.eval n

end Denotation

/-! The sub-checks (each `Bool`, each provable by `decide +kernel` on its own). -/

/-- Shapes (`box.length = n`, list lengths), positivity, `2 ≤ n`, `n - 1 ≤ τ`, `ρ∞ < ρ`,
`1 < s < σω`, `γ ≤ γbar`, `0 ≤ e`, `weight.rho = rho`, both weights, the `π` enclosure, the box
excludes `0` in some coordinate, and the ray margins against the box's lower bound of `‖ω*‖`. -/
def checkStatic {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- Ball arithmetic of the jet on `D` (every denominator certified) and the five bounds
`‖DH‖, ‖X_H‖, ‖DX_H‖, ‖D²X_H‖, ‖D²H‖ ≤ M` on `D`. -/
def checkHamBounds {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `ball (K θ) μ ⊆ D` on `T_ρ` and `‖DK‖ ≤ σK - μ` (row sums of `DK` models). -/
def checkEmbedding {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `sup_{T_ρ} ‖X_H(K) - DK (s ω)‖ ≤ e` at full precision, uniformly for `ω` in the box. -/
def checkInvariance {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `‖⟨H ∘ K⟩ - E₀‖ ≤ e` (zero mode of the composed model ± radius). -/
def checkEnergy {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- The Gram certificate (`gramCheck`) with bound `σB - μ`. -/
def checkGram {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `torsionModels` at `s` and the box, then `torsionAvgCheck n` (exact `(n+1)×(n+1)` shapes of
`T` and the witness `c.torsInv`) with bound `σT - μ`. -/
def checkTorsion {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `isoC1Q e < γ⁴ ρ^{4τ}` and `isoC2Q e ≤ disp γ² ρ^{2τ}`. -/
def checkSmallness {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  sorry

/-- **The black-box checker.** -/
def checkTorusCertificate {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c && checkEnergy c &&
    checkGram c && checkTorsion c && checkSmallness c

section Black

variable {n : ℕ} {α : Type} [CertArith α]

/-- Every hypothesis of `KAM.Iso.Apost.g1_explicit` and of `IG1Body`, verbatim, at the data
denoted by `c` and the exact reference vector `ωstar` (`IsDiophantine` excepted). -/
structure G1Hyps (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop where
  hn : 2 ≤ n
  hτ : (n : ℝ) - 1 ≤ (c.params.tau : ℝ)
  hρinf : (0 : ℝ) < c.params.rhoInf
  hρinfρ : (c.params.rhoInf : ℝ) < c.params.rho
  hM : (0 : ℝ) < c.params.M
  hσK : (0 : ℝ) < c.params.σK
  hσB : (0 : ℝ) < c.params.σB
  hσT : (0 : ℝ) < c.params.σT
  hμ : (0 : ℝ) < c.params.μ
  hγbar : (0 : ℝ) < c.params.γbar
  hσω : (1 : ℝ) < c.params.σω
  hν : (0 : ℝ) < c.params.nuRay
  hωstar : ωstar ≠ 0
  hopen : IsOpen c.D
  htransl : ∀ z ∈ c.D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ c.D
  hholo : DifferentiableOn ℂ c.H c.D
  hper : ∀ z ∈ c.D, ∀ k : Fin n → ℤ, c.H (z.1 + (fun i => (k i : ℂ)), z.2) = c.H z
  hreal : ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ c.D →
    (c.H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0
  hbd : ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧ ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
    ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
    ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M
  hK : DifferentiableOn ℂ c.K (complexStrip n c.params.rho)
  hKp : IsPrimaryOnStrip c.K c.params.rho
  hKr : IsRealOnReals c.K
  hball : ∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D
  hDK : ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ
  hG : ∀ θ ∈ complexStrip n c.params.rho, IsUnit (gramMatrix c.K θ).det ∧
    ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ
  hTu : IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det
  hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
    (c.params.σT : ℝ) - c.params.μ
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hν1 : (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖ωstar‖
  hν2 : (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hE : ∀ θ ∈ complexStrip n c.params.rho,
    ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err
  hEn : ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err
  hC1 : Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1
  hdisp : Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp

/-- The output of the black box: the conclusion of `IG1Body` for the denoted data, with the
explicit rational displacement bound `disp` in place of `C₂ e/(γ²ρ^{2τ})`. -/
def CertifiedTorus (c : TorusCertificate n α) (ωstar : Fin n → ℝ) : Prop :=
  ∃ (Kinf : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (sinf : ℝ),
    1 < sinf ∧ sinf < c.params.σω ∧ DifferentiableOn ℂ Kinf (complexStrip n c.params.rhoInf) ∧
    IsPrimaryOnStrip Kinf c.params.rhoInf ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, invarianceError c.H Kinf (sinf • ωstar) θ = 0) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, c.H (Kinf θ) = ((c.params.E0 : ℝ) : ℂ)) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, Metric.ball (Kinf θ) ((c.params.μ : ℝ) / 2) ⊆ c.D) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf,
      ‖fderiv ℂ Kinf θ‖ ≤ (c.params.σK : ℝ) - (c.params.μ : ℝ) / 2) ∧
    (∀ θ ∈ complexStrip n c.params.rhoInf, ‖Kinf θ - c.K θ‖ ≤ c.params.disp) ∧
    ‖sinf • ωstar - (c.params.s : ℝ) • ωstar‖ ≤ c.params.disp

/-! ### Sub-check contracts (`KAM/Certificate/Sound/*.lean`, finding F3)

Acyclic assembly: Static → (structural H, K) → HamBounds → Embedding → {Gram, Invariance,
Energy} → Torsion (uses Gram) → Smallness. Every `G1Hyps` field is produced by exactly one
contract below. -/

/-- The `ω`-free static facts. -/
structure StaticFacts (c : TorusCertificate n α) : Prop where
  hn : 2 ≤ n
  hτ : (n : ℝ) - 1 ≤ (c.params.tau : ℝ)
  hρinf : (0 : ℝ) < c.params.rhoInf
  hρinfρ : (c.params.rhoInf : ℝ) < c.params.rho
  hM : (0 : ℝ) < c.params.M
  hσK : (0 : ℝ) < c.params.σK
  hσB : (0 : ℝ) < c.params.σB
  hσT : (0 : ℝ) < c.params.σT
  hμ : (0 : ℝ) < c.params.μ
  hγbar : (0 : ℝ) < c.params.γbar
  hσω : (1 : ℝ) < c.params.σω
  hν : (0 : ℝ) < c.params.nuRay
  hs1 : (1 : ℝ) < c.params.s
  hsσ : (c.params.s : ℝ) < c.params.σω
  hγ : (0 : ℝ) < c.params.γ
  hγγbar : (c.params.γ : ℝ) ≤ c.params.γbar
  he0 : (0 : ℝ) ≤ c.params.err
  hrho : c.weight.rho = c.params.rho
  hW : checkWeight c.weight c.expHalvings c.expOrder = true
  hWH : checkWeight c.weightH c.expHalvings c.expOrder = true
  hpe : checkPiEnclosure c.piEnc = true

variable [LawfulCertArith α]

theorem checkStatic_sound {c : TorusCertificate n α} (h : checkStatic c = true) :
    StaticFacts c := sorry

/-- The `ω`-dependent static facts, for every `ω` in the box. -/
theorem checkStatic_freq {c : TorusCertificate n α} (h : checkStatic c = true)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ωstar ≠ 0 ∧ (c.params.nuRay : ℝ) ≤ ((c.params.s : ℝ) - 1) * ‖ωstar‖ ∧
      (c.params.nuRay : ℝ) ≤ ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := sorry

/-- Structural facts of `K` (law-free). -/
theorem TorusCertificate.emb_structural (c : TorusCertificate n α) :
    DifferentiableOn ℂ c.K (complexStrip n c.params.rho) ∧ IsPrimaryOnStrip c.K c.params.rho ∧
      IsRealOnReals c.K := sorry

theorem checkHamBounds_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkHamBounds c = true) :
    c.ham.NonvanishingOn c.D ∧ ∀ z ∈ c.D, ‖fderiv ℂ c.H z‖ ≤ c.params.M ∧
      ‖hamiltonianVectorFieldℂ c.H z‖ ≤ c.params.M ∧
      ‖fderiv ℂ (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 (hamiltonianVectorFieldℂ c.H) z‖ ≤ c.params.M ∧
      ‖iteratedFDeriv ℂ 2 c.H z‖ ≤ c.params.M := sorry

/-- Structural facts of `H` on `D`, given the certified denominators. -/
theorem TorusCertificate.ham_structural (c : TorusCertificate n α)
    (hnv : c.ham.NonvanishingOn c.D) :
    IsOpen c.D ∧ (∀ z ∈ c.D, ∀ k : Fin n → ℤ, (z.1 + (fun i => (k i : ℂ)), z.2) ∈ c.D) ∧
      DifferentiableOn ℂ c.H c.D ∧
      (∀ z ∈ c.D, ∀ k : Fin n → ℤ, c.H (z.1 + (fun i => (k i : ℂ)), z.2) = c.H z) ∧
      ∀ θ I : Fin n → ℝ, ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ))) ∈ c.D →
        (c.H ((fun i => (θ i : ℂ)), (fun i => (I i : ℂ)))).im = 0 := sorry

theorem checkEmbedding_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkEmbedding c = true) :
    (∀ θ ∈ complexStrip n c.params.rho, Metric.ball (c.K θ) c.params.μ ⊆ c.D) ∧
      ∀ θ ∈ complexStrip n c.params.rho, ‖fderiv ℂ c.K θ‖ ≤ (c.params.σK : ℝ) - c.params.μ :=
  sorry

theorem checkGram_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkGram c = true) : ∀ θ ∈ complexStrip n c.params.rho,
      IsUnit (gramMatrix c.K θ).det ∧
        ∀ i, ∑ j, ‖(gramMatrix c.K θ)⁻¹ i j‖ ≤ (c.params.σB : ℝ) - c.params.μ := sorry

theorem checkInvariance_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true)
    (h : checkInvariance c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err := sorry

theorem checkEnergy_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (h : checkEnergy c = true) :
    ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err := sorry

/-- Assembled from `torsionModels_sound` (with `D := c.D`, `hKD` from `checkEmbedding_sound`,
`hnv` from `checkHamBounds_sound`, `hG` from `checkGram`) and `torsionAvgCheck_sound` at the
certificate's own `n` (`torsionAvgCheck n`, exact shapes, F7). -/
theorem checkTorsion_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (hh : checkHamBounds c = true) (he : checkEmbedding c = true) (hg : checkGram c = true)
    (h : checkTorsion c = true) {ωstar : Fin n → ℝ} (hω : FreqEncloses n c.freqBox ωstar) :
    IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar)).det ∧
      ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤
        (c.params.σT : ℝ) - c.params.μ := sorry

theorem checkSmallness_sound {c : TorusCertificate n α} (hs : checkStatic c = true)
    (h : checkSmallness c = true) :
    Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT c.params.μ c.params.nuRay c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1 ∧
    Iso.Apost.isoC2 n c.params.tau c.params.rho c.params.rhoInf c.params.M c.params.σK
      c.params.σB c.params.σT * c.params.err /
      ((c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ))) ≤ c.params.disp :=
  sorry

/-- All hypotheses of `g1_explicit` from a passing check and a frequency in the box. -/
theorem checkTorusCertificate_hyps {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) : G1Hyps c ωstar := sorry

/-- **The black box.** A passing certificate, an exact reference vector `ωstar` in its box, and a
proved Diophantine input yield an exact analytic invariant torus `K_∞` within `disp` of `K`,
through the sealed `KAM.Iso.Apost.g1_explicit` instantiated at
`(n, τ, ρ, ρ∞, M, σK, σB, σT, μ, γbar, σω, ν, ω*) := (n, c.tau, c.rho, c.rhoInf, c.M, c.σK, c.σB,
c.σT, c.μ, c.γbar, c.σω, c.nuRay, ωstar)` and applied to
`(D, H, K, s, γ, e, E₀) := (c.D, c.H, c.K, c.s, c.γ, c.err, c.E0)`. -/
theorem checkTorusCertificate_sound {c : TorusCertificate n α}
    (h : checkTorusCertificate c = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) : CertifiedTorus c ωstar :=
  sorry

end Black

/-! ## §H. The clock lemma: `clock_frequency` is LANDED (`KAM/Certificate/Clock.lean`, imported). -/

/-! ## §J. A nonresonant `n = 3` frequency and the toys (`KAM/Certificate/Tests/*`; finding F1
example, finding F4). `cbrtTwo`, `cubicFreq`, `cubicFreq_eq_algFreq` and
`cubicFreq_isDiophantine` are LANDED (`KAM/Certificate/CubicDiophantine.lean`, SO-DIO3). The toys
use the `direct` product advice (§B′). -/

/-- Toy Hamiltonian `I₂ + I₀²/2 + I₁²/2` (isoenergetically nondegenerate; no perturbation). -/
def toyHam3 : HamExpr 3 :=
  .add (.action 2) (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
    (.mul (.const (1 / 2)) (.pow (.action 1) 2)))

/-- Toy T3: `K(θ) = (θ, (a, b, -(a² + b²)/2))` with RATIONAL `a ≈ ∛2`, `b ≈ ∛4`
(`|a - ∛2|, |b - ∛4| ≤ 10^{-N}`, `N` fixed by `isoC1Q` at `n = 3`, `τ = 2`), `s = 2`, a box of
`cubicFreq` of radius `≤ 10^{-N}`; the residual budget `err ≥ |(a, b) - 2 ω*|` is positive. -/
def toyCert3 : TorusCertificate 3 ℚ := sorry

theorem toyCert3_ham : toyCert3.ham = toyHam3 := sorry

theorem toyCert3_err_pos : 0 < toyCert3.params.err := sorry

theorem toyCert3_passes : checkTorusCertificate toyCert3 = true := sorry

theorem toyCert3_freq : FreqEncloses 3 toyCert3.freqBox cubicFreq := sorry

/-- The genuine `n = 3` black-box application (external Diophantine premise discharged). -/
theorem toyCert3_torus : CertifiedTorus toyCert3 cubicFreq := sorry

/-- Toy T2: `H = J + p²/2`, `K(θ) = (θ, (ν̃, -ν̃²/2))` with rational `ν̃ ≈ ν₋`, reference vector
`(ν₋/2, 1/2)` (SO-DIO), positive residual. Toy T2d: the same with `H` written with a division,
`J + (p²/2)·((3 + cos 2πq)/(3 + cos 2πq))` (exercises O2). -/
def toyCert2 : TorusCertificate 2 ℚ := sorry

def toyCert2d : TorusCertificate 2 ℚ := sorry

theorem toyCert2_passes : checkTorusCertificate toyCert2 = true := sorry

theorem toyCert2d_passes : checkTorusCertificate toyCert2d = true := sorry

theorem toyCert2_torus : CertifiedTorus toyCert2 ![lunarNuMinus / 2, 1 / 2] := sorry

theorem toyCert2d_torus : CertifiedTorus toyCert2d ![lunarNuMinus / 2, 1 / 2] := sorry

/-- Checker-only test (NO Diophantine premise exists: its rational reference vector `(1/4, 1/2)`
is resonant): zero error, exact rational `ν = 1/2`. It exercises the checker only. -/
def toyRatCert : TorusCertificate 2 ℚ := sorry

theorem toyRatCert_passes : checkTorusCertificate toyRatCert = true := sorry

/-! ### Range-reduction tests (`KAM/Certificate/Tests/ComplexExp.lean`, SO-CEXP; Revision 4):
`s = 0` small (passes) and large (`‖z‖ + r = 3/2`, rejected); the audit's centre `z = 2` rejected
at `s = 0` and accepted at `s = 2`; a large imaginary pin `2πi k·U(0) ≈ 19i` at `s = 5`. -/

theorem cexpTest_zero_small : (certCExpReduced (⟨1 / 2, 0⟩ : CC ℚ) 0 0 8).isSome = true := sorry

theorem cexpTest_zero_large : certCExpReduced (⟨1, 0⟩ : CC ℚ) (1 / 2) 0 8 = none := sorry

theorem cexpTest_two_rejected : certCExpReduced (⟨2, 0⟩ : CC ℚ) 0 0 8 = none := sorry

theorem cexpTest_two_reduced : (certCExpReduced (⟨2, 0⟩ : CC ℚ) 0 2 8).isSome = true := sorry

theorem cexpTest_large_pin : (certCExpReduced (⟨0, 19⟩ : CC ℚ) (1 / 1000) 5 12).isSome = true :=
  sorry

end KAM.Certificate


end
```

### A-L. `SOSignaturesLunar.lean` (lunar client), verbatim

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Arith.Rat
public import KAM.Certificate.Arith.Fixed
public import KAM.Certificate.Arith.PiEnclosure
public import KAM.Certificate.Model.Basic
public import KAM.Certificate.Expr.Basic
public import KAM.Certificate.Freq
public import KAM.Certificate.Clock
public import KAM.Certificate.QuadraticDiophantine
public import KAM.SpinOrbit.HamExpr
public import KAM.SpinOrbit.Freq
public import KAM.SpinOrbit.Barrier
public import KAM.SpinOrbit.Graph.Inverse

/-!
# SO-DESIGN Revision 5: exact draft signatures, lunar-client part (track SO)

Design document: `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (Appendix A is this file together with
the engine file `SOSignatures.lean`). Every proof and every non-trivial definition body is
`sorry`; the file only fixes the Lean surface and is never imported.

It imports the LANDED SO modules it consumes (`SpinOrbit/{Model,Hamiltonian,HamExpr,Freq,
Barrier,Graph/Inverse}`, `Certificate/{Clock,Freq,QuadraticDiophantine,Expr/Basic,Model/Basic,
Arith/Rat,Arith/Fixed}`). Two blocks are STAND-INS, so that the file elaborates on its own against
the shared `inp` build. §I.0b restates SO-ROTDIO's five orchestrator-fixed declarations
(`KAM/Certificate/DiophantineTransfer.lean`, proving) verbatim. §I.0 holds the engine
declarations the client names (`CertParams`, `TorusCertificate` and the types of its fields, the
sub-checks and `checkTorusCertificate`), copied VERBATIM from `SOSignatures.lean`
(`docs/tracks/SO/design/check_so_standins.py` compares them byte for byte). SO-GRAPHM's generic
core (`SoGraph.Torus`, `SoGraph.realPt`, `soBarrier_of_torus`, `soBarrier_of_exact_torus`) is
LANDED and imported.

Owner ruling O5 (2026-10-29, 14:20): the lunar client works in the ROTATED frame
`Q₀ = q - φ`, `Q₁ = φ`, `P₀ = p`, `P₁ = p + J` (linear, symplectic, unimodular), with
`H' = P₀²/2 - P₀ + P₁ + V(Q₀ + Q₁, Q₁)`, reference frequency `(ν - 1, 1)` and the parameter
package R1. The original-frame declarations (`soHamExpr`, landed; `soBarrier_of_cert`) stay
valid; the headline route goes through the rotated ones. The final statements are unchanged.
-/

@[expose] public noncomputable section

namespace KAM.Certificate

open KAM KAM.Torus CertArith

/-! ## §I.0 STAND-IN: engine declarations used by the client (verbatim from `SOSignatures.lean`) -/

/-- An exp witness: the polynomial `E ≈ exp g₀` and the pin's halving count and Taylor order
(certificate data, chosen by the generator from the size of `g₀(0)`). -/
structure ExpWitness (α : Type) where
  poly : CertPoly α
  pinHalvings : ℕ
  pinOrder : ℕ

/-- The embedding `K(θ) = (θ + (2π)^{dU_i} U_i(θ), (2π)^{dA_i} A_i(θ))` from real Fourier data;
a missing component denotes `0` (no backend default value is used, finding F2). -/
structure CertEmbedding (α : Type) where
  angleDeg : List ℤ
  angle : List (CertRealPoly α)
  actionDeg : List ℤ
  action : List (CertRealPoly α)

/-- Witnesses: one per `exp` slot and one per `inv` slot of the jet program (slot order), and
the character table keyed by the normalized index (coordinates with syntactically zero `U_j`
zeroed; `-k` uses `conjReflect`). Exp and character witnesses are `ExpWitness`es: each carries
its own pin halving count and order, and its pin `exp(2πi k·U(0))` (characters) or
`exp g₀(0)` goes through `certCExpReduced` (Revision 4, F10). -/
structure Witnesses (α : Type) where
  expWit : List (ExpWitness α)
  invWit : List (CertPoly α)
  charWit : List (CertKey × ExpWitness α)

/-- A dense box layout of Fourier keys `lo ≤ k < lo + dims` (mixed radix, row-major with the
row strides `stride`), slot width `width` and shard block size `blockRows` (rows). -/
structure PackLayout where
  lo : CertKey
  dims : List ℕ
  stride : List ℕ
  width : ℕ
  blockRows : ℕ

/-- Design-B advice for ONE real product (integers only): the two factor layouts, the result
box (`target`, a sub-box of the product window), the rounding scale, the rounded in-box result
of each output shard window (in units `2^scale`), and the log-bound of out-of-box slots. -/
structure PackedAdvice where
  la : PackLayout
  lb : PackLayout
  target : PackLayout
  scale : ℕ
  rounded : List (List ℤ)
  outLog : ℕ

/-- Advice for one model product: `packed` (four real packed products at mantissa scale `P`) or
`direct` (the direct product of Revision 4; tests and the `ℚ` toys). -/
inductive ProductAdvice : Type
  | direct
  | packed (P : ℕ) (rr ii ri ir : PackedAdvice)

/-- The checker's name of a product: `[site, i, j, …]`, assigned deterministically by the call
site (§7: compose 0, exp witnesses 1, reciprocal witnesses 2, Gram 3, torsion 4, invariance 5,
energy 6, SOS 7, graph 8). The generator emits the advice under the same keys. -/
abbrev ProductKey : Type := List ℕ

abbrev AdviceBook : Type := List (ProductKey × ProductAdvice)

/-- Truncation/precision controls and the product advice (Revision 5: indexed by the backend
for the mantissa decoder). -/
structure ModelConfig (α : Type) where
  /-- keep only product terms with `|k|₁ ≤ cutoff` -/
  cutoff : ℕ
  /-- Taylor order and halvings of the REAL upper bounds `ratExpUp` (`exp(2B)`, `exp(B)`,
  `exp(η) - 1`); complex pins carry their own counts (`ExpWitness`, Revision 4) -/
  taylorN : ℕ
  halvings : ℕ
  /-- untrusted mantissa decoder (`CertFixed.toMant P` in production); every value it returns is
  re-verified by `mantCheck` -/
  toMant : ℕ → α → Option ℤ
  /-- the advice of every product of the stage this configuration drives (§B′) -/
  advice : AdviceBook

/-- Parameters of `g1_explicit` (exact rationals; `τ ∈ ℕ`). `nuRay` is the theorem's `ν`. -/
structure CertParams where
  tau : ℕ
  rho : ℚ
  rhoInf : ℚ
  M : ℚ
  σK : ℚ
  σB : ℚ
  σT : ℚ
  μ : ℚ
  γbar : ℚ
  σω : ℚ
  nuRay : ℚ
  γ : ℚ
  s : ℚ
  err : ℚ
  E0 : ℚ
  /-- claimed explicit displacement bound, checked `≥ isoC2Q e / (γ² ρ^{2τ})` -/
  disp : ℚ

/-- The certificate: problem data, numerical witnesses and controls (data only; no proofs, no
real numbers). -/
structure TorusCertificate (n : ℕ) (α : Type) where
  params : CertParams
  ham : HamExpr n
  /-- `D = T_{ρ_H} × polydisc(centre, radius)` -/
  weightH : CertWeight
  centre : List ℚ
  radius : List ℚ
  /-- rational box of the reference vector `ω*` -/
  freqBox : FreqBox
  emb : CertEmbedding α
  /-- weight of the strip `T_ρ` (its `rho` must equal `params.rho`) -/
  weight : CertWeight
  wit : Witnesses α
  gramInv : List (List (CertPoly α))
  torsInv : List (List (CC α))
  cfgFull : ModelConfig α
  cfgLow : ModelConfig α
  piEnc : PiEnclosure α
  expHalvings : ℕ
  expOrder : ℕ

/-- Shapes (`box.length = n`, list lengths), positivity, `2 ≤ n`, `n - 1 ≤ τ`, `ρ∞ < ρ`,
`1 < s < σω`, `γ ≤ γbar`, `0 ≤ e`, `weight.rho = rho`, both weights, the `π` enclosure, the box
excludes `0` in some coordinate, and the ray margins against the box's lower bound of `‖ω*‖`. -/
def checkStatic {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- Ball arithmetic of the jet on `D` (every denominator certified) and the five bounds
`‖DH‖, ‖X_H‖, ‖DX_H‖, ‖D²X_H‖, ‖D²H‖ ≤ M` on `D`. -/
def checkHamBounds {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `ball (K θ) μ ⊆ D` on `T_ρ` and `‖DK‖ ≤ σK - μ` (row sums of `DK` models). -/
def checkEmbedding {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `sup_{T_ρ} ‖X_H(K) - DK (s ω)‖ ≤ e` at full precision, uniformly for `ω` in the box. -/
def checkInvariance {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `‖⟨H ∘ K⟩ - E₀‖ ≤ e` (zero mode of the composed model ± radius). -/
def checkEnergy {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- The Gram certificate (`gramCheck`) with bound `σB - μ`. -/
def checkGram {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `torsionModels` at `s` and the box, then `torsionAvgCheck n` (exact `(n+1)×(n+1)` shapes of
`T` and the witness `c.torsInv`) with bound `σT - μ`. -/
def checkTorsion {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool := sorry

/-- `isoC1Q e < γ⁴ ρ^{4τ}` and `isoC2Q e ≤ disp γ² ρ^{2τ}`. -/
def checkSmallness {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  sorry

/-- **The black-box checker.** -/
def checkTorusCertificate {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α) : Bool :=
  checkStatic c && checkHamBounds c && checkEmbedding c && checkInvariance c && checkEnergy c &&
    checkGram c && checkTorsion c && checkSmallness c

end KAM.Certificate

/-! ## §I.0b STAND-IN: SO-ROTDIO (`KAM/Certificate/DiophantineTransfer.lean`, proving; signatures
FIXED by the orchestrator, adopted VERBATIM, `sorry` bodies) -/

namespace KAM.Certificate

/-- Diophantine transfer along an integer change of the index: if every nonzero `k` has a nonzero
image `T k` with the same small divisor against `ω` and `|T k|₁ ≤ C |k|₁`, then `ω'` is
`(γ / C ^ τ, τ)`-Diophantine. -/
theorem isDiophantine_of_index_map {n m : ℕ} {γ τ C : ℝ} {ω : Fin n → ℝ} {ω' : Fin m → ℝ}
    (hω : IsDiophantine γ τ ω) (hγ : 0 ≤ γ) (hτ : 0 ≤ τ) (hC : 0 < C)
    (T : (Fin m → ℤ) → (Fin n → ℤ)) (hT : ∀ k, k ≠ 0 → T k ≠ 0)
    (hdot : ∀ k, ∑ i, (T k i : ℝ) * ω i = ∑ j, (k j : ℝ) * ω' j)
    (hnorm : ∀ k, ∑ i, |(T k i : ℝ)| ≤ C * ∑ j, |(k j : ℝ)|) :
    IsDiophantine (γ / C ^ τ) τ ω' := sorry

/-- The rotated lunar frequency `(ν₋ - 1, 1)` (owner ruling O5). -/
theorem lunarNuMinus_rot_isDiophantine : IsDiophantine (1 / 42) 1 ![lunarNuMinus - 1, 1] := sorry

/-- The rotated lunar frequency `(ν₊ - 1, 1)` (owner ruling O5). -/
theorem lunarNuPlus_rot_isDiophantine : IsDiophantine (1 / 42) 1 ![lunarNuPlus - 1, 1] := sorry

/-- The rotated isoenergetic reference vector `((ν₋ - 1)/2, 1/2)`. -/
theorem lunarNuMinus_rot_half_isDiophantine :
    IsDiophantine (1 / 84) 1 ![(lunarNuMinus - 1) / 2, 1 / 2] := sorry

/-- The rotated isoenergetic reference vector `((ν₊ - 1)/2, 1/2)`. -/
theorem lunarNuPlus_rot_half_isDiophantine :
    IsDiophantine (1 / 84) 1 ![(lunarNuPlus - 1) / 2, 1 / 2] := sorry

end KAM.Certificate

namespace KAM.SpinOrbit

open KAM KAM.Certificate

/-! ## §I.1 SO-GRAPHM (LANDED, `KAM/SpinOrbit/Graph/Inverse.lean`, `inp` 95c9bd7f): the generic
core `SoGraph.Torus` (frequency parameter `ν`, clock offset `c`), `SoGraph.realPt`,
`soBarrier_of_torus` and the original-frame wrapper `soBarrier_of_exact_torus` are imported. -/

/-! ## §I.2 The rotated frame (`KAM/SpinOrbit/Rotated.lean`, package SO-ROT; owner ruling O5)

LANDED, unchanged (original frame): `soHC`, `soHamExpr`, `soHamExpr_eval`, `soHamExpr_clock`
(`SpinOrbit/{Hamiltonian,HamExpr}`). The rotated frame is a client-side choice of `H` and `K`;
the black box and its theorem are unchanged. -/

/-- The linear symplectic unimodular change of variables from the rotated coordinates
`((Q₀, Q₁), (P₀, P₁))` to the original `((q, φ), (p, J)) = ((Q₀ + Q₁, Q₁), (P₀, P₁ - P₀))`. -/
def soRotMap (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![z.1 0 + z.1 1, z.1 1], ![z.2 0, z.2 1 - z.2 0])

/-- Its inverse `((q, φ), (p, J)) ↦ ((q - φ, φ), (p, p + J))`. -/
def soRotMapInv (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (![z.1 0 - z.1 1, z.1 1], ![z.2 0, z.2 0 + z.2 1])

theorem soRotMapInv_soRotMap (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soRotMapInv (soRotMap z) = z :=
  sorry

theorem soRotMap_soRotMapInv (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soRotMap (soRotMapInv z) = z :=
  sorry

/-- Symplectic: the angle block `A = [[1, 1], [0, 1]]` and the action block
`B = [[1, 0], [-1, 1]]` satisfy `Aᵀ B = I`, so `Σ_i (u_Q v_P - u_P v_Q)_i` is preserved. -/
theorem soRotMap_symplectic (u v : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    ∑ i, ((soRotMap u).1 i * (soRotMap v).2 i - (soRotMap u).2 i * (soRotMap v).1 i) =
      ∑ i, (u.1 i * v.2 i - u.2 i * v.1 i) := sorry

/-- `H' = soHC ∘ soRotMap = P₀²/2 - P₀ + P₁ + V(Q₀ + Q₁, Q₁)`. -/
def soRotHC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : ℂ := soHC (soRotMap z)

/-- `X_{H ∘ L} = L⁻¹ X_H ∘ L` for the symplectic `L` (rows `(q - φ, φ, p, p + J)` of `X_H`). -/
theorem hamiltonianVectorFieldℂ_soRotHC (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    hamiltonianVectorFieldℂ soRotHC z = soRotMapInv (hamiltonianVectorFieldℂ soHC (soRotMap z)) :=
  sorry

/-- `H'` in the expression language: `P₁ + (P₀²/2 - P₀) + Σ_m (-ε A_m) cos(2π(2Q₀ + (2 - m)Q₁))`
(mode `(2, 2 - m)`, `m = 1, …, 7`; the `m = 2` mode is independent of `Q₁`). Division-free. -/
def soRotHamExpr : HamExpr 2 :=
  .add (.action 1) (.add (.add (.mul (.const (1 / 2)) (.pow (.action 0) 2))
      (.mul (.const (-1)) (.action 0)))
    ((List.range 7).foldr (fun m acc =>
      .add (.mul (.const (-soEpsQ * soAQ (m + 1))) (.cosMode [2, 1 - (m : ℤ)])) acc)
      (.const 0)))

/-- **Evaluation identity**: `soRotHamExpr` denotes the landed `soHC` composed with `soRotMap`. -/
theorem soRotHamExpr_eval (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) : soRotHamExpr.eval z = soRotHC z :=
  sorry

/-- The clock direction `P₁` (`inr 1`): `∂_{P₁} H' ≡ 1`. -/
theorem soRotHamExpr_clock (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ soRotHamExpr.eval z (phaseBasis (.inr 1)) = 1 := sorry

/-- The time-scaled client Hamiltonian `c · H'` (package R1: `c = 237/125`, SO-GEN2). -/
def soRotHamExprScaled (c : ℚ) : HamExpr 2 := .mul (.const c) soRotHamExpr

theorem soRotHamExprScaled_eval (c : ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    (soRotHamExprScaled c).eval z = (c : ℂ) * soRotHC z := sorry

theorem soRotHamExprScaled_clock (c : ℚ) (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    fderiv ℂ (soRotHamExprScaled c).eval z (phaseBasis (.inr 1)) = c := sorry

/-- Time scaling: `invarianceError (c H) K ω = c · invarianceError H K (c⁻¹ ω)` (`c ≠ 0`; both
sides use `fderiv`, so no differentiability premise is needed). -/
theorem invarianceError_const_mul {n : ℕ} {c : ℝ} (hc : c ≠ 0)
    (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))
    (ω : Fin n → ℝ) (θ : Fin n → ℂ) :
    invarianceError (fun z => (c : ℂ) * H z) K ω θ = (c : ℂ) • invarianceError H K (c⁻¹ • ω) θ :=
  sorry

/-! ## §I.3 Rotated frequencies (`KAM/SpinOrbit/RotFreq.lean`, package SO-RFREQ)

`ω* = κ (ν± - 1, 1)` with `κ = c/s` (time scale over ray scalar), so that the torus frequency of
the scaled client is `s ω* = c (ν± - 1, 1)` and the clock gives `s∞ = s`. Exact `ℚ(√5)` boxes via
the landed `algFreq_encloses`; Diophantine constants from SO-ROTDIO (§I.0b, orchestrator-fixed:
`isDiophantine_of_index_map` with `T k = (k₀, k₁ - k₀)`, `C = 2`, applied to the landed SO-DIO):
`γ(ν - 1, 1) = 1/42` at `τ = 1`, hence `γ(ω*) = κ/42`. -/

/-- The rotated reference vector `κ (ν - 1, 1)`. -/
def lunarRotFreq (ν : ℝ) (κ : ℚ) : Fin 2 → ℝ := ![(κ : ℝ) * (ν - 1), κ]

theorem lunarRotFreqMinus_eq (κ : ℚ) :
    lunarRotFreq lunarNuMinus κ = algFreq 2 [[-79 * κ / 3118, κ / 3118], [κ]] (Real.sqrt 5) :=
  sorry

theorem lunarRotFreqPlus_eq (κ : ℚ) :
    lunarRotFreq lunarNuPlus κ = algFreq 2 [[79 * κ / 3118, -κ / 3118], [κ]] (Real.sqrt 5) :=
  sorry

/-- Positive scaling of a Diophantine vector. -/
theorem soIsDiophantine_smul {n : ℕ} {γ τ t : ℝ} {ω : Fin n → ℝ} (ht : 0 < t)
    (h : IsDiophantine γ τ ω) : IsDiophantine (t * γ) τ (t • ω) := sorry

/-- From SO-ROTDIO's `lunarNuMinus_rot_isDiophantine` (`1/42`) and `soIsDiophantine_smul`. -/
theorem lunarRotFreqMinus_isDiophantine {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 42) 1 (lunarRotFreq lunarNuMinus κ) := sorry

theorem lunarRotFreqPlus_isDiophantine {κ : ℚ} (hκ : 0 < κ) :
    IsDiophantine ((κ : ℝ) / 42) 1 (lunarRotFreq lunarNuPlus κ) := sorry

/-! ## §I.4 The lunar parameter package R1 (`KAM/SpinOrbit/LunarParams.lean`, package SO-R1)

CONSTANTS-STUDY §2.2 and §4, owner ruling O5: `ρ' = 1/70`, `ρ∞ = ρ'/1000`, `μ = 1/160`, ray
scalar `s = 1 + 10⁻⁶`, `ν = 10⁻⁶`, `σω = 2`, time scale `c = 237/125`, one majorant
`𝔪 = M = σK = σB = σT = 1987/1000` (Revision 6: SO-GEN2's measured package; binding `σB`, the
weighted-ℓ¹ Gram inverse bound 1.97994), `γ = γ̄ = c/(42 s)`, `τ = 1`, `E₀ = 0`. Enclosed
threshold `10^{-74.669}`. The residual budget `err` and the displacement `disp` of each torus are
named placeholders filled by SO-DATA (from SO-GEN2: `e ≈ 2 c η`, 4.03e-78 / 7.84e-78). -/

def lunarR1TimeScale : ℚ := 237 / 125

def lunarR1Scalar : ℚ := 1 + 1 / 10 ^ 6

/-- `κ = c/s`: the reference vectors are `lunarRotFreq ν± κ`. -/
def lunarR1Kappa : ℚ := lunarR1TimeScale / lunarR1Scalar

/-- The R1 parameters for a residual budget `err` and a displacement bound `disp`. -/
def lunarR1 (err disp : ℚ) : CertParams where
  tau := 1
  rho := 1 / 70
  rhoInf := 1 / 70000
  M := 1987 / 1000
  σK := 1987 / 1000
  σB := 1987 / 1000
  σT := 1987 / 1000
  μ := 1 / 160
  γbar := lunarR1Kappa / 42
  σω := 2
  nuRay := 1 / 10 ^ 6
  γ := lunarR1Kappa / 42
  s := lunarR1Scalar
  err := err
  E0 := 0
  disp := disp

theorem lunarR1Kappa_div : lunarR1Kappa / 42 = 316000 / 7000007 := sorry

/-- Placeholders (SO-DATA; literal rationals before the freeze). -/
def lunarLowerErr : ℚ := sorry

def lunarUpperErr : ℚ := sorry

def lunarLowerDisp : ℚ := sorry

def lunarUpperDisp : ℚ := sorry

/-! ## §I.5 Graph certificates and barriers (`KAM/SpinOrbit/Graph/{Inverse,Rot,Cert}.lean`) -/

/-- Graph data checked on top of a passing torus certificate: a monotonicity margin `mono` for
`∂_{θ₀}` of the angle component `(.1 0)` (checked with the strict margin `mono > disp/ρ∞`), the
range `[pLo, pHi]` of the action component `(.2 0)` on the real torus, and the SOS witnesses
with their certified centres. Frame-free: in the original frame `(.1 0) = q`, in the rotated
frame `(.1 0) = Q₀ = q - φ` (same monotonicity in `θ₀`); in both `(.2 0) = p`. -/
structure SoGraphCert (α : Type) where
  base : TorusCertificate 2 α
  mono : ℚ
  mono₀ : ℚ
  pLo : ℚ
  pLo₀ : ℚ
  pHi : ℚ
  pHi₀ : ℚ
  sosMono : CertPoly α
  sosLo : CertPoly α
  sosHi : CertPoly α

def checkSoGraph {α : Type} [CertArith α] (g : SoGraphCert α) : Bool := sorry

namespace SoGraph

/-- **Shear** `(x, y) ↦ (x - y, y)`: rotated real data (`Q₁` the angle `Q₀`, `Pp` the momentum
`P₀ = p`, clock `φ = y + c`, flow at `(ν - 1, 1)`) give the generic core's data at `(ν, 1)`:
`q = Q₀ + Q₁`, i.e. `Q x y = Q₁ (x - y) y + y + c`, `Pp x y = Pp (x - y) y`. -/
theorem torus_of_rot {Q₁ Pp dQ : ℝ → ℝ → ℝ} {ν c m : ℝ} (hm : 0 < m)
    (hQc : Continuous fun z : ℝ × ℝ => Q₁ z.1 z.2) (hPc : Continuous fun z : ℝ × ℝ => Pp z.1 z.2)
    (hQ₀ : ∀ x y, Q₁ (x + 1) y = Q₁ x y + 1) (hQ₁ : ∀ x y, Q₁ x (y + 1) = Q₁ x y)
    (hP₀ : ∀ x y, Pp (x + 1) y = Pp x y) (hP₁ : ∀ x y, Pp x (y + 1) = Pp x y)
    (hdQ : ∀ x y, HasDerivAt (fun s => Q₁ s y) (dQ x y) x) (hmono : ∀ x y, m ≤ dQ x y)
    (hflowQ : ∀ x y, HasDerivAt (fun t => Q₁ (x + t * (ν - 1)) (y + t)) (Pp x y - 1) 0)
    (hflowP : ∀ x y, HasDerivAt (fun t => Pp (x + t * (ν - 1)) (y + t))
      (-soVq (Q₁ x y + y + c) (y + c)) 0) :
    Torus (fun x y => Q₁ (x - y) y + y + c) (fun x y => Pp (x - y) y)
      (fun x y => dQ (x - y) y) ν c m := sorry

end SoGraph

open SoGraph in
/-- **Rotated-frame exact torus ⇒ barrier** (SO-GRAPHR). `K∞` is the black box's exact torus for
the scaled client `c · H'`, invariant at `s∞ ω*` with `s∞ ω*` Diophantine. With
`∂_{θ₀} Q₀ ≥ m > 0` and `P₀ ∈ [lo, hi]` on the real torus: `invarianceError_const_mul` and
`soIsDiophantine_smul` move to `H'` at `(s∞/c) ω*`; the landed `clock_frequency` (with
`soRotHamExpr_clock`) gives `Q₁ = θ₁ + c₀` and `(s∞/c) ω*₁ = 1`; `hamiltonianVectorFieldℂ_soRotHC`
gives the real flow `d/dt Q₀ = P₀ - 1`, `d/dt P₀ = -∂_q V(Q₀ + Q₁, Q₁)` at `(ν - 1, 1)`,
`ν = (s∞/c) ω*₀ + 1`; `torus_of_rot` and `soBarrier_of_torus` give the barrier in
`(q, p, φ) = (Q₀ + Q₁, P₀, Q₁)`. -/
theorem soBarrier_of_exact_rotTorus {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {ρ sinf γ τ m lo hi : ℝ} {c : ℚ} (hc : 0 < c) {ωstar : Fin 2 → ℝ} (hρ : 0 < ρ)
    (hholo : DifferentiableOn ℂ Kinf (complexStrip 2 ρ)) (hprim : IsPrimaryOnStrip Kinf ρ)
    (hreal : IsRealOnReals Kinf)
    (hinv : ∀ θ ∈ complexStrip 2 ρ,
      invarianceError (soRotHamExprScaled c).eval Kinf (sinf • ωstar) θ = 0)
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ (sinf • ωstar)) (hm : 0 < m)
    (hmono : ∀ x y : ℝ, m ≤ ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re)
    (hlo : ∀ x y : ℝ, lo ≤ ((Kinf (realPt x y)).2 0).re)
    (hhi : ∀ x y : ℝ, ((Kinf (realPt x y)).2 0).re ≤ hi) :
    Nonempty (SoBarrier lo hi) := sorry

/-- The barrier from a passing ORIGINAL-frame certificate (Revision 2; retained, valid, not on
the headline route). The band is widened by `disp`. -/
theorem soBarrier_of_cert {α : Type} [CertArith α] [LawfulCertArith α] (g : SoGraphCert α)
    (hham : g.base.ham = soHamExpr) (hc : checkTorusCertificate g.base = true)
    (hg : checkSoGraph g = true) {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  sorry

/-- **The barrier from a passing ROTATED-frame certificate** (Revision 5): black box
(`checkTorusCertificate_sound`), graph transfer (`checkSoGraph`, Cauchy on `T_{ρ∞}`, frame-free),
then `soBarrier_of_exact_rotTorus`. The band is widened by `disp`. -/
theorem soRotBarrier_of_cert {α : Type} [CertArith α] [LawfulCertArith α] (g : SoGraphCert α)
    {c : ℚ} (hc0 : 0 < c) (hham : g.base.ham = soRotHamExprScaled c)
    (hc : checkTorusCertificate g.base = true) (hg : checkSoGraph g = true)
    {ωstar : Fin 2 → ℝ} (hω : FreqEncloses 2 g.base.freqBox ωstar)
    (hdio : IsDiophantine (g.base.params.γ : ℝ) (g.base.params.tau : ℝ) ωstar) :
    Nonempty (SoBarrier ((g.pLo : ℝ) - g.base.params.disp) ((g.pHi : ℝ) + g.base.params.disp)) :=
  sorry

/-! ## §I.6 The lunar certificates and the final theorems (`KAM/SpinOrbit/Lunar*.lean`)

Barrier and confinement: `SoBarrier`, `so_global_exists_unique`, `so_confinement` are LANDED
(`SpinOrbit/Barrier`, SO-CONF). Data enters through generated modules
`KAM/SpinOrbit/Data/{Lower,Upper}/*` (design §7.2: chunked data modules, each below the 1500-line
cap; the line-width policy for generated data is an OWNER decision). -/

/-- The mantissa precision of the production backend: a named placeholder (SO-GEN2 measured
318 bits at R1, L = 88; the literal, with guard bits, is set by SO-DATA before the freeze). -/
def soPrecision : ℕ := 320

/-- The production backend: fixed point (SO-REPLAY recommendation; LANDED `CertFixed`, SO-ABK). -/
abbrev SoBackend : Type := CertFixed soPrecision

/-- Generated data; bodies are the generated terms. -/
def lunarLowerCert : SoGraphCert SoBackend := sorry

def lunarUpperCert : SoGraphCert SoBackend := sorry

theorem lunarLowerCert_ham :
    lunarLowerCert.base.ham = soRotHamExprScaled lunarR1TimeScale := sorry

theorem lunarUpperCert_ham :
    lunarUpperCert.base.ham = soRotHamExprScaled lunarR1TimeScale := sorry

theorem lunarLowerCert_params :
    lunarLowerCert.base.params = lunarR1 lunarLowerErr lunarLowerDisp := sorry

theorem lunarUpperCert_params :
    lunarUpperCert.base.params = lunarR1 lunarUpperErr lunarUpperDisp := sorry

theorem lunarLowerCert_passes : checkTorusCertificate lunarLowerCert.base = true := sorry

theorem lunarUpperCert_passes : checkTorusCertificate lunarUpperCert.base = true := sorry

theorem lunarLowerGraph_passes : checkSoGraph lunarLowerCert = true := sorry

theorem lunarUpperGraph_passes : checkSoGraph lunarUpperCert = true := sorry

/-- From `lunarRotFreqMinus_eq`, `algFreq_encloses` and `sqrt_mem_of_checkRootEnclosure`. -/
theorem lunarLowerCert_freq :
    FreqEncloses 2 lunarLowerCert.base.freqBox (lunarRotFreq lunarNuMinus lunarR1Kappa) := sorry

theorem lunarUpperCert_freq :
    FreqEncloses 2 lunarUpperCert.base.freqBox (lunarRotFreq lunarNuPlus lunarR1Kappa) := sorry

/-- The certified initial momentum window (ruling O1; literal rationals before the freeze). -/
def lunarPLo : ℚ := sorry

def lunarPHi : ℚ := sorry

theorem lunarPLo_lt_lunarPHi : lunarPLo < lunarPHi := sorry

/-- **Theorem A (continuous form).** Two invariant barrier graphs inside the 3.3% band
(unchanged by O5: `P₀ = p`). -/
theorem lunar_barriers :
    ∃ (Bm : SoBarrier (967 / 1000) (1033 / 1000)) (Bp : SoBarrier (967 / 1000) (1033 / 1000)),
      (∀ q φ, Bm.P q φ < Bp.P q φ) ∧
      (∀ q φ, Bm.P q φ < lunarPLo) ∧ (∀ q φ, (lunarPHi : ℝ) < Bp.P q φ) := sorry

/-- **Theorem B.** Every initial state with `lunarPLo < p₀ < lunarPHi` has a unique global
solution, and `|p(t) - 1| ≤ 33/1000` for all real `t` (unchanged by O5). -/
theorem lunar_spin_confinement (q₀ p₀ φ₀ : ℝ) (hp : (lunarPLo : ℝ) < p₀ ∧ p₀ < lunarPHi) :
    ∃ z : ℝ → ℝ × ℝ × ℝ, (z 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt z (soField (z t)) t) ∧
      (∀ t, |(z t).2.1 - 1| ≤ 33 / 1000) ∧
      ∀ y : ℝ → ℝ × ℝ × ℝ, (y 0 = (q₀, p₀, φ₀) ∧ ∀ t, HasDerivAt y (soField (y t)) t) →
        y = z := sorry

end KAM.SpinOrbit

end
```
