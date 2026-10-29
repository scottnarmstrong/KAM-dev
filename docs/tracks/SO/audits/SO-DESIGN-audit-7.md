# SO-DESIGN independent audit 7 — Revision 7

2026-10-29. **Overall verdict: PASS WITH NOTES for design acceptance. F14 and F15 are closed at design level. No new blocking finding.** This is not a proof-package PASS or a seal receipt: the two transient signature files still contain 184 `sorry` bodies. No SO theorem, passing lunar certificate, or confinement result has been proved by this revision.

Existing I-G1 is SEALED and unchanged. No new provider or frozen anchor is supplied; no track N/P anchor is affected. The permitted design placeholders must not be installed as production Lean modules.

## Scope and authority

Report destination: `/root/code/KAM-inp-design-so/docs/tracks/SO/audits/SO-DESIGN-audit-7.md`, as explicitly requested, overriding the generic brief's main-worktree destination. Only this report was written in repository content; all auditor probes/logs were confined to this worktree's `.lake/abi-scratch/so-audit7/` and removed after transcription. No state-changing git command, implementation edit, frozen edit, generated-root regeneration, or memory edit was performed.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the Round 7 focus in `SO-DESIGN-handoff.md`, audit 6 and its finding history, `.drafts/handoff-SO-DESIGN.md` Revision 7, the current design, and both complete draft signature surfaces. Consulted the controlling `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` (D30 and O1–O5), proposal, pilot, SO-REPLAY2 study, and shared inp's SO-GEN2 report. Engine comparison uses frozen `IsoenergeticKam.lean`, the frozen open strip, Gram, normal-frame, extended-torsion/average and energy-average definitions, `KAM/Iso/Charts/Inputs.lean`, `KAM/Iso/Apost/G1.lean`, track I statement, and blueprint-I `bpI:p0:g1` / `bpI:p2:g1`. The SO design is an unfrozen surface, not a new approved track statement.

Audited HEAD `9af1fbe6e8c123e770cc8bfec6fa1483ca7ea1da`; observed `inp` and the shared signature/build checkout at `23a055ed6eaa23e4cc5d0d57c6f3c7c42cabdd32`. Scope command `git diff inp...HEAD`: nine added files, 5,507 insertions, zero deletions (audits 1–6, handoff, design, stand-in checker). No production Lean is in this diff. Reviewed the substantive design surface and the exact Revision 7 delta with `git diff d965c152..HEAD -- docs/tracks/SO/design/SO-LEAN-DESIGN.md`; prior audits are historical evidence. Protected-path diff is empty.

## Numbered findings and closure

### F14 — CLOSED at design level: raw factors and exact output length are attached

Locations: design Revision 7 table (line 76), Appendix A-E lines 1217–1310; engine draft lines 340–431; validation §8 P5 at design lines 772–776.

The repaired whole-check description now explicitly checks the RAW `da.length = la.denseLen`, `db.length = lb.denseLen`, and positivity of both lengths. `checkPackedProduct_guards` exports all four facts from success; they are not caller premises. `PackedAdvice.prodLen` is the concrete natural-number expression `la.denseLen + lb.denseLen - 1`. `combined` is specified as overlap-add, zero-extension, then cropping to exactly this length; `combined_length` is unconditional in the advice. `listConv_length` applies only to nonempty factors, exactly as required by the actual landed `listConv` body.

A fresh Lean proof `audit7_length` derives the literal first conjunct of `checkPackedProduct_sound` using only the new guards, `combined_length`, `prodLen` and `listConv_length`; it does not call `checkPackedProduct_sound`. This elaborates at default budgets. It depends on `sorryAx` through draft contracts, so it verifies interface composition, not the algorithms. Independently, `SOAudit7.landed_listConv_length` proves the new convolution-length contract directly from the landed SO-POLY-A definition, with only `[propext, Quot.sound]`.

For audit 6's two-slot layout, `[0]` and `[0,0]` still have identical padded blocks, but only `[0,0]` has raw length two. `audit7_padding_reject` derives rejection of the short call for every advice whose left dense length is two. This is stronger than checking one numeric instance of the placeholder checker. The short raw convolution has length one and the long one length three, independently decided against landed `listConv`.

**Empty inputs:** `audit7_empty_left` and `audit7_empty_right` derive unconditional rejection from the exported positive lengths, including the case where both lists are empty. A zero-extent layout is specified to have `denseLen = 0`; raw-shape equality plus positivity therefore rejects every raw factor on that layout. Zero polynomials remain representable by an all-zero list on a nonempty box or the direct route. An empty `dims` list is a dimension-zero layout, distinct from a positive-dimensional box containing a zero extent; the existing dimension/compatibility tests govern that case. No restriction to nonempty callers was added to the public soundness theorem.

**Attempt to recover an indistinguishable pair:** at fixed valid layouts, every accepted input has the same canonical raw lengths. Cutting into positive-size blocks with only terminal zero-padding preserves all entries of those fixed-length lists: recover them by flattening and taking the known raw length. Thus identical cut data cannot identify distinct accepted raw inputs. Trailing zero insertions/deletions change raw length and fail the new tests. Empty factors fail before shard processing. Cropping changes no retained slot; high advice is separately checked zero, and the exact padded convolution's extra tail is zero. The positive-scale, anti-carry and at-most-two-overlap guards from F12/F13 remain in force. No new alias survives this argument.

An independent Python specification control checked 49,185 raw inputs (coefficients −1, 0, 1; lengths 0–6; canonical lengths 0–8; block lengths 1–5): 5,460 met the positive canonical-length tests and no distinct accepted lists had identical padded cuts. This is a finite control of the specified shape/cut behavior, not execution of the unfinished Lean checker. Independent `crop_extend_length` proves `(xs ++ replicate n 0).take n` has length `n` for arbitrary lists and natural `n`, showing the unconditional cropping contract is implementable even on malformed advice.

**Implementation obligations retained:** define `denseLen` and `dense` consistently on the whole carrier (reject malformed layouts or use the documented canonical formula); prove `dense_length`; implement zero-extension before `take`, not `take` alone; enforce all raw/empty guards inside the checker; prove the overlap-add and Fourier-layout glue; execute P5 in SO-TEST. Their `sorry` bodies are disclosed design debt, not a reason to claim that P5 already executes. No required design change remains for F14.

### F15 — CLOSED: B₀ now carries the time scale

Location: design §6 lines 540–549; shared `docs/tracks/SO/studies/SO-GEN2-rotated-frame-candidates.md:157–175`.

The design retains `B₀ = c · sup|ΔP₁|` and now explicitly labels SO-GEN2's values as unscaled `sup|ΔJ|`, multiplying by `c = 237/125`. The two displayed inputs give `2.37e-80` and `4.34184e-80`; they are below `e/4 = 1.0075e-78` and `1.96e-78`. Exact rational controls establish the factors and these strict comparisons after a common `1e-80` scaling. The printed `4.34e-80` is marked approximate; it is not an outward-rounded bound and must not be copied as an upper endpoint into SO-DATA. This closes the requested documentation repair. No claim of literal interval-certified numerical data follows.

### Earlier findings and new issues

F12/F13 remain closed at design level: `reconFits` bounds both reconstructed signed digits and residual allowance, `shardFits` bounds the exact side, and injectivity is applied at equal lengths. Positive scale pays the sum of at most two local errors; scale zero remains rejected. Revision 7 changes no reconstruction or slot-bound type. F1–F11's adopted interfaces are unchanged. **No new blocking issue was found.** The stale Revision 6 results explicitly labelled in §9 and historical package statuses do not override the fresh receipts below.

## Focus, engine fidelity and anchor verdicts

| Node / anchor / focus | Verdict | Assessment |
|---|---|---|
| F14 canonical raw shape, cropping, empty factors | PASS WITH NOTES | Sound repaired design; fresh interface proof and landed convolution-length proof; checker implementation/P5 unpaid. |
| `checkPackedProduct_sound` | PASS WITH NOTES | Literal type unchanged; its sole explicit premise is `checkPackedProduct adv da db = true`; no raw-shape or coefficient conclusion moved to callers. |
| SO-POLY-A stability | PASS | No production declaration changed; 6 mantissa and 12 packed declaration headers match the landed surface after whitespace normalization. |
| F15 B₀ units | PASS | Multiplied by `237/125`; margins survive. Approximate decimals remain feasibility summaries. |
| Existing I-G1 | PASS WITH NOTES | SEALED and unchanged; independent bridge has only permitted axioms; targeted build and kernel replay recorded below. No new seal requested. |
| New SO anchors / tracks N and P | N/A | No anchor/provider supplied. |
| General checker and lunar client design | PASS WITH NOTES | Both signatures elaborate, exact appendix/stand-ins agree; unproved checker, witnesses, data, toys and confinement remain unpaid. |

Fresh `audit7_engine_bridge` applies `.2.2.2` of `g1_explicit` to `(c.D,c.H,c.K,c.params.s,c.params.γ,c.params.err,c.params.E0)` with the literal `G1Hyps` field order. Its axiom set is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. In particular the reference is the external exact `ωstar`, the approximate frequency is `s • ωstar`, `ν = nuRay`, and `isoC1` uses the order `μ, ν, γbar`. Both closeness conclusions use the same explicit `isoC2`; `hdisp` weakens both bounds by transitivity.

| Literal engine binder group | Supplier and assessment |
|---|---|
| n≥2; τ≥n−1; 0<ρ∞<ρ; positive M, σK, σB, σT, μ, γbar; σω>1; ν>0 | Static facts, matching rational/natural casts. |
| Nonzero exact ωstar and both endpoint inequalities | Static frequency facts plus the external `FreqEncloses` fact. |
| Open translation-invariant D; holomorphic, periodic, real H | Structural domain/language facts after certified denominator nonvanishing. |
| Five H/XH derivative bounds on D | Ball arithmetic and jets, norm bridges using n≥1 from n≥2. |
| Holomorphic, primary, real K; μ-ball containment; DK bound | Structural Fourier embedding and embedding check. |
| Bilinear Gram invertibility and inverse row sums on Tρ | Gram check; no Hermitian replacement. |
| Bordered averaged torsion unit and row sums at sωstar | Exact (n+1)×(n+1) shape, literal torsion producer, entrywise averaging, constant approximate inverse. |
| Ray scalar 1<s<σω and two ν margins | Static/frequency contracts. |
| γ>0; γ≤γbar; Diophantine ωstar; e≥0 | Static facts and external `IsDiophantine`. |
| Invariance and average-energy errors; C₁ smallness | Respective sub-check contracts, at the same H/K/domain/frequency. |
| Two `disp` conclusions | Checked `hdisp` and `C₂=C₃`. |

`G1Hyps` packages conclusions to be produced by the checks; it is not a certificate field or an external assumption of `checkTorusCertificate_sound`. That theorem also requires the exact frequency's rational enclosure and a lawful arithmetic instance, as disclosed, besides Diophantine input. No hidden torus/proof field was found. The frozen strip is OPEN, matching the model semantics; no closed-strip extrapolation is needed for I-G1. Real averaging occurs on a compact cube inside the positive-width strip, with continuity explicitly supplied. The Gram matrix is bilinear on complex points and is certified by a uniform defect, not positivity. The derivative-of-inverse and bordered last row are the literal frozen ones.

The general carrier remains arbitrary n≥2, HamExpr with certified division, and Fourier data in all embedding components. A finite checker need not accept every possible candidate; rejection/fallback is sound and does not weaken the enclosure of the exact product. The n=3 algebraic-frequency toy remains proposed and unproved. O5's symplectic map keeps `P₀=p`, so the unchanged lunar theorem targets the original `33/1000` band and the O1 constant momentum window. Fourier approximation of the energy lift has its nonzero energy/derivative errors paid on the actual candidate. Continuous graphs are the O4 scope; analytic graph/conjugacy statements remain deferred. Literal endpoints, complete finite data, end-to-end replay and the final theorem are not delivered here.

Package/DAG feasibility remains conditional: replay GO is a benchmark, not a finished full-certificate replay. Layout and overlap-add proofs, arithmetic error budgets, torsion models, and generated-data packaging remain the significant work. SO-POLY-B may require additional focused modules; the 1500-line cap is unchanged. This round adds six declarations without changing the landed SO-POLY-A interfaces. No new dependency cycle or owner ruling was introduced.

## Input integrity, signature gates and hygiene

Both files are byte-identical to the shared `/root/code/KAM-inp/.drafts/design/` copies and to their respective Appendix A code blocks. The lunar appendix is byte-identical to Revision 6. Current SHA-256:

| Input | SHA-256 |
|---|---|
| `.drafts/design/SOSignatures.lean` | `9a4652019186e914a0ccfdba6e01c903e458b679d0c057ac4cf7b7d353a4c1cc` |
| `.drafts/design/SOSignaturesLunar.lean` | `f898ee080a52c631387764a2b7d1ab18e2df79b50442b18e5e05aa43f3209c6c` |
| Audit 6 | `8530622d1a4d22329c11cc9888bd9b93af3237f8027b039e83520c37329994dd` |
| Shared landed `Certificate/Arith/Mantissa.lean` | `e261dbdf28b3ceb4fa78c73656d3737427bc814a78862a02f326152c9e93fb9e` |
| Shared landed `Certificate/Poly/Packed.lean` | `7f7ed7f499168a8091230ee88a46d48f7095d5e625dc1cfde04add0328bb2948` |

The proposal, pilot and replay-study hashes match the design's recorded pins. The only changed existing signature HEADER since Revision 6 is `checkPackedProduct_guards` (four raw-shape conjuncts). Six new declarations are `PackLayout.denseLen`, `PackLayout.dense_length`, `listConv_length`, `PackedAdvice.prodLen`, `PackedAdvice.combined_length`, and `checkPackedProduct_raw_length`. Other changes are documentation. The supplied draft continues to restate some now-landed SO-POLY-A declarations; their draft axiom debt is not the landed module's axiom set.

Commands, all sequential with `LEAN_NUM_THREADS=1` and `nice -n 5` inside the gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignaturesLunar.lean
```

Both exit **0**: engine **130 warnings**, lunar **54 warnings**, all exactly `declaration uses 'sorry'`; no errors. Both have copyright/module/public-import/docstring/public-section form; 1185 and 540 lines, respectively. Comment-stripped source checks found no `axiom`, `admit`, `unsafe`, `opaque`, `EuclideanSpace`, `native_decide` or `set_option` overrides. `sorry` counts are 130 and 54, acceptable only for this expressly transient design gate, never as production hygiene.

```sh
python3 -I docs/tracks/SO/design/check_so_standins.py .drafts/design/SOSignatures.lean .drafts/design/SOSignaturesLunar.lean
```

Exit **0**, exact output:

```text
stand-ins checked: 20 (ExpWitness, CertEmbedding, Witnesses, PackLayout, PackedAdvice, ProductAdvice, ProductKey, AdviceBook, ModelConfig, CertParams, TorusCertificate, checkStatic, checkHamBounds, checkEmbedding, checkInvariance, checkEnergy, checkGram, checkTorsion, checkSmallness, checkTorusCertificate)
.drafts/design/SOSignatures.lean: 1185 lines; lines over 100 chars: none
.drafts/design/SOSignaturesLunar.lean: 540 lines; lines over 100 chars: none
PASS
```

Targeted build (shared landed checkout, as used by the signature gate; this design worktree has no new Lean modules):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp KAM.Iso.Apost.G1 KAM.Certificate.Poly.Packed KAM.Certificate.Expr.Diff KAM.Certificate.Clock KAM.SpinOrbit.HamExpr KAM.SpinOrbit.Graph.Inverse
```

Exit **0**, exact output (cached dependency warnings included):

```text
[inp-gate] slot 1 acquired 15:40:42 for KAM.Iso.Apost.G1 KAM.Certificate.Poly.Packed KAM.Certificate.Expr.Diff KAM.Certificate.Clock KAM.SpinOrbit.HamExpr KAM.SpinOrbit.Graph.Inverse
⚠ [3248/3283] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one

Hint: Omit it from the simp argument list.
  [apply] simp [div_eq_mul_inv]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [3256/3283] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hS

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [3277/3283] Replayed KAM.ODE.Exit
warning: KAM/ODE/Exit.lean:36:0: automatically included section variable(s) unused in theorem `KAM.ODE.gen_exit`:
  [NormedSpace ℝ E]
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit [NormedSpace ℝ E] in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
Build completed successfully (3283 jobs).
```

Kernel replay from `/root/code/KAM-inp`:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1 KAM.Certificate.Poly.Packed KAM.Certificate.Arith.Mantissa KAM.Certificate.Expr.Diff KAM.Certificate.Clock KAM.SpinOrbit.HamExpr KAM.SpinOrbit.Graph.Inverse
```

Exit **0**, exact output:

```text
replaying KAM.SpinOrbit.Graph.Inverse
replaying KAM.SpinOrbit.HamExpr
replaying KAM.Certificate.Clock
replaying KAM.Certificate.Expr.Diff
replaying KAM.Certificate.Arith.Mantissa
replaying KAM.Certificate.Poly.Packed
replaying KAM.Iso.Apost.G1
```

The unchanged engine/provider type is already SEALED; there is no new provider export or proposed seal body to check in this design revision. The independent bridge tests literal engine consumption rather than treating a signature-only soundness theorem as a proof.

## Declaration-by-declaration assessment and definition classification

PWN = **PASS WITH NOTES for design only**. ALG = specified algorithm with placeholder body; DEN = concrete denotation/check; DATA = untrusted data/configuration or representation alias; PROP = derived/semantic proposition; ENDPOINT = literal/generated data still unpaid. None of these labels certifies an unfinished body. Missing components use literal zero; matrices require present entries and exact shapes; invalid advice is rejected or yields the documented coarse enclosure. The new empty packed-factor rejection is explicit. Every top-level draft declaration is listed: 166 engine and 79 lunar entries, including 20 repeated engine stand-ins. The table's line numbers refer to the draft paths above; appendix blocks are byte-identical.

### Engine A-E

| Draft line / node | Declaration | Verdict | Classification / assessment |
|---|---|---|---|
| 93 | `KAM.Certificate.mantCheck` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 96 | `KAM.Certificate.mantCheck_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 101 | `KAM.Certificate.ofDyadic` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 105 | `KAM.Certificate.ofDyadic_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 110 | `KAM.Certificate.CertFixed.toMant` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 116 | `KAM.Certificate.CertFixed.mantCheck_m` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 124 | `KAM.Certificate.cexpHalvings` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 129 | `KAM.Certificate.certCExpReduced_cexpHalvings_isSome` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 141 | `KAM.Certificate.CertPoly.shift` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 143 | `KAM.Certificate.CertPoly.eval_shift` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 148 | `KAM.Certificate.CertPoly.conjReflect` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 150 | `KAM.Certificate.CertPoly.eval_conjReflect` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 172 | `KAM.Certificate.packSum` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 177 | `KAM.Certificate.packShift` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 180 | `KAM.Certificate.packShift_eq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 183 | `KAM.Certificate.SlotsBounded` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 186 | `KAM.Certificate.packSum_injective` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 191 | `KAM.Certificate.listConv` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 195 | `KAM.Certificate.packSum_listConv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 200 | `KAM.Certificate.convFits` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 202 | `KAM.Certificate.slotsBounded_listConv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 207 | `KAM.Certificate.packSum_flatten_mul_shards` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 216 | `KAM.Certificate.intSlotsBound` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 218 | `KAM.Certificate.intSlotsBound_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 225 | `KAM.Certificate.PackLayout` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 233 | `KAM.Certificate.PackLayout.slot` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 236 | `KAM.Certificate.PackLayout.dense` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 239 | `KAM.Certificate.PackLayout.prodKey` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 243 | `KAM.Certificate.PackLayout.compat` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 246 | `KAM.Certificate.intEval` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 251 | `KAM.Certificate.PackLayout.intEval_mul` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 262 | `KAM.Certificate.PackedAdvice` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 280 | `KAM.Certificate.reconSlots` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 283 | `KAM.Certificate.packSum_reconSlots` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 288 | `KAM.Certificate.reconFits` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 291 | `KAM.Certificate.slotsBounded_reconSlots` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 298 | `KAM.Certificate.shardConv` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 300 | `KAM.Certificate.shardConv_length` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 304 | `KAM.Certificate.packSum_shardConv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 312 | `KAM.Certificate.shardFits` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 314 | `KAM.Certificate.slotsBounded_shardConv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 321 | `KAM.Certificate.shard_reconstruct` | PWN | Correct local reconstruction; independent composition elaborates; lower-level proofs unpaid. |
| 332 | `KAM.Certificate.PackedAdvice.blockLen` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 335 | `KAM.Certificate.PackedAdvice.cut` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 337 | `KAM.Certificate.PackedAdvice.cut_length` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 343 | `KAM.Certificate.PackLayout.denseLen` | PWN | ALG: canonical slot length; zero on zero-extent boxes; whole-carrier layout consistency to be implemented. |
| 345 | `KAM.Certificate.PackLayout.dense_length` | PWN | PWN: exact dense length on successful densification; implementation/proof unpaid. |
| 348 | `KAM.Certificate.listConv_length` | PWN | PWN: nonempty length contract independently proved against landed listConv; draft body unpaid. |
| 353 | `KAM.Certificate.PackedAdvice.prodLen` | PWN | DEN: concrete la.denseLen + lb.denseLen - 1; positivity comes from success guards. |
| 356 | `KAM.Certificate.PackedAdvice.shardLogs` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 362 | `KAM.Certificate.PackedAdvice.combined` | PWN | ALG: overlap-add, zero-extend, crop to prodLen; F14 closed in specification. |
| 364 | `KAM.Certificate.PackedAdvice.combined_length` | PWN | PWN: unconditional exact length; zero-extension before cropping makes contract implementable. |
| 368 | `KAM.Certificate.PackedAdvice.inBox` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 375 | `KAM.Certificate.PackedAdvice.shapeOK` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 381 | `KAM.Certificate.checkShard` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 384 | `KAM.Certificate.checkShard_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 396 | `KAM.Certificate.checkPackedProduct` | PWN | ALG: includes positive canonical raw lengths, shape/shard guards; F14 closed in specification. |
| 399 | `KAM.Certificate.checkPackedProduct_guards` | PWN | PWN: success exports canonical raw lengths and positivity plus all former guards. |
| 408 | `KAM.Certificate.checkPackedProduct_scale_zero` | PWN | Correct unconditional scale-zero rejection contract; implementation/proof unpaid. |
| 413 | `KAM.Certificate.checkPackedProduct_raw_length` | PWN | PWN: internal rejection for either wrong raw length; draft body unpaid. |
| 424 | `KAM.Certificate.checkPackedProduct_sound` | PWN | PWN: sole premise is checker success; exact-length conjunct independently assembled; full proof unpaid. |
| 433 | `KAM.Certificate.packSum_audit5_cancel` | PASS | Concrete F12 control, proved by `decide`; axioms `[propext]`. |
| 435 | `KAM.Certificate.reconFits_audit5_rejects` | PASS | Concrete F12 control, proved by `decide`; axioms `[propext]`. |
| 439 | `KAM.Certificate.CertPoly.toMants` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 442 | `KAM.Certificate.CertPoly.toMants_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 453 | `KAM.Certificate.CertPoly.mulPacked` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 457 | `KAM.Certificate.CertPoly.mulPacked_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 466 | `KAM.Certificate.ProductAdvice` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 473 | `KAM.Certificate.ProductKey` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 475 | `KAM.Certificate.AdviceBook` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 484 | `KAM.Certificate.ModelConfig` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 497 | `KAM.Certificate.CertModel.add` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 506 | `KAM.Certificate.CertModel.mul` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 510 | `KAM.Certificate.CertModel.trim` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 514 | `KAM.Certificate.CertModel.toDeg` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 519 | `KAM.Certificate.CertModel.ofDeriv` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 522 | `KAM.Certificate.CertModel.Encloses.ofDeriv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 527 | `KAM.Certificate.CertModel.Encloses.add` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 532 | `KAM.Certificate.CertModel.Encloses.mul` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 538 | `KAM.Certificate.CertModel.Encloses.trim` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 543 | `KAM.Certificate.CertModel.Encloses.toDeg` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 549 | `KAM.Certificate.CertModel.Encloses.average` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 576 | `KAM.Certificate.ExpWitness` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 583 | `KAM.Certificate.expPinBall` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 585 | `KAM.Certificate.expPinBall_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 591 | `KAM.Certificate.expWitnessRadius` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 596 | `KAM.Certificate.expWitnessRadius_pin` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 602 | `KAM.Certificate.expWitness_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 610 | `KAM.Certificate.invWitnessRadius` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 613 | `KAM.Certificate.invWitness_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 635 | `KAM.Certificate.Slp.balls` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 638 | `KAM.Certificate.Slp.val_mem_ball` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 646 | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 653 | `KAM.Certificate.CertEmbedding` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 659 | `KAM.Certificate.CertEmbedding.eval` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 666 | `KAM.Certificate.CertEmbedding.differentiable_eval` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 669 | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 673 | `KAM.Certificate.CertEmbedding.isRealOnReals` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 681 | `KAM.Certificate.Witnesses` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 688 | `KAM.Certificate.Slp.compose` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 693 | `KAM.Certificate.Slp.compose_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 711 | `KAM.Certificate.ModelMatrix` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 715 | `KAM.Certificate.ModelMatrix.Encloses` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 723 | `KAM.Certificate.polyMatrix` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 728 | `KAM.Certificate.gramModels` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 731 | `KAM.Certificate.gramModels_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 739 | `KAM.Certificate.gramCheck` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 743 | `KAM.Certificate.gramCheck_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 754 | `KAM.Certificate.torsionIdx` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 761 | `KAM.Certificate.torsionModels` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 770 | `KAM.Certificate.torsionModels_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 788 | `KAM.Certificate.torsionAvgCheck` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 792 | `KAM.Certificate.torsionAvgCheck_shape` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 796 | `KAM.Certificate.torsionAvgCheck_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 809 | `KAM.Certificate.checkRealLowerBound` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 812 | `KAM.Certificate.checkRealLowerBound_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 832 | `KAM.Certificate.CertParams` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 853 | `KAM.Certificate.TorusCertificate` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 878 | `KAM.Certificate.TorusCertificate.D` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 881 | `KAM.Certificate.TorusCertificate.H` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 883 | `KAM.Certificate.TorusCertificate.K` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 893 | `KAM.Certificate.checkStatic` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 897 | `KAM.Certificate.checkHamBounds` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 900 | `KAM.Certificate.checkEmbedding` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 903 | `KAM.Certificate.checkInvariance` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 906 | `KAM.Certificate.checkEnergy` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 909 | `KAM.Certificate.checkGram` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 913 | `KAM.Certificate.checkTorsion` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 916 | `KAM.Certificate.checkSmallness` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 920 | `KAM.Certificate.checkTorusCertificate` | PWN | Verbatim engine stand-in. DEN/check: concrete body reviewed on its whole carrier. |
| 930 | `KAM.Certificate.G1Hyps` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 983 | `KAM.Certificate.CertifiedTorus` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 1002 | `KAM.Certificate.StaticFacts` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 1027 | `KAM.Certificate.checkStatic_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1031 | `KAM.Certificate.checkStatic_freq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1037 | `KAM.Certificate.TorusCertificate.emb_structural` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1041 | `KAM.Certificate.checkHamBounds_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1050 | `KAM.Certificate.TorusCertificate.ham_structural` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1058 | `KAM.Certificate.checkEmbedding_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1064 | `KAM.Certificate.checkGram_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1069 | `KAM.Certificate.checkInvariance_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1075 | `KAM.Certificate.checkEnergy_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1082 | `KAM.Certificate.checkTorsion_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1089 | `KAM.Certificate.checkSmallness_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1100 | `KAM.Certificate.checkTorusCertificate_hyps` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1110 | `KAM.Certificate.checkTorusCertificate_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1126 | `KAM.Certificate.toyHam3` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 1133 | `KAM.Certificate.toyCert3` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1135 | `KAM.Certificate.toyCert3_ham` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1137 | `KAM.Certificate.toyCert3_err_pos` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1139 | `KAM.Certificate.toyCert3_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1141 | `KAM.Certificate.toyCert3_freq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1144 | `KAM.Certificate.toyCert3_torus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1149 | `KAM.Certificate.toyCert2` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1151 | `KAM.Certificate.toyCert2d` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1153 | `KAM.Certificate.toyCert2_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1155 | `KAM.Certificate.toyCert2d_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1157 | `KAM.Certificate.toyCert2_torus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1159 | `KAM.Certificate.toyCert2d_torus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1163 | `KAM.Certificate.toyRatCert` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1165 | `KAM.Certificate.toyRatCert_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1171 | `KAM.Certificate.cexpTest_zero_small` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1173 | `KAM.Certificate.cexpTest_zero_large` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1175 | `KAM.Certificate.cexpTest_two_rejected` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1177 | `KAM.Certificate.cexpTest_two_reduced` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1179 | `KAM.Certificate.cexpTest_large_pin` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |

### Lunar A-L

| Draft line / node | Declaration | Verdict | Classification / assessment |
|---|---|---|---|
| 56 | `KAM.Certificate.ExpWitness` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 63 | `KAM.Certificate.CertEmbedding` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 74 | `KAM.Certificate.Witnesses` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 81 | `KAM.Certificate.PackLayout` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 91 | `KAM.Certificate.PackedAdvice` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 101 | `KAM.Certificate.ProductAdvice` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 108 | `KAM.Certificate.ProductKey` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 110 | `KAM.Certificate.AdviceBook` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 114 | `KAM.Certificate.ModelConfig` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 128 | `KAM.Certificate.CertParams` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 149 | `KAM.Certificate.TorusCertificate` | PWN | Verbatim engine stand-in. DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 173 | `KAM.Certificate.checkStatic` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 177 | `KAM.Certificate.checkHamBounds` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 180 | `KAM.Certificate.checkEmbedding` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 183 | `KAM.Certificate.checkInvariance` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 186 | `KAM.Certificate.checkEnergy` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 189 | `KAM.Certificate.checkGram` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 193 | `KAM.Certificate.checkTorsion` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 196 | `KAM.Certificate.checkSmallness` | PWN | Verbatim engine stand-in. ALG: intended operation reviewed; implementation and correctness unpaid. |
| 200 | `KAM.Certificate.checkTorusCertificate` | PWN | Verbatim engine stand-in. DEN/check: concrete body reviewed on its whole carrier. |
| 214 | `KAM.Certificate.isDiophantine_of_index_map` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 222 | `KAM.Certificate.lunarNuMinus_rot_isDiophantine` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 225 | `KAM.Certificate.lunarNuPlus_rot_isDiophantine` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 228 | `KAM.Certificate.lunarNuMinus_rot_half_isDiophantine` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 232 | `KAM.Certificate.lunarNuPlus_rot_half_isDiophantine` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 253 | `KAM.SpinOrbit.soRotMap` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 257 | `KAM.SpinOrbit.soRotMapInv` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 260 | `KAM.SpinOrbit.soRotMapInv_soRotMap` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 263 | `KAM.SpinOrbit.soRotMap_soRotMapInv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 268 | `KAM.SpinOrbit.soRotMap_symplectic` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 273 | `KAM.SpinOrbit.soRotHC` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 276 | `KAM.SpinOrbit.hamiltonianVectorFieldℂ_soRotHC` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 282 | `KAM.SpinOrbit.soRotHamExpr` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 290 | `KAM.SpinOrbit.soRotHamExpr_eval` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 294 | `KAM.SpinOrbit.soRotHamExpr_clock` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 298 | `KAM.SpinOrbit.soRotHamExprScaled` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 300 | `KAM.SpinOrbit.soRotHamExprScaled_eval` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 303 | `KAM.SpinOrbit.soRotHamExprScaled_clock` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 308 | `KAM.SpinOrbit.invarianceError_const_mul` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 323 | `KAM.SpinOrbit.lunarRotFreq` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 325 | `KAM.SpinOrbit.lunarRotFreqMinus_eq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 329 | `KAM.SpinOrbit.lunarRotFreqPlus_eq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 334 | `KAM.SpinOrbit.soIsDiophantine_smul` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 338 | `KAM.SpinOrbit.lunarRotFreqMinus_isDiophantine` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 341 | `KAM.SpinOrbit.lunarRotFreqPlus_isDiophantine` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 353 | `KAM.SpinOrbit.lunarR1TimeScale` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 355 | `KAM.SpinOrbit.lunarR1Scalar` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 358 | `KAM.SpinOrbit.lunarR1Kappa` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 361 | `KAM.SpinOrbit.lunarR1` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 379 | `KAM.SpinOrbit.lunarR1Kappa_div` | PWN | Updated rational value independently proved; draft proof still unpaid. |
| 382 | `KAM.SpinOrbit.lunarLowerErr` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 384 | `KAM.SpinOrbit.lunarUpperErr` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 386 | `KAM.SpinOrbit.lunarLowerDisp` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 388 | `KAM.SpinOrbit.lunarUpperDisp` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 397 | `KAM.SpinOrbit.SoGraphCert` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 409 | `KAM.SpinOrbit.checkSoGraph` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 416 | `KAM.SpinOrbit.SoGraph.torus_of_rot` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 438 | `KAM.SpinOrbit.soBarrier_of_exact_rotTorus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 452 | `KAM.SpinOrbit.soBarrier_of_cert` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 462 | `KAM.SpinOrbit.soRotBarrier_of_cert` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 479 | `KAM.SpinOrbit.soPrecision` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 482 | `KAM.SpinOrbit.SoBackend` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 485 | `KAM.SpinOrbit.lunarLowerCert` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 487 | `KAM.SpinOrbit.lunarUpperCert` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 489 | `KAM.SpinOrbit.lunarLowerCert_ham` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 492 | `KAM.SpinOrbit.lunarUpperCert_ham` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 495 | `KAM.SpinOrbit.lunarLowerCert_params` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 498 | `KAM.SpinOrbit.lunarUpperCert_params` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 501 | `KAM.SpinOrbit.lunarLowerCert_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 503 | `KAM.SpinOrbit.lunarUpperCert_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 505 | `KAM.SpinOrbit.lunarLowerGraph_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 507 | `KAM.SpinOrbit.lunarUpperGraph_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 510 | `KAM.SpinOrbit.lunarLowerCert_freq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 513 | `KAM.SpinOrbit.lunarUpperCert_freq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 517 | `KAM.SpinOrbit.lunarPLo` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 519 | `KAM.SpinOrbit.lunarPHi` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 521 | `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 525 | `KAM.SpinOrbit.lunar_barriers` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 532 | `KAM.SpinOrbit.lunar_spin_confinement` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |

## Exact axiom transcripts

The following commands elaborate fresh copies in the permitted scratch directory, with one process at a time. Engine and lunar copies append `#print axioms` for all **119** top-level draft theorems; the engine copy additionally contains the independent bridge/length/empty/alias probes. The controls file imports landed modules and has no draft placeholders.

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .lake/abi-scratch/so-audit7/engine_axioms.lean
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .lake/abi-scratch/so-audit7/lunar_axioms.lean
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .lake/abi-scratch/so-audit7/controls.lean
```

All final runs exit **0**. Draft theorem axiom output includes `sorryAx` for 80/82 engine and all 37 lunar theorem entries. The two engine carry controls have only `propext`. The fresh bridge and the landed results/controls have only permitted axioms; the four fresh draft length/empty/alias interface proofs retain `sorryAx`. Consequently production proof-package hygiene would FAIL for these drafts, as expected; design acceptance does not waive that future gate. An initial scratch-only controls run had `No goals to be solved` after `simp` already closed a goal; removing the redundant subsequent tactic produced the clean run below. No budgets were raised.

### Engine drafts and bridge

```text
'KAM.Certificate.mantCheck_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.ofDyadic_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.mantCheck_m' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.certCExpReduced_cexpHalvings_isSome' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'KAM.Certificate.CertPoly.eval_shift' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_conjReflect' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.packShift_eq' depends on axioms: [propext, sorryAx]
'KAM.Certificate.packSum_injective' depends on axioms: [propext, sorryAx]
'KAM.Certificate.packSum_listConv' depends on axioms: [propext, sorryAx]
'KAM.Certificate.slotsBounded_listConv' depends on axioms: [propext, sorryAx]
'KAM.Certificate.packSum_flatten_mul_shards' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.intSlotsBound_sound' depends on axioms: [propext, sorryAx]
'KAM.Certificate.PackLayout.intEval_mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_reconSlots' depends on axioms: [propext, sorryAx]
'KAM.Certificate.slotsBounded_reconSlots' depends on axioms: [propext, sorryAx]
'KAM.Certificate.shardConv_length' depends on axioms: [sorryAx]
'KAM.Certificate.packSum_shardConv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.slotsBounded_shardConv' depends on axioms: [propext, sorryAx]
'KAM.Certificate.shard_reconstruct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.PackedAdvice.cut_length' depends on axioms: [sorryAx]
'KAM.Certificate.PackLayout.dense_length' depends on axioms: [sorryAx]
'KAM.Certificate.listConv_length' depends on axioms: [sorryAx]
'KAM.Certificate.PackedAdvice.combined_length' depends on axioms: [sorryAx]
'KAM.Certificate.checkShard_sound' depends on axioms: [propext, sorryAx]
'KAM.Certificate.checkPackedProduct_guards' depends on axioms: [sorryAx]
'KAM.Certificate.checkPackedProduct_scale_zero' depends on axioms: [sorryAx]
'KAM.Certificate.checkPackedProduct_raw_length' depends on axioms: [sorryAx]
'KAM.Certificate.checkPackedProduct_sound' depends on axioms: [propext, sorryAx]
'KAM.Certificate.packSum_audit5_cancel' depends on axioms: [propext]
'KAM.Certificate.reconFits_audit5_rejects' depends on axioms: [propext]
'KAM.Certificate.CertPoly.toMants_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.mulPacked_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.ofDeriv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.add' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.trim' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.toDeg' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.average' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.expPinBall_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.expWitnessRadius_pin' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.expWitness_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.invWitness_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.val_mem_ball' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.HamExpr.nonvanishingOn_of_balls' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.differentiable_eval' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.isPrimaryOnStrip' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.isRealOnReals' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.compose_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.gramModels_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.gramCheck_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.torsionModels_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.torsionAvgCheck_shape' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.torsionAvgCheck_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkRealLowerBound_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic_freq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.emb_structural' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.ham_structural' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkEmbedding_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkGram_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkInvariance_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkEnergy_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkSmallness_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_hyps' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_ham' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_err_pos' depends on axioms: [propext, sorryAx, Quot.sound]
'KAM.Certificate.toyCert3_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_freq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert3_torus' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2_torus' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyCert2d_torus' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.toyRatCert_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_small' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_zero_large' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_rejected' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_two_reduced' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.cexpTest_large_pin' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'_private._stdin.0.KAM.Certificate.audit7_length' depends on axioms: [propext, sorryAx]
'_private._stdin.0.KAM.Certificate.audit7_empty_left' depends on axioms: [propext, sorryAx]
'_private._stdin.0.KAM.Certificate.audit7_empty_right' depends on axioms: [propext, sorryAx]
'_private._stdin.0.KAM.Certificate.audit7_padding_reject' depends on axioms: [propext, sorryAx]
'_private._stdin.0.KAM.Certificate.audit7_engine_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Apost.g1_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Lunar drafts

```text
'KAM.Certificate.isDiophantine_of_index_map' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_rot_isDiophantine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuPlus_rot_isDiophantine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.Certificate.lunarNuMinus_rot_half_isDiophantine' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'KAM.Certificate.lunarNuPlus_rot_half_isDiophantine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMapInv_soRotMap' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMap_soRotMapInv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotMap_symplectic' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.hamiltonianVectorFieldℂ_soRotHC' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExpr_eval' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExpr_clock' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExprScaled_eval' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotHamExprScaled_clock' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.invarianceError_const_mul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinus_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlus_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soIsDiophantine_smul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqMinus_isDiophantine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreqPlus_isDiophantine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarR1Kappa_div' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.SoGraph.torus_of_rot' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_exact_rotTorus' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_cert' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_cert' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarLowerCert_ham' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarUpperCert_ham' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarLowerCert_params' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarUpperCert_params' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarLowerCert_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarUpperCert_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarLowerGraph_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarUpperGraph_passes' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarLowerCert_freq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarUpperCert_freq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarPLo_lt_lunarPHi' depends on axioms: [sorryAx]
'KAM.SpinOrbit.lunar_barriers' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_spin_confinement' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

### Independent controls and landed exports

```text
'SOAudit7.landed_listConv_length' depends on axioms: [propext, Quot.sound]
'SOAudit7.landed_listConv_empty' depends on axioms: [propext]
'SOAudit7.padding_alias' does not depend on any axioms
'SOAudit7.raw_alias_split' depends on axioms: [propext]
'SOAudit7.crop_extend_length' depends on axioms: [propext, Classical.choice, Quot.sound]
'SOAudit7.B0_lower_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SOAudit7.B0_upper_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'SOAudit7.B0_margins' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packShift_eq' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.packSum_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_listConv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.packSum_flatten_mul_shards' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.intSlotsBound_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.mantCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ofDyadic_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertFixed.mantCheck_m' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Reproducible fresh probes

These were appended to a fresh copy of the engine draft. They do not invoke whole-product soundness or draft black-box soundness. Their axiom sets above distinguish the draft interface proofs from the engine bridge.

```lean
namespace KAM.Certificate
open KAM
open scoped Matrix.Norms.Operator
 theorem audit7_length {adv : PackedAdvice} {da db : List ℤ}
    (h : checkPackedProduct adv da db = true) :
    adv.combined.length = (listConv da db).length := by
  obtain ⟨_, _, _, ha, hb, hpa, hpb, _, _⟩ := checkPackedProduct_guards h
  have hna : da ≠ [] := by intro he; simp [he] at hpa
  have hnb : db ≠ [] := by intro he; simp [he] at hpb
  rw [PackedAdvice.combined_length, PackedAdvice.prodLen, listConv_length hna hnb, ha, hb]
 theorem audit7_empty_left (adv : PackedAdvice) (db : List ℤ) :
    checkPackedProduct adv [] db = false := by
  cases hc : checkPackedProduct adv [] db
  · rfl
  · have hp := (checkPackedProduct_guards hc).2.2.2.2.2.1
    simp at hp
 theorem audit7_empty_right (adv : PackedAdvice) (da : List ℤ) :
    checkPackedProduct adv da [] = false := by
  cases hc : checkPackedProduct adv da []
  · rfl
  · have hp := (checkPackedProduct_guards hc).2.2.2.2.2.2.1
    simp at hp
 theorem audit7_padding_reject {adv : PackedAdvice} (ha : adv.la.denseLen = 2) :
    checkPackedProduct adv [0] [0] = false := by
  apply checkPackedProduct_raw_length
  left
  simp [ha]
 theorem audit7_engine_bridge {n : ℕ} {α : Type} [CertArith α]
    {c : TorusCertificate n α} {ωstar : Fin n → ℝ} (h : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) :
    CertifiedTorus c ωstar := by
  have hg := (Iso.Apost.g1_explicit h.hn h.hτ h.hρinf h.hρinfρ h.hM h.hσK h.hσB h.hσT
    h.hμ h.hγbar h.hσω h.hν ωstar h.hωstar).2.2.2
  obtain ⟨Ki, si, hs1, hsσ, hh, hp, hr, hi, he, hb, hd, hcl, hsc⟩ :=
    hg c.D c.H c.K c.params.s c.params.γ c.params.err c.params.E0
      h.hopen h.htransl h.hholo h.hper h.hreal h.hbd h.hK h.hKp h.hKr h.hball h.hDK
      h.hG h.hTu h.hTb h.hs1 h.hsσ h.hν1 h.hν2 h.hγ h.hγγbar hdio h.he0 h.hE h.hEn h.hC1
  exact ⟨Ki, si, hs1, hsσ, hh, hp, hr, hi, he, hb, hd,
    fun θ hθ => (hcl θ hθ).trans h.hdisp, hsc.trans h.hdisp⟩
end KAM.Certificate
#print axioms KAM.Certificate.audit7_length
#print axioms KAM.Certificate.audit7_empty_left
#print axioms KAM.Certificate.audit7_empty_right
#print axioms KAM.Certificate.audit7_padding_reject
#print axioms KAM.Certificate.audit7_engine_bridge
#print axioms KAM.Iso.Apost.g1_explicit
```

Independent controls, compiled against the landed packing module:

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module
public import KAM.Certificate.Poly.Packed
public import KAM.Certificate.Arith.Rat
/-! # Independent audit 7 controls against landed SO-POLY-A. -/
@[expose] public section
namespace SOAudit7
open KAM.Certificate
 theorem landed_listConv_length {a b : List ℤ} (ha : a ≠ []) (hb : b ≠ []) :
    (listConv a b).length = a.length + b.length - 1 := by
  cases a with
  | nil => contradiction
  | cons x xs =>
    cases b with
    | nil => contradiction
    | cons y ys => simp [listConv]
 theorem landed_listConv_empty (a : List ℤ) :
    listConv [] a = [] ∧ listConv a [] = [] := by simp [listConv]
 theorem padding_alias :
    ([0] ++ List.replicate (2 - ([0] : List ℤ).length) 0 : List ℤ) =
    [0,0] ++ List.replicate (2 - ([0,0] : List ℤ).length) 0 := by decide
 theorem raw_alias_split :
    ([0] : List ℤ).length ≠ 2 ∧ ([0,0] : List ℤ).length = 2 ∧
    (listConv [0] [0]).length = 1 ∧ (listConv [0,0] [0,0]).length = 3 := by decide
 theorem crop_extend_length (xs : List ℤ) (n : ℕ) :
    ((xs ++ List.replicate n 0).take n).length = n := by simp
 theorem B0_lower_exact : (237 / 125 : ℚ) * (125 / 100) = 237 / 100 := by norm_num
 theorem B0_upper_exact : (237 / 125 : ℚ) * (229 / 100) = 54273 / 12500 := by norm_num
 theorem B0_margins :
    (237 / 125 : ℚ) * (125 / 100) < 10075 / 100 ∧
    (237 / 125 : ℚ) * (229 / 100) < 196 := by norm_num
end SOAudit7
#print axioms SOAudit7.landed_listConv_length
#print axioms SOAudit7.landed_listConv_empty
#print axioms SOAudit7.padding_alias
#print axioms SOAudit7.raw_alias_split
#print axioms SOAudit7.crop_extend_length
#print axioms SOAudit7.B0_lower_exact
#print axioms SOAudit7.B0_upper_exact
#print axioms SOAudit7.B0_margins
#print axioms KAM.Certificate.packShift_eq
#print axioms KAM.Certificate.packSum_injective
#print axioms KAM.Certificate.packSum_listConv
#print axioms KAM.Certificate.packSum_flatten_mul_shards
#print axioms KAM.Certificate.intSlotsBound_sound
#print axioms KAM.Certificate.mantCheck_sound
#print axioms KAM.Certificate.ofDyadic_sound
#print axioms KAM.Certificate.CertFixed.mantCheck_m
```

## Final lint, protected paths, uncertainties and errata

From `/root/code/KAM-inp-design-so`:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **0**, exact output:

```text
check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No stale-generated-root exception was needed. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check inp...HEAD` and `git diff --check` exit 0. All gate/build/replay/lint invocations were sequential within this audit; `LEAN_NUM_THREADS=1` was set throughout. No compile cache was cleaned, dependency checkout changed, or library rebuilt from scratch. Cached warnings in the targeted build are reproduced above and do not involve changed production sources.

No new suspected defect in a pinned mathematical source, frozen statement, or blueprint was established. F14 was a design-interface/algorithm attachment issue; F15 was a documentation units issue. Neither is an HL19 erratum. The auditor introduced no mathematical deviation. The revision's explicit rejection of empty packed factors is a computational policy with a direct/zero-filled alternative, not a restriction added to the soundness theorem's callers. Previously disclosed deviations remain: exact frequency with rational enclosure, bounded auxiliary-action domain, Fourier approximation to the energy lift with error paid, rotated/time-scaled client, O1 momentum window, and O4 continuous graphs. Approximate generator figures and benchmark projections remain distinct from proved interval bounds and actual end-to-end replay.

The outstanding work is implementation/proof of the draft algorithms and their contracts, literal data and window endpoints, generated-data packaging, P5 and other executable whole-check tests, and the final lunar theorem. This audit authorizes no seal and establishes no campaign theorem closure. The next design stage may proceed with F14/F15 closed; proof packages still need their ordinary independent type, axiom, build, kernel and source checks.

Report validation: 245 declaration rows cover the 166 engine and 79 lunar entries; exact axiom output covers all 119 draft theorems, six additional engine/bridge axiom probes, eight independent controls and eight landed exports. Code fences are balanced, trailing whitespace absent, and input hashes were rechecked after verification. Scratch probes were all below 1500 lines (engine 1314, lunar 578, controls 52), without resource overrides. All auditor-created scratch files/logs/full-diff capture were removed after transcription. Final repository status: only `?? docs/tracks/SO/audits/SO-DESIGN-audit-7.md`.
