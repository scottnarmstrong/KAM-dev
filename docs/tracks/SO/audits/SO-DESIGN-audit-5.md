# SO-DESIGN independent audit 5 — Revision 5

2026-10-29. **Overall verdict: FAIL (design acceptance), findings F12 and F13.** The rotated lunar client passes design review with numerical/proof obligations retained. Both exact signature files elaborate. The new packed-product soundness chain needs explicit anti-carry guards and a correction at rounding scale zero before it supports the advertised whole-carrier enclosure contract. These are design gaps, not an allegation that an existing implemented checker accepts a bad certificate: the relevant checker bodies are still `sorry`.

No new frozen anchor or provider is supplied by this branch, so **no seal-ready verdict applies**. Existing I-G1 is unchanged and SEALED; its explicit engine passes the fresh bridge, targeted build and kernel replay. Successful elaboration of placeholder signatures does not prove the checker or the lunar theorems.

## Scope, authorities and comparison

Report destination is the user's exact absolute path in this worktree, overriding the generic brief's main-worktree destination. Repository edits are restricted to this report; probes and logs are temporary under `.lake/abi-scratch/` and are removed after recording their results. No state-changing git command was used.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the complete Round 5 focus in `SO-DESIGN-handoff.md`, audit 4, `.drafts/handoff-SO-DESIGN-R5.md`, the design and both signature files. Controlling external-local inputs: `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` (D30 and O1–O5), the proposal and pilot, CONSTANTS-STUDY, SO-REPLAY2, and `/root/code/KAM-inp/.drafts/briefs/offload-main/SO-ROTDIO.md`. Also compared the I-G1 frozen anchor and used definitions, `IG1Body`, `g1_explicit`, track I statement, blueprint-I `bpI:p0:g1` and `bpI:p2:g1`, and landed shared arithmetic, model, expression, clock, lunar Hamiltonian and graph sources. There is no `docs/tracks/SO/statement.md` here; the design/owner plan supplies the unfrozen SO surface. No N/P anchor is being implemented by SO-DESIGN.

`HEAD = 453508a9ded6e9291cba0868354ac5690ce864dd`; `inp` and the shared signature-build checkout both equal `f8405551c09bb7baf63ad01547cc2ecb8d372bbc` when checked. `git diff inp...HEAD` contains seven documentation/script paths, 4,100 additions: audits 1–4, handoff, design (2,380 lines, including both full signature appendices), and the 51-line stand-in script. Revision 5 was additionally compared against `79ec938c`. There are **no production Lean changes** and the protected-path diff is empty.

## Numbered findings

### F12 — HIGH, packed residual decoding does not establish coefficientwise error without anti-carry checks

Locations: design §1.16, §5 and Appendix A-E, especially `SlotsBounded` / `packSum_injective` at lines 969–975, `intSlotsBound_sound` at 1004–1008, `checkShard` at 1064, `checkPackedProduct` at 1068, and `checkPackedProduct_sound` at 1073–1080. Corresponding draft locations: `.drafts/design/SOSignatures.lean:183–194, 217–226, 282–306`.

Quoted contract: a shard checks that `Σ pack(A_i)·pack(B_j) − 2^scale · pack(r_s)` "passes `intSlotsBound`"; the whole product checks "`compat`, `convFits`, the factor blocks ... every shard". The decoding theorem only exports **existence** of a bounded residual digit list. `packSum_injective` requires `SlotsBounded` for **both** digit lists being compared. `convFits` bounds the genuine convolution; it does not bound the certificate-supplied reconstructed digits `2^scale r_s + decoded_error`. No stated guard exports this second bound, or an equivalent unique-reconstruction argument.

Concrete counterexample to the implication supplied by those listed checks: let radix `2^w = 16`, `scale = 1`, both dense factors `[0,0]` (one two-slot block apiece), and full target window of length three. The exact convolution is `[0,0,0]`, hence satisfies `convFits` and every true-product slot bound. Supply rounded advice `r = [16,-1,0]`. Then

```text
packSum 4 [16,-1,0] = 16 - 16 = 0
pack(exact convolution) - 2 * pack(r) = 0.
```

The packed residual has the all-zero decoded list and passes every nonnegative error budget, but slot zero has `|0 - 2*16| = 32 > 2^scale = 2`. This embeds in dimension two by a singleton second axis and a compatible full product window. Thus factor no-wrap, true-product `convFits`, and bounded residual decoding alone are insufficient. It works at positive scale, independently of F13. The two concrete integer equalities/inequality were checked in Lean with `decide +kernel`, using the draft's concrete `packSum` body.

**Required change:** make the untrusted-advice validation explicit. For each reconstructed shard digit list, check sufficient bounds to put BOTH the exact shard convolution and the reconstructed `2^scale*r + e` in the injective signed-slot range (or prove another equally strong reconstruction lemma with checkable premises). Check advice lengths, zero advice outside the target, no unchecked high slots, compatible layout, positive block size/width as needed, and the error-log limits used by that argument. Add a lemma exporting these guards from a successful check; use it in the slotwise glue, with no conclusion-shaped hypothesis. `intSlotsBound_sound` may be strengthened with a digit-range property, but bounding the decoded residual alone still does not bound `2^scale*r + e`. The malformed advice above must be an explicit negative test.

The planned §8 negative test for advice "correct modulo `2^w` but violates the slot bound" recognizes the risk; it does not specify which runtime guard rejects this exact-cancellation example, nor discharge the missing injectivity premise. No evaluation of placeholder `checkShard` or `checkPackedProduct` is claimed. Their theorem types could be satisfied by a future checker that adds these guards; the present prose algorithm does not yet justify them.

### F13 — MEDIUM, whole-carrier rounding contract fails at `scale = 0` under the stated shard budget

Locations: `PackedAdvice.scale : ℕ` at design line 1052; `checkShard` description at 1062–1064 and `checkPackedProduct_sound` at 1070–1080 (draft lines 270, 280–306).

Quoted derivation: "two overlapping shard windows, each `≤ 2^(scale-1)`" give the global target-slot bound `≤ 2^scale`. Here scale is a natural number, so at zero `scale - 1 = 0`: each shard may err by one, and two overlapping errors may total two, while the promised bound is one. The failure remains with all digits far inside the signed-slot range.

Explicit blocks, of length `L=2`, with a large safe radix (e.g. `w=8`):

```text
A0=[1,1], A1=[0,0]; B0=[1,1], B1=[1,0].
s=0 exact local convolution [1,2,1], advice [1,2,0], error [0,0,1].
s=1 exact local convolution [1,1,0], advice [0,1,0], error [1,0,0].
s=2 all zeros.
```

Both local error lists meet `2^(0-1)=1`. Shard 1 is shifted by two slots; at global slot two the errors add to two. The full exact convolution is `[1,2,2,1,0,0,0]`, while the combined advice has coefficient zero at slot two. All slots can be inside the target. Python integer convolution independently checked these lists; Lean checked `2 * 2^(0-1) > 2^0` for natural exponents with `decide +kernel`.

**Required change:** either reject `scale = 0` in `checkPackedProduct` and export `1 ≤ scale` from success, or use exact zero-error checking at scale zero. Alternatively increase the exported bound and propagate it all the way to `mulPacked`'s strip radius. Keep the public theorem unconditional in the certificate data: establish the guard internally. Add a positive-scale overlap test and this scale-zero negative/special-case test. Merely choosing a positive scale for lunar data does not repair a general checker contract.

### F11 and carried F1–F10

F11's obsolete arithmetic-interface warning is closed by the Revision 5 clarification and historical status labels. The landed declarations now enter by import, rather than arithmetic stand-ins. F1–F10's repaired contract shapes remain present: exact frequency plus box and Diophantine input, law-free denotations, acyclic producer/consumer contracts, nonresonant toys, exact torsion shapes, positive dimension norm bridges, the corrected auxiliary-action residual, and successful-call range-reduced pins. No prior finding is reopened. F12/F13 concern the newly introduced product algorithm.

## Review against the five Round 5 focus items

| Focus / node | Verdict | Reason / remaining obligation |
|---|---|---|
| Rotated Hamiltonian and coordinate map | PASS WITH NOTES | `q=Q0+Q1`, `φ=Q1`, `p=P0`, `J=P1-P0`; inverse exact. `AᵀB=I`. New mode for old `m+1` is `[2,1-m]`, exactly `2-(m+1)`. `soRotHC=soHC∘L` by definition. Differentiated vector field formula has the correct direction `L⁻¹ X_H∘L`. Concrete inverse/symplectic proofs were independently elaborated; the full Hamiltonian derivative proof remains a package obligation. |
| Time scaling and clock | PASS WITH NOTES | `cH'` has clock derivative `c`; move to `H'` at `(sinf/c)ωstar` before invoking `clock_frequency` on `D=univ`. Nonzero scalar multiplication preserves differentiability in both directions, so the proposed error identity needs no extra differentiability premise. Clock yields `(sinf/c)ωstar₁=1`; at `ωstar₁=c/s`, this fixes `sinf=s`. |
| Rotated frequency and Diophantine transfer | PASS WITH NOTES | `κ(ν−1,1)` and the two exact sqrt(5) coefficients are correct. All five SO-ROTDIO statement headers match the fixed brief verbatim. `T(k)=(k0,k1-k0)`, `C=2` halves `1/21` to `1/42`; positive scaling gives `κ/42`. R1's rational value `125000/3000003` was independently proved. These declarations are stand-ins until their package lands. |
| Exact rotated torus to landed graph core | PASS WITH NOTES | `torus_of_rot` uses `Q(x,y)=Q0(x−y,y)+y+c0`. Under `(x+tν,y+t)`, its first argument moves at `ν−1`; derivative becomes `(P−1)+1=P`. Periodicity in y uses one negative x-period and one positive y-period. Force is exactly `−soVq(Q,y+c0)`; x-monotonicity and p-range persist. This matches all fields of landed `SoGraph.Torus`, then `soBarrier_of_torus`. No graph/conjugacy conclusion is assumed as certificate data. |
| Final original-coordinate theorem | PASS WITH NOTES | Final statements still use `soField`, original `(q,p,φ)`, original constant initial momentum window, unique global solution and `33/1000`. `P0=p` makes the transfer exact. `lunarPLo`, `lunarPHi`, certificates and passes are unpaid placeholders. |
| R1 and G-J | PASS WITH NOTES | R1 parameters match O5. `cH'(Ktilde)=cΔP1`; `E(Ktilde)=E(K0)−D_(sωstar)ΔP1` in the last row. Under scalar pilot identities that row is `c(p−1)r`, not zero. Named `Br,B1,Bq,Bc,B0,B2,β2` retain all invoices. No numerical margin, 39/20 majorant, residual threshold, graph margin or Fourier-P1 attachment is certified by this design audit. |
| Exact-product contracts | FAIL | `mulPacked_sound` encloses the exact product; `CertModel.Encloses.mul` encloses `f*g` without assuming the answer. Their intended strength is correct. The described checks need F12/F13 to derive that strength. |
| Packing and layout helper statements | PASS WITH NOTES | `packSum`, bounded injectivity, Kronecker substitution and shard identity have the right mathematical targets. `compat` must actually enforce no-wrap and valid shapes; integer Fourier multiplicativity uses exact convolution. These proofs and checker definitions are unpaid, rather than certified by performance prototypes. |
| Untrusted mantissa decoder / arithmetic interface | PASS WITH NOTES | `mantCheck` compares against BOTH outward conversions, whose laws squeeze `val a` to the exact dyadic. Independently proved from the landed laws. `ofDyadic` checks exact representability. No new backend trust assumption; fixed-point completeness still needs its own proof. |
| Failed/missing advice fallback | PASS WITH NOTES | Zero polynomial plus a correctly rounded upper bound on the product gives a sound crude enclosure, with the degree factor accounted for once. This is a legitimate fallback, not junk used to force a theorem. A missing key need not universally force checker rejection; only certificates depending on tighter bounds must fail. |
| Signature split and landed compatibility | PASS | 1049/539 lines, both gates pass; both Appendix blocks and both shared copies are byte-identical. Twenty engine stand-ins are verbatim. Landed names import successfully; no duplicated landed declaration appears. |
| Packaging owner choice | NOTE | §7.2 intentionally leaves A/B/C open. This is not a mathematical finding or permission request in this audit. SO-DATA waits for the decision; existing hard limits remain binding. |

## Engine fidelity and generality

Fresh `audit5_engine_bridge` supplies every `IG1Body` premise from `G1Hyps` in literal engine order: open and translation-invariant D; H holomorphy, periodicity, reality and all five bounds; K holomorphy/primarity/reality; ball and DK margins; Gram invertibility/rows; averaged bordered torsion invertibility/rows; ray interval and both endpoint margins; positive gamma, upper gamma, external Diophantine fact, nonnegative error, invariance, energy and smallness. It applies the exact `g1_explicit` type at `c.params` and the theorem-binder `ωstar`; it does not substitute a certificate-defined real frequency. Both displacement bounds use `isoC2` (`C2=C3` here) and `hdisp`. The bridge contains no placeholder and prints only `[propext, Classical.choice, Quot.sound]`.

`G1Hyps` and `StaticFacts` are derived propositions, never input fields. The external exact-frequency box membership is a typing/enclosure fact and the external mathematical small-divisor input is `IsDiophantine`. Backend laws are fixed arithmetic infrastructure, not torus-specific hypotheses. The general route remains `n≥2`, natural τ satisfying `n−1≤τ`, arbitrary finite `HamExpr` with certified nonvanishing divisions and general real Fourier data in every coordinate. It does not claim every real-analytic Hamiltonian has a finite expression or that every rationally independent vector is Diophantine.

The open-strip model semantics match the literal frozen `complexStrip` (`|Im θ_i|<ρ`), rather than any closed-strip replacement. Gram is bilinear, not Hermitian. Torsion producers retain exact `(n+1)×(n+1)` shapes, the original last row `DH(K)N`, the derivative of the true inverse Gram, entry enclosures and continuity before averaging. Their mathematical operations remain legitimate, but their actual enclosures depend on correct model products, so F12/F13 propagate to these consumers until repaired.

## Feasibility and dependencies

The replay GO is an owner ruling supported by prototypes, not a proof of packed-product glue or completion of every replay measurement. The design explicitly retains end-to-end design-B, complex-product and middle-size measurements before SO-DATA. Pre-gate SO-ROT, SO-ROTDIO, SO-RFREQ and SO-GRAPHR can proceed on landed interfaces; post-gate packing/model packages follow their DAG. SO-LUNAR's `LunarParams` correctly waits for certificate definitions rather than entering pre-gate RotFreq.

Totals check: 8,700 + 9,600 = 18,300; 30–40% overrun gives 23,790–25,620. These are package estimates including landed work at historical estimates. SO-EXPR's 1,700 is spread across modules; it cannot become a single file. SO-POLY's 1,150 must cover anti-carry, overlap, shapes and the complex split, so its 600-line B allowance is uncertain and may need splitting. Measured shard cost is evidence only for the sampled layouts/precision; the data packaging and product count dominate total volume. None of these estimates certifies actual lunar data or warrants an override.

## Independent check receipts

All Lean invocations below were serialized and used `LEAN_NUM_THREADS=1`; signature/compile gates launch `nice -n 5`. No lake clean/update/cache fetch or package-directory mutation was used.

1. `git diff inp...HEAD`, revision delta `git diff 79ec938c..HEAD`, `git diff --stat inp...HEAD`: scope as above. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `git diff --check inp...HEAD`: exit 0, no output.
2. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean`: exit 0, 110 warnings, all `declaration uses 'sorry'`, zero errors. Same for `SOSignaturesLunar.lean`: exit 0, 54 such warnings, zero errors. These gates use the shared `/root/code/KAM-inp` build as their script specifies.
3. `python3 -I docs/tracks/SO/design/check_so_standins.py .drafts/design/SOSignatures.lean .drafts/design/SOSignaturesLunar.lean`: exit 0. Output: `stand-ins checked: 20`; engine `1049 lines; lines over 100 chars: none`; lunar `539 lines; lines over 100 chars: none`; `PASS`. Additionally checked both complete Appendix blocks, shared draft byte identity, and all five fixed SO-ROTDIO headers.
4. The same signature gate, sequentially on `.lake/abi-scratch/SOAudit5engine.lean` and `SOAudit5lunar.lean`: zero errors, 110/54 expected placeholder warnings. The engine probe appends the fully proved engine bridge, three kernel-decided arithmetic controls, and axiom prints for all 67 draft theorems plus the bridge and engine. The lunar probe prints all 37 draft theorem axioms. Probe lengths remain below 1500.
5. Exhaustive draft theorem axiom outputs: 104 draft results all depend on `sorryAx` (expected for an explicitly unfrozen design). Engine: 60 `[propext, sorryAx, Classical.choice, Quot.sound]`, six `[propext, sorryAx]`, one `[propext, sorryAx, Quot.sound]`. Lunar: 36 full four-axiom lists, one `[sorryAx]` (`lunarPLo_lt_lunarPHi`). The fresh bridge and existing engine each have only `[propext, Classical.choice, Quot.sound]`. Exact outputs are transcribed below. There is no claim of package proof hygiene for these placeholders.
6. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-design-so KAM.Iso.Apost.G1`: exit 0. Exact output:

```text
[inp-gate] slot 1 acquired 15:00:15 for KAM.Iso.Apost.G1
Build completed successfully (3224 jobs).
```

7. From `/root/code/KAM-inp` (the landed modules imported by the signature gate): `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1 KAM.Certificate.Arith.Fixed KAM.Certificate.Clock KAM.SpinOrbit.HamExpr KAM.SpinOrbit.Graph.Inverse`: exit 0. Exact output:

```text
replaying KAM.SpinOrbit.Graph.Inverse
replaying KAM.SpinOrbit.HamExpr
replaying KAM.Certificate.Clock
replaying KAM.Certificate.Arith.Fixed
replaying KAM.Iso.Apost.G1
```

8. Concrete probe and final lint receipts are appended after completion below. A preliminary lint was deliberately stopped before its ABI Lean subprocess to keep it serialized with the running signature probe; only the completed final lint is a validation receipt. No concurrent auditor-owned Lean process was started by that preliminary run.
9. Comment-masked draft scans: engine 110 and lunar 54 deliberate `sorry` tokens; no `axiom`, `admit`, `unsafe`, `opaque`, `EuclideanSpace`, `native_decide`, `implemented_by`, or `set_option` in code. Both drafts have copyright, `module`, public imports, module docstring and exposed public section. No provider import or new DRAFT_SORRY anchor dependency is introduced. Existing imported sealed surfaces remain read-only.

## Exact axiom transcript

```text
'_private._stdin.0.KAM.Certificate.audit5_engine_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Apost.g1_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
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
'KAM.Certificate.checkPackedProduct_sound' depends on axioms: [propext, sorryAx]
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
'KAM.Certificate.HamExpr.jet_d3' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
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
'KAM.SpinOrbit.isDiophantine_smul' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
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

## Per-declaration design review and definition classification

`PWN` means PASS WITH NOTES at the design/type level; its placeholder implementation/proof remains unpaid. `FAIL` refers to F12/F13. `DATA` is a finite carrier or configuration; `DEN` is an explicit denotation; `ALG` is a placeholder algorithm requiring whole-carrier validation; `PROP` is a derived/semantic proposition, never certificate input; `ENDPOINT` is unpaid generated/example data. Names below are fully namespace-qualified. Mirrored engine declarations in the lunar file are listed too; they are not additional production declarations.

### Engine A-E

| Draft line / node | Lean declaration | Verdict | Classification / reason |
|---|---|---|---|
| 93 | `KAM.Certificate.mantCheck` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 96 | `KAM.Certificate.mantCheck_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 101 | `KAM.Certificate.ofDyadic` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 105 | `KAM.Certificate.ofDyadic_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 110 | `KAM.Certificate.CertFixed.toMant` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 116 | `KAM.Certificate.CertFixed.mantCheck_m` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 124 | `KAM.Certificate.cexpHalvings` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 129 | `KAM.Certificate.certCExpReduced_cexpHalvings_isSome` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 141 | `KAM.Certificate.CertPoly.shift` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 143 | `KAM.Certificate.CertPoly.eval_shift` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 148 | `KAM.Certificate.CertPoly.conjReflect` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 150 | `KAM.Certificate.CertPoly.eval_conjReflect` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 172 | `KAM.Certificate.packSum` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 177 | `KAM.Certificate.packShift` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. F12/F13 guards must be made explicit in consumers. |
| 180 | `KAM.Certificate.packShift_eq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 183 | `KAM.Certificate.SlotsBounded` | PWN | PROP/DEN: intended semantic predicate, not an input proof field. |
| 186 | `KAM.Certificate.packSum_injective` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 191 | `KAM.Certificate.listConv` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 195 | `KAM.Certificate.packSum_listConv` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 200 | `KAM.Certificate.convFits` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 202 | `KAM.Certificate.slotsBounded_listConv` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 207 | `KAM.Certificate.packSum_flatten_mul_shards` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 216 | `KAM.Certificate.intSlotsBound` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. F12/F13 guards must be made explicit in consumers. |
| 218 | `KAM.Certificate.intSlotsBound_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 225 | `KAM.Certificate.PackLayout` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 233 | `KAM.Certificate.PackLayout.slot` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 236 | `KAM.Certificate.PackLayout.dense` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 239 | `KAM.Certificate.PackLayout.prodKey` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 243 | `KAM.Certificate.PackLayout.compat` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 246 | `KAM.Certificate.intEval` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 251 | `KAM.Certificate.PackLayout.intEval_mul` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 262 | `KAM.Certificate.PackedAdvice` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. F12/F13 guards must be made explicit in consumers. |
| 271 | `KAM.Certificate.PackedAdvice.combined` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. F12/F13 guards must be made explicit in consumers. |
| 274 | `KAM.Certificate.PackedAdvice.inBox` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. F12/F13 guards must be made explicit in consumers. |
| 278 | `KAM.Certificate.checkShard` | FAIL | F12 anti-carry guard and F13 zero-scale overlap. |
| 282 | `KAM.Certificate.checkPackedProduct` | FAIL | F12 anti-carry guard and F13 zero-scale overlap. |
| 287 | `KAM.Certificate.checkPackedProduct_sound` | FAIL | F12 anti-carry guard and F13 zero-scale overlap. |
| 296 | `KAM.Certificate.CertPoly.toMants` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 299 | `KAM.Certificate.CertPoly.toMants_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 310 | `KAM.Certificate.CertPoly.mulPacked` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 314 | `KAM.Certificate.CertPoly.mulPacked_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). Exact-product target; blocked downstream by F12/F13. |
| 323 | `KAM.Certificate.ProductAdvice` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 330 | `KAM.Certificate.ProductKey` | PWN | Representation/index alias; no hidden mathematical premise. |
| 332 | `KAM.Certificate.AdviceBook` | PWN | Representation/index alias; no hidden mathematical premise. |
| 341 | `KAM.Certificate.ModelConfig` | PWN | DATA/configuration: untrusted decoder function plus advice, each decoded value rechecked. |
| 354 | `KAM.Certificate.CertModel.add` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 363 | `KAM.Certificate.CertModel.mul` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 367 | `KAM.Certificate.CertModel.trim` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 371 | `KAM.Certificate.CertModel.toDeg` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 376 | `KAM.Certificate.CertModel.ofDeriv` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 379 | `KAM.Certificate.CertModel.Encloses.ofDeriv` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 384 | `KAM.Certificate.CertModel.Encloses.add` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 389 | `KAM.Certificate.CertModel.Encloses.mul` | PWN | Reviewed statement; proof unpaid (`sorryAx`). Exact-product target; blocked downstream by F12/F13. |
| 395 | `KAM.Certificate.CertModel.Encloses.trim` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 400 | `KAM.Certificate.CertModel.Encloses.toDeg` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 406 | `KAM.Certificate.CertModel.Encloses.average` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 433 | `KAM.Certificate.ExpWitness` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 440 | `KAM.Certificate.expPinBall` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 442 | `KAM.Certificate.expPinBall_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 448 | `KAM.Certificate.expWitnessRadius` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 453 | `KAM.Certificate.expWitnessRadius_pin` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 459 | `KAM.Certificate.expWitness_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 467 | `KAM.Certificate.invWitnessRadius` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 470 | `KAM.Certificate.invWitness_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 485 | `KAM.Certificate.HamExpr.jet_d3` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 499 | `KAM.Certificate.Slp.balls` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 502 | `KAM.Certificate.Slp.val_mem_ball` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 510 | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 517 | `KAM.Certificate.CertEmbedding` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 523 | `KAM.Certificate.CertEmbedding.eval` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 530 | `KAM.Certificate.CertEmbedding.differentiable_eval` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 533 | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 537 | `KAM.Certificate.CertEmbedding.isRealOnReals` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 545 | `KAM.Certificate.Witnesses` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 552 | `KAM.Certificate.Slp.compose` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 557 | `KAM.Certificate.Slp.compose_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 575 | `KAM.Certificate.ModelMatrix` | PWN | Representation/index alias; no hidden mathematical premise. |
| 579 | `KAM.Certificate.ModelMatrix.Encloses` | PWN | PROP/DEN: intended semantic predicate, not an input proof field. |
| 587 | `KAM.Certificate.polyMatrix` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 592 | `KAM.Certificate.gramModels` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 595 | `KAM.Certificate.gramModels_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 603 | `KAM.Certificate.gramCheck` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 607 | `KAM.Certificate.gramCheck_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 618 | `KAM.Certificate.torsionIdx` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 625 | `KAM.Certificate.torsionModels` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 634 | `KAM.Certificate.torsionModels_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 652 | `KAM.Certificate.torsionAvgCheck` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 656 | `KAM.Certificate.torsionAvgCheck_shape` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 660 | `KAM.Certificate.torsionAvgCheck_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 673 | `KAM.Certificate.checkRealLowerBound` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 676 | `KAM.Certificate.checkRealLowerBound_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 696 | `KAM.Certificate.CertParams` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 717 | `KAM.Certificate.TorusCertificate` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 742 | `KAM.Certificate.TorusCertificate.D` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 745 | `KAM.Certificate.TorusCertificate.H` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 747 | `KAM.Certificate.TorusCertificate.K` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 757 | `KAM.Certificate.checkStatic` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 761 | `KAM.Certificate.checkHamBounds` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 764 | `KAM.Certificate.checkEmbedding` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 767 | `KAM.Certificate.checkInvariance` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 770 | `KAM.Certificate.checkEnergy` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 773 | `KAM.Certificate.checkGram` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 777 | `KAM.Certificate.checkTorsion` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 780 | `KAM.Certificate.checkSmallness` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 784 | `KAM.Certificate.checkTorusCertificate` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 794 | `KAM.Certificate.G1Hyps` | PWN | PROP: derived engine/static facts. |
| 847 | `KAM.Certificate.CertifiedTorus` | PWN | PROP/DEN: intended semantic predicate, not an input proof field. |
| 866 | `KAM.Certificate.StaticFacts` | PWN | PROP: derived engine/static facts. |
| 891 | `KAM.Certificate.checkStatic_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 895 | `KAM.Certificate.checkStatic_freq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 901 | `KAM.Certificate.TorusCertificate.emb_structural` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 905 | `KAM.Certificate.checkHamBounds_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 914 | `KAM.Certificate.TorusCertificate.ham_structural` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 922 | `KAM.Certificate.checkEmbedding_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 928 | `KAM.Certificate.checkGram_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 933 | `KAM.Certificate.checkInvariance_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 939 | `KAM.Certificate.checkEnergy_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 946 | `KAM.Certificate.checkTorsion_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 953 | `KAM.Certificate.checkSmallness_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 964 | `KAM.Certificate.checkTorusCertificate_hyps` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 974 | `KAM.Certificate.checkTorusCertificate_sound` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 990 | `KAM.Certificate.toyHam3` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 997 | `KAM.Certificate.toyCert3` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 999 | `KAM.Certificate.toyCert3_ham` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1001 | `KAM.Certificate.toyCert3_err_pos` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1003 | `KAM.Certificate.toyCert3_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1005 | `KAM.Certificate.toyCert3_freq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1008 | `KAM.Certificate.toyCert3_torus` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1013 | `KAM.Certificate.toyCert2` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 1015 | `KAM.Certificate.toyCert2d` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 1017 | `KAM.Certificate.toyCert2_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1019 | `KAM.Certificate.toyCert2d_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1021 | `KAM.Certificate.toyCert2_torus` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1023 | `KAM.Certificate.toyCert2d_torus` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1027 | `KAM.Certificate.toyRatCert` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 1029 | `KAM.Certificate.toyRatCert_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1035 | `KAM.Certificate.cexpTest_zero_small` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1037 | `KAM.Certificate.cexpTest_zero_large` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1039 | `KAM.Certificate.cexpTest_two_rejected` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1041 | `KAM.Certificate.cexpTest_two_reduced` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 1043 | `KAM.Certificate.cexpTest_large_pin` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |

### Lunar A-L

| Draft line / node | Lean declaration | Verdict | Classification / reason |
|---|---|---|---|
| 56 | `KAM.Certificate.ExpWitness` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 63 | `KAM.Certificate.CertEmbedding` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 74 | `KAM.Certificate.Witnesses` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 81 | `KAM.Certificate.PackLayout` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 91 | `KAM.Certificate.PackedAdvice` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. F12/F13 guards must be made explicit in consumers. |
| 101 | `KAM.Certificate.ProductAdvice` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 108 | `KAM.Certificate.ProductKey` | PWN | Verbatim engine stand-in. Representation/index alias; no hidden mathematical premise. |
| 110 | `KAM.Certificate.AdviceBook` | PWN | Verbatim engine stand-in. Representation/index alias; no hidden mathematical premise. |
| 114 | `KAM.Certificate.ModelConfig` | PWN | Verbatim engine stand-in. DATA/configuration: untrusted decoder function plus advice, each decoded value rechecked. |
| 128 | `KAM.Certificate.CertParams` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 149 | `KAM.Certificate.TorusCertificate` | PWN | Verbatim engine stand-in. DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 173 | `KAM.Certificate.checkStatic` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 177 | `KAM.Certificate.checkHamBounds` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 180 | `KAM.Certificate.checkEmbedding` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 183 | `KAM.Certificate.checkInvariance` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 186 | `KAM.Certificate.checkEnergy` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 189 | `KAM.Certificate.checkGram` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 193 | `KAM.Certificate.checkTorsion` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 196 | `KAM.Certificate.checkSmallness` | PWN | Verbatim engine stand-in. ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 200 | `KAM.Certificate.checkTorusCertificate` | PWN | Verbatim engine stand-in. DEN: concrete body reviewed on its whole carrier. |
| 214 | `KAM.Certificate.isDiophantine_of_index_map` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 222 | `KAM.Certificate.lunarNuMinus_rot_isDiophantine` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 225 | `KAM.Certificate.lunarNuPlus_rot_isDiophantine` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 228 | `KAM.Certificate.lunarNuMinus_rot_half_isDiophantine` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 232 | `KAM.Certificate.lunarNuPlus_rot_half_isDiophantine` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 253 | `KAM.SpinOrbit.soRotMap` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 257 | `KAM.SpinOrbit.soRotMapInv` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 260 | `KAM.SpinOrbit.soRotMapInv_soRotMap` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 263 | `KAM.SpinOrbit.soRotMap_soRotMapInv` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 268 | `KAM.SpinOrbit.soRotMap_symplectic` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 273 | `KAM.SpinOrbit.soRotHC` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 276 | `KAM.SpinOrbit.hamiltonianVectorFieldℂ_soRotHC` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 282 | `KAM.SpinOrbit.soRotHamExpr` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 290 | `KAM.SpinOrbit.soRotHamExpr_eval` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 294 | `KAM.SpinOrbit.soRotHamExpr_clock` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 298 | `KAM.SpinOrbit.soRotHamExprScaled` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 300 | `KAM.SpinOrbit.soRotHamExprScaled_eval` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 303 | `KAM.SpinOrbit.soRotHamExprScaled_clock` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 308 | `KAM.SpinOrbit.invarianceError_const_mul` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 323 | `KAM.SpinOrbit.lunarRotFreq` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 325 | `KAM.SpinOrbit.lunarRotFreqMinus_eq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 329 | `KAM.SpinOrbit.lunarRotFreqPlus_eq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 334 | `KAM.SpinOrbit.isDiophantine_smul` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 338 | `KAM.SpinOrbit.lunarRotFreqMinus_isDiophantine` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 341 | `KAM.SpinOrbit.lunarRotFreqPlus_isDiophantine` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 352 | `KAM.SpinOrbit.lunarR1TimeScale` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 354 | `KAM.SpinOrbit.lunarR1Scalar` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 357 | `KAM.SpinOrbit.lunarR1Kappa` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 360 | `KAM.SpinOrbit.lunarR1` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 378 | `KAM.SpinOrbit.lunarR1Kappa_div` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 381 | `KAM.SpinOrbit.lunarLowerErr` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 383 | `KAM.SpinOrbit.lunarUpperErr` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 385 | `KAM.SpinOrbit.lunarLowerDisp` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 387 | `KAM.SpinOrbit.lunarUpperDisp` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 396 | `KAM.SpinOrbit.SoGraphCert` | PWN | DATA: untrusted finite carrier/configuration; no mathematical conclusion field. |
| 408 | `KAM.SpinOrbit.checkSoGraph` | PWN | ALG: intended operation; whole-carrier implementation and correctness unpaid. |
| 415 | `KAM.SpinOrbit.SoGraph.torus_of_rot` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 437 | `KAM.SpinOrbit.soBarrier_of_exact_rotTorus` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 451 | `KAM.SpinOrbit.soBarrier_of_cert` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 461 | `KAM.SpinOrbit.soRotBarrier_of_cert` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 478 | `KAM.SpinOrbit.soPrecision` | PWN | DEN: concrete body reviewed on its whole carrier. |
| 481 | `KAM.SpinOrbit.SoBackend` | PWN | Representation/index alias; no hidden mathematical premise. |
| 484 | `KAM.SpinOrbit.lunarLowerCert` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 486 | `KAM.SpinOrbit.lunarUpperCert` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 488 | `KAM.SpinOrbit.lunarLowerCert_ham` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 491 | `KAM.SpinOrbit.lunarUpperCert_ham` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 494 | `KAM.SpinOrbit.lunarLowerCert_params` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 497 | `KAM.SpinOrbit.lunarUpperCert_params` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 500 | `KAM.SpinOrbit.lunarLowerCert_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 502 | `KAM.SpinOrbit.lunarUpperCert_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 504 | `KAM.SpinOrbit.lunarLowerGraph_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 506 | `KAM.SpinOrbit.lunarUpperGraph_passes` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 509 | `KAM.SpinOrbit.lunarLowerCert_freq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 512 | `KAM.SpinOrbit.lunarUpperCert_freq` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 516 | `KAM.SpinOrbit.lunarPLo` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 518 | `KAM.SpinOrbit.lunarPHi` | PWN | ENDPOINT: literal/generated/example data unpaid. |
| 520 | `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 524 | `KAM.SpinOrbit.lunar_barriers` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |
| 531 | `KAM.SpinOrbit.lunar_spin_confinement` | PWN | Reviewed statement; proof unpaid (`sorryAx`). |

## Errata, deviations, uncertainties and handoff

No new defect in a pinned mathematical source, frozen declaration or I-G1 blueprint was established. F12/F13 are defects in the proposed packed-product validation/rounding derivation, with exact locations and quoted contracts above; do not attribute them to HL19 or silently repair the source. The auditor introduced no mathematical deviation.

Documented design changes are O5's rotated client and R1, positive time scaling, `ModelConfig α` with untrusted decoder/advice and an added product key, and the split signature files. O1/O2/O3/O4 remain binding. Numerical G-J invoices, literal window endpoints, precision choice, data packaging, implementation/proof completion and full replay costs remain unpaid. Production code must import landed arithmetic rather than copy placeholder implementations.

Files written in the repository: this report only. Approach: independent refute-first comparison of the complete branch scope and current design surface, explicit arithmetic counterexamples to the new product derivation, exact landed/fixed-interface comparison, a fresh engine bridge, exhaustive theorem-axiom probes, concrete coordinate/arithmetic proofs, targeted build, serialized kernel replay and final source lint. Completion of this audit does not close the checker, lunar certificates or campaign theorem.

## Additional completed receipts and input hashes

Concrete signature gate: `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .lake/abi-scratch/SOAudit5Concrete.lean`: exit 0, zero warnings/errors. It proves the two explicit coordinate inverse identities, symplecticity, generic `mantCheck_sound` directly from the landed lawful interface, and the R1 rational constant. The first scratch attempt had an incorrect tactic reference `Bool.and_eq_true.mp`; this was corrected to rewriting with `Bool.and_eq_true`. No production source was changed and no budget override was used. All four named concrete results print exactly `[propext, Classical.choice, Quot.sound]`.

SHA-256 of audited inputs:

```text
2dca1501bc4b6c94d39428cbabfb7d2e02161a651168b0e21e277e241cd89fac  .drafts/design/SOSignatures.lean
9eafc5968a3dd2aa9257d5fc48be9886c6ca2ae5c2c72c2d63514fae02f68a7e  .drafts/design/SOSignaturesLunar.lean
9b53ffc81a9af6d56042d89a9de4e733c27cc281f182b8be3e82ec1c09245657  docs/tracks/SO/design/SO-LEAN-DESIGN.md
```

## Reproducible engine bridge used by the probe

Appended after the engine draft (no placeholder in this bridge):

```lean
namespace KAM.Certificate
open KAM
theorem audit5_engine_bridge {n : ℕ} {α : Type} [CertArith α]
    {c : TorusCertificate n α} {ωstar : Fin n → ℝ} (h : G1Hyps c ωstar)
    (hdio : IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar) :
    CertifiedTorus c ωstar := by
  have G := KAM.Iso.Apost.g1_explicit h.hn h.hτ h.hρinf h.hρinfρ
    h.hM h.hσK h.hσB h.hσT h.hμ h.hγbar h.hσω h.hν ωstar h.hωstar
  obtain ⟨K, s, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    G.2.2.2 c.D c.H c.K c.params.s c.params.γ c.params.err c.params.E0
      h.hopen h.htransl h.hholo h.hper h.hreal h.hbd h.hK h.hKp h.hKr h.hball h.hDK h.hG
      h.hTu h.hTb h.hs1 h.hsσ h.hν1 h.hν2 h.hγ h.hγγbar hdio h.he0 h.hE h.hEn h.hC1
  exact ⟨K, s, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    fun θ hθ => (h10 θ hθ).trans h.hdisp, h11.trans h.hdisp⟩
end KAM.Certificate
```

Final lint: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` from the audit worktree: **exit 0**, exact output:

```text
check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No stale-generated-root exception was needed. Final protected-path diff remained empty; tracked `git diff --check` and report whitespace validation passed. Final status contained only the new requested report. All auditor-created scratch probes, inventories, scripts and logs were removed after their evidence was transcribed here.
