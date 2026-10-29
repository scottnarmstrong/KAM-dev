# SO-DESIGN independent audit 6 — Revision 6

2026-10-29. **Overall verdict: FAIL (design acceptance), F14. F12 and F13 are closed at design level.** The new anti-carry reconstruction and positive-scale overlap argument are sound. A separate raw-input length/zero-padding attachment is missing from the stated whole-product checking algorithm, so its exact output-length contract does not follow from the listed guards. F15 is a nonblocking units correction in the numerical G-J table. Neither finding alleges an accepting execution of a completed Lean checker: its body is still `sorry`.

No new frozen anchor, provider or production Lean module is supplied. No SO declaration is seal-ready. Existing I-G1 remains SEALED and unchanged; the fresh engine bridge, targeted build and kernel replay are separate receipts for that existing engine. The draft checker, numerical certificates and lunar confinement theorem remain unproved.

## Scope and authority

The report destination is the user's exact absolute path in this worktree, overriding the generic brief's main-worktree destination and earlier handoff filenames. Only this report was written in repository content. Temporary scripts, probes and logs were confined to `.lake/abi-scratch/` and removed after transcription. No state-changing git command was used.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the Round 6 focus in `docs/tracks/SO/audits/SO-DESIGN-handoff.md`, audit 5 and the earlier finding history, `.drafts/handoff-SO-DESIGN.md`, the current design and both draft signature files. Checked the controlling `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md` (D30, O1–O5), the proposal/pilot, SO-REPLAY2, and the landed SO-GEN2 report at `/root/code/KAM-inp/docs/tracks/SO/studies/SO-GEN2-rotated-frame-candidates.md`. The removed SO-GEN2 worktree was not needed. Engine authorities: frozen `IsoenergeticKam.lean` and its strip/Gram/normal-frame/torsion/average/energy/Diophantine definitions, `KAM/Iso/Charts/Inputs.lean`, `KAM/Iso/Apost/G1.lean`, track I statement, and blueprint-I `bpI:p0:g1` / `bpI:p2:g1`. No `docs/tracks/SO/statement.md` exists here; the owner plan and exact design appendix supply the proposed SO surface. Tracks N/P receive no new anchor or node.

Audited HEAD `65dacca4e110ca491dfb632487362c0dd45fa98f`; `inp` and the shared signature checkout were observed at `c97c960083d7c8900659d434e5c759ebff9e1a3e`. Ran `git diff inp...HEAD`; the full diff has eight added files, 4,806 additions and no deletions: audits 1–5, handoff, the 2,551-line design and the 51-line stand-in checker. All are new-file hunks. Additionally inspected `git diff fc1231d2..HEAD -- docs/tracks/SO/design/SO-LEAN-DESIGN.md` for the Revision 6 delta. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

## Findings

### F12 — CLOSED at design level: advice reconstruction is now inside the injective range

Locations: design §1.16 and Appendix A-E lines 1123–1221; draft `.drafts/design/SOSignatures.lean:270–368`.

For a decoded residual list `e`, `intSlotsBound_sound` gives the exact packed residual and `|e_i| ≤ 2^(logs i)`. The concrete guard `reconFits` checks

```text
2 (2^scale |r_i| + 2^(logs i)) < 2^w.
```

Thus `2 |2^scale r_i + e_i| < 2^w` by the triangle inequality. The exact shard convolution is independently in that range by `shardFits`; equal lengths and `packSum_reconSlots` give equal packings. `packSum_injective` therefore equates the exact convolution with `2^scale r + e`. This proves the advertised local error bound for signed advice, arbitrary logs and every scale, without trusting advice or assuming the desired coefficientwise conclusion.

A fresh `audit6_reconstruct` proves the complete `shard_reconstruct` statement from the lower-level contracts, without using `shard_reconstruct`, `checkShard_sound` or whole-product soundness. It elaborates at default budgets. Its proof still depends on `sorryAx` through those draft lower-level contracts; this is a verified interface composition, not an implementation proof. Separately, `SOAudit6.recon_scalar` proves the numerical guard inequality from integer arithmetic with no draft imports or `sorryAx`.

The concrete draft controls `packSum_audit5_cancel` and `reconFits_audit5_rejects` both have only `[propext]`. Advice `[16,-1,0]` still packs to zero at width four but the new guard rejects it. No wrong coefficient was found under the complete reconstruction guards: 73,386 exhaustive two-slot candidate comparisons, 1,308 passing reconstructions, and 100,000 randomized reconstruction controls had no failure. These finite controls supplement the general argument; they do not execute placeholder checkers.

### F13 — CLOSED at design level: reject scale zero before overlap-add

Locations: design Appendix A-E 1202–1249; draft 349–396; validation plan §8 P3/P4.

`shapeOK` now requires `1 ≤ scale`, and `checkPackedProduct_guards` exports it from checker success. `checkPackedProduct_scale_zero` states unconditional rejection for zero scale and arbitrary data. At positive scale, two windows of length `2L-1`, shifted by `L>0`, cover any slot at most twice; `2 * 2^(scale-1) = 2^scale`. The independent Lean proof `SOAudit6.overlap_budget` verifies this identity for every positive natural scale. The out-of-target bound similarly adds at most two `2^outLog` contributions, with zero advice there.

A concrete positive overlap control uses `L=2`, `w=8`, `scale=1`:

```text
A=[[1,1],[0,0]], B=[[1,1],[1,0]].
Exact shard windows: [1,2,1], [1,1,0], [0,0,0].
Rounded advice:     [0,1,0], [0,0,0], [0,0,0].
Global exact:       [1,2,2,1,0,0,0].
Combined advice:    [0,1,0,0,0,0,0].
Global error:       [1,0,2,1,0,0,0].
```

Each local error is at most one; all reconstruction guards fit at width eight, and the overlap attains the promised bound two. This is an arithmetic control of the specified guards, not a claim that an unimplemented checker was evaluated. P3/P4 whole-check regression proofs and `checkPackedProduct_scale_zero` remain SO-POLY-B/SO-TEST obligations; only the two F12 draft controls are already implemented.

### F14 — MEDIUM, blocking design acceptance: raw factor lengths are lost by padding but still occur in the output contract

Locations: design Appendix A-E lines 1184–1197 (`blockLen`, `cut`, `combined`), 1202–1233 (`shapeOK`, whole check and success guards), 1244–1249 (`checkPackedProduct_sound`); draft 332–396.

Quoted definitions/contracts: `cut` is a dense factor cut into blocks, “the last one zero-padded”; `combined` takes **only** `adv`; `shapeOK` also takes only `adv`. The whole-check description checks “`shapeOK` ... the dense factors cut by `cut`, and `checkShard` on every shard”. Yet the soundness theorem's first conjunct is

```lean
adv.combined.length = (listConv da db).length
```

for arbitrary raw `da db : List ℤ`, with checker success as its only premise. Neither the described algorithm nor `checkPackedProduct_guards` attaches the raw lengths to the factor layouts or the fixed product window. `cut_length` only proves the lengths of the padded blocks.

Concrete counterexample to derivability from the **listed** checks: choose a valid two-slot factor layout (with a singleton transverse axis if dimension two is desired), `blockLen=2`, `w=8`, `scale=1`, a full three-slot target/product window and one advice window `[0,0,0]`. Compare calls with

```text
da=db=[0]        and        da=db=[0,0].
```

Both cut to exactly `[[0,0]]`. Both therefore have the same shard count, the same length-three zero advice, zero exact shard convolution, zero decoded residual and passing `shardFits`/`reconFits` (`2*(0+1)<256`). The advice-dependent structural checks are identical, including positive scale, valid layouts, target inclusion and zero high advice. Consequently every listed test has the same result in both calls. But the raw convolution lengths are respectively **one** and **three**. A fixed `adv.combined.length` cannot equal both. In the ordinary three-slot product-window implementation it is three, so the first call fails the literal contract despite passing those listed checks. This occurs at positive scale, without carries or excessive overlap.

The padding alias was independently decided in Lean, and the length contradiction proved by `omega`. This is a missing input-shape check in the specification, not a claim that the theorem type is inherently unimplementable: the current `sorry` checker could be replaced by one that performs the missing checks.

**Required change:** validate the original `da.length` and `db.length` against the canonical dense lengths determined by `adv.la` and `adv.lb` (including a specified empty-factor policy), and specify how `combined` is cropped to their exact convolution length. Export these raw-shape/cropping facts from success, or an equivalent checkable relation that excludes the padding alias. Test the two calls above: the incompatible short input must be rejected, or change the result representation/contract explicitly. Keep the public theorem's sole premise checker success; do not move raw-shape assumptions to callers. Valid advice layouts alone and checks on already padded blocks cannot supply this fact. Do not silently weaken the existing exact-length conjunct.

### F15 — LOW, nonblocking: copied B₀ values use the unscaled convention

Locations: design §6 table line 523 defines `B₀ = c · sup |ΔP₁|`, while line 526 copies `1.25e-80 / 2.29e-80`. SO-GEN2 report lines 157–175 explicitly defines its tabulated `B₀ = sup|ΔJ|`, without `c`; it notes that `B₁` and `B_r` carry `c`. Here `ΔP₁=ΔJ` when the other candidate components are fixed.

**Required documentation correction:** retain the design's energy-budget definition and multiply the copied SO-GEN2 B₀ figures by `237/125`, or label the copied figures as unscaled and check `c B₀ ≤ e/4`. On the displayed figures this gives approximately `2.37e-80 / 4.34184e-80`, still below `e/4 = 1.0075e-78 / 1.96e-78`. This does not invalidate the numerical feasibility margin. Decimal summaries are not literal outward-rounded Lean certificates.

## Round 6 focus and engine fidelity

| Node / focus | Verdict | Reason |
|---|---|---|
| F12 anti-carry repair | PASS WITH NOTES | Correct checkable reconstruction route; independent composition elaborates, foundational algorithms/proofs unpaid. |
| F13 scale and overlap | PASS WITH NOTES | Positive scale exported; general overlap identity verified; whole-check tests still planned. |
| Whole-product exact input/output shape | FAIL | F14: raw lengths are not attached before padding; local coefficient bounds themselves survive. |
| `checkPackedProduct_sound` premises | PASS | Only `checkPackedProduct adv da db = true`; no coefficientwise conclusion hidden in an input hypothesis. |
| Exact-product strip/model consumers | PASS WITH NOTES | Correct intended `a*b` enclosures; their implementation closure still needs the whole-product glue and F14 repair. |
| Updated R1 | PASS WITH NOTES | Constants and measured choices match SO-GEN2, with F15's B₀ units correction. |
| Both signature files and stand-ins | PASS | Both gates pass; appendix/shared copies agree; 20 stand-ins are verbatim; renamed `soIsDiophantine_smul` avoids the existing Iso short name. |
| Existing I-G1 anchor | PASS WITH NOTES | SEALED, unchanged; bridge/build/replay pass. No new seal is requested or justified. |
| New SO anchors; N/P anchors | N/A | None supplied. |

The fresh `audit6_engine_bridge` applies every premise of `IG1Body` in the literal order to `(c.D,c.H,c.K,c.params.s,c.params.γ,c.params.err,c.params.E0)`. Its axiom set is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` despite the draft types surrounding it. This checks actual engine applicability once the proposed checker produces `G1Hyps`; it does not prove that production step.

| Literal engine binder group | Supplier / assessment |
|---|---|
| n≥2, τ≥n−1, positive smaller radius, radius ordering | Static facts, exact casts from natural τ / rational parameters. |
| Positive M, σK, σB, σT, μ, γbar, ν; σω>1 | Static fields; `g1_explicit` uses μ,γbar,σω,ν; `isoC1` uses μ,ν,γbar in its own order. |
| Exact nonzero reference vector and endpoint margins | `checkStatic_freq` with proved `FreqEncloses`; reference vector is never replaced by the box centre. |
| Open D, translation invariance, H holomorphy/periodicity/reality | Certified nonvanishing for division, then structural expression/domain facts. |
| All five field/derivative bounds on D | `checkHamBounds_sound`, third-order jets and positive-dimension norm bridges. |
| K holomorphic/primary/real; ball inclusion and DK margin | Law-free denotation plus embedding sub-check. |
| Bilinear Gram determinant and inverse rows | Gram sub-check; no Hermitian substitution. |
| Full bordered torsion average determinant and inverse rows | Same n, exact (n+1)-square shapes, literal `DH(K)N`, true inverse derivative, entry enclosures and continuity before averaging. |
| Ray interval, γ positivity/upper bound, e nonnegative | Static fields and exact-vector margins. |
| `IsDiophantine γ τ ωstar` | External mathematical premise; box membership is the external enclosure/typing fact. |
| Full invariance error and averaged energy bounds | Recomputed on actual K̃, not the scalar pilot identity. |
| `isoC1` smallness; both displacement bounds | Smallness producer and `hdisp`; C₂=C₃=`isoC2`. |
| Every output clause | Exact invariance and pointwise energy, strip/real/primary conditions, μ/2 ball, derivative half-margin and both closeness bounds retained. |

`G1Hyps` and `StaticFacts` are derived propositions, not certificate input proof fields. Backend laws are fixed arithmetic infrastructure. The general route still covers n≥2, arbitrary finite Hamiltonian expressions including certified nonvanishing division, and general Fourier embeddings in every coordinate. A proved Diophantine vector and its rational enclosure are required; rational independence alone does not imply the quantitative premise. Model enclosures use the literal open `complexStrip`; tagged 2π degrees, successful-call exponential pins, reciprocal witnesses and bilinear Gram semantics remain compatible. No earlier F1–F11 contract repair is reversed.

## R1 comparison and feasibility limits

SO-GEN2's reported choices agree with the current definitions: `c=237/125`, `M=σK=σB=σT=1987/1000`, `s=1+10⁻⁶`, `μ=1/160`, `ρ=1/70`, `ρ∞=1/70000`, `γ=γbar=κ/42=316000/7000007`. The last identity was independently proved over ℚ. `σB-μ=7923/4000=1.98075`, above both reported checker-style Gram bounds (lower approximately 1.979943, upper approximately 1.9801). The grid-sup alternative is explicitly not adopted; it is not used to justify R1.

The design also copies SO-GEN2's threshold `10^(-74.669)`, L=88 / 318 bits, errors `4.03e-78 / 7.84e-78`, smallness summaries, domain discs, single normalized character witness, pinHalvings=0 / pinOrder=1, and bordered 3×3 torsion witness. The zero pin input follows from odd v and must still be checked on emitted data; a small residual alone would not imply it. The nearly singular top torsion block is harmless because the check inverts the full bordered matrix. `soPrecision=320` remains a design choice pending data replay, not a proof that 318-bit generator enclosures reproduce at that backend precision.

Withdrawing `B₂≤10⁻⁹⁰` is mathematically legitimate because DK/Gram/torsion bounds are recomputed on the actual K̃. It is a disclosed planning-budget change, not an omitted G1 premise. The original-coordinate headline is unchanged: `P₀=p`, the symplectic shear and time rescaling lead back to the landed graph/barrier core, and final `lunar_spin_confinement` states unique global `soField` solutions with `|p(t)-1|≤33/1000` for the explicit momentum-window region. Window endpoints, actual certificate bodies, all passing checks and theorem proofs remain unpaid.

SO-GEN2 is Python/data evidence; this audit compared its report and did not rerun its generator or certify those numbers in Lean. No numerical source receipt is promoted to a proved checker result. The design's “certified” R1 summaries should be read at this external-evaluator level until the planned Lean checks replay.

Replay GO is an owner ruling supported by prototypes. End-to-end design-B glue, complex products, middle-size replay and data packaging still need their specified receipts. Updated estimates total 8,700 pre + 9,700 post = 18,400 lines; 30–40% overrun is 23,920–25,760. These are package estimates including historically landed work, not permission to exceed 1,500 lines per Lean module. SO-POLY-B's 700-line allowance is especially uncertain with layout/padding/anti-carry/overlap proofs; split modules as needed. Existing pre-gate rotated/frequency/graph packages can proceed in DAG order. SO-DATA still waits on its actual enclosures/replay and packaging decision; this audit does not make that owner choice.

## Independent validation receipts

All auditor-owned Lean/Lake invocations were serialized and set `LEAN_NUM_THREADS=1`. Signature and build gates launch `nice -n 5`; direct kernel replay also used it. No clean, update, cache fetch, dependency-directory edit, budget override or generated-file repair was used.

1. `git diff inp...HEAD`, `git diff --stat inp...HEAD`, the focused Revision 6 delta and protected-path diff described above: documentation/script scope only. `git diff --check inp...HEAD` and tracked `git diff --check`: exit 0, no output.
2. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/design/SOSignatures.lean`: exit 0, 125 warnings, all `declaration uses 'sorry'`, zero errors. Same command for `SOSignaturesLunar.lean`: exit 0, 54 such warnings, zero errors.
3. `python3 -I docs/tracks/SO/design/check_so_standins.py .drafts/design/SOSignatures.lean .drafts/design/SOSignaturesLunar.lean`: exit 0. `stand-ins checked: 20`; engine `1152 lines; lines over 100 chars: none`; lunar `540 lines; lines over 100 chars: none`; `PASS`. Independently checked both appendix blocks and both `/root/code/KAM-inp/.drafts/design/` copies for byte identity (apart from the Markdown fence terminal newline).
4. Same signature gate, separately and serially on `.lake/abi-scratch/SOSignaturesAudit6.lean` and `SOSignaturesLunarAudit6.lean`: exit 0, 125/54 expected warnings and zero errors. Engine prints axioms of all 78 draft theorems, the fresh engine bridge and existing engine; lunar prints all 37 draft theorem axioms. A second engine run including the independent reconstruction proof also exits 0 with 125 expected warnings and zero errors. Probe lengths stay below 1,500.
5. Of 115 draft theorem entries (counting lunar declarations including its separate Diophantine stand-ins), 113 have `sorryAx`; only the two concrete F12 controls are proved. Engine draft counts: 61 full `[propext, sorryAx, Classical.choice, Quot.sound]`, ten `[propext, sorryAx]`, four `[sorryAx]`, one `[propext, sorryAx, Quot.sound]`, two `[propext]`. Lunar: 36 full four-axiom lists and one `[sorryAx]`. The bridge and engine have only the standard three axioms. The reconstruction composition has `sorryAx` inherited from its draft dependencies, explicitly not independent proof closure.
6. Same signature gate on `.lake/abi-scratch/SOAudit6Concrete.lean`: final exit 0, zero warnings/errors; exact axiom output below. This independent file proves the guard inequality, positive-scale overlap identity, padding alias, length contradiction and R1 rational arithmetic. The first attempt used nonexistent name `abs_add`; replacing it with `abs_add_le` corrected the scratch proof. No production file or budget was changed.
7. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-design-so KAM.Iso.Apost.G1`: exit 0, exact output:

```text
[inp-gate] slot 2 acquired 15:20:59 for KAM.Iso.Apost.G1
Build completed successfully (3224 jobs).
```

8. Kernel replay and final lint receipts are transcribed at the end of this report. No draft `.olean` is claimed or replayed: signature gates elaborate transient design input; kernel replay covers the named existing landed dependencies only.
9. Comment-masked scans of the two draft files found respectively 125/54 intentional `sorry` tokens, with no `axiom`, `admit`, `unsafe`, `opaque`, `EuclideanSpace`, `native_decide`, `implemented_by` or `set_option` in code. Both drafts have the copyright/module/public imports/module documentation/exposed public section. The draft placeholders are explicitly unfrozen design material and would fail production proof hygiene; they are not waived for a provider or claimed as allowed production `sorry`. No provider or DRAFT_SORRY theorem-anchor import is introduced. Production source hygiene is checked independently by lint.

Input SHA-256:

```text
eea4f3fc736fb86cc67a0120e4236f5c0ace175e765804b66e2718442bd68cb0  .drafts/design/SOSignatures.lean
f898ee080a52c631387764a2b7d1ab18e2df79b50442b18e5e05aa43f3209c6c  .drafts/design/SOSignaturesLunar.lean
4c46df8d9a0569b22d5cb0cc2bf952aa9567e8576ff1423f13589ab18b401694  docs/tracks/SO/design/SO-LEAN-DESIGN.md
5b61190362c9a6ee18bc82361b3ef6547cbb2b792cbc45c26641b1731f0f18ec  inp:docs/tracks/SO/studies/SO-GEN2-rotated-frame-candidates.md
```

## Declaration-by-declaration assessment and definition classification

PWN means **PASS WITH NOTES for the proposed statement/object only**, with no proof or seal claim. ALG denotes an intended algorithm whose implementation is still a placeholder; DEN a concrete denotation; DATA an untrusted carrier/configuration; PROP a semantic or derived proposition; ENDPOINT literal/generated data still unpaid. All omitted/bad-list defaults were assessed on the whole carrier: denotations use literal zero, matrix enclosures require present entries, invalid advice must fail or yield the documented crude model enclosure. F14 requires raw factor lengths to be rejected internally. The lunar engine stand-ins are reviewed as exact duplicates, not independent new production implementations.

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
| 225 | `KAM.Certificate.PackLayout` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 233 | `KAM.Certificate.PackLayout.slot` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 236 | `KAM.Certificate.PackLayout.dense` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 239 | `KAM.Certificate.PackLayout.prodKey` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 243 | `KAM.Certificate.PackLayout.compat` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 246 | `KAM.Certificate.intEval` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 251 | `KAM.Certificate.PackLayout.intEval_mul` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 262 | `KAM.Certificate.PackedAdvice` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
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
| 341 | `KAM.Certificate.PackedAdvice.shardLogs` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 344 | `KAM.Certificate.PackedAdvice.combined` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 347 | `KAM.Certificate.PackedAdvice.inBox` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 354 | `KAM.Certificate.PackedAdvice.shapeOK` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 360 | `KAM.Certificate.checkShard` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 363 | `KAM.Certificate.checkShard_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 372 | `KAM.Certificate.checkPackedProduct` | FAIL | F14: missing raw-length/cropping attachment in the stated algorithm. |
| 375 | `KAM.Certificate.checkPackedProduct_guards` | PWN | Positive scale/local guards sound in shape; export raw lengths too (F14). |
| 383 | `KAM.Certificate.checkPackedProduct_scale_zero` | PWN | Correct unconditional scale-zero rejection contract; implementation/proof unpaid. |
| 391 | `KAM.Certificate.checkPackedProduct_sound` | FAIL | F14: missing raw-length/cropping attachment in the stated algorithm. |
| 400 | `KAM.Certificate.packSum_audit5_cancel` | PASS | Concrete F12 control, proved by `decide`; axioms `[propext]`. |
| 402 | `KAM.Certificate.reconFits_audit5_rejects` | PASS | Concrete F12 control, proved by `decide`; axioms `[propext]`. |
| 406 | `KAM.Certificate.CertPoly.toMants` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 409 | `KAM.Certificate.CertPoly.toMants_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 420 | `KAM.Certificate.CertPoly.mulPacked` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 424 | `KAM.Certificate.CertPoly.mulPacked_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 433 | `KAM.Certificate.ProductAdvice` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 440 | `KAM.Certificate.ProductKey` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 442 | `KAM.Certificate.AdviceBook` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 451 | `KAM.Certificate.ModelConfig` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 464 | `KAM.Certificate.CertModel.add` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 473 | `KAM.Certificate.CertModel.mul` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 477 | `KAM.Certificate.CertModel.trim` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 481 | `KAM.Certificate.CertModel.toDeg` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 486 | `KAM.Certificate.CertModel.ofDeriv` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 489 | `KAM.Certificate.CertModel.Encloses.ofDeriv` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 494 | `KAM.Certificate.CertModel.Encloses.add` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 499 | `KAM.Certificate.CertModel.Encloses.mul` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 505 | `KAM.Certificate.CertModel.Encloses.trim` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 510 | `KAM.Certificate.CertModel.Encloses.toDeg` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 516 | `KAM.Certificate.CertModel.Encloses.average` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 543 | `KAM.Certificate.ExpWitness` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 550 | `KAM.Certificate.expPinBall` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 552 | `KAM.Certificate.expPinBall_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 558 | `KAM.Certificate.expWitnessRadius` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 563 | `KAM.Certificate.expWitnessRadius_pin` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 569 | `KAM.Certificate.expWitness_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 577 | `KAM.Certificate.invWitnessRadius` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 580 | `KAM.Certificate.invWitness_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 602 | `KAM.Certificate.Slp.balls` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 605 | `KAM.Certificate.Slp.val_mem_ball` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 613 | `KAM.Certificate.HamExpr.nonvanishingOn_of_balls` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 620 | `KAM.Certificate.CertEmbedding` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 626 | `KAM.Certificate.CertEmbedding.eval` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 633 | `KAM.Certificate.CertEmbedding.differentiable_eval` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 636 | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 640 | `KAM.Certificate.CertEmbedding.isRealOnReals` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 648 | `KAM.Certificate.Witnesses` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 655 | `KAM.Certificate.Slp.compose` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 660 | `KAM.Certificate.Slp.compose_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 678 | `KAM.Certificate.ModelMatrix` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 682 | `KAM.Certificate.ModelMatrix.Encloses` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 690 | `KAM.Certificate.polyMatrix` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 695 | `KAM.Certificate.gramModels` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 698 | `KAM.Certificate.gramModels_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 706 | `KAM.Certificate.gramCheck` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 710 | `KAM.Certificate.gramCheck_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 721 | `KAM.Certificate.torsionIdx` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 728 | `KAM.Certificate.torsionModels` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 737 | `KAM.Certificate.torsionModels_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 755 | `KAM.Certificate.torsionAvgCheck` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 759 | `KAM.Certificate.torsionAvgCheck_shape` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 763 | `KAM.Certificate.torsionAvgCheck_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 776 | `KAM.Certificate.checkRealLowerBound` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 779 | `KAM.Certificate.checkRealLowerBound_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 799 | `KAM.Certificate.CertParams` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 820 | `KAM.Certificate.TorusCertificate` | PWN | DATA: untrusted data/configuration or representation alias; no hidden torus proof. |
| 845 | `KAM.Certificate.TorusCertificate.D` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 848 | `KAM.Certificate.TorusCertificate.H` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 850 | `KAM.Certificate.TorusCertificate.K` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 860 | `KAM.Certificate.checkStatic` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 864 | `KAM.Certificate.checkHamBounds` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 867 | `KAM.Certificate.checkEmbedding` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 870 | `KAM.Certificate.checkInvariance` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 873 | `KAM.Certificate.checkEnergy` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 876 | `KAM.Certificate.checkGram` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 880 | `KAM.Certificate.checkTorsion` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 883 | `KAM.Certificate.checkSmallness` | PWN | ALG: intended operation reviewed; implementation and correctness unpaid. |
| 887 | `KAM.Certificate.checkTorusCertificate` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 897 | `KAM.Certificate.G1Hyps` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 950 | `KAM.Certificate.CertifiedTorus` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 969 | `KAM.Certificate.StaticFacts` | PWN | PROP: semantic/derived facts; no external conclusion assumed. |
| 994 | `KAM.Certificate.checkStatic_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 998 | `KAM.Certificate.checkStatic_freq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1004 | `KAM.Certificate.TorusCertificate.emb_structural` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1008 | `KAM.Certificate.checkHamBounds_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1017 | `KAM.Certificate.TorusCertificate.ham_structural` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1025 | `KAM.Certificate.checkEmbedding_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1031 | `KAM.Certificate.checkGram_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1036 | `KAM.Certificate.checkInvariance_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1042 | `KAM.Certificate.checkEnergy_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1049 | `KAM.Certificate.checkTorsion_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1056 | `KAM.Certificate.checkSmallness_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1067 | `KAM.Certificate.checkTorusCertificate_hyps` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1077 | `KAM.Certificate.checkTorusCertificate_sound` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1093 | `KAM.Certificate.toyHam3` | PWN | DEN/check: concrete body reviewed on its whole carrier. |
| 1100 | `KAM.Certificate.toyCert3` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1102 | `KAM.Certificate.toyCert3_ham` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1104 | `KAM.Certificate.toyCert3_err_pos` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1106 | `KAM.Certificate.toyCert3_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1108 | `KAM.Certificate.toyCert3_freq` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1111 | `KAM.Certificate.toyCert3_torus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1116 | `KAM.Certificate.toyCert2` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1118 | `KAM.Certificate.toyCert2d` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1120 | `KAM.Certificate.toyCert2_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1122 | `KAM.Certificate.toyCert2d_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1124 | `KAM.Certificate.toyCert2_torus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1126 | `KAM.Certificate.toyCert2d_torus` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1130 | `KAM.Certificate.toyRatCert` | PWN | ENDPOINT: generated/example/literal data unpaid. |
| 1132 | `KAM.Certificate.toyRatCert_passes` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1138 | `KAM.Certificate.cexpTest_zero_small` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1140 | `KAM.Certificate.cexpTest_zero_large` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1142 | `KAM.Certificate.cexpTest_two_rejected` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1144 | `KAM.Certificate.cexpTest_two_reduced` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |
| 1146 | `KAM.Certificate.cexpTest_large_pin` | PWN | Proposed statement reviewed; proof unpaid (`sorryAx`). |

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

### Engine drafts, fresh bridge and existing engine

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
'KAM.Certificate.checkShard_sound' depends on axioms: [propext, sorryAx]
'KAM.Certificate.checkPackedProduct_guards' depends on axioms: [sorryAx]
'KAM.Certificate.checkPackedProduct_scale_zero' depends on axioms: [sorryAx]
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
'_private._stdin.0.KAM.Certificate.audit6_engine_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
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

### Independent concrete controls

```text
'SOAudit6.recon_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'SOAudit6.overlap_budget' depends on axioms: [propext, Quot.sound]
'SOAudit6.padding_alias' does not depend on any axioms
'SOAudit6.length_conflict' depends on axioms: [propext, Quot.sound]
'SOAudit6.r1_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'SOAudit6.r1_gram_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'SOAudit6.positive_overlap' depends on axioms: [propext]
```

## Reproducible independent reconstruction proof

The following was appended to the current engine draft. Its lower-level draft dependencies remain unpaid; it establishes that the repaired local interfaces compose, not that the whole checker is proved.

```lean
namespace KAM.Certificate
-- Independent reconstruction from the lower-level contracts; no shard_reconstruct call.
theorem audit6_reconstruct {w scale L : ℕ} {logs : ℕ → ℕ} {A B : List (List ℤ)} {s : ℕ}
    {r : List ℤ} (hA : ∀ x ∈ A, x.length = L) (hB : ∀ x ∈ B, x.length = L)
    (hfit : shardFits w L A B s = true) (hrec : reconFits w scale logs r = true)
    (hlen : r.length = 2 * L - 1)
    (hdec : intSlotsBound w (2 * L - 1) logs
      ((∑ i ∈ Finset.range (s + 1), packSum w (A.getD i []) * packSum w (B.getD (s - i) [])) -
        2 ^ scale * packSum w r) = true) :
    ∀ i < 2 * L - 1, |(shardConv L A B s).getD i 0 - 2 ^ scale * r.getD i 0| ≤ 2 ^ logs i := by
  obtain ⟨e, helen, he, hpack⟩ := intSlotsBound_sound hdec
  have hlength : e.length = r.length := helen.trans hlen.symm
  have hreclen : (reconSlots scale r e).length = 2 * L - 1 := by
    simp [reconSlots, hlen, helen]
  have hrange := slotsBounded_reconSlots hrec hlength (by simpa only [hlen] using he)
  have hp : packSum w (shardConv L A B s) = packSum w (reconSlots scale r e) := by
    rw [packSum_reconSlots w scale hlength.symm, ← hpack, packSum_shardConv w L A B hA hB]
    ring
  have hlist := packSum_injective (slotsBounded_shardConv hfit) hrange
    ((shardConv_length L A B s).trans hreclen.symm) hp
  intro i hi
  have hir : i < r.length := by omega
  have hie : i < e.length := by omega
  have hget : (shardConv L A B s).getD i 0 = 2 ^ scale * r.getD i 0 + e.getD i 0 := by
    rw [hlist]
    simp [reconSlots, List.getD, List.getElem?_eq_getElem hir, List.getElem?_eq_getElem hie,
      List.getElem?_zipWith]
  rw [hget]
  simpa only [add_sub_cancel_left] using he i hi
end KAM.Certificate
#print axioms KAM.Certificate.audit6_reconstruct
```

## Errata, deviations and handoff

No new defect in a pinned mathematical source, frozen theorem or blueprint statement was established. F14 is a design-interface/algorithm gap, and F15 is a numerical-budget transcription/units mismatch; neither is an HL19 erratum. The auditor introduced no mathematical deviation and edited no implementation or protected file. Carried deviations remain explicit: exact-frequency box plus external exact vector, bounded auxiliary-action domain, Fourier energy-lift data checked on the actual candidate, rotated client/time scaling, O1 momentum window and O4 continuous graphs. Revision 6 discloses the withdrawn obsolete B₂ planning target.

Files written in repository content: this report only. Approach: full branch scope comparison and focused Revision 6 review, explicit guard/reconstruction and padding counterexamples, exact engine bridge, exhaustive draft theorem-axiom probes, concrete arithmetic proofs, targeted build, serial kernel replay and final source lint. Required follow-through is F14's raw-shape/cropping repair and F15's units correction; all checker algorithms, end-to-end replay/data and SO theorem proofs remain separately unpaid.

## Final kernel, lint and protected-path receipts

From `/root/code/KAM-inp` (the shared landed build used by the signature gate):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1 KAM.Certificate.Arith.Fixed KAM.Certificate.Expr.Diff KAM.Certificate.Clock KAM.SpinOrbit.HamExpr KAM.SpinOrbit.Graph.Inverse
```

Exit **0**, exact output:

```text
replaying KAM.SpinOrbit.Graph.Inverse
replaying KAM.SpinOrbit.HamExpr
replaying KAM.Certificate.Clock
replaying KAM.Certificate.Expr.Diff
replaying KAM.Certificate.Arith.Fixed
replaying KAM.Iso.Apost.G1
```

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

No stale-generated-root exception was needed. Final `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty; `git diff --check inp...HEAD` and `git diff --check` pass. The report has balanced code fences, no trailing whitespace, all 239 inventoried draft declarations represented, and complete axiom output for all 115 draft theorem entries. Rechecked the input hashes against the audited copies. All auditor-created scratch probes, inventories, scripts, full-diff capture and logs were removed after transcription. Final repository status contains only `?? docs/tracks/SO/audits/SO-DESIGN-audit-6.md`.
