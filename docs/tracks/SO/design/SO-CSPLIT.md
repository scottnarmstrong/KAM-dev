# SO-CSPLIT: segmented proof of the heavy sub-checks under the 10 GB kernel cap (design, Phase 1)

Status: design, **revision 2** (2026-10-30), answering:
- design audit 1 (`SO-CSPLIT-design-audit-1.md`: F1–F4, N1–N4);
- delta audit 2 (`SO-CSPLIT-design-audit-2.md`: F1, N1, N2).

Dispositions are in §1. Owner ruling D39; track SO.

**The exact Lean interface is `.drafts/design/SOCsplitSignatures.lean`.** It is a module-form scratch file
elaborated against the landed `inp` build (`lake env lean` through the compile gate, default heartbeats: rc = 0,
no errors). It holds:
- 33 definitions with their bodies, 3 structures and 1 instance;
- 49 theorems with exact statements. **36 are proved.** **13 are `sorry`:**
  - the five comparator reflections (`eq_of_termsBeq`, `CertPoly.eq_of_segBeq`, `CertModel.eq_of_segBeq`,
    `eq_of_pairBeq`, `eq_of_cacheBeq`);
  - the M1 core (`pushSlot_slot_lt`, `composeStep_congr`, `seed_slot_of_mem`, `shadowRun_agree`,
    `composeOpsAux_slot_persist`, `ComposeCkpt.compose_eq`);
  - two table lemmas (`modelMatMul_eq_of_entries`, `gramModels_eq_of_entries`).

The Lean blocks below are excerpts of that file; where they differ, the file is authoritative. No library Lean
file was written, and no kernel probe was run by me.
This revises route E of SO-COMPOSE-SPLIT (branch `inp-socsplit`) and answers its audit 1. The Python evidence is two
new untrusted tools, `scripts/spin_orbit/csplit_census.py` and `csplit_plan.py`. Their outputs are in
`/mnt/HC_Volume_106379410/kam-data/so-csplit/` (`census_{lower,upper}.json`, `plan_*.json`).

Inputs read:
- the study and audit on `inp-socsplit`;
- SO-DATA3's interim notes 1–3, kernel logs (`kam-data/so-data3/kpass`, `probes`) and pass modules (`inp-sodata3`:
  `KAM/SpinOrbit/Data/{Lower/Pass,GramSplit}`, `LunarAssemblyV2.lean`);
- the landed checker: `KAM/Certificate/Expr/{Slp,Compose,ComposeModels}.lean`, `Defs.lean`, `Gram.lean`,
  `Torsion/{Models,Average}.lean`, `Model/{Ops,Terms,Exp}.lean`, `Poly/{MulPacked,Sparse,Advice}.lean`;
- sharp-v2's `CertificateSharp/Kernel/{Prune,Shared}.lean`, `V2/Engine.lean` and `Frame/Majorants.lean`;
- the handoffs SO-KDEPTH, SO-PACKFIX and SO-BALLDY;
- SO-LOCK-COST rev 3 (`inp-lockdesign`, unlanded);
- SO-DATA3's isolated product, witness and L = 14 probes, written for this design
  (`kam-data/so-data3/product-probes.md`, `probes/csplit/`).

## 0. Summary

- **Shape (§3): prove the landed Bools.** Each of `checkInvariance`, `checkEnergy`, `checkGram`, `checkTorsion`,
  `checkFrameN` and `checkFrameT` is proved `= true` for the certificate. The proof uses segment and stage theorems
  plus generic chaining lemmas that are computation-only (agreement and congruence, with no enclosures). No landed
  definition or statement changes. SO-DATA3's `landedBase_check_of` and `checkTorusCertificateV2_refined_of`, and
  hence the v2 soundness `checkV2With_sound`, apply verbatim. A new `BaseChecker` is rejected (§3.1).
- **Four mechanisms, all generic and audited once:**
  - **M0, literal jet bridge.** `base.ham.jet = jetLit` is proved once per Hamiltonian, shared by both tori. No
    other theorem forces the jet compiler, which costs 6.9 GB on its own (BALLDY J0). That one fact explains why
    even the 86-slot pruned energy probe was OOM-killed.
  - **M1, composition chain (route E, extended).** The segments run a *shadow* fold seeded from a ledger of slot
    pairs. The shadow fold skips dead infallible ops, which the audited route E did not do. A chain lemma proves
    `Slp.compose … = some (wanted.map ledger)` for the landed, unpruned program.
  - **M2, stage memoization (Level 2).** Every heavy closed subterm of the Gram, torsion and frame computations is
    proved equal to a literal, one entry per theorem. Table lemmas let `rw` move these equalities under the
    `List.ofFn`/`buildMat` binders of the landed bodies, and the residual Bool is closed by `decide +kernel` on
    literals.
  - **M3, product and op split (part of Level 1, mandatory).** SO-DATA3 measured the 503×503 product forced in
    full at 69 s and 9.89 GB, +6.4 GB over its literal baseline. Every packed product is therefore proved apart
    from its consumer, in two theorems:
    - its shard checks (≈ 0.47 GB per shard);
    - its target decode (≈ 3.1 GB at 8,536 target slots, *projected* by subtraction, P1 − RR, pending G4).

    The two ops of the program that contain packed products (slot 10 and the slot-28 character witness) are
    one-op segments, proved by rewriting with their memoized products.
- **Granularity (§4) comes from measurements.**
  - The kernel receipts of §4.1 give a stable law: peak ≈ 1.5 GB + (0.04–0.13 GB per kernel-second) × time.
  - The kernel keeps every reduction result of a declaration in its caches. Memory is therefore bounded by bounding
    *work per declaration*, not live data.
  - The census measures work in backend primitives (`FixedB` calls). Calibrated against two receipts, one call
    costs 0.3–0.6 ms and 25–42 KB of kernel.
  - **Budget: 75 k backend calls per theorem** (predicted peak 3.4–5.1 GB), re-fitted by the Phase-2 gate
    (§4.5).
  - Packed products come from SO-DATA3's forced probes, not from the census:
    - one shard costs 4 s and 0.47 GB;
    - the decode and assembly of the 847-term output are *projected* at 26 s and 3.1 GB (P1 − RR; measured
      only by gate G4).
  - Per torus that is 129 packed products in SO-DATA3's report (128 evaluated: §4.3), 667–718 shards and
    351–358 k target slots.
  - L = 14 does not rescue a whole compose: its `checkEnergy` was OOM-killed. That is consistent with M0, because
    the jet alone costs 6.9 GB at any L.
- **Ledger (§5): ≈ 10.4 / 10.3 MB of Lean literals per torus (formatted definitions plus overhead estimates),
  ≈ 20.7 MB for both, far below the 50 MB flag.** The final receipt is the generator's `du -b`.
  - cfgFull 155 models (2.5 MB); cfgLow 324 models (5.6 MB); 384 distinct across the chains.
  - Stage literals and decoded product memos add about 2.0 MB.
  - Plans, metas and module headers add about 0.2 MB.
- **Cost (§6), per torus:**
  - about 460–480 theorems, each in its own module and built serially under the cap (about 256 of them are
    packed-product shard and decode theorems);
  - 10.7 M backend calls plus 128 packed products of kernel work;
  - **≈ 3.0–4.3 CPU-h per torus, 6–8.6 CPU-h for both.**
- **Lock (§7).** M0–M3 carry over unchanged in shape. The lock's models are about 6.5× larger and its program is
  3.56× longer, so the projection is 25–60 CPU-h and a ledger of roughly 100–200 MB. The volume flag applies to the
  lock, not to the lunar tori (§10, owner item O2).
- **Packages (§8).** About 1,650 Lean lines in four packages (SO-CSEG-A, -B, -L2, -L3), plus a Python emitter
  (SO-CSEG-GEN, ~900 lines, extending `sofx_*`) and two Phase-2 calibration gates (SO-CSEG-CAL-1, CAL-2).

## 1. What changed since SO-COMPOSE-SPLIT, and the audit's findings

| | SO-COMPOSE-SPLIT (v1 data) | now (SO-DATA3, v2 certifier) |
|---|---|---|
| precision, truncation | CertFixed 320, about 8.5k terms per heavy model | **CertFixed 96, L = 20: mean 488 terms, max 1,067** (census) |
| heavy×heavy products in the program | 1 (slot 10) | 3 packed: slot 10 (`[0,10]`, 503×503) and the two residual products of the slot-28 character witness |
| what dies at the cap | estimated | **measured**: `checkEnergy`, `checkInvariance`, `checkGram` (even one defect row), and pruned `[v0]` (86 slots) |
| per-model literal | 1.4–1.7 MB | **≈ 16 KB** (31.7 B per term, measured on SO-DATA3's `tm` rows) |

Audit 1 and where it is answered:

| finding | answer |
|---|---|
| F1: P11 is an `isSome`, not forced; PF28 − P11 is invalid | No calibration here uses those receipts. The law of §4.1 uses only completed passes with forced Bool or equality results, plus SO-PACKFIX's forced shard and SO-DATA3's forced product (P1: sum, length, radius and degree of all 847 terms). The Phase-2 gate (§4.5) forces equality to complete literals, with matched imports. |
| F2: invariants of route E | §3.3 lists the full invariant set: whole-pair agreement, meta indices, length checks and terminal exports. It adds the dead-op extension and its argument. |
| F3: terminal outputs missing; union vs sum; per-chain counts | The planner exports the wanted slots and counts the ledger as a union, separately per chain and torus. Volumes: see N1 below. |
| F4: additive memory law; Level 2 "needed regardless" | The law is now a fitted *rate*, with its mechanism (§4.1) and an explicit gate. Level 2 is needed because a single Gram defect row was OOM-killed (SO-DATA3 interim 3), which is a measured fact. |
| F5: sharing needs a projection | M1 yields one `composeOps` success plus a ledger; `ComposeCkpt.compose_eq` projects to any `wanted ⊆ ledger`, so invariance (`d1Slots`) and energy (`[v0]`) share the run. |
| F6: simpler alternatives | §3.1 and §3.6. Measured sharing and pruning (sharp-v2's `checkInvEnShared`, `composePruned`) were OOM-killed (SO-DATA3 round 2). Pruning is kept *inside* M1 as dead-op skipping. |

Design audit 1 (codex-1) and revision 1:

| finding | disposition |
|---|---|
| F1 (blocking): no elaborating signatures | `.drafts/design/SOCsplitSignatures.lean`: every definition with a body; every lemma of §3 with its exact statement; elaborates at default heartbeats (§3, excerpts). It covers `segOk`, `planOk`, `AgreeOn`, `composeStep_congr`, `composeStep_infallible`, `shadowRun_agree`, the four comparators with reflection, the bridges, `all_range_of_lt`, `gramCheck_eq_of_rows`, `expWitnessRadius*`, and the two assembly templates. `meta` is renamed `stateMeta`; the shape premise is explicit (`hrows`, `hcols`). |
| F2: the product carrier | `polyProduct_eq_of_mulPacked` (→ `some (out.1.toErrTerms, out.2)`) and `CertPoly.mulPacked_eq_of_parts` (II decoded negated into the real component; RI and IR into the imaginary component, as landed). Both are **proved** in the file. |
| F3: the sparse-product contract | `packedRealProduct_eq_nil_left/right` (`some ([], 0)`), `packedRealProduct_eq_of_sparse`, and `checkPackedSp_of_groups`: the verbatim non-shard prefix `checkPackedSpPrefix`, a coverage premise over `PackedAdvice.shardRange`, and per-group `checkShardAt` at the exact `spBlocks`/`spMax` arguments. All **proved**. |
| F4: `segOk_one_of` | `segOk` is factored as `segPrefixOk` (S1, S2, all bounds) `&&` the shadow run `&&` `segResultOk` (S3 metadata, S4). `segOk_one_of` takes `hprefix` and `hresult` and is **proved**; `segOk` is never assumed. |
| N1: prospective counts; bytes not complete | §4.3 is the plan the planner now **emits** (its `SegSpec` rows are in the plan JSON), with forced one-op cuts. §5 gives **complete** emitted bytes: definitions with degree, radius and cached norm, module headers, plan and metas, stage literals, product memos. |
| N2: product split is a projection | §4.1–4.2 now label the shard/decode split (RR vs P1) a projection by subtraction, pending gate G4. GB are decimal; the cgroup cap `MemoryMax=10G` is 10 GiB = 10.74 GB. |
| N3: calibration order | CAL is split: CAL-1 (G0–G5, standalone probes, after A and L3) and CAL-2 (G6, G7, after L2 and the B bridges); §4.5, §8. |
| N4: sharing changes the plan proposition | `planOk C len` no longer mentions `wanted`; each projection adds the cheap `wantedOk C wanted` (`compose_eq`'s `hw`). One `hplan` and the same `hseg` serve `[v0]` and `d1Slots` (templates `checkEnergy_of_ckpt`, `checkInvariance_of_ckpt`, proved from `compose_eq`). |

**Design signals from the elaboration** (default heartbeats; nothing raised):
- `simp only [torsionModels, …]` over the landed body exhausts `whnf`, and `congr 1` on `sumUp` does too.
- Both proofs became explicit `unfold`/`rw`/`congrArg` chains, and the generated proofs follow the same rule:
  rewriting only, never `simp` over a landed checker body.

Delta audit 2 and revision 2:

| finding | disposition |
|---|---|
| F1 (blocking): `shadowRun_agree` false on its carrier (a retained future slot can be a skipped dead op) | **Adopted** the proposed signature: new premise `hR : ∀ i, R i → i < σ.len`. Its conclusion keeps old slots (`R`) plus the live or fallible new slots of the segment. The counterexample is now the **proved** negative contract test `shadowRun_agree_needs_hR` (shadow run, landed run, failed agreement at `fun _ => True`). The intended caller (`R := s.imports`) discharges `hR` by the **proved** `ComposeCkpt.imports_lt_seed_len`, from `planOk`'s import bound `a < s.start`, `segPrefixOk`'s `m.len = s.start`, and the seed's length `m.len` (`seed_stateMeta`). `compose_eq` and the two templates are unchanged and consistent. `compose_eq` gets `hplan` and, through `segOk = segPrefixOk && …`, every `segPrefixOk`. Both templates consume only `compose_eq`. Axioms: the two new theorems use `[propext, Classical.choice, Quot.sound]`; the templates still inherit `sorryAx` from the admitted `compose_eq`. |
| N1: volume totals are estimates | §5 is relabelled **formatted-definition plus overhead estimates**, with every estimated item listed. The planner now counts UTF-8 bytes, formats the metas at their real boundary lengths, and drops the product memo of the dead cfgLow slot 10 (−6,401 B lower). The final receipt stays the generator's `du -b` plus a line-count check of every emitted module (the gate). |
| N2: superseded claims in summary and tables | The projection qualifiers are propagated to §0. The evaluated count (128) is in §4.3–4.4. Names are corrected (`all_range_of_lt`; the templates in SO-CSEG-B). |

## 2. Facts that fix the design

1. **The kernel's memory grows with the work of one declaration.** The type checker caches every `whnf` and
   infer result of a declaration until the declaration is done. Every receipt in §4.1 fits
   peak ≈ base + r·t, with r = 0.04–0.13 GB per kernel-second. Splitting the *work* across declarations is
   therefore the only lever; reducing the live data alone is not. Lean 4.35 checks the declarations of a file
   concurrently, so each heavy theorem sits alone in its module (SO-DATA3's rule, kept).
2. **The jet compiler is the single largest fixed cost.**
   - Forcing `c.ham.jet.prog` costs 54 s and 3.9 GB for the spine (K0), and 59 s and 6.9 GB with every op forced
     (J0), against BALLDY's whole `checkHamBounds` at 91 s and 8.98 GB.
   - SO-DATA3's EN probe (`Slp.composePruned … base.ham.jet.prog …`) and every landed sub-check that mentions
     `c.ham.jet` pay this first.
   - M0 removes it from every segment theorem.
3. **`composeStep` reads only `st.len`, `st.nExp`, `st.nInv`, `st.cache` and the pairs `st.slot W a` of its
   operands.**
   - `const`, `action`, `add` and `mul` always return `some`.
   - `const`, `action`, `add` and `mul` leave `nExp`, `nInv` and `cache` unchanged.
   - `pushSlot` never changes a slot below `len`.
   - These are the facts of audit 1 F2, plus infallibility, which is new.
4. **The heavy work is outside the program, too.**
   - `gramCheck` evaluates 9 `DKᵀDK` products and 8 `B·G` products, all packed.
   - `torsionModels` evaluates the cfgLow composition and then about 100 packed matrix products (`[4,0]`–`[4,9]`).
   - `checkFrameN` and `checkFrameT` recompute `gramCheck`, and FrameT also recomputes `torsionModels`.
5. **A packed product is the heaviest single unit, and it fits only when split.**
   - SO-DATA3 forced the 503×503 product `[0,10]` in full (7 shards of 1,312 slots at w = 207 bits; 847 output
     terms) from literal operands: **69 s, 9.89 GB**, against a 3.50 GB literal baseline.
   - Its parts: one shard costs 10.8 s and 4.18 GB (+0.7 GB). All 7 shards (`packedRealProduct … .isSome`) cost
     36 s and 6.78 GB (+3.3 GB). By subtraction, the rest, about 3.1 GB, is the decode of the 8,536-slot target
     (`dyadicTerms`), `toErrTerms`, `truncPoly` and `errRadius`. This is a projection, not a measured isolated
     decode (N2; gate G4).
   - So a whole product is too close to the cap to share a theorem with anything. One shard group (measured as
     part of RR) or one decode (projected) is expected to fit.
   - Per torus there are 129 packed products (3 cfgFull, 126 cfgLow), 667 / 718 shards and 351 / 358 k target
     slots (lower / upper). Their targets at cfgLow are 1.2–4.3 k slots, smaller than `[0,10]`'s 8.5 k.
   - The other 485 products of the program are scalar × model (`directItems`, up to 1 × 1,067). These are census
     work, not packed.

## 3. Proof shape

### 3.1 Choice: prove the landed Bools (option A), not a new `BaseChecker` (option B)

**Option A** proves `checkInvariance base = true` and the rest from smaller theorems:
- `landedBase_check_of` (SO-DATA3, `LunarAssemblyV2.lean`) turns the seven facts into `landedBase.check base = true`;
- `checkTorusCertificateV2_refined_of` adds `checkHamClaim`, `checkFrameMajorants` and `refinedCore`;
- `checkTorusCertificateV2_sound` gives `CertifiedTorus`.

Nothing on that path changes, and nothing new is trusted. Every new lemma is an equation between computable terms.

**Option B** would be a new `segBase : BaseChecker` whose `check` reads ledger data. It needs either the ledger
inside the certificate or a checker family `segBase L`. Its `sound` needs either the same agreement argument as A
(and then gains nothing) or enclosure checkpoints (route S: a re-derived invariance, energy and torsion contract,
about 900 more lines, a new audited soundness proof and a second assembly entry). Its only advantage, tolerating a
mirror that is not bit-exact, is not needed: SO-DATA3 shows the mirror bit-identical on `Slp.balls`
(887 slots), byte-identical regenerations, and passing verdicts on all sub-checks.

**Decision: A.** Route S stays the documented fallback for risk R1 (§9).

### 3.2 M0: the literal jet bridge

```lean
def keyBeq : CertKey → CertKey → Bool                       -- tail-recursive `&&`
def SlpOp.beq : SlpOp → SlpOp → Bool                        -- eight arms, `false` across
def opsBeq : List SlpOp → List SlpOp → Bool                 -- `a.beq b && opsBeq as bs`
def HamJet.beq (J J' : HamJet) : Bool :=
  opsBeq J.prog.ops J'.prog.ops && J.v0 == J'.v0 && J.d1 == J'.d1 && J.d2 == J'.d2 && J.d3 == J'.d3
theorem HamJet.eq_of_beq {J J' : HamJet} (h : J.beq J' = true) : J = J'      -- proved
```
`&&` puts the recursive call in tail position, so the kernel iterates. The derived `DecidableEq` on `List` would
nest one `whnf` per element and risk the depth limit at 887 ops. The reflection lemmas `eq_of_keyBeq`,
`SlpOp.eq_of_beq` and `eq_of_opsBeq` are proved.

`lower_jet : base.ham.jet = jetLit` is proved as `HamJet.eq_of_beq (by decide +kernel)`.
- `jetLit : HamJet` is emitted from the mirror (`sofx_lunar.jet()`), which SO-DATA3 found identical to Lean's
  `(soRotHamExprScaled lunarR2TimeScale).jet` via `#eval`.
- Both tori share `soRotHamExprScaled lunarR2TimeScale`, so one theorem in a shared module serves both.
- Expected cost: J0 plus the comparison, ≈ 7–7.5 GB. That is the largest theorem of the plan, and it is measured
  first (gate G0).
- The same `HamJet.beq` is SO-LOCK-COST's G1b `jetBeq`, so one package serves both campaigns.

Every later theorem rewrites `c.ham.jet` to `jetLit` (`rw [lower_jet]`) and never reduces the compiler.
- Optional, recommended: `checkHamBounds` and `checkHamClaim` can be re-proved the same way. That would take
  them from 9.75 and 10.24 GB (HamClaim is 2 % under the cap) to about 3–4 GB.

### 3.3 M1: the composition chain (route E with a shadow fold)

**Data (untrusted, emitted).** `ComposeMeta` (`len`, `nExp`, `nInv`, `cache`), `SegSpec` (`start`, `stop`,
`live`, `imports`, `exports`) and `ComposeCkpt` (`segs`, `metas`, `ledger : List (ℕ × (CertModel α × α))`), as in the
file.
- `C.pairOpt i` is the first ledger match.
- `C.pair W i := (C.pairOpt i).getD (slotEntry W zeroModel)`, the same default as `ComposeState.slot`.

**The shadow fold** (file §B):
```lean
def SlpOp.fallible : SlpOp → Bool                      -- char, exp, inv, sqrt
def shadowStep (n) (K) (wit) (W) (cfg) (pe) (s : SegSpec) (st : ComposeState α) (op : SlpOp) :
    Option (ComposeState α) :=
  if s.live.contains st.len || op.fallible then composeStep n K wit W cfg pe st op
  else some (st.pushSlot W zeroModel)
def shadowRun … (s : SegSpec) : Option (ComposeState α) → List SlpOp → Option (ComposeState α)
  -- strict loop, as `composeOpsAux`
def ComposeState.seed (W) (m : ComposeMeta α) (C : ComposeCkpt α) (imps : List ℕ) : ComposeState α :=
  { rev := (List.range m.len).reverse.map fun i =>
      if imps.contains i then C.pair W i else slotEntry W zeroModel
    len := m.len, nExp := m.nExp, nInv := m.nInv, cache := m.cache }
```

**`C.segOk n ops K wit W cfg pe j : Bool`** is `C.segPrefixOk ops j && (shadow run from the seed) && C.segResultOk
W ops j st`. All indexing is `[j]?` with a `false` fallback. It checks, for `s = C.segs[j]`:
- **(S1) Metas.** `C.metas[j].len = s.start` and `C.metas[j+1]` exists.
- **(S2) Reads.** For each `i ∈ [start, stop)` with `liveEff s i ops[i]`, every `a ∈ opDeps ops[i]` satisfies
  `a < i` and either `a ∈ s.imports` or (`start ≤ a` and `liveEff s a ops[a]`). This is index arithmetic only.
- **(S3) Run.** The shadow fold of `(ops.drop start).take (stop - start)` from `seed (metas[j]) C s.imports` is
  `some st`, and `meta st = C.metas[j+1]`. Comparing `cache` uses `cacheBeq`.
- **(S4) Exports.** For each `e ∈ s.exports`: `start ≤ e < stop`, `liveEff s e ops[e]`, and
  `pairBeq (st.slot W e) (C.pair e) = true`. This compares the **whole pair**, model and cached norm (audit F2).

**`C.planOk len : Bool`** works on indices only, with no model compared:
- `segsTile` of `[0, len)`;
- `metas.length = segs.length + 1` and the initial meta `⟨0, 0, 0, []⟩`;
- `ledgerAsc`;
- every import of segment `j` is `< segs[j].start` and is `C.exported`;
- every ledger slot is `C.exported`.

**`C.wantedOk wanted`** checks that every wanted slot is on the ledger. It is separate from `planOk`, so one
`hplan` serves every projection (audit N4).

**Bool equalities** (file §A):
- `ccBeq`, `termsBeq`, `CertPoly.segBeq`, `CertModel.segBeq` (degree, radius, terms), `pairBeq` (with the cached
  norm), `cacheBeq` (key, polynomial, radius, in order) and `ComposeMeta.beq`.
- They are tail-recursive `&&` chains, which SO-KDEPTH measured as depth-safe at 20 k elements. Derived
  `DecidableEq` on `List` is never used.
- `[DecidableEq α]` is used only for the leaves. For `CertFixed P` it is a **new instance**,
  `instDecidableEqCertFixedSeg`, through the mantissa (`decidable_of_iff` with `CertFixed.eq_of_m`). This is the
  one instance SO-CSEG-A adds on a landed type; an alternative is a leaf comparator passed as an argument.
- Reflection lemmas give `… = true → … = …` (stated; `sorry` in the file).

**Chain theorem (proved once, generic in all data).**
```lean
theorem ComposeCkpt.compose_eq [DecidableEq α] (n : ℕ) (K : CertEmbedding α) (wit : Witnesses α)
    (W : CertWeight) (cfg : ModelConfig α) (pe : PiEnclosure α) (C : ComposeCkpt α)
    {p : Slp} {wanted : List ℕ} (hplan : C.planOk p.ops.length = true)
    (hseg : ∀ j < C.segs.length, C.segOk n p.ops K wit W cfg pe j = true)
    (hw : C.wantedOk wanted = true) :
    Slp.compose n p K wit W cfg pe wanted = some (wanted.map fun i => (C.pair W i).1)
```
**Its lemmas** (file §B):
- `composeStep_congr` (to `Option.Rel` of `AgreeOn W (R ∪ {len})`, reads in `R` and below `len`);
- `composeStep_infallible` (`∃ m, … = some (st.pushSlot W m)`), **proved**;
- `seed_slot_of_mem`, and `seed_stateMeta` (proved);
- `shadowRun_agree`, with the domain premise `hR : ∀ i, R i → i < σ.len` (audit 2 F1). It is discharged for
  `R := s.imports` by `ComposeCkpt.imports_lt_seed_len` (proved). `shadowRun_agree_needs_hR` (proved) shows the
  premise is necessary;
- `composeOpsAux_slot_persist`;
- `pushSlot_slot_lt`.

**Proof (computation-only).**

Let `M_j` be the landed run on the prefix `p.ops.take segs[j].start`. The induction invariant **I(j)** is:
`M_j = some X` with `meta X = metas[j]` and `X.slot W e = C.pair e` for every ledger `e < segs[j].start`.

- **Base.** `composeOps` of `[]` is the empty state, so I(0) holds.
- **Step `j → j+1`.** Let `σ` be the seed, and maintain `AgreeOn R σ' X'`: equal `len`/`nExp`/`nInv`/`cache`, and
  equal pairs on the index set `R`. Start with `R = s.imports`, which holds by I(j) and the seed. `R` is confined
  to the old prefix (`hR`: every import `< s.start = m.len`), so a later dead op can never be a retained slot.
  For the op at
  `i = len`:
  - **If `liveEff`:** its operands are in `R` (S2). `composeStep_congr` gives both `some` with agreement on
    `R ∪ {i}`, or both `none`; S3 excludes `none`.
  - **Otherwise the op is infallible:** `composeStep_infallible` gives `some X''` with `len + 1` and the same
    `nExp`/`nInv`/`cache`. The shadow pushes a placeholder; `R` is unchanged and `i ∉ R`.
  - **At the end:** agreement on meta gives `meta = metas[j+1]`. S4 together with `exports ⊆ liveEff ⊆ R` gives the
    new ledger slots. `pushSlot` persistence keeps the older ones. `composeOpsAux` of an append is the composite
    (`composeOps_eq`, `foldl_append`), and `take start ++ (drop start).take (stop - start) = take stop`.
- **End.** The tiling gives `M_m = composeOps … p.ops`; `Slp.compose` projects `wanted ⊆ ledger`.

**The extension beyond the audited route E** is the dead-op case. It needs only two facts, both about the four
infallible arms of the landed `composeStep` (a `simp` of each arm):
- the four arms return `some`;
- the four arms leave `nExp`, `nInv` and `cache` unchanged.

Fallible ops always run, because `liveEff` makes them live. A dead fallible op can therefore never be skipped, and
a dead failure is never hidden. This is the audit F6 caveat ("success of the whole run, including dead operations
that can fail"). In the lunar program, all 14 `char` ops run; 13 are cache hits (exact shifts).

**Sharing.** One plan per chain:
- **cfgFull.** The templates `checkEnergy_of_ckpt` and `checkInvariance_of_ckpt` (file §F) take the same `hplan`
  and `hseg` and differ only in `hw` and the residual (energy, or the 4 rows). Both are proved from `compose_eq`.
- **cfgLow.** `wanted = torsionSlots`.

**The lunar plans (§4.3).** 38 cfgFull and 70 cfgLow segments per torus.

### 3.4 M2: stage memoization (Gram, torsion, frames, the tails)

**The pattern.** For a closed heavy subterm `t`, a stage theorem proves `t = lit` (`decide +kernel` on a literal
`lit`); the consumer proof `rw`s it and decides the rest. This is SO-DATA3's FrameN pattern
(`rw [lower_gramCheck_eq]; decide +kernel`), generalized.

**Table lemmas** (file §E). The landed bodies build matrices under binders, so a closed equality cannot be
`rw`ritten there; generic lemmas over variables move the per-entry equalities inside.
- **Proved:**
  - `matMulEntry`, the `(i, j)` body of `modelMatMul`, with `modelMatMul_eq_buildMat` (`rfl`);
  - `matMulEntry_eq_of_products`;
  - `gramDefectRows_eq_of_entries`;
  - `gramCheck_eq_of_rows` (shape premise, memoized rows, then the landed `gramBoundsOk`/`maxCandidate`
    residual);
  - `torsionModels_eq_of_stages`;
  - `frameNModels_eq_of_stage`.
- **Stated, `sorry`:**
  - `modelMatMul_eq_of_entries` (explicit `hrows`, `hcols`);
  - `gramModels_eq_of_entries` (triangular reuse, as landed).

`torsionModels_eq_of_stages` has one premise per landed stage, each stated on the previous stages' results with
the landed keys and shapes, from `[4,0]` (`L·Gi`) to `[4,9]` (`d1·N`). Its conclusion is the landed final
`buildMat`. Since it is proved by `unfold; rw`, the premises are exactly the landed stage terms:
```lean
    (hN0 : modelMatMul W cfg pe [4, 0] (n + n) n n L Gi = N0)
    …
    (hTb : modelMatMul W cfg pe [4, 8] n (n + n) n
      (modelMatTranspose (n + n) n (modelMatOmega n n N0))
      (modelMatOmega n n (modelMatAdd W pe (n + n) n XN1
        (modelMatNeg (n + n) n (modelMatOmega n n (modelMatAdd W pe (n + n) n DN1 DN2))))) = Tb)
    (hY : modelMatMul W cfg pe [4, 9] 1 (n + n) n (d1Models n ms) (modelMatOmega n n N0) = Y) :
    torsionModels n e K wit Binv δβ box s W cfg pe =
      some (buildMat (n + 1) (n + 1) fun i j =>
        if i < n then (if j < n then modelMatrixEntry Tb i j else freqModel n box s i)
        else (if j < n then modelMatrixEntry Y 0 j else zeroModel))
```

**Recipes** (`L = lower`; `jet` = M0; `Cfull`, `Clow` = M1 plans):

| landed Bool | proof |
|---|---|
| `checkInvariance base` | the template `checkInvariance_of_ckpt` (proved from `compose_eq`, `checkInvariance_eq_of_compose`, `all_range_of_lt`) with `hjet := lower_jet`. The residual is `(List.range 4).all (row a)`, assembled by `all_range_of_lt` from **4 row theorems** (43 k, 0.1 k, 57 k, 59 k calls) on the literal `d1` models. |
| `checkEnergy base` | the template `checkEnergy_of_ckpt` with the same `hplan`/`hseg`, `hw` for `[v0]`, and **1** `energyOk …` theorem (3 k calls) |
| `checkGram base` | `checkGram_of_gramCheck` (proved) on the `gramCheck` equation below |
| `gramCheck … = some δβ` | `gramCheck_eq_of_rows` with **3 entry** theorems (`gramEntryModel`, 67–76 k calls; their 3 packed products each memoized by L1c) and **4 BG-entry** theorems (31–40 k; 2 memoized products each). Then `gramModels_eq_of_entries` and `gramDefectRows_eq_of_entries`; the final `gramBoundsOk` and the `maxCandidate` on literal rows are one cheap decide. |
| `checkTorsion base` | `checkTorsion_eq_of` (proved), then `torsionAvgCheck` on literal `T` (one decide) |
| `torsionModels … = some T` | `torsionModels_eq_of_stages`, built from: the cfgLow chain; `dkModels`, `dkwModels` and `gramInvModels` (one theorem each); **one theorem per matrix-product entry** (54 entries; their 106 packed products memoized by L1c; an entry over B splits per product: 54–75 theorems, §4.3); and the adds, transposes and omegas (cheap, one each) |
| `checkFrameN base bN bNt` | `checkFrameN_eq_of` with `frameNModels_eq_of_stage` (both proved). The `[4,0]` stage literal **is** torsion's `N`, so nothing is recomputed. Then 2 corner theorems (54 k calls each). |
| `checkFrameT base bT` | `checkFrameT_eq_of` (proved), then 1 corner theorem (33 k) |
| `checkFrameL base bL` | DK corner bounds (69 k calls): 1 theorem, unchanged (not yet run by SO-DATA3) |

Each `rw` in elaboration matches closed terms. The residual `decide +kernel` sees only literals. Risk R7
(accidental evaluation through defeq) is controlled in two ways:
- stating the table lemmas over variables, so the kernel checks an *application* of a proved lemma;
- a SO-CSEG-L2 test that the residual of a toy recipe reduces in negligible time.

### 3.5 M3: product and op split (Level 1, mandatory)

An op or stage entry that contains a packed product is never decided whole. Its own closed subterms are
memoized instead. There is still no new checker code: these are equation lemmas about the landed
`CertModel.mul`/`mulN`, `polyProduct`, `mulPacked`, `packedRealProduct` and `expWitnessRadius` bodies.
The chain of lemmas (file §D; all **proved**):
```lean
theorem CertModel.mulN_eq_of_polyProduct … (h : CertModel.polyProduct W cfg key a.poly b.poly = some out) :
    CertModel.mulN W cfg key a na b nb =
      ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1,
        upAdd (upAdd out.2 (errRadius W (out.1.map (truncErr cfg.cutoff))))
          (upAdd (upAdd (crossUp na b.rad) (crossUp nb a.rad)) (upMul a.rad b.rad))⟩
theorem polyProduct_eq_of_mulPacked … (ha : a.isConst = false) (hb : b.isConst = false)
    (hk : adviceLookup cfg.advice key = some (.packed P rr ii ri ir))
    (hp : CertPoly.mulPacked cfg.toMant W P rr ii ri ir a b = some out) :
    CertModel.polyProduct W cfg key a b = some (out.1.toErrTerms, out.2)            -- F2
theorem CertPoly.mulPacked_eq_of_parts … (hma : a.toMants dec P = some ma) (hmb : …)
    (hRR : packedRealProduct rr W (2 * P) ma.1 mb.1 = some pRR) (hII : … ii … ma.2 mb.2 …)
    (hRI : … ri … ma.1 mb.2 …) (hIR : … ir … ma.2 mb.1 …)
    (htRR : dyadicTerms (2 * P) rr.scale (fun v => ⟨v, ofInt 0⟩) pRR.1 = some tRR)
    (htII : dyadicTerms (2 * P) ii.scale (fun v => ⟨v, ofInt 0⟩) (pII.1.map fun t => (t.1, -t.2)) = some tII)
    (htRI : dyadicTerms (2 * P) ri.scale (fun v => ⟨ofInt 0, v⟩) pRI.1 = some tRI)
    (htIR : dyadicTerms (2 * P) ir.scale (fun v => ⟨ofInt 0, v⟩) pIR.1 = some tIR) :
    CertPoly.mulPacked dec W P rr ii ri ir a b =
      some (⟨tRR ++ tII ++ tRI ++ tIR⟩, ofRatUp (pRR.2 + pII.2 + pRI.2 + pIR.2))
theorem packedRealProduct_eq_nil_left … (hx : x.isEmpty = true) : packedRealProduct adv W P2 x y = some ([], 0)
theorem packedRealProduct_eq_nil_right … (hy : y.isEmpty = true) : … = some ([], 0)
theorem packedRealProduct_eq_of_sparse … (hx : x.isEmpty = false) (hy : y.isEmpty = false)
    (ha : adv.la.allSlots x = true) (hb : adv.lb.allSlots y = true)
    (hs : checkPackedSp adv (adv.la.slotTerms x) (adv.lb.slotTerms y) = true) :
    packedRealProduct adv W P2 x y = some (adv.targetTerms, adv.remainderBound W P2)       -- F3
def checkPackedSpPrefix (adv) (ea eb) : Bool          -- the non-shard prefix of `checkPackedSp`, verbatim
def PackedAdvice.shardRange (adv) : List ℕ            -- `List.range (spCount la + spCount lb - 1)`
def checkShardAt (adv) (ea eb) (s) : Bool             -- `checkShardSp` at the exact `spBlocks`/`spMax`
theorem checkPackedSp_of_groups (adv) (ea eb) (groups : List (List ℕ))
    (hpre : checkPackedSpPrefix adv ea eb = true)
    (hcover : ∀ s ∈ adv.shardRange, ∃ g ∈ groups, s ∈ g)
    (hgroups : ∀ g ∈ groups, g.all (checkShardAt adv ea eb) = true) :
    checkPackedSp adv ea eb = true                                                          -- F3
```
**Per packed part, two theorems, plus a cheap one:**
- **(a) the shard group.** The shards `checkShardSp … s`: at ≈ 0.47 GB each, all 7 fit one theorem (≈ 3.3 GB of
  work). Above 7, or under a lower B, they are grouped.
- **(b) the decode.** `dyadicTerms (2P) adv.scale … adv.targetTerms = some t_lit`: ≈ 3.1 GB at 8.5 k target slots,
  ≤ 1.6 GB at cfgLow's ≤ 4.3 k.
- **(c) `toMants` of the two literal operands:** cheap; it may merge into (a).

`checkPackedSp_of_groups`, `packedRealProduct_eq_of_sparse` (or the empty lemmas), `mulPacked_eq_of_parts` and
`polyProduct_eq_of_mulPacked` then assemble `polyProduct … = some (lit.toErrTerms, err)` with no kernel
evaluation. The real lunar embedding makes 3 of the 4 parts empty for every lunar product. The census
counts the truncation, `errRadius` and norm work of the product's consumer; that work stays in the consumer's
theorem (a segment or a stage entry).

**One-op segments for the two program ops with packed products.** These are slot 10 (`[0,10]`) and slot 28 (the
character witness: `expResidualProduct` with keys `[1,j]`, j = 0, 1, both packed `ir`).
- The plan forces the cuts `[10, 11)` and `[28, 29)`. Their operands are ledger slots (slot 10 reads slots 8 and
  5), and slot 28 reads the meta cache only.
- `segOk` for such a segment is not decided whole. It is proved (F4) through
  ```lean
  theorem ComposeCkpt.segOk_one_of … (hs : C.segs[j]? = some s) (hm : C.metas[j]? = some m)
      (hone : s.ops ops = [op])
      (hprefix : C.segPrefixOk ops j = true)                       -- S1, S2, bounds: one cheap decide
      (hop : shadowStep n K wit W cfg pe s (ComposeState.seed W m C s.imports) op = some st')
      (hresult : C.segResultOk W ops j st' = true) :               -- S3 meta, S4: a small decide
      C.segOk n ops K wit W cfg pe j = true                         -- proved
  theorem seed_slot_of_mem … (ha : imps.contains a = true) (hlt : a < m.len) :
      (ComposeState.seed W m C imps).slot W a = C.pair W a
  theorem shadowStep_of_live … (h : s.live.contains st.len = true) :
      shadowStep n K wit W cfg pe s st op = composeStep n K wit W cfg pe st op        -- proved
  ```
- `hop` is proved by rewriting:
  - slot 10: `composeStep` of `.mul`, `seed_slot_of_mem`, then `CertModel.mulN_eq_of_polyProduct` with the
    assembled `polyProduct` literal;
  - slot 28: `composeStep` of `.char`, `charSlot`, `charEntry`, then `charResolve_eq_of_radius` (cache miss, own
    key). Its radius premise comes from:
    - `expWitnessRadius_eq_of_pin`;
    - `expWitnessRadiusOf_eq_of_residuals`, which takes the two memoized `expResidualUp … j` values;
    - `expResidualProduct_eq_of_polyProduct`, which takes the (a)+(b) product literals.

    All are proved in the file.
- `hresult` is a small decide on literals.

SO-DATA3's C1 (`(charResolve … [2,0]).isSome`, 10.9 s, 3.66 GB) did not force the radius, so the packed residual
products inside `res` were not evaluated (audit F1). It is not used as a bound.

**Stage entries with packed products** (Gram, BG, torsion) use the same per-product memo:
- the entry theorem is stated through `matMulEntry_eq_of_products`, or the Gram analogue, with the products'
  `polyProduct` literals rewritten in;
- it keeps only the truncation, `errRadius`, `modelSum` and `toDeg` work, which is the census count.

### 3.6 Alternatives considered (measured where possible)

- **Pruning or sharing in the checker** (sharp-v2 `checkInvEnShared`, `composePruned`): OOM-killed (SO-DATA3
  round 2). Both force the jet; their live work is still 2.4 M calls for 215 slots in one declaration. Pruning
  survives inside M1 as dead-op skipping.
- **Full-state checkpoints** (literal `ComposeState` at every boundary, with no agreement lemma): rejected.
  - The ledger would carry dead slots (887 rather than about 160 per chain).
  - Each boundary equality would traverse the whole state: kernel `decide` does not short-circuit shared tails.
- **Data levers** (cutoff, precision, truncation): ruled out by SO-DATA3. The cost is bits, not terms; L = 20 is
  the minimal truncation.

## 4. Granularity from measurements

### 4.1 The memory law (receipts; forced results only)

| receipt | proposition | kernel time | peak | (peak − base)/time |
|---|---|---:|---:|---:|
| SO-DATA3 Core / Static | small decides | 3.7 / 4.0 s user | 1.52 / 1.58 GB | (base) |
| SO-DATA3 Embedding | `checkEmbedding base = true` | 27.7 s user | 3.17 GB | 0.060 |
| SO-DATA3 HamBounds | `checkHamBounds base = true` | 70.7 s user | 9.75 GB | 0.117 |
| SO-DATA3 HamClaim | `checkHamClaim …` | 69.1 s user | 10.24 GB | 0.127 |
| SO-DATA3 bite δ₁ | `siteOk … = true` | 123 s wall | 8.36 GB | 0.056 |
| BALLDY K0 / J0 | spine / all ops forced | 54 / 59 s wall | 3.9 / 6.9 GB | 0.044 / 0.092 |
| SO-PACKFIX shard | `checkShardSp … = true` (forced) | +45 s over its data baseline | +3.5 GB | 0.078 |
| SO-KDEPTH synthetic | `weightedNormUp` / `directItems` 200² (20 k terms, 320 bit) | 36 / 73 s | 3.3 / 7.0 GB | 0.083 / 0.092 |
| SO-DATA3 GramRow0 | `(gramDefectRows …).getD 0 … .m = lit` | killed at 131.9 s user | 9.34 GB at kill | ≥ 0.059 |
| SO-DATA3 P0 (two 503-term literals in the file) | lengths | 7.3 s wall | 3.50 GB | (base with in-file literals) |
| SO-DATA3 P1 | `mulN … [0,10]` forced (sum, length, radius, degree) | +62 s over P0 | +6.39 GB | 0.103 |
| SO-DATA3 SH / RR | one shard `= true` / all 7 shards (`packedRealProduct … .isSome`, whose `if` forces every shard check) | +3.5 / +29 s | +0.68 / +3.28 GB | 0.19 / 0.11 |

**The fitted law:**
- For runs of at least 20 s, the rate is 0.04–0.13 GB per kernel-second. Very short runs (SH, 3.5 s) show a higher
  apparent rate from fixed per-declaration costs.
- The base with the certificate imports is 1.5 GB. With 503-term literals elaborated *in the file* it is 3.5 GB
  (P0).
- Production modules import their literals from built `.olean`s, so their base is expected near 1.5–2 GB. G1
  (§4.5) measures it.
- **Peak ≈ base + 0.13 GB/s × t (conservative).**

**Consequences:**
- A theorem with at most 40 s of kernel work is predicted at ≤ 6.7 GB at base 1.5 GB, and ≤ 8.7 GB even at the
  in-file 3.5 GB base.
- The plan therefore budgets t ≤ 40 s. It expects every single unit (a shard group, measured within RR; a decode,
  projected) at about 3.3 GB of work or less, to be confirmed by G4.

### 4.2 Work proxy: backend calls (census)

`csplit_census.py` runs SO-DATA3's mirror (N = 65, L = 20, CertFixed 96, cutoffs 100000/160) on both tori. It
counts every `FixedB` primitive call per slot, per Gram entry, per torsion stage, per invariance row and per frame
corner. Packed products are counted separately, because the mirror evaluates them with numpy.

**Calibration:**
- `checkEmbedding`: 40.7 k calls ↔ 24 s of kernel above the import (27.7 s − 3.7 s) and 1.65 GB. That is
  **0.59 ms and 41 KB per call**.
- SO-KDEPTH `weightedNormUp`: about 6 calls per term × 20 k terms = 120 k ↔ 36 s and 3.0 GB, i.e.
  **0.30 ms and 25 KB per call** (at 320 bits; 96 bits is cheaper).
- **Per call, 0.3–0.6 ms and 25–42 KB.**

**Cross-checks against the OOM kills** (consistent, not proofs):
- GramRow0's work: 292 k calls plus 13 packed products. The prediction is 87–175 s and 7.3–12 GB of work above the
  base; it was killed at 132 s and 9.3 GB.
- Pruned energy: 859 k calls plus J0 (6.9 GB). That is far over the cap; it was killed within 1.5 min.

**Packed products (SO-DATA3 P1/SH/RR; the split is a projection, N2).**
- *Measured:* the whole product P1 at +6.39 GB and +62 s; all 7 shards RR at +3.28 GB and +29 s; one shard SH at
  +0.68 GB.
- *Projected by subtraction (P1 − RR), not measured:*
  - ≈ 0.47 GB and 4.1 s per shard;
  - a remainder of ≈ 3.1 GB and 26 s for the decode, `toErrTerms`, truncation and `errRadius` of the 847-term
    output. That is ≈ 0.36 MB and 3 ms per target slot.
- Peaks under different cache states need not subtract. The isolated decode theorem (b) is therefore **unmeasured
  until gate G4**, and no bound "≤ 3.1 GB" is claimed before then.
- **Units:** GB are decimal (`/usr/bin/time` max RSS in kB × 10³). The cgroup cap `MemoryMax=10G` is 10 GiB, i.e.
  10.74 GB. The gate records cgroup `memory.peak` as well.

My earlier scaling from SO-PACKFIX (0.3–1.1 GB per whole product) under-estimated by 6×. By the
projection, the decode remainder, which SO-PACKFIX's shard probe did not include, is about half the cost.

**Planning value.** Each packed product is memoized in its own theorems (§3.5). Inside segments and entries it
costs 0, and the shard and decode theorems are planned by GB directly.

**Budget B = 75 k calls per theorem:**
- 23–45 s of kernel;
- 1.9–3.1 GB of work, plus 1.5 GB of base and at most 0.5 GB of imports and seed;
- **predicted peak 3.4–5.1 GB.**

### 4.3 The plans (census + `csplit_plan.py`; both tori; B = 75 k)

**These are the plans the planner emits** (N1): the plan JSON carries every `SegSpec` row
(`kam-data/so-csplit/plan_{lower,upper}_75000.json`, field `segSpecs`).
- The segment counts include the forced one-op cuts: cfgFull `[10,11)` and `[28,29)`; cfgLow `[28,29)` only.
- In cfgLow, slot 10 is dead for `torsionSlots`. Its packed product is skipped by the shadow run, never
  evaluated, so a torus has 128 evaluated packed products, not 129.
- Packed products are memoized (L1c) and cost 0 inside segments and entries.
- The largest segment cost is the one-op character segment: 112 k census calls in cfgFull, 94 k in cfgLow. Its
  two residuals are memoized in their own theorems (`expResidualProduct`/`expResidualUp`, §3.5), so the segment
  keeps only the remainder. G5 measures this.
- Every other segment is ≤ 75 k.

| | lower | upper |
|---|---:|---:|
| cfgFull: live slots / live work | 215 / 2.40 M | 215 / 2.39 M |
| cfgFull: segments (one-op cuts) / max imports per segment | 38 (10, 28) / 8 | 38 (10, 28) / 8 |
| cfgLow (torsion): live slots / live work | 401 / 4.52 M | 401 / 4.51 M |
| cfgLow: segments (one-op cuts) / max imports | 70 (28) / 12 | 70 (28) / 12 |
| ops over B before M3 | slot 28 (char): 112 k (cfgFull) / 94 k (cfgLow) calls plus its 2 packed products; slot 10's product | the same |
| packed products in SO-DATA3's report (128 evaluated) / shards / target slots | 129 / 667 / 351 k | 129 / 718 / 358 k |
| packed theorems, (a) shards + (b) decode per evaluated product | 256 (projected ≈ 3.3 + ≈ 3.1 GB of work each; G4) | 256 |
| Gram: work without products / packed / entry theorems | 361 k / 17 / 9 (entry (0,0) at 75.8 k splits) | 351 k / 17 / 7 |
| torsion stages: work without products / packed / entry theorems | 3.03 M / 106 / 54–75 (an entry over B splits per product) | 2.99 M / 106 / 54–75 |
| invariance rows / energy tail / frame corners (L, N, Nt, T) | 43, 0.1, 57, 59 k / 3 k / 69, 54, 54, 33 k | ≈ the same |

The live sets reproduce SO-DATA3's independent counts exactly (v0 86 slots / 26 products; d1 rows 99/36, 85/31,
16/7, 3/1; shared 215/100), which cross-validates the census.

**Sensitivity.** At B = 150 k (if the gate shows the faster end of the rate), cfgFull needs 20 segments and cfgLow
33, with the same forced cuts. The plan generator takes B as its parameter.

### 4.4 Level structure

| level | unit | used for |
|---|---|---|
| L0 | the jet bridge (M0) | once per Hamiltonian |
| L1a | a segment of consecutive ops (M1) | cfgFull and cfgLow compositions |
| L1b | a one-op segment proved by rewriting (M3) | slot 10 (`[0,10]`) and slot 28 (character witness); any op over B |
| L1c | one packed product → shard group + decode (M3) | every evaluated packed product (128 per torus; 129 in SO-DATA3's report, which includes cfgLow's dead slot 10) |
| L2 | one stage entry (M2) | Gram entries, BG entries, torsion matrix entries, invariance rows, corners |

### 4.5 Phase-2 gates SO-CSEG-CAL-1 and CAL-2 (before any generation at scale; N3)

**CAL-1** (G0–G5) runs after packages A and L3. Its probes are standalone: G2 and G3 use A's `segOk` on one
emitted segment; G4 and G5 use L3's lemmas and hand-written stage statements. **CAL-2** (G6, G7) runs after L2
and B's bridges and templates, because those probes exercise the table lemmas and an assembled recipe.

Every probe runs alone under the kernel-probe lock with `MemoryMax=10G`, `MemorySwapMax=0` and
`LEAN_NUM_THREADS=1`, and records USER+SYS CPU, wall and `memory.peak`. Each forces **equality to a complete
literal** with the **production import closure** (audit F1):

| probe | statement | decides |
|---|---|---|
| G0 | `lower_jet` (M0) | M0 fits (< 9 GB); else split by program segments (SO-LOCK-COST G1c) |
| G1 | import-only control of a segment module | the base with the plan and ledger imports |
| G2 | one cfgFull segment at ≈ 75 k calls (8 imports, real exports) | κ (ms and KB per call), seed and export overhead |
| G3 | one cfgFull segment at ≈ 150 k calls | linearity of the rate; whether B = 150 k is safe |
| G4 | (a) all 7 shards of `[0,10]` `= true` and (b) its decode `dyadicTerms … = some lit`, as production modules | **measures** the projected split of SO-DATA3's P1/RR (6.4 GB ≈ 3.3 + 3.1), with module imports and forced literals |
| G5 | slot-28 pieces: `expResidualProduct … 0 = lit` (forced; C1 was an `isSome`), the remainder, the one-op segment | L1b |
| G6 | one Gram entry and one torsion `[4,8]` entry | L2 entry vs per-product split |
| G7 | a residual recipe (`checkEnergy` from the chain) | R7: no accidental evaluation |

**Rule:**
- B is set to the largest value whose predicted peak is ≤ 7 GB, using the fitted κ and the G1 base.
- If any probe exceeds 9 GB after its split, the procedure stops and reports. That is a design signal; no limit is
  ever raised (no heartbeat or depth override, AGENTS.md rules 1 and 4).
- SO-DATA3's forced P1/SH/RR receipts are the packed-product calibration. G4 re-checks them in the production
  module form.

## 5. Ledger

**Contents per chain** (both stored as `(model, cached norm)` pairs, so the importing segment never recomputes a
norm):
- the live slots read across a boundary;
- the wanted slots.

**Metas per boundary:**
- `len`, `nExp`, `nInv` (both 0 for the lunar program);
- `cache`, with at most 2 entries per chain: the witness `E` by its existing data name and its `reflectSorted`
  image as a literal, plus the certified radii.

**Stage literals:**
- Gram entries;
- BG entries and the final rows `(δ, β)`;
- `dkModels`, `dkwModels` and `gramInvModels`;
- the products and entries of `[4,0]`–`[4,9]`;
- the adds, `T`, `ms` (the cfgLow `torsionSlots` models, already in the ledger), and `ε`.

**Volume: formatted-definition plus overhead estimates** (audits 1 and 2, N1; B = 75 k). The census formats every
ledger and stage literal as SO-CSEG-GEN will emit it
(`csplit_census.py` `def_text`):
- the definition header;
- degree and radius;
- one `tm` row per term;
- the cached norm `def <name>.norm`.

The planner adds:
- the plan text (`SegSpec` rows) and the metas;
- the stage literals: Gram entries, BG entries, every torsion stage matrix and add;
- the decoded product memos, one per packed product (its output terms);
- one 700-byte module header per ≤ 1,400-line module.

| per torus (bytes) | lower | upper |
|---|---:|---:|
| cfgFull ledger (155 models, with norms) | 2,508,714 | 2,505,875 |
| cfgLow ledger (324 / 322 models) | 5,615,385 | 5,566,978 |
| plans and metas (UTF-8; metas at real lengths; 400 B allowance) | 14,329 | 14,313 |
| reflected character witness (cache literal) | ≈ 20,000 | ≈ 20,000 |
| compose product memos (evaluated only: 3 cfgFull + 2 cfgLow) | 90,583 | 89,748 |
| Gram stage literals / Gram product memos | 55,033 / 121,398 | 54,320 / 122,160 |
| torsion stage literals / torsion product memos | 877,953 / 923,141 | 884,497 / 933,483 |
| module headers | 145,600 | 144,900 |
| **total (estimate)** | **10,372,136 (10.4 MB)** | **10,336,274 (10.3 MB)** |

Both tori: **≈ 20.7 MB**.
- Deduplicating the 384 distinct models across the two chains would save about 1 MB per torus. These figures do
  not dedupe.
- At B = 150 k the totals are 8.51 / 8.45 MB.
- **Formatted bytes:** the ledger and stage definitions (degree, radius, rows, cached norm, definition header) and
  the product memos' term rows.
- **Estimates:**
  - the plan's 400 B allowance and the metas' cache printed as a name;
  - the product-memo definition headers (200 B each);
  - the reflected witness (≈ 20 kB);
  - the module headers (700 B per predicted module of ≤ 1,400 lines, from bytes ÷ 50 kB, not from split files).
- **The receipt (gate before the volume decision):** `du -b` of the generator's emitted tree, plus a line-count
  check of every emitted module (≤ 1,500 lines, hard rule 2).

**Flag:** not triggered by the estimate (≈ 10.4 MB per torus, well under 50 MB). It lands in the public
repository.

Alternatives, which matter for the lock (§7):
- **(i) Content-addressed shards:** one module per distinct model hash, shared across chains, tori and segments.
  This saves 20 % here, more where tori share slots.
- **(ii) Packed mantissas:** a model's coefficients as one `natChunks` integer, decoded in the kernel by
  SO-PACKFIX's balanced `natSlotsSh`. That is about 2× smaller text, at a measured decode cost per use.
- **(iii) Fewer boundaries:** a larger B after the gate, or L1b-memoized single ops, which shrinks the ledger
  roughly ∝ 1/B.
- **(iv) Compressed JSON in the repository plus a Lake build step that regenerates the `.lean`.** This is ruled
  out unless the owner wants it; it complicates public verification.

## 6. Cost

**Theorems per torus** (B = 75 k; the ranges come from entries split per product):

| part | theorems |
|---|---:|
| cfgFull segments (incl. one-op `[10,11)`, `[28,29)`, + slot-28 remainder) | 40 |
| cfgLow segments (the same) | 72 |
| packed products: (a) shard group + (b) decode, 128 evaluated products | 256 |
| invariance rows + energy tail | 5 |
| Gram and BG entries + final rows | 8 |
| torsion: `dkModels`, `dkwModels`, `gramInvModels`, 54–75 entries, adds, `T` average | 62–83 |
| frames: L, N, Nt, T corners | 4 |
| assembly (`compose_eq` instances, recipes; no heavy kernel work) | ≈ 10 |
| **total** | **≈ 460–480** (plus the existing Static, HamBounds, HamClaim, Embedding, Core, bites, Graph) |

Shared: one jet bridge for both tori.

**Per-theorem memory bound and evidence.** The bound is predicted, not guaranteed: peak ≤ base + 0.13·t, with
t ≤ 40 s ⇒ ≤ 6.7 GB at base 1.5 GB (≤ 8.7 GB at the in-file 3.5 GB base). A shard group of ≤ 7 shards is
measured as part of RR (+3.3 GB). The decode is projected at about 3.1 GB until G4. Each theorem's own capped build
is its receipt, and the runner records the cgroup `memory.peak`. A
theorem above 8 GB is re-planned at B/2. After L1c that is a reported design signal.

**CPU-h per torus:**

| item | estimate |
|---|---|
| kernel work: 10.7 M calls (cfgFull 2.4, cfgLow 4.5, Gram 0.36, torsion 3.0, tails and frames 0.4) × 0.3–0.6 ms | 0.9–1.8 h |
| packed: 667–718 shards × 4.1 s + 351–358 k target slots × 3 ms | 1.05–1.1 h |
| fixed per theorem (process, imports, elaboration ≈ 8–10 s) × 460–480 | 1.0–1.3 h |
| ledger data modules (≈ 10 MB literals) | < 0.1 h |
| **total** | **≈ 3.0–4.3 CPU-h per torus; 6–8.6 for both, plus about 2 min for the jet bridge** |

Wall time equals CPU time, since the builds are serial.

**Build ordering** (each heavy module alone; light modules through the compile gate):
1. Data: `jetLit`, the ledger modules, the plans and the stage literals. These are definitions only, cheap, and can
   go through the gate in parallel.
2. `Jet` (G0): one heavy module, serial.
3. cfgFull segments, then cfgLow segments, in plan order; Gram entries; torsion stages in dependency order; frames
   and tails. All are heavy and serial, under `csplit_kbuild.sh`. It extends `sodata3_kbuild.sh` and is a
   restartable driver: it skips any module whose `.olean` is up to date.
4. Assembly modules (`*Chain`, `*Checks`, `Passes`): light.

**At landing.** `KAM.lean` imports every module (D43 parts). A plain `lake build` at landing would schedule the
heavy modules in parallel and exceed the cap. Owner/orchestrator item O3:
- `land-branch.sh` runs `csplit_kbuild.sh` over the heavy-module list, serially, on the landing tree **before**
  any parallel build;
- the parallel build then finds them up to date;
- the list is emitted by the generator (`heavy_modules.txt`) and checked by lint.

## 7. Reuse for the lock (3,158-op polar Hamiltonian)

| mechanism | lock |
|---|---|
| M0 | the same `HamJet.beq`. The lock's J0 projects above 10 GB (SO-LOCK-COST §2), so the bridge itself is split by program segments: `opsBeq` on `[0,800)`, …, plus `v0`/`d1`/`d2`/`d3` and a structural `List.take_append_drop` assembly (SO-LOCK-COST G1c). **Dependency:** at the lock's 3,116 ops, the lock gate found kernel deep recursion in the jet compiler (`slpCompile`/Diff), which M0 reduces. SO-KDEPTH2 (worktree `KAM-inp-sokdepth2`) is fixing it body-only, with the compiled programs identical. The lock's M0 waits for it. The 887-op lunar program is unaffected. |
| M1 | unchanged. The 4 `sqrt`, 8 `inv` and 4 `exp` ops are fallible, so they always run; the metas carry `nExp`/`nInv`; `sqrtWit` is keyed by slot number, which survives segmentation. |
| M2 | unchanged; the same checker functions (Gram, torsion, frames) |
| M3 | needed more often: the factors are ≈ 6.5× larger (LOCK-GEN-2 P2.6; ≈ 7.1 k half-terms). L1c shards, plus **L1d** for single linear ops over B, staged by the subterms of `CertModel.mul`/`add`: `polyProduct` output, `truncPoly`, `errRadius`, `supNormUp`, and `sumUp` round by round. These are all closed subterms of the landed bodies, so this is still memoization, not new code. |

**Projection** (unmeasured; wide error):
- work ≈ 10.7 M × 6.5 (terms) × 2.5 (pruned ops) ≈ 170 M calls, i.e. about 2,300 theorems at B = 75 k;
- about 300 packed products, with shards and decode scaling with the factors;
- **25–60 CPU-h**;
- **ledger ≈ 100–200 MB** for one torus.

**Flag for the owner (O2).** The lock's ledger likely exceeds 50 MB. Options (i)–(iii) of §5 are the mitigations;
the lock's G3 probe (SO-LOCK-COST) should run with M1/M3 in hand.

## 8. Packages and sizes

| package | modules (new; ≤ 400 lines each) | lines | depends on |
|---|---|---:|---|
| **SO-CSEG-A** | `CertificateSharp/Kernel/SegDefs.lean`: `ComposeMeta`, `SegSpec`, `ComposeCkpt`, `seed`, `shadowStep`, `segOk`, `planOk`, `polyBeq`/`modelBeq`/`pairBeq`/`cacheBeq` with soundness, `SlpOp.beq`/`opsBeq`/`HamJet.beq` with `eq_of_beq` (≈ 330). `Kernel/SegAgree.lean`: `AgreeOn`, `composeStep_congr` (8 arms), `composeStep_infallible`, `shadowRun_agree` (with `hR`), `ComposeCkpt.imports_lt_seed_len`, the negative test `shadowRun_agree_needs_hR`, persistence (≈ 330). | 660 | landed `Expr/Compose`, `Kernel/Prune` (`opDeps`) |
| **SO-CSEG-B** | `Kernel/SegChain.lean`: `planOk` facts, induction, `ComposeCkpt.compose_eq` (≈ 280). `Kernel/SegBridges.lean`: `checkInvariance_eq_of_compose`, `checkEnergy_eq_of_compose`, `all_range_of_lt`, the templates `checkEnergy_of_ckpt`, `checkInvariance_of_ckpt` (≈ 120). `Tests/Seg.lean`: toys equal to the monolithic run; negatives: corrupted export, wrong norm, wrong radius, missing import, dead read, skipped fallible op, wrong counter, wrong cache order, malformed meta (≈ 220). | 620 | A |
| **SO-CSEG-L2** | `Kernel/Stage.lean`: the §3.4 table lemmas, `gramCheck_eq_of_rows`, `torsionModels_eq_of_stages`, `frameNModels_eq_of_stage` (≈ 300). `Tests/Stage.lean`: toy recipes, R7 timing (≈ 120). | 420 | landed Gram, Torsion, Frame |
| **SO-CSEG-L3** | `Kernel/ProductSplit.lean`: `mulN_eq_of_polyProduct`, `polyProduct_eq_of_mulPacked`, `mulPacked_eq_of_parts`, the three `packedRealProduct` lemmas, `checkPackedSpPrefix`/`checkShardAt`/`checkPackedSp_of_groups`, `charResolve_eq_of_radius`, the three `expWitnessRadius*`/`expResidualProduct` lemmas (≈ 280). `Kernel/SegOne.lean`: `segOk_one_of`, `seed_slot_of_mem`, the `composeStep` arm equations (≈ 100). Tests (≈ 110). | 490 | landed `Model/*`, `Poly/*`; A |
| **SO-CSEG-GEN** | Python. `csplit_census.py` (done), `csplit_plan.py` (done; to become the optimizer: union-aware ledger, forced cuts at L1b ops, B from the gate). `csplit_ledger.py`: pairs, metas and stage literals from the mirror, bit-exact, self-checked by re-running segments in the mirror. `csplit_emit.py`: Lean modules, extending `sofx_lean.py`'s formatters. `csplit_kbuild.sh`. `heavy_modules.txt`. | ≈ 900 | sofx mirror (SO-DATA3) |
| **SO-CSEG-CAL-1 / CAL-2** | the §4.5 gates (probes in `kam-data/so-csplit/gate`, not landed) | – | CAL-1: A (G2/G3), L3 (G4/G5); CAL-2: L2 and B (G6/G7) |
| **SO-CSEG-DATA** | per torus: the emitted modules and the serial capped run | generated | all |

**Order:** A → (B ∥ L3) → CAL-1 → L2 → CAL-2 → GEN finalization → DATA.
- **Lean core:** ≈ 2,190 lines including tests (≈ 1,650 without).
- **Audits:** one design-level audit of this document (codex-1, next), then one per package. The packages are
  computation-only lemmas, and A plus B carry the chain argument.

## 9. Risks

- **R1. Bit-exact ledger.** Route E needs Lean and the mirror to agree exactly.
  - Evidence: SO-DATA3's byte-identical `Slp.balls` on all 887 slots, the mirror `directItems` aligned to SO-KDEPTH's
    tree, and regenerations byte-identical.
  - Detection: a divergence fails closed in one segment, which localizes it. `csplit_ledger.py` also compares the
    mirror's segment re-run.
  - Fallback: route S (§3.1).
- **R2. Packed products.** The whole product is measured at 6.4 GB, so products are always split. The split
  (shard groups ≈ 3.3 GB, decode ≈ 3.1 GB) is a **projection** by subtraction until G4 measures the isolated
  decode. If the decode is over budget, it needs a further split by target ranges: `targetTerms` is a `filterMap` over
  `(List.range prodLen).zip combined`, and `dyadicTerms` is a guarded `map`. That needs an `append` lemma for each,
  plus `List.range` splitting. These are new, small lemmas, designed only if G4 shows the need; that would be a
  design signal, reported. The cfgLow
  products are smaller by the report (≤ 7 shards, ≤ 4.3 k target slots against 8.5 k), but this is not
  established until measured.
- **R3. Jet bridge near the cap** (expected 7–7.5 GB). If G0 exceeds 9 GB, split it by program segments (lock G1c),
  as designed for the lock.
- **R4. The rate law.** It is a fit, not a theorem. Every heavy module is its own receipt; the runner aborts at the
  cap, and the plan is regenerated at B/2.
- **R5. Elaboration of the `rw` recipes.** `rw` on closed terms is cheap, but `interval_cases` and table-lemma
  instantiation over 54 entries must stay light. Generated proofs instantiate the lemma with explicit functions
  (lookup in literal tables), never by search.
- **R6. Import closure.** Segment modules import the plan, hence every ledger module of the chain (about 8 MB of
  definitions). The kernel unfolds only what it reads; G1 measures the base.
- **R7. Accidental evaluation in assembly.** Generic lemmas are applied, and the residual decides see literals only;
  G7 checks this.
- **R8. Graph pass (`checkSoGraph`).** It was not run by SO-DATA3. If it is over the cap, the same M2 applies
  (stage its SOS products).

## 10. Owner-review items

- **O1.** Option A (prove the landed Bools) over a new `BaseChecker`: recommended. No trusted change.
- **O2.** Lock ledger volume projected at 100–200 MB (§7): above the 50 MB flag. Choose among content-addressed
  shards, packed mantissas and fewer boundaries (§5) when the lock's data exist. The lunar tori are at about
  10.4 / 10.3 MB each, under the flag.
- **O3.** Landing procedure for heavy modules: a serial capped prebuild in `land-branch.sh` (§6), plus a lint on
  `heavy_modules.txt`.
- **O4.** Optional: re-prove `checkHamBounds` and `checkHamClaim` through the jet bridge (HamClaim is at 10.24 GB
  RSS, 2 % under the cap).

## 11. Evidence files

- `scripts/spin_orbit/csplit_census.py`, `csplit_plan.py` (this branch).
- `kam-data/so-csplit/census_{lower,upper}.json`: per-slot op, reads, operand and output terms, backend calls,
  packed products, literal bytes, model hash; Gram entries; torsion stages; invariance rows; energy tail; frame
  corners.
- `kam-data/so-csplit/plan_{lower,upper}_{75000,150000}.json`: the emitted plans (`segSpecs`), counts and
  complete volume (`volume`).
- SO-DATA3's product probes: `kam-data/so-data3/product-probes.md`, `probes/csplit/{P0,P1,SH,RR,C1,EN14}`.
- Runs: `python3 -B csplit_census.py lower|upper OUT` (85 s each, 0.23 GB RSS), then
  `python3 -B -I csplit_plan.py CENSUS B SHARD`.
