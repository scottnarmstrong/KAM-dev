# SO-CSPLIT: segmented proof of the heavy sub-checks under the 10 GB kernel cap (design, Phase 1)

Status: design only, 2026-10-30 (owner ruling D39; track SO). No Lean file was written and no kernel probe was run.
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
    - its target decode (≈ 3.1 GB at 8,536 target slots).

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
    - the decode and assembly of the 847-term output cost 26 s and 3.1 GB.
  - Per torus that is 129 packed products, 667–718 shards and 351–358 k target slots.
  - L = 14 does not rescue a whole compose: its `checkEnergy` was OOM-killed. That is consistent with M0, because
    the jet alone costs 6.9 GB at any L.
- **Ledger (§5): 10–11 MB of Lean literals per torus, about 21 MB for both, far below the 50 MB flag.**
  - cfgFull 155 models (2.5 MB); cfgLow 324 models (5.6 MB); 384 distinct after dedupe.
  - Level-2 stage literals and the decoded packed-product outputs add about 2.4 MB.
  - Volumes are exact emitted bytes from the mirror at SO-DATA3's `tm` format.
- **Cost (§6), per torus:**
  - about 430–480 theorems, each in its own module and built serially under the cap (about 260 of them are
    packed-product shard and decode theorems);
  - 10.7 M backend calls plus 129 packed products of kernel work;
  - **≈ 3.0–4.3 CPU-h per torus, 6–8.6 CPU-h for both.**
- **Lock (§7).** M0–M3 carry over unchanged in shape. The lock's models are about 6.5× larger and its program is
  3.56× longer, so the projection is 25–60 CPU-h and a ledger of roughly 100–200 MB. The volume flag applies to the
  lock, not to the lunar tori (§10, owner item O2).
- **Packages (§8).** About 1,650 Lean lines in four packages (SO-CSEG-A, -B, -L2, -L3), plus a Python emitter
  (SO-CSEG-GEN, ~900 lines, extending `sofx_*`) and a Phase-2 calibration gate (SO-CSEG-CAL).

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
| F3: terminal outputs missing; union vs sum; per-chain counts | The planner exports the wanted slots and counts the ledger as a union, separately per chain and torus. Volumes are exact emitted bytes. |
| F4: additive memory law; Level 2 "needed regardless" | The law is now a fitted *rate*, with its mechanism (§4.1) and an explicit gate. Level 2 is needed because a single Gram defect row was OOM-killed (SO-DATA3 interim 3), which is a measured fact. |
| F5: sharing needs a projection | M1 yields one `composeOps` success plus a ledger; `ComposeCkpt.compose_eq` projects to any `wanted ⊆ ledger`, so invariance (`d1Slots`) and energy (`[v0]`) share the run. |
| F6: simpler alternatives | §3.1 and §3.6. Measured sharing and pruning (sharp-v2's `checkInvEnShared`, `composePruned`) were OOM-killed (SO-DATA3 round 2). Pruning is kept *inside* M1 as dead-op skipping. |

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
     36 s and 6.78 GB (+3.3 GB). The rest, about 3.1 GB, is the decode of the 8,536-slot target (`dyadicTerms`),
     `toErrTerms`, `truncPoly` and `errRadius`.
   - So a whole product is too close to the cap to share a theorem with anything, while one shard group or one
     decode fits easily.
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
/-- Bool equality of op lists, tail-recursive (`&&` in tail position; derived `DecidableEq` on `List` nests one
kernel `whnf` per element, risking the depth limit at 887 ops). -/
def SlpOp.beq : SlpOp → SlpOp → Bool
def opsBeq : List SlpOp → List SlpOp → Bool
def HamJet.beq (J J' : HamJet) : Bool       -- prog, v0, d1, d2, d3
theorem HamJet.eq_of_beq {J J' : HamJet} (h : J.beq J' = true) : J = J'
```

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

**Data (untrusted, emitted).**
```lean
structure ComposeMeta (α : Type) where      -- the non-slot fields of `ComposeState`
  len : ℕ
  nExp : ℕ
  nInv : ℕ
  cache : List (CertKey × CertPoly α × α)

structure SegSpec where                       -- ops [start, stop)
  start : ℕ
  stop : ℕ
  live : List ℕ          -- the slots of [start, stop) that must be computed faithfully
  imports : List ℕ       -- ledger slots < start read by live ops
  exports : List ℕ       -- ledger slots in [start, stop)

structure ComposeCkpt (α : Type) where
  segs : List SegSpec
  metas : List (ComposeMeta α)               -- `metas.length = segs.length + 1`
  ledger : List (ℕ × (CertModel α × α))      -- (slot, (model, cached norm)), slots strictly increasing
```

**The shadow fold.** `fallible op := op is char/exp/inv/sqrt`; `liveEff s i op := i ∈ s.live ∨ fallible op`.
```lean
def shadowStep (env) (s : SegSpec) (st : ComposeState α) (op : SlpOp) : Option (ComposeState α) :=
  if liveEff s st.len op then composeStep n K wit W cfg pe st op    -- the landed step, unchanged
  else some (st.pushSlot W zeroModel)                                -- dead infallible op: a placeholder
def ComposeState.seed (W) (m : ComposeMeta α) (C : ComposeCkpt α) (imports : List ℕ) : ComposeState α
  -- `rev` dense of length `m.len`: the ledger pair at imported slots, `slotEntry W zeroModel` elsewhere
```

**`segOk env ops C j : Bool`** checks, for `s = C.segs[j]`, with checked indexing (`getD` only after length checks):
- **(S1) Metas.** `C.metas[j].len = s.start` and `C.metas[j+1]` exists.
- **(S2) Reads.** For each `i ∈ [start, stop)` with `liveEff s i ops[i]`, every `a ∈ opDeps ops[i]` satisfies
  `a < i` and either `a ∈ s.imports` or (`start ≤ a` and `liveEff s a ops[a]`). This is index arithmetic only.
- **(S3) Run.** The shadow fold of `(ops.drop start).take (stop - start)` from `seed (metas[j]) C s.imports` is
  `some st`, and `meta st = C.metas[j+1]`. Comparing `cache` uses `cacheBeq`.
- **(S4) Exports.** For each `e ∈ s.exports`: `start ≤ e < stop`, `liveEff s e ops[e]`, and
  `pairBeq (st.slot W e) (C.pair e) = true`. This compares the **whole pair**, model and cached norm (audit F2).

**`planOk C ops.length wanted : Bool`** works on indices only, with no model compared:
- the segments tile `[0, ops.length)` in order;
- `metas.length = segs.length + 1` and `metas[0] = ⟨0, 0, 0, []⟩`;
- the ledger slots are strictly increasing, hence distinct;
- every import of segment `j` is `< segs[j].start` and is an export of the segment containing it;
- every ledger slot is an export of the segment containing it;
- `wanted ⊆ ledger slots`.

**Bool equalities.** `polyBeq`, `modelBeq`, `pairBeq` and `cacheBeq` are tail-recursive conjunctions over the term
lists. `[DecidableEq α]` is used for the leaves (`CertFixed P` through `m : ℤ`). Soundness lemmas give `… = true → … = …`.
The checks traverse lists by `&&` chains, which SO-KDEPTH measured as depth-safe at 20 k elements. Derived
`DecidableEq` on `List` is never used.

**Chain theorem (proved once, generic in all data).**
```lean
theorem ComposeCkpt.compose_eq [DecidableEq α] (C : ComposeCkpt α) {p : Slp} {wanted : List ℕ}
    (hplan : C.planOk p.ops.length wanted = true)
    (hseg : ∀ j < C.segs.length, C.segOk n p.ops K wit W cfg pe j = true) :
    Slp.compose n p K wit W cfg pe wanted = some (wanted.map fun i => (C.pair i).1)
```

**Proof (computation-only).**

Let `M_j` be the landed run on the prefix `p.ops.take segs[j].start`. The induction invariant **I(j)** is:
`M_j = some X` with `meta X = metas[j]` and `X.slot W e = C.pair e` for every ledger `e < segs[j].start`.

- **Base.** `composeOps` of `[]` is the empty state, so I(0) holds.
- **Step `j → j+1`.** Let `σ` be the seed, and maintain `AgreeOn R σ' X'`: equal `len`/`nExp`/`nInv`/`cache`, and
  equal pairs on the index set `R`. Start with `R = s.imports`, which holds by I(j) and the seed. For the op at
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
- **cfgFull.** `wanted = v0 :: d1`. `compose_eq` applied with `[v0]` and with `d1Slots` uses the same `hplan` and
  `hseg` facts (audit F5).
- **cfgLow.** `wanted = torsionSlots`.

**The lunar plans (§4.3).** 38 cfgFull and 70 cfgLow segments per torus.

### 3.4 M2: stage memoization (Gram, torsion, frames, the tails)

**The pattern.** For a closed heavy subterm `t`, a stage theorem proves `t = lit` (`decide +kernel` on a literal
`lit`); the consumer proof `rw`s it and decides the rest. This is SO-DATA3's FrameN pattern
(`rw [lower_gramCheck_eq]; decide +kernel`), generalized.

**Table lemmas.** The landed bodies build matrices under binders, so a closed equality cannot be `rw`ritten there.
Generic congruence lemmas (`funext` / `List.ofFn` / `buildMat` extensionality) move the per-entry equalities
inside. All are stated over variables:
```lean
theorem gramModels_eq_of_entries {E : ℕ → ℕ → CertModel α}
    (h : ∀ a < n, ∀ b < n, a ≤ b → gramEntryModel n K W cfg pe a b = E a b) :
    gramModels n K W cfg pe = (List.range n).map fun a => (List.range n).map fun b =>
      if a ≤ b then E a b else E b a
theorem gramDefectRows_eq_of_entries {T : ℕ → ℕ → CertModel α}
    (h : ∀ i < n, ∀ j < n, gramBGModel n B G W cfg pe i j = T i j) :
    gramDefectRows n B G W cfg pe =
      List.ofFn fun i : Fin n => sumUp (fun j : Fin n => gramDefectUp W i.val j.val (T i.val j.val))
        (List.finRange n)
/-- the `(i, j)` body of `modelMatMul` (definitionally equal; new name) -/
def matMulEntry (W) (cfg) (pe) (key) (m : ℕ) (A B : ModelMatrix α) (i j : ℕ) : CertModel α
theorem modelMatMul_eq_of_entries {M : ModelMatrix α} (hs : M has shape r × c)
    (h : ∀ i < r, ∀ j < c, matMulEntry W cfg pe key m A B i j = modelMatrixEntry M i j) :
    modelMatMul W cfg pe key r m c A B = M
theorem matMulEntry_eq_of_products {P : ℕ → CertModel α}
    (h : ∀ k < m, CertModel.mul W cfg (key ++ [i, j, k]) (modelMatrixEntry A i k)
      (modelMatrixEntry B k j) = P k) :
    matMulEntry W cfg pe key m A B i j = CertModel.toDeg W pe 0 (modelSum W pe (List.ofFn fun k : Fin m => P k))
theorem torsionModels_eq_of_stages … : torsionModels n e K wit B δβ box s W cfg pe = some T
  -- hypotheses: the cfgLow `Slp.compose … (torsionSlots n e.jet) = some ms`, `gramInvRadius δβ = some ε`,
  -- `dkModels … = Llit`, `dkwModels … = DLlit`, and one equation per matrix stage `[4,0]`–`[4,9]`, add,
  -- transpose and omega, each on the previous stage's literal; conclusion: the `buildMat` of the final stage
  -- literals (`unfold torsionModels; rw [...]`, no evaluation)
```

**Recipes** (`L = lower`; `jet` = M0; `Cfull`, `Clow` = M1 plans):

| landed Bool | proof |
|---|---|
| `checkInvariance base` | `rw [lower_jet]`, then `checkInvariance_eq_of_compose (Cfull.compose_eq …)`. The residual is `(List.range 4).all (row a)`, assembled by `List.all_range_of` from **4 row theorems** (43 k, 0.1 k, 57 k, 59 k calls) on the literal `d1` models. |
| `checkEnergy base` | the same chain with `[v0]`, then **1** `energyOk …` theorem (3 k calls) |
| `checkGram base` | `gramCheck_eq_some` (below), then `Option.isSome_some` |
| `gramCheck … = some δβ` | **3 entry** theorems (`gramEntryModel`, 67–76 k calls; their 3 packed products each memoized by L1c) and **4 BG-entry** theorems (31–40 k; 2 memoized products each). Then `gramModels_eq_of_entries` and `gramDefectRows_eq_of_entries`; the final `gramBoundsOk` and the `maxCandidate` on literal rows are one cheap decide. |
| `checkTorsion base` | `rw [gramCheck_eq_some, torsionModels_eq_some]`, then `torsionAvgCheck` on literal `T` (one decide) |
| `torsionModels … = some T` | `torsionModels_eq_of_stages`, built from: the cfgLow chain; `dkModels`, `dkwModels` and `gramInvModels` (one theorem each); **one theorem per matrix-product entry** (54 entries; their 106 packed products memoized by L1c; an entry over B splits per product: 54–75 theorems, §4.3); and the adds, transposes and omegas (cheap, one each) |
| `checkFrameN base bN bNt` | `unfold checkFrameN frameGram frameNModels`, `rw [gramCheck_eq_some, hε, stage [4,0] equations]`. The `[4,0]` stage literal **is** torsion's `N`, so nothing is recomputed. Then 2 corner theorems (54 k calls each). |
| `checkFrameT base bT` | `rw [gramCheck_eq_some, torsionModels_eq_some]`, then 1 corner theorem (33 k) |
| `checkFrameL base bL` | DK corner bounds (69 k calls): 1 theorem, unchanged (not yet run by SO-DATA3) |

Each `rw` in elaboration matches closed terms. The residual `decide +kernel` sees only literals. Risk R7
(accidental evaluation through defeq) is controlled in two ways:
- stating the table lemmas over variables, so the kernel checks an *application* of a proved lemma;
- a SO-CSEG-L2 test that the residual of a toy recipe reduces in negligible time.

### 3.5 M3: product and op split (Level 1, mandatory)

An op or stage entry that contains a packed product is never decided whole. Its own closed subterms are
memoized instead. There is still no new checker code: these are equation lemmas about the landed
`CertModel.mul`/`mulN`, `polyProduct`, `mulPacked`, `packedRealProduct` and `expWitnessRadius` bodies.
```lean
theorem CertModel.mulN_eq_of_polyProduct (h : CertModel.polyProduct W cfg key a.poly b.poly = some out) :
    CertModel.mulN W cfg key a na b nb = ⟨a.deg + b.deg, truncPoly cfg.cutoff out.1, upAdd (upAdd out.2 …) …⟩
theorem polyProduct_eq_of_parts (ha : a.isConst = false) (hb : b.isConst = false)
    (hk : adviceLookup cfg.advice key = some (.packed P rr ii ri ir))
    (hma : a.toMants cfg.toMant P = some ma) (hmb : b.toMants cfg.toMant P = some mb)
    (hRR : packedRealProduct rr W (2 * P) ma.1 mb.1 = some pRR) (hII : …) (hRI : …) (hIR : …)
    (htRR : dyadicTerms (2 * P) rr.scale (fun v => ⟨v, ofInt 0⟩) pRR.1 = some tRR) (htII : …) (htRI : …) (htIR : …) :
    CertModel.polyProduct W cfg key a b = some (⟨tRR ++ tII ++ tRI ++ tIR⟩, ofRatUp (pRR.2 + pII.2 + pRI.2 + pIR.2))
theorem packedRealProduct_eq_of_shards (hx : adv.la.allSlots x = true) (hy : adv.lb.allSlots y = true)
    (hg : checkPackedSp guards = true)
    (hs : ∀ s ∈ group₁ ++ … ++ group_g, checkShardSp adv SA SB mA mB s = true) :
    packedRealProduct adv W P2 x y = some (adv.targetTerms, adv.remainderBound W P2)
```
**Per packed part, two theorems, plus a cheap one:**
- **(a) the shard group.** The shards `checkShardSp … s`: at ≈ 0.47 GB each, all 7 fit one theorem (≈ 3.3 GB of
  work). Above 7, or under a lower B, they are grouped.
- **(b) the decode.** `dyadicTerms (2P) adv.scale … adv.targetTerms = some t_lit`: ≈ 3.1 GB at 8.5 k target slots,
  ≤ 1.6 GB at cfgLow's ≤ 4.3 k.
- **(c) `toMants` of the two literal operands:** cheap; it may merge into (a).

`packedRealProduct_eq_of_shards` and `polyProduct_eq_of_parts` then assemble `polyProduct … = some lit` with no
kernel evaluation. The real lunar embedding makes 3 of the 4 parts empty for every lunar product. The census
counts the truncation, `errRadius` and norm work of the product's consumer; that work stays in the consumer's
theorem (a segment or a stage entry).

**One-op segments for the two program ops with packed products.** These are slot 10 (`[0,10]`) and slot 28 (the
character witness: `expResidualProduct` with keys `[1,j]`, j = 0, 1, both packed `ir`).
- The plan forces the cuts `[10, 11)` and `[28, 29)`. Their operands are ledger slots (slot 10 reads slots 8 and
  5), and slot 28 reads the meta cache only.
- `segOk` for such a segment is not decided whole. It is proved through
  ```lean
  theorem segOk_one_of (hj : C.segs[j] = ⟨i, i + 1, [i], imps, [i]⟩)
      (hop : composeStep n K wit W cfg pe (seed W (C.metas[j]) C imps) (ops[i]) = some st')
      (hx : metaBeq (meta st') (C.metas[j+1]) && pairBeq (st'.slot W i) (C.pair i) = true) :
      C.segOk n ops K wit W cfg pe j = true
  theorem seed_slot_of_mem (ha : a ∈ imps) (ha' : a < m.len) : (seed W m C imps).slot W a = C.pair a
  ```
- `hop` is proved by rewriting:
  - slot 10: `composeStep` of `.mul`, `seed_slot_of_mem`, then `CertModel.mulN_eq_of_polyProduct` with the
    assembled `polyProduct` literal;
  - slot 28: `composeStep` of `.char`, `charSlot`, `charEntry`, `charResolve` on the meta cache `[]`, then
    `expWitnessRadius_eq_of_residuals`, whose two `expResidualProduct … j = lit_j` premises come from (a) and (b)
    plus one remainder theorem.
- `hx` is a small decide on literals.

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
- The plan therefore budgets t ≤ 40 s and keeps every single unit (a shard group or a decode) at ≤ 3.3 GB of work.

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

**Packed products (measured, SO-DATA3 P1/SH/RR).**
- 0.47 GB and 4.1 s per shard;
- 0.36 MB and 3 ms per decoded target slot (`[0,10]`: 3.1 GB and 26 s).

My earlier scaling from SO-PACKFIX (0.3–1.1 GB per whole product) under-estimated by 6×. The decode, which
SO-PACKFIX's shard probe did not include, is half the cost.

**Planning value.** Each packed product is memoized in its own theorems (§3.5). Inside segments and entries it
costs 0, and the shard and decode theorems are planned by GB directly.

**Budget B = 75 k calls per theorem:**
- 23–45 s of kernel;
- 1.9–3.1 GB of work, plus 1.5 GB of base and at most 0.5 GB of imports and seed;
- **predicted peak 3.4–5.1 GB.**

### 4.3 The plans (census + `csplit_plan.py`; both tori; B = 75 k)

The segment counts include the forced one-op cuts. Packed products are memoized (L1c) and cost 0 inside
segments and entries.

| | lower | upper |
|---|---:|---:|
| cfgFull: live slots / live work | 215 / 2.40 M | 215 / 2.39 M |
| cfgFull: segments / max imports per segment | 38 / 8 | 38 / 8 |
| cfgLow (torsion): live slots / live work | 401 / 4.52 M | 401 / 4.51 M |
| cfgLow: segments / max imports | 70 / 12 | 70 / 12 |
| ops over B before M3 | slot 28 (char): 112 k (cfgFull) / 94 k (cfgLow) calls plus its 2 packed products; slot 10's product | the same |
| packed products / shards / target slots | 129 / 667 / 351 k | 129 / 718 / 358 k |
| packed theorems, (a) shards + (b) decode per product | 258 (≤ 3.3 + ≤ 3.1 GB each) | 258 |
| Gram: work without products / packed / entry theorems | 361 k / 17 / 7 | 351 k / 17 / 7 |
| torsion stages: work without products / packed / entry theorems | 3.03 M / 106 / 54–75 (an entry over B splits per product) | 2.99 M / 106 / 54–75 |
| invariance rows / energy tail / frame corners (L, N, Nt, T) | 43, 0.1, 57, 59 k / 3 k / 69, 54, 54, 33 k | ≈ the same |

The live sets reproduce SO-DATA3's independent counts exactly (v0 86 slots / 26 products; d1 rows 99/36, 85/31,
16/7, 3/1; shared 215/100), which cross-validates the census.

**Sensitivity.** At B = 150 k (if the gate shows the faster end of the rate), cfgFull needs 18 segments and cfgLow
33, and nothing is over budget (slot 28 fits). The plan generator takes B as its parameter.

### 4.4 Level structure

| level | unit | used for |
|---|---|---|
| L0 | the jet bridge (M0) | once per Hamiltonian |
| L1a | a segment of consecutive ops (M1) | cfgFull and cfgLow compositions |
| L1b | a one-op segment proved by rewriting (M3) | slot 10 (`[0,10]`) and slot 28 (character witness); any op over B |
| L1c | one packed product → shard group + decode (M3) | every packed product (129 per torus) |
| L2 | one stage entry (M2) | Gram entries, BG entries, torsion matrix entries, invariance rows, corners |

### 4.5 Phase-2 gate SO-CSEG-CAL (before any generation at scale)

Every probe runs alone under the kernel-probe lock with `MemoryMax=10G`, `MemorySwapMax=0` and
`LEAN_NUM_THREADS=1`, and records USER+SYS CPU, wall and `memory.peak`. Each forces **equality to a complete
literal** with the **production import closure** (audit F1):

| probe | statement | decides |
|---|---|---|
| G0 | `lower_jet` (M0) | M0 fits (< 9 GB); else split by program segments (SO-LOCK-COST G1c) |
| G1 | import-only control of a segment module | the base with the plan and ledger imports |
| G2 | one cfgFull segment at ≈ 75 k calls (8 imports, real exports) | κ (ms and KB per call), seed and export overhead |
| G3 | one cfgFull segment at ≈ 150 k calls | linearity of the rate; whether B = 150 k is safe |
| G4 | (a) all 7 shards of `[0,10]` `= true` and (b) its decode `dyadicTerms … = some lit`, as production modules | confirms SO-DATA3's P1/RR split (6.4 GB = 3.3 + 3.1) with module imports |
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

Counts (exact; B = 75 k):

| per torus | models | bytes (exact emitted) |
|---|---:|---:|
| cfgFull ledger | 155 | 2.49 MB |
| cfgLow ledger | 324 / 322 | 5.58 / 5.54 MB |
| distinct across the two chains (by hash) | 384 | ≈ 7.6 MB |
| Gram stage literals | 7 entries + 17 decoded product outputs | 0.05 + 0.15 MB |
| torsion stage literals | ≈ 60 matrix entries + 106 decoded product outputs | 0.8 + 1.2 MB |
| compose product literals (`[0,10]` and the two residuals, per chain) | 6 | ≈ 0.2 MB |
| metas | ≤ 2 cache entries, 109 boundaries | ≈ 0.1 MB (the reflected witness once) |
| **total** | | **≈ 10–11 MB per torus; ≈ 21 MB for both** |

The literal format is SO-DATA3's `tm k₀ k₁ re im` rows, at 31.7 B per term (census). For scale: the whole
887-slot cfgFull state would be 13.7 MB. At B = 150 k the ledger shrinks to 1.7 + 4.6 MB per torus.

**Flag:** not triggered (≈ 10–11 MB per torus). The total is well under 50 MB, but it lands in the public
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
| packed products: (a) shard group + (b) decode, 129 products | 258 |
| invariance rows + energy tail | 5 |
| Gram and BG entries + final rows | 8 |
| torsion: `dkModels`, `dkwModels`, `gramInvModels`, 54–75 entries, adds, `T` average | 62–83 |
| frames: L, N, Nt, T corners | 4 |
| assembly (`compose_eq` instances, recipes; no heavy kernel work) | ≈ 10 |
| **total** | **≈ 460–480** (plus the existing Static, HamBounds, HamClaim, Embedding, Core, bites, Graph) |

Shared: one jet bridge for both tori.

**Per-theorem memory bound and evidence.** The bound is predicted, not guaranteed: peak ≤ base + 0.13·t, with
t ≤ 40 s ⇒ ≤ 6.7 GB at base 1.5 GB (≤ 8.7 GB at the in-file 3.5 GB base). The shard groups and decodes are
≤ 3.3 GB of work by SO-DATA3's measurement (§4.1). Each theorem's own capped build is its receipt, and the runner records the peak. A
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
| M0 | the same `HamJet.beq`. The lock's J0 projects above 10 GB (SO-LOCK-COST §2), so the bridge itself is split by program segments: `opsBeq` on `[0,800)`, …, plus `v0`/`d1`/`d2`/`d3` and a structural `List.take_append_drop` assembly (SO-LOCK-COST G1c). |
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
| **SO-CSEG-A** | `CertificateSharp/Kernel/SegDefs.lean`: `ComposeMeta`, `SegSpec`, `ComposeCkpt`, `seed`, `shadowStep`, `segOk`, `planOk`, `polyBeq`/`modelBeq`/`pairBeq`/`cacheBeq` with soundness, `SlpOp.beq`/`opsBeq`/`HamJet.beq` with `eq_of_beq` (≈ 330). `Kernel/SegAgree.lean`: `AgreeOn`, `composeStep_congr` (8 arms), `composeStep_infallible`, `shadow_agree`, persistence (≈ 330). | 660 | landed `Expr/Compose`, `Kernel/Prune` (`opDeps`) |
| **SO-CSEG-B** | `Kernel/SegChain.lean`: `planOk` facts, induction, `ComposeCkpt.compose_eq` (≈ 280). `Kernel/SegBridges.lean`: `checkInvariance_eq_of_compose`, `checkEnergy_eq_of_compose`, `List.all_range_of` (≈ 120). `Tests/Seg.lean`: toys equal to the monolithic run; negatives: corrupted export, wrong norm, wrong radius, missing import, dead read, skipped fallible op, wrong counter, wrong cache order, malformed meta (≈ 220). | 620 | A |
| **SO-CSEG-L2** | `Kernel/Stage.lean`: the §3.4 table lemmas, `gramCheck_eq_some_of`, `torsionModels_eq_of_stages`, `frameNModels` unfolding (≈ 300). `Tests/Stage.lean`: toy recipes, R7 timing (≈ 120). | 420 | landed Gram, Torsion, Frame |
| **SO-CSEG-L3** | `Kernel/ProductSplit.lean`: `mulN_eq_of_polyProduct`, `polyProduct_eq_of_parts`, `packedRealProduct_eq_of_shards`, `expWitnessRadius_eq_of_residuals`, `charResolve` unfolding (≈ 280). `Kernel/SegOne.lean`: `segOk_one_of`, `seed_slot_of_mem`, the `composeStep` arm equations (≈ 100). Tests (≈ 110). | 490 | landed `Model/*`, `Poly/*`; A |
| **SO-CSEG-GEN** | Python. `csplit_census.py` (done), `csplit_plan.py` (done; to become the optimizer: union-aware ledger, forced cuts at L1b ops, B from the gate). `csplit_ledger.py`: pairs, metas and stage literals from the mirror, bit-exact, self-checked by re-running segments in the mirror. `csplit_emit.py`: Lean modules, extending `sofx_lean.py`'s formatters. `csplit_kbuild.sh`. `heavy_modules.txt`. | ≈ 900 | sofx mirror (SO-DATA3) |
| **SO-CSEG-CAL** | the §4.5 gate (probes in `kam-data/so-csplit/gate`, not landed) | – | A (for G2/G3), L3 (G4/G5) |
| **SO-CSEG-DATA** | per torus: the emitted modules and the serial capped run | generated | all |

**Order:** A → B and L3 in parallel → CAL → L2 → GEN finalization → DATA.
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
- **R2. Packed products.** These are measured: 6.4 GB for the largest whole, so they are always split, giving
  shard groups ≤ 3.3 GB and decodes ≤ 3.1 GB. The residual risk is a cfgLow product whose decode or shard group is
  larger than `[0,10]`'s; none is, by the report's shard counts (≤ 7) and target sizes (≤ 4.3 k).
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
  10–11 MB each, under the flag.
- **O3.** Landing procedure for heavy modules: a serial capped prebuild in `land-branch.sh` (§6), plus a lint on
  `heavy_modules.txt`.
- **O4.** Optional: re-prove `checkHamBounds` and `checkHamClaim` through the jet bridge (HamClaim is at 10.24 GB
  RSS, 2 % under the cap).

## 11. Evidence files

- `scripts/spin_orbit/csplit_census.py`, `csplit_plan.py` (this branch).
- `kam-data/so-csplit/census_{lower,upper}.json`: per-slot op, reads, operand and output terms, backend calls,
  packed products, literal bytes, model hash; Gram entries; torsion stages; invariance rows; energy tail; frame
  corners.
- `kam-data/so-csplit/plan_{lower,upper}_{75000,150000}.json` and `plan_*_75000_s6500.json` (with a cost per
  packed product inside segments; superseded by L1c memoization, kept for comparison).
- SO-DATA3's product probes: `kam-data/so-data3/product-probes.md`, `probes/csplit/{P0,P1,SH,RR,C1,EN14}`.
- Runs: `python3 -B csplit_census.py lower|upper OUT` (85 s each, 0.23 GB RSS), then
  `python3 -B -I csplit_plan.py CENSUS B SHARD`.
