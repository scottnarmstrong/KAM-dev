# SO-KDEPTH: audit request

Audit the checker commit `f1f3b760` (branch `inp-sokdepth`). It is the only commit to land. Everything else on the branch is R1 measurement (`.drafts/kd`) or the unlanded soemitfix base. The full prover handoff follows.


Branch `inp-sokdepth`. **Checker change to land: commit `f1f3b760` only** (cherry-pick without the data). The
following handoff commit (`.drafts/`, `docs/tracks/SO/audits/SO-KDEPTH-handoff.md`) is R1 measurement and
report only, so do not land the `.drafts/kd` probes. The parent commits up to `9c774b03` are the inp-soemitfix base,
whose R1 data does not land. Probes and
logs are in `.drafts/kd/` (not for landing). No frozen file, manifest, README, KAM.lean or Ball.lean was touched.

## Files
- NEW `KAM/Certificate/Arith/BalancedSum.lean`: `sumPairsUp`, `pairRounds`, `sumUp` and `sumPairsUp_ge`,
  `pairRounds_ge`, `foldr_upAdd_ge`, `sumUp_ge`, MOVED unchanged from `Model/Terms.lean` (same names, namespace and
  bodies), so that `Model/Basic.lean` can use them. Everything that imports `Model/Terms` still sees them.
- `KAM/Certificate/Model/Basic.lean`: `CertPoly.weightedNormUp` body is now a balanced `sumUp`. New lemma
  `CertPoly.weightedNormUp_ge`, used by `CertModel.norm_le_supBound`. The old `weightedNormUp_bound` (a foldr
  statement) is kept unchanged as a compatibility export.
- `KAM/Certificate/Model/Terms.lean`: `directItems` body is now a balanced merge tree (`mergeRowsLevel`,
  `mergeRowsTree`). The old body is kept as `directItemsLinear`. `directItems_spec` keeps its statement and is
  re-proved via `ErrRep`, `RowsRep` (inductive: `empty`, `push`), `errRep_merge`, `errRep_nil`, `rowsRep_level`,
  `rowsRep_foldl`, `rowsRep_tree`.
- `KAM/Certificate/Expr/Compose.lean`: `composeOps` body is the strict loop `composeOpsAux`. Equal to the old fold:
  `composeOpsAux_eq` and `composeOps_eq`. `composeOps_sound` keeps its statement and rewrites with `composeOps_eq`.
- NEW `KAM/Certificate/Model/FixedEq.lean`: `CertFixed.eq_of_m`, `sumPairsUp_fixed_m`, `pairRounds_fixed_m`,
  `foldr_upAdd_fixed_m`, `sumUp_fixed_m`, `CertPoly.weightedNormUp_fixed_eq`.

No signed statement and no certificate format changed. Only bodies and helper lemmas changed.

## What the kernel's depth limit actually is (P0 probe, 20,000 elements)
Each of these passes at 20k: `length`, `all`, `filter` (both branches), `reverse`, `map`, `++`, `getD`, `range`,
`filterMap`, `zip`, `flatMap`, `take`, `find?`, and `foldl`/`foldr` of **Nat** `+` (GMP literals). Only
accumulations of non-literal arithmetic fail, for example a `foldl`/`foldr` of `Int` `+` (and so of `CertFixed`
`upAdd`, and of nested lazy merges or binds). This narrows the inventory a lot.

## Inventory (kernel paths of the 8 sub-checks and `checkSoGraph`)
| Traversal | Where | Depth before | Action |
|---|---|---|---|
| `CertPoly.weightedNormUp` (foldr `upAdd`, every `supBound`) | Model/Basic | O(L), fails at 20k (control `S_wnuOld`: deep recursion at 9 s) | **balanced `sumUp`** |
| `directItems` (foldl of lazy `mergeErrTerms`, one per row) | Model/Terms | O(rows) nested merges (sos products: about 265 rows) | **balanced merge tree** |
| `composeOps` (foldl of `Option.bind`, one per SLP op; about 887 ops) | Expr/Compose | O(ops) | **strict loop** |
| `sumUp`, `errRadius`, `supNormUp`, `coeffSumBall` (`listSum`), `modelSum`, `spPack`, `packShift`, `packRangeSum/Max`, `natSlotsSh` | various | O(log L) already | none |
| `mergeErrTerms`, `itemsPoly`, `truncPoly`, `toMants`, `dyadicTerms`, `toSortedPoly` (reverse/map/++), `filter`/`filterMap`/`all` uses, `List.range`, `targetTerms`, `packOverlapAdd`, `windowZeroOK`/`adviceZeroOK`, `reconFitsAux`, `packStrictAsc`, `packMaxAbsAux`/`spMax` | Model, Poly | O(1) per cell (lazy cons or tail-iterative Bool, Nat accumulators) | none |
| `spBlocks` (nested `dropWhile`, one per block) | Poly/Sparse | O(#blocks) (tens of shards) | none (small) |
| `shardPackedSp` / `shardConv` Int `.sum` over `range (s+1)` | Poly | O(#shards), small | none |
| `maxAbs` (foldr Nat `max`), `freqNormLo`, `maxCandidate`, `charPhaseModel`/`(List.range n).foldl` | Packed, Defs, Gram, ComposeModels | Nat, or n ≤ 3 entries | none |
| `findKeyIdx` (`Option.map` per position) | ComposeModels | O(position) in charWit/cache (1 entry for R1) | none (small) |
| `Slp.balls` / `ballsAux` (`acc ++ [b]`) | Expr/Ball.lean | not changed (SO-BALLDY's file, checkHamBounds only) | reported to the orchestrator |
| `Slp.vals`, `packSum`, `pairVal`, `listConv`, dense `packFill` | specs and the dense fallback only | never on the sparse kernel path | none |

## Value preservation (for the Python mirror `scripts/spin_orbit/sofx_*.py`)
- `composeOps`: **value-preserving for every backend**. Exact equality `composeOps_eq` (old foldl). The mirror
  needs no change.
- `weightedNormUp`: the order of upward additions changes from a right fold to `sumUp`, i.e. 64 rounds of
  `[a,b,c,…] ↦ [upAdd a b, …]` then `foldr upAdd (ofInt 0)`. That is the mirror's existing `sumUp(B, …)` over the
  same summands `upMul(normUp c, ofRatUp(w^{Σ|k_i|}))` in term order. On `CertFixed P` `upAdd` is exact integer
  addition, so the value is **unchanged**: Lean `CertPoly.weightedNormUp_fixed_eq` (equal to the old foldr). The
  mirror may keep its loop, or call `sumUp`; the results are bit-identical. For a general backend there is no `_eq`.
  Soundness then comes from `sumUp_ge` with the per-term bounds (`CertPoly.weightedNormUp_ge`).
- `directItems`: new merge order. Rows `r_i = rowItems(a_i, bs)` in order. Repeat
  `[r0,r1,r2,…] ↦ [merge(r0,r1), merge(r2,r3), …]` (an odd last row is carried) until one row remains (`[]` if
  there are no rows). The 64-level fallback (linear foldl) is unreachable below 2^64 rows. Soundness:
  `directItems_spec`, same statement (each merge preserves the representation invariant `ErrRep`).
  - On `CertFixed`, `add` and `upAdd` are exact and `addErr = 0`, so each key's coefficient and error are the same
    integer sums in any grouping.
  - When every row has strictly increasing keys (true for sorted factors), both orders give the same sorted output
    list, so the value is unchanged and the mirror needs no change.
  - This is my argument only, **not proved in Lean**. For unsorted or duplicate-key rows the output list order may
    differ. To be bit-safe, change the mirror's `directItems` to the tree above.

## Acceptance (lower R1 torus, `CertFixed 320`; each run alone under the lock + `MemoryMax=10G`)
Times are total process wall time. In Lean 4.35 `addDecl` checks asynchronously, so the in-file "ms" is
meaningless.

| run | before (SO-DATA-2 / SO-EMITFIX) | now |
|---|---|---|
| `checkStatic` | – | passes, 7 s, 0.3 GB |
| `checkSmallness` | – | passes, 6 s, 0.2 GB |
| `checkEmbedding` (whole) | kernel deep recursion at 15 s, 0.9 GB | **no deep recursion**; cap hit (OOM) after about 22 min, 10 GB |
| – `angleImOk` branch 1, angle 0 (`angleModel` supBound) | | passes, 23 s, 1.4 GB |
| – `compDerivModel` angle 0 supBound | | passes, 119 s, 2.6 GB |
| – `actionShiftModel` 0 supBound | | passes, 24 s, 2.3 GB |
| – `dkRowUp` row 0 | | passes, 384 s, 5.5 GB |
| `checkSoGraph` | stuck or deep recursion | **no deep recursion**; killed at the cap after 386 s, 10 GB |
| `checkGram` | – | **stopped by me at the orchestrator's request** after about 72 min (16:14–17:26 UTC), still running under the 10 GB cap, no error so far (the peak was not recorded, because the sampler was stopped with the run) |
| `checkEnergy`, `checkTorsion`, `checkInvariance` | – | **not run** (stopped before their turn, to free the shared lock for SO-DATA3) |

**Finding for SO-DATA3.**
- `checkGram` on R1 runs for more than 55 min (stopped at about 72 min) in a single kernel check.
- On R1 the whole `checkEmbedding` and `checkSoGraph` are memory-bound in one kernel check. Each piece of
  `checkEmbedding` passes alone.
- Splitting theorems per shard and per bound (as SO-DATA3 plans) is the remedy.
- Per the orchestrator, no further memory work was done for R1.

Synthetic 20,000-term polynomial (`CertFixed 320`, degree ≤ 150, `w = 11/10`; `.drafts/kd/S_*.lean`). Every run
passes with no deep recursion:

| op | time | memory |
|---|---|---|
| `weightedNormUp` | 36 s | 3.3 GB |
| `supNormUp` | 33 s | 3.3 GB |
| `supBound` | 32 s | 3.3 GB |
| `CertModel.add` | 57 s | 5.2 GB |
| `coeffSumBall` | 10 s | 1.3 GB |
| `toSortedPoly` (40k) | 73 s | 6.7 GB |
| `directItems` 200×200 | 73 s | 7.0 GB |
| `toDeg` | 90 s | 7.2 GB |
| `ofDeriv` | 79 s | 6.3 GB |

Control: the old foldr `weightedNormUp` gives deep recursion at 9 s. (Each `S_*` file also reports a compile error
for its helper constant `big`; that is noncomputable and harmless, since the theorems themselves passed.)

## Tests
Every `KAM/Certificate/Tests/*.lean` (20 modules, built one at a time through the gate) built OK:
`Toy2d` 93 s, `Negative` 63 s, `Toy3` 34 s, and so on (`.drafts/kd/tests.log`). `KAM/CertificateSharp/Tests` does
**not exist** on this branch, so I could not run it.

## Checks
- Gate builds:
  - `KAM.Certificate.Model.FixedEq`, `KAM.Certificate.Soundness`, `KAM.SpinOrbit.Graph.Cert`,
    `KAM.SpinOrbit.LunarAssembly`, `KAM.SpinOrbit.Data.Lower.Cert` and the tests: success, no warnings in my files.
- `scripts/lint_sources.sh`: `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144)`. It also reports `KAM.lean is out of
  date` and `check_lean_modules: FAIL`.
  - `KAM.lean` is generated (rule 10). The new modules `Arith/BalancedSum` and `Model/FixedEq` must be added by
    `scripts/gen_root_imports.py` at landing. The branch's existing data modules also make it stale.
  - The module check flags `.drafts` probes (plain scripts, as in SO-EMITFIX).
- `main_shortname_check.py` on my modules: no new reused names. The remaining hits (`CertModel.Encloses`,
  `ComposeState.SlotsEnclose`) are pre-existing.
- Lines ≤ 100 columns. No heartbeat or recursion-depth options anywhere.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
  - `checkTorusCertificate_sound`
  - `checkSoGraph_sound`
  - `directItems_spec`
  - `composeOps_eq`
  - `CertPoly.weightedNormUp_fixed_eq`

  `checkTorusCertificateSharp_sound` does not exist on this branch.

## Uncertainties and deviations
- No `_eq` for `directItems` (rounded merge order); see "Value preservation" above.
- No `_eq` for `weightedNormUp` on a general backend; it is exact on `CertFixed`.
- Moving `sumUp` to a new module is a file move (same declarations).
- `Ball.lean` traversals (`ballsAux` `acc ++ [b]`, `getD`) are left to SO-BALLDY.
- No errata in pinned sources.

## Landing branch and AUDIT FOCUS (orchestrator)

Landing branch: inp-sokdepth-oninp. The checker commit f1f3b760 is cherry-picked onto inp a5f010eb as f1dc41bf. inp
contains sharp-v2 (V2, Sharp2), SO-BALLDY/BALLFIX and the lock packages; none of the R1 data or .drafts probes land.
A full `KAM` build of this branch passes (10687 jobs), and KAM.Certificate.Model.FixedEq builds; it is imported
nowhere yet, and the root is regenerated at landing.

AUDIT FOCUS (owner ruling D39: implementation change, statements unchanged):
1. No signed statement changed. Every public declaration of Model/Basic.lean, Model/Terms.lean and
   Expr/Compose.lean present on inp keeps its exact header, in particular `directItems_spec`, `composeOps_sound`,
   `CertModel.norm_le_supBound` and `weightedNormUp_bound`. The declarations moved into Arith/BalancedSum.lean
   keep their names, namespace, statements and bodies, and every former importer still sees them.
2. Soundness: `sumUp_ge` and `weightedNormUp_ge`; the `ErrRep`/`RowsRep` invariant through the balanced merge tree
   (`errRep_merge`, `rowsRep_tree`), including odd row counts, zero rows and the unreachable 64-level fallback;
   `composeOpsAux_eq` and `composeOps_eq`.
3. Value claims for the Python mirror:
   - `composeOps` is equal for every backend (proved);
   - `weightedNormUp` is equal on CertFixed (`weightedNormUp_fixed_eq`, proved);
   - `directItems` equality for sorted rows is only argued. Say whether the argument is right, and how the
     mirror must order merges to be bit-safe.
4. Kernel friendliness: no O(length)-deep accumulation of non-literal arithmetic remains on these paths.
5. sharp-v2 and the lock modules consume these internals (compose, models), and the full build passes, so check
   that no consumer's statement changed.
6. Tests, kernel replay, and the axioms of `checkTorusCertificate_sound`, `checkTorusCertificateSharp_sound` and
   `checkTorusCertificateV2_sound`.
