# V2-PACKED-PROD handoff (kamx-packed): the jet chain as one theorem per chain, `jetCheck`, the shared data

Task (orchestrator, after V2-PACKED-JET-FULL; split over three workers at 14:30): **kamx-packed** keeps
- the jet chain as one theorem per chain (Low, Full), with the block-order proof and the prefix lemma;
- `jetCheck` / `jetPacked_sound` (design §12.2 signature);
- the 13-node segment cap;
- the shared data module.

The consumers and `jetBase` are kamx-pk-cons's (`v2-packed-cons`). The sharp-site engine, the whole-torus harness
and the end-to-end run are kamx-pk-gen's (`v2-packed-gen`).

Branch `v2-packed-prod` from `v2-packed-jet` `34d30126`. Commits:
- `e4bb0b16`: the API (`PROD-API`);
- `0d5f39d9`: the prefix lemma, the certificate copy and the production emitter;
- `6ddf90d0`: the module runner;
- `0bb4def2`: the chunked chain proof;
- the final commit: receipts and this handoff.

## Result

**Each jet chain of LG00's T′ is one theorem**, checked in the kernel and built module by module, one Lean
process at a time, every process under 4 GiB except the jet bridge (exception below). The data is T′ from
`lg00-app` `8210d92e`. That commit pins only the shared modules: T′'s `TP/Data/*` and the generator state are
untracked in `lg00-app`, so they are pinned by sha256 in `studies/V2-PACKED-PROD/inputs.sha256` (with the copies,
the extractions and the mirrors; AUDIT-V2-PACKED-PROD-1 C1). The "`lg00-app 8210d92e`" in the generated docstrings
and in `*Plan.json` `source` means the same.
- **Low.** `LG00P.TP.jetLow_check : jetCheck 2 lg00Cert.weight lg00Cert.piEnc lg00Cert.cfgLow lg00Cert.emb
  lg00Jet.prog jdLow bLow wantedLow = true`. It covers 77 blocks and the order certificate, with wanted =
  `torsionSlots 2 lg00Jet`.
- **Full.** `LG00P.TP.jetFull_check`, the same at `cfgFull`, with 175 blocks and wanted = `lg00Jet.v0 :: d1Slots 2
  lg00Jet`.
- **At the certificate's own jet.** `jetLow_check_cert` and `jetFull_check_cert` give the same at
  `lg00Cert.ham.jet.prog`, with the consumers' wanted lists, through the jet bridge.
- **For the consumers.** `jetPacked_sound S.hW S.hpe jetLow_check_cert` gives the `PEnc` of every torsion slot,
  and `… jetFull_check_cert` gives those of `v0` and `d1`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]` for all four chain theorems and the API theorems
  (receipts `audit/`).

| | landed T′ (run18, CPU-s) | packed, one theorem per chain (CPU-s) | ratio |
|---|---:|---:|---:|
| Low chain | 55,812.7 (2,484 modules) | **1,467.2** (110 modules) | **38.0×** |
| Full chain | 32,255.4 (1,637 modules) | **2,647.8** (197 modules) | **12.2×** |
| both chains | 88,068.1 | **4,115.0** | **21.4×** |
| with the shared data | + 3,378.5 (`LG00.TP.Data`: the advice `A#`, 3,295.3, and the witnesses, books and certificate data) | + 94.6 (the certificate copy) + 39.2 (the bridge) | 21.5× |

The largest charge is 3.76 GB at Low (`B71`, 40-node cap) and 3.55 GB at Full (`B142`, 13-node cap).

## The API (Lean; `KAM/CertificateSharp/Packed/JetKeyed.lean`, `JetCheck.lean`)

**The block order without node equality.** `JNode` has no decidable equality, so every node is read from one ledger
by its key, and the order becomes a statement about keys.
- `JLed`: an `α`-free node. Its radius and norm bound are rationals, rounded up by `JLed.node`; that is exact
  for the dyadic radii at the arithmetic's scale.
- `JLedger.look`: the node of a key. The partial sum of degree 0 is read as the Taylor term of degree 0, both being
  `1` (`canonKey`).
- `KBlock`: a block given by its keys only. `KBlock.toT` builds the `JBlockT` of `JetStage.lean` with its nodes
  read from the ledger. So a block's imports and exports are the pairs `(k, look k)` of its keys (`toT_imports`,
  `toT_exports`), and membership of a pair reduces to membership of its key.
- `orderOk kbs cert`: the order certificate. `cert[i][t]` is an earlier block that exports the key of the `t`-th
  import of block `i`. It is decided on keys, in one pass, with no search over blocks.
- `jChainK_slot`, `jetChainOk`, `jetChainOk_sound`: the chain theorem, by `jChainT_slot` with `hfirst` from
  `orderOk_spec` and `hng` from `toT_isGiven`, and its Boolean.

**The contract** (`JetCheck.lean`):
- `JetData`: the book, the ledger, the key-only blocks and the order certificate.
- `jetCheck`: the chain, plus every wanted slot's entry on the box at the scale `2^P` with load at most `B`.
- `jetPacked_sound`: every wanted slot `i` has a model `PEnc jd.jb.Lb B jd.jb.P (jetNode jd i) (jetRad jd i)
  (jetNb jd i)` of `θ ↦ p.val n (K.eval n θ) i` on the strip.
- `jetCheck_of`: the assembly from separate block theorems.
- `slpVal_take` (the prefix lemma) and `jetPacked_sound_prefix`, for a chain checked on a prefix of the program.
  The T′ chains name the certificate's own program, so they do not need it.
- AUDIT-V2-PACKED-CONS-1 audited `e4bb0b16`: PASS. Its C1 (a test line of 106 characters) is fixed.
- kamx-pk-cons adds `jetCheck_mono` in its own file, to meet its torsion book's load `rb.bA` and its invariance
  book's `ib.bJ` from the generated `b<C>`.

**Tests** (`JetKeyedTests.lean`, default build): a two-segment toy chain (constants, then a product) passes. It
fails with an import certified by a block that is not earlier, with a ledger norm bound below the computed one,
and with a wanted slot that no block exports.

## The shared data and the generators

Format: `docs/campaign/design/V2-PACKED-PROD-API.md`. Generated into a Lake package with `require kam`. The
scratch package is `.lake/v2-packed-prod/pkg`, wired like LG00's `applications/lg00`; it is opt-in and outside
the default build.
- **`scripts/packed/prod_cert_gen.py`.** It copies LG00's shared modules (`Format*`, `Coeffs*`, `Ham`, `JetOps*`,
  `Jet`, `JetBridge`) and T′'s `Data/{DCoeffs,E0,W8,Cert}` from `lg00-app` (read only), renamed `LG00P`. The
  certificate copy has no advice and no witnesses; every other field is the source's text (diff in the
  receipts).
  - `CertifiedTorus` reads only `params`, `ham`, `weightH`, `centre`, `radius` and `emb`, so the proposition is
    the same, without LG00's 3,378.5 CPU-s of T′ data (`LG00.TP.Data`, run18; the advice is 3,295.3 of it).
  - **The copy is a different constant** (AUDIT-V2-PACKED-PROD-1 C2). The chain theorems are about
    `LG00P.TP.lg00Cert`, in a separate package. It is tied to LG00's `LG00.TP.lg00Cert` by its source text only:
    the shared modules are byte-identical after renaming, and `Cert` differs exactly as `cert_copy.diff` shows. No
    Lean theorem relates the two constants (two `kam` checkouts cannot share a workspace). kamx-pk-cons is building
    the Lean bridge; until it lands, a whole-torus theorem on this route is a theorem about the copy.
- **`scripts/packed/jet_extract_low.py`**, run on T′'s generator state (`gen_tp_L18/state.pkl`, `lg00-app`
  `8210d92e`). Then `jet_low_gen.py --mirror-only --cache=` computes the bit-exact mirror (Low 19 min, Full
  60 min), and **`scripts/packed/jet_prod_gen.py`** emits one chain:
  - `Book`;
  - the ledger parts `Led<k>` (every node once);
  - `Data` (the key-only blocks and the order certificate);
  - one theorem module per block, `B<i>`;
  - `Chain` (`jet<C>_check`) and `ChainCert` (`jet<C>_check_cert`, through the jet bridge).
- **`scripts/packed/run_module.sh` / `run_modules.sh`.** One module at a time under a memory cap, with costs;
  resumable.
- **`scripts/packed/prod_sum.py`.** The receipts by module class.

## Measured (receipts `docs/campaign/studies/V2-PACKED-PROD/`)

| part | Low modules | Low CPU-s | Full modules | Full CPU-s |
|---|---:|---:|---:|---:|
| book | 1 | 3.5 | 1 | 2.4 |
| ledger parts (every node once) | 29 (1,129 nodes) | 550.7 | 18 (706 nodes) | 786.1 |
| chain data (blocks, order certificate) | 1 | 13.0 | 1 | 10.4 |
| block theorems (`decide +kernel`) | 77 | 880.5 | 175 | 1,836.0 |
| chain theorem (`jetCheck_of`) | 1 | 15.6 | 1 | 8.2 |
| bridge corollary (`…_check_cert`) | 1 | 3.9 | 1 | 4.7 |
| **total** | 110 | **1,467.2** | 197 | **2,647.8** |
| largest charge | | 3.76 GB | | 3.55 GB |

- **Shared by both chains.** The certificate copy is 18 modules, 94.6 CPU-s, at most 0.55 GB. The jet bridge is
  39.2 CPU-s and 6.07 GB.
- **Against the probes of V2-PACKED-JET-LOW/FULL** (the earlier torus, probe-local data):
  - Full 4,382.8 → 2,647.8 CPU-s; Low 1,415.0 → 1,467.2.
  - A block process no longer elaborates its nodes. A Full block averages 10.5 CPU-s (the probes: 26).
  - The nodes are elaborated once each, in the ledger parts: about 0.5 s a node at Low and 1.1 s at Full. That is
    now the largest cost after the kernel: 37% of Low and 30% of Full.
- **The plans.**
  - Low: `--heavy=34 --seg-io=40`, the action, exponential, power and character blocks of JET-LOW (expo,
    powsX, ≤ 8 keys).
  - Full: `--heavy=8 --seg-io=13 --act=4 --taylor=3 --pows=2 --char-keys=2 --char-io=12`.
  - The order certificates: Low 1,129 and Full 706 exported keys, every import named with its exporter, decided by
    `orderOk` in the chain theorem.
- **Radii of the wanted slots (T′).** Low 1.2e-17 to 3.0e-15; Full 4.9e-23 to 1.05e-21. The landed invariance
  margin of T′ is 7.9e-19 (err 7.2e-16), so the Full radii are about 750 times below it.
- **Ledger lookups.** A node read is a linear search of the chain's ledger (List.lookup by key). There is no sign of a
  lookup cost: the Full blocks average 10.5 CPU-s, below the probes. It was not measured separately.
- **Landed figures.** run18's ledger (LG00's T′ run, read only), each module's last run: `LG00.TP.Low.*` 2,484
  modules, `LG00.TP.Full.*` 1,637, `LG00.TP.Data.*` 275.
- **The first Full build** (receipts `full_build1/`, the same blocks before the chunked chain proof): its blocks
  took 1,851.4 CPU-s against 1,836.0 in the counted build.
- **Low, first cut** (no node cap, `low_io0/`): 58 of its 60 blocks (`B0`–`B57`) passed before `B58` was OOM-killed.

## Exceptions and process events

1. **The jet bridge.** The orchestrator allowed one solo build above 4 GiB, and it was built once: `LG00P.JetBridge`
   (`lg00Ham.jet = lg00Jet`, LG00's shared bridge, recopied), 39.2 CPU-s, 6.07 GB charged under MemoryMax=7152M,
   user anon 8.9 GB, no other Lean process of mine.
   - The first attempt at 4G was OOM-killed (43 CPU-s, receipts `logs/data`).
   - Importing `lg00-app`'s built `LG00.JetBridge` was not possible. That package requires its own checkout of
     `kam`, a workspace cannot hold two `kam` packages, and loading its `.olean` outside Lake would trust
     declarations checked against another tree.
2. **Low, first cut** (no node cap: 60 blocks). Block 58 (34 heavy steps, 74 imports + exports) was OOM-killed at
   4 GiB. Re-cut with `--seg-io=40` (77 blocks); the first cut's receipts are kept (`logs/low_io0`).
3. **The chain proof's last conjunct.** `simp only` did not discharge `∀ x ∈ [], _`. Fixed in the emitter
   (`List.forall_mem_nil _`), and the chain module was rebuilt.
4. **A rebuild of `JetCheck` inside a block build** (`Low.B68`, 1.9 s): an edit to `JetCheck.lean` during the run,
   reverted at once. Lake rebuilt only `JetCheck`, one process at a time, and judged the dependents up to date.
   The line wrap was applied after the runs.
5. **Python.** The two mirrors and the emissions ran under `py_capped.sh` (8 GiB, `-B`, so nothing is written
   into `lg00-app`).
6. **The Low instance keeps the flat block list** (77 blocks; its chain proof passed). The chunked list was
   introduced for Full (175 blocks: a 175-way `simp only` hit the default recursion depth; no override). The
   emitter now chunks every chain.

## Checks

- **Targeted build** `lake build KAM.CertificateSharp.Packed.JetCheck KAM.CertificateSharp.Packed.JetKeyedTests`:
  `Build completed successfully (3285 jobs)`; its only warnings are in landed `KAM/Certificate/` modules.
- **`#print axioms`** (`audit/Axioms.lean`, in the package):
  - `[propext, Classical.choice, Quot.sound]` for `jetLow_check`, `jetLow_check_cert`, `jetFull_check`,
    `jetFull_check_cert`, `jetPacked_sound`, `jetPacked_sound_prefix`, `jetCheck_of`, `jChainK_slot` and
    `jetChainOk_sound`;
  - `[propext, Quot.sound]` for `orderOk_spec`.
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS (4174 Lean files)` and `FROZEN-ANCHOR GUARD OK`. The
  ABI step fails as before (a frozen `.olean` is not built in this worktree). `gen_root_imports.py --check`
  exits 0.
- **Source limits** (counted in characters):
  - `JetKeyed.lean` 279 lines, `JetKeyedTests.lean` 62, `JetCheck.lean` 156;
  - no line over 100 characters in `Packed/` (AUDIT-V2-PACKED-CONS-1 C1 fixed);
  - no forbidden token or option.
- **The certificate copy.** Every copied module except `Cert` is byte-identical to its renamed source. `Cert`
  differs only as `cert_copy.diff` shows: the advice and witness imports, `lg00Wit`, the two `advice` fields and
  the docstring.

## Uncertainties

1. **The bridge above 4 GiB.** Built once under the exception. A whole-torus run builds it once, in whatever
   package holds the packed modules. Where the packed instance finally lives (an application package on main, or
   LG00's) decides whether LG00's own `LG00.JetBridge` can be imported instead.
2. **Margins.** The largest Low block (3.76 GB) is 0.53 GB under the cap; `--seg-io=36` would widen it.
3. **The generated package** (333 MB of source) is scratch, under `.lake/v2-packed-prod/pkg`. It is reproducible
   by the commands below and not committed.
4. **Single runs**, on a machine shared with LG00's run (three processes).

## Reproduce

The measured T′ instance was generated by the emitter at `3a84cc28`, and its Full `Data`/`Chain` were then
patched to the chunked block list (`chunk_patch.py`, scratch). The emitter has changed since: `2796f8c8` lists
the wanted slots first in the ledger, and `dcd95117` fixes its own chunking (it failed before; found by T″). A
rerun therefore gives the same blocks, order certificate and theorems, but not the measured files byte for byte.
`jet_prod_gen.py`'s defaults are Full's (`--heavy=8 --seg-io=13`); Low's are `--heavy=34` and no node cap.

```
S=<LG00 scratch>/gen_tp_L18/state.pkl; PK=.lake/v2-packed-prod/pkg
python3 -I scripts/packed/prod_cert_gen.py $PK                    # + lakefile, manifest, .lake/packages link
scripts/packed/py_capped.sh scripts/packed/jet_extract_low.py $S low.json <lg00-app> --stage=Low   # and Full
scripts/packed/py_capped.sh scripts/packed/jet_low_gen.py low.json --stage=Low --mirror-only --cache=low_mirror.pkl
scripts/packed/py_capped.sh scripts/packed/jet_prod_gen.py low.json low_mirror.pkl $PK --stage=Low --seg-io=40 \
  --led-nodes=40                                                   # Full: --stage=Full --seg-io=13 --led-nodes=40
bash scripts/packed/run_modules.sh 4G $PK cert_data.txt <logs>; bash scripts/packed/run_modules.sh 4G $PK \
  $PK/modules_Low.txt <logs>                                       # then Full, then the ChainCert modules
python3 -I scripts/packed/prod_sum.py $PK/modules_Low.txt <logs>
```

## AUDIT-V2-PACKED-PROD-1 (PASS WITH CHANGES) and its fixes (`PROD-FIX`, docs and receipts only)

- **C1.** `studies/V2-PACKED-PROD/inputs.sha256` pins T′'s inputs: LG00's `TP/Data/{Cert,DCoeffs,E0,W8}` sources,
  their `LG00P` copies, the generator state `gen_tp_L18/state.pkl` (saved in `~/kam-data/v2-packed-prod`), and the
  extractions and mirrors (`.lake/v2-packed-prod/tp`). Every value agrees with the report's, except that the report
  prints `W8`'s source as `2a5d6c98…00cd1a`. The full value ends `…f8cacd1a`, the file is unchanged since 03:14 on
  1 Nov, and its renamed copy matches the report's `a4c7835c…62f3`. So the report's suffix is most likely a
  transcription slip.
- **C2.** The handoff, `V2-PACKED-PROD-API.md` §2 and §12.13 now say that the copy is a different constant, tied
  to LG00's certificate by source text, not by a Lean theorem.
- **C3.** Not on this branch. The stale passages are in §14 of `V2-PACKED.md` and in `V2-PACKED-CONS.md`. Both
  exist only on `v2-packed-cons` and are kamx-pk-cons's text (`V2-PACKED-CONS M2`). This branch's `V2-PACKED.md`
  has 910 lines and no run18 figure that is still open. Editing §14 here would conflict at the merge.
- **C4.** The axiom receipt is renamed `studies/V2-PACKED-PROD/audit/Axioms.lean.txt`.
- **N1.** `prod_sum.py` now rounds once, at the end. The summaries are regenerated: the same rows and totals, with
  the per-class figures exact. The copy is 94.6, the Low ledger 550.7, the Low blocks 880.5 and the Full ledger
  786.1.
- **N2.** The data row now says what `LG00.TP.Data` holds: the advice is 3,295.3 of its 3,378.5 CPU-s.
- **N4.** The Reproduce section says which emitter made the measured instance. The emitter's usage line gives
  Low's defaults.

## Errata and deviations

- **Errata:** no suspected defect in a pinned source.
- **Deviations:**
  - The block order is an explicit order certificate on keys, with nodes read from one ledger, rather than
    `DecidableEq` on `JNode`.
  - The certificate copy has no advice and no witnesses. It is a different constant, tied to LG00's certificate
    by source text, not by a Lean theorem (above; kamx-pk-cons is building the Lean bridge).
  - The jet bridge was built above 4 GiB (the orchestrator's exception).

## Next

- **kamx-pk-cons:** the consumers on `jetPacked_sound` (its `jetCheck_mono` meets its books' load bounds).
- **kamx-pk-gen:** the whole-torus harness, from `prod_cert_gen.py` and `jet_prod_gen.py`.
- **Cost.** The ledger's literal elaboration is the next cost centre. `P = 64` (the orchestrator's next item)
  halves the digits and the literals.
