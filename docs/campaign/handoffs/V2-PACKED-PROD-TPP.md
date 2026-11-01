# V2-PACKED-PROD-TPP handoff (kamx-packed): T″'s jet chains, one theorem each

Task (orchestrator, after V2-PACKED-PROD): emit and build T″'s Low and Full jet chains as one theorem each, with
the same emitter, `_cert` versions for the consumers, measured against run18's T″ rows where they exist.
- The same emitter: wanted slots first in the ledger, the 13-node Full cap, the 40-node Low cap.
- T″'s data from `lg00-app`'s `TPP`, read only.
- LG00's jet bridge, shared by both tori.

Owner decision (Scott, 1 Nov, during the run): LG00 goes by the packed route, run18 is stopped, and T″ is proved
only by the packed route. These chains are on the critical path. Up to 3 Lean processes, each under 4 GB, each
started only while user anon memory is below 18 GB. Built before 04:30 UTC (reboot at 05:00). `P = 64` is postponed.

Branch `v2-packed-prod`, on top of `2796f8c8`; no history rewritten. Commits:
- `5086da8e`: the tooling for a second torus in the same package.
- `6bca9591`: the T″ drivers.
- `8f0c128a`: the parallel runner.
- `dcd95117`: the emitter's chunking fix.
- `ce60af37`: the start gap.
- `ad3f7c66`: T″ Low, receipts and the input pins.
- `dbeb60af`: `PROD-FIX` (AUDIT-V2-PACKED-PROD-1, docs and receipts only).
- the final commit: T″ Full, the receipts and this handoff.

## Result

**Both of T″'s jet chains are one theorem each, built with their `_cert` versions** (22:20:47 UTC).
- Every process was under 4 GiB: at most 3 at a time, each started only while user anon memory was below 18 GB.
- The jet bridge `LG00P.JetBridge` is reused, unchanged; no process went above 4 GiB.
- The data is T″ from `lg00-app` (`TPP`, read only), pinned by sha256 in `studies/V2-PACKED-PROD-TPP/inputs.sha256`:
  - LG00's `TPP/Data/*` sources and their `LG00P` copies;
  - the generator state `gen_tpp_L18/state.pkl`;
  - the extractions and the mirrors;
  - the 15 shared modules.
- The data pins equal those of V2-PACKED-CONS-GATE/TPP (kamx-pk-cons), and kamx-pk-gen's copy is byte-identical.

The theorems:
- **Low.** `LG00P.TPP.jetLow_check : jetCheck 2 lg00Cert.weight lg00Cert.piEnc lg00Cert.cfgLow lg00Cert.emb
  lg00Jet.prog jdLow bLow wantedLow = true`.
  - 77 blocks and the order certificate.
  - wanted = `torsionSlots 2 lg00Jet`, 20 slots, first in the ledger.
- **Full.** `LG00P.TPP.jetFull_check`, the same at `cfgFull`.
  - 175 blocks.
  - wanted = `lg00Jet.v0 :: d1Slots 2 lg00Jet` = `[7731, …, 7735]`.
- **For the consumers.** `jetLow_check_cert` and `jetFull_check_cert` give the same at `lg00Cert.ham.jet.prog`,
  through `LG00P.lg00Ham_jet`, with T′'s statements verbatim in the namespace `LG00P.TPP`.
- **Axioms.** `[propext, Classical.choice, Quot.sound]` for all four, and `[propext, Quot.sound]` for
  `orderOk_spec` (receipt `audit/`).
- **The certificate is the copy** `LG00P.TPP.lg00Cert`, with no advice and no witnesses. As for T′
  (AUDIT-V2-PACKED-PROD-1 C2), it is tied to LG00's `LG00.TPP.lg00Cert` by its source text
  (`studies/V2-PACKED-PROD-TPP/cert_copy.diff`, the same shape as T′'s), not by a Lean theorem.
- **Handed over.** kamx-pk-gen was told at each step, by direct message: Low `Book`/`Data` at 21:48, Low
  `ChainCert` at 21:56, the Full mirror at 21:56, Full `Book`/`Data` at 22:11, Full `ChainCert` at 22:21. It
  hard-links the built modules into its package and never rebuilds them.
- **Used end to end** (kamx-pk-gen's report, not re-checked here). `LG00P.TPP.PK.MainJ` passed at 22:23:02 UTC on
  these chains, with LG00's T″ statement verbatim and standard axioms. The whole torus took 592 modules and
  6,288 CPU-s, 17.1× below run18's complete T′. kamx-pk-gen's runner marks `LG00P.TPP.Jet.*` as foreign and never
  built them.

| T″ (packed, one theorem per chain) | modules | CPU-s | largest charge |
|---|---:|---:|---:|
| certificate copy, `TPP/Data/{DCoeffs,E0,W8,Cert}` | 4 | 17.5 | 0.50 GB |
| Low: book, 29 ledger parts (1,129 nodes), data, 77 blocks, chain, `ChainCert` | 110 | **1,789.3** | 3.72 GB (`B71`) |
| Full: book, 18 ledger parts (706 nodes), data, 175 blocks, chain, `ChainCert` | 197 | **2,149.4** | 3.38 GB (`B171`) |
| both chains | 307 | **3,938.7** | |

- **Per class.**
  - Low: ledger 647.1, blocks 1,111.9, the rest about 30.
  - Full: ledger 608.9, blocks 1,520.4, the rest about 20.
- **The shared modules** (`Format*`, `Coeffs*`, `Ham`, `JetOps*`, `Jet`) and the jet bridge were built for T′ and
  are reused unchanged: no new cost.
- **Wall time.**
  - Low's Lean ran 21:43–21:56 and Full's 22:08–22:21, three processes at a time.
  - Emission took 5 min 40 s for Low and 12 min 09 s for Full.
  - The mirrors took 20 and 44 min, the two concurrently.
- **Radii of the wanted slots.**
  - Low: 1.07e-17 to 2.70e-15.
  - Full: 5.01e-23 to 1.08e-21. kamx-pk-cons's T″ gate has an invariance slack of 1.52e-18.
- **Against T′'s packed build.** Low 1,467.2 → 1,789.3 and Full 2,647.8 → 2,149.4, with the same plans and the same
  block and node counts.
  - Single runs on a shared machine: T′ ran one process at a time beside LG00's three, T″ three at a time beside
    kamx-pk-gen's two.
  - The per-module CPU moves with the load: Full blocks average 8.7 CPU-s (T′ 10.5) and Low blocks 14.4 (T′ 11.4).
    So the two tori cost the same within about ±20%.
**Against run18's T″ rows** (`run18_cmp.json`, from the final ledger `~/kam-data/lg00/run18/ledger.tsv`; run18
was stopped, so T″ is partial):

| | run18 T″ rows | landed CPU-s | packed T″ CPU-s | ratio |
|---|---:|---:|---:|---:|
| Full (rows that exist) | 1,177 of T′'s 1,637 | 26,940.1 | 2,149.4 (whole chain) | ≥ 12.5× |
| Full (estimate, whole landed stage) | | ≈ 44,960 | 2,149.4 | ≈ 20.9× |
| Low | none | (T′: 55,812.7) | 1,789.3 | — |
| Data | 274 | 4,066.3 | 17.5 (+ shared, reused) | |

- **The 1,177 measured rows already cost 12.5 times the whole packed Full chain.**
- **The estimate.** The same 1,177 modules cost 1.394 times their T′ counterparts (19,328.9 CPU-s). Scaling T′'s
  remaining 460 Full modules (12,926.5 CPU-s) by 1.394 gives about 44,960 CPU-s for a complete landed T″ Full
  stage. This is an estimate, not a measurement.
- **Low.** run18 has no T″ Low row, so T″ Low has no landed figure. T′'s landed Low (55,812.7) is given only for
  scale.

## Process events

1. **The emitter's chunked block list had never run** (fixed in `dcd95117`).
   - The cause: `0bb4def2` added the chunk size as a module constant `CH`, which `main()` rebinds to the mirror's
     characters.
   - It never ran because T′'s chunked Full chain was produced by patching the generated `Data`/`Chain`
     (`chunk_patch.py`), and T′'s Low kept the flat list.
   - T″'s first Low emission failed after the ledger parts (5 min 40 s). The second was stopped, and the third,
     with `CHUNK`, succeeded.
   - The Lean of the chunked chain proof is the same as T′'s Full chain (audited).
2. **The sequential driver was replaced mid-run** by the parallel one once the owner freed run18's slots. The
   emission in progress was left to finish; no Lean process was interrupted.
3. **Start spacing.** `run_gated.sh` first held its start lock for 20 s, then 3 s (`ce60af37`). Start times only;
   no effect on any receipt.
4. **Python.** The extractions, the mirrors and the emissions ran under `py_capped.sh` (8 GiB, `-B`). The Low
   mirror took 19 min 47 s and the Full mirror 44 min 08 s, the two concurrently.

## Resume after reboot (lemma.farm reboots at 05:00 UTC Mon 2 Nov; /tmp is wiped)

**State at 22:30 UTC (1 Nov).**
- Both T″ chains and their `_cert` versions are built.
- No Lean process of mine is running.
- Everything is committed. The receipts are under `docs/campaign/studies/V2-PACKED-PROD-TPP/`.
- Nothing needs rerunning after the reboot. kamx-pk-gen holds hard links to the built modules.

Everything needed survives under `/home`:
- **The generator states of T′ and T″:** `~/kam-data/v2-packed-prod/gen_tp_L18` and `gen_tpp_L18`, each with
  `SOURCE.txt` and `MANIFEST.sha256`. Their originals were in another session's `/tmp` scratchpad.
- **run18's final ledger:** `~/kam-data/lg00/run18/ledger.tsv` (sha256 `976d40fe…83de`).
- **The extractions and mirrors:** `.lake/v2-packed-prod/tp/` (T′) and `.lake/v2-packed-prod/tpp/` (T″).
- **The generated package and its builds:** `.lake/v2-packed-prod/pkg`, holding T′ and T″ (`LG00P.TP.*` and
  `LG00P.TPP.*`). kamx-pk-gen hard-links the built T″ modules into its own package.
- **The build receipts:** `.lake/v2-packed-prod/logs/{tpp_data,tpp_low,tpp_full,tpp_cert}`, copied into
  `docs/campaign/studies/V2-PACKED-PROD-TPP/`.

Commands (from the worktree root):
```
# a missing or partial T'' build: rerun the driver (receipts with exit 0 are skipped)
DEADLINE= nohup bash scripts/packed/prod_tpp_pipe.sh > .lake/v2-packed-prod/tpp/pipe.log 2>&1 &
# the receipts
python3 -I scripts/packed/prod_sum.py .lake/v2-packed-prod/pkg/modules_TPP_Full.txt .lake/v2-packed-prod/logs/tpp_full
python3 -I scripts/packed/run18_cmp.py ~/kam-data/lg00/run18/ledger.tsv
```

**Next:** `P = 64`, postponed by the owner. It is larger than first estimated (see Next below).

## Checks

- **The pipeline.** Every module has `exit 0` and `oom_kill 0` in its receipt: 4 data modules, 110 Low and 197
  Full (`prod_sum.py`: `all_pass` true, `missing` empty). The largest charges were 3.72 GB (Low `B71`) and
  3.38 GB (Full `B171`).
- **`#print axioms`** (`audit/Axioms.lean.txt`, the module `LG00P.TPP.Audit.Axioms` in the package):
  - `[propext, Classical.choice, Quot.sound]` for `jetLow_check`, `jetLow_check_cert`, `jetFull_check`,
    `jetFull_check_cert`, `jetPacked_sound`, `jetPacked_sound_prefix`, `jetCheck_of`, `jChainK_slot` and
    `jetChainOk_sound`;
  - `[propext, Quot.sound]` for `orderOk_spec`.
- **Generated sources.** The 312 `LG00P/TPP` files contain no `native_decide`, `set_option`, `sorry`, `axiom`,
  `implemented_by`, `extern`, `unsafe`, `opaque`, `macro`, `elab`, `#eval`, `ofReduceBool` or `admit`.
  - Every block module has exactly one `decide +kernel` theorem, in T′'s shape.
  - T″'s Full `Chain.lean` is byte-identical to T′'s hand-patched one after `TPP → TP`, apart from the source line.
    So the fixed emitter reproduces the audited chunked proof.
- **The certificate copy.** `DCoeffs`, `E0` and `W8` are byte-identical to `lg00-app`'s `TPP/Data` after
  `LG00 → LG00P`. `Cert` differs as `cert_copy.diff` shows, with the same shape as T′'s diff.
- **No Lean source of the core changed** in this task. `KAM/**` is untouched since `PROD-API`; the lint result is
  the same as in `PROD-FIX`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, and the old ABI step failure.

## Uncertainties

1. **The copy's identity** (AUDIT-V2-PACKED-PROD-1 C2) holds for T″ as for T′. The theorems are about
   `LG00P.TPP.lg00Cert`. The definitional bridge to LG00's own constants is kamx-pk-cons's `LG00B.TPP.Main`
   (V2-PACKED-CONS-BRIDGE, built 22:25 UTC on kamx-pk-gen's `MainJ`).
2. **The landed comparison** is partial: run18 was stopped. The Full ratio of about 20.9× is an estimate, and Low
   has no landed T″ figure.
3. **Single runs** on a shared machine; per-module CPU moved by about ±20% between T′ and T″.

## Errata and deviations

- **Errata:** no suspected defect in a pinned source.
- **Deviations:**
  - The certificate is a copy (as for T′).
  - Three Lean processes at a time (owner decision).
  - The jet bridge was not rebuilt.

## Next

- **`P = 64`, postponed.** Its earlier estimate ("a new module of 50–100 lines") is too low. `jb.P` is the
  arithmetic's working scale everywhere: every `jMul` targets `jb.P`, and `JetCheck` reads the nodes at `jb.P`.
  `jLeaf` reads leaves with `toMants cfg.toMant jb.P`, and `CertFixed.toMant 128` decodes only at scale 128. A
  rounding leaf therefore needs one of two things:
  - new copies of the block checkers that call `jLeaf` inline: the actions (`JetChain`), the constants and
    characters (`JetChar`), the constants in segments (`JetSeg`) and `jConstQ` (`JetWit`), each with its
    soundness;
  - or a new leaf-block kind with its own chain theorem, since `KBlock` is closed in a landed file.
- **kamx-pk-gen:** the end-to-end T″ run on these chains.
