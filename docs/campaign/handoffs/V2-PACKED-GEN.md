# V2-PACKED-GEN handoff: the packed sharp-site engine, the whole-torus packed generator and its run harness

Brief: `/home/scott/kam-tools/briefs/V2-PACKED-GEN.md` (kamx-pk-gen). Branch `v2-packed-gen`, from `v2-packed-jet`
`34d30126`, fast-forwarded to `origin/main` `7b81f9b9` (the landing of `v2-packed-jet`). Local commits only.

DRAFT (in progress; the sections marked TODO are filled when the runs finish).

## Result

TODO

## (A) The packed sharp-site engine

**Lean:** `KAM/CertificateSharp/Packed/RouteSharp.lean` (new).
- `FrameChecker`: a Boolean frame test with the landed `FrameMajorants` as its soundness, under `BaseFacts`.
  Instances: `landedFrames` (the landed `checkFrameMajorants`) and `framesR bk mm rb tm rm` (B3b's packed
  `checkFrameMajorantsR`). The jet-fed packed frames (`checkFrameMajorantsRJ`, kamx-pk-cons) are one more
  instance (`framesRJ`, below): no new engine is needed for the jet route.
- `refinedTestSWith F`, `routeARefinedSWith F : EngineV2`: route A refined with the certified sharp sites
  (`refinedCoreS`, `V2/RouteARefinedS.lean`, unchanged) and the frame checker `F`.
  `refinedTestSWith landedFrames = refinedTestS` by `rfl` (`refinedTestSWith_landed`).
- `refinedTestPackedS bk mm rb tm rm` (`= checkHamClaim && checkFrameMajorantsR … && refinedCoreS`, by `rfl`:
  `refinedTestPackedS_eq`), `routeARefinedPackedS`, `routeV2AllPackedS := routeV2AllS.orElse routeARefinedPackedS`
  (every witness of `routeV2AllS` runs unchanged: `checkV2With_routeV2AllPackedS_inl`, `_inr`).
- Soundness at every base checker: `checkV2With_routeARefinedSWith_sound`, `checkV2With_routeV2AllPackedS_sound`;
  at B3b's `torsRBase`: `checkV2With_packedS_sound` (the landed `CertifiedTorus`).
- Assembly: `refinedTestPackedS_of`, `checkV2With_packedS_of`; never worse than the classical-site packed engine:
  `refinedTestPackedS_ofPacked`.
- **`refinedCoreS` reads nothing the packed route removed.** Its inputs are `n`, `c.params`, `c.freqBox` and the
  rational witness `RefinedWitS` (`RefinedWit.num`, `sitesOk`, `coverOk`, `classicalOk`, `finalOkA`): no Gram,
  torsion or frame model. It is reused verbatim.

**Gate (T′'s data, production form).** TODO

## (B) The whole-torus packed pipeline

**Where the modules live (opt-in; never in the core's build).** A scratch Lake package, by default
`<core worktree>/.lake/lg00-packed` (git-ignored, never committed), made by `scripts/packed/gen_pkg.py`:
- its `lakefile.lean` is LG00's (`applications/lg00` on `lg00-app`) byte for byte, except the core's path: the
  package keeps LG00's name `kam-lg00` and its library `LG00` with LG00's Lean options, so an LG00 module whose
  sources and core imports are unchanged has the very Lake trace LG00's run computed;
- two more libraries: `LG00Packed` (the packed modules on LG00's **real** certificate: the A gate, the B3b route)
  and `LG00P` (the production route on kamx-packed's **certificate copy**, V2-PACKED-PROD-API §3), both with
  LG00's options plus the profiler (the harness reads each module's kernel time);
- the LG00 modules a root needs are copied (sources) and their built artifacts reused from LG00's run: `.olean*`
  and `.ir` hardlinked (Lake replaces them, never rewrites them in place), everything else (`.trace`, `.hash`,
  `.ilean`, `.c`) copied, so nothing this package's Lake does can touch `lg00-app`'s files;
- `lake-manifest.json` is LG00's with the core's path; `.lake/packages` is a symlink to the core's packages.
Measured: T′'s 279 data modules are reused against this branch's core with no rebuild
(`lake build --no-build LG00.TP.Data.Cert`: `All targets up-to-date (3539 jobs)`). Only the modules importing
`V2/SiteSign.lean` or `V2/SiteShard.lean` (changed on `main` after `lg00-app`'s pin: T′'s `Final` site and witness
modules) are rebuilt, as V2-SITES-SIGN's landing note predicted.

**Generators** (`scripts/packed/`, all new; untrusted; every emitted module is checked by the kernel):

| script | role |
|---|---|
| `gen_cert.py` | reads a certificate tree (`LG00/TP`, `LG00/TPP`, or the first certificate `KAM/LG00Cert`): every number of the packed stages (parameters, box, weight, zero modes, degrees, π enclosure, `cfgLow`, claims) from the tree, none hard-coded; `compute` = B2/B3b (the legacy gate generators' arithmetic, reused); `compute_j` = B3b on the jet's wanted nodes (kamx-packed's mirror cache); `frames` = the frame mirror. Regression: `--check-legacy` reproduces V2-PACKED-FRAMES' edges of the first certificate bit for bit. |
| `gen_pkg.py` | the scratch package and the reuse of LG00's built modules (above). |
| `gen_port.py` | the chain-free part of LG00's proof (static, Hamiltonian balls and bounds, embedding, disc pass, sharp sites, frequency facts, Hamiltonian identity, model, window, confinement form) copied onto kamx-packed's certificate copy, renamed `LG00 → LG00P` with `prod_cert_gen.cert_text`; fails closed if the closure reaches a landed chain or the advice/witness data (T′: 168 modules). |
| `gen_packed.py` | the packed modules of a tree (below), `--prefix LG00` (real certificate) or `LG00P` (the copy). |
| `run_packed.py` | the run harness (below). |

**`gen_packed.py` stages.** Every module is a Lean module (copyright, `module`, `public import`, docstring,
`@[expose] public noncomputable section`), lines ≤ 100 characters, ≤ 1,400 lines (data split into parts).
- `data`: the shared data modules, one definition per memo entry: `pkGBook`, `pkGMemo` (B2), `pkTMemo` (the B3b
  boundary memo; on the jet route only `D²K`), `pkRBook`, `pkRMemo` (the rounded node memo and its tables),
  `pkGDB`, `pkEps`.
- `frames` (+ `sharp`): `pkFrameL/N/T` at the route witness's claims; the A gate `pkGateA`; the one-ulp attacks.
- `gram`: the 8 boundary entries, the core, `pkCheckGram : checkGramPacked pkGBook pkGMemo lg00Cert = true`.
- `tors`: the 36 boundary entries, the guards, the seven stages (`DN`, `X_N` entry by entry), the averages, the
  final test, `pkTorsCore` (via `TorsRAsm.lean`).
- `assembly` (real certificate, the B3b route): the landed `cfgLow` composition (`pkComposeLow`, from the tree's
  `Low` chain), `pkCheckTorsion`, `pkFrames`, `pkEngine`, `pkBase` (`torsRBase`), `pk_check`, and
  `pk_kamTorus`: the statement of the tree's `Main.lean`, verbatim, re-proved through
  `checkV2With_packedS_sound`.
- `jet` (the production route, `--prefix LG00P --jet-low CACHE --jet-full CACHE`): the B3b memos recomputed on
  the jet's nodes; the torsion (`checkTorsionJ`: `ptD2All`, `jetLowOk`, `torsRCoreJ` in 13 parts), the frames
  (`checkFrameMajorantsRJ`), the invariance (`pkIBook`, `ivGuard`, four `ivRowOk`, `jetFullOk`), the energy,
  `jetBase`, the engine `routeARefinedPackedSJ`, `pk_checkJ`, `pk_kamTorus`. Generated against kamx-pk-cons'
  committed API (`v2-packed-cons` `75deebd9`) and kamx-packed's (`v2-packed-prod` `0d5f39d9`, API note §3: the
  chain theorems `jetLow_check_cert`, `jetFull_check_cert`, `jdLow`, `jdFull`, `bLow`, `bFull` in
  `LG00P.<T>.Jet.<C>.ChainCert`).

**Agreements the jet route needs (checked in the kernel; the generator asserts them first).**
- The Low chain's box is the torsion's box: `layoutEq jdLow.jb.Lb pkRBook.Lb` (half-width 25, stride 101) at
  the same slot width. T′: the B3b book needs 392 bits and the jet's Low chain has 392: equal, no regeneration.
  If a tree needs more, `gen_packed.py` stops with the width to pass to `jet_prod_gen.py --width`.
- `pkRBook.bA = bLow` (the jet's largest wanted load; `jetLowOk` reads `jetCheck … rb.bA`), `pkIBook.bJ = bFull`,
  `pkIBook.Lb` the Full chain's box (half-width 48) at its width.
- T′ (mirror): the torsion test on the jet's nodes passes with margin 0.00132 (the landed-model route: 0.00118;
  the jet's radii are tighter), and the frames at T′'s claims: `|Lᵀ|` 1.3620 / 1.37, `|N|` 1.1992 / 1.21,
  `|Nᵀ|` 1.4397 / 1.45, `sup |T|` 117.5007 / 118.

**T″ the same way.** `gen_cert.py …/LG00/TPP` (no change to any script): T″'s own parameters, box
(`s = 886058956738442102019008342433694847/886058070680308099785085113265000000`), zero modes and claims are read
from its tree. The B3b mirror passes (torsion margin 0.00118) and the frames at T″'s claims: `|Lᵀ|` 1.3513 / 1.36,
`|N|` 1.1961 / 1.2, `|Nᵀ|` 1.4334 / 1.44, `sup |T|` 115.68 / 116.

**Run harness** (`run_packed.py LOGDIR CAP TARGET…`).
- The module list: the targets' import closure inside the package, dependencies first.
- Reuse: staleness predicted from the import graph (no artifacts, a stale import, or a core import whose source
  differs from the core LG00's artifacts were built against), confirmed by ONE `lake build --no-build` of the
  predicted-fresh set (bisected only if Lake disagrees). A per-module check costs ≈ 30 s of Lake workspace
  loading, so this matters: T′'s 272 reused modules are confirmed in one call.
- Each module: `lake build <module>` alone (its imports are built), `systemd-run --user --scope -p MemoryMax=CAP
  -p MemorySwapMax=0`, `nice -n 5`, `LEAN_NUM_THREADS=1`, `/usr/bin/time -v`, the scope's charge sampled every 0.2 s.
  Gates: user anon ≤ 20 GB (wait), ≥ 30 GB free disk (stop: `V2-PACKED-GEN BLOCKED disk`).
- Ledger (`LOGDIR/ledger.tsv`): module, user s, sys s, wall, max RSS kB, cgroup peak bytes, exit, kind
  (`built`/`reused`), kernel s (the module's own `type checking took` lines: Lake replays the logs of the imports,
  so only the module's section is read), cap. Resumable: passed modules are skipped. A failed module's dependants
  are skipped. `--summary LOGDIR` prints the totals per stage.

## Checks and their output

TODO

## Owner questions

TODO

## Suspected errata and deviations

TODO
