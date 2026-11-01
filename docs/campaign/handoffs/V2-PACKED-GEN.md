# V2-PACKED-GEN handoff: the packed sharp-site engine, the whole-torus packed generator and its run harness

Brief: `/home/scott/kam-tools/briefs/V2-PACKED-GEN.md` (kamx-pk-gen). Branch `v2-packed-gen`, from `v2-packed-jet`
`34d30126`, fast-forwarded to `origin/main` `7b81f9b9` (the landing of `v2-packed-jet`). Local commits only.

DRAFT (in progress: the B3b route's end-to-end run and stage C are pending).

## Result

- **(A) done** (`V2-PACKED-SHARP DONE 11955893`; AUDIT-V2-PACKED-SHARP-1 PASS WITH CHANGES, fixed in
  `SHARP-FIX 41f9e45e`). `routeARefinedPackedS` (`checkHamClaim && checkFrameMajorantsR … && refinedCoreS`) and
  `routeV2AllPackedS`, sound to the landed `CertifiedTorus` for every base checker, standard axioms. The engine is
  generic in the frame check (`FrameChecker`), so the jet route is one instance (`RouteSharpJ`, compile-checked
  against the two branches on `v2-packed-gen-int`). Gate: the gate's own modules pass on T′'s real certificate
  (frame sums at the claims, the certified sharp sites, one-ulp attacks); what it does not establish is stated in
  (A).
- **(B) built** (scripts below, all new): a certificate-tree reader (regression-equal to the first certificate's
  gates), the scratch package with LG00's built modules reused read-only, the port of LG00's chain-free proof onto
  kamx-packed's certificate copy, the module generator (B2, B3b, frames, A gate, B3b-route assembly, jet route), and
  the run harness (ledger, cap, gates, resumable, staleness predicted and confirmed by one Lake call).
  - On T′'s real certificate: the A gate (353 modules) and the B2 + B3b stages in production form (389 modules,
    1,233 CPU-s against 13,551 for the landed Gram and Torsion stages of the first certificate) pass in the kernel.
    The B3b route's end-to-end assembly to `pk_kamTorus` (LG00's `lg00_kamTorus` statement, verbatim) is emitted and
    runs when LG00's run18 finishes T′'s `Low` chain (armed; see below).
  - T″: the same scripts, unchanged, read T″'s tree; its B3b and frame mirrors pass at T″'s claims.
  - The jet route for T′ (kamx-packed's certificate copy and chains, kamx-pk-cons' consumers) is emitted (103
    modules); its mirrors pass (torsion on the jet's nodes, frames, invariance, energy), and the book widths agree.
- **(C) not started:** it needs `v2-packed-prod` and `v2-packed-cons` landed (the orchestrator's go), then
  `RouteSharpJ.lean` added, then one command: `scripts/packed/run_tree.sh TP jet <logdir>` (with kamx-packed's
  chain inputs).
- **Found on the way:** LG00's generated `Final.Freq` (T′, T″) does not elaborate (errata below); LG00's run18 will
  hit it at `TP.Main`. One-line fix verified.

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

**The jet route needs no new engine.** `RouteSharpJ.lean` (`framesRJ`, `routeARefinedPackedSJ :=
routeARefinedSWith (framesRJ …)`, `checkV2With_jetSharp_sound`, and the assembly lemmas `ptD2All_of`,
`torsRCoreJ_of`) instantiates the engine at kamx-pk-cons' `checkFrameMajorantsRJ`. It imports their modules, so it
is not on this branch: it is compile-checked on the local integration branch `v2-packed-gen-int` (this branch
merged with `v2-packed-prod` `0d5f39d9` and `v2-packed-cons` `75deebd9`; never to be landed) and is to be added
after both land (text below, "Pending module"). kamx-pk-cons' `routeARefinedPackedJ` is the classical-site engine;
LG00's tori need the sharp sites: with classical sites T″ fails (0.98× at L = 20; "classical fails" at T″'s
L = 18; route/cost table of the LG00-T2 handoff, `git show lg00-app:docs/campaign/handoffs/LG00-T2.md`).

**Gate (T′'s data, production form): the gate's own modules pass.** `run_tree.sh TP gate` (log `runA`,
2026-11-01 14:35–15:04 UTC): 353 modules, all passed, every process under the 4 GiB cap (largest charge 2.68 GB).
The modules prove facts about LG00's own `LG00.TP.lg00Cert` and `lg00RW` (not copies): T′'s 275 data modules and 5
shared LG00 modules (280) are reused from LG00's run18 (no rebuild), everything else is built here.
- `pkGateA` (`LG00Packed.TP.GateA`): `trFrameLOk … lg00Cert.weight pkRBook pkGMemo lg00RW.base.R.bL = true ∧
  trFrameNOk … = true ∧ trFrameTOk … = true ∧ refinedCoreS 2 lg00Cert.params lg00Cert.freqBox lg00RW = true`,
  from `pkFrameL/N/T` (T′'s packed Gram memo and rounded node memo, generated) and LG00's own
  `lg00_refinedCore` (T′'s `Final` site modules, rebuilt against this core: the certified sharp sites).
  **Gate A establishes neither `refinedTestPackedS … lg00Cert lg00RW = true` nor T′'s frame bounds
  (`FrameMajorants`).** It decides only the final frame sums (`trFrameLOk`, `trFrameNOk`, `trFrameTOk`) and
  `refinedCoreS`. The sums run on memos (`pkRBook`, `pkGMemo`, `pkRMemo`) that gate A does not verify: their
  verification is the stage conjuncts the packed frames share with `checkTorsionR` (`gramPackedCheck`,
  `gramInvRadius`, the composition, `ptEntries`, `trLayOk`, `trNormOk`, `ptPackOk`, the seven `trSt*`). Those, with
  `checkHamClaim` and `checkFrameOmega` (true by construction for `RefClaim.frame`: `bOm = freqNormUp box`), are
  left to the B3b route below, whose assembly (`refinedTestPackedS_of`, `checkFrameMajorantsR_of`) gives
  `refinedTestPackedS … lg00Cert lg00RW = true`.
- **One-ulp attacks.** For each frame bound, the test at the largest packed sum (exact mirror) decides `true` and
  one ulp (2⁻¹²⁸) below it decides `false`: `|Lᵀ|`, `|N|`, `|Nᵀ|`, `sup |T|` (8 modules, all as predicted).

| part | modules | CPU-s | kernel-s | largest charge |
|---|---:|---:|---:|---:|
| packed data (Gram memo, node memo, books; shared) | 24 | 204.7 | — | 0.76 GB |
| `FrameL` / `FrameN` / `FrameT` | 3 | 8.4 / 5.9 / 20.4 | 3.17 / 0.05 / 16.6 | 2.18 GB |
| sharp sites and `refinedCoreS` (LG00's `Final` modules) | 37 | 848.1 | — | 2.68 GB |
| `GateA` | 1 | 7.6 | 0 | 0.54 GB |
| attacks (8) | 8 | 121.0 | 69.1 | 2.36 GB |
| reused (T′ data, shared LG00 modules) | 280 | 0 | — | — |

Kernel times are the profiler's (`LG00Packed` modules only; LG00's library has no profiler), read from each
module's own log section (the receipt's ledger is recomputed so: see `gateA/NOTES.md`). `FrameT`'s kernel time is
16.6 s against 8.9 s for the first certificate's standalone probe (V2-PACKED-FRAMES), but its CPU is lower: 20.4
CPU-s against 22.1 (user 15.7 s). The profiler measures wall time, and the run shared the machine with LG00's three
workers (user anon at the 20 GB gate, 4.6 s of system time).

**AUDIT-V2-PACKED-SHARP-1: PASS WITH CHANGES** (Lean sound, axioms standard; changes to receipts and this handoff
only). F1: the receipt ledger's kernel column is recomputed from the logs by the committed parser (GateA 19.82 s →
0, the replayed imports' lines; harness versions recorded in `gateA/NOTES.md`). F2: the run window is 14:35–15:04
UTC. F3: what gate A does not establish is stated above and in `pkGateA`'s docstring (module rebuilt; statement and
proof unchanged). F4: the T″ classical-site figure now cites the LG00-T2 handoff. Nits: 280 reused modules; the
`v2-packed-prod` prerequisites of `gen_port.py` and `run_tree.sh`'s jet route are listed under (B).

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
Measured: the 279 modules of `LG00.TP.Data.Cert`'s closure (275 data, 4 shared) are reused against this branch's
core with no rebuild (`lake build --no-build LG00.TP.Data.Cert`: `All targets up-to-date (3539 jobs)`). Only the modules importing
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
| `run_tree.sh` | one torus through a route: `gate`, `b3b` (LG00's real certificate) or `jet` (the copy). |

**`LG00.JetBridge` is imported, never re-proved** (orchestrator, 2026-11-01). On LG00's real certificate the
package reuses LG00's built `LG00.JetBridge` (`lg00Ham_jet`) by hardlink: the same inode as `lg00-app`'s olean
(built 02:57), `lake build --no-build LG00.JetBridge`: `All targets up-to-date`. No solo high-memory build was run
(no exception). On the certificate copy, `gen_port.py` follows kamx-packed's `prod_cert_gen.py`: the modules it
lists in `KEEP` are imported from LG00 and neither copied nor traversed (kamx-packed owns that fix).

**Prerequisites not on this branch.** `gen_port.py` and the `jet` route of `run_tree.sh` need kamx-packed's
`scripts/packed/prod_cert_gen.py` and `jet_prod_gen.py` (branch `v2-packed-prod`, `0d5f39d9`; `gen_port.py` falls back
to `v2-packed`'s worktree copy, `run_tree.sh` takes `PROD_GEN`/`JET_PROD_GEN`), and the `jet` route's Lean needs
`v2-packed-prod`'s `JetKeyed`/`JetCheck` and `v2-packed-cons`' consumers in the core, plus `RouteSharpJ.lean`
(on `v2-packed-gen-int` only: this branch carries no Lean that needs unlanded APIs).

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

**The jet route for T′, emitted** (`gen_packed.py --prefix LG00P --stages jet --jet-low … --jet-full …`, on
kamx-packed's T′ mirror caches `.lake/v2-packed-prod/tp/{low,full}_mirror.pkl` of `v2-packed`, read only):
103 modules plus the shared format, every one under the line caps. Book agreement: Low 392 bits (jet) = 392
(torsion), Full 400 bits; `bLow = bFull = 2^140`; `pkIBook` = Full box (half-width 48, stride 193, width 400),
`lI = 273`, `normOk` asserted by the generator. The generator mirrors the consumers' tests before emitting (`gen_cert.inv_energy`): the four `ivRowOk` values are
1.25415, 7.19172, 0.146282, 0.0820981 (×10⁻¹⁶) against `err = 7.2·10⁻¹⁶`, just below the landed `checkInvariance`
rows of T′'s generator (1.25427, 7.19210, 0.146446, 0.0824246 ×10⁻¹⁶; margin 8.3·10⁻¹⁹ against the landed
7.9·10⁻¹⁹), and `enOk` 5.7·10⁻²³ (landed 3.5·10⁻²¹). Row 1 is tight by construction: the generator sets `err` just
above the torus's defect. Not built: it needs the two branches' Lean in the core and
kamx-packed's chain modules in the package (stage C). The emitted names follow V2-PACKED-PROD-API §3
(`LG00P.TP.Jet.<C>.ChainCert`: `jdLow`, `bLow`, `jetLow_check_cert`, …); if kamx-packed renames them, only
`emit_j`'s import and name strings change.

**The jet route compiled for T′ (integration, log `runJ`, 2026-11-01 16:43–18:00 UTC).** On the local branch
`v2-packed-gen-int` (this branch + `v2-packed-cons` `4b2cf9af` + `v2-packed-prod` `0bb4def23`; never landed), in a
scratch package mirroring kamx-packed's `kam-lg00p` (same name, library and options), so their built modules are
reused read-only by hardlink: the certificate copy, `LG00P.JetBridge`, and both chains with their theorems
(`jetLow_check_cert`, `jetFull_check_cert`; 307 chain modules, all up to date). Proved, standard axioms:
`pkCheckTorsionJ` (`checkTorsionJ … jdLowW lg00Cert`), `pkFramesJ` (`checkFrameMajorantsRJ` at the claims),
`pkCheckInvJ` (`checkInvarianceJ … jdFullW`, all four rows, the tight row 1 included), `pkCheckEnJ`, `pkLowOk`,
`pkFullOk`, `pkFrontLowOk`.

| part | built | reused | CPU-s | peak |
|---|---:|---:|---:|---:|
| packed data (books, memos, `pkIBook`, fronts, `pkHamJet`) | 31 | 0 | 177.4 | 0.65 GB |
| front checks (25 lookups, five per module) and assemblies | 7 | 0 | 78.0 | 1.22 GB |
| Gram (B2) | 10 | 0 | 76.3 | 2.01 GB |
| torsion on the jet: 16 `D²K`, guards, 6 stages, 8 + 8 entries, `T`, `Y`, final, `jetLowOk` | 46 | 0 | 423.6 | 2.77 GB |
| torsion core assembly (`torsRCoreJ_of`) | 1 | 0 | 166.0 | 2.84 GB |
| `checkTorsionJ` assembly | 1 | 0 | 400.9 | 3.06 GB |
| frames on the jet's torsion | 4 | 0 | 44.8 | 2.21 GB |
| invariance on the jet (guard, 4 rows, `jetFullOk`, assembly) | 7 | 0 | 76.5 | 1.23 GB |
| energy on the jet | 2 | 0 | 12.5 | 0.68 GB |
| ported chain-free LG00 proof (static, embedding, disc-pass parts, sites, frequency, confinement, identity) | 68 | 14 | 653.7 | 3.02 GB |
| ported Hamiltonian balls | 64 | 0 | 360.2 | 1.74 GB |
| kamx-packed's certificate copy and chains | 0 | 311 | 0 | — |
| **total** | **241** | **325** | **2,470.0** | **3.06 GB** |

**Not built: `LG00P.TP.Balls.T38`** (the ported ball module of the disc pass; LG00's own run charged 6.00 GB for it,
killed here at the 4 GB cap in three attempts), and its 22 dependants: `Balls.HamBounds`, `Final.HamClaim` and their
parts, hence `Asm.BaseJ` (`jetBase`), `Asm.EngineJ`, `Asm.CheckJ`, `MainJ`. Everything else of the jet route is
built. Two ways out (owner's/orchestrator's choice): one solo build of `T38` at 7.5 GB under the JetBridge exception
rules; or the copy imports LG00's `Ham` (kamx-packed's `KEEP`), so `checkHamBounds` and `checkHamClaim` of the copy
transfer from LG00's own `lg00_hamBounds`, `lg00_hamClaim` by `rfl` (same fields) instead of being re-proved: this
also saves the ported balls' 360 CPU-s and the disc pass.

**Missing from kamx-packed: nothing on the chains.** Both chain theorems are built and plug into the consumers
(`pkLowOk`, `pkFullOk`). Open items for the owners:
- **Do not state the consumers at `lg00Cert.ham.jet`.** Reading the certificate's jet makes the kernel compile the
  Hamiltonian's jet (`lg00Ham_jet`'s cost): every `X_N` entry was killed at 4 GB (eight, three attempts) until the
  stages were stated at the literal `lg00Jet` and the assemblies rewrote with `lg00Ham_jet` (`pkHamJet`). Then
  `X_N` entries take 1.4 GB, as on the landed-model route.
- **`JetFront.lean`** (on `v2-packed-gen-int`; text in `pending/`): `jd.withFront front` puts a chain's wanted
  nodes (its own `JLed` constants, by name) in front of its ledger; `jetCheck_withFront` moves the chain theorem
  across, given one checked lookup per front entry (`frontOk`, 25 lookups, ≤ 0.54 GB). It bounds every consumer
  lookup by 20 or 5 entries (AUDIT/CONS L2). Whether it is necessary is unmeasured: it did not by itself fix the
  `X_N` entries (the cause was the jet above).
- **Two slow assemblies:** `TorsJ.Core` (166 CPU-s) and `TorsJ` (401 CPU-s), against 4.3 and 7.3 s for the same
  assemblies on the landed-model route. Proof terms are the same lemma applications; something in the unification
  of `jetSlots jdLowW` or the rewrite unfolds a large definition. Under the cap; to profile.

**T″ the same way.** `gen_cert.py …/LG00/TPP` (no change to any script): T″'s own parameters, box
(`s = 886058956738442102019008342433694847/886058070680308099785085113265000000`), zero modes and claims are read
from its tree. The B3b mirror passes (torsion margin 0.00118) and the frames at T″'s claims: `|Lᵀ|` 1.3513 / 1.36,
`|N|` 1.1961 / 1.2, `|Nᵀ|` 1.4334 / 1.44, `sup |T|` 115.68 / 116.

**The B2 and B3b stages of T′ in production form (built, log `runB`).** On LG00's real `lg00Cert`, with the shared
data modules: `pkCheckGram : checkGramPacked pkGBook pkGMemo lg00Cert = true`, `pkTorsEntries : ptEntries … = true`
(36 entries), `pkTorsCore : torsRCore … = true` (13 parts; `DN`, `X_N` entry by entry): 389 modules pass (304
reused), every process ≤ 2.81 GB.

| stage | modules built | CPU-s | kernel-s |
|---|---:|---:|---:|
| shared data (Gram memo, node memo, books; from `runA`) | 24 | 204.7 | — |
| jet slot models of the torsion (`pkTMs`, copied from the tree) | 10 | 119.0 | 0.4 |
| Gram (B2): 8 entries, core, assembly | 10 | 157.8 | 113.7 |
| torsion (B3b): 36 entries, guards, stages, averages, final test, assembly | 66 | 751.7 | 453.3 |
| **total** | **110** | **1,233.2** | **567.4** |

Against the landed Gram and Torsion stages of the first certificate (726 modules, 13,551 CPU-s, run20e): ≈ 11×, now
with the production assembly (shared data, the `_of` assembly theorems) measured rather than estimated; the B3b
gate's 64 probes took 1,292 CPU-s for the torsion alone, mostly data elaboration per probe. CPU of failed first
attempts (generator bugs, fixed: below) is not counted. Remaining for the B3b route: the assembly through the
tree's `Low` chain (`pkComposeLow`, `pkCheckTorsion`, `pkFrames`, `pkEngine`, `pkBase`, `pk_check`, `pk_kamTorus`),
emitted; it runs when LG00's run18 has finished T′'s `Low` chain (2,062 / 2,484 at 15:38 UTC).

**The B3b route end to end on LG00's real T′ certificate: PROVED** (logs `runC`, `runD`, 2026-11-01 16:43–17:23 UTC,
after run18 finished T′'s `Low` chain). `LG00Packed.TP.Main` proves `pk_kamTorus` (LG00's `lg00_kamTorus`
statement, verbatim) and `pk_kamTorusStatement` (`LG00TorusStatement lg00Cert lg00OmegaStar lg00WindowTP`) from
`pk_check : checkV2With (torsRBase …) (routeARefinedPackedS …) lg00Cert lg00RW = true`, through
`checkV2With_packedS_sound`: `pkCheckGram`, `pkCheckTorsion` (with the tree's landed `cfgLow` composition,
`pkComposeLow`), `pkFrames`, `pkEngine` (`lg00_hamClaim`, the packed frames, `lg00_refinedCore`), `pkBase` (the
tree's landed static, Hamiltonian, embedding, invariance and energy facts). 4,695 modules pass, every process
≤ 2.81 GB.

| part | modules built | CPU-s | largest charge |
|---|---:|---:|---:|
| packed data (shared) | 34 | 323.7 | 1.02 GB |
| B2 Gram stage | 10 | 157.8 | 2.08 GB |
| B3b torsion stage | 66 | 751.7 | 2.81 GB |
| packed frame tests (from the A gate) | 3 | 34.7 | 2.18 GB |
| assembly (`Compose`, `Tors`, `Frames`, `Engine`, `Base`, `Check`) and `Main` | 7 | 61.2 | 2.08 GB |
| LG00's landed inputs not yet built by run18 (disc pass, confinement checks, identity, `Final.Freq` patched) | 16 | 104.7 | 1.90 GB |
| LG00's sharp sites and witness (rebuilt against this core, in the A gate) | 37 | 848.1 | 2.68 GB |
| reused from LG00's run18 (data, balls, Full and Low chains, static, embedding, invariance) | 4,519 | 0 | — |

The packed part (data, Gram, torsion, frames, assembly) is 1,329 CPU-s. It replaces LG00's landed Gram, Torsion,
frame and `Final.Torsion`/`Final.Frames` modules for T′ (run18 is building them now; on the first certificate
they cost 14,138 CPU-s, V2-PACKED-FRAMES). This route keeps the landed `Low` and `Full` chains; the jet route
replaces them.

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

- **Targeted builds** (`nice -n 5 systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 lake build …`):
  `✔ Built KAM.CertificateSharp.Packed.RouteSharp (1.0s)`, `✔ Built KAM.CertificateSharp.Packed.TorsRAsm (3.8s)`,
  `Build completed successfully`; no warning in `Packed/`. (They rebuilt `V2/SiteSign`, `V2/SiteShard`,
  `Packed/Frames`, `V2/RouteARefinedS`: stale in the seeded build, unchanged sources.)
- **Integration** (`v2-packed-gen-int`: this branch + `v2-packed-prod` `0d5f39d9` + `v2-packed-cons` `75deebd9`, both
  merges clean): their modules and `RouteSharpJ` built one at a time, `✔ Built
  KAM.CertificateSharp.Packed.RouteSharpJ (7.6s)`. My first draft re-declared `torsRCoreJ_of` (kamx-pk-cons has it,
  same arguments); removed.
- **`#print axioms`**, each `[propext, Classical.choice, Quot.sound]`: `routeARefinedPackedS`, `routeV2AllPackedS`,
  `routeARefinedSWith`, `checkV2With_packedS_sound`, `checkV2With_routeV2AllPackedS_sound`,
  `checkV2With_routeARefinedSWith_sound`, `refinedTestPackedS_of`, `refinedTestPackedS_ofPacked`, `framesR`,
  `FrameChecker.facts`; on the integration branch `routeARefinedPackedSJ`, `checkV2With_jetSharp_sound`,
  `checkV2With_jetSharp_of`, `refinedTestPackedSJ_of`, `ptD2All_of`, `framesRJ`.
- **`scripts/lint_sources.sh`**: `check_lean_modules: PASS (4411 Lean files, 0 comparator configurations)`, the 25
  tests `OK`, `FROZEN-ANCHOR GUARD OK`; only the ABI step fails, as in every worktree so far (`object file
  …/KAM/Frozen/Planetary/Spatial/Defs/AngularMomentum3.olean` not built here). `gen_root_imports.py --check`: exit 0.
- **Additivity:** against `origin/main` the only changes under `KAM/` are the new `Packed/RouteSharp.lean` (208 lines),
  `Packed/TorsRAsm.lean` (73 lines) and the generated `KAM/Root/CertificateSharp.lean`. No forbidden token, no
  `set_option`, no line over 100 characters. Nothing under `lg00-*`, `applications/`, `KAM/Frozen`, `manifest/`
  changed; `lg00-app`'s files are read only (sources copied, artifacts hardlinked read-only or copied).
- **Generator regression:** `gen_cert.py --check-legacy` reproduces V2-PACKED-FRAMES' frame edges of the first
  certificate bit for bit (`LEGACY OK`).
- **Emitted modules:** every one asserted ≤ 100 characters per line and ≤ 1,500 lines by the emitter; they are
  modules (copyright, `module`, `public import`, docstring, `@[expose] public noncomputable section`).

## Owner questions (overnight mode: none blocked the work)

1. **Where the packed LG00 modules live.** Now: a scratch Lake package (`<core>/.lake/lg00-packed`, never committed),
   which reuses LG00's built modules read-only. The brief's alternative, `applications/lg00/LG00/Packed/` on
   `lg00-app`, needs the orchestrator's approval (not asked to write there). The generators work for either:
   only `gen_pkg.py`'s package root changes.
2. **Which certificate the production theorem is about.** The jet route certifies kamx-packed's certificate COPY
   (`LG00P.TP.lg00Cert`: LG00's certificate without advice and witnesses, which `CertifiedTorus` does not read).
   `pk_kamTorus` is therefore `lg00_kamTorus`'s statement about the copy, not about `LG00.TP.lg00Cert`. A transfer
   lemma (same `params`, `ham`, `weightH`, `centre`, `radius`, `emb` ⇒ same `CertifiedTorus`) would restate it at
   LG00's certificate in one environment that imports both. Owner's choice.
3. **The B3b route as a deliverable.** It replaces only LG00's Gram, Torsion and frame stages (the landed `Low` and
   `Full` chains stay); it is the end-to-end validation of the assembly on LG00's real certificate, not the
   production route.

## Suspected errata and deviations

- **Defect in LG00's generated `LG00.TP.Final.Freq` (and `LG00.TPP.Final.Freq`), on `lg00-app` (untracked, generated
  03:37).** Line 23, `open KAM KAM.Certificate LG00 LG00.Confinement KAM.CertificateSharp.V2`: the module's import
  closure (532 modules: `LG00.TP.Data.Cert`, `LG00.Model`, `LG00.Window`, `LG00.Confinement.Main`) contains no
  `KAM.CertificateSharp.V2` module, so the `open` fails (`unknown namespace KAM.CertificateSharp.V2`) and with it
  every later name (`FreqEncloses`, `IsDiophantine`, `lg00WindowTP`): 6 errors. The closure is byte-identical to
  `lg00-app`'s (checked file by file), so **LG00's run18 will fail the same way at `TP.Final.Freq` and hence
  `TP.Main`** (it has not built them yet). Fix, verified here (`✔ Built LG00.TP.Final.Freq`): add
  `public import KAM.CertificateSharp.V2.RouteARefinedS` after `public import LG00.Confinement.Main` (or drop
  `KAM.CertificateSharp.V2` from the `open`). `gen_pkg.py` applies this to its copies only (`PATCHES`).
- **Deviations:** none in the core. The packed modules live in a scratch package, not on `lg00-app`.
