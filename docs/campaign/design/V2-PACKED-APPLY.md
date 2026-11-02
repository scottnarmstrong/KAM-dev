# V2-PACKED-APPLY: running the packed route on a new certificate application

For the magnetic pilot (`mag-pilot`, `certificates/magnetic`) and later certificates (the lunar band and lock). This
note says what an application must provide to run the packed jet route, and what the generators still fix to LG00.
The entry point is `scripts/packed/apply_packed.py`: a thin driver over the existing emitters. It changes no Lean and
no emitter, and it reproduces LG00's packed sources byte for byte (§9).

Sources: `V2-PACKED.md` §12–14, `V2-PACKED-PROD-API.md`, and the handoffs `V2-PACKED-PROD`, `V2-PACKED-GEN`,
`V2-PACKED-CONS`, `LG00-RELEASE` (`lg00-release`) and `V2-PACKED-FIXEDCOST` (`v2-packed-group`).

## 1. The route, and who provides what

| part | where | provided by |
|---|---|---|
| packed jet API, consumers, engines (`JetKeyed`, `JetCheck`, `JetCons*`, `JetBase`, `RouteSharp`, `RouteSharpJ`, `JetFront`, `CertCongr`) | core, `KAM/CertificateSharp/Packed/` (landed `617c5ddb`) | nobody: generic |
| the certificate, its Hamiltonian, its jet program literal and jet bridge, its chain-free proofs (static, balls, embedding, disc pass, sites, frequency), its chart and statement | the application's Lake package (`applications/<name>`) | **the application** (§2–§5) |
| the jet chains (Low, Full) | generated (`jet_prod_gen.py`) | the driver, from the app's generator state (§4) |
| the packed modules `<root>.**` (Gram, torsion and frames on the jet, invariance, energy, assembly, `pk_kamTorus`) | generated (`gen_packed.py --stages jet`) | the driver |
| the build | `run_packed.py` (one Lean process at a time) | the driver's caller (§7) |

**Two layouts.**
- **`own` (recommended):** the packed modules are emitted at the application's own constants, under
  `<NS>.<T>.PK`, beside its certificate. The app's `Main` proves its statement `:= pk_kamTorus`. This is the
  LG00 release's design B′ (`lg00-release`): no copy, no bridge.
- **`copy`:** the packed modules are emitted on a copy of the certificate without advice and witnesses,
  `<P>.<T>.Data.Cert`, built with `prod_cert_gen.py`. The chain-free proof is ported onto the copy (`gen_port.py`).
  The app's statement then needs a bridge: kamx-pk-cons's `LG00B`, definitional, `:= <P>.<T>.pk_kamTorus`. This is
  how LG00's T′ and T″ were first proved.

**The pipeline** (each step one Python process under 8 GB; `apply_packed.py` steps in brackets):

```
generator state ─[extract] jet_extract_low.py → low.json, full.json
               ─[mirror]  jet_low_gen.py --mirror-only → low_mirror.pkl, full_mirror.pkl
certificate tree ─[cert]  prod_cert_gen.py   (copy only)
               ─[port]    gen_port.py        (copy only)
mirrors ───────[chains]   jet_prod_gen.py --stage=Low, --stage=Full → <P>.<T>.Jet.{Low,Full}.**
tree + mirrors ─[packed]  gen_packed.py --stages jet → <root>.** and modules_<T>.json
                          then run_packed.py (Lean, 4 GB, serial)
```

## 2. The certificate dump

**The emitters read Lean text, not JSON.** The certificate dump they read is an LG00-format certificate tree: the
Lean files that LG00's generator writes (`lg00-app`, `applications/lg00/LG00/<T>`). `gen_cert.Cert` parses them.
The application emits them from its own certificate, for instance the sofx JSON `mag_cert.json`. LG00's emitters
are `lg00-app`'s `scripts/sjs/lg00cert/lg00_emit_{cert,data,jet,final,main}.py`, run on the generator state of
`lg00_cert_gen.py`.

| file (under the tree `<pkg>/<NS>/<T>/`) | read | what |
|---|---|---|
| `Data/Cert.lean` | `gen_cert.Cert`, `prod_cert_gen` | `namespace <NS>.<T>`. `lg00Params` (one `k := v` per line), `lg00Box` (the frequency box: a list of pairs), `lg00Cert` (`weight := ⟨ρ, lgD<i>⟩`, `cfgLow := <name>`, whose `cutoff`, `taylorN`, `halvings` are integers), `lg00Emb` (`angleDeg`, `actionDeg`, zero modes `⟨⟨k⟩, lg00Angle<j>_0⟩`), `lg00Pi` (`⟨⟨a⟩, ⟨b⟩, c, d⟩`), `lg00GramInv`, `lg00TorsInv` |
| `Data/DCoeffs.lean` | the reader | the long rationals `def lgD<i> : ℚ := ((a : ℤ) : ℚ) / ((b : ℕ) : ℚ)` |
| `Data/E0.lean`, `Data/W8.lean` | the reader | the embedding's components `lg00Angle<j>_0`, `lg00Action<j>_0`; the Gram witness `lg00Gram<ij>_0` |
| `Final/Wit.lean` | the reader (claims) | `lg00RW : RefinedWitS`, whose `R` holds the claimed frame bounds `bL`, `bN`, `bNt`, `bT` |
| `Main.lean` | `gen_packed` (statement) | `lg00_kamTorus`, and `lg00_kamTorusStatement : … := ⟨lg00_kamTorus.1, lg00_kamTorus.2.2⟩`, copied verbatim into `MainJ`. The frequency name is read from `(lg00_certifiedTorus_iff lg00Cert <ω>).mp` |
| `../Jet.lean` (the package's) | `gen_cert.ham_jet` | the jet literal `lg00Jet : HamJet`: `v0 := i`, `d1 := [...]`, `d2 := [[...], ...]` (§4) |
| `Torsion/{D0,V*}.lean` | non-jet stages only | the landed `cfgLow` composition's 20 slot models (the B3b route); the jet route does not read them |

Rationals are written `(a / b : ℚ)`, `(-a / b : ℚ)`, as an integer, or as `lgD<i>`. Mantissas are at scale 2¹²⁸
(`P = 128`).

`apply_packed.py` checks every file and definition of this table before any emitter runs. It fails closed, naming
the missing item. It also checks the namespace, the jet bridge's file (`../JetBridge.lean`, defining `lg00Ham_jet`)
and the files of the §5 modules that the assembly imports.

## 3. The application config

One JSON file per torus. The LG00 instances are `scripts/packed/apply/lg00_{tp,tpp}_{copy,own}.json`.

| key | meaning |
|---|---|
| `application`, `tree` | display name; the tree `<T>` (LG00: `TP`, `TPP`) |
| `dump.tree`, `dump.package` | the certificate tree (§2) and the application's package root (where `<NS>/Jet.lean`, `JetBridge.lean` and the chain-free proofs live) |
| `names` | the Lean names of §2 and §4–5 the emitters read and write: `namespace`, `params`, `box`, `cert`, `emb`, `pi`, `gram_inv`, `tors_inv`, `witness`, `jet`, `jet_bridge`, `field`, `statement`. Checked against the names the emitters use (§6), so a mismatch fails before any emitter runs |
| `layout` | `{"kind": "own", "prefix": <NS>, "pk_root": "<NS>.{T}.PK", "pk_format": "<NS>.PKFormat"}` or `{"kind": "copy", "prefix": <P>}` |
| `ham` | `ported` (`gen_packed --ham-ported`): the packed assembly reads the Hamiltonian bounds and disc pass of the tree it is emitted on. In `own` they are the app's own. In `copy` the port proves them on the copy (`gen_port --ham-port`). Otherwise (`copy` only) the app's are imported and carried over by `CertCongr`, and the app's advice comes into the closure with them (§8) |
| `asm_suffix` | the suffix of the assembly modules (`MainJ<s>`; LG00 T′ copy: `H`, beside an older assembly) |
| `port.split_balls` | the ball chunks to split at their stored halves (LG00: `[38]`, a 6 GB chunk) |
| `jet` | `low_mirror`, `full_mirror` (the caches `packed` reads); `state`, `tooling` (the generator state and the package whose classes unpickle it, for `extract`); `chains.{Low,Full}.{json, mirror, cut}` (the cut options of `jet_prod_gen.py`, §4); `box_low`, `box_full` (documentation only: fixed today, §6) |
| `steps` | a subset of `extract, mirror, cert, port, chains, packed`, run in this order |
| `caps` | documentation of the caps the run assumes (§7) |

Usage: `python3 -I scripts/packed/apply_packed.py CONFIG --out=DIR [--steps=…] [--check=REF] [--dry-run]`.

**Writes.**
- Only into `--out`, and only when `--out` is new or an earlier output of the script. It refuses a non-empty
  directory without `apply_<T>.json`, so it never writes into a reference or another worker's package.
- `extract` and `mirror` refuse to overwrite an existing file.
- `OUT/apply_<T>.json` records every command with its exit code, and the SHA-256 and size of every emitted file.
- `--check=REF` compares every emitted file with `REF`'s file at the same path, byte for byte, and compares the
  module lists.

## 4. The jet program literal, the jet bridge and the chains

**What the application provides.**
- **`<NS>.lg00Jet : HamJet`:** the compiled jet program of its Hamiltonian, as a literal (`LG00/Jet.lean`, with its
  ops in `JetOps0..6`), with the slots `v0`, `d1`, `d2`.
- **`<NS>.lg00Ham_jet : lg00Ham.jet = lg00Jet`:** the jet bridge, `HamJet.eq_of_segBeq (by decide +kernel)`,
  built once in the application. LG00's took 39 CPU-s and 6.07 GB: the one standing memory exception (§7).
- **Its generator state:** the pickled sofx state, read by `jet_extract_low.py` with the application's tooling on
  the path, giving the chain programs, live slots and leaves.

For the magnetic pilot: the jet program is the compile of `magHamExpr` (`adv_jet.jet(2, sofx_mag.mag_ham_expr())`,
`certificates/magnetic/README.md`), with four character ops.

**The chains** (`jet_prod_gen.py`, from the mirrors):

| chain | box half-width | cut options used for LG00 (`V2-PACKED-PROD`) | LG00 T′ |
|---|---|---|---|
| Low (`cfgLow`, the torsion's slots) | 25 (the torsion box; `gen_packed` asserts the widths agree) | `--seg-io=40 --led-nodes=40` (Low's default `--heavy=34`) | 110 modules, 1,467 CPU-s, 3.76 GB peak |
| Full (`cfgFull`, `v0` and `d1`) | 48 | `--seg-io=13 --led-nodes=40` (Full's defaults `--heavy=8 --char-keys=2 --char-io=12 --act=4 --taylor=3 --pows=2`) | 197 modules, 2,648 CPU-s, 3.55 GB peak |

The chain theorems are stated at the certificate's fields (`lg00Cert.cfgLow`, `.emb`, `.weight`, `.piEnc`) and at
the jet literal `lg00Jet.prog`. The `_cert` corollaries rewrite to `lg00Cert.ham.jet` through the bridge, once.

## 5. The chart, the chain-free proofs and the statement

The packed assembly (`gen_packed.py`'s `Asm.*`, `MainJ`) imports these modules and calls these lemmas of the
application (names relative to `<NS>.<T>` or `<NS>`):

| role | module | lemma |
|---|---|---|
| static check | `Final.Static` | `lg00_checkStatic` |
| Hamiltonian bounds | `Balls.HamBounds` | `lg00_hamBounds` |
| embedding check | `Final.Embedding` | `lg00_checkEmbedding` |
| disc pass | `Final.HamClaim` | `lg00_hamClaim` |
| certified sharp sites | `Final.RefinedCore` | `lg00_refinedCore` (`refinedCoreS … = true`) |
| frequency | `Final.Freq` | `lg00_freqEncloses`, `lg00_diophantine` |
| chart (the Hamiltonian in physical coordinates) | `<NS>.Physical.HamIdentity` | `lg00Ham_identity` |
| model and window | `<NS>.Model`, `<NS>.Window`, `<NS>.Confinement.*` | `lg00_certifiedTorus_iff`, `lg00_window` |
| statement | `<T>/Main.lean` | `lg00_kamTorus`, `lg00_kamTorusStatement` |

**The statement's shape.** `MainJ` proves the statement of `Main.lean`, copied verbatim, with LG00's proof script:
- `refine ⟨lg00Ham_identity, by decide +kernel, ?_⟩`;
- `(lg00_certifiedTorus_iff lg00Cert ω).mp (checkV2With_jetSharp_sound … pk_checkJ lg00_freqEncloses
  lg00_diophantine)`;
- `lg00_window h.2.2.2.2.2.2.2.2.2.2`.

The statement must therefore be: a Hamiltonian identity, a decidable energy fact, and `∃ K∞ s∞, TorusWith … ∧
window`. An application with another headline, such as the magnetic barrier `KAM.Magnetic.magnetic_barrier`, takes
the generic part up to `Asm.CheckJ`, which gives `pk_checkJ : checkV2With … = true` and with it `CertifiedTorus`
(`checkV2With_jetSharp_sound`). It writes its own `Main`, as LG00's release did.

## 6. What the emitters still fix to LG00 (the parameterization still to do)

Today an application's dump must use LG00's names, in its own namespace `<NS>.<T>`. The driver states them as
`EMITTER_NAMES` and fails closed on any other. A parameterized emitter must take the following:

| fixed today | where |
|---|---|
| the names of §2, §4 and §5: about 230 literal occurrences in `gen_packed.py` (`lg00Cert` 75, `LGF` 23, `lg00RW` 21, `lg00Jet` 6, `lg00Ham_jet` 5, the lemmas of §5, …) | `gen_packed.py`'s templates; the regexes of `gen_cert.py` |
| the namespace `LG00.<T>` | `gen_packed.main` (`assert cert.ns == "LG00.%s"`); the renaming `LG00` → `<P>` of `prod_cert_gen` and `gen_port` |
| the box half-widths 25 (Low, the torsion's) and 48 (Full) | `gen_cert.compute`, `compute_j`, `inv_energy`; `gen_packed` (`jet_nodes(…, 48)`, `i_book`); `jet_extract_low.STAGES` |
| the scale `P = 128` and the dimension `n = 2` | constants of `gen_cert`, `gen_packed`, `jet_extract_low` |
| the four frame claims `bL`, `bN`, `bNt`, `bT`; the 20 torsion slot models | `gen_cert.claims`, `emit_tms` |
| the certified **sharp** sites (`refinedCoreS`, `routeARefinedPackedSJ`) | the jet assembly |
| the statement template (§5) | `emit_j`'s `MainJ`, `stmt_form` |
| the docstrings (`# LG00 <T> packed: …`, `from LG00/<T>`) | `Emit.write` (text only) |

**The magnetic pilot meets three of these at once:**
- its names are `mag*`;
- its route is A refined with **classical** sites (`certificates/magnetic/README.md`). The core's classical-site
  jet engine is `routeARefinedPackedJ` (`JetConsFrames.lean`), with `checkV2With_jetBasePackedJ_sound`, but the
  emitter's jet assembly uses only the sharp form;
- its headline is a barrier theorem, not LG00's torus statement.

So the next step for the pilot is a parameterized `gen_packed` (a `names` table passed to `Emit`, the box
half-widths as options, a classical/sharp switch, the assembly ending at `Asm.CheckJ`), checked by the same
byte-identity test on LG00 (§9) before its first magnetic emission.

## 7. Memory and cost caps

- **Lean:** one process at a time, `nice -n 5`, `systemd-run --user --scope -p MemoryMax=4G -p MemorySwapMax=0`,
  `LEAN_NUM_THREADS=1`, started only while the user's anonymous memory is under 20 GB (`run_packed.py`,
  `cons_perf_run.sh`). lemma.farm kills processes above 10 GB.
- **Exceptions** are named rulings, never defaults. LG00's only one is `LG00.JetBridge` at `MemoryMax=7152M`,
  alone, while anon is under 12 GB (6.07 GB measured).
- **Python:** 8 GB (`py_capped.sh`). Measured here (§9) for T′'s `cert`, `port` and `packed` together, the
  mirrors read and the torsion recomputed: 78 s wall, 76.5 CPU-s, largest process 1.29 GB. The mirrors themselves
  took 19 min (Low) and 60 min (Full) for LG00 T′.
- **Known hot spots:**
  - a ball chunk above 4 GB is split at its stored halves (`--split-balls`; LG00's `T38`: 6 GB → 2.9 + 3.6 GB);
  - the heaviest Low block (31 heavy steps) reached 4.7–4.9 GB RSS under the 4 GB charge cap;
  - unfolding a Boolean check of a certificate (`checkHamBounds c = true := …` by `rfl`) makes the kernel run it:
    killed at 4 GB. Use the congruence lemmas `checkHamBounds_congr` and `checkHamClaim_congr` (`CertCongr`).
- **Failure accounting.** `/usr/bin/time` reports exit 0 for a process killed by a signal, so the runners record
  an OOM kill or a signal as a failure. `lake build <M>` also rebuilds every stale dependency inside the same
  process: run `lake build --no-build` first (V2-PACKED-CONS-PERF).
- **Cost to expect (LG00 T′, measured):**
  - the whole jet route: 592 modules, 6,370 CPU-s, against run18's 107,577 (16.9×);
  - of which, roughly: chains 4,115, packed modules 800, chain-free proofs 700, data 295; the balls and the shared
    modules make up the rest.
  - A module's fixed cost is 4.0–5.3 CPU-s (V2-PACKED-FIXEDCOST).

## 8. Lessons (rules for a new application)

1. **State the consumers at the jet literal.** Every packed stage reads `lg00Jet.prog`, never `c.ham.jet`. Reading
   `lg00Cert.ham.jet` makes the kernel compile the Hamiltonian's jet in every module: LG00's jet-route `X_N` entries
   were all killed at 4 GB that way, until `931260a4e`. The assembly rewrites with the jet bridge once
   (`pkHamJet`).
2. **Reuse the application's jet bridge.** `<NS>.JetBridge` is the heaviest single module (LG00's: 6.07 GB). It is
   built once in the application and imported (orchestrator, 2026-11-01). In the `own` layout the packed modules
   import it directly. The `copy` layout copies it with the certificate (`LG00P.JetBridge`, one of the copy's 19
   modules) and proves it again: `gen_port` would import LG00's own modules named in a `KEEP` list of
   `prod_cert_gen.py`, but `main`'s has none. One more reason for `own`.
3. **Groups.** Put several block theorems in one module, elaborated sequentially (`set_option Elab.async false`).
   Without that, the merged module ran out of memory at 4 GB. Each module removed saves 5.3–5.6 CPU-s of fixed
   cost, projected at 870–1,160 CPU-s per torus (22–29 %) with up to 8 blocks a module (V2-PACKED-FIXEDCOST,
   `v2-packed-group`).
   `jet_prod_gen.py` on `main` emits one block per module. Grouping is kamx-packed's current work and is not yet
   a driver option.
4. **Emit at the application's own constants** (`own`). The `copy` layout needs a second certificate, the port of
   the chain-free proof (≈ 170 modules and 1,300 CPU-s per torus) and a bridge.
5. **Keep the advice out of the closure.** The packed route never reads `cfgLow`/`cfgFull` advice or `wit`. But any
   import of the full certificate brings the advice with it: it was 90 % of LG00 T′'s Data stage (3,295 of 3,378
   CPU-s; V2-PACKED-CONS-DATA). An advice-free certificate is an owner decision: deferred for LG00.
6. **State block theorems at named constants.** Do not state them at projections of one large data literal, or at
   fields that compute nodes: every block's kernel check would unfold and recompute them. This is the same mechanism
   as lesson 1, raised for the Taylor × Fourier layer's `PairData` (PREVIEW-PACKEDTF-1 K3: a review finding, not
   yet measured).
7. **Mirror first.** Every emitted Boolean is run in the bit-exact Python mirror before any Lean process starts.
   `gen_packed` asserts the frame verdicts, invariance, energy and layout widths, and stops otherwise.
8. **Pin the generated text.** Generated sources are not committed (LG00: 772 MB). They are pinned by SHA-256
   (`apply_<T>.json`, the release's `RELEASE_MANIFEST.tsv`) and must regenerate byte for byte (§9).

## 9. The test: LG00's packed sources regenerated byte for byte

Receipts: `docs/campaign/studies/V2-PACKED-APPLY/` (2026-11-02, 02:51–02:57 UTC). No cache was reused; no Lean ran.

**Inputs (read only):**
- LG00's trees (`lg00-app`, `applications/lg00/LG00/{TP,TPP}`);
- kamx-packed's mirrors (`v2-packed/.lake/v2-packed-prod/{tp,tpp}/{low,full}_mirror.pkl`).

| layout | steps | reference | T′ files | T″ files | different |
|---|---|---|---:|---:|---:|
| `copy` | `cert`, `port`, `packed` | the integration package that proved T′ and T″ (`v2-packed-gen-int/.lake/lg00p`) | 286 | 286 | **0** |
| `own` | `packed` | the LG00 release package (`lg00-release`, `applications/lg00`, `LG00.<T>.PK`) | 115 | 115 | **0** |

- **The lists and records match too.** The module lists, the port's lists, and `gen_packed`'s records (claims,
  edges, torsion margin, invariance and energy) are equal to the references'.
- **The tori are emitted in the references' order, T′ then T″.** The shared `<P>.PKFormat`'s docstring names the
  tree emitted last.
- **`--pk-root` is cherry-picked.** It is `v2-packed-gen` `59ea55407` (5 lines; the release's emitter).
- **Fail-closed checks:** 8 cases, among them the magnetic example config and the release package as `--out`.
  Each stops before writing.

**Not tested byte for byte: the chains.** The measured T′ chains were made by an older `jet_prod_gen.py` and then
patched (`V2-PACKED-PROD`: "not the measured files byte for byte"), and kamx-packed is regenerating T″'s chains as
groups now. The `chains`, `extract` and `mirror` steps are wired and dry-run only.
