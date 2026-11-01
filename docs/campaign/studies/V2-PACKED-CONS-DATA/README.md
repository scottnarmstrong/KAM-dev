# V2-PACKED-CONS-DATA: the Data stage of the packed whole-torus route (LG00 T′)

**The question.** In kamx-pk-gen's whole-torus table (V2-PACKED-GEN handoff, `0191598d`), the Data stage is the
packed jet route's largest cost: 326 modules, 3,673 CPU-s, 36 % of 10,207 CPU-s.

## 1. Where the 3,673 CPU-s go

The Data row of `MainJ`'s import closure, attributed as `run_compare.py` does (run18 for LG00's own modules; runJ and
kamx-packed's summaries for the rest):

| group | modules | CPU-s | |
|---|---:|---:|---|
| **LG00's advice, `LG00.TP.Data.A*`** | **254** | **3,295.3** | **90 %**: the landed `Slp.compose` advice of `cfgLow`/`cfgFull`, never read by the packed route |
| the packed route's own data (`LG00P.TP.PK.*`: memos, books, fronts, `HamJet`) | 37 | 252.4 | 7 % (§3 C) |
| LG00's other data (`W*`, `B*`, `E`, `Leaves`, `Cert`, `DCoeffs`) | 21 | 83.1 | 2 % |
| kamx-packed's certificate copy and shared modules (`LG00P.Format*`, `Coeffs*`, `Ham`, `TP.Data.*`) | 9 | 42.4 | 1 % |
| shared LG00 modules with no ledger row (`Format`, `Coeffs*`, `Ham`) | 5 | 0 | |

**Why the advice is in the closure.**
- The packed route never reads the advice: kamx-packed's copy `LG00P.TP.lg00Cert` drops it.
- T′'s `Xfer` imports LG00's own Hamiltonian bounds (`LG00.TP.Balls.HamBounds`). Their disc pass reads four fields of
  `LG00.TP.lg00Cert`, so they import `LG00.TP.Data.Cert`, which imports all 274 data modules: every advice part and
  every witness part.
- The bridge to LG00's own constants (V2-PACKED-CONS-BRIDGE) names `LG00.TP.lg00Cert` in the statement, so it
  imports `LG00.TP.Data.Cert` too.
- T″'s packed route proves the ball bounds on the copy (kamx-pk-gen; its `MainJ` imports no `LG00.*` module). The
  bridge to LG00's statement still brings in `LG00.TPP.Data.Cert`.
- So, as LG00's certificate is defined (one constant whose body names the advice), **any theorem about LG00's own
  `lg00Cert` elaborates all of LG00's advice.**

**Why each advice module costs 13 CPU-s** (run18: 8.7–15.4, mean 13.0, ≤ 0.96 GB):
- Each part is about 124 KB of `noncomputable def … : List ℤ := dzs [n₀, n₁, …]`, about 34,000 numerals. In all:
  10,408 lists, 8,705,459 values, 31.6 MB.
- 94.9 % of the values are 0, in 453,932 runs; 444,601 are nonzero, many of them wide (up to 15 bytes).
- The cost is elaboration, one numeral at a time: `A100` takes 5.1 s of elaboration against 26 ms of kernel time.
  So the cost follows the numeral count, not the bytes: LG00's `W*` parts cost 4.2 CPU-s per 104 KB, because their
  numerals are wide.
- The fixed cost per module is small by comparison: the floor (an empty module importing `LG00.Format`) is
  1.2–1.8 CPU-s.

## 2. A measured fix: packed advice (`scripts/packed/cons_data_gen.py`, `cons_data_build.sh`)

**The packed form keeps each definition** (name, type, value) and stores its naturals in a few large literals, at most
88 digits each, one per line. Per list, the generator picks whichever of three forms needs the fewest literals:
- fixed-width fields, `dzs (List.take LEN (unpkC W K [c₀, …]))`;
- the values' LEB128 bytes, 36 per literal (`leb 0 0 (unpkC 8 36 …)`);
- the same over run-length tokens, one token per run of zeros (`rle (leb 0 0 (unpkC 8 36 …))`).

The decoders (`LG00X.Pack`: `unpk`, `unpkC`, `leb`, `rle`) are structural, and the kernel evaluates them with GMP.
The Python mirror checks every round trip.

**Measured on real parts.**
- Each module was compiled with `lean` alone (no Lake), against the integration core and `kam-lg00`, read only.
- One process at a time under 4 GB, after the 20 GB anon wait.
- Two passes. Pass 1 ran under heavier machine load; pass 2 interleaves originals and packed forms on a quieter
  machine. The table is `table.txt`; the logs are `logs/`.

| module | what | CPU-s, pass 1 | CPU-s, pass 2 | elaboration | kernel | peak |
|---|---|---:|---:|---:|---:|---:|
| `Floor` | empty module importing `LG00.Format` | 1.84 | 1.19 | 2 ms | 0 | 0.28 GB |
| `A0` | LG00's `A0`, verbatim (117 KB, 28 lists) | 12.74 | 7.03 | 3.3 s | 22 ms | 0.59 GB |
| `Pk0` | `A0` packed (planned module 0) | 1.57 | 1.44 | 125 ms | 3 ms | 0.30 GB |
| `A100` | LG00's `A100`, verbatim (126 KB, 44 lists) | 18.26 | 9.90 | 5.1 s | 26 ms | 0.76 GB |
| `A100P` | `A100` packed | 1.75 | 1.28 | 38 ms | 2 ms | 0.28 GB |
| `A253` | LG00's `A253`, verbatim (72 KB, 25 lists) | 10.28 | — | 5.3 s | 52 ms | 0.57 GB |
| `A253P` | `A253` packed | 1.73 | — | 33 ms | 2 ms | 0.28 GB |
| `MP` | `A0` + `A100` + `A253` packed in one module | 2.35 | — | 234 ms | 9 ms | 0.31 GB |
| `Pk50` | `A72` packed (planned module 50) | 1.49 | — | 122 ms | 3 ms | 0.30 GB |
| `Pk103` | `A250`–`A253` packed (planned module 103) | 1.82 | 1.67 | 170 ms | 7 ms | 0.30 GB |
| `A0Eq` | `A0`: packed = original, every list, `decide +kernel` | 12.10 | — | 28 ms | 10.4 s | 0.52 GB |
| `A100Eq` | `A100`: packed = original | 12.69 | — | 74 ms | 11.1 s | 0.55 GB |
| `A253Eq` | `A253`: packed = original | 7.98 | — | 23 ms | 6.5 s | 0.47 GB |
| `A100Sum` | `A100` original: every value forced in the kernel | 5.02 | — | 96 ms | 3.2 s | 0.52 GB |
| `A100PSum` | `A100` packed: every value forced | 10.96 | — | 82 ms | 9.2 s | 0.57 GB |

**Reading.**
- **A packed part costs about the floor.** It is 5–8× cheaper than the original in pass 2 and 5–10× in pass 1. Three
  parts in one module cost 2.35 CPU-s against 41.3 for the originals (17.6×, pass 1).
- **The packing is faithful.** For every list of `A0`, `A100` and `A253`, `packed = original` holds by
  `decide +kernel`. That costs 6.5–11 kernel-s per part: an audit cost, not needed in production.
- **A consumer of the values pays more in the kernel.** Forcing every value of `A100` costs 9.2 kernel-s packed
  against 3.2 original. The packed route never reads the advice. LG00's landed `Low`/`Full` chains do, so packing
  would add kernel work to them (about 6 s per part read in full).

**The whole T′ advice, packed** (`stats_TP.txt`):
- 254 parts and 10,408 lists become 77,156 literals in 108,380 lines: 7.5 MB against 31.6 MB.
- At ≤ 1,400 lines per module, with whole parts per module, that is 104 modules. The planned modules 0, 50 and 103
  were built: 1.4–1.8 CPU-s each.
- **Projection:** about 104 × 1.6 ≈ 170 CPU-s, plus Lake's start per module, against 3,295 CPU-s in run18. That
  saves about 3,100 CPU-s per torus: about 30 % of the packed route's 10,207 CPU-s, and 150 of its 881 modules. Filling
  modules by list rather than by whole part would bring them to about 80.

## 3. Options (owner's and orchestrator's choice)

Ordered by the saving to the packed route; none is applied here.
- **(A) An advice-free certificate core in LG00's generator.**
  - What: emit `lg00CertCore` (every field but the advice and the witnesses) in a module that imports only the
    advice-free data, and `lg00Cert := { lg00CertCore with … }` in the module that imports the advice (the audit's
    suggestion, AUDIT-V2-PACKED-PROD-1 C2).
  - Then `CertifiedTorus`, `lg00TorusWith` and `LG00TorusStatement` of `lg00Cert` and of `lg00CertCore` are
    `Iff.rfl`. The packed route, the bridge and kamx-conf's assembly can be stated at `lg00CertCore` and never import
    the advice.
  - Saving: 3,295 CPU-s per torus (about 32 % of the route), plus whatever of LG00's other data (83 CPU-s) the core
    no longer needs. The landed route is unchanged.
  - Costs: an `lg00-app` generator change, and kamx-conf would consume `LG00TorusStatement lg00CertCore …` (or its
    `Iff.rfl` image).
- **(B) Packed advice in LG00's generator** (§2, measured).
  - The advice stays in `lg00Cert`, with the same names and values, so every statement is unchanged.
  - Saving: about 3,100 CPU-s per torus in elaboration.
  - Cost: LG00's landed chains decode in the kernel instead of reading literals. Not needed if the landed route is
    retired; otherwise measure on one landed chain module first.
- **(C) Smaller items on the packed route.**
  - Drop the fronts: kamx-pk-gen's `JetFront` lookup checks and `Data.Front`, 8 modules, 84 CPU-s. They are not
    needed on ledgers that list the wanted slots first, which kamx-packed's `jet_prod_gen.py` emits since
    `2796f8c8`, so this applies to T″ and later trees. T′'s chains (`3a84cc28`) keep the old order; there my
    LOOKUP study measured the reads at 2.5 % of the consumers' kernel time without the front.
  - Pack or merge the memos: 25 modules, 152 CPU-s, 2.3 MB of `CertFixed` literals. That needs structure-specific
    decoders; perhaps about 100 CPU-s.
  - Importing LG00's own `Data` instead of kamx-packed's copy would save about 42 CPU-s, but every jet chain is
    stated at the copy. With the definitional bridge there is no correctness reason to do it.

**What is not the cause.**
- The packed route re-elaborates nothing that LG00's own data already proved: the Data row's LG00 modules are
  LG00's built artifacts, reused and not rebuilt.
- kamx-packed's copy duplicates only about 42 CPU-s.
- The fixed cost per module (about 1.2–1.8 CPU-s) is about 10 % of an advice module's cost.

## Reproduce

```
python3 -I scripts/packed/cons_data_gen.py A0 A100 A253          # Pack, Floor, A*, A*P, A*Eq, A*Sum, A*PSum, MP
python3 -I scripts/packed/cons_data_gen.py A100 --stats --emit=0,50,103   # whole-tree figures; planned modules
scripts/packed/cons_data_build.sh 4G LG00X.Pack LG00X.Floor LG00X.TP.Data.A100 LG00X.TP.Data.A100P …
```
The inputs are LG00's `TP/Data/A*` sources in `lg00-app` (untracked there), pinned in `sha256.txt` with the generated
sources.
