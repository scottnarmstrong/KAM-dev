# V2-PACKED-B3 handoff: the packed torsion stage

Task: the orchestrator's commission of 2026-11-01 (overnight decision): start the packed torsion stage on a new
branch `v2-packed-b3` from `v2-packed-b2`, under the same rules (new modules under `KAM/CertificateSharp/Packed`
only), end to end on LG00's data with its gate measurement. The Python-computed boundary values, re-checked
entry by entry in Lean, are approved. Rules: `V2-COMMON-RULES.md`, AGENTS.md. Branch `v2-packed-b3` is local
only; it is based on `v2-packed-b2` after V2-PACKED-B2-FIX (`0608588b`).

## Result in one paragraph

**The Lean is complete and sound end to end**, on the standard axioms:
- `checkTorsionPacked_sound` has the conclusion of the landed `checkTorsion_sound_of`, under its hypotheses.
- `torsPackedBase` (packed Gram **and** packed torsion) yields the landed `CertifiedTorus`
  (`checkV2With_torsPacked_sound`), and no landed Gram certificate is evaluated anywhere.

**On LG00's data, the gate passes for every part except the chain itself:**
- the 36 boundary entries;
- the layout, load and packing guards;
- the link to the Gram stage (the packed Gram core returns the generator's `δβ`);
- a data-mutation control.

**The exact packed chain does not fit the kernel at LG00 size, so the target is NOT met.** Its products
grow to 97-Mbit numbers, and two measured kernel limits stop it:
1. the kernel refuses `Nat.pow` results above 2^(2^24), i.e. 16.8 Mbit;
2. the kernel keeps every intermediate big integer of a declaration, so one entry of `DG⁻¹` alone reaches
   4.1 GB.

**Consequence.** There is still **no end-to-end saving** on LG00. A fix is designed and estimated below
(B3b: the landed truncation and rounding in packed form, the final split by entry); it needs an owner
decision.

## What was built (new modules, `KAM/CertificateSharp/Packed/`)

| module | lines | content |
|---|---:|---|
| `Enc.lean` | 418 | **Packed models** `PEnc L A e x r nb n ρ f` (an exact packed polynomial at scale `2^e` within `r` of `f`, of size ≤ `nb`) with `mul` (exact, radius `‖a‖ s + r ‖b‖ + r s`), `add`, `neg`, `sumN`, `shift` (a power of two at the zero key: change of window and scale), `renorm` (packed weighted norm), the boundaries `ofPCRep`, `ofMemo`. **Packed model matrices** `PMat` and `PMat.Encloses`, mirroring the landed `ModelMatrix.EntryEncloses`: `mul` (over `Fin m ≃ μ`), `add`, `neg`, `tr`, `omega`, `shift`, `renorm`. |
| `Avg.lean` | 203 | Digit extraction `slotAt` (two `Int.bmod`, one exact division; `slotAt_packSum`); **the average of a slot Fourier sum is its zero-key slot** (`torusAverage_slotSum`, via `keyOf_eq_zero_slot`); `PEnc.average`. |
| `Tors.lean` | 390 | `PTorsBook` (layouts, loads, norm exponents; windows `LDL … LT`), `PTorsMemo` (`D²K`, `DX_H ∘ K`, `DH ∘ K` at degree 0); boundary checks `ptD2Ok`/`ptAOk`/`ptD1Ok` against the landed `d2kModel` and `toDeg 0` of the landed `dxhModels`/`d1Models` entries; the exact chain `ptN, ptDL, ptDG, ptC, ptDGi, ptDN, ptXN, ptT, ptY`; the averaged test `ptFinal` (exact rational centres, exact `I − S C`, the landed `avgBoundsOk` and `avgInvRows`); the guards; `torsPackedCore`; `checkTorsionPacked`. |
| `TorsChain.lean` | 445 | Guard decompositions (`PTLay`, `PTNorm`, `PTPack`); base enclosures (`ptK_encloses` from the Gram memo, `ptB_encloses` from the Gram check's radius, `ptD2_encloses`, `ptF_encloses`, `ptDL_encloses`, `ptA_encloses`, `ptD1_encloses`); the chain lemmas `ptN_encloses … ptY_encloses` — packed models of exactly the matrices of the landed `torsion_eq_models`. |
| `TorsSound.lean` | 366 | `ptDef_eq` (the exact defect), **`torsPacked_sound`** (the landed `torsionAvgCheck_sound` conclusion for the frozen `extendedTorsionAverage`), **`checkTorsionPacked_sound`**, `checkTorsionPacked_of` (assembly from parts). |
| `TorsBase.lean` | 55 | **`torsPackedBase`** (landed sub-checks with packed Gram and packed torsion), **`checkV2With_torsPacked_sound`** → landed `CertifiedTorus`. |
| `TorsTests.lean` | 74 | Default kernel tests (about 3 s): a toy integrable case (`K` the identity, `B = I`, `DX_H = [[0, I], [0, 0]]`, `DH = (0, ω)`) whose bordered torsion `[[I, sω], [ωᵀ, 0]]` has an exact inverse witness; the core passes with bound 3 and fails with bound 1. |

Supporting files:
- `scripts/packed/tors_gate_gen.py`, the gate generator. It does four things:
  - copies LG00's literals read-only (`lg00-cert` `fd82fef5`, recorded in `TorsGate.json`);
  - computes the memos with the bit-exact mirror (`sofx_check.d2kModel`, `dxhModels`, `toDeg`);
  - computes the book from the Lean formulas, and `δβ`/`eps` with a bit-exact mirror of the packed Gram core
    (`gram_core`, checked by the kernel in `TorsGramVal`);
  - emits every probe behind a receipt, including the chain profile.

  `--toy` prints the book of `TorsTests`.
- `docs/campaign/studies/V2-PACKED-B3-GATE/`: the receipts (`entries/`, `profile/`, `superseded/`).

## Approach

- **Contract.** The landed `checkTorsion` builds models of the frozen bordered torsion through ten stages of
  truncated, rounded model products and averages them. `checkTorsionPacked` proves the same proposition
  with exact packed products:
  - **the matrices** are those of the landed `torsion_eq_models`: `N = Ω₀ (L G⁻¹)`,
    `D L = Σ_l (sω)_l ∂_l L`, `DG = D Lᵀ L + Lᵀ D L`, `D(G⁻¹) = −G⁻¹ DG G⁻¹`,
    `DN = Ω₀ (D L G⁻¹ + L D(G⁻¹))`, `X_N = A N − DN`, `T = Nᵀ Ω₀ X_N`, `Y = DH N`;
  - **the averages** are the zero-key slots of `T` and `Y` (digit extraction), the box centre for the
    frequency column, and 0 in the corner;
  - **the final test** is the landed `avgBoundsOk`.
- **The Gram link.** `checkTorsionPacked` takes `δβ` from the packed Gram check, through its contract
  (`‖G⁻¹ − B‖ ≤ δβ/(1 − δ)`). So `torsPackedBase` no longer needs the landed `gramCheck`; that is the
  dependency the B2 audit (M1) pointed at.
- **Boundary.** Every model the chain starts from is a landed model, memoized and re-checked per entry:
  - `DK`, via the Gram memo;
  - `∂_j ∂_l K`, via the landed `d2kModel`;
  - `DX_H ∘ K` and `DH ∘ K` at degree 0, via `toDeg 0` of the landed `dxhModels`/`d1Models` entries of the
    composed jet slots.

  The jet slots themselves are the landed `Slp.compose` at `cfgLow`, exactly as in the landed
  `checkTorsion`. In LG00 this is the `Low` stage (14.0 CPU-h), which is unchanged here.

## Checks and their output

- **Targeted builds**, `nice -n 5 systemd-run … MemoryMax=4G lake build KAM.CertificateSharp.Packed.<M>`
  for `Enc`, `Avg`, `Tors`, `TorsChain`, `TorsSound`, `TorsBase`, `TorsTests`: all give
  `Build completed successfully`, with **0 warnings in `Packed/`**.
- **Toy tests.** `TorsTests` passes (both examples). Its reversed claim fails, as a control.
- **`#print axioms`** gives `[propext, Classical.choice, Quot.sound]` for each of `PEnc.mul`,
  `PMat.Encloses.mul`, `PEnc.average`, `slotAt_packSum`, `torusAverage_slotSum`, `ptDL_encloses`,
  `ptT_encloses`, `torsPacked_sound`, `checkTorsionPacked_sound`, `checkTorsionPacked_of`, `torsPackedBase`
  and `checkV2With_torsPacked_sound`.
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS (3679 Lean files)` and `FROZEN-ANCHOR GUARD OK`.
  Only the pre-existing ABI step fails (missing `FixedSunPlanetaryKAM.olean`, as in B2).
  `gen_root_imports.py --check` exits 0.
- **Source limits.** No forbidden token in the new modules (`sorry`, `axiom`, `admit`, `native_decide`,
  `implemented_by`, `unsafe`, `opaque`, `extern`, `csimp`, `set_option`, heartbeats). No line exceeds 100
  characters; the largest file has 445 lines.
- **Additivity.** Against `v2-packed-b2` and against the merge base with `main`, the only changes under
  `KAM/` are the added `Packed/*.lean` and the generated `KAM/Root/CertificateSharp.lean`.

## Gate on LG00's data (receipts in `docs/campaign/studies/V2-PACKED-B3-GATE/`)

**Method.** As in B2: `run_probe.sh 4G`, one process at a time, `LEAN_NUM_THREADS=1`, `nice -n 5`; the memory
figure is the sampled cgroup charge. Data are at `lg00-cert` `fd82fef5`.

**Book** (`TorsGate.json`). One stride (315) and one slot width (1,168 bits) cover the whole chain. The
windows grow from `DK` (41 × 51) to `T` (263 × 315, 82,845 slots), so the packed sizes run from 14.8 Mbit
(`DK`) through 27 (`N`), 55 (`DG⁻¹`) and 69 (`DN`, `X_N`) to **97 Mbit (`T`)**.

| probe | forces | kernel | process (user + sys) | charged |
|---|---|---:|---:|---:|
| `TorsD2_r_j_l` × 16 | one `D²K` entry against the memo | 3.0–4.7 s (59.5 s) | 103.6 s | ≤ 0.97 GB |
| `TorsA_a_b` × 16 | one `DX_H ∘ K` entry at degree 0 | 0.4–2.2 s (16.4 s) | 93.3 s | ≤ 0.88 GB |
| `TorsD1_a` × 4 | one `DH ∘ K` entry at degree 0 | 0.4–1.2 s (2.8 s) | 21.6 s | ≤ 0.66 GB |
| `TorsAMut_0_2` | entry `A(0, 2)` vs. a memo mantissa + 1: `= false` | 0.7 s | 6.0 s | 0.62 GB |
| `TorsData` | all data of the core (control) | — | 11.5 s | 0.72 GB |
| `TorsGramVal` | the packed Gram core returns the mirror's `δβ` | 7.9 s | 12.5 s | 2.24 GB |
| `TorsEps` | `gramInvRadius δβ = eps` | ≈ 0 | 4.2 s | 0.50 GB |
| `TorsLay` | `ptLayOk ∧ ptNormOk` | 1.3 s | 11.7 s | 0.83 GB |
| `TorsPack` | `ptPackOk` (every memo entry and `B` packs) | 10.4 s | 19.8 s | 2.37 GB |
| **`TorsFinal`** | **`ptFinal` (the chain and the averaged test)** | — | **OOM-killed at 4 GB after 16 s** | 4.17 GB |

**Chain profile** (`profile/`, one entry of one node per process, `TorsNode*`):

| node | kernel | charged | outcome |
|---|---:|---:|---|
| `K` (packing of one entry) | 0.25 s | 0.75 GB | ok |
| norm of `K` | 0.49 s | 1.09 GB | ok |
| `D L` | 0.48 s | 0.94 GB | ok |
| `N` | 2.7 s | 1.28 GB | ok |
| `DG` | 3.4 s | 2.16 GB | ok |
| `DG⁻¹` | 10.2 s | **4.14 GB** | ok, at the cap |
| `X_N` | 7.3 s | 3.09 GB | **stuck**: the shift unit of `D L B` is `2^(21.1 Mbit)` > the numeral cap |
| `T` | — | 4.16 GB | **OOM-killed** |

**The two limits** (measured):

1. **Numeral cap.** The kernel refuses `Nat.pow` results above `2^16,777,216`: `2^16,777,216` evaluates, and
   `2^16,777,217` gives `(kernel) the kernel refused to evaluate Nat.pow … increase the LEAN_NAT_MAX_SIZE
   environment variable`. The exact chain needs powers up to:
   - `2^(21.1 Mbit)` for the `DN` shift unit;
   - `2^(69 Mbit)` for the norm masks of `X_N`;
   - `2^(48.4 Mbit)` for the zero-slot digits of `T`.
2. **Memory.** Within one declaration the kernel keeps every intermediate value.
   - One packing of a memo entry costs 20–90 MB of charge across runs (1.85 MB of packed data); one packed
     norm costs ≈ 0.35 GB.
   - Products cost roughly 4× their result size (an estimate from `TorsNodeN`).
   - One `DG⁻¹` entry already needs 4.1 GB, so the whole chain is far beyond 4 GB in one process.
   - Splitting it across processes would mean handing multi-megabyte intermediates over as literals (the
     deferred Decision 1). The intermediates above 16.8 Mbit are also above the cap. This was not measured
     further.

**Current method** (LG00 `run20e.tsv`): the Torsion stage is 637 modules, 11,258 s user + 868 s system
(**12,126 CPU-s**), max charge 2.44 GB; `Final.Torsion` adds 9.5 CPU-s. The `Low` stage (2,469 modules,
14.0 CPU-h) feeds both methods and stays.

**What the gate establishes.**
- The packed torsion **boundary** costs 36 processes and 218 CPU-s (79 s kernel), at ≤ 0.97 GB each.
- The **guards** cost 2 processes and 31.5 CPU-s.
- The **Gram link** is one probe with the Gram core's cost.

The **chain and the averaged test do not run at LG00 size**, so no end-to-end figure exists. The LG00 torsion
stage cannot yet be replaced, and the B2 caveat (no end-to-end saving) still holds.

## The fix (B3b, designed and estimated, not built)

Keep every packed number below the cap and every process below 4 GB, by doing what the landed check does,
in packed form:

1. **Round after every product.**
   - `gmpRound` (Round.lean, `gmpRound_spec`) brings each node back to scale `2^P`.
   - The rounding residual is exact (`Z − 2^s · round(Z)`, a unit product and a subtraction), and its packed
     norm enters the radius.
   - The slot width drops from 1,168 to about 370 bits: `2P` plus growth, plus the norm guard.
2. **Truncate every node to the `ℓ∞` box of half-width 24.**
   - This box contains the landed `cfgLow` cutoff (the `ℓ¹` ball of radius 24), so the result is at least as
     accurate as the landed models.
   - The truncation uses digit masks and a shift (Digits.lean: `natPack_land_mask`, `periodic`,
     `land_split`). The tail's packed norm enters the radius.
   - Windows stay at most 97 × 97, so every number is ≤ 3.5 Mbit, under the cap.
3. **Split the final test by entry.**
   - Each `T`/`Y` entry is decided in its own process, which hands over its exact centre (rational) and
     radius (backend value) as small literals.
   - One last cheap process runs `avgBoundsOk` on those literals.

**Estimate.**
- At width 370, packing costs ≈ 30 MB per memo entry, and products are ≤ 0.4 MB.
- One `T` entry's dependency cone is ≈ 50 packings and ≈ 250 products, which gives ≤ 2 GB per process.
- **Lean work:** the rounding and truncation lemmas in `PEnc` form (≈ 300–400 lines, on existing digit
  lemmas), and a literal-handoff `ptFinal` (≈ 150 lines).
- **Generator:** the mirror of the rounded chain, which is needed for the literals.

The radii grow by the rounding and truncation errors. The landed models carry the same kinds of error, so
the radii should be comparable to the landed ones, but this is not measured.

## Owner questions (overnight mode: none blocked work)

1. **B3b.** Should the packed torsion become rounded and truncated (the landed design in packed form, with
   radius-accounted errors) rather than exact? Without it, the packed torsion cannot run at LG00 size, and
   neither B2 nor B3 saves anything end to end.
2. **`LEAN_NAT_MAX_SIZE`.** Raising this kernel resource variable would lift limit 1, but not limit 2. Is it
   acceptable for opt-in application builds at all? It is not needed if B3b is approved.
3. **Assembly.** The production assembly is unmeasured, as in B2 L3:
   - a shared data module;
   - `checkTorsionPacked_of`, from LG00's `Slp.compose … = some lg00TMs` (its `Low` stage) and the probes.

## Deviations and uncertainties

- **The LG00 target is not met** (above). The Lean contract, the toy tests and the LG00 boundary, guards and
  Gram link are met.
- **The monolithic core probe was superseded** (`superseded/`).
  - It recomputed `eps` from the packed Gram core in the same declaration, and was OOM-killed after 22 s.
  - The gate now takes `δβ` and `eps` as literals from the bit-exact mirror `gram_core`, checked by
    `TorsGramVal` and `TorsEps`.
  - It decides `torsPackedCore`'s three conjuncts separately.
- **Entry probes carry only the memo entry they read.** The cost of the full data (one shared data module in
  production) is measured once, by `TorsData`.
- **`n = 2` only, effectively** (the packed norms need two-axis layouts); other `n` fail closed, as in B2.
- **No errata.** No pinned source was found defective.

V2-PACKED-B3 DONE — partial: the Lean is complete and sound; the LG00 chain does not fit the kernel limits
(see "The fix (B3b)").
