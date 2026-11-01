# V2-PACKED-B3B handoff: the rounded and truncated packed torsion stage, end to end on LG00

Task: the orchestrator's decision 1 of 2026-11-01 (overnight). Build B3b on branch `v2-packed-b3`, under the
same rules and end to end on LG00's data with its gate. B3b is the rounded and truncated packed torsion:
- round each intermediate to 128 bits;
- truncate it to the landed mode box;
- put both errors in the radius;
- split the final test by entry.

Decision 2 (raising `LEAN_NAT_MAX_SIZE`) was declined, so the design must not need it, and it does not. B3 and
B3b are to be audited together. The branch is local and builds on B3 (`docs/campaign/handoffs/V2-PACKED-B3.md`).

## V2-PACKED-B3-FIX (audit AUDIT-V2-PACKED-B3-1: PASS WITH CHANGES, Lean sound)

- **M1.** The LG00 saving claim is withdrawn. The B3b figures are a stage-cost comparison only: route A refined's
  frame checks re-run the landed Gram check and torsion models, so with `torsRBase` the landed stages stay and
  the packed stages add ≈ 1,355 CPU-s (under "Result"). Design §9, §11 and §12 are corrected the same way.
- **L1.** The "production assembly unmeasured" caveat now stands next to the figures, together with the gate's
  statement names (`gW`, `gCfg`, literal `s`/`σ`).
- **L2.** The audit's sharp negative controls are now in the generator and the receipts (`controls/`):
  - `TRStCRadUlp`: the radius of `C(0,0)` lowered by one ulp (2⁻¹²⁸) gives `= false`;
  - `TRStCDrop`: the largest term of `C(0,0)` dropped, radius kept, gives `= false`;
  - `TRFinalEdge_hi` (σ = 0.2088116) gives `= true`, and `TRFinalEdge_lo` (σ = 0.2088114) gives `= false`.
    These bracket σ* = ‖S‖/(1 − δ_T) = 0.20881152.
- **L3.** The generator order is documented: `gram_gate_gen.py` must run before `tors_gate_gen.py` (same
  `V2P_GATE_DIR`; this is asserted). `torsr_gate_gen.py` has no such dependency.
- **I1.** The `TorsR.lean` docstring now says that the box containing the landed truncation is a property of
  the book chosen by the generator, which the check does not rely on.

## Result

- **The Lean is complete and sound end to end**, on the standard axioms.
  - `checkTorsionR_sound` has the conclusion of the landed `checkTorsion_sound_of`, under its hypotheses.
  - `torsRBase` (the packed Gram stage and the rounded packed torsion stage) yields the landed `CertifiedTorus`
    (`checkV2With_torsRBase_sound`). No landed Gram or landed torsion product is evaluated.
- **The gate passes on LG00's data** (`lg00-cert` `fd82fef5`): every conjunct of `checkTorsionR` is decided in
  its own process under the 4 GB cap, with no failure.
  - Every number is ≤ 3.67 Mbit, so the kernel numeral cap is never approached.
  - Every process is charged ≤ 3.19 GB.
- **A stage-cost comparison, not an LG00 saving (corrected by AUDIT-V2-PACKED-B3-1 M1).** For the base
  checker's Gram and Torsion sub-checks alone, on LG00's data:

  | sub-check | current method (LG00 run20e) | packed |
  |---|---|---|
  | Gram stage | 89 modules, 1,425 CPU-s | 9 processes, 73 CPU-s (B2) |
  | Torsion stage | 637 modules, 12,126 CPU-s (+ `Final.Torsion` 9.5) | **64 processes, 1,292 CPU-s** (269 s kernel) |
  | **both** | **726 modules, 13,561 CPU-s** | **73 processes, 1,365 CPU-s (≈ 9.9× per stage)** |
  | max cgroup charge | 2.44 GB | 3.19 GB (4 GB cap) |

  - **Production assembly is unmeasured (L1).** The packed column counts the probes only. It leaves out the
    shared data module and the assembly theorems (`checkTorsionR_of`; `stageAll` from the per-entry `stageOk`
    of `DN`/`X_N`).
  - **The probes are stated at the gate's names** (`gW`, `gCfg := ⟨24, 30, 12, CertFixed.toMant lgP, []⟩` with
    empty advice, literal `s` and `σT − μ`). These agree with `lg00Cert` in every field the checks read, but a
    production proof must state them at `lg00Cert.cfgLow` etc., and that link was not measured.
  - **There is no LG00 end-to-end saving.** LG00 certifies with route A refined, whose test also runs
    `checkFrameMajorants` (`RouteARefinedEngine.lean:35`). Its `checkFrameN` and `checkFrameT`
    (`KAM/CertificateSharp/Frame/Majorants.lean:141-167`) re-evaluate the landed `gramCheck`, a landed `[4,0]`
    product and the landed `torsionModels`. In LG00 these are `Final/FrameN.lean:22-24` (`lg00GramCheck`,
    `lg00TStage_0`) and `Final/FrameT.lean:22` (`lg00GramCheck`, `lg00TorsionModels`).
  - **So the effect today is a cost.** With `torsRBase` all 726 landed Gram and Torsion modules stay in LG00's
    build, and the packed stages **add** ≈ 1,355 CPU-s: only `Final.Torsion`, ≈ 10 s, disappears.
  - **What an LG00 saving needs:**
    - packed frame checks: `|N|`/`|Nᵀ|` from the verified `N` memo and `sup |T|` from the packed `T` on the
      window;
    - a route-A-refined engine variant whose test reads them.

    This is the orchestrator's next task, V2-PACKED-FRAMES.
  - The `Low` and `Full` jet compositions (14.0 and 10.2 CPU-h) are unchanged either way.
- **The final test.** With LG00's own torsion witness, `tabFinal` gives:
  - `‖S‖ = 0.2087` and `δ_T = 6.8·10⁻⁴`;
  - the test `‖S‖ + σ δ_T ≤ σ` with `σ = σT − μ = 0.20999` holds with **margin 1.18·10⁻³** (generator mirror);
  - the kernel decides `TRFinal` `= true`.

## Design (as decided; `docs/campaign/design/V2-PACKED.md` §11)

- **One box, one window.**
  - Every boundary entry and every node lives on the box `Lb`, the ℓ∞ box of half-width 25. It contains the
    landed `cfgLow` truncation (the ℓ¹ ball of radius 24) and every `DK` key.
  - Every product lands on the window `Lw = win Lb Lb` (101 × 101, stride 101).
  - The slot width is 360 bits, so a window number is 3.67 Mbit.
  - One unit layout `Lu` with `win Lb Lu = Lw` re-expresses a box node on the window, at scale `2^P`.
- **Nodes as verified memos** (`Stage.lean`).
  - Every node is an untrusted memo on `Lb` at scale `2^128`: `N = L G⁻¹`, `D L`, `DG`, `C = G⁻¹ DG`, `C G⁻¹`,
    `D L G⁻¹ + L D(G⁻¹)` and `X_N`.
  - The generator computes the exact product of the memoized inputs, **rounds** it to 128 bits (ties up) and
    **truncates** it to the box.
  - The kernel checks each entry by its exact residual `x − 2^P · memo` on the window. The residual's packed
    norm plus the propagated radius must stay below the memo's radius, and the memo's packed norm below its
    norm bound (`stageOk`).
  - So the rounding and truncation errors are in the radius and **never assumed**. A wrong memo fails the
    check (`TRStNMut`).
  - No digit lemma about rounding or masks is needed: the memo is validated by `packRepOk` and the residual.
- **The averages and the final test, split by entry.**
  - The zero-key slots of `T = Nᵀ Ω₀ X_N` and `Y = DH N` on the window are checked against small tables of exact
    centres (rationals) and radius bounds (`trTCheck`, `trYCheck`).
  - The landed averaged test then runs on the tables (`tabFinal`, `TabFinal.lean`). It is generic, so
    `tabFinal_sound` holds for any bordered matrix within the table radii of the table centres.
- **Radii.** The memos' radius and norm bounds equal what the kernel recomputes, bit for bit: the generator
  mirrors `CertFixed`'s `ofRatUp`, `upAdd`, `upMul` and `sumUp`, and the exact packed norms.

## What was built

**New modules** (`KAM/CertificateSharp/Packed/`):

| module | lines | content |
|---|---:|---|
| `Stage.lean` | 146 | `NodeEntry`, `nodePC`, `nodeRes`, **`stageOk`**, `stageAll`, `nodeMat`; **`PEnc.stage`** and `PMat.Encloses.stage` (a node memo passing `stageOk` is a packed model of the same function, with its radius and norm bound). |
| `TabFinal.lean` | 190 | `tabFinal` (the landed `avgBoundsOk` and `avgInvRows` on centre and radius tables, exact `I − S C`), **`tabFinal_sound`** (generic in the matrix). |
| `TorsR.lean` | 243 | `PRBook` (box, unit, loads, norm exponents; `toT` reuses B3's boundary), `PRMemo` (the seven nodes and the tables), the exact products `trMN … trMXN`, `trT`, `trY`, the stage checks `trStN … trStXN`, `trTCheck`, `trYCheck`, the tables `trCentre`, `trRad`, the guards, **`torsRCore`**, **`checkTorsionR`**. |
| `TorsRChain.lean` | 260 | `TRLay`, `TRNorm` (guard facts), `trDL0_encloses`, `trStage_encloses`, and the nodes `trNm_encloses … trXNm_encloses`, `trT_encloses`, `trY_encloses`: packed models of exactly the matrices of the landed `torsion_eq_models`. |
| `TorsRSound.lean` | 212 | **`torsR_sound`** (the landed averaged conclusion), **`checkTorsionR_sound`**, `checkTorsionR_of` (assembly from parts). |
| `TorsRBase.lean` | 52 | **`torsRBase`**, **`checkV2With_torsRBase_sound`** (landed `CertifiedTorus`). |
| `TorsRTests.lean` | 71 | Default kernel tests on the toy integrable case of `TorsTests` (box of half-width 1): the core passes with bound 3 and fails with 1 (about 3 s). |

B3's base enclosures (`ptK_encloses`, `ptB_encloses`, `ptD2_encloses`, `ptF_encloses`, `ptA_encloses`,
`ptD1_encloses`), its averages (`PEnc.average`) and its boundary checks (`ptEntries`) are reused unchanged.

**Scripts:**
- `scripts/packed/torsr_gate_gen.py` (new). It computes the exact Kronecker products (Python integers), the
  rounded and truncated nodes, the bit-exact radius and norm bounds, the tables, and a mirror of the final test.
  It emits every probe; `--toy` prints the book and memo of `TorsRTests`.
- `scripts/packed/tors_gate_gen.py`: its data loading is factored into `load()`. The B3 probes regenerate byte
  for byte (53 probes and `TorsGate.json` compared).

**Receipts:** `docs/campaign/studies/V2-PACKED-B3B-GATE/`, with `entries/`, `stages/`, `controls/` and
`profile/`, plus `TorsRGate.json`.

## Checks and their output

- **Targeted builds.** `nice -n 5 systemd-run … MemoryMax=4G lake build KAM.CertificateSharp.Packed.<M>` for
  `Stage`, `TabFinal`, `TorsR`, `TorsRChain`, `TorsRSound`, `TorsRBase` and `TorsRTests` all give
  `Build completed successfully`, with **0 warnings in `Packed/`**.
- **Toy tests.** `TorsRTests` passes, and its reversed claim fails as a control.
- **Spot re-runs.** After a reformatting of long lines, `TRFinal` and `TRStC` were re-run against the rebuilt
  modules; both still pass.
- **`#print axioms`** gives `[propext, Classical.choice, Quot.sound]` for each of `PEnc.stage`,
  `PMat.Encloses.stage`, `tabFinal_sound`, `trXNm_encloses`, `trT_encloses`, `torsR_sound`,
  `checkTorsionR_sound`, `checkTorsionR_of`, `torsRBase` and `checkV2With_torsRBase_sound`.
- **`scripts/lint_sources.sh`:** `check_lean_modules: PASS (3685 Lean files)` and `FROZEN-ANCHOR GUARD OK`.
  Only the pre-existing ABI step fails (`FixedSunPlanetaryKAM.olean`). `gen_root_imports.py --check` exits 0.
- **Source limits.** No forbidden token in the new modules. No line exceeds 100 characters; the largest file has
  445 lines.
- **Additivity.** Against the merge base with `main`, the only changes under `KAM/` are the added `Packed/*.lean`
  and the generated `KAM/Root/CertificateSharp.lean`.

## Gate on LG00's data

**Method.** As in B2 and B3: `run_probe.sh 4G`, one process at a time. The book is `TorsRGate.json`:
- box half-width 25, stride 101, slot width 360 bits;
- window 3.67 Mbit;
- product load bound `aW < 2^287`;
- node memos of 9,628 / 5,312 / 5,108 / 5,170 / 5,170 / 10,355 / 10,356 terms (51k in all).

Each probe carries the data it reads (one data module in production).

| group | processes | CPU (user + sys) | kernel | max charged |
|---|---:|---:|---:|---:|
| boundary entries (`TRE_*`: `D²K` 16, `DX_H ∘ K` 16, `DH ∘ K` 4) | 36 | 573.0 s | 89.8 s | 1.38 GB |
| guards (`TRLay`, `TRPack`) | 2 | 33.4 s | 10.9 s | 2.37 GB |
| nodes `N`, `D L`, `DG`, `C`, `C G⁻¹` (one process each) | 5 | 116.5 s | 44.1 s | 3.19 GB |
| node `D L G⁻¹ + L D(G⁻¹)` (one process per entry) | 8 | 238.3 s | 60.4 s | 2.03 GB |
| node `X_N` (one process per entry) | 8 | 259.1 s | 40.9 s | 2.07 GB |
| averages `T`, `Y` (`TRT`, `TRY`) | 2 | 50.3 s | 15.2 s | 2.58 GB |
| final test on the tables (`TRFinal`) | 1 | 4.5 s | 0.06 s | 0.49 GB |
| Gram link (`TorsGramVal`, `TorsEps`; B3 receipts, book-independent) | 2 | 16.7 s | 7.9 s | 2.24 GB |
| **total** | **64** | **1,291.8 s** | **269.3 s** | **3.19 GB** |

- **Data elaboration dominates.** Of the 1,292 CPU-s, 1,023 s is outside the kernel: process start-up, imports,
  and mostly each process re-elaborating its own copy of the data (the full data cost 30.4 s and 1.34 GB in
  `TRData`). A shared data module would elaborate it once (see
  owner question 1).
- **Controls:**
  - `TRFinalNeg` (bound 1/100) decides `= false`;
  - `TRStNMut` (a node mantissa off by `2^120`) decides `= false` in 3.7 s;
  - `TRData` is data only.
- **Profile** (`profile/`): `DN` in one process passes but at 4.24 GB, and `X_N` in one process is OOM-killed at
  4 GB. Hence the per-entry split of those two nodes.

## Owner questions (overnight mode: none blocked work)

1. **Production assembly** (as B2 L3): a shared data module (the memos), and the assembly theorems
   (`checkTorsionR_of`, plus `stageAll` from the per-entry `stageOk` of `DN` and `X_N`). These are unmeasured.
   A shared module would also remove most of the 1,000 CPU-s of per-process data elaboration.
2. **The exact B3 path** (`Tors.lean`, `TorsChain.lean`, `TorsSound.lean`, `TorsBase.lean`, `TorsTests.lean`)
   is sound and tested, but does not scale to LG00. Keep it as a small-instance reference, or drop it before
   landing?
3. **Next stage.** The largest landed stages of LG00 are now the jet compositions at `cfgLow` (14.0 CPU-h) and at
   `cfgFull` (10.2 CPU-h), i.e. `Slp.compose`. A packed jet evaluator (with the same verified-memo nodes) is the
   next candidate.

## Deviations and uncertainties

- **Truncation box.** The box is the ℓ∞ box of half-width 25, not the landed ℓ¹ ball of radius 24. It contains the
  ℓ¹ ball, so it is at least as fine as the landed truncation.
- **Rounding.** It is at scale `2^128` (`P`), ties up. Every truncated or rounded part is in the radius.
- **Per-entry probes for `DN` and `X_N`.** The assembly `stageAll ⇐ ∀ entries, stageOk` is by `List.all`
  (definitional), and was not measured as a separate process.
- **Boundary probes under the box book.** The boundary probes were re-run with the box book (`rBook.toT`, all
  `TRE_*`). The B3 `Tors*` entry probes decide the same checks (`ptD2Ok` reads only `tb.P`).
- **Gram link reused.** `TorsGramVal` and `TorsEps` (B3) are reused: their statements do not involve the torsion
  book.
- **Margin.** The final margin, 1.18·10⁻³ against `σ = 0.21`, is tight but positive. It uses LG00's own witness
  `S`, which was fitted to the landed centres.
- **No errata.**

V2-PACKED-B3B DONE

V2-PACKED-B3-FIX DONE
