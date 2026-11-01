# V2-PACKED-B2 handoff: a packed Gram stage of the v2 certifier, end to end

Task: the orchestrator's commission of 2026-11-01. It asks for the packed sub-checker of the V2-PACKED design
(bridge B2), feeding the existing soundness theorem, on a new branch `v2-packed-b2` from `v2-packed`, with
new modules only. The target is a complete packed check of one LG00-shaped stage, end to end, measured
against the current method, on the standard axioms. Rules: `V2-COMMON-RULES.md` (no existing `KAM/**.lean`
edited), AGENTS.md. Branch `v2-packed-b2` is local only; it rebases on `v2-packed` at `cd84bf86`
(V2-PACKED-FIX and V2-PACKED-MOVE).

## Result

- **The stage: Gram** (`checkGram`), the certificate's proof that `G = DKᵀDK` is invertible on the strip
  with `Σ_j |G⁻¹_ij| ≤ σB − μ`. It is the field `hG` of the landed `BaseFacts`.
- **The packed check and its contract.** `gramPackedCheck_sound` has **exactly the conclusion of the landed
  `gramCheck_sound`**. `checkGramPacked_sound` has that of the landed `checkGram_sound`.
- **End to end.**
  - `gramPackedBase bk mm : BaseChecker` is the landed sub-checks with `checkGram` replaced by
    `checkGramPacked bk mm`. Its `sound` field yields the landed `BaseFacts`.
  - `checkV2With_gramPacked_sound` then gives the **landed `CertifiedTorus c ωstar`**, through the landed
    `checkV2With_sound`.
- **Axioms.** Every main result uses only `[propext, Classical.choice, Quot.sound]`.
- **Gate on LG00's own certificate data** (embedding, Gram inverse witness, weight, π enclosure), each piece
  in its own Lean process under a 4 GB cap on the cgroup charge:
  - **The packed check passes.** The eight boundary entries and the core each decide `true`.
  - **Negative control:** with the bound `σ = 1/100` the core returns `none`.

  | | current method (LG00 run20e) | packed |
  |---|---|---|
  | processes (modules) | 89 | **9** |
  | process CPU (user + system) | 1,306 + 119 s = **1,425 s** | 65 + 8 s = **73 s** (**≈ 19.5×**) |
  | kernel time | (not separated) | 31 s: 23.1 s boundary entries + 8.0 s core |
  | max cgroup charge | 2.28 GB (5.9 GiB cap) | **2.23 GB** (4 GB cap) |

  Of the packed 65 s of user time:
  - ≈ 35 s is import plus data elaboration (3.9 s per process × 9, from the data-only control);
  - 23.1 s is the boundary: the landed per-coefficient DK models and their mantissa comparison;
  - 5.3 s is the core's guard: packing the memo and the boundary of `B`;
  - ≈ 2.7 s is the packed arithmetic (products, defects, norms, final test): core 8.0 s − guard 5.3 s.

  The system time (8 s) is mostly process start-up.

## What was built (new modules, `KAM/CertificateSharp/Packed/`)

| module | content |
|---|---|
| `Slots.lean` | Slot semantics without term lists: `keyOf`, `InBox`, `layoutWf`, `slotSum`, `SRep` (packed slot data, with no gap slots). The boundary `srep_of_packRepOk`. Window layouts `win` (`win_wf`, `win_denseLen`, `win_inBox_add`). **Exact product** `SRep.mul` (Fourier sum = product of sums), sums `SRep.add`/`neg`/`sumN`, a unit at one slot `srep_unit`. |
| `Norm.lean` | Packed absolute values `packAbs` (`packAbs_spec`: masks and three subtractions). The no-carry product digit (`natPack_digit`, `dot_extract`). 2-D weight tables of `⌈w^e 2^q⌉` (`wCeil_ge`, `rowsPack_eq`, `weightRevList_getD`). **The strip bound of the packed weighted norm**, `slotSum_le_packNorm`, under the decidable guard `normOk`. |
| `Complex.lean` | Packed complex arrays `PC`, the meaning `PCRep`: `PCRep.mul` (four multiplications), `add`, `sumN`, `unitSub`, the boundary `ofPoly`, the strip bound `norm_le`. |
| `Gram.lean` | `PGramBook` (layouts, loads, norm precision). `PGramMemo` (the DK boundary, backend-free) and `pgEntryOk` / `pgEntries` (each entry checked against the landed `dkAngleModel` / `dkActionModel`). The packed computation `pgG`, `pgE`, `pgD` (exact, no rounding), norms and radii, `pgGuard`, `gramPackedCore`, `gramPackedCheck`, `gramPackedCheck_eq_core`. **`gramPackedCheck_sound`**. |
| `GramBase.lean` | `checkGramPacked`, **`checkGramPacked_sound`**, **`gramPackedBase`**, **`checkV2With_gramPacked_sound`**. |
| `GramTests.lean` | Default kernel tests on the identity embedding: entries, core, negative core (about 2 s). |

Supporting files:
- `scripts/packed/gram_gate_gen.py`: the gate generator. It copies LG00's literals read-only, computes the book,
  and computes the memo with the landed mirror (`sofx_check.dkAngleModel` / `dkActionModel`, bit-exact; the
  kernel re-checks each entry). The probes go to `.lake/v2-packed-gate/`, outside the sources.
- `docs/campaign/studies/V2-PACKED-B2-GATE/`: the receipts.

## Approach

- **Exact, not rounded.** `(B G)_ij = Σ_k B_ik Σ_r DK_rk DK_rj` is computed exactly as packed integers on
  window layouts, at scale `2^(3P)`. The slot width is 504 bits for LG00. There is no intermediate
  rounding, so the chain needs no read-back. Its meaning is slot data on layouts (`SRep`/`PCRep`), which
  carry the zero-gap invariant themselves.
- **Defect bound.** `δ_ij − (B G)_ij` (`pcUnitSub`) is bounded on the strip by a **packed weighted ℓ¹ norm**:
  - masked absolute values, then one product with a reversed 2-D weight table, reading the middle digit;
  - no digit carries, by the guard `normOk`.

  The radii of the landed DK models propagate through the cross terms, upward in the backend.
- **Boundary.** The DK entries are the landed models themselves (`dkAngleModel`/`dkActionModel`, degree `0`).
  Their mantissas come in a memo. Each entry is checked by `pgEntryOk` (mantissas equal, radius below the
  memo's bound), one per declaration. The core packs the memo; `B` is packed directly.
- **The landed final test.** `gramBoundsOk` and `matrix_inv_of_approx_inverse` are reused, so the conclusion
  is the landed one verbatim.

## Checks and their output

- **Targeted builds** (`nice -n 5 systemd-run --user --scope -p MemoryMax=4G … lake build
  KAM.CertificateSharp.Packed.<M>`), for `Slots`, `Norm`, `Complex`, `Gram`, `GramBase`, `GramTests` (and the
  V2-PACKED modules): `Build completed successfully`. No warning is attributed to a `Packed/` file; the
  warnings printed come from replayed landed modules (`KAM/Certificate/Sound/Static.lean`, …).
- **`#print axioms`** gives `[propext, Classical.choice, Quot.sound]` for each of: `slotSum_le_packNorm`,
  `SRep.mul`, `srep_of_packRepOk`, `packAbs_spec`, `gramPackedCheck_sound`, `pgDn_bound`,
  `checkGramPacked_sound`, `gramPackedBase`, `checkV2With_gramPacked_sound`.
- **`scripts/lint_sources.sh`:**
  - in the `Packed/` Lean modules, no line over 100 characters and no file over 1,500 lines (largest
    565). Scripts and docs follow the repo's wider existing convention.
  - `check_lean_modules: PASS (3672 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`;
  - only the ABI-hash step fails, on the missing `FixedSunPlanetaryKAM.olean`. This is pre-existing and
    unrelated, as in V2-PACKED.
- **Forbidden tokens.** A grep of `KAM/CertificateSharp/Packed/` for `sorry`, `axiom`, `admit`,
  `native_decide`, `implemented_by`, `unsafe`, `opaque`, `set_option` and heartbeats finds nothing.
- **Additivity.** Against the merge base, `git diff --name-status` over `KAM/**` shows only added
  `KAM/CertificateSharp/Packed/*.lean` and the generated `KAM/Root/CertificateSharp.lean`.

## Measurements (receipts in `docs/campaign/studies/V2-PACKED-B2-GATE/`)

**Method.** As in V2-PACKED: `scripts/packed/run_probe.sh 4G`, one process at a time, `LEAN_NUM_THREADS=1`,
`nice -n 5`. The memory figure is the sampled cgroup charge; max RSS runs ≈ 1.2–1.6 GB higher. The
machine was shared with other workers' builds, so timings vary with its load.

**LG00 data** (`GramGate.json`):
- dense lengths at stride 139: DK box 41 × 51 → 5,611; `B` box 35 × 39 → 4,765; `G` window 81 × 101 →
  11,221; `B G` window 115 × 139 → 15,985;
- slot width 504 bits; norm precision `q = 24`;
- memo: 5,314 mantissas of at most 129 bits.

| probe | forces | kernel | charged |
|---|---|---:|---:|
| `GramData` | data only (control) | — | 0.51 GB (3.9 s user) |
| `GramEntry_r_a` × 8 | one boundary entry `pgEntryOk … r a` | 2.0 / 2.0 / 2.0 / 2.4 / 3.3 / 3.8 / 3.7 / 3.5 s | ≤ 1.05 GB |
| `GramCore` | `(gramPackedCore … (σB − μ)).isSome = true` | **8.0 s** | **2.23 GB** |
| `GramCoreGuard` | the core's guard alone | 5.3 s | 1.26 GB |
| `GramCoreNeg` | `(gramPackedCore … (1/100)).isSome = false` | 7.7 s | 2.27 GB |

**Current method** (LG00 `run20e.tsv`, `KAM.LG00Cert.Gram.*`): 89 modules, 1,306 s user + 119 s system,
max charge 2.28 GB, max RSS 3.45 GB. Its shard modules recompute the landed DK models inside each group
(e.g. `KAM/LG00Cert/Gram/T26.lean`: `groupOk … ((dkAngleModel …).poly) …`).

**Why the boundary is split** (`scaling/`):
- **The single-declaration design was measured first.** `monolithic_GramGuard`: the guard, with the eight
  landed DK models in one declaration, took 142 s and 2.9 GB. `monolithic_GramPacked`: the whole check in one
  declaration was OOM-killed at 4 GB.
- **Landed per-coefficient work is superlinear in one process.** The same boundary for 2, 4 and 8 DK
  entries took 4.3, 14.1 and 110 s (`GramK2`, `GramK4`, `GramKall`), against 1.8–3.8 s per entry in
  its own process (`GramE1ok`, `GramE3ok`, the gate). Packing all four `B` entries in one declaration took
  3.8 s (`GramBall`).
- LG00's ledger reports a related memory effect (LG00-CERT.md: "Kernel memory accumulates across the
  declarations of a module" and "a regular segment's memory grows with its program position"). One entry
  per declaration avoids it.

## What it means

- **For LG00's Gram stage**, the packed check costs ≈ 19.5× less CPU (73 s against 1,425 s) and 10× fewer
  processes, at the same peak charge, measured on the same data.
  - The packed arithmetic itself is ≈ 2.7 s.
  - The rest is the landed per-coefficient boundary (23 s) and import plus literal elaboration (≈ 35 s).
- **A further gain** would come from building the DK entries packed from `K` (derivative ramps, design §2)
  instead of through the landed models; this was not built.
- **What `gramPackedBase` does not remove.** It replaces the Gram **fact** in the certifier. The landed
  `checkTorsion` recomputes the landed Gram certificate internally (`checkTorsion` matches on `gramCheck`),
  so the landed Gram work remains inside the torsion check until a packed torsion stage exists. In LG00's
  run20e the torsion stage is 637 modules, 11,258 s user + 868 s system (3.37 CPU-h).
- **Expectation, not measured:** if the other product stages have this stage's shape (exact packed products
  of landed models), their packed arithmetic should also take seconds at LG00 sizes. Their cost would then
  be set by the per-coefficient boundary, not by the products.

## Owner questions (overnight mode: none blocked work)

1. **Next stage?** Torsion would remove the landed Gram work still inside `checkTorsion`, and LG00's torsion
   stage is 3.37 CPU-h (run20e). Its boundary is larger: the second derivatives of the Hamiltonian along `K`, through the
   landed `cfgLow` chain.
2. **The boundary memo is untrusted Python** (the SO mirror), re-checked entry by entry in the kernel. Is a
   generator-side mirror acceptable for production stages? (It is for SO/LG00 today.)
3. The deferred owner items of V2-PACKED (long literal lines, the upstream `Hashable Nat` report, a home for
   generated data) stand.

## Deviations and uncertainties

- **`n = 2` only, effectively.** The packed norm needs two-axis layouts (`normOk`). Other `n` fail closed
  (sound, not complete).
- **The memo is computed by the SO mirror**, not by Lean, because the landed `CertFixed` instance is
  noncomputable, so `#eval` is impossible. The kernel re-checks every entry, so a wrong memo fails closed.
- **Wide slots.** The packed exact chain uses 504-bit slots, about 4× the mantissa width, for its guard bits.
  The core's GMP work is small anyway (about 2.7 s).
- **The `B` mantissas** of LG00 are multiples of `2^81`, the low-64-bit hash hazard of V2-PACKED. Here they
  measured linear (3.8 s for all four `B` entries), so no mitigation was applied.
- **Receipts.** `scaling/` holds the exploratory probes, including the superseded single-declaration design
  (`monolithic_*`).

V2-PACKED-B2 DONE
