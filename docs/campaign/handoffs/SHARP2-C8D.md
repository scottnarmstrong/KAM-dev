# SHARP2-C8D: the hybrid producer, the exact mirror and the format (C8d, first part)

Branch `sharp-c8d` from `sharp-v2` at 290d7682. Python and documents, an unbuilt R1-scale kernel test, and one `.drafts`
probe (≤ 1.84 GB). No kernel test was built or run.

## Outcome

- **R1, L = 8 candidate: the hybrid test passes in the exact mirror.**
  - The restarted run has e₁ = 5.191·10⁻¹² against e₁* = 1.54·10⁻¹¹: hybrid margin **+0.472** decades.
  - The plain run on the same K̂ has e = 4.319·10⁻⁶ against e* = 1.554·10⁻¹¹: margin −5.444.
  - The design's floating estimate was +0.34. The difference is the certifier's own route-A′ threshold (10^−10.81)
    against the design mirror's (10^−10.95).
- **Toy T2: passes** with the zero step, margin +35.770 for both the plain and the hybrid run. The zero step reproduces
  the plain margin here; design note F3 explains why this is not a general claim.
- **Caveats.**
  - Eight claims are "kernel-only" (`lE`, `dE0`, `dE0R`, `o0`, `o0R`, `o1`, `o1R`, `lH`). They are floating values
    × 1.10, not exact.
  - The base claim `r1Claim` is design data (sampled sups × 1.05), as in every v2 R1 test.
  - The package is the design package (c = 7/4), not SO's `lunarR1`; decision D1.

## Files (all new; no tracked file modified)

| File | Lines | Content |
|---|---:|---|
| `scripts/apost_sharp/hybrid_numq.py` | 328 | Exact `Fraction` port of the route-A′ numbers of the certifier (`StepQ`, `NumQ`, `okR`, `budgetOk`, `wfOk`, `finalOkA`, `c2Q`, `c3Q`, `capRQ`, `initRQ`), `max_xs`, the R1 and T2 data; `validate()` against four kernel facts |
| `scripts/apost_sharp/hybrid_mirror.py` | 280 | The exact mirror of the hybrid test: parses a `kam-hybrid` file, recomputes the polynomial claims exactly, checks H0–H5 and reports margins and slacks |
| `scripts/apost_sharp/hybrid_producer.py` | 444 | The producer: K̂, ΔK̂, W, Gram and torsion witnesses, models of E and Ẽ, claims, restart numbers and witnesses (R1-L8, T2); the Lean data emitter |
| `docs/campaign/design/hybrid/format.md` | 166 | Format v1, the spec shared with C8c (owned by this package): §1 conventions, §2 `base`, §3 `step`, §4 `restart`, §5 checks H0–H5, §6 scope, §7 Lean data and test modules |
| `docs/campaign/design/hybrid/hybrid-R1-L8.json` | 73 kB | The R1 hybrid file |
| `docs/campaign/design/hybrid/hybrid-T2.json` | 4 kB | The T2 hybrid file |
| `kernel-tests/CertificateSharp/V2/HybridR1L8Data.lean` | 508 | Generated Lean data (from the JSON alone) |
| `kernel-tests/CertificateSharp/V2/HybridR1L8.lean` | 120 | Unbuilt: H5 without the sites; the margin pair |
| `kernel-tests/CertificateSharp/V2/HybridR1L8Core.lean` | 61 | Unbuilt: H5 with the base run's certified sites |

Lean files: at most 508 lines, at most 100 characters per line. Python follows the repository's mirrors (about 120).

## Approach

1. **Exact port first.** `hybrid_numq.py` transcribes `RouteAQ.lean` and `RouteAQRef.lean` into `Fraction`
   arithmetic. It must reproduce four kernel facts before anything else is trusted: `r1_refinedCoreR` true at
   155·10⁻¹³, `r1R_final_rejects` false at 156·10⁻¹³, `toyCert2_refinedCoreR` true, and its rejection with
   `bT = 1/100`.
2. **The mirror** (`hybrid_mirror.py`) reads only the JSON.
   - Polynomial claims (`d0`, `dinf`, `d1`, `d1t`, `d0R`, `d1R`, `d1tR`) are recomputed exactly: weighted norms with
     upward enclosures of e^{2πρ}, π ∈ [333/106, 355/113], and complex moduli bounded by |re| + |im|.
   - H0–H4 (margins, frames by Neumann, e₁, torsion with the iso term, consistency of `params1` and the transferred
     claim) are exact rational inequalities.
   - H5 is `refined_core_r`, the port of `refinedCoreR` without its site certificates, which are reused (D4).
   - Margins: e* = X*_max γ⁴ δ₀′^{4τ}, with X*_max the largest X⋆ for which `okR` passes (bisection, exact).
3. **The producer.**
   - K̂ is R1's L = 8 candidate: v̂ cut at 10⁻⁸ (23 terms), Ĵ with tail 10⁻³e (73 terms), coefficients dyadic at 2⁻⁶⁰.
   - ΔK̂ is the finite Newton step, truncated at 10⁻³e² and rounded (DK̂ supports 125, 60, 149, 191).
   - Witnesses: W ≈ e^{2iv̂} (127 terms), the Gram inverse, the torsion inverse. Advisory models of E and Ẽ.
   - Claims: the polynomial ones exact (the mirror's norms, rounded up); the kernel-only ones floating × 1.10.
   - Restart: the transfer computed exactly; `params1` rounded outward; X⋆ = 0.999·X*_max rounded down; the
     closeness budget D₁ = max(c2Q, c3Q)·e₁/(γ²ρ^{2τ}) rounded up; outer `disp` = max(dinf, d_ω) + D₁.
   - T2: the zero step (D2).
4. **Lean.** `write_lean` emits the data from the JSON dict alone. The test modules use only the existing route-A′ API
   (`refinedCoreR_of`, `sitesOk`, `finalOkA`). H0–H4 wait for C8c's checker; I did not invent its API.

Key numbers of the R1 restart (exact values in the JSON):

| | base | restarted |
|---|---|---|
| err | 4.319·10⁻⁶ | 5.191·10⁻¹² |
| μ | 1/160 | 6.2382·10⁻³ |
| σK, σB, σT | 1.37440, 1.93090, 0.619450 | 1.37439, 1.93094, 0.619792 |
| bL, bN, bNt, bT | r1Claim | 1.39314, 1.42178, 1.44772, 3.48063 |
| X⋆ | 161000 | 19934881/125 ≈ 159479 |
| ρ, s | 1/70, 1 + 10⁻⁶ | 1/70, 1 + 10⁻⁶ |

Step claims: d₀ = 1.154·10⁻⁷, d₁ = 5.923·10⁻⁶, d₁ᵗ = 4.423·10⁻⁶, dinf = 5.692·10⁻⁸, d₀ᴿ = 5.688·10⁻⁸, d₁ᴿ = 2.722·10⁻⁶,
d₁ᴿᵗ = 1.810·10⁻⁶; lE = 5.184·10⁻¹², dE0 = 1.971·10⁻⁴, o0 = 2.761·10⁻⁶, o1 = 1.662·10⁻¹², lH = 7.15·10⁻¹⁸,
dw = 3.93·10⁻¹³. Transfer: g = 1.43·10⁻⁵, t_A = 9.41·10⁻⁴, Δ_ab = 8.77·10⁻⁴, λ₀ = 1.10·10⁻³, λ₁ = 1.25·10⁻⁸.

## Decisions (overnight, conservative, recorded)

- **D1. Design package, not SO's `lunarR1`.** The v2 certifier's R1 tests (`r1Params`, `r1Box`, `r1Claim`,
  `r1RefinedWitR`, `r1R_sites`) are in the design package, so the restart can reuse their certified sites. K̂ and ΔK̂ do
  not depend on c; the parameters, the claim and E's model do. The SO production is a later package (C8d part 2,
  format.md §6).
- **D2. T2 uses the zero step.** T2's residual is the width of its frequency box, which no step reduces. T2's base
  embedding in the JSON is the 2⁻⁶⁰ rounding of the toy's exact rationals; the hybrid test reads only the step, the claims
  and the numbers.
- **D3. Kernel-only claims are floating × 1.10**, rounded up. The mirror cannot recompute them without the composition.
- **D4. Sites reused at ρ₁ = ρ.** `sitesOk` reads only `n`, `τ`, `kp`, `ρ`, `ρ∞`, `c`, `c̄` and `γ`, `κ`, the box, and
  all of these equal the base run's. The congruence `hyb_sitesOk_congr` lives in the test module, not in `KAM/`.
- **D5. The restarted torsion cap.** The restarted `t` is the base `t` shifted by the increment bT₁ − bT, which keeps
  the base witness's slack t − bT = 0.0814.
- **D6. `kernel-tests/README.md` not edited** (tracked file; additive rule). The rows to add are below.
- **D7. Module paths** follow the kernel-tests convention: `kernel-tests/CertificateSharp/V2/X.lean` compiles as
  `KAM.CertificateSharp.V2.Tests.X` when placed back under `KAM/`.
- **D8. Lean data split** into declarations of at most 40 terms, with mantissas written `q60 m`, after a
  default-heartbeat timeout (next section).

## Design signal: a default-heartbeat timeout in the generated data (resolved by splitting)

The first emission wrote `r1HybStep` as one 261-term literal with `(m / 2 ^ 60 : ℚ)` coefficients. The probe failed:

```
.drafts/c8d/HybProbe.lean:299:34: error: (deterministic) timeout at `«synthesize pending MVars»`, maximum number of
heartbeats (200000) has been reached
```

Per hard rule 1, I did not raise the budget. Instead:

- every mantissa goes through an exposed helper `q60 (m : ℤ) : ℚ := m / 2 ^ 60`, so no `HDiv`/`HPow` unification
  happens per literal;
- each component's term list is split into declarations of at most 40 terms (`r1HybStepAct1P0 ++ …`).

The whole data file then elaborates in seconds (next section).

## Checks (exact commands and output)

1. Port validation: `cd scripts/apost_sharp && python3 -I hybrid_numq.py`
   ```
   r1_refinedCoreR at e = 155/10^13: True {'Xs_pos': True, 'wf': True, 'okR': True, 'budget': True, 'final': True} (kernel: true)
   r1R_final_rejects at e = 156/10^13: finalOkA = False (kernel: false)
   toyCert2_refinedCoreR: True {'Xs_pos': True, 'wf': True, 'okR': True, 'budget': True, 'final': True} (kernel: true)
   toyCert2_refinedCoreR_rejects (bT = 1/100): False (kernel: false)
   validate: PASS
   ```
2. Producer:
   `OMP_NUM_THREADS=1 nice -n 10 python3 -I scripts/apost_sharp/hybrid_producer.py --out docs/campaign/design/hybrid --lean kernel-tests/CertificateSharp/V2`
   ```
     wrote docs/campaign/design/hybrid/hybrid-T2.json (4004 bytes)
     R1-L8: v^ 23, J^ 73, DK^ [125, 60, 149, 191] terms; e 3.927e-06 (analytic 3.927e-06); E_lin~ 4.713e-12, E1 sup 2.365e-12 (11s)
     wrote docs/campaign/design/hybrid/hybrid-R1-L8.json (73496 bytes)
     wrote kernel-tests/CertificateSharp/V2/HybridR1L8Data.lean (508 lines)
   ```
   Re-running it after the final source edits reproduced all three outputs byte for byte (`cmp`: same, same, same).
3. Mirror:
   `python3 -I scripts/apost_sharp/hybrid_mirror.py docs/campaign/design/hybrid/hybrid-T2.json docs/campaign/design/hybrid/hybrid-R1-L8.json`
   ```
   == T2: hybrid test PASSES
      plain run:  e = 3.207e-43, e* = 1.89e-07, margin +35.770
      restarted:  e1 = 3.207e-43, e1* = 1.89e-07, hybrid margin +35.770
      slacks: d0+mu1<=mu 1e-06, d1+mu1/2<=mu/2 1e-06, beta g<1 1, m tA<1 1, closeness 1, outer disp 0, params1.err 3.06e-14
      exact polynomial claims: d0 0, d1 0, d1t 0, dinf 0, d0R 0, d1R 0, d1tR 0
   == R1-L8: hybrid test PASSES
      plain run:  e = 4.319e-06, e* = 1.554e-11, margin -5.444
      restarted:  e1 = 5.191e-12, e1* = 1.54e-11, hybrid margin +0.472
      slacks: d0+mu1<=mu 0.00188, d1+mu1/2<=mu/2 1.6e-10, beta g<1 1, m tA<1 0.999, closeness 1, outer disp 1.86e-13, params1.err 7.22e-14
      exact polynomial claims: d0 1.15e-07, d1 5.92e-06, d1t 4.42e-06, dinf 5.69e-08, d0R 5.69e-08, d1R 2.72e-06, d1tR 1.81e-06
   ```
   The slack `d1+mu1/2<=mu/2` is small by construction: μ₁ = μ − 2·max(d₀, d₁) − 10⁻¹². It is an exact comparison.
4. Margin pair for the restarted witness (exact, `hybrid_numq.final_ok_a`, with three times the closeness budget): passes
   at e = 1.5·10⁻¹¹, fails at 1.55·10⁻¹¹ on the smallness alone (`small: False, disp: True, ray: True`). These are the
   theorems `r1Hyb_final_room` and `r1Hyb_final_rejects`.
5. Probe (`.drafts/c8d/HybProbe.lean`, assembled by a script from the verbatim text of the three test files):
   - the R1 decides of `HybridR1L8` become hypotheses with the same names and statements, so the assembly proofs are
     checked verbatim;
   - `RefinedR1`/`RefinedRefR1`'s data blocks are copied, and `r1R_sites` becomes a hypothesis;
   - the only decides run are the six small ℚ/ℕ equalities of `r1Hyb_sites`.

   Command: `nice -n 5 lake env lean .drafts/c8d/HybProbe.lean`, under a watchdog that kills its own `lean` child
   above 4 GB.
   ```
   wall 19.38 s, maxrss 1669008 kB
   exit 0, peak lean RSS 1648424 kB (sampled)
   ```
   No errors, no warnings. Three runs of the final probe text took 11.8–21.3 s with peaks of 1.65–1.84 GB (machine
   load). The `#print axioms` output is below.
6. `sh scripts/lint_sources.sh` (exit 1, from the ABI step only):
   ```
   check_lean_modules: PASS (1815 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   …/.lake/abi-scratch/tmp….lean:1:0: error: object file '…/.lake/build/lib/lean/KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean' of module KAM.Frozen.Planetary.Theorems.FixedSunPlanetaryKAM does not exist
   ```
   The ABI step needs frozen oleans that this worktree has not built. It fails identically on branches that add no Lean
   file (SJS-FEAS). No line-length finding remains.
7. Name clashes: `grep -rln "HybridR1Test\|HybridR1L8\|hyb_sitesOk_congr\|\bq60\b" KAM kernel-tests scripts` lists only
   this package's files. `git log --all -S HybridR1Test` is empty. `KAM/CertificateSharp/V2/Tests/` has no `Hybrid*`.

## `#print axioms` (probe)

```
'KAM.CertificateSharp.HybridR1Test.r1Hyb_refinedCoreR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.r1Hyb_sites' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.hyb_sitesOk_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.r1HybBase_num' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.r1HybParams1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.r1HybStep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.CertificateSharp.HybridR1Test.r1HybEmb' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In the probe, `r1Hyb_refinedCoreR` takes the five R1 decides and `r1R_sites` as hypotheses. In the kernel test they are
`decide +kernel` theorems, which add no axiom.

## The R1-scale kernel test and its expected cost (not built, not run)

| Module | What it checks | Expected cost | Basis |
|---|---|---|---|
| `HybridR1L8Data` | data only | about 2 GB, seconds (inside the probe, with the imports and the test text: 11.8–21.3 s, ≤ 1.84 GB) | probe |
| `HybridR1L8` | `wfOk`, `okR`, `budgetOk`, tail, `finalOkA` of the restarted run; `r1Hyb_refinedCoreR_of_sites`; the margin pair | seconds; ≤ 3 GB | C6L8 measured the same five decides of `Tests/RefinedRefR1` together at about 1 s; here the rationals are larger (denominators up to 10²⁴) |
| `HybridR1L8Core` | `r1Hyb_sites` (congruence from `r1R_sites`), `r1Hyb_refinedCoreR` (H5) | itself small; **its imports need `Tests/RefinedRefR1` (19.2 GB, 6 min) and `Tests/RefinedR1` (10.4 GB, 2.5 min)**, so it cannot run on lemma.farm until those bites are rounded or sharded (C6's suggestion) | C6, C6L8 handoffs |

These estimates are not measured, apart from the data. C8c's checks H0–H4 are not yet written; their expected costs are
in `HybridR1L8Core`'s docstring:

- polynomial claims: seconds;
- the Ω products: under a minute, one declaration per matrix entry;
- the model of Ẽ: minutes, one declaration per coordinate, each expected ≤ 6 GB (calibration: SJS-FEAS packed product
  t ≈ 1.3·10⁻⁴ S^1.9 s, model ops 220 kB per term; C6L1 `invarianceModel` one coordinate at a time);
- the transfer arithmetic: about 1 s.

Proposed rows for `kernel-tests/README.md` (D6; for the orchestrator):

```
| `CertificateSharp/V2/HybridR1L8Data.lean` | data of the hybrid test on R1's L = 8 candidate (SHARP2-C8D; generated from `docs/campaign/design/hybrid/hybrid-R1-L8.json`) | ≈ 2 GB (probe) | seconds |
| `CertificateSharp/V2/HybridR1L8.lean` | the restarted route-A′ run of the hybrid on R1 (H5 without the sites; imports `HybridR1L8Data` by module path) | ≤ 3 GB (expected) | seconds (expected) |
| `CertificateSharp/V2/HybridR1L8Core.lean` | H5 with the base run's sites (imports `HybridR1L8` and `RefinedRefR1` by module path) | as `RefinedRefR1` | as `RefinedRefR1` + seconds |
```

## Uncertainties

- **Kernel-only claims.** `lE` dominates e₁ (5.184·10⁻¹² of 5.191·10⁻¹²). The restarted witness tolerates e₁ up to
  1.5·10⁻¹¹ (about × 2.9) if the closeness budget is re-sized with it (`r1Hyb_final_room`). So the kernel's `lE` may
  exceed the claimed value (floating × 1.10) by a factor of up to about 2.9 before H5 fails. The torsion has wide
  slack (m·t_A^ext ≈ 10⁻³ against 1).
- **Floating measurements** (Ẽ sup on 512 × 128 shifted grids) are sampled, not enclosures. The models are advisory;
  the kernel computes its own.
- **Base claim.** `r1Claim` is design data, as in every v2 R1 test. The hybrid inherits that status.
- **Base certificate's Lean data.** W, `gramInv`, `torsInv` and the Hamiltonian, domain and advice are in the JSON (or
  in the SO pipeline) but not emitted in Lean: the Lean shape is C8c's (format.md §7, open item).
- **Package.** SO's `lunarR1` needs its own run: the parameters, the claim and E's model change with c (D1).

## Errata

None found in pinned sources. Deviations: none beyond decisions D1–D8.

## Reproduce

```
cd scripts/apost_sharp && python3 -I hybrid_numq.py && cd ../..
OMP_NUM_THREADS=1 nice -n 10 python3 -I scripts/apost_sharp/hybrid_producer.py --out docs/campaign/design/hybrid --lean kernel-tests/CertificateSharp/V2
python3 -I scripts/apost_sharp/hybrid_mirror.py docs/campaign/design/hybrid/hybrid-T2.json docs/campaign/design/hybrid/hybrid-R1-L8.json
```
