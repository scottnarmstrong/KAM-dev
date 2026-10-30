# SHARP2-C8C handoff: the hybrid certifier

Branch `sharp-c8c` (from `sharp-v2` at `4383bf40`; `sharp-c8a` merged once, at C8b's commit `5719ff81`). Design:
`APOST-SHARP-V2-HYBRID.md` §§2–3, blueprint `p2s2-hybrid-cert` (`bp:p2s2hc:*`, `bpI:p2s2hc:*`), data format
`docs/campaign/design/hybrid/format.md` v1 (C8d, read on `sharp-v2`; not merged).

## Result

The hybrid route is a certifier: a passing check gives `CertifiedTorus` for the **base** certificate, through C8b's
`iso_g1_hybrid_R`.

- **`checkHybrid c w`** (`Hybrid/Check.lean`): the transfer checks H0–H4 (`transferOk`, exact rationals), the step claims
  `(S1)–(S7)`, `ℓ_H`, `d_ω` (`hybStepOk`, models in the backend), and the route-A′ core at the restart numbers
  (`refinedCoreR n params1 box witness1`, H5).
- **`checkHybrid_sound`**: with the landed base facts and the base claim (`HamFacts`, `FrameFacts` of `w.R0`), the conclusion
  `IG1Concl` of `iso_g1_hybrid_R` for `K̂`, within `dinf + disp₁` of `K̂` on `T_{ρ∞}`, at a frequency within `d_ω + disp₁` of
  `s ω*`.
- **`hybrid_certified`, `routeHybrid`, `routeV2Hyb`** (`Hybrid/Iso.lean`): `CertifiedTorus c ω*` against `base.params.disp`. The
  engine's test is `checkHamClaim`, `checkFrameMajorants` of the base claim (as `routeARefinedR`) and `checkHybrid`.
  `routeV2Hyb` is `routeV2All` with `routeHybrid` as one more `orElse`:
  - `Sum.inl ()` is `checkTorusCertificateSharp` by `rfl` (`checkTorusCertificateV2_routeV2Hyb_sharp`);
  - a witness `Sum.inr w` of `routeV2All` is `Sum.inr (Sum.inl w)` here (`_all`, `rfl`);
  - `Sum.inr (Sum.inr w)` names the hybrid route (`_hybrid`, `rfl`).
- **T2 in the kernel** (`Hybrid/Tests/T2.lean`): the producer's `hybrid-T2.json` passes every check by sharded
  `decide +kernel`. `toyCert2H_hybrid_torus : CertifiedTorus toyCert2H ![ν₋/2, 1/2]` has displacement `1.6·10⁻⁴²`; the toy's own
  claim is `1.9·10⁻²⁶`. Three negative tests are rejected: a `dE0` below the Cauchy bound, a restart ray budget above
  `ν − d_ω`, and an outer displacement below `max {dinf, d_ω} + disp₁`.
- **R1, H0–H4** (`kernel-tests/CertificateSharp/V2/HybridR1L8Transfer.lean`, unbuilt): `transferOk` passes on
  `hybrid-R1-L8.json`.

## Files (2467 lines; all new except the root)

| File | Lines | Contents |
|---|---:|---|
| `Hybrid/ModelMul.lean` | 163 | `mulD` (direct product advice), `dotModel` (one merged model of `Σ_j a_j b_j`), `realWeight` and real-torus sup bounds |
| `Hybrid/Cauchy.lean` | 154 | `derivC`: the exact derivative of a model's polynomial plus a Cauchy bound of its radius |
| `Hybrid/Step.lean` | 236 | `stepFun` (ΔK from a `CertEmbedding`), `isStep_stepFun`, step models, `stepSupOk`, `stepRealOk`, `dstepOk` and their soundness |
| `Hybrid/Lin.lean` | 190 | `linModel` of `Ẽ = E(K, s₁ω*) + DX_H(K)ΔK − DΔK·s₁ω*` (one merged model per coordinate), `linNewError_le` |
| `Hybrid/Omega.lean` | 158 | `lagModel` (`Mᵀ Ω₀ M` entrywise), `dkM`, `dk1M`, `omegaOk`, `lagrangeMat_le`, `lagrangeMat_real_le` |
| `Hybrid/Energy.lean` | 184 | `enModel`, `energyLinOk`, `linNewEnergy_le` (`|ε̃| ≤ ℓ_H`) |
| `Hybrid/TransferQ.lean` | 239 | exact rational mirrors `FrameQ`, `KDataQ`, `StepNumQ`, `IsoNumQ` of C8b's numbers, with cast equalities |
| `Hybrid/Claims.lean` | 228 | `ratE` (the ℚ step rounded into α), `HybStep`, `hybStepOk`, `hybStepBounds` (C8b's `StepBounds`, `ℓ_H`, `d_ω`) |
| `Hybrid/RestartQ.lean` | 211 | `okRI_mono`, `budget_mono`, `finalOkA_at`, `HybWit`, `TransferFacts`, `transferOk`, `transferOk_sound` |
| `Hybrid/Check.lean` | 311 | `checkHybrid`, `frame_norms`, `checkHybrid_sound` |
| `Hybrid/Iso.lean` | 106 | `hybrid_certified`, `hybTest`, `routeHybrid`, `routeV2Hyb` and its `rfl` theorems |
| `Hybrid/Tests/T2.lean` | 198 | the T2 kernel test |
| `kernel-tests/CertificateSharp/V2/HybridR1L8Transfer.lean` | 89 | H0–H4 on R1 (unbuilt) |

All under `KAM/CertificateSharp/`, namespace `KAM.CertificateSharp.Hybrid`. `KAM/Root/CertificateSharp.lean` is regenerated
by `python3 -I scripts/gen_root_imports.py`; `KAM.lean` did not change.

## Approach

- **Newton cancellation on coefficients.** `Ẽ`, `Ω_K`, `Ω_{K₁}` and `ε̃` are each one model: `CertModel.addMixed` merges equal
  keys and `dotModel` sums exact products (`mulD`, advice `direct`) before any norm. The landed product needs advice for
  non-constant factors, so `directCfg` prepends `([8], direct)` to the configuration's advice.
- **The step** is `stepFun n (ratE dK)`, with `dK : CertEmbedding ℚ` from the witness. `ratE` rounds each coefficient with
  `ofRatUp`; any rounding is sound, because the claims are checked on the rounded step, which is the certified one. An
  `EngineV2` witness type cannot depend on `α`, so the step is carried over `ℚ`.
- **Weights.** The strip bounds use models built at the weight of the strip they bound (`W1`, `WT`): the weight enters only
  the rounding radii, and at `c.weight` (`w ≈ 3.6·10²⁴` for T2) those are large. Real-torus bounds use models built at `Winf`,
  bounded with `realWeight = ⟨0, 1⟩`.
- **The restart numbers.** The witness rounds `params1` and `witness1.R` upward (format H4: `≥`), but `iso_g1_hybrid_R` asks for
  the run at the exact transferred numbers. `routeAOkRI` is monotone in the caps and antitone in the initial values (both
  enter only (J3)); `Budget` is antitone in `m_T` and `i_H` (`okRI_mono`, `budget_mono`). The exact values are cast from
  `TransferQ` (`cast_init1`, `cast_sK1`, `cast_sB1`, `cast_tAext`).
- **`e₁`.** The theorem's `ℓ_H` is `err₁ − (M_{h2}/2)(d₀ᴿ)²` (`HybWit.qq`). By H2 this is at least the claimed `ℓ_H`, and
  `q.e1 = max(e₁ᴱ, err₁) = err₁` exactly, so the closeness constants `c2I`, `c3I` need no monotonicity in `e₁`.
- **The other iso numbers.** `q.dω = d_ω`, `q.Mh1 = R0.dh`, `q.Mh2 = R0.d2h`, `c_Th = 2 R0.dx` (`norm_hamComm_le`, format §5).
- **C8b's `restartI` note.** The restarted run's numbers are `witness1.base.num n params1 box`, whose `HY` is
  `R1.dh · sN`. `transferOk` checks `R1.dh = R0.dh = q.Mh1`, so `hHY` holds. This is `restartI`'s `HY := Mh1 · sN`, without
  going through `NumA.restart`.
- **`finalOkA_at`.** This is `finalOkA_sound` at the restart parameters, which are not a certificate's: rational facts on `p`
  replace `checkStatic`.
- **The wrapper.** The ray bound `σh = Θ/‖ω*‖` stands for `σω` (as in route A). Then `sinf < σω` follows from
  `ray_lt_of_disp`, with `d_ω + disp₁ ≤ base.disp < (σω − s) freqNormLo` (the outer checks of `transferOk`).

## Deviations and choices (overnight: the conservative option, recorded)

1. **Module split.** The brief's `Step.lean` is split into `Step`, `Lin`, `Omega`, `Energy`, `TransferQ` and `Claims`, and its
   `Check.lean` into `RestartQ` and `Check`. Each file stays well under 800 lines.
2. **Isoenergetic only.** The checker wires `iso_g1_hybrid_R` (format: `iso = true`; R1 and T2 are iso). The fixed-frequency
   `g1_hybrid_R` is not wired.
3. **`dE0`, `dE0R`** use the whole-error Cauchy bound `n·err/(ρ − ρT)`, the alternative of format §3. It holds on the reals too
   (C8a's `errDerivMat_step_le` with `BaseFacts.hE`). `Cauchy.lean`'s `derivC` (exact derivative plus Cauchy remainder) is
   built and proved but not used by the checker; it is there for a sharper `dE0`.
4. **The witness** is `HybWit = {R0, step, p1, w1}`.
   - `R0` is `base.claim`.
   - `step : HybStep` holds `dK`, `s1`, three weights, `cl : StepNumQ` (the 14 claims), `lH` and `dw`.
   - `p1` is `params1` and `w1` is `witness1`.
   - `step.rho1` and `step.mu1` are not separate fields: the checker reads `ρ₁ = p1.rho` and `μ₁ = p1.μ`.
   - The real weight `(0, 1)` is the built-in `realWeight`.
5. **Checks beyond format H0–H4.**
   - `0 ≤ err₁`, `0 < m`, `0 < ν − d_ω`, `p1.M = M` and `p1.E0 = E0`.
   - The strips: `ρ₁ ≤ W1.rho ≤ ρ`, `ρ∞ ≤ Winf.rho`, `ρT ≤ WT.rho` and `0 < ρT < ρ`, with `ρT = ρ₁ − δ₀′` computed from the
     restarted run.
   - Format H0's `d₀ < μ`, `μ₁ < μ` follow from `d₀ + μ₁ ≤ μ`, `μ₁ > 0`; `ρ∞ < ρ₁` follows from the restarted `wfOk`.
6. **The T2 test certifies `toyCert2H`.** This is `toyCert2` with the file's `base.params`: they are the toy's except
   `disp = 1.6·10⁻⁴²`, against the toy's `1.9·10⁻²⁶`. No landed sub-check reads `disp`, by three generic `rfl` lemmas
   (`landedBase_check_disp`, `checkHamClaim_disp`, `checkFrameMajorants_disp`). The test therefore reuses
   `L1.toyCert2_base`, `toyCert2_hamClaim` and `L1.toyCert2_frame` instead of recomputing them.
7. **The T2 test's weights are not the file's** (format request F1 below). It takes the ceilings of `ratExpUp (2 piUpQ ρ) 8 24`:
   `⟨9, 3620571072184847796340984⟩`, `⟨1, 536⟩`, `⟨8, 6761204449081709109867⟩`.

## Format requests (for C8d)

- **F1. Weights.** All three `step.weights` of `hybrid-T2.json` fail the certifier's `checkWeight W c.expHalvings c.expOrder`
  (`#eval`: `false, false, false`). They are above `e^{2πρ}`, but below the certifier's rigorous upper bound
  `ratExpUp (2·piUpQ·ρ) 8 24`; at `ρ = 9` the gap is `5·10⁻⁶` relative. The same holds for `hybrid-R1-L8.json` at `8, 24`. The
  base R1 certificate's `expHalvings`, `expOrder` are not yet fixed, so this needs re-checking once they are. Proposed text
  for §1: "`w ≥ ratExpUp (2·piUpQ·ρ) expHalvings expOrder` of the base certificate (the mirror evaluates `ratExpUp`
  exactly)".
- **F2. T2's `base.params`** are not the Lean toy's verbatim (`disp`, item 6). This is harmless, but the file should say so.
- **F3. The Lean shape of the base certificate (format §7 open item).** The hybrid reads the base as the landed
  `TorusCertificate n ℚ`: `params`, `ham`, `weightH`, `centre`, `radius`, `freqBox`, `emb`, `weight`, `wit`, `gramInv`,
  `torsInv`, `cfgFull`, `cfgLow`, `piEnc`, `expHalvings`, `expOrder`. The witness is `HybWit` as in item 4. Once R1's
  certificate exists in Lean, `hybStepOk` on R1 follows the pattern of `Tests/T2.lean`.
- The kernel-only claims of T2 (`lE = err`, `dE0 = dE0R = 2 err`, the four `o` and `lH` equal to `0`) pass exactly in the
  kernel.

## Checks

- **Builds** (one niced `lake build` of a target at a time, with an RSS watchdog at 3.9 GB). Each hybrid module builds at
  default heartbeats with no override and no warning in the new files. The library modules peaked at 1.28–1.49 GB, and
  `KAM.CertificateSharp.Hybrid.Tests.T2` at **1.64 GB** (under the 2 GB budget). The last build of each:
  - `lake build KAM.CertificateSharp.Hybrid.Check`: `Build completed successfully (3608 jobs)`;
  - `lake build KAM.CertificateSharp.Hybrid.Iso`: `Build completed successfully (3640 jobs)`;
  - `lake build KAM.CertificateSharp.Hybrid.Tests.T2`: `Build completed successfully (3646 jobs)`.
  - `lake build KAM.CertificateSharp.Hybrid.Tests.T2 KAM.CertificateSharp.Hybrid.Iso --no-build`:
    `All targets up-to-date (3646 jobs)`.
- **T2 memory.** `lake env lean` of the test file measured 2.26 GB before the reuse of item 6, of which 1.8 GB is the
  imports alone (`lake env lean` on the imports only: 1.79–1.83 GB).
- **R1 transfer.** The kernel-test file was compiled with the data module inlined (`.drafts/c8c/R1Validate.lean`): no error,
  2.8 s, 1.87 GB. Expected cost in place is the same.
- **Root.** `KAM/Root/CertificateSharp.lean` is regenerated, but not built. Building it would compile unrelated, unbuilt
  `sharp-v2` modules in parallel (toy tests `Toy3`, `Toy2d`, `V2/Tests/Frozen`, `RefinedRef`, …; see `--no-build`). Every
  module it adds is built above.
- **`sh scripts/lint_sources.sh`.**
  - Output: `check_lean_modules: PASS (1839 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`.
  - The non-zero exit is the ABI probe: `KAM.Frozen.Planetary.Theorems.FixedSunPlanetaryKAM.olean` does not exist, and building
    it needs about 600 Planetary modules. This is the known accepted failure (C8B's handoff).
  - The pattern, line-length, size, root, errata and module checks print nothing.
- **Limits.** Files ≤ 800 lines (largest 311), lines ≤ 100 characters, no `sorry`, `axiom`, `set_option` or `native_decide`.
  Frozen files, `manifest/`, `README.md`, `KAM.lean`, `KAM/Certificate/**`, `KAM/SpinOrbit/**`, `scripts/spin_orbit/**` and
  `certificates/**` are untouched.
- **Names.** The new top-level names were searched in `KAM/**/*.lean` before use (none existed). `KAM.CertificateSharp.Hybrid` is
  a fresh namespace. The T2 names (`toyHybStep`, `toyParams1`, `toyWit1`, `toyHybWit`, `toyCert2H`, …) are new, and so are
  the R1 names (`r1BaseClaim`, `r1BaseParams`, `r1HybCl`, `r1HybStepH`, `r1HybWitH`, `r1Hyb_transfer`) in
  `KAM.CertificateSharp.HybridR1Test`.
- **`#print axioms`** (`.drafts/c8c/Axioms.lean`): `checkHybrid_sound`, `hybrid_certified`, `routeHybrid`, `routeV2Hyb`,
  `checkTorusCertificateV2_routeV2Hyb_sharp`, `hybStepBounds`, `transferOk_sound`, `toyHyb_passes` and
  `toyCert2H_hybrid_torus` all give `[propext, Classical.choice, Quot.sound]`.

## Uncertainties

- **T2 runs the step machinery only at `ΔK = 0`, `s₁ = s`, `ρ₁ = ρ`.** The merged products, the step models and the Ω models
  run on zero step data. A nonzero step is untested in the kernel; R1 needs its base certificate in Lean (F3).
- **R1 margins.** The R1 step claims marked kernel-only are the producer's floats × 1.10. Whether the kernel's merged models
  meet them is open until F3.
- **Weights and rounding radii.** For R1, the models at `W1` carry rounding radii that scale with the weight. T2 (exact `ℚ`,
  zero step) cannot show their size; this needs measuring on R1.

## Errata

No suspected erratum in a pinned source. F1 and F2 concern the producer's data files (C8d), not a pinned source.
