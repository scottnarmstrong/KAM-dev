# SJS-FEAS handoff: can we certify a KAM torus of the planar Sun–Jupiter–Saturn system?

Brief: `/home/scott/kam-tools/briefs/SJS-FEAS.md` (Opus), branch `sjs-feas` (from `sharp-v2`). LOCAL-COMMON applies.
This is a feasibility study: Python, documents and throwaway kernel probes in `.drafts/` (all deleted). No Lean file
was added or edited and nothing was built. No SO-owned path and no HQ file was touched. The landed `KAM/Certificate/Poly`,
`KAM/CertificateSharp` and C7's `composePruned` were only read, or copied verbatim into `.drafts` probes.

## Answer

**Yes, the gap can be closed, but only with two things that do not exist yet:**
- **v2's route B:** FH24's modified Newton step with split derivative bounds, measured torsion and frequency-specific
  small-divisor constants;
- **a packed ("GMP-resident") kernel arithmetic,** so that the kernel cost is big-integer time rather than a fixed
  interpretive overhead per coefficient.

| Configuration | Kernel CPU-h per torus | Outlook |
|---|---:|---|
| v1 theorem + landed checker (today) | ≈ 10⁷ | not feasible |
| v1 + packed arithmetic | 4·10⁴–2·10⁵, every product blocked 35–70× | not feasible in practice |
| v2 route B + per-slot checker (D34-like), box layout | 1.0–3.3·10⁴ (up to ×20, see calibration), 1–3.5 TB of advice | cluster, data-bound |
| v2 route B + per-slot checker, ideal sparse layout | 1.8–6.9·10³ | cluster |
| **v2 route B + packed arithmetic** | **34–351** | **this machine, days** |
| v2 hybrid L6 (estimate) + packed arithmetic | 6–19 | this machine, hours |

- **Most striking milestone feasible now:** LG00's secular SJS model. It is lunar-class (an estimate, to be scouted)
  and would be the first formally verified KAM torus of a planetary model. A GLS17-type secular model comes next.
- **The recommended path** is §8 of the document: LG00 scout → route B in SHARP-PLUS → a packed-arithmetic probe
  package → chart and frequency → GLS17-type → FH25.

## Files (new)

- `docs/explorations/sjs-feasibility.md`: the deliverable. It contains the gap table (§1), theorem (§2), representation
  (§3), normalization (§4), kernel (§5), compute (§6), milestones (§7), path (§8), caveats (§9) and reproduction (§10).
- `scripts/sjs/sjs_freq.py`: Diophantine infima and S(ω, δ) for FH25's frequency (fibered exact sums plus a tail
  bound).
- `scripts/sjs/sjs_support.py`: the support model from FH25 Fig. 3 decay (cross-polytope, strip weight, threshold → L
  → S).
- `scripts/sjs/sjs_model_support.py`: FFT of the first-order planar SJS perturbation in Delaunay angles. It gives the
  true support against the product model, and the boxes in the Delaunay and adapted frames.
- `scripts/sjs/sjs_thresholds.py`: v0, v1 and SHARP-PLUS route B on FH's data, with v1, classical and
  frequency-specific c_R, k stages, and `--geff`.
- `scripts/sjs/sjs_cost.py`: item 5 (CPU-h, declarations, advice, per-shard limits, lunar calibration).
- `scripts/sjs/kernel_probe_gen.py`, `kernel_probe_run.py`, `kernel_probe_summary.py`, `jet_counts.py`: item 4,
  written by the kernel subagent.
- `scripts/sjs/lit/{fh24consts,fh25run,sens,divsum}.py`, `shells{300,1500}.npy`: the FH24 Appendix B re-evaluation,
  by the literature subagent, moved from the session scratchpad with paths made relative.
- `scripts/sjs/results/`:
  - `sjs_freq.json`, `S3_cache.json`, `sjs_model_support_256.json`;
  - `sjs_thresholds.{json,log}`, `sjs_thresholds_geff.log`;
  - `kernel_probes.{md,json}`, `kernel_probes_raw.jsonl` (raw probe records), `jet_counts.json`;
  - `sjs_cost.{json,log}`.
- `docs/campaign/handoffs/SJS-FEAS.md`: this handoff.

Commits: f8205119, 49920580, 37596106 and the handoff commit.

## Approach

- **Item 1 (theorem).**
  - A literature subagent re-evaluated FH24's Theorem 2.18 constants (Appendix B, Tables 1–4) on FH25's data, which
    explains 10⁻³⁸ / 10⁻⁴⁴ term by term (§2.1).
  - I ran our mirrors on the same data, importing SHARP-PLUS's `thresholds.py`, `thresholds_v2.py` and
    `benchmark_fh24.py` read-only from the `sharp-plus` worktree (§2.2).
- **Item 2 (representation).** A first-order model of the true Hamiltonian's Fourier content (d'Alembert structure,
  frames) and an analysis of reversibility and charts.
- **Item 3 (normalization).** An analysis only (§4).
- **Item 4 (kernel).** A kernel subagent generated synthetic Lean probes of the landed packed product, per-coefficient
  passes, and `Slp.compose` against C7's `composePruned`. It ran them one at a time under `nice -n 5`, fitted them and
  extrapolated. I integrated the results.
- **Item 5 (compute).** `sjs_cost.py` combines items 1, 2 and 4.
- **Item 6 (milestones).** From the literature subagent's reading of LG00, LG07, GLS09, GLS17 and FH25.

## Checks run and their output

- `python3 -I scripts/sjs/sjs_freq.py`:
  - inf |k|₁^τ|k·ω| = 1.8501·10⁻⁵ at k = (0, 0, 1) for τ = 2, 2.4 and 3 (|k|₁ ≤ 2000);
  - near resonance 2ω₁ − 5ω₂ = −0.00121;
  - S(ω, ρ/6) = 2.77·10¹², Γ_spec/Γ_classical = 10^−5.4 (ρ/12: −5.7; ρ/24: −5.9).
- `python3 -I scripts/sjs/sjs_thresholds.py`, log₁₀ threshold (τ = 2 / 3, FH γ and numerical γ):

  | Theorem | Range |
  |---|---|
  | v0 | −535…−550 |
  | v1 | −123.3…−140.3 |
  | route B with v1's c_R | −55.1…−62.8 |
  | route B with classical c_R | −51.1…−57.5 |
  | route B, frequency-specific (2 stages) | −48.5…−54.1 |
  | + frequency-specific tail | −46.5…−52.1 |

  k = 6 and 10 stages give no gain (binding: "tail decay"). `--geff`: −44.2 (τ = 2), −43.8 (τ = 3).
- `python3 -I scripts/sjs/lit/fh25run.py`:
  - uniform ĉ_R: η^L < 6.9·10⁻⁴⁷, η^N < 6.3·10⁻⁵⁷;
  - sharp c_R with 10 Iterative-Lemma steps: 10^−37.1 / 10^−45.9 (FH25 report 10⁻³⁸ / 10⁻⁴⁴).
- `sens.py`: σ = 1.01·norm gives 10^−32.7 / 10^−42.7. c_D²Xh enters linearly: ×100 moves the threshold by 2
  orders.
- `python3 -I scripts/sjs/sjs_model_support.py 256`:
  - product model / true support (trusted counts) = 14.1, 12.7, 11.8, 11.1 at ρ = 0 (L = 6–12), 11.1, 9.9, 8.7 at
    ρ = 0.05, and 6.7 at ρ = 0.1;
  - box/S = 46 in Delaunay angles, about 10 in the frame (k₁, k₂, m − k₁).
- **Kernel probes** (`results/kernel_probes.md`):
  - **Landed packed product:** 4.1 / 9.6 / 61.6 s at S = 225 / 441 / 961, t ≈ 1.3·10⁻⁴ S^{1.9±0.3} s.
  - **Prototype per-slot route:** 1.0 ms and 82 kB per advice slot, 1.4 ms and 260 kB per factor term.
  - **GMP:** 6.6 ns per bit.
  - **Model ops:** 1.26 ms and 220 kB per term.
  - **Negative control** (one advice slot +2) rejected.
- **C7** (S = 441 / 961):
  - `composePruned` 8.0 / 24.0 s, against 8.5 / 24.5 s for one shared compose and 7.8 / 24.5 s for two composes in
    one declaration: no gain;
  - separate declarations 11.2 / 31.2 s;
  - `liveSet` + `pruneOk` 17.5 s, 5.9 GB on the lunar program, and they fail on a 2 860-op program.
- `python3 -I scripts/sjs/sjs_cost.py`: the table of §6. Lunar calibration 0.65 CPU-h against tier P's 7.5–14.5
  (ratio 11–22, unresolved).
- `sh scripts/lint_sources.sh` (exit 1, nothing from this branch, which adds no Lean file):
  - `check_lean_modules: PASS (1472 Lean files, 0 comparator configurations)`;
  - `FROZEN-ANCHOR GUARD OK`;
  - the ABI step failed: `object file '…/.lake/build/lib/lean/KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.olean'
    … does not exist`. This is the known missing frozen olean in worktrees; SHARP-C7 hit the same. It writes a scratch
    file under `.lake/abi-scratch/`. The worktree already had `.lake/packages`, so nothing was fetched.
- `#print axioms`: not applicable. No Lean declaration was added. The probes were throwaway `.drafts` files, with no
  `maxHeartbeats` or `maxRecDepth` override.

## Uncertainties

- **Thresholds** come from Python mirrors of unformalized designs:
  - SHARP-PLUS's route B, read from its worktree as of today;
  - integer τ only;
  - FH's norms reused, with the unreported c_Th and c_DTh guessed;
  - the frequency-specific tail extrapolated;
  - `--geff` an emulation.
  - The hybrid L6 numbers (−23…−26) are an analogy with R1, not a computation.
- **Support.**
  - The d'Alembert ratio 7–14 is measured on the first-order Hamiltonian model, not on FH's torus; 7 is used.
  - The adapted-frame box ratio 10 was measured at L ≤ 12.
  - L = −log₁₀T + 6 was calibrated only against FH's grid.
- **Kernel.**
  - Single runs at load 12–14 (±30 %); fits on 3–7 points.
  - The per-slot route is a prototype without soundness proofs.
  - The packed (GMP-resident) algebra is hypothetical, its memory factor (4–8× the factor size) was not measured at
    10¹⁰ bits, and its Lean cost (3–6k lines) is an estimate.
  - The 11–22× gap between the demanded-work model and tier P is unresolved.
  - The decode cliff and the `toMants` superlinearity are measured, not explained.
- **Operation counts** for SJS (60–150 full products, 500–2000 ops) are hand estimates.
- **Not costed:** generating the numerical torus (FH25-scale numerics); an explicit Diophantine frequency (its
  certified γ may be weaker than 1.85·10⁻⁵); the Lean work of route B.
- **The LG00 milestone cost** (1–100 CPU-h) is an estimate. Its threshold under v1 was not computed.

## Suspected errata (pinned sources) and deviations

- **E1. FH24** (arXiv:2304.10205v1), Lemma 2.14, p. 14.
  - c_R(δ) = γδ^τ(2^d Σ e^{−4π|k|δ}/|k·ω|²)^{1/2} lacks the factor (2π)⁻² that ĉ_R includes, since
    u_k = −v_k/(2πi k·ω).
  - ĉ_R = (2^{d+1−2τ}ζ(2, 2^τ)π^{−2τ−2}Γ(2τ+1))^{1/2} carries 2^{d+1−2τ}, while the derivation gives 2^{d−1−2τ}.
  - The middle line of the chain carries π^{−2τ} and the last π^{−2τ−2}.
  - So the printed chain c_R(δ) ≤ c_R(δ, m) ≤ ĉ_R is internally inconsistent. The printed ĉ_R is still a valid,
    conservative bound (the corrected one is ĉ_R/2).
  - Found independently by the literature subagent; it agrees with E1 in SHARP-PLUS's
    `scripts/apost_sharp/benchmark_fh24.py`.
- **E2. FH24 (3.72).** N^⊤ = B L^⊤ J^⊤, so the bound on (N̄ − N)^⊤ needs σ_{L^⊤} and C_{ΔL̄^⊤}; the table prints σ_L
  and C_{ΔL̄}. This is SHARP-PLUS's E2, listed for completeness; I did not re-derive it.
- **E3. FH25** (arXiv:2403.10152), Section 5 and Appendix A.
  - It chooses δ = ρ/6, while Theorem A.1 (FH24 Theorem 2.18) requires δ ∈ ]0, ρ/6[. This is harmless numerically,
    but as printed it lies outside the hypothesis.
  - It uses c_Th and c_DTh (and ν, ϰ, κ, the bite schedule) without reporting them, so the thresholds cannot be
    reproduced exactly. We guessed c_Th = 2c_DXh and c_DTh = 2c_D²Xh.
- **Conventions, not a defect.**
  - FH25 uses 2π-periodic angles and FH24 1-periodic ones, so the transport of ĉ_R (0.0653 → 33.8) is left to the
    reader.
  - FH25's γ = 1.69·10⁻⁶ is 11× below the numerical infimum because they certify a non-explicit nearby vector.
- **Deviation 1 (memory budget).** One probe exceeded the brief's 8 GB: a landed `checkShard` at S = 10 201 peaked at
  9.9 GB RSS, and the series was stopped there. The landed decode micro-probe at n = 3 000 reached 7.6 GB in 403 s.
  Every other probe stayed under 8 GB and took minutes.
- **Deviation 2 (read-only import).** The thresholds import SHARP-PLUS's mirrors read-only from another worktree
  (`KAM_V2_DIR`, default `/home/scott/KAM-dev-worktrees/sharp-plus/scripts/apost_sharp`). Nothing there was modified.
- **Deviation 3 (applications study not edited).** `docs/explorations/striking-applications.md` §9 still says
  "infeasible". It was not edited (additive rule). The new document supersedes its verdict and costs; a cross-link is
  the orchestrator's call.

## Suspected defects in landed code (SO-owned; not touched)

- `CertPoly.weightedNormUp` and `cornerSumUp` (C1's `cornerLeq`) use `foldr`. `decide +kernel` fails ("failed to
  reduce", deep recursion) at S = 10 201.
- `CertPoly.toMants` is superlinear: 1.7, 6.5 and > 59 ms per term at S = 961, 3 025 and 10 201.
- The landed `intSlotsBound` decode has a cliff: 3.6 s at 4 000-slot windows, 403 s and 7.6 GB at 6 000.
- `shardFits` re-flattens `A.take (s+1)` for every shard, which makes the landed full check quadratic.
- C7's `liveSet` and `pruneOk` are quadratic in program length and fail at about 3 000 ops.

## Suggestions for the orchestrator

- **SHARP-PLUS.** Use Γ_spec (the frequency-specific constant) instead of γδ^κ in route B's weighted-error weight.
  That is +2.3 to +8.3 orders on SJS, enough to reach FH24's own level. More frequency-specific stages give nothing
  until this is done.
- **New probe package: packed arithmetic.** Measure in the kernel, at S = 10⁵–10⁶:
  - a packed-resident add;
  - a product with rounding by mask and compare (no advice);
  - a weighted ℓ¹ norm by one product with a weight table;
  - a sign split.

  This decides the architecture for every large client, not only SJS.
- **New scout: SJS-LG00.** In Python: LG00's secular polynomial, its tori in Cartesian secular variables, and
  `optimize.py` under v1 and v2.
- **C7.** It gives no kernel gain, at any size, inside one declaration. If kept for native use, `liveSet` needs a
  near-linear rewrite before it meets programs of planetary size.
