# APOST-SHARP-V2-HYBRID: the certified first step (package SHARP2-HYBRID)

30 October 2026. Branch `sharp-hybrid` (from `sharp-v2` at f7bd6712). Design work: blueprint, signatures (a `.drafts`
probe), Python. No Lean proof, no kernel test. Every number comes from `scripts/apost_sharp/` (untrusted design tooling,
double precision). The numbers of §4 are computed in the norms of the enclosures specified in §3, on sampled grids; they
are design numbers, not certificates.

**Contents.** §0 summary; §1 the decision (restart, additive step); §2 the mathematics; §3 the certifier side; §4 the R1
numbers; §5 Lean signatures and package split; §6 risks; §7 reproduction; §8 the audit findings this answers.

## 0. Summary

- **The theorem form (§2).** The hybrid is a *restart*: apply a proved v2 branch theorem to the new torus
  K₁ = K + ΔK, then transfer its conclusion back to K (Proposition `bp:p2s2hc:restart`).
  - Every hypothesis of the restarted theorem for K₁ follows from explicit bounds by four transfer lemmas
    (`bp:p2s2hc:struct`, `:error`, `:frames`, `:torsion`; iso `bpI:p2s2hc:errors`, `:torsion`). The bounds are on ΔK,
    on the linearised new error Ẽ = E + DX_h(K)ΔK − DΔK·ω, and on data of K that the checker already certifies.
  - The new error is |E₁| ≤ |Ẽ| + (M₂/2)|ΔK|² (Taylor; no composition of h with K₁).
  - Theorem `bp:p2s2hc:g1` concludes the frozen body; Corollary `bp:p2s2hc:frozen` takes the minimum with the existing
    routes, by cases. It is never worse because the plain branch remains available; the transfer formulas are not claimed
    to reproduce a route at ΔK = 0 (AUDIT-HYBRID-1, F3).
  - Soundness never uses that ΔK solves the cohomological equations. The producer computes ΔK; the kernel divides by no
    small divisor and needs no `cohSolve`.
- **The certifier side (§3).** Beyond today's checks of K, the kernel needs one new arithmetic primitive, a product of
  models (DX_h∘K times ΔK), plus weighted norms of a polynomial and the existing engines at the restart numbers.
  - The composition (exp witnesses) is run once, on the coarse K, at the accuracy of the final error. Frames, Gram and
    torsion models run on the coarse K only.
  - Cost estimate, package split and the placement of kernel tests are in §3 (R1-scale tests go to `kernel-tests/`,
    unbuilt).
- **The R1 numbers (§4).** These are floating planning numbers in the enclosures' intended norms, not certificates
  (AUDIT-HYBRID-1, F2). The primary experiment uses the checker's actual finite inputs: a finite dyadic embedding K̂ and a
  finite dyadic step ΔK̂, with every bound recomputed from them (§4.2, F1). On these finite R1 candidates, iso route A′:
  - the plain v2's floating test passes from L = 15 (Û 174, P̂₂ 310 terms, residual 4.6·10⁻¹², threshold 10^{−10.95});
  - the hybrid's passes from **L = 8 (Û 46, P̂₂ 73 terms, residual 3.9·10⁻⁶, margin +0.34)**, a planning scale of about
    **10^{−5.25}**;
  - route B's passes from L = 9.

  The best restart strip is ρ₁ = ρ (no strip loss). The analytic-graph experiment gives the same scale (≈ 10^{−5.28}, §4.3).
  On R1's own 10⁻⁷⁹ residual shape (formal) the hybrid gives 10^{−3.80} at ρ₁ = ρ − 3δ₀; the earlier heuristic gave −4.4.

  The remaining binding terms are the restarted theorem's own threshold (route A′'s cap sum `Tab`) and the quadratic
  Newton residual Ẽ (≈ 0.34e² in ℓ¹, 2.2× the directly computed sup). The Taylor remainder is 10⁻³ of e₁, every transfer
  increment ≤ 4.4·10⁻⁴ relative, and the displacement 5.7·10⁻⁸ (§4.5).
- **Lean (§5).** The signature probe elaborates against `sharp-v2` (785 lines, 52 declarations, 15 `sorry` targets, 9 s,
  3.6 GB peak); every target was checked against its intended proof (§5.2). The implementation is split into four
  packages C8a–C8d (§3.4): about 5k Lean lines, every Lean process under 8 GB, R1-scale tests only in `kernel-tests/`.
- **An observation on R1 (§4.6).** The ordinary torsion average is sampled as nearly singular (|⟨T⟩⁻¹| ≈ 8·10¹⁹); the
  design package bounds only the bordered inverse (0.584). It therefore supplies only isoenergetic applicability, and the
  "fixed-frequency" R1 rows are formal scalar experiments. Exact singularity is not claimed (AUDIT-HYBRID-1, F4).

## 1. The decision

### 1.1 Restart, not an engine stage

There are two ways to measure the first step.

| | (a) Measured stage 0 inside the engine (the ℓ¹-entry way, B10) | (b) Restart (chosen) |
|---|---|---|
| What is proved | the engine with special stage-0 constants | the frozen conclusion of a proved theorem, transferred |
| Needs the step identities | yes (E_red, E_sym, the Newton error identity) | no |
| ΔK must be a Newton step | yes | no: any trigonometric polynomial |
| Restart strip | fixed: ρ − 3δ₀ | free: ρ₁ ∈ (ρ∞, ρ₀] |
| Which theorems | one engine | any theorem concluding the frozen body (v1, A, A′, B, ℓ¹ entry) |
| Lean | inside the engine | a corollary of proved branch theorems plus transfer lemmas |

The restart loses nothing against (a):
- For ρ₁ = ρ₀ − 3δ₀ (and ρ₀ − ρ∞ ≤ 6), the restarted schedule *is* the original schedule from stage 1 (AUDIT-B10D-1 F5).
- The restart also allows ρ₁ = ρ₀. On R1's truncated candidates (finite §4.2 and analytic §4.3) this is the measured
  optimum: a measured ΔK needs no strip loss.
- The caps of K₁ enter as the restarted run's initial values; its budgets are fresh. The frozen ball and |DK| budgets are
  reduced exactly by the step increments (μ₁ ≤ μ − 2 max{d₀, d₁}, `bp:p2s2hc:struct`). The internal caps and their budgets
  are free parameters of any run.

### 1.2 The additive step

- The step is additive, ΔK = Lξᴸ + Nξᴺ for the Newton correction (the form of route A), even when the restarted run is
  route B. The restart accepts any K₁; the form of the step affects only the size of Ẽ.
- Route B's step (K + Nξᴺ)∘(id + ξᴸ) would need a certified composition of models with a shifted argument, plus its Taylor
  remainder in θ. The brief's "composition K̃∘(id + ξᴸ) needs a certified composition/remainder" is exactly that. It is not
  needed: the measured new error of the additive step is already second order, sup|E₁| ≈ 0.57(sup|E|)² on R1's truncations
  (§4.2). The true Taylor remainder is 10⁻⁶ of it (its bound (M₂/2)d₀² is 10⁻³), and the binding part is Ẽ itself.

### 1.3 Why not just certify a better candidate

K₁ is itself an explicit polynomial, so one could make it the certificate's embedding (survey of the certifier, §3). That
needs its own exp witnesses, the composition of h with K₁, and the frame, Gram and torsion models of K₁, all at K₁'s
support. The hybrid runs the composition once, on the coarse K, at the accuracy of e₁. Its frame models are those of the
coarse K. K₁ enters only through Ẽ (linear in ΔK) and through norms of ΔK. §3.3 quantifies the difference.

## 2. The mathematics

Blueprint `blueprint/parts/p2s2-hybrid-cert.tex` (track K, labels `bp:p2s2hc:*`) and
`blueprint-I/parts/p2s2-iso-hybrid-cert.tex` (track I, labels `bpI:p2s2hc:*`). Driver files `blueprint/sharp2-hybrid.tex`
and `blueprint-I/sharp2-hybrid.tex`.

- **Standing data** (`bp:p2s2hc:standing`):
  - the frozen hypotheses and refined data of K on T_{ρ₀};
  - a step ΔK, holomorphic on T_{ρ₀}, 1-periodic and real;
  - a restart strip ρ₁ ∈ (ρ∞, ρ₀] and a restart margin μ₁ ∈ (0, μ).
- **Step bounds** (S1)–(S7) (`bp:p2s2hc:bounds`). Each bounds an explicit object:
  - |ΔK| on T_{ρ₁} (d₀ < μ), on T_{ρ∞} (d∞) and on ℝⁿ (d₀^ℝ);
  - |DΔK| and |(DΔK)ᵀ| on T_{ρ₁} and on ℝⁿ;
  - |Ẽ| ≤ ℓ_E on T_{ρ₁};
  - |DE|, |Ω_K| (K's local torsion data) and |Ω_{K₁}| on the torsion strip T' = T_{ρ₁−δ₀'} and on ℝⁿ.

  Iso adds |ε̃| ≤ ℓ_H for the linearised energy error ε̃ = ⟨H∘K⟩ − E₀ + ⟨DH(K)ΔK⟩, and |Δs||ω*| ≤ d_ω with ν₁ = ν − d_ω > 0.
- **Restart** (`bp:p2s2hc:restart`, `bpI:p2s2hc:restart`). Proved in the probe: `concl_restart`, `iconcl_restart`.
  - Suppose the frozen conclusion holds for K₁ with (μ₁, σ_{K,1}), closeness D₁ (and frequency closeness D₁^ω), and that
    d∞ + D₁ ≤ μ/2 and σ_{K,1} − μ₁/2 ≤ σ_K − μ/2.
  - Then the frozen conclusion holds for K with closeness d∞ + D₁ (and frequency closeness d_ω + D₁^ω).
- **Transfer.**
  - The new torus: holomorphic, primary, real, B_{μ₁}(K₁) ⊂ 𝔅, |DK₁| ≤ ℓ + d₁.
  - The new error: |E₁| ≤ ℓ_E + (M₂/2)d₀² (`KAM.taylor_iteratedFDeriv`). Iso: Ẽ at s₁ω* and the energy
    |⟨H∘K₁⟩ − E₀| ≤ ℓ_H + (M_{h2}/2)(d₀^ℝ)².
  - Frames, by Neumann:
    - g = ℓᵗd₁ + d₁ᵗℓ + d₁ᵗd₁, β₁ = β/(1 − βg), b = β²g/(1 − βg);
    - n_Δ = β₁d₁ + ℓb, n_Δᵗ = β₁d₁ᵗ + ℓᵗb.
  - Torsion, through the torsion polynomial T = 𝒯_ab + local part (no derivative of a frame enters):
    - Δ_ab = n_Δᵗc_Thν₁ + νᵗc_DTh|ΔK|ν₁ + νᵗc_Thn_Δ;
    - local parts λ₀ (of K) and λ₁ (of K₁, with |DE₁| ≤ ne₁/δ' by Cauchy);
    - sup |T₁| ≤ min{t + Δ_ab + λ₀, ν₁ᵗc_Thν₁} + λ₁;
    - average |⟨T₁⟩⁻¹| ≤ m/(1 − mt_A), with t_A the real-torus increment. Iso: the bordered matrix, adding the column
      Δs ω* and the row DH(K₁)N₁ − DH(K)N.
- **Theorem** (`bp:p2s2hc:g1`, `bpI:p2s2hc:g1`). The transferred initial values feed route R's branch theorem at the
  restart numbers N₁ (strip ρ₁, small-divisor constants at the schedule from ρ₁). `HybOk_R` collects:
  - the margins;
  - the Neumann conditions;
  - route R's numerical condition at N₁;
  - smallness at e₁;
  - the closeness budget.
- **Corollary** (`bp:p2s2hc:frozen`, `bpI:p2s2hc:frozen`): the plain branch or the hybrid branch; the closeness is the
  maximum of the two.

Nothing in the existing blueprint changes. Corollary `bp:p2s2:hybrid` (L6) is superseded by this part: no step identities,
no stage-0 constants.

## 3. The certifier side

### 3.1 What the checker computes

| Item | Object | Norm | Existing primitive | New |
|---|---|---|---|---|
| K's checks | Ham bounds, embedding and ball, Gram witness, torsion and frame majorants, invariance error | as today | all (`checkHamBoundsTrigSplit`, `checkEmbedding`, `gramCheck`, `torsionAvgCheck`, `checkFrameMajorants`, `checkInvariance`) | none |
| ΔK | a `CertPoly` (producer output) | — | `CertPoly` | realness and periodicity are structural (conjugate-symmetric coefficients, integer keys) |
| (S1)–(S4) | ΔK, DΔK on T_{ρ₁}, T_{ρ∞}, ℝⁿ | weighted ℓ¹, `supBound` | `supBound`, `ofDeriv` (exact derivative of a polynomial), `dkModels`-style row sums | none |
| (S5) | Ẽ = E + (DX_h∘K)ΔK − DΔK·ω | weighted ℓ¹ of the model | `invarianceModel` (E), the jet of the composition (DX_h∘K), `ofDeriv`, ω as an interval | **products of models** (16 entries of DX_h∘K times ΔK); sup arithmetic `mul` with advice exists, an ℓ¹ product does not |
| (S6) | DE on T', ℝⁿ | weighted ℓ¹ | `ofDeriv` on the polynomial part | Cauchy for a model's remainder (`rad·n/δ`), about 40 lines. Alternative without it: \|DE\| ≤ ne/δ' from K's error bound |
| (S6), (S7) | Ω_K = DKᵀΩ₀DK, Ω_{K₁} | weighted ℓ¹ | polynomial products (exact) | none; or the defect lemma from \|η^N₁\| |
| Transfer | Definition `bp:p2s2hc:data` | rationals | — | about 30 rational operations |
| Engine | route R's core at N₁ | — | `refinedCoreR` / `routeAV2'` (route A′), the route-B core | none |
| Small divisors | constants at N₁'s bites | — | `SmallDivQ` / `ClassicalQ` | none; for ρ₁ = ρ₀ they are the plain certificate's |
| Iso | ε̃, Δs, bordered increments | — | the energy check, the jet (DH∘K) | the zero mode of DH∘K·ΔK (a product) |

`cohSolve` (C5CORE) is not needed for soundness. It can produce ΔK inside the kernel, but the producer does that better in
floating point; any truncation of ΔK is paid for linearly in Ẽ.

### 3.2 Precision

- Ẽ must be enclosed with a remainder ≤ 10% of the target e₁. Here e₁ ≈ e*(ρ₁) ≈ 1.1·10⁻¹¹ for route A′ iso on R1, so the
  model of E needs rad ≲ 10⁻¹² on T_{ρ₁}. The composition must run at this absolute accuracy although K is coarse; this is the
  accuracy the plain certificate needs for its own final residual (§3.3).
- ΔK is of size ≈ 3·10⁻² e (§4.2). It needs only about 6 significant digits: absolute accuracy 10⁻¹³ at |ΔK| ≈ 10⁻⁷. The
  product (DX_h∘K)·ΔK is low precision.
- The real-torus increments that drive the twist transfer are ≈ 10⁻⁵ of the strip increments for R1's own residual and
  ≈ ½ of them for truncations. In both cases t_A ≤ 7·10⁻⁴ at the passing candidates, and |⟨T^ext⟩⁻¹| moves by ≤ 4.4·10⁻⁴
  relative (§4.2).

### 3.3 Kernel cost at lunar size

**Supports of the finite candidates** (§4.2, AUDIT-HYBRID-1 F1; all embedding components and the witness). Counts are
nonzero coefficients on the full lattice; for the witness and the model of E, the count is the number of terms needed
for a dropped weighted-ℓ¹ mass ≤ 2·10⁻¹² (or 2·10⁻¹³) on T_ρ.

| Candidate | Û | P̂₁ | P̂₂ (with Ĵ) | witness W = e^{4πiÛ} | model of E | ΔK̂ (largest component) |
|---|---:|---:|---:|---:|---:|---:|
| L = 8 (hybrid passes, §4.2) | 46 | 47 | 73 | 101 / 127 | 171 / 213 | 191 |
| L = 15 (plain route A′ passes) | 174 | 175 | 310 | 113 / 139 | 11 / 43 | — |

The earlier analytic-graph sizes (`--sizes`, `r1-sizes.json`: E 176, character 82, ΔK 123 at L = 8) agree with these to
within the change of tolerance rule.

- **The composition costs about the same for both.** The witness needs about 100–140 terms at this accuracy, whatever the
  truncation: it is fixed by the torus's analyticity at the accuracy of the final error.
- **The frame, Gram and torsion models shrink.** They are products of the embedding's components (Û, P̂₁, P̂₂ and their
  derivatives), so their cost scales like the square of those supports: (310/73)² ≈ 18× and (174/46)² ≈ 14× fewer
  operations for the hybrid. They include the Gram witness, N = Ω₀LB, DN, Nᵀ(Ω₀X_N) and the corner majorants.
- **The new items are small.**
  - Ẽ: 16 products of ≈ 100–130-term entries of DX_h∘K with ΔK̂ (≤ 191 terms per component), ≈ 4·10⁵ low-precision
    multiplications. In R1 only
    three entries of DX_h are non-constant.
  - Norms of ΔK, DΔK: linear in 123 terms.
  - Ω_{K₁}: n²·2n products of ≈ 150-term polynomials, ≈ 2·10⁵ multiplications.
  - At ≈ 1 μs per coefficient product these are seconds. That rate is inferred, not measured: it follows from the estimate
    "35–95 s per compose op on an 8.5k-term model" (CERTIFIER-SHARPNESS §4.2), which is about 7·10⁷ products per op.
- **The numerical core at N₁ costs what the plain core costs.** C6L8 measured 6 min and 19.2 GB for R1's route-A′ core
  (`RefinedRefR1`). That is over the machine's 10 GB per-process cap, a design signal for the core (split the per-stage
  `decide`s, round the arithmetic), not for the hybrid. With ρ₁ = ρ₀ the small-divisor bites are the plain certificate's.
- **Net.** Against plain v2 at L = 15, the hybrid removes most of the frame-model cost (up to ≈ 14×), keeps the composition
  and core costs, and adds seconds. These are estimates; no lunar kernel test was run (orchestrator rule, below).

### 3.4 Implementation packages C8a–C8d (SHARP2-HYBRID-FIX)

This is the whole implementation, theorem side and certifier side, as four packages. It replaces the earlier split into
H1–H5 (theorem side) and C8a–C8d (certifier side). Binding rules (orchestrator): every Lean process stays under about
8 GB; only toy-size kernel tests (a few GB at most) live under `KAM/`; any R1-scale test goes to `kernel-tests/`, is not
built, and its expected cost is stated; a killed build is a design signal (split the `decide`, round the arithmetic). Every
file stays under 800 lines.

| Package | Modules (new) | Lines | Lean process budget | Kernel tests | Depends on |
|---|---|---:|---|---|---|
| **C8a**: restart and transfer lemmas | `KAM/Sharp2/Hybrid/Restart.lean` (`G1Concl`, `IG1Concl`, `restart_close`, `concl_restart`, `iconcl_restart`; proved in the probe), `Hybrid/Step.lean` (`IsStep`, `linNewError`, `linNewEnergy`, `step_struct`, `invarianceError_step_le`, `energyAverage_step_le`, `errDerivMat_step_le`), `Hybrid/Frames.lean` (`FrameNum`, `frames_step`), `Hybrid/Torsion.lean` (`dAB`, the M₂ variant of `norm_hamComm_sub_le`, `torsionAB_step_sub_le`, `torsion_step_le`, `torsionAverage_step` with its t_A = 0 case and the integrability from holomorphy, `extTorsionAverage_step`) | 150 + 350 + 350 + 600 ≈ 1.45k | ≤ 5 GB per module. The comparable modules `TorsionRef` and `ModStepB/Frames` are of this size, and the probe of all statements runs at 3.6 GB. | none (pure analysis) | `KAM.Sharp2.TorsionRef`, `KAM.Sharp2.RouteA.Torsion`, `KAM.Strip.Taylor`, `KAM.Strip.Bridges` |
| **C8b**: the hybrid theorems and the minimum | `KAM/Sharp2/Hybrid/Core.lean` (`g1_hybrid_core_R`, `g1_hybrid_core_B`), `Hybrid/Data.lean` (`KData`, `StepNum`, `StepBounds`, transferred values, `RestartA`, `NumA.restart`, `HybOkR`), `Hybrid/G1.lean` (`g1_hybrid_R`, `g1_v2A'_hybrid`), `KAM/Iso/Sharp2/Hybrid/Core.lean` (`iso_g1_hybrid_core_R`), `Iso/Sharp2/Hybrid/G1.lean` (`IsoNum`, `iso_g1_hybrid_R`, `iso_g1_v2A'_hybrid`) | 250 + 300 + 500 + 200 + 550 ≈ 1.8k | ≤ 6 GB per module. Hypothesis plumbing on top of `g1_branch_R`, `g1_branch_B`, `iso_g1_branch_R`; split `G1` modules at the fixed/iso boundary if over budget. | none | C8a; B9 (route A′), B6 (route B), B7 (iso) |
| **C8c**: certifier primitives and the hybrid checker (toy scale) | `KAM/CertificateSharp/Hybrid/ModelMul.lean` (products of models with soundness, combining coefficients before bounding so the Newton cancellation is kept), `Hybrid/Cauchy.lean` (derivative of a model with a remainder), `Hybrid/Step.lean` (ΔK as a `CertPoly`, the model of Ẽ, step norms on T_{ρ₁}, T_{ρ∞}, ℝⁿ, exact Ω_K and Ω_{K₁}), `Hybrid/Check.lean` (transfer arithmetic, the route-A′ core at the restart numbers, `checkHybrid_sound` → hypotheses of `g1_hybrid_R`), `Hybrid/Iso.lean` (ε̃, Δs, bordered increment, `CertifiedTorus` wrapper with disp = max{d∞ + D₁, d_ω + D₁^ω}), `Hybrid/Tests/T2.lean` | 350 + 80 + 450 + 400 + 350 + 120 ≈ 1.75k | ≤ 4 GB per module. The toy test is ≤ 2 GB and seconds (T², about 20 modes, exact ℚ or `CertFixed 64`). | toy T² only, `KAM/` | C8b (soundness targets); C5CORE models; route-A′ certifier (C6L8) |
| **C8d**: R1 production and the R1-scale test | `scripts/apost_sharp/hybrid_producer.py` (from this package's finite pipeline, §4.2: emits K̂ = (ψ + Û, φ, P̂₁, P̂₂), ΔK̂, the witness W = e^{4πiÛ}, the model of E, the restart numbers, in the certifier's format with outward rounding); `kernel-tests/hybrid/R1-*.lean` (**not built**) | ≈ 450 Python; kernel-test files ≈ 400 | Each kernel declaration ≤ 6 GB by construction: one file per stage. (i) Witness and composition check at accuracy 2·10⁻¹³: W ≈ 127 terms (§4.2). (ii) Frames, Gram witness and torsion of K̂: Û 46, P̂₁ 47, P̂₂ 73 terms at L = 8 (full lattice). (iii) Ẽ products and step norms: ΔK̂ ≤ 191 terms per component. (iv) The route-A′ core at N₁, split per engine stage and per small-divisor bite. Unsplit, C6L8's core took 19.2 GB and one bite 18.8 GB, so (iv) must be split before anyone runs it. Expected total: (iv) dominates. | `kernel-tests/` only | C8c; the plain R1 small-divisor constants (reused at ρ₁ = ρ) |

Sum: about 5k Lean lines in C8a–C8c plus the C8d producer and unbuilt tests. Order: C8a → C8b → C8c (`ModelMul` and `Cauchy`
can start at once). The C8d producer can start at once in Python. The C8d kernel tests come last and are not run on this
machine.

**SO wiring.** `CertifiedTorus` is stated for the certificate's own torus c.K, with ‖K∞ − c.K‖ ≤ disp. The hybrid
conclusion is about K = c.K, with disp ≥ max{d∞ + D₁, d_ω + D₁^ω}, so no change of the SO consumer is needed beyond the
wrapper. `checkSoGraph` needs disp < mono·ρ∞ ≈ 1.4·10⁻⁵. The measured d∞ is 5.7·10⁻⁸ at L = 8 (§4.2), far inside it.

## 4. The R1 numbers

`scripts/apost_sharp/hybrid_cert_r1.py`; raw outputs in `docs/campaign/design/hybrid/r1-{finite,trunc,shape,sizes}.json` and
the emitted finite candidate `r1-L8-finite-candidate.json`. These are floating-point planning numbers in the intended norms of
§3's enclosures, computed on sampled grids. They are not certificates (AUDIT-HYBRID-1, F2): aliasing, omitted modes,
coefficient enclosures, rational weight majorants and the model remainders (the 10% allowance) are not checked. "Passes"
below means passes the floating test, and "planning scale" means the residual size at which the floating test crosses
zero. §4.2 (finite candidates) is the primary experiment; §4.3 and §4.4 are the earlier analytic experiments, kept for
comparison.

### 4.1 Method

- **Candidates.**
  - (a′) **Finite candidates (§4.2, AUDIT-HYBRID-1 F1).** The checker's carrier: K̂ = (ψ + Û, φ, P̂₁, P̂₂), with all four
    components finite dyadic trigonometric polynomials, and a finite dyadic step ΔK̂. Everything is recomputed from these
    finite objects.
  - (a) **Truncations of R1, analytic graph (§4.3).** R1's angle function v is cut at |b_k| > 10^{−L}. The graph torus of `r1_norms.py` (rotated
    frame, c = 7/4) is energy-normalised exactly, H∘K ≡ 0. Its residual is in closed form:
    E_L = (0, 0, −cR, −c(1 − p)R), R = D_t p + V_q.
  - (b) **R1's own L = 88 torus.** Its residual is 4·10⁻⁷⁹, far below every threshold. Normalised by e = sup_{T_ρ}|E|, it
    gives the *shape* of a high-accuracy residual. This is a formal scaling model, the setting of the earlier heuristic
    (`step0_actual.py`, `A_MEAS_R1`).
- **The step.** The isoenergetic additive step: the bordered system [[⟨T⟩, ω], [⟨Y⟩, 0]], with ΔK = Lξᴸ + Nξᴺ and
  ω₁ = ω − ξ^ω ω. R1's ordinary ⟨T⟩ is sampled as nearly singular (§4.6), so the fixed-frequency step is not usable for R1.
  The "fixed" rows below use the same step and are formal scalar experiments.
- **Enclosure norms.**
  - e_L = ‖E_L‖_{ℓ¹,ρ}, the norm the certifier's `supBound` computes for the plain theorem.
  - ℓ_E = 1.10·‖Ẽ‖_{ℓ¹,ρ₁}, with 10% reserved for the model remainders.
  - The Taylor term is (M₂/2)‖ΔK‖²_{ℓ¹,ρ₁}, with M₂ = 1.05·1.0342.
  - The increments, |DE|, |Ω_K| and |Ω_{K₁}| are ℓ¹ norms on T_{ρ₁} and ℝⁿ.
  - The transfer is Definition `bp:p2s2hc:data` against the R1 package's caps.
  - The restarted theorem is `thresholds_v2.py`'s route A′ (A7 with L8′, k = 5) or route B (B6 options) at the strip ρ₁,
    for ρ₁ ∈ {ρ, ρ − δ₀/4, ρ − δ₀/2, ρ − δ₀, ρ − 3δ₀/2, ρ − 2δ₀, ρ − 3δ₀}; the best strip is reported.
- **A check of the bound.** For (a), the new error E₁ = X_H(K + ΔK) − D(K + ΔK)ω₁ is also computed directly (difference
  formulas, no cancellation). It verifies that e₁ bounds it and shows how sharp e₁ is.

### 4.2 Finite candidates: the checker's polynomial K̂ and ΔK̂ (AUDIT-HYBRID-1 F1)

`--finite`. For each L:
- **K̂_L** = (ψ + Û, φ, P̂₁, P̂₂), every component a finite dyadic trigonometric polynomial (coefficients rounded to 2⁻⁶⁰),
  the carrier of `CertEmbedding`:
  - Û = (v cut at 10^{−L})/(2π) and P̂₁ = ν + D_tÛ;
  - P̂₂ = P̂₁ + Ĵ, where Ĵ truncates the infinite series J = −P̂₁²/2 − V(q, φ) at weighted tail mass 10⁻³e on T_ρ (e = the
    analytic graph's residual).

  K̂ is not energy-normalised exactly, and its residual is not in closed form. E(K̂) = X_H(K̂) − DK̂·ω is computed from K̂
  itself, and ⟨H∘K̂⟩ − E₀ (E₀ = 0) is its energy error.
- **The step.** It is computed on K̂ (K̂'s frame, torsion and bordered system) and emitted as a finite polynomial ΔK̂: the
  coefficients come from the corner values, truncated at weighted tail mass 10⁻³e² and rounded to 2⁻⁶⁰. K̂₁ = K̂ + ΔK̂ is a
  finite embedding; it is no longer a graph over the angle, since ΔK̂ has a Q₂ component.
- **Every bound is recomputed from K̂ and ΔK̂:**
  - ‖ΔK̂‖, ‖DΔK̂‖ and its transpose as exact coefficient sums (finite polynomials);
  - Ẽ, E₁, DE, Ω_{K̂} and Ω_{K̂₁} on the shifted grids;
  - ⟨H∘K̂⟩ − E₀ + ⟨DH(K̂)ΔK̂⟩;
  - K̂'s own sampled caps.
- **Emitted candidate.** `docs/campaign/design/hybrid/r1-L8-finite-candidate.json`: Û, P̂₁, P̂₂ and the four components of
  ΔK̂ as integers at scale 2⁶⁰, plus ξ^ω and E₀.

Iso route A′; the best restart strip is ρ₁ = ρ in every row. Plain threshold 10^{−10.95}.

| L | Û / P̂₁ / P̂₂ terms | ΔK̂ terms (Q₁, Q₂, P₁, P₂) | e (ℓ¹, T_ρ) | energy error | plain margin | e₁ (ℓ¹ bound) | E₁ direct sup | hybrid margin |
|---:|---|---|---:|---:|---:|---:|---:|---:|
| 6 | 20 / 21 / 47 | 89 / 72 / 111 / 119 | 9.31·10⁻⁵ | 8·10⁻¹⁷ | −6.91 | 3.47·10⁻⁹ | 1.64·10⁻⁹ | −2.50 |
| 7 | 32 / 33 / 61 | 109 / 92 / 141 / 159 | 1.47·10⁻⁵ | 7·10⁻¹⁸ | −6.11 | 8.19·10⁻¹¹ | 3.87·10⁻¹¹ | −0.86 |
| **8** | 46 / 47 / 73 | 127 / 60 / 149 / 191 | 3.93·10⁻⁶ | 1·10⁻¹⁷ | −5.54 | 5.19·10⁻¹² | 2.37·10⁻¹² | **+0.34** |
| 9 | 58 / 59 / 83 | 153 / 76 / 189 / 239 | 1.07·10⁻⁶ | 5·10⁻¹⁸ | −4.97 | 4.10·10⁻¹³ | 1.93·10⁻¹³ | +1.44 |
| 10 | 76 / 77 / 101 | 181 / 32 / 284 / 289 | 1.32·10⁻⁷ | 4·10⁻¹⁷ | −4.07 | 2.25·10⁻¹⁴ (floor) | 2.06·10⁻¹⁵ | +2.70 |
| **15** | 174 / 175 / 310 | 79 / 0 / 264 / 164 | 4.63·10⁻¹² | 4·10⁻¹⁷ | **+0.39** | 2.44·10⁻¹⁴ (floor) | 1.97·10⁻¹⁵ | +2.67 |

Term counts are nonzero coefficients on the full lattice (Û's 46 terms at L = 8 are the 23 sine terms of v). "Floor" marks
the 2⁻⁶⁰ rounding floor of ΔK̂ in Ẽ, about 2·10⁻¹⁴. The other forms:

| Form | Hybrid passes from |
|---|---|
| route A′ fixed (formal) | L = 8 (+0.58) |
| route B iso | L = 9 (+0.06) |
| route B fixed | L = 9 (+0.14) |

- **The finite candidates agree with the analytic graph** (§4.3) to within 0.06 orders at L ≤ 9: the residual is unchanged,
  and the hybrid margin at L = 8 is +0.34 against +0.28.
- **Planning scale.** log₁₀ e + margin/2 = −5.26, −5.24, −5.25 at L = 7, 8, 9: an admissible residual scale around
  **10^{−5.25}** (iso route A′).
- **Truncation and rounding ledger.**
  - Ĵ: changes the residual by less than 10⁻³ relative, by the choice of its tolerance.
  - ΔK̂: ‖Ẽ‖_{ℓ¹} with ΔK̂ is 8–12% *below* the value with the unrounded step at L ≤ 9. Both are floating estimates; the
    unrounded step's derivative is taken on the shifted grid, the finite one exactly.
  - At L ≥ 10 the 2⁻⁶⁰ rounding of ΔK̂ sets the floor of about 2·10⁻¹⁴ in Ẽ, 10⁻³ of e₁*.
  - The energy error of K̂ is ≤ 10⁻¹⁶; |ε̃| ≤ 2·10⁻¹⁴ at L = 6 and ≤ 10⁻¹⁷ for L ≥ 8.
- **K̂'s sampled caps are R1's** at every L, inside the package's 5% headroom: |DK̂| 1.3025, |L̂ᵀ| 1.3268, |B| 1.8331,
  |N| 1.354, |Nᵀ| 1.3787, sup|T| 3.313, |⟨T^ext⟩⁻¹| 0.5843. The ordinary |⟨T⟩⁻¹| is 6·10¹⁰ to 1.5·10²⁰ (§4.6).
- **At L = 8:**
  - ‖ΔK̂‖_{ℓ¹} on T_ρ = 1.15·10⁻⁷ ≈ 0.03e;
  - e₁ = 5.19·10⁻¹² ≈ 0.34e², 2.2× the directly computed sup;
  - the displacement on T_{ρ∞} is d∞ = 5.7·10⁻⁸;
  - |ξ^ω| = 2·10⁻¹³.
- **Supports for the cost proxy** (all embedding components and the witness, full lattice; tolerance = dropped weighted mass
  on T_ρ):

| Candidate | Û | P̂₁ | P̂₂ (with Ĵ) | witness W = e^{4πiÛ} (2·10⁻¹² / 2·10⁻¹³) | model of E (2·10⁻¹² / 2·10⁻¹³) | ΔK̂ (largest component) |
|---|---:|---:|---:|---:|---:|---:|
| hybrid, L = 8 | 46 | 47 | 73 | 101 / 127 | 171 / 213 | 191 |
| plain, L = 15 | 174 | 175 | 310 | 113 / 139 | 11 / 43 | — |

  - The embedding components shrink 3.8–4.2×, so the frame, Gram and torsion products, quadratic in the supports, shrink
    by roughly 15–18×.
  - The witness and the composition do not shrink (101 against 113 terms).
  - The hybrid adds ΔK̂ (at most 191 terms per component) and a model of E of about 200 terms.
  - These are counts, not kernel measurements.

### 4.3 Analytic-graph truncations (planning experiment; superseded by §4.2)

Here K is the analytic graph of `r1_norms.py` (J not truncated, H∘K ≡ 0) and ΔK is the analytic step on grids. Neither is
the checker's finite input (AUDIT-HYBRID-1 F1). The table is kept for comparison with §4.2.

The plain v2 thresholds are:

| | Iso | Fixed |
|---|---:|---:|
| route A′ | 10^{−10.95} | 10^{−10.71} |
| route B | 10^{−12.33} | 10^{−12.25} |

A margin is log₁₀ of threshold over error; positive means the floating test passes.

| L | v terms | e_L (ℓ¹, T_ρ) | plain margin | e₁ (ℓ¹ bound) | E₁ direct sup | best ρ₁ | e₁* at ρ₁ | **hybrid margin** |
|---:|---:|---:|---:|---:|---:|---|---:|---:|
| 5 | 7 | 4.05·10⁻⁴ | −7.55 | 6.93·10⁻⁸ | 3.05·10⁻⁸ | ρ | 10^{−11.02} | −3.86 |
| 6 | 10 | 9.31·10⁻⁵ | −6.91 | 3.82·10⁻⁹ | 1.64·10⁻⁹ | ρ | 10^{−10.96} | −2.54 |
| 7 | 16 | 1.47·10⁻⁵ | −6.11 | 9.25·10⁻¹¹ | 3.90·10⁻¹¹ | ρ | 10^{−10.95} | −0.91 |
| **8** | **23** | 3.93·10⁻⁶ | −5.54 | 5.99·10⁻¹² | 2.49·10⁻¹² | ρ | 10^{−10.95} | **+0.28** |
| 9 | 29 | 1.07·10⁻⁶ | −4.97 | 4.67·10⁻¹³ | 1.93·10⁻¹³ | ρ | 10^{−10.95} | +1.38 |
| 10 | 38 | 1.32·10⁻⁷ | −4.07 | 6.95·10⁻¹⁵ | 2.75·10⁻¹⁵ | ρ | 10^{−10.95} | +3.21 |
| 11 | 47 | 1.30·10⁻⁸ | −3.06 | 6.08·10⁻¹⁷ | 2.53·10⁻¹⁷ | ρ | 10^{−10.95} | +5.27 |
| 12–14 | 56–74 | 1.8·10⁻⁹–4.2·10⁻¹¹ | −2.19 to −0.57 | ≈ 10⁻¹⁸ (floor) | | | | ≥ +7 |
| **15** | **87** | 4.57·10⁻¹² | **+0.39** | ≈ 10⁻¹⁸ (floor) | | | | ≥ +7 |

For L ≥ 12 the computed Ẽ is at the double-precision floor (≈ 10⁻¹⁸); the margins there are unresolved numerical
estimates, not lower bounds.

- **The plain floating test first passes at L = 15 (87 terms); the hybrid's at L = 8 (23 terms).**
- **The planning scale is about 10^{−5.28} for route A′ iso.** Each row with |margin| < 2 gives log₁₀ e_L + margin/2 =
  −5.29, −5.27, −5.28, since e₁ ∝ e_L². The other forms:

  | Form | Hybrid planning scale | Plain threshold |
  |---|---:|---:|
  | route A′ iso | 10^{−5.28} | 10^{−10.95} |
  | route A′ fixed (formal) | 10^{−5.16} | 10^{−10.71} |
  | route B iso | 10^{−5.96} | 10^{−12.33} |
  | route B fixed | 10^{−5.92} | 10^{−12.25} |

  The minimum with the routes (Corollary `bp:p2s2hc:frozen`) takes route A′.
- **The best restart strip is ρ₁ = ρ in every certified row.** At L = 8, ‖Ẽ‖_{ℓ¹} falls only from 5.44·10⁻¹² (ρ₁ = ρ) to
  3.25·10⁻¹² (ρ₁ = ρ − 3δ₀), 0.22 orders, while the restarted threshold loses about one order. The decay rate corresponds to
  a weight at |k|₁ ≈ 10; the residual of a truncation sits at low modes. A measured step needs no strip loss.
- **The bound against the direct computation.** e₁ ≥ E₁ (direct sampled sup) in every row. The ratio is about 2.4, the ℓ¹/sup
  factor of Ẽ; it costs 0.19 orders in the planning scale.
- **At L = 8 (ρ₁ = ρ):**
  - ‖ΔK‖_{ℓ¹} = 1.15·10⁻⁷ ≈ 0.03e;
  - ‖Ẽ‖_{ℓ¹} = 5.44·10⁻¹² ≈ 0.35e²;
  - the Taylor term (M₂/2)d₀² = 7·10⁻¹⁵, about 10⁻³ of e₁ (the true remainder is 5·10⁻¹⁸);
  - |Ω_{K₁}| = 7·10⁻¹³ against |Ω_K| = 2.6·10⁻⁶ (the step makes the torus Lagrangian to second order);
  - |ξ^ω| = 2·10⁻¹³, and ε̃ = 3·10⁻²⁷ (zero up to rounding: H∘K ≡ 0 and the bordered row);
  - the displacement on T_{ρ∞} is d∞ = 5.7·10⁻⁸ (SO needs ≤ 1.4·10⁻⁵).
- **Transfer at L = 8:**

  | Quantity | K | K₁ |
  |---|---:|---:|
  | margin | μ = 0.00625 | μ₁ = 0.00624 |
  | \|B\| | | +5.2·10⁻⁵ |
  | \|N\| | | +8.3·10⁻⁵ |
  | sup\|T\| | 3.4787 | 3.4801 |
  | \|⟨T^ext⟩⁻¹\| | 0.61320 | 0.61347 |
  | t_A | | 7·10⁻⁴ |

  The restarted threshold equals the plain one to 0.01 orders.

### 4.4 R1's own residual (formal scaling model)

R1's L = 88 residual, normalised by e = 4.09·10⁻⁷⁹ (grid 1024 × 256). Every step object is scaled to a residual of size e
with the same spectrum: ΔK ∝ e and Ẽ ∝ e² (Ẽ = P·E_lin at leading order). A = 1.10‖Ẽ^‖_{ℓ¹,ρ₁} + (M₂/2)‖ΔK^‖²_{ℓ¹,ρ₁}, and
the planning scale is the largest e with A e² ≤ e₁*(ρ₁; increments at e), found by a fixed-point iteration and a final
log-bisection. It agrees with (log₁₀ e₁* − log₁₀ A)/2 to 0.01.

| ρ₁ (strip loss) | A | route A′ iso | route A′ fixed | route B iso | route B fixed |
|---|---:|---:|---:|---:|---:|
| ρ | 22.0 | −6.15 | −6.03 | −6.84 | −6.80 |
| ρ − δ₀/2 | 2.16 | −5.70 | −5.57 | −6.38 | −6.34 |
| ρ − δ₀ | 0.220 | −5.26 | −5.13 | −5.94 | −5.90 |
| ρ − 2δ₀ | 2.61·10⁻³ | −4.47 | −4.29 | −5.11 | −5.07 |
| **ρ − 3δ₀** | 4.11·10⁻⁵ | **−3.80** | **−3.57** | **−4.38** | **−4.34** |

Binding: route A′ `sum Tab` (fixed) and the tail E (iso, at ρ₁ ≤ ρ − δ₀); route B the tail decay.

- **This residual favours a strip loss.** 90% of its mass is at |k|₁ ≈ 100–176 (`step0_actual.py`). Ẽ falls by a factor of 60–100 per δ₀, and
  ‖DΔK^‖_{ℓ¹} = 41 per unit e on the full strip. The largest tested loss (3δ₀) is the best; larger losses may help this
  shape further.
- **Against the earlier heuristic** (`thresholds_v2.hybrid`, A_meas = 7.28·10⁻⁴: a sampled, bound-structured
  leading-order sup on T_{ρ−2δ₀}, restart at ρ − 3δ₀, increments neglected):

  | | Iso | Fixed |
  |---|---:|---:|
  | route A, heuristic | −4.42 | −4.18 |
  | route A′, enclosures | −3.80 | −3.57 |
  | route B, heuristic | −5.01 | −4.97 |
  | route B, enclosures | −4.38 | −4.34 |

  The enclosure numbers are *better*, by 0.6. The heuristic measured Ẽ on T_{ρ−2δ₀} but restarted at ρ − 3δ₀, and its
  bound-structured form, |P|·2|E_lin| + …, is coarser than ‖Ẽ‖_{ℓ¹} at the restart strip itself. Every increment is now
  included. At the best strip they change |T| by at most 0.25%, |⟨T^ext⟩⁻¹| by at most 3·10⁻⁴
  relative, and μ by at most 2·10⁻⁵.
- **This is a property of a residual that is 10⁻⁷⁹ in size; R1 itself needs no hybrid.** The realistic planning number is
  §4.2's (finite candidates).

### 4.5 The planning scale and the remaining binding term

**The R1 planning scale.** These are floating tests in the intended norms; certification requires finite inputs, outward
enclosures and all restarted hypotheses checked by the kernel (AUDIT-HYBRID-1, F2).

| Setting | Hybrid (iso, route A′) | Plain v2 (iso, route A′) | What a certificate needs |
|---|---:|---:|---|
| **R1's finite candidates (§4.2)** | **planning scale ≈ 10^{−5.25}**: floating tests pass from L = 8 (Û 46, Ĵ 73 terms) | 10^{−10.95}: pass from L = 15 (Û 174, Ĵ 312 terms) | the composition at accuracy ≈ 10⁻¹² in both; frames on the coarse K̂ |
| R1's truncations, analytic graph (§4.3) | ≈ 10^{−5.28} | 10^{−10.95} | — |
| R1's own residual shape (§4.4, formal) | 10^{−3.80} (ρ₁ = ρ − 3δ₀) | 10^{−10.95} | — |

On the finite candidates, route B passes from L = 9, one L later than route A′; the minimum with the routes takes A′. The
fixed-frequency numbers are formal for R1 (§4.6).

**The remaining binding term.** On a finite candidate,

  e₁ = 1.10‖Ẽ‖_{ℓ¹,ρ} + (M₂/2)d₀² ≈ 0.34 e²,

and the hybrid's floating test passes when e₁ ≤ e₁*(ρ). The binding pieces, in order:
1. **The restarted theorem's own threshold** e₁*(ρ) = 10^{−10.95}, bound by route A′'s cap sum `Tab`: the frame part of
   the torsion against the initial torus, Lemma `bp:p2s2:torsion-ref`. Every order
   gained by the plain theorem gives half an order here (the planning scale is √(e₁*/0.34)).
2. **The quadratic Newton residual Ẽ.** This is the error of one additive Newton step: E_red·ξ and Ω_K·∂_ωξ. It is a
   property of the candidate, not of the theorem.
   - Its ℓ¹ enclosure is 2.2× the directly computed sup. A sup enclosure by corner majorants (as the certifier does for frames) would
     recover up to 0.19 orders.
3. **Negligible:**
   - the Taylor remainder (10⁻³ of e₁);
   - every transfer increment (at L = 8: ≤ 4.4·10⁻⁴ relative on every cap);
   - the frequency change and the energy error (|ε̃| ≤ 10⁻¹⁷ for the finite candidates from L = 8);
   - the displacement (5.7·10⁻⁸ on T_{ρ∞}).

**Levers beyond this package (projections, not computed).** Because the restart accepts any K₁, the next levers are free
on the theorem side:
- (a) **A multi-step correction.** The producer takes two Newton steps, ΔK = K₂ − K, at no extra kernel cost. Then Ẽ
  drops to the size of the neglected quadratic Taylor term, ≈ (M₂/2)|ΔK|² ≈ 5·10⁻⁴e², so e₁ ≈ 10⁻³e² instead of 0.39e².
  That is about 1.3 orders on the planning scale, to ≈ 10⁻⁴.
- (b) **Model the quadratic term.** Enclose E + DX_h(K)ΔK + ½D²X_h(K)[ΔK, ΔK] − DΔK·ω. This needs D²X_h∘K, available
  from the composition's jet, and a bound M₃ ≥ |D³X_h| on 𝔅 for the cubic remainder. The binding term then becomes the
  frozen |DK| and ball budgets: μ₁ = μ − 2max{d₀, d₁} > 0 with d₁ ≈ 1.5e at L = 8 gives e ≲ 2·10⁻³.

Both are recorded for a follow-up package; neither changes the theorem of §2.

### 4.6 Observation: R1's ordinary twist is nearly singular (wording corrected after AUDIT-HYBRID-1, F4)

`r1_norms.measure()` on R1's candidate:
- ⟨T⟩ ≈ [[1.9626, 1.9·10⁻²⁰], [−5.6·10⁻²¹, −1.3·10⁻²⁰]], with |⟨T⟩⁻¹| ≈ 8·10¹⁹;
- the bordered |⟨T^ext⟩⁻¹| = 0.5843 = 1.022/1.75, the value in the R1 package's σ_T.

On the finite candidates of §4.2, |⟨T⟩⁻¹| ranges from 6·10¹⁰ (L = 6) to 1.5·10²⁰ (L = 15).

The ordinary torsion average is *sampled* as nearly singular. The design package uses the bordered inverse, and so
supplies only isoenergetic applicability. The listed fixed-frequency rows (here, in design §§6 and 11, and in the
SHARP2-FIX and DOMPLUS tables) are formal scalar experiments, not certified R1 applications. A bordered inverse cannot
supply the required ordinary inverse cap, whether that cap is infinite or merely enormous.

Exact singularity of the frozen torsion average is *not* claimed. H = c(P₁²/2 − P₁ + P₂ + V(Q₁ + Q₂, Q₂)) is affine in P₂,
but that alone does not make ⟨T⟩ of an approximate torus exactly singular; that would need an exact identity on the specific
K. The coarse finite candidates show a determinant that is small but nonzero in floating point. This is not an erratum of a
pinned source; it is recorded for the orchestrator.

## 5. Lean: signatures and package split

**Probe.** `docs/campaign/design/APOST-SHARP-V2-HYBRID-SIGNATURES.lean.txt` (the probe `.drafts/hybrid/Signatures.lean`):
- 785 lines, 52 declarations, 15 `sorry` targets;
- it elaborates against `sharp-v2` at f7bd6712 in 9 s at 3.6 GB peak, with `autoImplicit false`;
- it imports `KAM.Sharp2.RouteA.Ref.G1`, `KAM.Sharp2.RouteB.G1`, `KAM.Sharp2.RouteB.Frozen`, `KAM.Sharp2.TorsionRef` and
  `KAM.Iso.Sharp2.RouteA.Ref.G1`. Nothing is copied.

| Declaration | Blueprint | Status |
|---|---|---|
| `G1Concl`, `restart_close`, `concl_restart` | `bp:p2s2hc:restart` | **proved** in the probe |
| `IG1Concl`, `iconcl_restart` | `bpI:p2s2hc:restart` | **proved** in the probe |
| `linNewError`, `linNewEnergy`, `IsStep` | `bp:p2s2hc:lin`, `bpI:p2s2hc:lin`, `:standing` | definitions |
| `step_struct` | `bp:p2s2hc:struct` | target |
| `invarianceError_step_le` | `bp:p2s2hc:error` | target (Taylor) |
| `FrameNum` (`g`, `β1`, `b`, `nΔ`, `nΔt`), `frames_step` | `bp:p2s2hc:frames` | target |
| `dAB`, `torsionAB_step_sub_le`, `torsion_step_le`, `torsionAverage_step`, `errDerivMat_step_le` | `bp:p2s2hc:torsion` | targets |
| `energyAverage_step_le`, `extTorsionAverage_step` | `bpI:p2s2hc:errors`, `:torsion` | targets |
| `g1_hybrid_core_R`, `g1_hybrid_core_B`, `iso_g1_hybrid_core_R` | `bp:p2s2hc:g1` with a direct K₁ | targets |
| `KData`, `StepNum`, `StepBounds`, `StepNum.{e1, frS, frR, wB, lam0, lam1, t1, tA, init1, sK1, sB1, sT1}` | `bp:p2s2hc:bounds`, `:data` | definitions |
| `g1_hybrid_R`, `iso_g1_hybrid_R` (`IsoNum`, `IsoNum.e1`, `IsoNum.tAext`) | `bp:p2s2hc:g1`, `bpI:p2s2hc:g1` | targets |
| `RestartA`, `NumA.restart` (with `rfl` for `.n`), `HybOkR`, `g1_v2A'_hybrid` | `bp:p2s2hc:data`, `:frozen` | target |
| iso minimum (`iso_g1_v2A'_hybrid`) | `bpI:p2s2hc:frozen` | C8b target; same proof by cases; not in the probe (800-line cap) |

**Names.** All new names are in the namespaces `KAM.Sharp2.Hybrid` and `KAM.Iso.Sharp2.Hybrid`, plus
`KAM.Sharp2.RouteA.NumA.restart`. The clash check is in §5.1.

**Package split.** The implementation packages are C8a–C8d, in §3.4 (theorem side C8a, C8b; certifier side C8c, C8d).
The hard lemmas:
- `frames_step` and `torsionAB_step_sub_le`: matrix identities N = Ω₀LB and BLᵀ = NᵀΩ₀, Neumann, triple telescoping; the
  pieces exist in `RouteA/Torsion.lean` and `TorsionRef.lean`.
- `torsionAverage_step`: integrability of the torsions on the real cube, from holomorphy.
- The step-form theorems: long hypothesis plumbing, no new analysis.

### 5.1 Name-clash check

`.drafts/hybrid/Clash.lean` imports every module of the library whose olean exists in this worktree (1186 of the 1658
modules reachable from `KAM.lean`), followed by the signature body:
- exit 0, the same 15 `sorry` warnings, no redeclaration error;
- 7.1 GB peak, under a watchdog at 8.5 GB (run on the final signatures; the first run, before the §5.2 repairs, gave the same
  result at 7.3 GB).

The 472 modules without an olean (358 under `Planetary`, the rest mostly tests, `SpinOrbit`, `Certificate`, `Frozen`) were
not built (forbidden). A textual search of all `KAM/**/*.lean` finds none of the new names or namespaces.

### 5.2 Review of the targets

Each `sorry` target was checked against the proof the blueprint gives; all are true as stated. Three statements were
repaired in this review (before the copy in the signature file):
- `torsion_step_le` takes two frequencies (K at ω, K₁ at ω₁). The iso transfer compares T(K, sω*) with T(K₁, s₁ω*); the
  frame part 𝒯_ab does not depend on the frequency.
- `StepBounds` takes the frequency of K₁ for `lin`, so the iso step form uses Ẽ_s directly.
- The last row of the bordered increment is bounded through transposes. A sum over the columns v_j of a linear form ℓ
  applied to them is at most n|ℓ||Xᵀ|, not |ℓ||X|. This gives `IsoNum.tAext`'s n(M_{h1}n_Δᵗ + M_{h2}d₀(νᵗ + n_Δᵗ)).

Plumbing facts the proofs need, none of them new mathematics:
- ‖`tangentMat` K θ‖ against ‖fderiv K θ‖;
- ‖Xᵀ‖ = ‖X‖ for the symmetric B and B₁ − B;
- the mean-value bound |C(K₁θ) − C(Kθ)| ≤ 2M₂|ΔK| with M₂ in place of the frozen M (`norm_hamComm_sub_le` is stated
  with Standing's M; C8a adds the M₂ variant);
- the case t_A = 0 in `torsionAverage_step` (`inv_le_of_ref` needs m < σ strictly);
- integrability of the torsions and of H∘K on the real cube (from holomorphy).

## 6. Risks

- **Not a property of the theorem.** The planning scale depends on the candidate's residual spectrum (§4.2 against
  §4.4: R1's own high-mode residual gives A = 22 at ρ₁ = ρ and 4·10⁻⁵ at ρ₁ = ρ − 3δ₀; a finite truncated candidate gives
  A ≈ 0.34 at ρ₁ = ρ, nearly independent of ρ₁). The certificate always measures the actual
  step, so it is sound for any candidate; only the planning numbers change.
- **The model of E at fine accuracy.** The composition's remainder must be ≤ 10% of e₁ on T_{ρ₁}. The certifier's
  composition is sound at any accuracy; the cost is that of the plain certificate's composition (§3.3).
- **The numerical core over the memory cap.** This is inherited from C6L8; it needs splitting regardless of the hybrid.
- **Integrability side conditions** in `torsionAverage_step` and `energyAverage_step_le` are stated as hypotheses in the
  probe. C8a should derive them from holomorphy (continuity on the compact cube). They are typing data, not
  conclusion-shaped.
- **R1's "fixed-frequency" rows are formal** (§4.6). The hybrid that SO needs is the isoenergetic one.
- **Floating planning numbers.** The finite candidates are now the checker's carrier (finite K̂ and ΔK̂), but their norms
  are still computed in floating point on 512 × 128 grids, with a 10% allowance for model remainders that is not checked.
  Certification needs the kernel's outward enclosures (C8c, C8d).
- **The design package is not SO's `lunarR1`** (c = 7/4 with separate σ's against c = 237/125 with one σ = 1.987); the C8d
  producer must use SO's package.

## 7. Reproduction

```
python3 -I scripts/apost_sharp/hybrid_cert_r1.py --finite --emit DIR --json OUT   # finite candidates, §4.2 (about 15 min)
python3 -I scripts/apost_sharp/hybrid_cert_r1.py --trunc --json OUT    # analytic-graph truncations, §4.3 (about 1 h, loaded machine)
python3 -I scripts/apost_sharp/hybrid_cert_r1.py --shape --json OUT    # R1's residual shape, §4.4 (35 min, grid 1024 x 256, 1 GB)
python3 -I scripts/apost_sharp/hybrid_cert_r1.py --sizes --json OUT    # model sizes, §3.3 (2 min)
nice -n 5 lake env lean .drafts/hybrid/Signatures.lean               # the signature probe (9 s, 3.6 GB)
```

## 8. The audit findings this answers

| Finding | Answer |
|---|---|
| AUDIT-HYBRID-1 F1 (finite inputs) | §4.2: finite dyadic K̂ = (ψ + Û, φ, P̂₁, P̂₂) and ΔK̂ are emitted (`r1-L8-finite-candidate.json`). Every bound is recomputed from them: residual, energy error, Ẽ, E₁, derivatives, Ω products, caps. The truncation and rounding ledger is recorded, and the supports of all components and of the witness are counted (§3.3). The analytic-graph tables are relabelled as planning experiments (§4.3). |
| AUDIT-HYBRID-1 F2 (wording) | "Certified threshold" is replaced by "planning scale" and "certifies" by "passes the floating test", in this note, the handoff, the blueprint register and the script. Floor values are unresolved estimates, not lower bounds. |
| AUDIT-HYBRID-1 F3 (zero step) | Corollary `bp:p2s2hc:frozen` and §0: never worse because the plain branch remains available; exact recovery through the transfer formulas is withdrawn (the local torsion bounds do not cancel at ΔK = 0). A remark on branchwise closeness is added. |
| AUDIT-HYBRID-1 F4 (singularity) | §4.6, §0, blueprint register (v), iso part intro, script: "sampled as nearly singular"; exact singularity is not claimed; the fixed rows are formal scalar experiments. |
| AUDIT-SHARP-V2-iso-1 F6, AUDIT-SHARP-V2-fixed-1 F6 (hybrid) | "A certified threshold requires an enclosure of the actual new invariance and energy errors, the actual new caps and ray margin, and budgets reduced by measured stage-zero increments. Add the first displacement and frequency correction." Each item is now an explicit hypothesis: Ẽ and the Taylor term (new invariance error), ε̃ and the Taylor term for H (energy), Lemmas frames/torsion (new caps), ν₁ = ν − d_ω (ray margin), μ₁ ≤ μ − 2max{d₀, d₁} and σ_{K,1} − μ₁/2 ≤ σ_K − μ/2 (reduced budgets), d∞ and d_ω in the closeness (displacement, frequency). The numbers of §4 replace the sampled leading-order coefficient by the enclosure norms. |
