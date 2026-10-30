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
    routes, by cases, so it is never worse. ΔK = 0 reproduces each route exactly.
  - Soundness never uses that ΔK solves the cohomological equations. The producer computes ΔK; the kernel divides by no
    small divisor and needs no `cohSolve`.
- **The certifier side (§3).** Beyond today's checks of K, the kernel needs one new arithmetic primitive, a product of
  models (DX_h∘K times ΔK), plus weighted norms of a polynomial and the existing engines at the restart numbers.
  - The composition (exp witnesses) is run once, on the coarse K, at the accuracy of the final error. Frames, Gram and
    torsion models run on the coarse K only.
  - Cost estimate, package split and the placement of kernel tests are in §3 (R1-scale tests go to `kernel-tests/`,
    unbuilt).
- **The R1 numbers (§4).** TO BE FILLED FROM THE RUNS.
- **Lean (§5).** The signature probe elaborates against `sharp-v2` (781 lines, 52 declarations, 15 `sorry` targets, 9 s,
  3.6 GB peak). About 2.3k Lean lines in five packages H1–H5, almost all linear algebra and mean-value estimates on top of
  B9 (route A′), B6/B7 (route B) and `TorsionRef`.
- **An observation on R1 (§4.5).** In R1's rotated frame H is linear in P₂, so the frozen torsion average is singular,
  ⟨T⟩ = diag(1.96, 0); only the bordered (isoenergetic) twist is invertible (|⟨T^ext⟩⁻¹| = 0.584). Only the isoenergetic
  theorem applies to R1, and the "fixed-frequency" R1 rows of the design tables are formal.

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
- The restart also allows ρ₁ = ρ₀. On R1's truncations this is the measured optimum: a measured ΔK needs no strip loss
  (§4.3).
- The caps of K₁ enter as the restarted run's initial values; its budgets are fresh. The frozen ball and |DK| budgets are
  reduced exactly by the step increments (μ₁ ≤ μ − 2 max{d₀, d₁}, `bp:p2s2hc:struct`). The internal caps and their budgets
  are free parameters of any run.

### 1.2 The additive step

- The step is additive, ΔK = Lξᴸ + Nξᴺ for the Newton correction (the form of route A), even when the restarted run is
  route B. The restart accepts any K₁; the form of the step affects only the size of Ẽ.
- Route B's step (K + Nξᴺ)∘(id + ξᴸ) would need a certified composition of models with a shifted argument, plus its Taylor
  remainder in θ. The brief's "composition K̃∘(id + ξᴸ) needs a certified composition/remainder" is exactly that. It is not
  needed: the measured new error of the additive step is already second order, |E₁| ≈ 0.6|E|² on R1's truncations (§4.3).
  The Taylor remainder is 10⁻⁴ of it, and the binding part is Ẽ itself.

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

- Ẽ must be enclosed with a remainder ≤ 10% of the target e₁. Here e₁ ≈ e*(ρ₁) ≈ 2·10⁻¹¹ for route A′ on R1, so the model of
  E needs rad ≲ 2·10⁻¹² on T_{ρ₁}. The composition must run at this absolute accuracy although K is coarse; this is the
  accuracy the plain certificate needs for its own final residual (§3.3).
- ΔK is of size ≈ 10⁻² e (§4.3); it needs only about 7 significant digits (absolute accuracy 10⁻¹² at e ≈ 4·10⁻⁶). The
  product (DX_h∘K)·ΔK is low precision.
- The real-torus increments are 10⁻⁵–10⁻⁶ of the strip increments (the residual sits at high modes); the twist
  transfer is negligible.

### 3.3 Kernel cost at lunar size

Model sizes measured on R1's truncations (`sizes` measurement, §7). The count is the number of terms on the full lattice
for a dropped weighted-ℓ¹ mass ≤ 2·10⁻¹² on T_ρ.

| Candidate | v terms (half lattice) | E model | character χ = e^{4πiq} of the composition | ΔK |
|---|---:|---:|---:|---:|
| L = 8 (hybrid certifies, §4.3) | 23 | 176 | 82 | 123 |
| L = 9 | 29 | 168 | 83 | 106 |
| L = 15 (plain v2 route A′ certifies) | 87 | (residual 4.6·10⁻¹² ≈ tol) | 89 | — |
| L = 17 | 113 | — | 89 | — |

- **The composition costs the same for both.** The character needs about 85 terms at this accuracy, whatever the
  truncation: it is fixed by the torus's analyticity at the accuracy of the final error.
- **The frame, Gram and torsion models shrink.** They are products of models of the embedding, so their cost scales like
  (v terms)²: (87/23)² ≈ 14× fewer operations for the hybrid. They include the Gram witness, N = Ω₀LB, DN, Nᵀ(Ω₀X_N) and the
  corner majorants.
- **The new items are small.**
  - Ẽ: 16 products of ≈ 85-term entries of DX_h∘K with the 123-term ΔK, ≈ 2·10⁵ low-precision multiplications. In R1 only
    three entries of DX_h are non-constant.
  - Norms of ΔK, DΔK: linear in 123 terms.
  - Ω_{K₁}: n²·2n products of ≈ 150-term polynomials, ≈ 2·10⁵ multiplications.
  - At the measured rates (compose ≈ 1 μs per coefficient operation, C7; `cohSolve`-type rational ops ≈ 10–20 μs, C5CORE)
    these are seconds.
- **The numerical core at N₁ costs what the plain core costs.** C6L8 measured 6 min and 19.2 GB for R1's route-A′ core
  (`RefinedRefR1`). That is over the machine's 10 GB per-process cap, a design signal for the core (split the per-stage
  `decide`s, round the arithmetic), not for the hybrid. With ρ₁ = ρ₀ the small-divisor bites are the plain certificate's.
- **Net.** Against plain v2 at L = 15, the hybrid removes most of the frame-model cost (up to ≈ 14×), keeps the composition
  and core costs, and adds seconds. These are estimates; no lunar kernel test was run (orchestrator rule, below).

### 3.4 Package split (certifier side) and kernel tests

| Package | Content | Lines | Kernel tests |
|---|---|---:|---|
| C8a | ℓ¹ (or advice-based sup) products of models, with soundness (`EnclosesL1.mul`); Cauchy for a model remainder | 350 | toy, `KAM/` |
| C8b | the hybrid checker: Ẽ's model, the step norms, Ω's, the transfer arithmetic, the call of the route core at N₁; soundness to the step-form theorems' hypotheses | 500 | toy T² (a few seconds, < 2 GB), `KAM/` |
| C8c | iso: ε̃, Δs, the bordered increments; wrapper `CertifiedTorus` with disp = max{d∞ + D₁, d_ω + D₁^ω} | 300 | toy, `KAM/` |
| C8d | R1-scale test | — | **`kernel-tests/`, not built**; expected cost: the plain core (≈ 6 min, ≈ 19 GB unsplit; must be split below 8 GB) plus the composition at accuracy 2·10⁻¹² plus seconds; to be stated again in C8d's handoff |

Orchestrator rule (binding): every compile stays under about 8 GB; no lunar-size kernel test is built or run; R1-scale
tests live in `kernel-tests/`.

**SO wiring.** `CertifiedTorus` is stated for the certificate's own torus c.K, with ‖K∞ − c.K‖ ≤ disp. The hybrid
conclusion is about K = c.K, with disp ≥ max{d∞ + D₁, d_ω + D₁^ω}, so no change of the SO consumer is needed beyond the
wrapper. `checkSoGraph` needs disp < mono·ρ∞ ≈ 1.4·10⁻⁵. The measured d∞ is below 10⁻⁷ (§4.3), far inside it.

## 4. The R1 numbers

TO BE FILLED FROM THE RUNS.

## 5. Lean: signatures and package split

**Probe.** `docs/campaign/design/APOST-SHARP-V2-HYBRID-SIGNATURES.lean.txt` (the probe `.drafts/hybrid/Signatures.lean`):
- 781 lines, 52 declarations, 15 `sorry` targets;
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
| iso minimum (`iso_g1_v2A'_hybrid`) | `bpI:p2s2hc:frozen` | H4 target; same proof by cases; not in the probe (800-line cap) |

**Names.** All new names are in the namespaces `KAM.Sharp2.Hybrid` and `KAM.Iso.Sharp2.Hybrid`, plus
`KAM.Sharp2.RouteA.NumA.restart`. The clash check is in §5.1.

**Package split (theorem side).**

| Package | Content | Lines | Depends on |
|---|---|---:|---|
| H1 | `G1Concl`, `IG1Concl`, the restarts (done in the probe), `IsStep`, `step_struct`, `linNewError`, `invarianceError_step_le` | 300 | `Strip.Taylor` |
| H2 | `FrameNum`, `frames_step`, `dAB`, `torsionAB_step_sub_le`, `torsion_step_le`, `torsionAverage_step`, `errDerivMat_step_le` | 550 | H1, `TorsionRef`, `Strip.Bridges` |
| H3 | `g1_hybrid_core_R`, `g1_hybrid_core_B`, `KData`, `StepNum`, `StepBounds`, `g1_hybrid_R` | 500 | H2, B9 (`g1_branch_R`), B6 (`g1_branch_B`) |
| H4 | iso: `linNewEnergy`, `energyAverage_step_le`, `extTorsionAverage_step`, `iso_g1_hybrid_core_R`, `iso_g1_hybrid_R`, `iso_g1_v2A'_hybrid` | 600 | H3, `iso_g1_branch_R`, `iso_g1_v2A'` |
| H5 | `NumA.restart`, `HybOkR`, `g1_v2A'_hybrid`; the route-B step form if the certifier wants it | 300 | H3 |

Total about 2.25k lines, every file under 800 lines. The hard lemmas:
- `frames_step` and `torsionAB_step_sub_le`: matrix identities N = Ω₀LB and BLᵀ = NᵀΩ₀, Neumann, triple telescoping; the
  pieces exist in `RouteA/Torsion.lean` and `TorsionRef.lean`.
- `torsionAverage_step`: integrability of the torsions on the real cube, from holomorphy.
- The step-form theorems: long hypothesis plumbing, no new analysis.

### 5.1 Name-clash check

TO BE FILLED (probe importing every built module of the library with the signature body).

## 6. Risks

- **Not a property of the theorem.** The hybrid threshold depends on the candidate's residual spectrum (§4.2 against
  §4.3: R1's own high-mode residual gives A ≈ 10⁻³, a truncation gives A ≈ 0.4). The certificate always measures the actual
  step, so it is sound for any candidate; only the planning numbers change.
- **The model of E at fine accuracy.** The composition's remainder must be ≤ 10% of e₁ on T_{ρ₁}. The certifier's
  composition is sound at any accuracy; the cost is that of the plain certificate's composition (§3.3).
- **The numerical core over the memory cap.** This is inherited from C6L8; it needs splitting regardless of the hybrid.
- **Integrability side conditions** in `torsionAverage_step` and `energyAverage_step_le` are stated as hypotheses in the
  probe. H2/H4 should derive them from holomorphy (continuity on the compact cube). They are typing data, not
  conclusion-shaped.
- **R1's "fixed-frequency" rows are formal** (§4.5). The hybrid that SO needs is the isoenergetic one.

## 7. Reproduction

```
python3 -I scripts/apost_sharp/hybrid_cert_r1.py --trunc --json OUT    # truncated candidates (about 2 h on a loaded machine)
python3 -I scripts/apost_sharp/hybrid_cert_r1.py --shape --json OUT    # R1's residual shape (grid 1024 x 256, 1 GB)
nice -n 5 lake env lean .drafts/hybrid/Signatures.lean               # the signature probe (9 s, 3.6 GB)
```

## 8. The audit findings this answers

| Finding | Answer |
|---|---|
| AUDIT-SHARP-V2-iso-1 F6, AUDIT-SHARP-V2-fixed-1 F6 (hybrid) | "A certified threshold requires an enclosure of the actual new invariance and energy errors, the actual new caps and ray margin, and budgets reduced by measured stage-zero increments. Add the first displacement and frequency correction." Each item is now an explicit hypothesis: Ẽ and the Taylor term (new invariance error), ε̃ and the Taylor term for H (energy), Lemmas frames/torsion (new caps), ν₁ = ν − d_ω (ray margin), μ₁ ≤ μ − 2max{d₀, d₁} and σ_{K,1} − μ₁/2 ≤ σ_K − μ/2 (reduced budgets), d∞ and d_ω in the closeness (displacement, frequency). The numbers of §4 replace the sampled leading-order coefficient by the enclosure norms. |
