# Track R — proof route for R-HEAD (`KAM.Russmann.russmann_kam`)

30 October 2026, brief RUSSMANN-W. Route for the provider `KAM.Provider.Russmann.russmann_kam` of the
draft statement in [statement.md](statement.md). The whole KAM content comes from track P's internal
theorem `KAM.Planetary.weak_kam_quantitative` (`KAM/Planetary/Quantitative/Assembly.lean`). The
provider builds that theorem's data `d : QuantitativeData n` and hypotheses
`QuantitativeInput d h f` from R-HEAD's hypotheses. It then turns the output family
`QuantitativeFamily d (realHamiltonian h f) cΔ ε` into the volume bound for
`fundamentalDomain B ∩ russmannCover h f B r₀ τ δ`.

Notation: `‖·‖` is the max norm, `|·|₂ = KAM.Nekhoroshev.euclid` the Euclidean length,
`B_r = {x ∈ ℝⁿ : ∃ J ∈ B, ‖x − J‖ < r}` the real `r`-neighbourhood (`KAM.Russmann.realNbhd`).

## Step 0 — order of choices

1. From `(n, r₀, B, h)`: the order `μ ≥ 1` and amount `β₀ > 0` of non-degeneracy on `closure B`
   (Step 1). Put `τ := n·μ`. Then `τ > n − 1`, `τ > n·μ/1 − 1` and `τ ≥ 0`. **This is the `∃ τ`
   of R-HEAD.**
2. From `(n, B)`, before `δ`: the compact `K ⊂ B` with `meas K` close to `meas B`, its margin
   `m := dist(K, ℝⁿ ∖ B) > 0`, the loss `ε*`, and the widths `ϑ, s` (Steps 2–3).
3. From `(K, ϑ, h)`: the bounds `M, M₀, C₁` (Step 3). This fixes `d`, hence `γ = d.gamma > 0` and
   `thresholds d > 0` (`qbc_gamma_pos`, `qbc_thresholds_pos`), and `cΔ` from
   `weak_kam_quantitative n μ τ s C₁`.
4. From `δ`: `ε₀ := min (thresholds d) ((γ · min(δ, m/2) / cΔ)²)`.

Nothing in Steps 1–3 depends on `δ` or on `f`. Only `ε₀` depends on `δ`.

## Step 1 — Rüssmann's non-degeneracy lemma (helper `KAM/Russmann/Nondegeneracy.lean`)

- `B_r` is open and connected (a union of balls, each meeting the connected set `B`), and it contains
  `closure B` (for `r > 0`). Its real points map into `actionNbhd B r₀` for `r ≤ r₀`.
- `ω = frequencyMap h` is real-analytic on `B_{r₀}`. Holomorphy gives analyticity
  (`KAM.analyticOnNhd_of_differentiableOn`). Realness gives `ω(I) = Re ∂h(I)` near each real point
  (`KAM.Planetary.p11_freq_eq`), so `ω` agrees, near each point, with an analytic map.
- R-HEAD's condition on `B ⊆ B_{r₀}` is `p11RNondegenerate B_{r₀} ω`.
- `KAM.Planetary.rank_compact` (Part 10/11a: Rus01 Lemma 18.2, `cp09_unsquared`), with `ρ = 1` on
  the compact set `closure B`, gives `μ ≥ 1` with `0 < index_def 1 μ ω (closure B)`.
- Unfolding `index_def` through `p11maxJet_attained`, `p11dg_attained` and
  `p11c_zero_euclid_iter` (exactly as in `KAM.Planetary.p11_wr_qi`, there with `ρ = 2`) gives the
  `QuantitativeInput` clause: for every Euclidean-unit `c` and every `y ∈ closure B`, there are
  `j ≤ μ` and a Euclidean-unit `v` with `β₀ ≤ |D^j (p11c_scalar 1 ω c)(y)(v,…,v)|`.

  This holds for **every** compact `K ⊆ closure B` with the same `(μ, β₀)`, which is why `τ` can be
  fixed before `K`.

## Step 2 — the compact parameter set and the measure budget (helper `KAM/Russmann/Domain.lean`)

- `meas B ∈ (0, ∞)`: `B` is open and nonempty, and bounded.
- Constants: `q := (1 − 2⁻¹⁰)^{2n}` and `p := 4⁻ⁿ < q`. Put `η := (q − p)/(2q) ∈ (0, ½)`.
- Inner regularity (`MeasurableSet.exists_isCompact_lt_add`) gives a compact `K ⊆ B` with
  `meas K > (1 − η)·meas B`. Put `ε* := η·meas B / 2`. Then `0 < ε* < meas K` and
  `q·(meas K − ε*) ≥ p·meas B`.
- Margin: `B` is bounded and `n ≥ 1`, so `ℝⁿ ∖ B` is nonempty. `K` is compact and `B` is open, so
  `m := infDist(K, ℝⁿ ∖ B) > 0`, and every `y` with `‖y − b‖ < m` for some `b ∈ K` lies in `B`.

## Step 3 — the data `d` and `QuantitativeInput d h f` (helper `KAM/Russmann/Bounds.lean`)

- `ϑ := min(1, r₀/4)`, `s := min(1, s₀)`, `ρ := 1`, `μ`, `τ` as in Step 1, `K`, `ε*` as in Step 2.
  Then `U := actionNbhd K (2ϑ) ⊆ actionNbhd B r₀` and `complexStrip n s ⊆ complexStrip n s₀`.
- `V := {y : ∃ x ∈ K, |y − x|₂ ≤ ϑ}` is compact (the image of `K × closed Euclidean ball`) and lies
  in `B_{r₀}`, where `ω` is `C^∞`.
  - `M` bounds `|D^j(c·ω)(y)(v₁,…,v_j)|` for `1 ≤ j ≤ μ+1`, `y ∈ V`, `|vᵢ|₂ ≤ 1`, `|c|₂ = 1`.
  - `M₀` bounds `|D^jω(y)(v,…,v)|₂` for `j ≤ μ`, `y ∈ V`, `|v|₂ = 1`.

  Both come from continuity of `y ↦ D^jω(y)` on the compact set `V`, with
  `‖c·‖ ≤ n` and `|w|₂ ≤ √n·‖w‖`. **No Cauchy estimate is needed:** only the existence of finite
  bounds matters, since `ε₀` is existential.
- `C₁` bounds `‖D(∂h)(y)‖` on `U`. Its closure lies in the compact set
  `{z : ∃ J ∈ K, ‖z − J‖ ≤ 2ϑ} ⊆ actionNbhd B r₀`, on which `D(∂h)` is continuous (`h` is analytic).
- Normalise to the `Valid` ranges: `β := min(β₀, 1)`, `M := max(M, β)`, `M₀ := max(M₀, 1)`,
  `C₁ := max(C₁, 1)`.
- The holomorphy, periodicity and realness clauses restrict from `actionNbhd B r₀` and
  `complexStrip n s₀`. `realInclusion n y = fun i => (y i : ℂ)` is `rfl`
  (`KAM.Head.realInclusion_eq`).
- `‖f‖ ≤ ε` on the large domain gives `‖f‖ ≤ ε` on `complexStrip n s ×ˢ U`, and `0 ≤ ε`, because the
  domain is nonempty.

## Step 4 — the family (`weak_kam_quantitative`)

For `ε ≤ ε₀ ≤ thresholds d`, `weak_kam_quantitative n μ τ s C₁` gives
`Q : QuantitativeFamily d (realHamiltonian h f) cΔ ε`, with `good ⊆ K` compact,
`meas K ≤ meas good + ε*`, and tori `Q.torus b`, frequencies `Q.freq b` for `b ∈ good` such that:

- `IsLatticeTorus angleShift (realHamiltonian h f) (p11c_realDomain d) (Q.freq b) (Q.torus b)`;
- `IsDiophantine γ τ (Q.freq b)`;
- `‖Q.torus b θ − (θ, b)‖ ≤ p11c_displacement d cΔ ε ≤ cΔ √ε / γ ≤ min(δ, m/2)`;
- the bi-Lipschitz bounds with constants `1 ± 2⁻¹⁰`, and `E := T(unitCube × good)` Borel, where
  `T(θ, b) = Q.torus b θ`.

## Step 5 — from the family to the cover

- **Torus transfer** (helper `KAM/Russmann/Torus.lean`):
  `IsLatticeTorus angleShift H O ω K → IsInvariantLagrangianTorus H ω K`. Analyticity, the lattice
  identity, the immersion, the Lagrangian identity and the flow are the same clauses. Embeddedness:
  `K θ' = K θ + (k, 0) = K(θ + k)` gives `θ' = θ + k + l` (IsLatticeTorus (L3)), and then
  `K θ' = K θ + (k + l, 0)` forces `l = 0`. The track-P assemblies (`Hamiltonian/Transport.lean`)
  contain only the chart-transport versions, so this is new but short.
- **Cover clauses.** For `z = Q.torus b θ`, the witnesses are `K = Q.torus b`, `ω = Q.freq b`,
  `γ = d.gamma > 0`, `I₀ = b ∈ good ⊆ K ⊆ B`.
  - Actions within `r₀` of `B`: `Q.torus b θ ∈ p11c_realDomain d`, so its action is within `2ϑ < r₀`
    of `K ⊆ B`.
  - Closeness: `≤ δ` by Step 4.
- **Volume of `E`** (helper `KAM/Russmann/FamilyVolume.lean`): `QuantitativeFamily.lower` makes
  `T⁻¹ : E → unitCube × good` Lipschitz with constant `(1 − 2⁻¹⁰)⁻¹`, so `KAM.lip_image_prod` gives
  `meas good = meas(unitCube × good) ≤ (1 − 2⁻¹⁰)^{−2n} meas E`.
- **Fundamental-domain rearrangement** (helper `KAM/Russmann/FundamentalDomain.lean`).
  - Let `S` be a set stable under `z ↦ z + (k, 0)` on `E` (here: the cover). Assume `E` is
    measurable, injective modulo `ℤⁿ × {0}` (from `lower` and the lattice identity), and has actions
    in `B` (displacement `< m`).
  - Then `meas E ≤ meas(fundamentalDomain B ∩ S)`. The map `φ(θ, I) = (fract θ, I)` sends `E` into
    `[0,1)ⁿ × B` and into `S`. It is a translation on each measurable piece
    `E_k = E ∩ {⌊θ⌋ = k}`, and its images `E_k − (k, 0)` are pairwise disjoint.
- **Conclusion.**
  `4⁻ⁿ meas FD = p·meas B ≤ q·(meas K − ε*) ≤ q·meas good ≤ meas E ≤ meas(FD ∩ russmannCover …)`,
  where `meas FD = meas B` since `meas [0,1)ⁿ = 1`.

## Status of the pieces

| Piece | Module | Status |
|---|---|---|
| Rüssmann non-degeneracy lemma (Step 1) | `KAM/Russmann/Nondegeneracy.lean` | see handoff |
| compact set, margin, budget (Step 2) | `KAM/Russmann/Domain.lean` | see handoff |
| bounds `M, M₀, C₁` (Step 3) | `KAM/Russmann/Bounds.lean` | see handoff |
| torus transfer (Step 5) | `KAM/Russmann/Torus.lean` | see handoff |
| volume of `E`, rearrangement (Step 5) | `KAM/Russmann/FamilyVolume.lean`, `FundamentalDomain.lean` | see handoff |
| assembly in inline form (Steps 0–5) | `KAM/Russmann/Assembly.lean` | see handoff |

The **assembly in inline form** is a theorem with R-HEAD's hypotheses and, in its conclusion, an
explicit set `E ⊆ fundamentalDomain B` of volume `≥ 4⁻ⁿ meas FD`, every point of which satisfies
the defining predicate of `russmannCover` written out. It refers to no draft definition. After
freezing, the provider is a few lines: `E ⊆ FD ∩ russmannCover` by `Iff.rfl` on the definition, then
`measure_mono`.
