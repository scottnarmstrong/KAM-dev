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

## Status of the pieces (all proved, 30 October 2026)

| Piece | Lean declaration | Module |
|---|---|---|
| real neighbourhood; analyticity of `∇h` and `∇_ℂ h` (Step 1) | `isConnected_realNbhd`, `analyticOnNhd_frequencyMap`, `analyticOnNhd_gradC` | `KAM/Russmann/Frequency.lean` |
| Rüssmann non-degeneracy lemma (Step 1) | `russmann_finite_order`, `russmann_finite_order_frequencyMap` | `KAM/Russmann/Nondegeneracy.lean` |
| compact set, margin, budget (Step 2) | `exists_compact_budget`, `volume_fundamentalDomain` | `KAM/Russmann/Domain.lean` |
| bounds `M, M₀, C₁` (Step 3) | `exists_bound_iteratedFDeriv`, `abs_iteratedFDeriv_scalar_le`, `euclid_iteratedFDeriv_le`, `isCompact_euclidThick`, `exists_hessian_bound` | `KAM/Russmann/Bounds.lean` |
| data and `QuantitativeInput` (Step 3) | `russmannData`, `russmannData_valid`, `russmannData_input` | `KAM/Russmann/Data.lean` |
| torus transfer (Step 5) | `isInvariantLagrangianTorus_of_isLatticeTorus` | `KAM/Russmann/Torus.lean` |
| volume of `E` (Step 5) | `volume_le_of_lower_bound`, `familyImage_volume_lower`, `familyImage_eq_add_angleTranslate` | `KAM/Russmann/FamilyVolume.lean` |
| reduction modulo `ℤⁿ` (Step 5) | `volume_le_volume_fundamentalDomain_inter` | `KAM/Russmann/FundamentalDomain.lean` |
| assembly in inline form (Steps 0–5) | `russmann_tori` | `KAM/Russmann/Assembly.lean` |

`KAM.Russmann.russmann_tori` has R-HEAD's hypotheses verbatim, and its conclusion is R-HEAD's
with `russmannCover h f B r₀ τ δ` written out as a set-builder. It refers to no draft definition.
Its axioms are `propext`, `Classical.choice`, `Quot.sound`.

A probe (`.drafts/russmann/ProviderCheck.lean`: the draft cover, then the draft theorem with body
`KAM.Russmann.russmann_tori hn hs₀ hr₀ hB_open hB_conn hB_bdd hh hh_real h_russmann`) elaborates
with the same three axioms. So after freezing, the provider of R-HEAD v0.1 is this one term: the
draft cover and the inline set are equal by definition.

## Cost of the stronger form (audit F1: `meas(FD ∖ cover) ≤ κ · meas FD` for every `κ > 0`)

The audit's form `∀ δ > 0, ∀ κ > 0, ∃ ε₀ > 0, … → volume (fundamentalDomain B \ russmannCover …) ≤
ENNReal.ofReal κ * volume (fundamentalDomain B)` needs `meas(FD ∩ cover) ≥ (1 − κ) meas FD`. Two
losses enter the current chain.

- **Parameter loss.** `meas good ≥ meas K − ε*`, with `K` and `ε*` free. Already arbitrarily small.
- **Evaluation loss.** The factor `(1 − 2⁻¹⁰)^{2n}`. Track P exports only the bi-Lipschitz bounds
  `lower`/`upper` with the fixed constant `λ* = 2⁻¹⁰`. With only those clauses and `Δ(ε) → 0`, the
  loss cannot be removed in general: a bi-Lipschitz map close to the identity in sup norm may
  compress a Cantor-like set by up to `(1 − λ)^{2n}`, unless one uses degree theory.

There are two ways to remove it.

**(A) Make `λ(ε) → 0` inside track P.** Mathematically free: both halves of the defect's Lipschitz
constant are linear in `Q₀Ξ`, and `Q₀ = C_Q 2^N T₀^τ λ₀ / (π γ ς₀^{N+1})` with
`λ₀ = (2 N C₁ ε)^{1/2}` (`free-radius`), so `λ(ε) ≤ C(d)·√ε`.
- The parameter half is already explicit: `pl4_sum_node` gives `S_b ≤ (32/31) Q₀Ξ (2/C_Q + 1/32)`.
- The angle half is not. `selectionLim_derivative_bound` (LimitProps.lean) and
  `selectionLim_defect_lipschitz` (Limit.lean) use the structure field
  `SelectionChain.composition_small : ‖DΦ^ν − id‖ ≤ 2⁻¹¹`, produced by the composition budget
  (`CompositionBound.lean`, `e^{Σ m_j} ≤ 1 + 2⁻¹¹`). Threading `e^{Σ m_j} − 1 ≤ c·Q₀Ξ` through it
  means:
  - a parallel chain structure (or a changed field);
  - new versions of the limit derivative bound, the angle Lipschitz bound, `lipschitz_family` and
    `evaluation_bilipschitz` with `λ(ε)`;
  - a lemma `Q₀(ε) = c(d)·√ε`;
  - a new export carrying `lower` with `1 − λ(ε)`.

  Estimate: **600–900 lines** in `KAM/Planetary/WeakKAM` and `Quantitative`, plus about 100 in
  track R. It is invasive: existing track-P files or structures would change, or be duplicated.

**(B) Keep `λ = 2⁻¹⁰` fixed; use the global extension and `Δ(ε) → 0` (recommended).**
- *Track P (additive).* Export the defect Lipschitz bound that is already proved,
  `SelectionLipschitz.lipschitz_joint`: `‖u(b,θ) − u(b′,θ′)‖ ≤ 2⁻¹⁰ ‖(θ,b) − (θ′,b′)‖` on
  `good × ℝⁿ`, with `u(b,θ) = torus b θ − (θ, b)`. This needs a theorem parallel to
  `weak_kam_quantitative`, repeating the repackaging of `Assembly.lean` (`p11c_asm_family`, about
  120 lines) with one more clause. The zero case is trivial (`u = 0`). **About 150 lines**, with no
  change to track P's constants or files.
- *Track R.*
  - Extend `u|_{ℝⁿ × good}` to a global `2⁻¹⁰`-Lipschitz `Φ` (Mathlib `LipschitzOnWith.extend_pi`,
    max norm), and clip it componentwise to `[−Δ, Δ]`. `E = id + Φ` is then a bijection
    (`KAM.lipeo_onto`) with `‖E − id‖ ≤ Δ`, and `E = T` on `ℝⁿ × good`. Track P's
    `Evaluation.lean` (`EvalExtData`) already does this internally.
  - With `U` open, `K ⊆ U ⊆ B`, `meas(U ∖ K)` small (outer regularity), `Ω = [0,1)ⁿ × U` and
    `A = [0,1)ⁿ × good`:
    - `E(Ω) ⊇ {z : closedBall z Δ ⊆ Ω} ⊇ [Δ, 1 − Δ)ⁿ × U_Δ`, where
      `U_Δ = {b : closedBall b Δ ⊆ U}`. This is elementary from bijectivity and `‖E − id‖ ≤ Δ`;
      no degree theory is needed.
    - `meas E(Ω ∖ A) ≤ (1 + 2⁻¹⁰)^{2n} meas(U ∖ good)` (`KAM.lip_image_prod`).
    - Hence `meas T(A) ≥ (1 − 2Δ)ⁿ meas U_Δ − (1 + 2⁻¹⁰)^{2n} (meas(U ∖ K) + ε*)`.
  - `meas U_Δ ↑ meas U` as `Δ ↓ 0` (continuity from below), and `Δ(ε) ≤ c_Δ √ε / γ` is already
    exported. Hence `meas T(A) ≥ (1 − κ) meas B` for `ε ≤ ε₀(κ)`. `τ` is unaffected (it is fixed
    on `closure B` before `κ`).
  - The complement: a measurable-subset variant of `volume_le_volume_fundamentalDomain_inter` (it
    already builds the measurable set `⋃ₖ Aₖ`), and `meas(FD ∖ cover) ≤ meas FD − meas(⋃ₖ Aₖ)`.

  **About 350 lines.**

  Total for (B): **about 500 lines**, no new mathematics, nothing invasive. (B) can reuse every
  current track-R module unchanged except the assembly (a second assembly theorem).
