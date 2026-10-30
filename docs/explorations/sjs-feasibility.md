# Can we certify a KAM torus of the planar Sun–Jupiter–Saturn system? (SJS-FEAS)

30 October 2026, branch `sjs-feas`. Feasibility study: Python, literature and small kernel probes. Nothing here is a
theorem or a certificate. The numbers come from:
- `scripts/sjs/*.py` (section 10);
- the kernel probes in `scripts/sjs/results/kernel_probes.md`;
- a re-evaluation of Figueras–Haro 2024's constants (section 2.1, `scripts/sjs/lit/`).

The question comes from `docs/explorations/striking-applications.md` §9, which calls Figueras–Haro's planar SJS torus
(FH25: J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152) "infeasible in the kernel by about 4 orders of magnitude in
support and 6 in cost": S ≈ 10⁸ Fourier coefficients at L ≈ 85 digits, ≥ 100 full-precision products, ≈ 10⁷ CPU-h.

**Can the gap be closed? Yes, but only with two things that do not exist yet:**
- **The v2 theorem in its route-B form:** FH24's modified Newton step, split derivative bounds, measured torsion
  and frequency-specific small-divisor constants.
- **A kernel arithmetic that keeps Fourier models packed,** so that the kernel cost is big-integer time rather than
  a fixed overhead per coefficient.

**With both,** one torus of FH25's planar SJS system costs about **30–350 CPU-h** of kernel time: a few days on this
machine. With v2's hybrid step-0 lever (an estimate) it is **6–19 CPU-h**, the cost class of the lunar torus.

**With route B but today's per-coefficient checker** (even with the D34 fix):
- **10⁴–3·10⁴ CPU-h and 1–3.5 TB of advice per torus,** and up to 20× more if the landed checker's extra work (every
  jet slot at full support, untrimmed low-precision factors) carries over;
- that is a cluster job, bound by its data volume.

**Without route B it is out of reach in practice.** v1 needs L ≈ 146 digits and 5.6·10⁷ coefficients even after
every representation lever. The per-slot checker would then need 1.4–3.6·10⁵ CPU-h and 32–83 TB of advice. Even
packed arithmetic would need 4·10⁴–2·10⁵ CPU-h, with every product 35–70 times larger than a 32 GB slice.

| Configuration | Kernel CPU-h per torus | Outlook |
|---|---:|---|
| v1 theorem + landed checker (today) | ≈ 10⁷ | not feasible |
| v1 theorem + packed arithmetic | 4·10⁴–2·10⁵, products blocked 35–70× | not feasible in practice |
| v2 route B + per-slot checker (D34-like), box layout | 1.0–3.3·10⁴ (up to ×20), 1–3.5 TB of advice | cluster, data-bound |
| v2 route B + per-slot checker, ideal sparse layout | 1.8–6.9·10³, 0.1–0.35 TB | cluster |
| v2 route B + packed (GMP-resident) arithmetic | **34–351** | **this machine, days** |
| v2 hybrid L6 (estimate) + packed arithmetic | **6–19** | this machine, hours |

**Where the applications study's 6 orders go** (section 1 has the table):
- **Theorem.** Route B on FH's own data gives 10^−46.5…−52.1, against v1's 10⁻¹²³…⁻¹⁴⁰: L drops from 85 to 57–62.
  With Γ_spec in route B's weighted error (a design remark for SHARP-PLUS) it reaches FH24's own level, 10⁻⁴⁴.
- **Representation.** The d'Alembert structure makes the true support 7–14 times smaller than the product of
  per-axis decays, and reversibility halves it: S goes from 10⁸ to 3.6–4.7·10⁶. Frames change the layout cost
  (box/support from 46 to 10), not S. Charts and preliminary normalization do not reduce S.
- **Kernel.** The measured cost is interpretive overhead, 0.2–1.5 ms and 20–260 kB per coefficient or slot, and bits
  barely matter. Packed arithmetic would be about 250× cheaper per product and 500–2000× per add.
  - **C7's `composePruned` does not pay.** It gives no gain inside one declaration at any size, its pruning fails
    beyond about 3 000 ops, and at SJS sizes every model op is its own declaration anyway.

**Milestones.** The most striking one feasible now is LG00's secular SJS model. LG00 proved it rigorously with
interval arithmetic in 2000; a formal proof would be the first formally verified KAM torus of a planetary model, at
lunar-class cost (an estimate, still to be scouted). A GLS17-type 3-degree-of-freedom secular model, never proved
rigorously, comes next.

## 1. The gap, factor by factor

Columns: the applications study's assumption (`striking-applications.md` §9), what is achievable, the effect, and the
evidence.

| Factor | Applications study | Achievable | Effect | Evidence |
|---|---|---|---|---|
| Theorem threshold (log₁₀ at FH's ρ = 0.1) | v2-type −79, assumed. v1 on FH's data: −123…−140 | v2 route B, frequency-specific: −46.5…−52.1. With Γ_spec in the weight: −44. Hybrid L6: ≈ −23…−26 (estimate) | L 85 → 57–62 (hybrid 32–35). Product-model S 10⁸ → 5.0–6.6·10⁷ (hybrid 1.0–1.3·10⁷) | §2.2, `sjs_thresholds.py` |
| Small divisors | classical Γ with FH's γ = 1.69·10⁻⁶ | Γ_spec/Γ = 10^−5.4…−5.9 at the first bites; numerical γ 1.85·10⁻⁵ | +4.6–5.6 orders on route B's threshold; γ adds 1.1–2.1 more | §2.3, `sjs_freq.py` |
| Strip weight | ignored (S(L) unweighted) | included, strip re-optimized (ρ = 0.02–0.03) | the study's S was 2.4× too low at ρ = 0.1 | §2.4 |
| d'Alembert structure | product of per-axis decays | true support 7–14× smaller | S ÷7 (conservative end) | §3, `sjs_model_support.py` |
| Reversibility | — | real cos/sin half lattice | S ÷2 | §3 |
| Frame | box/support 6 assumed | 46 in Delaunay angles, about 10 in an adapted unimodular frame | product layout cost: 13.5·(box/support) advice slots per term | §3, §5 |
| Chart | Delaunay (Kepler's equation) | regularized chart: c_D²Xh below 5·10¹⁰ | threshold gains what c_D²Xh loses, linearly (route B); not quantified. Kepler needs an implicit witness | §2.1, §3 |
| Preliminary normalization | — | — | none on S for the true system | §4 |
| Precision | 307 bits | 212–231 (route B), 132–141 (hybrid) | none on the per-slot cost; ×0.7 / ×0.45 on the packed design | §5 |
| Operations | N_full ≥ 100 | 60–150 full products, 500–2000 scalar/add ops, Gram/torsion stage on the 17-digit support | — | `jet_counts.py`, hand count |
| Kernel arithmetic | tier P (lunar unit), linear in S | per-slot (D34-like): (2.8 + 13.5β) ms per term per product; packed: 3.4·10⁻⁸ s per factor bit | per product at β = 10: 250× for packed | §5, `kernel_probes.md` |
| CPU-h per torus | ≈ 10⁷ | per-slot 1.0–3.3·10⁴ (box layout), 1.8–6.9·10³ (ideal layout); packed 34–351; hybrid + packed 6–19 | 2.5–5.5 orders | §6, `sjs_cost.py` |
| Data | > 1 TB of advice | per-slot 1.0–3.5 TB; packed: K and witnesses, 3–4 GB | | §6 |

## 2. Theorem (brief item 1)

### 2.1 Why FH's thresholds are 10⁻³⁸ and 10⁻⁴⁴

FH25 applies Theorem 2.18 of Figueras–Haro 2024 (FH24, arXiv:2304.10205; FH25 Appendix A). The setting:
- the 3-degree-of-freedom Hamiltonian, reduced by the total angular momentum, at fixed frequency;
- d = n = 3, no remaining first integrals, the canonical symplectic form;
- the translated tori are used only for the continuation.

The smallness condition is FH24 (2.24) = FH25 (A.1):

  C/(γ δ^{τ+1}) · max{‖η^L‖_ρ, ‖η^N‖_ρ/(γ δ^τ)} < 1,  η^L = −Nᵀ Ω E, η^N = Lᵀ Ω E,

that is, C‖η^L‖ < γ δ^{τ+1} for the tangential component and C‖η^N‖ < γ² δ^{2τ+1} for the normal one.

The reason is the **modified Newton step**:
- the tangential correction is applied by composition, K̄̄ = (K + Nξ^N)∘(id + ξ^L);
- so the quadratic Taylor remainder, the one carrying c_D²Xh, only ever acts on Nξ^N, which is O(ε) in the weighted
  error;
- one step then costs a single factor γ⁻¹δ^{−τ−1} (FH24 (3.42)–(3.43)).

The additive step of Haro–Luque 2019, which our v0 and v1 use, applies the remainder to DKξ^L ~ ε/(γ²δ^{2τ}), hence
γ⁻⁴δ^{−4τ}.

**Re-evaluation** (literature subagent; FH24 Appendix B Tables 1–4 on FH25's data; `scripts/sjs/lit/fh24consts.py`,
`fh25run.py`, `sens.py`):
- Theorem 2.18 applied directly with FH24's uniform constant ĉ_R gives η^L 7·10⁻⁴⁷ and η^N 6·10⁻⁵⁷.
- With 10 Iterative-Lemma steps first, which may use the sharp frequency-specific c_R(δ) at their own bite, it gives
  10^−37.1 and 10^−45.9. FH25 reports 10⁻³⁸ and 10⁻⁴⁴; about 2 orders of the normal one are unexplained, and the
  inputs FH25 does not report (c_Th, c_DTh, ν, ϰ, κ, the bite schedule) were guessed.
- Binding term: the drift budget of ⟨T⟩⁻¹. FH take σ = (1 + 10⁻¹⁰)·norm, which leaves ‖T̄̄ − T‖ a budget of
  2.8·10⁻¹³. With σ = 1.01·norm the thresholds rise to 10^−32.7 and 10^−42.7.
- **c_D²Xh = 5·10¹⁰ costs only its own 10.7 orders, linearly.** It enters Q_N̄ (FH24 (3.59)) as δ σ_{Lᵀ} ½ c_D²Xh
  C²_ΔK̄, never multiplied by γ⁻ᵏ: changing it by 10⁴ moves the threshold by 3.9 orders.

**Decomposition of the gap**, from our best previous estimate (v2-type, 10⁻⁷⁵) to FH's normal threshold 10⁻⁴⁴: 31
orders.

| Source | Orders |
|---|---:|
| γ⁴ → γ² (γ = 2.7·10⁻⁷ in period-1 units) | 11.5 |
| δ^{4τ} → δ^{2τ+1} | 6.8 |
| the sharp frequency-specific c_R at the first bites (legitimate through the lemma pre-steps) | 9.1 |
| tangential and normal constants tracked separately | 1.2 |
| constants | 0.5 |
| unexplained | 1.9 |

The tangential component (37 orders) splits as 17.3 (γ³), 11.0 (δ^{6.2}), 9.1 (sharp c_R) and −0.4 (rest). The v1
value 10⁻¹³⁷ is a further 62 orders lower: one size M = c_D²Xh = 5·10¹⁰ is put into every constant (|X_h| = 0.09 and
|DX_h| = 129 in reality) and compounded with γ⁴.

### 2.2 Our theorems on FH's data

`scripts/sjs/sjs_thresholds.py` runs the mirrors on FH's data: v0, v1, and SHARP-PLUS's route B (`thresholds_v2.py`,
FH24's modified step plus the v2 levers, read-only), with classical or frequency-specific small-divisor constants. The
mirrors take integer τ only, so τ = 2 and τ = 3 bracket FH's 2.4. FH's norms are used unchanged, in period-1 angles.

log₁₀ of the threshold on the invariance error at FH's strip ρ = 0.1 (2π units). Route B uses SHARP-PLUS's levers
(L1 split derivative bounds M₀ = 0.09, M₁ = 129, M₂ = c_D²Xh = 5·10¹⁰; measured torsion |⟨T⟩⁻¹| = 354 and
sup |T|; caps), 2 frequency-specific stages and the classical tail unless stated.

| τ | γ (FH units) | v0 | v1 | Route B, v1's c_R | Route B, classical c_R | Route B, frequency-specific (2 stages) | + frequency-specific tail (estimate) |
|---|---|---:|---:|---:|---:|---:|---:|
| 2 | 1.69·10⁻⁶ (FH) | −539.3 | −127.5 | −57.2 | −53.2 | −49.8 | −47.6 |
| 2 | 1.85·10⁻⁵ (numerical) | −535.1 | −123.3 | −55.1 | −51.1 | −48.5 | **−46.5** |
| 3 | 1.69·10⁻⁶ (FH) | −549.9 | −140.3 | −62.8 | −57.5 | −54.1 | **−52.1** |
| 3 | 1.85·10⁻⁵ (numerical) | −545.7 | −136.2 | −60.8 | −55.4 | −52.0 | −50.0 |

Reading the ladder (τ = 2, numerical γ):
- **v1 → route B: 68 orders.** This is the modified Newton step (γ⁻⁴δ^{−4τ} → γ⁻²δ^{−2τ−1}), the split derivative
  bounds (c_D²Xh no longer multiplies everything) and the measured torsion together. It is the decisive lever.
- **Rüssmann → classical c_R: 4 orders.** Then **classical → frequency-specific: 2.6 orders** at the first two
  stages and **2 more** from the tail estimate.
- **FH's γ → numerical γ: 1.1 orders** (τ = 2) and 2.1 (τ = 3).
- **More stages do not help.** k = 6 or 10 frequency-specific stages give −46.7…−52.1, no better. The binding
  condition is the tail convergence radius ("tail decay"): route B's weighted error uses the weight γδ^κ, not
  Γ_spec.
- **Design remark for SHARP-PLUS.** With Γ_spec in that weight (`--geff`, an effective γ from S(ω, δ), an
  emulation) the thresholds become **−44.2 (τ = 2) and −43.8 (τ = 3)**, the level FH24 reaches with their 10
  lemma pre-steps (normal component −44 reported, −45.9 re-evaluated).

Route A (the additive step, with the same levers) was not evaluated separately. §2.1's decomposition puts the cost of
the additive step at about 18 orders: 11.5 for γ⁴ → γ² and 6.8 for the δ powers. So route A would land near −65…−70,
the order of the brief's v2-type range (10⁻⁷⁵…⁻⁸⁶).

**First integrals.** FH reduce the total angular momentum before applying their theorem, so it runs with d = n = 3
and no integral. Our theorems (v0–v2) have no first-integral version either, so a certificate must work in a reduced
chart, which is the expressibility question of §3. The threshold numbers above already assume the reduced system.

**v2's own hybrid lever L6** (a measured step 0 instead of the a-priori bound) is not in the mirror. On the lunar R1
package it moves route B from 10⁻¹²·⁰ to about 10⁻⁴·⁵. Halving log₁₀ T here gives **−23…−26**. That is an analogy,
not a computation, and is labelled "estimate" wherever it is used.

### 2.3 Frequency data: the dominant lever for this frequency vector

`scripts/sjs/sjs_freq.py` gives the numbers below. In FH's units, ω = (0.083955, 0.033824, −1.8501·10⁻⁵) rad per
time unit: two fast frequencies and one secular frequency, 4500 times slower.

- **γ.** Over |k|₁ ≤ 2000, inf |k|₁^τ|k·ω| = 1.85·10⁻⁵ at k = (0, 0, 1), for τ = 2, 2.4 and 3 alike.
  - FH25's certified γ = 1.69·10⁻⁶ is **11× smaller**. FH certify, by the measure-of-rotations technique, that *some*
    (γ, τ)-Diophantine vector lies within 10⁻⁸⁰ of the ephemeris frequency; that vector is not explicit.
  - The 5:2 near-resonance, 2ω₁ − 5ω₂ = −0.00121, is compensated at k₃ ≈ −65 but does not set γ.
  - An explicit algebraic frequency in a cubic field, with a norm-type proof (as `CubicDiophantine.lean`), could reach
    the numerical value. Every power of γ is then worth 1.04 orders.
- **Small divisors.** The Rüssmann/classical constant pays γ⁻¹δ^{−τ} on *every* mode. The frequency-specific sum
  S(ω, δ) = Σ|k·ω|⁻²e^{−4πδ|k|₁} pays mainly for the slow mode k = (0, 0, 1) and the near-resonant fibres. At the
  first bites:

  | Bite | S | Γ_spec | Classical Γ (FH's γ) | Ratio |
  |---|---:|---:|---:|---:|
  | δ₀ = ρ/6 = 0.00265 | 2.77·10¹² | 7.5·10⁵ | 1.9·10¹¹ | 2.5·10⁵ (10^5.4) |
  | ρ/12 | 2.17·10¹³ | | | 10^5.7 |
  | ρ/24 | 2.29·10¹⁴ | | | 10^5.9 |

  The literature subagent's independent sum gives c_R(ρ/6) about 5·10⁵ below FH24's uniform ĉ_R, which agrees.
- **Who uses it.** FH use the sharp constant only inside the Iterative Lemma steps (worth 9.1 orders on their result).
  v2's L2 (frequency-specific stage data, SHARP-PLUS) uses it in the theorem itself, and the kernel-cheap fibered form
  is already landed (`KAM.smallDivisorSum_snoc_le_fiber`, SHARP-L2B).

### 2.4 From threshold to digits and support

The model (`scripts/sjs/sjs_support.py`):
- **Decay.** FH25 Fig. 3 fits the coefficient decay per angle: r = (0.524, 0.417, 0.316) per mode (2π angles; the
  secular angle ĝ decays slowest).
- **Kept coefficients.** On the strip ρ the certificate keeps every k with Σ_i (r_i − ρ)|k_i| ≤ L ln 10: a
  cross-polytope with S = (4/3)Π_i L ln 10/(r_i − ρ) points and box/support = 6.
- **Digits.** L = −log₁₀T + 6: two orders of headroom plus about 4 for the edge-term count and the derivatives.
- **Calibration.** FH's 1024³ grid at error 3.6·10⁻⁵⁴ corresponds to L ≈ 54–60 here (box 5.3·10⁸ against their
  1.07·10⁹).
- **Strip optimization** uses T(ρ) ∝ ρ^{2τ+1} (route B) or ρ^{4τ} (v1).

| Threshold | Best ρ | L | S (product model) |
|---|---:|---:|---:|
| v1, 10⁻¹³⁰ | 0.01 | 146 | 7.9·10⁸ |
| FH24-type, 10⁻³⁸ | 0.02 | 48 | 3.1·10⁷ |
| 10⁻³⁰ | 0.02 | 40 | 1.8·10⁷ |
| 10⁻²⁰ | 0.03 | 29 | 7.3·10⁶ |
| 10⁻¹⁵ | 0.04 | 23 | 4.1·10⁶ |

The applications study's S(L) ignored the strip weight e^{ρ|k|}, which multiplies S by 2.4 at ρ = 0.1. Section 3 shows
that the product model itself overcounts by 7–14×.

## 3. Representation of the torus (brief item 2)

`scripts/sjs/sjs_model_support.py` provides a small reproducible model. It takes the planar SJS perturbation H₁ of
FH25 (2.1) in Delaunay angles at the real elements: α = a_J/a_S = 0.5455, e = (0.0489, 0.0565), Kepler's equation
solved on the grid. This is the source of every harmonic of the torus at first order in μ. Its FFT on a 256³ grid
(double precision, noise floor 10⁻¹⁴, only trusted counts reported) gives the following.

| ρ | L | S_true | Product model from its own per-axis decay rates | Ratio | Box, Delaunay frame | Box, adapted frame |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 8 | 4,898 | 62,400 | 12.7 | 225,321 | 57,285 |
| 0 | 12 | 18,984 | 211,000 | 11.1 | 867,825 | 191,835 |
| 0.05 | 10 | 18,468 | 166,000 | 9.0 | 1,307,647 | 232,199 |
| 0.10 | 6 | 7,558 | 50,800 | 6.7 | 962,143 | 128,947 |

The per-axis marginal rates of the model are 0.554, 0.459 and 0.525 (FH's torus: 0.524, 0.417, 0.316). At ρ = 0 the
model fits S_true(L) ≈ 4.6 L^{3.35}.

What each representation choice does:
- **d'Alembert skewness: ÷7 to ÷14 on S (model evidence).**
  - Rotation invariance ties the indices: the harmonic k₁ℓ₁ + k₂ℓ₂ + mĝ has size ~ e₁^{|m−k₁|}e₂^{|m+k₂|}α^{(…)}. So
    the coefficients live in a skewed slab around the line k₁ ≈ m ≈ −k₂, not in an axis-aligned octahedron.
  - The count of the true set is frame-invariant, and it is 7–14× below the product model built from per-axis
    marginals, which is what FH's Fig. 3 reports.
  - Applying the ratio to FH's torus (its ĝ-decay is slower than the Hamiltonian's) is an inference, flagged as such.
- **Resonance- or d'Alembert-adapted unimodular frame: S unchanged, box ÷4.6.**
  - A unimodular change of angles relabels lattice points, so the count cannot change.
  - It changes the box of packed products: box/S drops from 46 (Delaunay frame) to about 10 in the frame
    (k₁, k₂, m) → (k₁, k₂, m − k₁) of mean-longitude-type angles. The product model assumed 6.
  - It also changes the strip weight |k|₁ and the norms, as the lunar rotated frame did (𝔪 from 3.6 to 2.0).
- **Reversibility: ÷2 on S.** The planar problem is reversible under (ℓ, g) → (−ℓ, −g). The torus has real
  cosine/sine data (half lattice), and the parity lever K-b of `CERTIFIER-SHARPNESS.md` §4.3 applies.
- **Charts: no gain on S; a gain on M; a blocker for expressibility.**
  - **No gain on S.** The slow decay is intrinsic. The fast harmonics decay like the Laplace coefficients, α^{|k|}
    (rate 0.61 per mode), and that does not depend on the chart. Poincaré variables are regular at e = 0 but give the
    same angle content.
  - **A gain on M.** c_D²Xh = 5·10¹⁰ comes from the Delaunay chart's derivatives near e ≈ 0.05: e = √(1 − G²/L²)
    makes ∂_G derivatives grow like powers of 1/e. A regularized chart can cut it by orders. Under route B that is
    worth at most about the same number of orders (c_D²Xh is linear, §2.1).
  - **Expressibility.** Delaunay variables need Kepler's equation E − e sin E = ℓ inside H. The certifier's `HamExpr`
    has no implicit functions. It would need an implicit-function witness primitive (the certificate supplies the
    series E(θ); the checker bounds E − e sin E − ℓ and applies a contraction argument, like the exp witnesses),
    about 1–2k Lean lines.
  - The applications study's eccentric-anomaly time change regularizes one Kepler problem, not two with different
    anomalies. Poincaré heliocentric Cartesian variables make H explicit (division and `sqrt`), but the torus is not
    primary there.

## 4. Preliminary normalization (brief item 3)

A certified canonical change Φ (a few Lie-series or Kolmogorov steps, in the manner of Locatelli–Giorgilli) makes the
torus nearly flat in the new variables: K′ ≈ (θ, I*) + small, with small support. The difficulty does not disappear,
it moves.
- **The Hamiltonian the checker must evaluate becomes H∘Φ.** Φ is the time-one flow of a generating function χ, or a
  truncated Lie series that is not exactly canonical. Neither is a `HamExpr`. Two ways to keep the theorem honest:
  1. **Certify the truncated normalized model.** Truncate H∘Φ to a finite Fourier–Taylor polynomial and certify the
     torus of that polynomial. Its support is about the torus support it replaced, since the Fourier content moves
     from K into χ and H′. The theorem is then about a truncated model, not about the true system. This is what
     LG00, LG07 and GLS09 do (section 7).
  2. **A flow-composition primitive.** The checker evaluates H(Φ(K′(θ))) with verified Taylor-model enclosures of
     the flow of χ. That is new verified-ODE infrastructure (about 5–15k Lean lines, none in Mathlib at the required
     level). The composition still needs Φ∘K′ = K with its full Fourier content to the required accuracy, so the
     kernel's Fourier load does not drop.
- **Effect on S: none for the true system.** Information is conserved: the d'Alembert-limited support of section 3
  is a property of H, and any certificate of the true system must resolve it somewhere.
- **Effect on the constants: real but secondary.**
  - The torsion becomes the Hessian of the normal form: well conditioned, against |⟨T⟩⁻¹| = 354 in FH's chart.
  - σ_K and σ_B become close to 1.
  - The γ and δ powers are unchanged, and they dominate (section 2).
- **Verdict.** Normalization is the right tool for a truncated-model milestone (section 7), not for the true system.

## 5. Kernel arithmetic (brief item 4)

`scripts/sjs/results/kernel_probes.md` has the full report. Setup:
- probes generated by `kernel_probe_gen.py` into `.drafts/`, run one at a time with `nice -n 5 lake env lean`;
- each times one `theorem … := by decide +kernel`, with no heartbeat or recursion overrides;
- the machine was at load 12–14 on 16 cores, so every timing is ±30 %.

**Scope.** This worktree has the landed packing from before D34. The D34 fix (sparse blocks, mask/shift decode)
lives on a farm branch, so I measured my own prototypes of its ideas (`F*` probes, measurement devices without
soundness proofs). SO-PACKFIX's one reported shard (about 2–3 ms per window slot) is the same order as the
prototype.

**Measured.**

| Object | Size reached | Cost |
|---|---|---|
| Landed `checkPackedProduct` (2-D box, 200 bits) | S = 961 terms | 4.1 / 9.6 / 61.6 s at S = 225 / 441 / 961; t ≈ 1.3·10⁻⁴ S^{1.9±0.3} s, extra memory 6.8·10⁻⁴ S^{1.28} GB. One landed shard at S = 10 201: 188 s, 9.9 GB |
| Prototype (D34-like) full product | S = 3 025 (2-D), 729 (3-D box), 377 (3-D diamond) | 1.25–1.48 ms per factor term packed, 0.6–0.95 ms per advice slot packed, 0.20–0.34 ms per slot decoded, block products negligible; 82 kB per advice slot, 260 kB per factor term |
| Advice slots per factor term (layout inflation) | | 2-D box 7.7, 3-D box 13.5, 2-D diamond 15.5, 3-D diamond 83 (asymptotically 96), 4-D box ≈ 32, 4-D diamond ≈ 768 |
| GMP in the kernel | 4·10⁸-bit products | mul 6.6 ns per bit; add, and, shift 4–17 ms per 10⁸ bits |
| Per-coefficient passes (`supNormUp`, `add`, `toDeg`) | S = 10 201 | 0.5–1.6 ms per term, linear; precision (170 vs 300 bits) irrelevant |
| `weightedNormUp`, C1 `cornerLeq` | | fail at S = 10 201 (`foldr`: the kernel cannot reduce the recursion) |
| `toMants` | | superlinear: 1.7 → 6.5 → > 59 ms per term at S = 961 / 3 025 / 10 201 |
| Floor: walking a literal list | | 190 µs and 21 kB per element |
| Model op in a compose (scalar route, add) | S = 961 | 0.9–1.26 ms and 220 kB per term per live op |

**What dominates.** The cost is not big-integer arithmetic. It is the kernel's interpretive overhead: a few hundred
µs and 20–250 kB for every coefficient, advice slot and list cell. Three things multiply it:
- the layout inflation in 3-D;
- the number of products and model operations;
- passes repeated across shards (each shard declaration re-packs its factors unless the packed blocks are
  certificate data).

Precision barely enters: fewer bits do not help the per-slot design.

**Composition and C7's `composePruned`** (orchestrator's question).

| S | E alone | I alone | E + I, separate declarations | E ∧ I, one declaration | One compose [e, i] | `composePruned` | All slots forced |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 441 | 5.5 | 5.7 | 11.2 | 7.8 | 8.5 | 8.0 | 11.7 |
| 961 | 15.9 | 15.3 | 31.2 | 24.5 | 24.5 | 24.0 | 34.2 |

- **No gain inside one declaration, at any size.** The whnf cache already shares the common prefix and laziness
  already skips dead `mul`/`add`. That depends only on which slots are demanded, not on S. Separate declarations
  pay the shared prefix twice (+27 %).
- **Not measured at 10⁴–10⁵ terms.** At 220 kB per term per live op, a 14-op compose at S = 10⁴ needs about 31 GB,
  beyond the 8 GB probe budget. The mechanism above is independent of S.
- **Pruning itself costs.** C7's `liveSet` + `pruneOk` take 17.5 s and 5.9 GB on the 887-op lunar program, and fail
  (deep recursion) on a 2 860-op planetary toy.
- **At SJS sizes memory forces each model op into its own declarations,** with intermediate models supplied as
  certificate data. Dead ops then cost nothing because the generator never emits them. So C7 pays nothing at scale.
  If kept, `liveSet` needs a near-linear rewrite.

**Jet counts** (`jet_counts.py`, the Python mirror of the landed jet compiler):
- **Lunar:** 887 ops, 658 of them on models. Invariance and energy share 140 model ops; there is 1 genuine
  model × model product.
- **Planetary-type toy (n = 4):** 2 860 ops (16 modes) to 20 068 (64 modes), with 49–204 genuine products for
  invariance and energy.
- **For SJS** I use 60–150 full-precision products, 500–2000 scalar/add model ops, and a Gram/torsion stage of
  300–600 products and 1000–3000 ops on the 17-digit support. These are hand estimates for a reduced chart with
  inv/sqrt witnesses.

**What a redesign reaches** (per product with S terms in 3-D, layout box/support β):

| Design | Cost per product | S = 3.6·10⁶ (route B), β = 10 | Largest single declaration in 32 GB |
|---|---|---:|---|
| Landed | ≈ 1.3·10⁻⁴ S^{1.9} s, unsharded | out of reach | ≈ 4 100 terms (2-D) |
| D34-like per-slot (prototype constants) | S·(2.8 + 13.5 β) ms | 140 CPU-h | ≈ 3.5·10⁵ advice slots, ≈ 6 min |
| Same with an ideal sparse layout (β → 1) | S·16 ms | 16 CPU-h | same |
| GMP-resident packed algebra (hypothetical) | 3.4·10⁻⁸ s per factor bit, factor bits ≈ 3.4 w β S | 32 min, 28–56 GB peak (1–2 blocks) | one whole product up to S ≈ 1.8–3.6·10⁶ at β = 10 (3.0–6.0·10⁶ at β = 6), 16–33 min |

**The GMP-resident design.** Every model is stored as one Kronecker-packed integer with offset (non-negative) digits
of fixed width w. Each model operation is then a constant number of big-integer operations:
- **add and scalar multiplication** directly on the packed integers;
- **product** by one multiplication;
- **rounding** by mask, shift and compare against a constant periodic mask, with no advice at all;
- **ℓ¹ and weighted norms** by one product with a packed weight table, reading the middle digit;
- **absolute values** by sign-bit masks.

Its kernel time is GMP time. At β = 10 that is about 250× less than the per-slot route per product, and 500–2000×
less per add.

It is hypothetical: none of this algebra or its soundness proof exists. The estimate rests only on the measured GMP
throughput and on a 4–8× memory factor over the factor size, which was not measured at 10¹⁰ bits. Its Lean cost is
a new layer of the size of `KAM/Certificate/Poly` (3 040 lines today); my estimate is 3–6k lines.

**Suspected defects in landed code** (SO-owned; reported, not touched):
- `weightedNormUp` and `cornerSumUp` use `foldr` and fail at about 10⁴ terms;
- `toMants` is superlinear;
- the landed `intSlotsBound` has a cliff at about 6 000-slot windows (403 s, 7.6 GB, cause not isolated);
- C7's `liveSet` is quadratic in program length.

## 6. Compute (brief item 5)

`scripts/sjs/sjs_cost.py` (output in `results/sjs_cost.log`) combines:
- the thresholds of §2.2;
- the strip-optimized support of §2.4, divided by 7 (d'Alembert, the conservative end) and by 2 (reversibility);
- the Gram/torsion stage on the 17-digit support (lunar cfgLow);
- the kernel constants of §5;
- the operation counts above.

All figures are per torus. CPU-h is single-thread kernel time; declarations run in parallel. Each range is low to
high operation counts.

| Scenario | ρ | L | Bits | S (true) | Per-slot, box layout (β = 10) | Per-slot, ideal layout | Declarations ≤ 29 GB (box) | Advice (box) | GMP-resident | Applications study's model (tier P) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Applications baseline (S 10⁸ product model, box 6) | 0.10 | 85 | 307 | 1.0·10⁸ | 1.7–4.4·10⁵ | n/a | 1.9–5.2·10⁶ | 23–60 TB | 1.7–8.6·10⁴ (23–46 blocks) | 5.9·10⁶–1.1·10⁷ |
| v1 (−130) | 0.01 | 146 | 509 | 5.6·10⁷ | 1.4–3.6·10⁵ | 2.5–7.8·10⁴ | 1.5–4.1·10⁶ | 32–83 TB | 4.0·10⁴–2.0·10⁵ (35–70 blocks) | 7.4·10⁶–1.4·10⁷ |
| v2 route B (−46.5) | 0.02 | 57 | 212 | 3.6·10⁶ | 0.99–2.5·10⁴ | 1.8–5.3·10³ | 1.1–2.8·10⁵ | 1.0–2.5 TB | **34–167** (1–2 blocks) | 2.9–5.7·10⁵ |
| v2 route B (−52.1) | 0.02 | 62 | 231 | 4.7·10⁶ | 1.3–3.3·10⁴ | 2.3–6.9·10³ | 1.4–3.7·10⁵ | 1.4–3.5 TB | **93–351** (2–3 blocks) | 4.0–7.8·10⁵ |
| v2 hybrid L6, estimate (−23.3) | 0.03 | 32 | 132 | 7.2·10⁵ | 3.0–7.1·10³ | 500–1 400 | 3.2–7.8·10⁴ | 0.2–0.5 TB | **6–15** | 0.6–1.1·10⁵ |
| v2 hybrid L6, estimate (−26.1) | 0.03 | 35 | 141 | 9.2·10⁵ | 3.5–8.4·10³ | 590–1 700 | 3.7–9.3·10⁴ | 0.25–0.6 TB | **8–19** | 0.7–1.4·10⁵ |

**Calibration.** The same per-term constants price the lunar unit (R1) at 0.65 CPU-h, when only demanded operations
are evaluated and the cfgLow factors are trimmed. Tier P puts that unit at 7.5–14.5 CPU-h; SHARP-CERTSIDE found that
the landed certificate evaluates every jet slot at full support and does not trim cfgLow factors. The ratio, 11–22,
is not resolved here. **The per-slot and GMP columns assume the demanded-work design.** If the landed architecture's
extra work persists, multiply them by up to 20.

**Data elaboration** is a separate cost. In the per-slot design, the advice (box layout, route B) takes 1.7·10³–
1.9·10⁴ CPU-h to elaborate, at 0.18–0.6 ms per element, the same order as the kernel. The GMP-resident design needs
only K and the witness series, about 3–4 GB for route B. Ingesting multi-GB packed literals was not tested.

**Per shard (32 GB slice, 29 GB to the kernel after the 3.1 GB Mathlib import).**
- **Landed:** one declaration holds about 4 100 terms of a 2-D product.
- **Per-slot route:** at most 3.5·10⁵ advice slots per declaration (about 6 min), with the factors pre-packed as
  certificate data; otherwise each shard re-packs them at 260 kB per term. Model ops: at most 1.3·10⁵ term-ops
  per declaration (about 3 min). Route B needs 1–4·10⁵ such declarations per torus.
- **GMP-resident:** one whole product per declaration up to S ≈ 1.8–3.6·10⁶ (β = 10, L = 59) or 3–6·10⁶
  (β = 6), at 16–33 min. Route B's products need 1–3 blocks, and the hybrid's fit whole.

**Wall time.** This machine has 16 cores and 124 GB, so it runs 3 concurrent 32-GB declarations (about 12 at 8 GB).
A 1 000-core cluster at 32 GB per core runs 1 000.

| Scenario | This machine (3 concurrent) | 1 000-core cluster |
|---|---|---|
| v2 route B, per-slot, box layout | 4.5–15 months | 10–33 h |
| v2 route B, per-slot, ideal layout | 1–3 months | 2–7 h |
| v2 route B, GMP-resident | **0.5–5 days** | about 1 h (one product per declaration) |
| v2 hybrid, GMP-resident | **2–6 h** | about 10 min |

A certificate is checked once per torus, and one torus suffices for the headline result.

## 7. Intermediate milestones (brief item 6)

All entries are from the papers, as read by the literature subagent:

| Paper | Model | What is proved | Size |
|---|---|---|---|
| **LG00**, Locatelli–Giorgilli, CMDA 78 (2000) | Secular SJS: 2 degrees of freedom, polynomial of degree 6 in (ξ, η) (eq. 11; 69 printed monomials, all even in η; SJS-LG00), from degree 2 in fast actions, order 7 in eccentricity, 21 Laplace terms, averaged at order 2 in the masses | **Rigorous** (interval arithmetic) KAM for the truncated secular model: two invariant tori confining the secular motion (Thm 1). γ = 8·10⁻⁶, τ = 1 | Birkhoff to order 6 (truncated at degree 70, up to 5.9·10⁵ monomials), 33 explicit Kolmogorov steps; about 30 h of 2000-era CPU per run |
| **LG07**, Locatelli–Giorgilli, DCDS-B 7 (2007) | Full 3-body, spatial, Jacobi-reduced, 4 degrees of freedom; fast actions degree 3, (ξ, η) degree 10–12, Fourier \|k\| ≤ 20; averaged at order 2 | **Not rigorous** ("strong indication") | about 10⁷ coefficients, a week of CPU |
| **GLS09**, Giorgilli–Locatelli–Sansottera | as LG07; normal form of order 17, Fourier order 34 | **Not rigorous**; Nekhoroshev-type time about 10¹⁰ yr | over 7.1·10⁶ coefficients |
| GLS17 / SLG13 (Sun–Jupiter–Saturn–Uranus, secular, planar) | 3 degrees of freedom; 25 Kolmogorov steps, Fourier degree 50 | **Not rigorous** | intermediate Hamiltonian 9.4·10⁷ monomials |
| FH25 | Full planar SJS, 3 degrees of freedom (reduced) | **Numerical**; the computer-assisted proof is "in progress" | 1024³ grid, 76 digits, 194 GB |

**Verdict: LG00's secular model is the most striking milestone feasible now.** GLS17-type 3-degree-of-freedom secular
models come next, and LG07/GLS09 are not worth it.

- **LG00** (truncated secular SJS, 2 degrees of freedom).
  - **Why it fits.** The Hamiltonian is a degree-6 polynomial with 69 monomials (SJS-LG00 count), so it is a `HamExpr` today: no
    Kepler equation, no witnesses beyond the polynomial.
  - **Why it is cheap.** The tori surround an elliptic equilibrium, so in Cartesian secular variables (ξ, η) the
    embedding K: 𝕋² → ℝ⁴ is close to linear in cos θ and sin θ, and its harmonics decay at about the eccentricity
    ratio per mode. That puts S at 10³–10⁴ and n = 2: the lunar regime.
  - **Estimate, not computed here:** 1–100 CPU-h per torus under v1 with the current checker.
  - **Unknowns.** LG00's γ = 8·10⁻⁶ (τ = 1) enters v1 as γ⁴. The threshold and L have to be computed by a scouting
    package before this is promised.
  - **What it would be.** The first formally verified KAM theorem for a planetary model. It is a formal
    reproduction of a rigorous 2000 result, not new mathematics.
- **GLS17-type secular SJSU** (3 degrees of freedom, Fourier degree 50: S ≤ 1.7·10⁵ in 3-D).
  - Only numerical evidence exists, so a rigorous torus would be a **new result**, for a truncated model.
  - **Estimate,** with about 100 products and β = 10: about 10³ CPU-h per-slot (weeks here, a day on a cluster), or
    a few CPU-h GMP-resident. It needs v2 if γ is as small as LG00's.
- **LG07 / GLS09** (4 degrees of freedom, spatial, Fourier order 20–34, polynomial degree 10–12).
  - n = 4 multiplies the layout inflation (4-D box 32, 4-D diamond 768 advice slots per term), and the
    models have 10⁷ coefficients.
  - They are not feasible before the GMP-resident redesign. After it they cost at least as much as the true planar
    SJS, and they are truncated models.
- **FH25, the true planar SJS.** Sections 2–6 above and section 8.

## 8. Recommended path

In order. Each step is useful on its own.

1. **SJS-LG00 scout** (Python, about a day).
   - Rebuild LG00's secular polynomial (eq. 11, 69 monomials).
   - Compute its invariant tori in Cartesian secular variables.
   - Run `scripts/certifier/optimize.py` under v1 and the v2 mirrors.
   - This is the go/no-go for a v1 certificate with today's checker. On a go, the certificate is lunar-class: the
     first formally verified KAM torus of a planetary model.
2. **SHARP-PLUS route B with frequency-specific constants.** This is the decisive lever: 68 orders on SJS over v1.
   - Adopt the design remark: Γ_spec instead of γδ^κ in route B's weighted error. That is +2.3 to +8.3 orders here,
     and it reaches FH24's level.
   - Then the L6 hybrid (measured step 0), which halves log₁₀ T if the R1 analogy holds.
3. **Packed-arithmetic prototype** (a probe package, no soundness proofs).
   - In the kernel, at S = 10⁵–10⁶, measure: a packed-resident add; a product with rounding by mask and compare (no
     advice); a weighted ℓ¹ norm by one product with a weight table; a sign split.
   - **Go:** it stays within 2–3× of the GMP model (3.4·10⁻⁸ s per factor bit). Then write the algebra with its
     soundness proofs, about 3–6k Lean lines.
   - **No-go:** fall back on the per-slot route with a support-adapted sparse layout. That costs 10³–10⁴ CPU-h on a
     cluster.
   - Separately, the SO track should fix the four defects of §5 (`foldr` norms, `toMants`, the `intSlotsBound`
     cliff, `liveSet`).
4. **Chart and frequency.**
   - A reduced chart expressible as a `HamExpr`: either Kepler's equation through an implicit-function witness (1–2k
     Lean lines), or an algebraic rotating chart.
   - An explicit cubic-field frequency near FH's ω, with a certified γ (`CubicDiophantine.lean`).
5. **A GLS17-type secular model** (3 degrees of freedom, truncated; a new rigorous result). After step 2, and
   cheaper after step 3: estimated 10³ CPU-h per-slot, a few CPU-h packed.
6. **FH25's planar SJS.** After steps 2–4.
   - **Data:** FH25-scale numerics (about 4·10⁶ coefficients per component to about 60 digits), or FH's own data.
   - **Kernel:** 30–350 CPU-h with packed arithmetic, or 10⁴–3·10⁴ CPU-h on a cluster per-slot.

**Decision point.** Step 3's prototype decides the architecture. Steps 1 and 2 are worth doing whatever it shows.

## 9. Caveats

- **Thresholds come from mirrors.**
  - Route B is SHARP-PLUS's design, not Lean, and the mirrors take integer τ only (2 and 3 bracket 2.4).
  - FH's norms are reused as published, including c_D²Xh, |⟨T⟩⁻¹| and the unreported c_Th and c_DTh, which were
    guessed.
  - The frequency-specific tail is an extrapolation, and the γ_eff variant is an emulation.
  - The hybrid L6 numbers are an analogy with R1, not a computation.
- **Support.**
  - The d'Alembert ratio (7–14) is measured on the first-order Hamiltonian model, not on FH's torus, whose ĝ-decay
    is slower. 7 is used.
  - L = −log₁₀T + 6 carries a 4-digit allowance calibrated only against FH's grid.
  - The adapted-frame box ratio (10) was measured at L ≤ 12; it is 10–17 at small L.
- **Kernel.**
  - Single runs at load 12–14 (±30 %); fits on 3–7 points.
  - The D34-like route is a prototype without soundness proofs.
  - The GMP-resident algebra is hypothetical, and its memory factor was not measured at 10¹⁰ bits.
  - The 11–22× calibration gap against the lunar tier P is unresolved.
- **Operation counts** for SJS (60–150 full products, 500–2000 ops) are hand estimates. The jet mirror has no
  SJS chart.
- **Not costed:**
  - **The numerical torus.** About 4·10⁶ coefficients per component to about 60 digits in a reduced chart:
    FH25's computation used a 1024³ grid, 76 digits and 194 GB.
  - **The explicit Diophantine frequency.** A cubic-field vector near FH's ω needs a norm-type γ bound, which may
    be weaker than the numerical 1.85·10⁻⁵.
  - **The Lean work** of route B itself.
- **Errata-type observations about the sources** are in the handoff:
  - FH25's δ = ρ/6 sits on the boundary of FH24's open interval;
  - FH24 Lemma 2.14's chain c_R(δ) ≤ c_R(δ, m) ≤ ĉ_R is inconsistent as printed (a missing (2π)⁻² and a factor 4);
  - FH25 uses 2π-periodic angles and FH24 1-periodic ones.

## 10. Reproduction

All commands run from the worktree root with `python3 -I`; numpy and mpmath are required.

```
python3 -I scripts/sjs/sjs_freq.py --json scripts/sjs/results/sjs_freq.json            # gamma(tau), S(omega, delta)
python3 -I scripts/sjs/sjs_support.py                                                  # S(L, rho), threshold -> S
python3 -I scripts/sjs/sjs_model_support.py 256 --json scripts/sjs/results/sjs_model_support_256.json
python3 -I scripts/sjs/sjs_thresholds.py --json scripts/sjs/results/sjs_thresholds.json   # needs SHARP-PLUS's mirror (KAM_V2_DIR)
python3 -I scripts/sjs/sjs_cost.py --json scripts/sjs/results/sjs_cost.json            # section 6
python3 -I scripts/sjs/jet_counts.py scripts/sjs/results/jet_counts.json                # jet op counts (section 5)
python3 -I scripts/sjs/kernel_probe_summary.py                                          # fits of the probe records
python3 -I scripts/sjs/lit/fh25run.py; python3 -I scripts/sjs/lit/sens.py               # FH24 constants (section 2.1)
```

The kernel probes are described in `scripts/sjs/results/kernel_probes.md`. `kernel_probe_gen.py` writes a probe to
`.drafts/`, and `kernel_probe_run.py` runs it (one niced Lean process at a time) and appends the record to
`results/kernel_probes_raw.jsonl`.
