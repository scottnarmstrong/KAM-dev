# Can we certify a KAM torus of the planar Sun–Jupiter–Saturn system? (SJS-FEAS)

30 October 2026, branch `sjs-feas`. Feasibility study: Python, literature and small kernel probes. Nothing here is a
theorem or a certificate. The numbers come from:
- `scripts/sjs/*.py` (section 10);
- the kernel probes in `scripts/sjs/results/kernel_probes.md`;
- a re-evaluation of Figueras–Haro 2024's constants (section 2.1, scratch scripts cited there).

The question comes from `docs/explorations/striking-applications.md` §9, which calls Figueras–Haro's planar SJS torus
(FH25: J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152) "infeasible in the kernel by about 4 orders of magnitude in
support and 6 in cost": S ≈ 10⁸ Fourier coefficients at L ≈ 85 digits, ≥ 100 full-precision products, ≈ 10⁷ CPU-h.

⟨SUMMARY⟩

## 1. The gap, factor by factor

⟨GAP-TABLE⟩

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

**Re-evaluation** (literature subagent; FH24 Appendix B Tables 1–4 on FH25's data; scripts in the session scratchpad,
`lit/fh24consts.py`, `lit/fh25run.py`):
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

⟨THR-TABLE⟩

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

⟨KERNEL⟩

## 6. Compute (brief item 5)

⟨COMPUTE⟩

## 7. Intermediate milestones (brief item 6)

All entries are from the papers (literature subagent; page and equation references in the scratch report):

| Paper | Model | What is proved | Size |
|---|---|---|---|
| **LG00**, Locatelli–Giorgilli, CMDA 78 (2000) | Secular SJS: 2 degrees of freedom, polynomial of degree 6 in (ξ, η) (eq. 11; 129 monomials), from degree 2 in fast actions, order 7 in eccentricity, 21 Laplace terms, averaged at order 2 in the masses | **Rigorous** (interval arithmetic) KAM for the truncated secular model: two invariant tori confining the secular motion (Thm 1). γ = 8·10⁻⁶, τ = 1 | Birkhoff to order 6 (truncated at degree 70, up to 5.9·10⁵ monomials), 33 explicit Kolmogorov steps; about 30 h of 2000-era CPU per run |
| **LG07**, Locatelli–Giorgilli, DCDS-B 7 (2007) | Full 3-body, spatial, Jacobi-reduced, 4 degrees of freedom; fast actions degree 3, (ξ, η) degree 10–12, Fourier \|k\| ≤ 20; averaged at order 2 | **Not rigorous** ("strong indication") | about 10⁷ coefficients, a week of CPU |
| **GLS09**, Giorgilli–Locatelli–Sansottera | as LG07; normal form of order 17, Fourier order 34 | **Not rigorous**; Nekhoroshev-type time about 10¹⁰ yr | over 7.1·10⁶ coefficients |
| GLS17 / SLG13 (Sun–Jupiter–Saturn–Uranus, secular, planar) | 3 degrees of freedom; 25 Kolmogorov steps, Fourier degree 50 | **Not rigorous** | intermediate Hamiltonian 9.4·10⁷ monomials |
| FH25 | Full planar SJS, 3 degrees of freedom (reduced) | **Numerical**; the computer-assisted proof is "in progress" | 1024³ grid, 76 digits, 194 GB |

⟨MILESTONES⟩

## 8. Recommended path

⟨PATH⟩

## 9. Caveats

⟨CAVEATS⟩

## 10. Reproduction

All commands run from the worktree root with `python3 -I`; numpy and mpmath are required.

```
python3 -I scripts/sjs/sjs_freq.py --json scripts/sjs/results/sjs_freq.json            # gamma(tau), S(omega, delta)
python3 -I scripts/sjs/sjs_support.py                                                  # S(L, rho), threshold -> S
python3 -I scripts/sjs/sjs_model_support.py 256 --json scripts/sjs/results/sjs_model_support_256.json
python3 -I scripts/sjs/sjs_thresholds.py --json scripts/sjs/results/sjs_thresholds.json   # needs SHARP-PLUS's mirror (KAM_V2_DIR)
python3 -I scripts/sjs/sjs_cost.py                                                     # section 6
```

The kernel probes are described in `scripts/sjs/results/kernel_probes.md`.
