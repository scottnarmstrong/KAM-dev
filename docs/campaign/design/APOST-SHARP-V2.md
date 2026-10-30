# APOST-SHARP-V2: the least crude explicit a-posteriori KAM theorem (SHARP-PLUS)

30 October 2026. Branch `sharp-plus` (from `apost-sharp`). Design study: Python, LaTeX and signature probes; no Lean proof.

**Contents.**
- §0 summary;
- §1 benchmark (HL19, FH24) on R1;
- §2 competitors;
- §3 loss inventory (L1–L8);
- §4 the v2 design;
- §5 dominance;
- §6 expected thresholds and costs;
- §7 honest comparison;
- §8 errata;
- §9 reproduction.

Every number comes from a script in `scripts/apost_sharp/`. All of them are untrusted design tooling: exact rationals for the
constants, double precision for measured norms and small-divisor sums, sampled sups where it says "measured".

## 0. Summary

- **Benchmark.** On the lunar package R1, with the same inputs:
  - Haro–Luque 2019 (HL19) reaches 10⁻²⁹·⁵. v1 (the sharp design being proved) reaches 10⁻²⁴·⁷ (fixed frequency) and 10⁻²⁵·⁰
    (iso), so v1 already beats HL19 by 4.7 orders on v1's own data.
  - HL19 accepts finer data (σ_Kᵀ, separate bounds on X_h and its derivatives) and then reaches 10⁻²³·⁵, which beats v1.
  - The strongest competitor is **Figueras–Haro 2024** (FH24, Physica D 462, arXiv:2304.10205). Its *modified* Newton step (tangential
    correction by composition) gives a smallness e/(γ²δ^{2τ+1}) instead of e/(γ⁴δ^{4τ}). It reaches 10⁻¹⁹·⁶ on v1's data and 10⁻¹⁴·⁷
    on the finer data.
- **The v2 design.**
  - **Route B** is the FH24 modified step. To it v2 adds:
    - a stage-0 anisotropic weight;
    - small-divisor constants at each bite (full-strip Bessel, frequency-specific);
    - refined certificate data (|Lᵀ|, |N|, |Nᵀ|, |T_h|, separate |DX_h|, |D²X_h|);
    - a stage-dependent engine with an exact prefix.
  - **Route A** (v1's additive step with the same levers) is kept as a second branch. The smallness of the final theorem is the
    disjunction, so v2 is never worse than v1.
  - The frozen form keeps `IG1Body`'s conclusion. Only `checkSmallness` changes.
- **Numbers (R1, iso).** See §6 for the full tables; the ranges below cover the fixed and iso forms.
  - v1: 10⁻²⁴·⁹⁸.
  - v2 route A: 10⁻¹¹·⁴. v2 route B: 10⁻¹²·⁰ to 10⁻¹²·⁴.
  - **Hybrid** (first Newton step measured by the certificate, L6): about 10⁻⁴·⁵ on R1's own residual.
  - H50 (tori closer to the separatrix, ν = 1 − 1/(50+g)): v1 10⁻²⁷·⁴, v2 10⁻¹²·⁴ to 10⁻¹³·².
- **Dominance.**
  - On a 108-point grid (n = 2, 3, 4; τ = n−1 and τ = 2 for n = 2; γ and ρ from 10⁻³ to 10⁻¹; norms 1, 3, 10), v2 on the same data
    beats HL19 and erratum-corrected FH24 at **every** point. The minimum margin is +0.03 orders and the median +0.6.
  - FH24 *as printed* wins at about half the points, by up to 0.9 orders. In every case this is because of its erratum (3.72), which
    multiplies by σ_L where the valid bound needs σ_Lᵀ = 2nσ_K. That is not a valid bound, so it is not a real win.
  - On R1's own finer data, v2 beats FH24 by 0.5 orders.
- **Recommendation.**
  - Fund route B and the hybrid corollary (packages B1–B8, about 6k Lean lines; §4.5).
  - The SO certificate gains about 13 orders from route B, and up to 20 from the hybrid.
  - Route A's levers (package B9, optional) add about one more order on R1.

## 1. Benchmark on R1 (task 1)

### 1.1 What was evaluated

- **HL19** (arXiv:1711.05515v1), Theorems 3.1 and 3.6. `scripts/apost_sharp/benchmark_hl19.py`.
  - Each constant of Appendix B (Tables 1–5) is cited by equation number, specialised to the canonical case d = n.
  - The canonical case is HL19's Case III, since J² = −I; so A = 0 and every starred constant vanishes.
- **FH24** (arXiv:2304.10205v1), Theorem 2.18. `scripts/apost_sharp/benchmark_fh24.py`.
  - Each constant of Appendix B (Tables 1–4) is checked against the PDF.
  - An independent re-derivation of the canonical case matches it exactly.
- **The same small-divisor constant for all theorems.** HL19's Lemma 4.1 leaves c_R open. FH24's printed ĉ_R is twice the classical
  value (§8).
- **Two readings of the margins.**
  - *Stated*: the competitor's σ = ours, margin μ. This is generous to the competitor, whose conclusion is weaker.
  - *Normalised*: the competitor gets σ − μ/2 and a domain shrunk by μ/2, so that its conclusion implies the frozen one. This is the
    like-for-like comparison.
- **Free parameters** are optimised: HL19's a₁ and ν_HL; FH24's δ, ν and both control constants.

### 1.2 Results (log₁₀ of the largest admissible e)

| Theorem | Form | Data | c_R | Stated | Normalised |
|---|---|---|---|---:|---:|
| sealed `g1_explicit` | fixed / iso | v1 | 1 | −76.55 / −74.51 | |
| v1 sharp design | fixed / iso | v1 | 0.316 | −24.72 / −24.98 | |
| HL19 Thm 3.1 = 3.6 | fixed / iso | v1 (σ_Kᵀ = 2nσ_K) | 0.316 | −29.46 | −29.43 |
| HL19 Thm 3.1 / 3.6 | fixed / iso | finer (measured σ_Kᵀ, M₂) | 0.316 | −23.49 / −23.74 | −23.46 / −23.71 |
| FH24 Thm 2.18 | fixed | v1 | 0.316 | −19.62 | −19.71 (corrected −20.14) |
| FH24 Thm 2.18 | fixed | finer | 0.316 | −15.38 | −15.49 (corrected −15.52) |
| FH24 Thm 2.18 | fixed | finer | 0.0814 | −14.58 | −14.73 (corrected −14.74) |

**HL19's binding entry.** It is the quadratic one, a₁^{4τ}C_E. On v1's data its derived torsion bound is C_T = 1690, against v1's
H_T = 109. HL19 bounds X_N through L_ω-estimates of L, B and N, while v1 uses the torsion polynomial. With the finer data C_T = 124.

**FH24's binding entries.** They are Q (the quadratic entry) and ⟨T⟩⁻¹ (the twist-margin entry), tied at the optimum by the control
constant κ.

**HL19's iso constants.** HL19 Thm 3.6 adds C_ω = σ_ω|ω*|, C_Δω, and the energy terms of Table 4. None of them binds on R1.

## 2. Competitors (owner directive, item 1)

**Search.** The search is recorded in the helper reports (scratchpad `competitors-report.md`, `l5-report.md`). It covered:
- arXiv listing searches;
- web searches on "explicit constants" a-posteriori KAM for flows, 2005–2026;
- the citing papers of HL19 and of FHL17;
- the authors' pages (Haro, Figueras, Villanueva, Celletti, Locatelli).

| Competitor | Setting | Explicit? | Smallness | Verdict |
|---|---|---|---|---|
| **FH24**, Physica D 462 (2024) 134127, Thm 2.18 | flows, isotropic/Lagrangian tori, first integrals, general compatible triple | yes (App. B) | (C/(γδ^{τ+1}))·max{‖ηᴸ‖, ‖ηᴺ‖/(γδ^τ)} < 1, i.e. ~e/(γ²δ^{2τ+1}) | **The best published.** v2 route B adopts its step and dominates it on the grid (§5). No iso version. |
| HL19, arXiv:1711.05515, Thms 3.1, 3.6 | flows, first integrals; iso version | yes (App. B) | C₁e/(γ⁴ρ^{4τ}) < 1 | Dominated by v1 on v1's data and by v2 everywhere (§5). Its iso Thm 3.6 is the only published explicit iso theorem of this type. |
| Calleja–Haro–Porras 2025, JDE 449, arXiv:2503.09740 | Lagrangian tori, flows with ℓ ≥ 1 quasi-periodic time frequencies | yes (App. C) | C₁e/(γ⁴ρ^{4τ}) < 1 (HL19 structure, Cauchy-free torsion) | Not literally autonomous. Same γ⁴ structure as HL19, so structurally dominated by route B. Not transcribed (marked unverified). |
| FHL17, FoCM 17 (2017), arXiv:1601.00084 | **maps** | yes | a₁^{4τ}Ĉ₅e/(γ⁴δ₀^{4τ}) < 1 | Different setting. Its gain is computer-assisted c_R(δ) and heavy rigorous FFT, adopted as L2. Standard map: E ≤ 2.7·10⁻⁴¹, condition 0.08, 0.004% below breakdown. |
| FHL18, arXiv:1703.06809 | the Rüssmann estimate | — | — | Ad hoc bound overestimates the true norm by 2–4 for n = 1 and ≥ 10 for n = 2 (the Parseval step); classical bound by 10–10⁴. |
| Villanueva 2017, J. Nonlinear Sci. 27, Thm 2.6 | flows, Lagrangian | **no** (Remark 2.8) | m/(γδ^{ν+1})(μ₃ + (μ₁+μ₂)/(γδ^ν)) < … | The origin of the composition device; not explicit. |
| Villanueva 2008, JDE 244 | Kolmogorov normal form | yes | ε/(γ²δ₀^{2τ+6}) ≤ 1 | Near-integrable setting, not a-posteriori on general tori. |
| dLGJV 2005, Nonlinearity 18, Thm 5 | flows | no | cγ⁻⁴δ₀^{-4σ}‖e‖ < 1 | Not explicit; suspected erratum (γ^{+2} in Thms 3, 6). |
| Calleja–Celletti–de la Llave 2013, JDE | conformally symplectic | no (flows); 2-D maps explicit with 1/(\|λ\|−1) | γ⁴; γ² only for λ away from 1 | Blows up in the symplectic limit. |
| González-Enríquez–Haro–de la Llave, Mem. AMS 2014 | non-twist | no | effectively γ⁸ | Worse. |
| Celletti–Chierchia, Mem. AMS 187 (2007) | 2-DOF iso, Delaunay variables, weighted ℓ¹ | yes | ∝ γ⁻⁴ξ^{−(4τ+1)}, c* = 38528 | Different norms and variables; the helper found an inconsistent closing inequality. |
| Kolmogorov-normal-form CAPs (Celletti–Chierchia, Locatelli, Valvo, Caracciolo, Gabern–Jorba) | normal-form remainders | partly | — | Not like for like. Forced pendulum: 55% → 70% → 92% of breakdown. Moon spin–orbit (Celletti 1990): rotational tori at the true ε and e in a truncated model; librational tori only up to ε_obs/5.26. |
| FH25, J. Nonlinear Sci. 35 (2025) 13, arXiv:2403.10152 | Sun–Jupiter–Saturn 3-torus (FH24) | numerically checked | γ = 1.69·10⁻⁶, ρ = 0.1, τ = 2.4 | The like-for-like test case of FH24; its KAM inequality was not checked in interval arithmetic. |

**L5 (the γ-exponent).**
- γ⁴ is **not** the best for general Lagrangian tori. FH24 reaches γ² with explicit constants.
- γ² is optimal: the pendulum needs ε/α² < 1/4.
- The mechanism is the tangential correction by composition plus the weighted error. A naive "a-posteriori → nearly-integrable"
  reduction lands at γ³.
- v2 route B adopts the mechanism.

## 3. Loss inventory (task 2 and owner directive 2)

### 3.1 Cumulative table, route A (v1's additive step), R1

`thresholds_v2.py`, main table.

| Row | Lever | Fixed | Iso | Binding | Gain (iso) |
|---|---|---:|---:|---|---:|
| A0 | v1 sharp design (reproduced exactly) | −24.72 | −24.98 | 2^{2a}C_E | |
| A1 | **L1** finer data: M₁ = \|DX_h\|, M₂ = \|D²X_h\|, \|Lᵀ\|, \|N\|, \|Nᵀ\|, Θ_ω = σ_ω\|ω*\| | −21.00 | −21.13 | ⟨T⟩⁻¹ cap sum | +3.85 |
| A2 | **L1** measured torsion cap (sup\|T\| on T_{ρ−δ₀}) | −20.68 | −20.90 | T cap sum | +0.23 |
| A3 | **L2a** classical constant c♮ = 0.0814 (full-strip Bessel, ordered divisors, exact Abel) | −19.29 | −19.50 | T cap sum | +1.40 |
| A4 | **L2b** Ω_K through ηᴺ (FH24 Lemma 3.1); averages at the full bite | −18.99 | −19.12 | T cap sum | +0.38 |
| A5 | **L3** δ powers kept (no γ̄-absorption) | −16.19 | −16.30 | T cap sum | +2.82 |
| A6 | **L2c** frequency-specific constants at the bites, k = 5 (c(δ_s) ≈ 0.0030) | −13.44 | −13.60 | T cap sum | +2.70 |
| A7 | **L8** caps for the barred factors, free budgets (internal caps +5 %) | −11.18 | −11.37 | ⟨T⟩⁻¹ cap sum | +2.23 |

Notes on route A:
- A1 is dominated by the torsion: 2M₁|Nᵀ||N| = 7.6 replaces 4nMσ_K²σ_B² = 102, and C_E ∝ H_T⁴. The transposition factors (|Nᵀ| 1.45
  against 10.6) do the rest.
- From A1 on the binding constraint is a cap *sum* (twist, torsion), not the quadratic entry. This is why L3 (it removes the
  γ̄²-absorption in the sums: δ₀^{a−1} = 400×) and L8 pay.
- Rows A3–A7 change the H50 thresholds the same way: −27.37 → −12.44 for route A, iso.

### 3.2 Route B (the modified step, L5) and its levers, R1

| Row | Lever | Fixed | Iso | Binding |
|---|---|---:|---:|---|
| B0 | **L5** modified step, v1 data, c_R = 0.316 (FH24 structure; FH24 itself −19.6 printed, −20.1 corrected) | −21.02 | −21.20 | tail decay |
| B1 | + L1 finer data, incl. c_Th ≥ \|T_h\| | −15.97 | −16.17 | ⟨T⟩⁻¹ cap sum |
| B3 | + L2a classical constant | −15.12 | −15.32 | ⟨T⟩⁻¹ cap sum |
| B4 | + L2c frequency-specific stage data (k = 5) | −14.01 | −14.19 | ⟨T⟩⁻¹ cap sum |
| B5 | + L8 free budgets | −14.09 | −14.24 | tail decay (the +5 % caps cost 0.1 here) |
| B6 | + **L3b** anisotropic stage-0 weight λ₀ = σ_Nᵀγδ₀^κ/σ_Lᵀ (ours; FH24 has λ = 1) | −12.25 | −12.39 | tail decay |

On R1 the levered route A is about one order ahead of the levered route B. Both are bound by the same frame-perturbation cap sums,
which scale like e/(γ²δ₀³) in both routes; route B's structural advantage is in the quadratic entry. That advantage appears at
smaller γδ (the grid, §5) and on H50 at equal footing.

### 3.3 The levers one by one

- **L1, finer hypotheses.** Measured on R1 (`r1_norms.py`, c = 7/4), against what v1 derives:

  | Object | Measured | v1 |
  |---|---:|---:|
  | \|Lᵀ\| | 1.33 | 2nσ_K = 5.50 |
  | \|N\| | 1.35 | σ_Kσ_B = 2.65 |
  | \|Nᵀ\| | 1.38 | 10.6 |
  | sup\|T\| on T_{ρ−δ₀} | 3.31 | H_T = 109 |
  | \|D²X_h\| | 1.03 | M = 1.92 |
  | \|T_h\| | 1.82 | 2M = 3.85 |
  | \|ω\| | 1.75 | Θ = 31 |

  Cost: one hypothesis per object (RefHyp). SHARP-CERTSIDE measures the same values and finds them cheap to certify.
- **L2, small divisors.**
  - (a) Proposition `bp:p2s2sd:classical`: c♮(2,1) = 0.0814, against 0.316.
  - (b) Lemma `bp:p2s2sd:omega` and the full-bite average (FH24 Table 2).
  - (c) Frequency-specific constants: c(δ_s) = 0.0030 for R1 and 0.0024 for H50 at s = 0..4, essentially constant in δ.
  - SHARP-L2 has proved `KAM.cohomological_sum` with the weight e^{−2πδ|k|} (bite ρ−δ/2), which gives c_R ≈ 0.0058 for R1. The
    full-strip refinement here (weight e^{−4πδ|k|}) halves it: 0.0030.
  - The certificate cost is one finite sum per bite. SHARP-L2B is building a fibered, kernel-cheap check for clock frequencies.
- **L3, multi-term recursion.**
  - (a) Keep the δ powers (stage constants evaluated at δ_s; monotone, so the tail uses δ_k).
  - (b) The anisotropic stage-0 weight (route B).
  - The γ-exponents of the recursion are those of the route; there is no extra term structure beyond the quadratic form.
- **L4, schedule.**
  - FH24's optimum is a ≈ 2.1–3.8. Ratio 2 is optimal for the quadratic entry, since a²/(a−1) is minimal at a = 2.
  - The free bite in the prefix is allowed by the engine (any finite prefix schedule) but was not used. On R1 it is worth < 0.2
    orders, because the binding entries are the cap sums.
  - A split of the Cauchy bite (ηδ) is in the route-A mirror: < 0.5 orders.
- **L5, the γ-exponent.** See §2. Route B is the answer: e/(γ²δ^{2τ+1}).
- **L6, measured step-0 objects (hybrid).** `step0_actual.py` measures the actual sizes on R1 (actual / derived):

  | Object | Ratio |
  |---|---:|
  | \|Ω_K\| | 1.7·10⁻⁹ |
  | \|E_red\| | 1.5·10⁻² |
  | ξᴺ | 9.5·10⁻¹⁰ |
  | ξᴸ | 1.1·10⁻¹⁷ |
  | ΔK₀ | 1.3·10⁻¹⁶ |
  | the new error Ē (≤ 7.3·10⁻⁴e² against 6·10²³e²) | 1.2·10⁻²⁷ |
  | ξ₀, ξ^ω | vanish |

  - The residual of a truncated spectral solution lives at |k|₁ ≈ 100–186, where the divisors are moderate and each δ₀ of strip loss
    damps it ninefold.
  - Corollary `bp:p2s2:hybrid` takes certified bounds on these objects and runs the derived theorem from stage 1. On R1 this admits
    e up to about 10⁻⁴·⁵ (route A from stage 1; route B 10⁻⁶·⁰).
  - **This is a property of the candidate's residual, not of the theorem.** A much coarser truncation would put residual mass at
    near-resonant modes, so the hybrid must be re-measured per candidate.
  - Checker cost (SHARP-CERTSIDE §2.7): one coefficient-wise division plus about 20 low-precision products of frame models with
    E-sized models.
- **L7, reversibility.**
  - The spin–orbit tori are R-symmetric for R(Q, P) = (−Q, P): v odd; p, J even. In the parameterization scheme, symmetry gives
    these parities:
    - ηᴺ odd, so ⟨ηᴺ⟩ = 0 holds automatically (already true by exactness);
    - ηᴸ even, T even, 𝓡ηᴺ even, so ⟨ηᴸ − T𝓡ηᴺ⟩ is generically non-zero;
    - Ω_K odd.
  - The averages that carry the twist and the frequency correction are averages of even functions, so they do not vanish, and no
    constant improves. The Newton step preserves symmetry (ξᴸ odd, ξᴺ even, ξᴸ₀ = 0 is the symmetric choice, which is v1's).
  - The certificate already stores only sine coefficients for v and cosines for p, J (half the support). Sup norms can be sampled on
    half the torus.
  - Verdict: no theorem change; the support halving is already realised.
  - On R1, ξ₀ and ξ^ω vanish numerically. This is because the residual has no low modes, not because of symmetry.
- **L8, engine losses.**
  - (i) Budgets μ/2 for every cap and μ/4 for the ball. The internal caps (B, N, Nᵀ, Lᵀ, T, ⟨T⟩⁻¹) are free in v2 (row A7, B5); only
    |DK| and the ball are tied to the frozen conclusion (μ/2). Route B's ball budget is μ/2 with d < β instead of μ/4 with 2d ≤ β.
  - (ii) The geometric-series bounds Σ ε_s/δ_s^i ≤ 2e/δ₀^i are replaced by the explicit prefix sums. This is worth a factor up to 2
    in the sums, and it halves the closeness constant C₂ (|K∞ − K| ≈ |ΔK₀|).
  - (iii) The ratio 1/8: replaced by caps for the barred factors (no θ̂⁴, θ̂⁵); θ = 1/16 is best for route B on the grid.
  - (iv) The limit step: no loss found beyond (ii).
  - (v) The perturbation of 𝒯_c in v1 bounds |Ω̄_K − Ω_K| by d/δ. The Lagrangian defect of the new torus is itself quadratically
    small (Lemma `bp:p2s2:omega`), worth about 1.6× in C_ΔT.
  - (vi) v1's step constant takes the γ̄-absorbed form of every smallness entry (δ₀^{2a−1} lost in "ε ≤ δ"). It never binds after L1.

## 4. The v2 design (task 3)

### 4.1 Mathematics

**Blueprints.**
- `blueprint/parts/p2s2-smalldiv.tex`, labels `bp:p2s2sd:*`: small-divisor constants at a bite, full-strip Bessel, ordered divisors,
  Abel summation, the classical and frequency-specific constants, Rüssmann–Cauchy, averages at the full bite.
- `blueprint/parts/p2s2-modified.tex`, labels `bp:p2s2:*`: refined data, geometry controlled by ηᴺ, the modified step with every
  constant, the stage-dependent engine, route A's deltas, Theorem G1♯♯, the frozen form, the hybrid corollary, the register and the
  errata.
- `blueprint-I/parts/p2s2-iso-modified.tex`, labels `bpI:p2s2:*`: the bordered modified step (frequency and energy errors, bordered
  torsion), I-G1♯♯ concluding `IG1Body`.
- Top files `blueprint/sharp2.tex` and `blueprint-I/sharp2.tex` compile with no undefined reference.

**The modified isoenergetic step is new.** No source has it; HL19 §6 provides the bordered ingredients. The two identities it needs
are proved in the blueprint:
- the energy cancellation ⟨H∘K̃⟩ = E₀ + ⟨Δ²H⟩;
- D(H∘K̃) = −ωᵀΩ_K̃ + (η̃ᴺ)ᵀ, which makes the composition term cubic.

### 4.2 Hypotheses (all certificate-checkable; old ⇒ new with v1 values)

| Hypothesis | Object | v1 value implied by the frozen hypotheses |
|---|---|---|
| (R1) M₁ ≥ \|DX_h\|, M₂ ≥ \|D²X_h\| on 𝔅; c_Th ≥ \|T_h\| | Hamiltonian | M, M; 2M |
| (R2) σ_Lᵀ ≥ \|Lᵀ\|, σ_N ≥ \|N\|, σ_Nᵀ ≥ \|Nᵀ\| on T_ρ | frame of K | 2nσ_K, σ_Kσ_B, 2nσ_Kσ_B (`refHyp_ofV1`) |
| (R3) optional t ≥ sup\|T\| on T_{ρ−δ₀} | frozen torsion | derived: c_Th σ_Nᵀσ_N + slack |
| (R4) Σ_{0<\|k\|₁≤N}\|k·ω*\|⁻²e^{−4πδ_s\|k\|₁} ≤ Ŝ_s, s < k | finite sums | the Rüssmann constant |
| (R5) optional: certified sups of the step-0 objects (hybrid) | ξᴺ, ξᴸ, E_red, E_sym, ∂_ωξ, ΔK₀ | none (corollary only) |
| smallness: X₀ ≤ X⋆ with `routeBOk … X⋆` (finitely many polynomial inequalities) | arithmetic | C₁^{♯♯} = min{C₁^♯, …} |

No hypothesis is conclusion-shaped: each bounds an explicit object of (h, K, ω) or is an inequality between explicit numbers.

### 4.3 Lean signature deltas

The probe `.drafts/sharp2/Signatures.lean` (copy: `docs/campaign/design/APOST-SHARP-V2-SIGNATURES.lean.txt`, 612 lines) elaborates:
12 declarations with `sorry` bodies, every diagnostic "declaration uses `sorry`", no error. `c1V2_le_sharpC1` is proved.

| Module (planned) | Declarations |
|---|---|
| `KAM/Sharp2/SmallDiv/Defs.lean` | `SDConst`, `ray`, `sdSum`, `sdFinite`, `shellConst`, `sdTail`, `sdEps`, `cohConstC`, `cohConstF` |
| `KAM/Sharp2/SmallDiv/Instances.lean` | `sdConst_of_cohData`, `sdConst_classical`, `cohConstC_mono`, `sdConst_freq`, `norm_avg_mul_cohR_le` |
| `KAM/Sharp2/Data.lean` | `RefData`, `RefData.ofV1`, `RefHyp`, `refHyp_ofV1` |
| `KAM/Sharp2/Geometry.lean` | `norm_lagrangeMat_le_etaN`, `norm_invarianceError_le_eta` |
| `KAM/Sharp2/ModConstants.lean` | `StepIn`, `StepConsts`, `stepConsts`, `stepCond` |
| `KAM/Sharp2/ModStep.lean` | `modXiN0`, `modXiN`, `modKtilde`, `modXiL`, `modNewton`, `modified_step` |
| `KAM/Sharp2/Engine.lean` | `StageScheme`, `StageConsts`, `StageScheme.IsNewton`, `xSeq`, `StageScheme.converge` |
| `KAM/Sharp2/G1.lean` | `G1BodyRef`, `stageInB`, `routeBOk`, `ballSumB`, `freqSumB`, `closenessV2`, `c1V2`, `g1_v2`, `c1V2_le_sharpC1` |
| `KAM/Iso/Sharp2/G1.lean` | `iso_g1_v2` (literally `IG1Body` with C₁ = min{`sharpIsoC1`, route B}, C₂, C₃ = max{v1, route B}) |

The constants `stepConsts` are verbatim Definition `bp:p2s2:constantsB` / `bpI:p2s2:constants`, and `stageB` in `thresholds_v2.py`
is their mirror.

### 4.4 v1 Lean results reused unchanged

- **Small divisors.**
  - `KAM.Sharp.CohData` and `cohData_russmann`, `_parseval`, `_crude` (KAM/Sharp/CohData.lean): the tail and the default data.
  - SHARP-L2's `KAM.cohomological_sum`, `_operator_sum`, `smallDivisorSum_le_box_add_tail`, `sdTail_le` (branch `sharp-l2`): the
    base of L2; the full-strip version is a delta (B1).
- **Torsion.** `KAM.Sharp.torsionPoly`, `torsion_identity` (KAM/Sharp/TorsionPoly.lean): the torsion of both tori, 𝒯_ab, 𝒯_F, 𝒯_c.
- **Frame.** `KAM.Sharp.frame_bounds` (KAM/Sharp/Frame.lean): N = Ω₀LB, NᵀΩ₀ = BLᵀ, Aᵀ = Ω₀AΩ₀.
- **Tools.** `KAM.Sharp.neumann_ratio`, `norm_mul_sub_mul_le` (KAM/Sharp/Tools.lean).
- **v1 constants.** `KAM.Sharp.sharpC1`, `sharpC2`, `KAM.Iso.Sharp.sharpIsoC1`/`C2`/`C3` (Constants.lean): the minimum with v1.
- **Engine.** `KAM.Sharp.Engine.schedule`, `error_decay` (A1, on `main`): the tail when constants are uniform. The limit lemmas
  `KAM.Apost.tendstoUniformlyOn_telescope`, `lim_k`, `lim_dk`, `lim_holo`, `lim_primary`, `lim_close`, `lim_margins`,
  `lim_invariance` (KAM/Apost/Limit.lean).
- **Apost and Iso layers.**
  - `KAM.Apost.periodicity`, `exactness`, `frame_identities`, `hamiltonian` (the identity Aᵀ Ω₀ + Ω₀A = 0), `triangular`
    (qualitative), `KAM.taylor_of_differentiableOn_fderiv`, the Cauchy corollaries.
  - `KAM.Iso.Linear.border_solve` (qualitative), `LastRowAux.energyRow_eq_sub_etaL`, `extended_regular`,
    `ExtendedAux.extendedTorsionAverage_eq_bordMat`, `energy_approx`, `energy_conservation`.
  - `KAM.Iso.Sharp.BorderBounds` helpers (A6A).
  - `KAM.Iso.Apost.lim_invariance_moving`, `tendsto_energyAverage_of_uniform`.
- **Not reused.** v1's A4–A7 targets (step, scheme, G1) are not needed by route B. They remain the source of C₁^♯ in the minimum.
  Re-targeting them to refined data is package B9 (optional).

### 4.5 Package split (dependency order; files ≤ 800 lines each)

| Package | Content | Lines | Depends on |
|---|---|---:|---|
| B1 SHARP2-SD | `SmallDiv/Defs`, `Instances`: full-strip version of `cohomological_sum`, classical constant (ordered divisors, Abel), frequency constants, averages at the full bite | 600 | SHARP-L2 |
| B2 SHARP2-GEO | `Data`, `Geometry`: refined data, Ω_K from ηᴺ, recovery of E, DE | 500 | B1, `KAM.Sharp.Frame` |
| B3 SHARP2-CONST | `ModConstants`: defs, positivity, monotonicity in δ and in the small-divisor constants | 400 | — |
| B4 SHARP2-STEP | `ModStep` (split: normal correction / composition and new errors / frames and torsion) | 1500 | B1–B3, `TorsionPoly` |
| B5 SHARP2-ENGINE | `Engine`: prefix, tail with critical sums, limit | 700 | A1 limit lemmas |
| B6 SHARP2-G1 | `G1`: `routeBOk`, `g1_v2`, frozen form | 400 | B4, B5, `KAM.Sharp.Constants` |
| B7 SHARP2-ISO | bordered step deltas, iso scheme, `iso_g1_v2` | 1200 | B4–B6, Iso.Linear, Iso.Sharp.BorderBounds |
| B8 SHARP2-HYBRID | measured first step (both forms) | 500 | B4, B7 (and v1's step identities) |
| B9 (optional) SHARP2-A | route A levers on v1's A4–A7 | 1000 | v1 A4–A7 |

**Total.** About 5.8k lines, 6.8k with B9.

**Order.** B1, B2 and B3 can run in parallel; then B4 and B5; then B6; then B7 and B8.

**The certifier (SHARP-CERTSIDE, A8).** It changes only `checkSmallness`: rational mirrors of `stepConsts` and a certified X⋆, plus
the certificate checks of (R1)–(R4) (and (R5) for the hybrid).

## 5. Dominance (owner directive)

`scripts/apost_sharp/dominance.py` (about 4.5 min). v2 uses only the competitors' information:
- one size M = σ;
- σ_Kᵀ = 2nσ_K, σ_N = σ_Kσ_B, σ_Nᵀ = 2nσ_Kσ_B, c_Th = 2M;
- the classical small-divisor constant;
- no measured objects.

Every competitor receives the same constant (smaller than FH24's printed ĉ_R) and the normalised margins.

Results (108 points; log₁₀ orders; "margin" = v2 minus the best of HL19 and corrected FH24):

| n, τ | Points | Min margin | Median | Max lead of printed FH24 | Route B chosen |
|---|---:|---:|---:|---:|---:|
| 2, 1 | 27 | +0.61 | +0.74 | −0.04 (never leads) | 26/27 |
| 2, 2 | 27 | +0.33 | +0.61 | 0.28 | 27/27 |
| 3, 2 | 27 | +0.32 | +0.50 | 0.46 | 27/27 |
| 4, 3 | 27 | +0.03 | +0.58 | 0.87 | 27/27 |

- **Corrected FH24 and HL19 never win.** Against HL19 the margin is 4.9 to 42.6 orders.
- **Printed FH24** leads at 48/108 points, all for n ≥ 2 with τ ≥ 2 or norms ≥ 3 (erratum E2, below).
- **v2's free parameters on the grid:** θ ∈ {1/16, 1/8}, prefix k = 5, and the classical constant c♮(n, τ, δ_s) at the stages and
  c♮(δ_k) in the tail (constants valid for every bite ≤ δ_k).

**Like for like on the packages (same finer data, classical c_R; FH24 receives c♮(δ₀)).**

| Package | FH24 printed | FH24 corrected | v2 route B |
|---|---:|---:|---:|
| R1 | −14.73 | −14.74 | **−14.26** |
| H50 | — | — | −15.41 |

FH24 on H50 was not run (its script takes R1's data). With all the v2 data (frequency-specific constants, free budgets, anisotropic
weight), route B reaches −12.25 on R1.

**Where a competitor wins, and why.**
- *Printed* FH24 leads by up to 0.9 orders at about half the grid points, all with norms ≥ 3 or n ≥ 3. With σ_Lᵀ = 2nσ_K its
  (3.72) multiplies the B-correction by σ_L instead of σ_Lᵀ, an underestimate by 2n in C_ΔN̄ᵀ, which enters its binding entries Q and
  ⟨T⟩⁻¹.
- With the erratum corrected, FH24 never wins.
- This cannot be "fixed" by v2: matching an invalid printed bound would make v2 invalid.

**Competitors not evaluated numerically.**
- Calleja–Haro–Porras 2025: HL19 structure, γ⁴; not autonomous as stated.
- Celletti–Chierchia 2007: other variables and norms.
- The non-explicit theorems.

## 6. Expected thresholds and costs

| Package / form | v1 | v2 route A | v2 route B | v2 hybrid (R5) | HL19 (finer data) | FH24 (finer data) |
|---|---:|---:|---:|---:|---:|---:|
| R1 fixed | −24.72 | −11.18 | −12.25 | −4.4 (A) / −5.0 (B) | −23.5 | −14.7 |
| R1 iso | −24.98 | **−11.37** | −12.39 | −4.5 / −5.0 | −23.7 | — (no iso version) |
| H50 fixed | −27.19 | −12.29 | −13.05 | not measured | | |
| H50 iso | −27.37 | **−12.44** | −13.17 | not measured | | |

- **Expected R1 threshold with the recommended Lean plan.** Route B plus v1 by the minimum gives 10⁻¹²·⁴ (iso). Route A's levers
  (B9) give 10⁻¹¹·⁴.
- **With the hybrid.** The R1 candidate's admissible error is about 10⁻⁴·⁵; it must be re-measured per candidate.

**Truncation (CONSTANTS-STUDY §2.3 fit, log₁₀η ≈ −0.94L + 3, 2 orders of headroom).**
- v1's 10⁻²⁵ needs L ≈ 32 digits.
- v2's 10⁻¹¹·⁴ needs L ≈ 17 digits, with E-support about 1.1·17² ≈ 320 terms instead of 1.1k (about 3.5× fewer pairs).
- The hybrid threshold would allow much coarser truncations only after re-measurement (§3.3, L6).
- These are extrapolations from the study's fits, not measurements.

**Lean.**
- About 5.8k lines for route B and the hybrid (B1–B8).
- The probe is 612 lines of signatures.
- Risks:
  - the composition estimates (θ + ξᴸ(θ) stays in the strip; the chain rule for the error of K̃∘φ; the mean value inequality on the
    strip);
  - the stage engine with `Nat.rec` iterates;
  - long `max`/polynomial constants in `stepConsts`: keep them folded, and prove monotonicity once (the no-heartbeat rule).

## 7. Honest comparison

- **Where v2 is sharper than every published explicit theorem.**
  - Generic data (the grid): it dominates HL19 and FH24 (corrected) everywhere, typically by 0.5 orders against FH24 and by 10–30
    orders against HL19.
  - Lunar packages: refined data, frequency-specific constants and the anisotropic weight add about 3 orders over FH24 on R1. The
    hybrid adds many more on the actual candidate.
  - Isoenergetic: v2 route B is the first modified-step iso theorem. Its only explicit competitor, HL19 Thm 3.6, is 18+ orders behind
    on R1.
- **Where it is not.**
  - On generic data the margin over FH24 is small (+0.03 at worst), because route B *is* FH24's mechanism.
  - The gains over FH24 are:
    - its erratum;
    - the frozen torsion (no E^{LN}_red);
    - caps for the intermediate frame (n·θ_ξ instead of n);
    - the anisotropic weight (worth up to 2 orders when ηᴸ ≪ ηᴺ/(γδ^κ), as for spectral candidates);
    - stage constants.
  - FH24 handles general compatible triples and first integrals; v2 is canonical, d = n.
  - FHL17's computer-assisted proofs reach 0.004% of breakdown for the standard map. That is a map, with ad hoc c_R and a
    10⁻⁴¹-accurate 8M-mode torus; v2 makes no claim there.
- **Why not more.** After L1–L8 the binding constraints on R1 are the twist and torsion cap sums (frame perturbation), which scale
  like e/(γ²δ₀³) in both routes. Further gains would need either a measured second step (hybrid) or sharper frame perturbation
  bounds, e.g. the actual |B̄ − B| from the certificate. The hybrid already covers the first step.

## 8. Suspected errata (for the ledger)

| Source | Location | Quoted text | Why it is wrong |
|---|---|---|---|
| FH24 (arXiv:2304.10205v1) | Lemma 2.14, p. 14 | ĉ_R = (2^{d+1−2τ}ζ(2,2^τ)π^{−2τ−2}Γ(2τ+1))^{1/2} | Its own route gives half of this (the middle line has π^{−2τ}, the last π^{−2τ−2}, and the definition of c_R(δ) lacks (2π)⁻²). The printed value is a valid but loose bound. |
| FH24 | Table 3, (3.72), p. 38 | C_ΔN̄̄ᵀ = δσ_Bσ_L c_DJᵀ C_ΔK̄̄ + σ_B C_ΔL̄̄ c_Jᵀ + C_ΔB̄̄ σ_L c_Jᵀ | Nᵀ = BLᵀJᵀ, so the bound needs σ_Lᵀ and C_ΔL̄̄ᵀ. As printed it is an underestimate; in the canonical case it equals (3.71). |
| FH24 | (3.10); p. 19 | "C_E =" for C_{Eᵀ}; "Corollary 2.14" for 2.16 | Typos. |
| HL19 (arXiv:1711.05515v1) | (3.16) vs (6.51) | \|ω∞ − ω\| < C₃‖E_c‖/(γ²ρ^{2τ}) vs C₃‖E_c‖/(γρ^τ) | Inconsistent exponents between the statement and the proof. |
| HL19 | §5.3, p. 43, with Lemma 4.1 | "taken to be the same for all steps by considering the worst value of δ_s, that is, δ₀" | Correct for uniform c_R, but Lemma 4.1 allows c_R(δ), which increases as δ ↓ 0 for τ = 1. |
| FHL17 | proof of Thm 2.5, p. 16 | the same as the previous row | The same gap (helper report E2). |
| FHL17 | p. 37 | "6 orders" at ε = 0.96 with τ = 1 | Consistent with τ = 1.26, not 1 (helper report E1). |
| dLGJV 2005 | Thms 3, 6 | "cγ²δ₀^{−2σ}‖e₀‖" | Should be γ⁻² (helper report). |
| `docs/explorations/lunar-band-2p8-2p9.md` | item 3 | "Torsion and Gram constants. They change little between N = 40 and N = 60" | At N = 50, \|B\| grows by 41 %, costing 1.75 orders under v1 (H50 helper report). |
| same document | item 1 | "the binding mode is k = (1, −1), so γ ≈ 2/(N+g)" | True in the θ-frame. In the rotated frame the binding mode is (1, 0) and γ′ ≈ 1/(N+g). |

**Deviations introduced by this design.** See Remarks `bp:p2s2sd:errata`, `bp:p2s2:register` and `bpI:p2s2:dev`:
- small-divisor constants per bite;
- the frozen torsion in the modified step;
- caps for the intermediate frame;
- the anisotropic weight;
- the stage engine;
- the isoenergetic modified step (no source).

## 9. Reproduction

```
python3 -I scripts/apost_sharp/r1_norms.py          # measured R1 norms (1 s)
python3 -I scripts/apost_sharp/smalldiv.py          # small-divisor constants (1 s)
python3 -I scripts/apost_sharp/benchmark_hl19.py    # HL19 on R1 (1 s)
python3 -I scripts/apost_sharp/benchmark_fh24.py    # FH24 on R1 (2 s)
python3 -I scripts/apost_sharp/h50_package.py       # the H50 torus and norms (25 s)
python3 -I scripts/apost_sharp/step0_actual.py      # measured step-0 objects (20 s, 0.9 GB)
python3 -I scripts/apost_sharp/thresholds_v2.py     # cumulative tables, routes A and B, hybrid, H50 (2 min)
python3 -I scripts/apost_sharp/thresholds_v2.py --routeB   # route B on R1 only
python3 -I scripts/apost_sharp/dominance.py [--quick]      # the dominance grid (4.5 min; quick 1 min)
nice -n 5 lake env lean .drafts/sharp2/Signatures.lean     # the signature probe
```

## 10. Owner directives 3 and 4: PlasmaLean, Figueras–Haro 2025, L9, low-dimensional refinements

### 10.1 PlasmaLean on its own example (`dominance.py --plasmalean`)

**PlasmaLean** (github.com/siddhartha-gadgil/PlasmaLean; data from `docs/explorations/striking-applications.md` §8, branch
`apps-scout`):
- field-line KAM on T², 1½ degrees of freedom;
- Newton in weighted ℓ¹ coefficient norms with two unknown functions;
- proved tolerance δ₀⁴/(32κ) = 5.7·10⁻¹⁹ (10⁻¹⁸·²⁴), at γ = 0.0687, strip 0.1257 rad (ρ = 0.02 turns), δ₀ = r/7.

**What is compared.** Our threshold on e (sup norm of the invariance error of a canonical n = 2 flow with clock frequency
ω = (ι, 1), ι = (75+√5)/562), at PlasmaLean's γ, strip and frame and torsion bounds, against its proved tolerance on its own error
norm. The norm sets are those of `run_mag.py`:
- "cA-like": σ_K 3.1, σ_B 2.0, M 3.0, ‖T‖ 19.84, twist ≥ 0.22;
- "R1-like": R1's.

Transposes are not measured for PlasmaLean's torus, so v2 uses the conservative defaults 2nσ_K and so on.

**Not like for like.** Its exact field has a non-canonical area form and no closed-form canonical chart, so our theorem does not
apply to it literally.

| Norms | Small-divisor data | v2 route A | v2 route B | Best | Margin over PlasmaLean |
|---|---|---:|---:|---:|---:|
| cA-like | classical c♮ | −20.01 | −24.88 | −20.01 | −1.77 |
| cA-like | frequency-specific, sup norm (L2c; flat in δ, value at δ₀) | −17.27 | −22.15 | −17.27 | **+0.97** |
| cA-like | ℓ¹ c_∞ = 0.00123 (L9, SHARP-L9), E charged ×3.6 (ℓ¹/sup) | −16.24 | −20.73 | −16.24 | **+2.01** |
| R1-like | classical | −15.94 | −19.61 | −15.94 | +2.30 |
| R1-like | frequency-specific | −13.87 | −17.28 | −13.87 | +4.37 |
| R1-like | ℓ¹ (L9) | −12.99 | −16.12 | −12.99 | +5.26 |

**Verdict.**
- v2 beats PlasmaLean's 10⁻¹⁸·² on its example with the frequency-specific small-divisor data alone (+1.0 orders at its own,
  pessimistic bounds), and by +2.0 with the ℓ¹ constant.
- The sup-norm theorem loses to it only with the generic classical constant (−1.8). That is PlasmaLean's reason 1 (no L² detour in
  ℓ¹).
- Here route A wins: γδ₀ is larger and the norms are larger, so the modified step's advantage is smaller than its larger Q.

### 10.2 L9: the ℓ¹ (Wiener-algebra) variant

**The estimate.** SHARP-L9 (merged into `sharp-v2`) proved the weighted-ℓ¹ cohomological estimate with
Γ_∞(ω,δ) = sup_k e^{−2πδ|k|₁}/(2π|k·ω|): scalar, vector, matrix, a-priori, and the ℓ¹ ⇒ sup bridge, with certified fibered bounds.

| Effective constant c = Γγδ^τ | Value |
|---|---:|
| R1, c_∞ (ℓ¹) | 0.00051 |
| R1, ℓ² sum, full-strip Bessel (this design) | 0.0030 |
| R1, ℓ² sum, bite ρ−δ/2 (SHARP-L2) | 0.0058 |
| generic ℓ¹ | 0.0093 |
| Rüssmann | 0.316 |

**Recommendation: a hybrid, not a full ℓ¹ scheme.**
- The cohomological solutions and the errors would be carried in ℓ¹, where the certificate already computes them.
- The frame and Hamiltonian bounds stay in sup norms, where they are smaller.
- The conclusions are sup-norm (ℓ¹ ≥ sup), so `G1Body`/`IG1Body` follow.

**Gain and cost.**
- On R1 the swap c_freq → c_∞ is worth about 0.9 orders net of the ℓ¹/sup penalty on E (2.0–3.6×; CERTIFIER-SHARPNESS §1.2).
  It is about 1 order on PlasmaLean's data.
- The Lean cost is a parallel norm layer for the step: about 1.5–2k lines (package B10, optional).
- It is not in the blueprint addenda. Only its small-divisor input exists, and it is proved (SHARP-L9).

### 10.3 Low-dimensional and clock refinements

For n = 2 and ω = (ω′, 1), the clock row of the frame is exactly (0, 1), the φ-component of K is θ₂ exactly, and the invariance
error vanishes in that row. All of this is already captured by the measured majorants of L1: R1's |Lᵀ| = 1.33 and |N| = 1.35 are
measured on a clock torus, against 2nσ_K = 5.5.

Exact transposition factors for n = 2 are the measured |Lᵀ|, |Nᵀ|. No further unknown is removed by the theorem: the isoenergetic
form already slaves J through the energy row.

**Remaining low-dimensional lever (not quantified).** Specialize the frame to the clock (L = [[1+u_ψ, u_φ],[0, 1],[p_ψ, p_φ],[P_ψ, P_φ]])
and solve one fewer cohomological equation in the normal direction. That changes the frozen object definitions, so it is a
different theorem.

### 10.4 Figueras–Haro 2025, Sun–Jupiter–Saturn, on their data (`dominance.py --fh25`)

**Their data (§5 of the paper).**
- τ = 2.4, γ = 1.69·10⁻⁶, ρ = 0.1, δ = ρ/6.
- c_Xh = 0.09, c_DXh = c_(DXh)ᵀ = 129, c_D²Xh = 5·10¹⁰.
- ‖DK‖ 4.78, ‖DKᵀ‖ 6.88, ‖B‖ 7.36, ‖N‖ 3.57, ‖Nᵀ‖ 2.86, |⟨T⟩⁻¹| 354.
- σ = norm·(1 + 10⁻¹⁰).
- Their claim: running the Iterative Lemma numerically for 10 steps closes at ‖η^{DK}‖ = 10⁻³⁸, ‖ηᴺ‖ = 10⁻⁴⁴. This was checked
  numerically, not in interval arithmetic.

**Mapping.**
- v2 is d = n canonical. Their norms are used as the caps of a d = n = 3 problem: the first integral and moment flow are dropped.
- Small-divisor data: c♮(3, 2.4).
- c_Th = 2c_DXh and c_DTh = 2c_D²Xh (they do not report these two).
- Margins 10⁻¹⁰·norm.
- 10 exact prefix stages, matching their 10 numerical steps.

| Theorem on FH25's data | Admissible scale of (10⁻³⁸, 10⁻⁴⁴) | Binding |
|---|---:|---|
| FH24 closed form (3.99), δ = ρ/6 as in FH25 | 10⁻⁶·¹⁸ | ⟨T⟩⁻¹ entry |
| FH24 closed form, δ optimised (0.027) | 10⁻⁵·⁵³ | ⟨T⟩⁻¹ entry |
| v2 route B, FH24 weight, ratio 2 | 10⁻⁶·²³ | ⟨T⟩⁻¹ cap sum |
| v2 route B, anisotropic weight, ratio 2 (δ = ρ/6) | **10⁻⁵·⁹⁸** | ⟨T⟩⁻¹ cap sum |
| v2 route B, anisotropic, prefix ratio 3 / 4 (L4) | 10⁻⁵·⁶⁸ / **10⁻⁵·⁵⁶** | ⟨T⟩⁻¹ cap sum |
| v2 route B, ratio 3, if c_DTh = 2c_DXh (hypothetical) | 10⁻²·⁹⁹ | ⟨T⟩⁻¹ cap sum |
| apps-scout "v2-type" emulation (route A type) | about 10⁻³¹ to 10⁻⁴² | quadratic entry |

**Verdict.**
- On FH25's published data v2 **matches FH24's own theorem**: ahead by 0.2 orders at their δ, and within 0.03 orders with free
  schedules.
- **Neither reproduces FH25's numerical closure.** Both are about 5.5 orders short, in the twist-margin entry:
  - σ_T² = 1.25·10⁵;
  - the change of the torsion C_ΔT is dominated by c_DTh·σ_Nᵀσ_N·|K̄ − K|, with c_DTh ≈ 2c_D²Xh = 10¹¹;
  - the margin is σ_T − |⟨T⟩⁻¹| = 3.5·10⁻⁸.
- So FH25's closure must use either a much smaller c_DTh or c_Th (unreported), or larger margins, or a reading of the Iterative
  Lemma we could not reconstruct. Even with c_DTh = 258, three orders remain.
- We record this as a reproducibility note, not an erratum.

**Factor-by-factor decomposition of the gap**, from the apps-scout v2-type emulation (10⁻⁷⁵…10⁻⁸⁶ in e; about 10⁻³¹…10⁻⁴² relative
to FH25's errors) to v2 route B (10⁻⁵·⁶):

| Factor | Orders |
|---|---:|
| (i) L5, the modified step: γ⁴δ₀^{4τ} → γ²δ₀^{2τ+1}, i.e. 1/(γ²δ₀^{2τ−1}) = 1/(2.9·10⁻¹²·1.7·10⁻⁷) | about 18.3 |
| (ii) M₂ = c_D²Xh = 5·10¹⁰ in the quadratic entry (route A: C_E ∋ (M₂/2)C_ΔK²; route B: multiplied by γδ^{τ+1} ≈ 1.5·10⁻¹² in Q_L, or by δ in Q̃_N); M₂ stays in the binding twist entry through c_DTh | about 10 |
| (iii) the full-bite average (δ/ρ)^τ = 6^{−2.4} in C₀ | 1.9 |
| (iv) the anisotropic stage-0 weight (their η^{DK}/(ηᴺ/(γδ^τ)) ≈ 10⁻⁴) | 0.25 |
| (v) the prefix ratio (FH24's optimal δ) | 0.4 |
| (vi) the classical constant c♮ vs the emulation's c_R = 0.05 | about 1 |

The rest is the emulation's absorptions and its single-size M.

**What it would take to apply v2 literally to FH25.**
- **The first integral** (d = 3 < n = 4). FH24's L = (DK, X_p∘K) and the moment-flow composition Φ_{ξ_{Xp}} in the tangential
  correction, with c_Xp, c_DXp, c_DΦ. That is about 1.5k Lean lines on top of B4. It would not change the binding entry.
- **Non-integer τ** is already supported: κ is real throughout, and c♮ uses Γ(2τ+1).
- **Their schedule** (δ = ρ/6) is v2's default.
