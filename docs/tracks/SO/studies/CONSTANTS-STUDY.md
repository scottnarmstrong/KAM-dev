# Track SO: constants study for `KAM.Iso.Apost.g1_explicit`

29 October 2026. This is a read-only analysis: nothing was edited, built or committed in any repository.
Sources read:

- `/root/code/KAM` at `41a749b4`, and `KAM-inp` at `8aa7e422`, for the Lean code;
- `blueprint/parts/p2-aposteriori.tex`;
- `scripts/spin_orbit/*`;
- `certificates/lunar-spin-orbit/*`;
- the SO plan, the pilot report, and the SO-REPLAY handoff.

All numerics were run on copies in this directory (scripts listed in the Appendix).

## 0. Answers in brief

1. **Factor decomposition.**
   - The threshold is **η < γ⁴ δ₀^{2a} / ĉ_\***, because ρ^{4τ} cancels exactly between `isoC1` and the hypothesis.
   - At the pilot package this is −6.49 (γ⁴) − 56.08 (δ₀¹⁶) − 37.30 (ĉ_\*) = **−99.87** orders.
   - The single most lossy ingredient is the **torsion bound |T| ≤ C_T/δ**, which takes the Cauchy route instead of the
     HL19 route (blueprint deviation V4). It accounts for about **38 orders**: δ₀⁻⁴ is 14.0 orders through the "+2" in
     a = 2κ+2, and C_T⁴ = (80𝔪⁷)⁴ is 24.5 orders inside ĉ_\*.
   - Next is the **crude small-divisor exponent κ = τ+n** (deviation V2): 28 orders.
   - Last is the **one-size polynomial 𝔪³⁷** (deviation V6): 22 orders at 𝔪 = 4.
2. **Best package inside the existing theorem.**
   - Two levers do most of the work. The first is to rotate the KAM angles to the certificate's own (ψ, φ) frame,
     which needs no Lean change to the theorem. The second is to fix ρ∞ → 0, s → 1⁺, μ = 1/160 and add a time
     rescaling.
   - Result: **10^−74.5** with sharp norm majorants (sampled sup + 5 %), or **10^−80.3** with norm majorants as loose
     as the pilot's. The pilot gets 10^−99.9.
   - With 2 orders of headroom, the truncation drops from 111.5 to **87–93 digits**.
   - Support drops from 13.9k/13.7k (full-lattice v / E) to **8.3k/8.1k – 9.6k/9.4k**: **2.1–2.8× fewer product
     pairs**. Measured against the 19k coefficients emitted at 10⁻¹³⁰, it is 4–5× fewer.
   - Precision drops from about 440 bits to 300–320 bits.
3. **Sharper theorem options.** Ranked by gain per Lean line, they are:
   - the HL19 torsion route (+11 to +20 orders);
   - a Parseval cohomological estimate with κ = τ+n/2 (+11–12);
   - both together (+22–24, which gives the "≤ 4096 per factor" regime of the replay handoff);
   - Rüssmann with κ = τ (+11 more);
   - actual-norm constants (+5–10);
   - schedule 4δ → 3δ (+2–3);
   - anisotropic strips (≤ +5, very expensive).

   Each theorem change except the Parseval estimate itself needs a shared generic-exponent refactor first, about
   0.8–1.5k lines. A complete HL19/FHL17-faithful theorem would reach roughly 10⁻²⁰–10⁻³⁰. That means 29–38 digits,
   0.8–1.4k E-coefficients and 100–300× fewer product pairs, which is the "10× support" goal. It costs an estimated
   6–10k lines, about half to most of the existing 12.45k-line a-posteriori layer.
4. **Recommendation.**
   - **Do not fund a sharper theorem for the lunar client now.** Adopt the zero-Lean package of item 2. Size the
     truncation to the threshold, not to 10⁻¹³⁰. Certify the Gram inverse with an enclosure close to its sup.
   - If the advice-shard prototype shows the comfortable regime really is ≤ 4096 coefficients per factor, the
     package alone is not enough (≈ 8k per factor). Then fund the smallest theorem change that reaches it: the
     generic-exponent refactor plus the HL19 torsion route plus the Parseval cohomological estimate, about 3–4k lines,
     giving 10⁻⁵², 62 digits and ≈ 4.0k E-terms.
   - The full HL19-faithful theorem is justified only by the black box's generality. For n ≥ 3 the current exponent
     2a = 4(τ+n)+4 grows quickly.

## 1. Factor decomposition of the threshold 1.3366·10⁻¹⁰⁰

**Definitions.** All citations are to `/root/code/KAM`.

- `isoC1 = ρ^{4τ} max{γ̄⁴, ĉ_* δ₀^{-2a}}`: `KAM/Iso/Apost/Defs.lean:208`.
- The smallness hypothesis `C₁ e/(γ⁴ρ^{4τ}) < 1`: `KAM/Iso/Apost/G1.lean:86-93`, used by `g1_explicit` at `:95`.
- Hence **threshold = γ⁴ δ₀^{2a} / ĉ_\*** whenever ĉ_\*δ₀^{−2a} ≥ γ̄⁴, which always holds. **ρ⁴ cancels; it is not a
  factor.** The exact mirror confirms this identity.
- Other definitions:
  - `hatcStar` (`Defs.lean:111`) is the max of 2^{2a}Ĉ_E, ĉ_step·max{1, 2/μ}, 2ĉ_sum/μ and 4Θ²Ĉ_Δ/ν.
  - `hatcStep` is at `:107`, `hatCE` at `:97-103`, `hatCDelta` at `:89`, `hatCDK` at `:88`, `hatCxi` at `:87`,
    `hatCg` at `:85`, `hatCS` at `:82`, `CDTbord` at `:106`.
  - `kappa = τ+n` is at `KAM/Apost/Constants.lean:60`, `aExp = 2κ+2` at `:62`, `cR = max 1 cohConst` at `:64`.
  - `mSize = max{1, M, σK, σB, σT}` is at `:66`, `Theta = 4n𝔪³` at `:68`, `C_X = 5n²𝔪⁵` at `:70`,
    `C_T = 2n𝔪²C_X` at `:72`, `C_xi0` at `:80`, and `delta0 = min{1, (ρ−ρ∞)/8}` at `:119`.
  - `cohConst` is at `KAM/Strip/CohomologicalDefs.lean:31`. For n = 2, τ = 1 it is 128/(eπ⁴) ≈ 0.48, so c_R = 1.
  - The schedule δ_s = 2^{−s}δ₀ and r_{s+1} = r_s − 4δ_s is at `KAM/Apost/Schedule.lean:47,49`.

| Factor (pilot package) | Value | log₁₀ |
|---|---|---:|
| **γ⁴**, γ = γ̄ = 1/42 = γ(ω)/s with s = 2 | 3.2·10⁻⁷ | **−6.49** |
|   of which the ray scalar s = 2 (γ(ω) = 1/21 is proved) | 2⁻⁴ | −1.20 |
| **δ₀^{2a}**, δ₀ = (ρ−ρ∞)/8 = 1/3200, 2a = 16 | 5.4·10⁻⁵⁷ | **−56.08** |
|   split by source: ρ¹⁶ | | −36.82 |
|   (1 − ρ∞/ρ)¹⁶ = 2⁻¹⁶ (ρ∞ = ρ/2) | | −4.82 |
|   8⁻¹⁶ (schedule: per-step loss 4δ_s, total 8δ₀; blueprint V4/V7) | | −14.45 |
|   split by exponent: HL19's 4τ = 4 | | −14.02 |
|   + 4n = 8 (crude κ = τ+n; blueprint V2) | | −28.04 |
|   + 4 ("+2" in a = 2κ+2, from \|T\| ≤ C_T/δ; blueprint V4) | | −14.02 |
| **1/ĉ_\***, ĉ_\* = 1.99·10³⁷ (step branch active) | | **−37.30** |
|   2/μ = 2000 (μ = 1/1000) | | −3.30 |
|   ĉ_step = 2Θ³·𝔪·CDTbord·Ĉ_Δ = 9.94·10³³ | | −34.00 |
|     2Θ³ (Θ = 4n𝔪³ = 512) | | 8.43 |
|     𝔪 = 4 | | 0.60 |
|     CDTbord = 2.63·10⁹ | | 9.42 |
|     Ĉ_Δ = 3.53·10¹⁵ | | 15.55 |
|   E-branch for comparison: 2^{16}Ĉ_E = 3.27·10³⁶ (Ĉ_E ≈ 𝔪Ĉ_Δ²) | | 36.51 |
| **Total** | 1.3366·10⁻¹⁰⁰ | **−99.87** |

**Polynomial view.** Every constant is a polynomial in the single size 𝔪 (blueprint V6). In the branches that
matter, Ĉ_Δ ≈ 51200·𝔪¹⁸, Ĉ_E ≈ 2.62·10⁹·𝔪³⁷, ĉ_step ≈ 5.23·10¹¹·𝔪³⁷ and ĉ_sum ≈ 1.31·10¹¹·𝔪³⁵. At 𝔪 = 4 the
factor 𝔪³⁷ is **22.3 orders**. Near 𝔪 = 4, each unit less in 𝔪 is worth about 4 orders (37/(𝔪 ln 10)).

**Where 𝔪¹⁸ in Ĉ_Δ comes from.**

- Ĉ_Δ = 2𝔪²Ĉ_ξ, with Ĉ_ξ ≈ Ĉ_g ≈ C_T·Ĉ_ξN and Ĉ_ξN ≈ C_ξ0 ≈ 2n𝔪²·c_R·C_T.
- The torsion constant C_T = 80𝔪⁷ therefore enters Ĉ_Δ **twice**, and Ĉ_E ∝ Ĉ_Δ² **four times**.
- C_T arises from bounding |T| by C_T/δ through a Cauchy estimate on ∂_ωN together with the frequency bound
  |ω| ≤ Θ:
  - `KAM/Apost/Frame.lean:377` (C_X/δ), `:401` `norm_torsion_le`, `:423` `frequency`;
  - blueprint `p2-aposteriori.tex:357` (frequency), `:382` (frame-basic (d)) and `:427` (Remark "Route for the
    torsion").
- This one lemma costs C_T⁴ ≈ 10^{24.5} inside ĉ_\* at 𝔪 = 4, plus δ₀⁻⁴ = 10^{14.0} through a. That is **≈ 38 of the
  99.9 orders**.
- HL19 bounds T without 1/δ by expanding ∂_ωN through ∂_ωL = AL − DE (HL19 Lemma 4.8). That identity is already in
  the blueprint as frame identity (c), `p2-aposteriori.tex:441`.

**Other factors.** The displacement coefficient is 2Ĉ_Δ/(γ²δ₀^a) = 1.37·10⁴⁷ (`isoC2`, `Defs.lean:213`). The
blueprint's own deviation list (`p2-aposteriori.tex:1174`, V2, V4, V6, V7) names exactly these losses relative to
HL19, whose step error is O(e²/(γ⁴δ^{4τ})).

## 2. The best package inside the existing sealed theorem

### 2.1 Free levers (pilot norm table fixed, θ-frame, ρ = 1/200)

All thresholds below come from the exact `Fraction` mirror (`exact_packages.py`).

| Step | Change | log₁₀ threshold | Gain |
|---|---|---:|---:|
| P0 | Pilot | −99.87 | |
| P1 | ρ∞ = ρ/1000. ρ∞ only sets the analyticity strip of K∞; O4 already defers analytic graphs. | −95.06 | +4.81 |
| P2 | Ray scalar s = 1 + 10⁻⁶, ω\* = ω/s, γ = γ̄ = 1/(21s), ν = 10⁻⁶, σω = 2. | −93.86 | +1.20 |
| P3 | μ = 1/160, which switches step → E branch (μ ≥ 0.0061). 𝔪 = 3.56 = σB (3.544 + μ). | −91.21 | +2.66 |
| P3′ | ρ = 1/160 (re-optimized). | −89.70 | +1.5 |
| P4 | Time rescaling H → cH with c = 5/4. γ → cγ and η → cη; M → cM ≤ 𝔪; σT → σT/c. | −89.31 (−89.41 on unscaled η) | +0.4 |

Notes on these levers:

- **"γ̄ = 1/42 is fixed by the frequencies" is not quite right.** γ(ω\*) = γ(ω)/s and s > 1 is free. Here
  γ(ω) = 1/21 is proved; the numerical infimum is 2α = 0.04924 at k = (1, −1).
- The ν-branch 4Θ²Ĉ_Δ/ν is 15 orders below the others, so s − 1 can be about 10⁻⁶.
- M, σK and σT do not matter separately: only 𝔪 = max(·) enters the constants. In the θ-frame, σB (the Gram
  inverse) is binding.

### 2.2 Reconstructed norm package and the rotated frame (main in-theorem lever)

I rebuilt the pilot's norm table from the certificate data (`norms.py`):

- K = (θ₁ + u, θ₂, p, J), with H = p²/2 + V + J and the frozen frame N = Ω₀LB;
- T = Nᵀ Ω₀ (A N − ∂_ω N), with the bordered average and inverse;
- sups sampled on the distinguished boundary of the polystrip (max principle) on a 256 × 64 grid.

**Validation.** The averaged-torsion inverse reproduces the pilot exactly: **2.718037 / 2.849753**. The other
majorants are sampled sups and sit below the pilot's analytic majorants:

| θ-frame, ρ = 1/200 | Pilot majorant | Sampled sup | Comment |
|---|---:|---:|---|
| Gram inverse \|B\| | 3.544 | **2.299** | The pilot's entrywise-Q⁻¹ plus Neumann majorant overestimates by 54 %; this is what makes σB binding. |
| H majorant M | 2.686 | 2.315 (μ = 1/160) | Dominated by D²X_H (third derivatives of V). |
| \|DK\| | 1.680 | 1.599 | |
| Torsion inverse | 2.850 | 2.850 | Exact match. |

**Rotated frame.** The KAM angles are the data's own (ψ, φ). The change is symplectic and unimodular: Q₁ = q − φ,
Q₂ = φ, P₁ = p, P₂ = p + J. Then:

- H′ = P₁²/2 − P₁ + P₂ + V(Q₁ + Q₂, Q₂);
- K′(ψ, φ) = (ψ + u, φ, p, p + J), which is primary;
- ω′ = (ν − 1, 1);
- the residual is ((0, 0), (−r, (p − 1)r));
- E₀ = 0 is still exact;
- P₁ = p, so the confinement statement transfers with no work.

This is a client-side choice of H and K. The general black box handles it and **the theorem is unchanged**.

In this frame the norms collapse:

| Rotated, ρ′ = 1/70 | Value | θ-frame (ρ = 1/200) |
|---|---:|---:|
| M (H majorant) | 1.047 | 2.315 |
| \|DK′\| | 1.303 | 1.599 |
| Gram inverse | 1.833 | 2.299 |
| Torsion inverse | 1.022 | 2.850 |

Why they collapse:

- \|p − 1\| ≈ 0.03 replaces \|p\| ≈ 1.
- The mode-m forcing direction (2, 2 − m) kills the m = 2 term in the third derivatives.
- The off-diagonal of the Gram block becomes u_φ, which is small, instead of u_φ − u_ψ, where u_ψ reaches ±0.26.
- The ω′-border makes the bordered torsion nearly unimodular.

So 𝔪 drops from 3.56 to about 1.95, and 𝔪³⁷ is worth about 10 orders.

The costs are:

- γ′ = γ(ω′): the numerical infimum is α = 0.02462 at k = (1, 0), and |k₁| + |k₂ − k₁| ≤ 2|k|₁ gives the proved
  value 1/42. That is −1.20 orders relative to 1/21.
- An isotropic strip ρ′ ≈ 2ρ is needed to match the ψ-width. Its residual weight is only 0.2–0.3 orders worse than
  the θ-strip, because the support is elongated in ψ.

**Two packages in the rotated frame.** Both use ρ′ = 1/70, ρ∞ = 1/70000, μ = 1/160, s = 1 + 10⁻⁶, ν = 10⁻⁶ and
σω = 2.

| Package | 𝔪 = M = σK = σB = σT | c | γ = γ̄ | log₁₀ threshold (exact) | On unscaled η |
|---|---|---|---|---:|---:|
| **R1** (sharp majorants: sampled sup × 1.05) | 39/20 | 7/4 | 1/(24s) | **−74.51** | −74.75 |
| **R2** (majorants as loose as the pilot's, × the pilot/sup ratios) | 2.84 | 2 | 1/(21s) | **−80.29** | −80.59 |

Constraint checks for R1:

- M = 1.05·1.047·1.75 = 1.92 ≤ 1.95;
- σB = 1.05·1.833 + μ = 1.931 ≤ 1.95;
- σT = 1.05·1.022/1.75 + μ = 0.62;
- σK = 1.37.

R1's factor table against the pilot:

- γ⁴: −5.52 (+0.97: s → 1 gives +1.20, rotation gives −1.20, c = 7/4 gives +0.97);
- δ₀¹⁶: −43.98 (+12.1: ρ∞ → 0 gives +4.8, ρ = 1/70 gives +7.3);
- ĉ_\*: 25.01 (+12.3: 𝔪 from 4 to 1.95 gives 11.5, the step → E branch switch gives 0.8).

The full optimizer (`optimize.py`) searched over ρ, μ, time scale c ∈ [0.5, 3], action scale λ ∈ [0.5, 2] and both
frames. It confirms these optima. Action scaling helps only in the θ-frame (to about 10^−82) and is never better than
rotation.

### 2.3 Support versus threshold (from `*_truncation_residuals`, extended)

I recomputed the exact (Fraction/ℚ(√5)) residual of the truncated candidate at every 5 digits of truncation, L = 20 to
130 (`trunc.py`, mirroring `analyze.py`; at L = 110 it gives 2.13·10⁻¹⁰¹, matching the JSON). The weighted ℓ¹ residual
bound was evaluated for any strip shape (`resid.py`).

- The relation is log₁₀ η ≈ −0.94 L + 3 at ρ = 1/200, and the upper torus saturates at L ≥ 125 (solver floor).
- Support grows as N_v,half ≈ 0.55 L² and N_E ≈ 2N_v,half.
- Rule used: the smallest L with η(L) ≤ threshold·10⁻² (2 orders of headroom, about the pilot's 10⁻¹⁰³ vs 1.3·10⁻¹⁰⁰).

| Package | Digits L | Bits ≈ | v half / full | E terms | Product pairs vs P0 | vs the emitted 10⁻¹³⁰ data |
|---|---:|---:|---:|---:|---:|---:|
| P0 pilot (sized to its threshold) | 111.5 | 380 | 6955 / 13909 | 13655 | 1 | 0.53 |
| P4 θ-frame, all free levers | 101.7 | 348 | 5737 / 11474 | 11273 | 0.68 | 0.36 |
| **R2** rotated, loose majorants | 93.4 | 320 | 4804 / 9609 | 9438 | **0.48** | 0.25 |
| **R1** rotated, sharp majorants | 87.0 | 299 | 4141 / 8282 | 8127 | **0.35** | 0.19 |
| (emitted data, 10⁻¹³⁰) | 130 | 440 | 9512 / 19024 | 18766 | 1.88 | 1 |

Truncating at the level the threshold actually needs, instead of 10⁻¹³⁰, is itself worth 1.9× in pairs.

**On the ψ-width.** The coefficient decay is ≈ 0.50 digits per unit k in ψ and ≈ 1.94 per unit l in φ, so the
analyticity widths are ≈ **0.18 in ψ** and ≈ 0.71 in φ. The binding limit on ρ is therefore not analyticity. It is the
trade-off between δ₀¹⁶ (+4.8 orders per doubling of ρ) and two costs:

- the residual's strip weight at the truncation edge (|k| ≈ 2L), about 10^{10.9ρL};
- the growth of the majorants with ρ. In the θ-frame M grows quickly, to 3.13 at ρ = 0.02; in the rotated frame the
  Gram inverse reaches 2.05 at ρ′ = 0.05.

The optimum is ρ ≈ 0.006–0.007 (θ-frame) or ρ′ ≈ 0.012–0.017 (rotated), and it moves to larger ρ as L shrinks.

## 3. Sharper theorem options

All gains are at the re-optimized ρ, computed with `variants.py` and `variants_hl.py`. Each row gives the rotated
frame with sharp majorants, then with loose majorants in brackets. Pair ratios are relative to P0 sized to its
threshold.

| Rank | Option | 2a | log₁₀ threshold | L | E terms | Pairs vs P0 | Lean lines (estimate) |
|---|---|---:|---:|---:|---:|---:|---:|
| 0 | **In-theorem package R1/R2** (§2) | 16 | −74.5 [−80.3] | 87 [93] | 8.1k [9.4k] | 0.35 [0.48] | **0** in the theorem; small client-side transport |
| 1 | **(c) HL19 torsion route** (dominant lossy lemma) | 12 | ≈ −63 [−69] with a crude C′_T; up to ≈ −55 with an actual-norm \|T\| bound | ≈ 74 | ≈ 5.8k | ≈ 0.18 | 1.5–2.5k including the generic-exponent refactor |
| 2 | **(a/c) Parseval cohomological estimate**, κ = τ + n/2 (κ = 2 for n = 2) | 12 | −62.8 [−69.4] | 74 [80] | 5.8k [6.9k] | 0.18 [0.25] | 1–1.5k including the refactor |
| 3 | **1 + 2 together** | 8 | ≈ −52 [−58] | 62 [68] | 4.0k [4.9k] | 0.085 [0.13] | ≈ 3–4k |
| 4 | (c) Rüssmann estimate, κ = τ (instead of 2) | 8 (alone), 4 (with 1) | −52 alone; −41.6 [−47.3] with 1 | 50 [56] with 1 | 2.5k [3.2k] with 1 | 0.033 [0.054] with 1 | +1.5–3k on top of 2 |
| 5 | (c) Actual-norm constants: separate M, σK, σB, σT and checked \|ω\|, \|T\| instead of 𝔪; drop the Θ-absorptions | – | +5–10 (more with 1) | | | | 2–4k (`Constants.lean` 952, `ConstantsArith.lean` 1062, `Iso/Apost/Constants.lean` 255, plus every lemma's closing arithmetic) |
| 6 | Schedule loss 4δ_s → 3δ_s per step (HL19), δ₀ = (ρ−ρ∞)/6 | – | +2 (2a = 16) down to +0.5 (2a = 4) | | | | 0.5–1k |
| 7 | (b) Anisotropic strips (ρ_ψ ≠ ρ_φ) | – | ≤ +5 beyond rotation | | | | > 5k: `complexStrip` underlies Strip/Torus/Apost/Iso. **Not recommended.** |
| 8 | **(d) HL19/FHL17-faithful theorem** (1 + 4 + 5 + 6) | 4 | ≈ −20 to −30 (literature-calibrated) | 29–38 | 0.8–1.4k | 0.003–0.01 (100–300×) | 6–10k (half to most of the 12.45k-line layer, rewritten) |

Notes on the options:

- **The generic-exponent refactor is shared by options 1–4.**
  - The sealed `g1_explicit` must stay untouched. So parametrize `KAM/Apost/**` and `KAM/Iso/Apost/**` over (κ, c_R)
    and the "+2". Feed the cohomological estimate in as a hypothesis.
  - The cohomological estimate enters only through `KAM.Apost.cohomological` (`KAM/Apost/Tools.lean:322`, bridge at
    `:296`). It also enters directly in `Iso/Linear/Energy.lean:234` and `BorderSolve`.
  - `kappa` occurs about 260 times, 129 of them in `Iso/Apost/ConstantsArith.lean`.
  - `eight_le_aExp` is used about 10 times (Limit, Iteration, NewtonError, Constants) and `three_le_kappa` once. These
    need weakening to a ≥ 4 or κ ≥ 1.
  - Then re-derive the existing theorem as the instance κ = τ+n. That keeps the 1500-line cap: it means narrower
    lemmas, not bigger files.
  - Elaboration risk sits in `ConstantsArith` (1062 lines). Under the no-heartbeat rule, any timeout there is a design
    signal to split further.
- **(a) n = 2/τ = 1-specific constants by themselves** gain only the integer prefactors: 5n², 6n², 2n(n+1), the
  transposition factor 2n. That is about 2–4 orders. The useful n = 2 fact is κ = τ + n/2 = 2, which option 2
  delivers for all n.
- **Option 2 in detail.** On each corner of the polystrip, Parseval gives Σ|ĝ_k|²e^{4π|k|₁ρ} ≤ 2ⁿ‖g‖². Cauchy–Schwarz
  against Σ|k|₁^{2τ}e^{−4πδ|k|₁}/γ² then gives ‖u‖_{ρ−δ} ≤ c′/(γδ^{τ+n/2}). For n = 2, τ = 1, c′ ≈ 0.06, so c_R stays
  1. No Rüssmann counting is needed. Mathlib has torus Parseval, but this needs the shifted-torus version for strip
  holomorphic functions.
- **Option 1 in detail.** ∂_ωN = Ω₀(AL − DE)B − Ω₀LB(∂_ωG)B gives |T| ≤ f(M, σK, σB) + O(e/δ) with no 1/δ, so
  a = 2κ. A crude f ≈ 68𝔪⁸ saves only δ₀⁻⁴ (≈ 11–12 orders). A bound in actual norms, where the candidate's |T| is
  about 1–2, could save up to about 25 more orders. The perturbation lemma for the twist (blueprint V4, "Step 7",
  `PerturbationTorsion.lean`) must follow the same route.
- **Literature calibration for (d)** (Figueras–Haro–Luque, FoCM 17 (2017) 1123–1193, arXiv:1601.00084; read from the
  arXiv PDF):
  - Their iterative lemma is ‖Ē‖ < Ĉ₅‖E‖²/(γ⁴δ^{4τ}), and the smallness is a₁^{4τ}Ĉ₅‖E‖/(γ⁴δ₀^{4τ}) < 1 with
    δ₀ = ρ/a₃.
  - Standard map, Table 5: errors of 10⁻³³ give C₁b_E/(γ⁴ρ^{4τ}) = 1.35·10⁻²⁸ at ε = 0.06 (ρ = 0.016) and 2.3·10⁻¹² at
    ε = 0.96 (ρ = 1.2·10⁻⁴). At ε = 0.9716: E ≤ 2.74·10⁻⁴¹, ratio 0.0823, ρ = 3.7·10⁻⁷, 8.4M modes.
  - **Froeschlé map, 2-tori in T² × R², the same dimension as ours** (Table 8): grids 128² to 512², tolerances 10⁻³³
    to 10⁻⁶⁶, ratios 10⁻⁵ to 10⁻⁴¹. The implied thresholds (tolerance/ratio) are about **10⁻²²–10⁻²⁹** at
    ρ ≈ 0.006–0.05. These are lower bounds on the true thresholds, since b_E exceeds the grid tolerance.
  - Their Rüssmann constants for 2-D frequencies are c_R ≈ 2·10⁻⁴–4·10⁻² (Table 4: classic 3.4–4.4·10⁻²; ad hoc down
    to 2·10⁻⁴).
  - **Unverified for our problem:** I did not re-derive their constants for this Hamiltonian. The band 10⁻²⁰ to 10⁻³⁰
    assumes Ĉ₅ between 10⁴ and 10¹² (scaling as 𝔪⁸) at our norms. HL19 itself is a theorem without computer-assisted
    examples.
  - The Calleja–Celletti–Gimeno–de la Llave spin–orbit works (2021–23) are numerically validated, not fully rigorous,
    by their own statement. I found no rigorous threshold numbers for a Moon spin–orbit KAM proof to compare with.

## 4. Recommendation

1. **Fund the zero-Lean package now.**
   - Formulate the lunar client in the rotated (ψ, φ) frame, with H′ and K′ as in §2.2.
   - Package: ρ′ = 1/70, ρ∞ = ρ′/1000, μ = 1/160, s = 1 + 10⁻⁶, γ = γ̄ = c/(42s), ν = 10⁻⁶, σω = 2, time scale
     c ≈ 7/4–2, and 𝔪 set by the certified majorants.
   - Certify the Gram inverse with an enclosure that tracks its sup (≈ 1.83), for example a Fourier-ℓ¹
     approximate inverse with a Neumann check. The pilot's entrywise majorant is 54 % loose and costs about 6 orders.
   - Size the truncation at about 10⁻⁸⁹ to 10⁻⁹⁵ (L = 87–93), not 10⁻¹³⁰.
   - Net effect: threshold +19 to +25 orders, 2.1–2.8× fewer pairs than the pilot sized to its threshold, and 4–5×
     fewer than the 19k emitted data. Precision drops to about 300 bits.
   - Cost: none in the theorem.
2. **Do not fund a sharper theorem for this client at "tens of CPU-hours".** Every theorem option below the full
   HL19-faithful rewrite buys at most another 2–10× in pairs, for 1–5k audited Lean lines. CPU-hours are cheaper.
3. **Contingency: the advice-shard prototype misses its projection.** The SO-REPLAY handoff's comfortable target is
   ≤ 4096 coefficients per factor; it was not measured, and the advice-shard path was not prototyped. If that limit is
   real, the package (≈ 8k per factor) is not enough. Fund rank 3:
   - the generic-exponent refactor;
   - the HL19 torsion route;
   - the Parseval cohomological estimate;
   - about 3–4k lines, giving about 10⁻⁵², 62 digits and ≈ 4.0k E-terms.

   This is the smallest theorem change with the biggest gain. It is a new, unfrozen theorem; the sealed `g1_explicit`
   stays as the instance κ = τ+n. It must be written to the hard rules: files ≤ 1500 lines, split rather than raise
   heartbeats.
4. **Strategic case.** The black box is meant to be general. The current exponent 2a = 4(τ+n)+4 with τ ≥ n−1 is 24 at
   n = 3, and the 𝔪³⁷-type polynomials grow with n. Any future client in n ≥ 3, or one closer to breakdown, will hit
   the constants long before this one does. The full HL19-faithful theorem (rank 8: 10⁻²⁰–10⁻³⁰, 100–300× fewer pairs)
   is the right long-term investment if the owner wants the black box to serve such clients. It is not justified by
   the lunar certificate alone.

## Appendix: method, caveats, reproduction

**Caveats.**

- The reconstructed majorants are sampled sups, not enclosures. R1 assumes certified majorants within 5 % of the sup;
  R2 assumes the pilot's looseness. The truth for a good certificate lies between them.
- The H-majorant uses cosh bounds on the μ-neighbourhood. The pilot's value (2.686 vs my 2.315) was evidently more
  conservative; its script is not on disk.
- Support counts are max(lower, upper) at 5-digit steps, linearly interpolated. The 2-order headroom is a convention.
- The sharper-theorem rows change only 2a, 2^{2a} and the stated constant factors. Real proofs would shift the
  polynomial constants as well.
- Lean line counts are engineering estimates from the current layer's sizes:
  - KAM/Apost: 7484 lines;
  - KAM/Iso/Apost: 4966 lines;
  - Strip cohomological: 1054 lines;
  - Iso/Linear: 4618 lines.

**Scripts.** All are in `/tmp/claude-0/-root/0e739fce-e1ef-4aa1-9d8d-2d63fa1ad512/scratchpad/constants-study/`.

| File | What it does |
|---|---|
| `factors.py` | Factor table |
| `cfast.py` | Float mirror of the constants, checked against the exact one |
| `levers.py` | The P0–P4 levers |
| `exact_packages.py` | Exact thresholds of the packages |
| `norms.py`, `precompute.py` | Norm reconstruction (`normgrid.pkl`) |
| `trunc.py` | Exact truncated residuals (`trunc_{lower,upper}.pkl`) |
| `resid.py` | Strip-weighted residual bounds |
| `optimize.py` (output `opt1.log`) | Parameter optimizer |
| `package_support.py` | Support per package |
| `variants.py`, `variants_hl.py` | Sharper-theorem variants |
| `dio.py` | Diophantine infima in both frames |
| `fhl17_dl/` | Downloaded FHL17 PDF and its text (untrusted data, read only) |
