# Certifier sharpness: the checker side of the sharp KAM certifier (SHARP-CERTSIDE)

30 October 2026, branch `sharp-certside`. Design study: Python and documents only, no Lean change. Every number
below comes from a script in `scripts/certifier/` (section 9 gives the commands). Those scripts are untrusted
design tooling: double precision, sampled sups where it says "sup". The exact residual coefficients come from
`scripts/spin_orbit/rot_build.py`, imported read-only.

Companion documents:
- the theorem side, `docs/campaign/design/APOST-SHARP-V2.md` (SHARP-PLUS, in progress on branch `sharp-plus`);
- the first sharp certifier, `KAM/CertificateSharp/` (SHARP-A8, in progress on branch `sharp-a8`);
- the zero-Lean package study `docs/tracks/SO/studies/CONSTANTS-STUDY.md`;
- the SO kernel studies (SO-REPLAY, SO-REPLAY2, SO-ADVCOUNT, D34).

Notation:
- **R1** is the lunar package: rotated frame (ψ, φ), ρ = 1/70, ρ∞ = ρ/1000, μ = 1/160, s = 1 + 10⁻⁶, ν = 10⁻⁶,
  σω = 2, time scale c = 237/125. The data are the emitted `certificates/lunar-spin-orbit/{lower,upper}_rot.json`,
  truncated at 88 digits, 318 bits.
- **T/e** is threshold over invariance error, in orders of magnitude.
- The theorems: **v0** is the sealed `KAM.Iso.Apost.g1_explicit`; **v1** is the sharp iso design
  (`scripts/apost_sharp/thresholds.py`, Rüssmann data); **v2** is SHARP-PLUS's mirror (`thresholds_v2.py`, work
  in progress).

## 0. Answers in brief

1. **Inventory (§1).** On R1 the landed checker is already tight wherever SO-GEN2 put the effort: the torsion
   inverse is exact, and DK is 4 % and the Gram inverse 8 % above their sups. The real looseness is in three places:
   - **the invariance error**: weighted ℓ¹ is 2.0–3.6× above the sampled sup, and 2.1–4.3× on the polynomial
     part alone;
   - **the ball arithmetic of H**: the cosine modes are bounded by the character disc w^{|k|}, not by cosh. This
     costs +1.7 % on the D²H sum, which sets M, and +39 % on |D²X_H|;
   - **γ**: the proved 1/42 is 3.4 % below the exact infimum.

   The pilot's entrywise Gram inverse (+54 %) is gone in the rotated certificates. The toys are degenerate: flat
   tori with exact models. Their one lesson is the dependency problem of ball arithmetic: T2d's ‖D²X_H‖ is
   bounded by 1522.6 for a function that is identically 0.
2. **Tighter majorants (§2), recommended: P1, the corner (vertex) bound** sup_{T_ρ}|Σc_k e_k| ≤ max_σ Σ|c_k|
   e^{2πρ σ·k}.
   - It is rigorous by convexity, uses the same data, costs nothing in the kernel and about 600–900 Lean lines.
   - It recovers essentially the whole sup for DK and the Gram inverse (1.3026 against a sup of 1.3025, and
     1.8332 against 1.8331), and two thirds (lower torus) to all (upper) of the residual's ℓ¹ excess, measured in
     orders.
   - Under v1 at the R1 package it gains **+0.75 to +0.82 orders**.
   - With the cosh primitive in the ball pass (+0.03) and the exact quadratic γ* (+0.06) the total is +0.84 to
     +0.91 orders.
   - The maximum-principle grid bound (P2) adds only +0.01 to +0.20 more, for 1.5–3k Lean lines and a heavy kernel
     evaluation. It is not recommended.
3. **Frequency data (§2.5, §2.6).**
   - *Quadratic frequencies.* The exact Diophantine infimum is kernel-certifiable with a 2-row enumeration plus
     the norm tail. It gives γ* = 1/(40+g) = 0.024620 instead of 1/42, worth +0.06 orders.
   - *Cubic frequencies.* The direction-optimized norm argument certifies γ ≈ 0.3378 instead of 1/12 for the cubic
     test vector, a factor 4.05, worth +2.4 orders on γ⁴ for an n = 3 client.
   - *Small-divisor sums.* The exact sum S(ω, δ) is kernel-evaluable in O(1/δ) rational operations. At
     δ₀(R1) the frequency-specific constant is **107× below the Rüssmann constant** of v1 (c_R,eff = 0.00296
     against 0.3163; it agrees with SHARP-PLUS's `c_freq` within 0.7 %).
4. **Measured step-0 objects (§2.7).** On R1 the actual cohomological solution of the invariance error is
   **10^6.1–10^6.5 below the Rüssmann a-priori bound**, and 10^4.0–10^4.5 below even the frequency-specific
   bound. The reason is that the residual's mass sits at the truncation edge (|k| ≈ 170), where the strip loss and
   moderate divisors damp it. This is the strongest evidence for SHARP-PLUS's lever L6. The checker cost is a
   coefficient-wise division plus about 20 low-precision products of frame models (≤ 1k terms) against E-sized
   models.
5. **The v2 hypotheses (§2.7)** are cheap to certify, because every object they bound is already built by the
   checker. Measured on R1, compared with what v1 derives:

   | Object | Measured | v1 derives |
   |---|---:|---:|
   | \|Lᵀ\| | 1.33 | 5.24 |
   | \|N\| | 1.35 | 2.41 |
   | \|Nᵀ\| | 1.38 | 9.63 |
   | sup \|T\| on the strip | 3.60 | H_T = 93 |
   | \|ω\| | 1.90 | Θ = 28.8 |
   | \|D²X_H\| | 1.13 (cosh) | M = 1.99 |
6. **Optimizer (§3).** `scripts/certifier/optimize.py` searches 13 unimodular frame classes, action scaling, time
   scaling, ρ, μ and s against v0, v1, an L2-emulated v1 and SHARP-PLUS's v2.
   - It reproduces CONSTANTS-STUDY exactly: P0 −99.87, R1 −74.51, and the emitted R1 −74.67 with T/e +3.03.
   - The rotated frame is optimal among 13 frame classes, by 3.2 orders.
   - At the emitted L = 88 data, re-optimizing gains +2.0 / +2.3 orders under v1, almost all from a smaller strip
     (ρ ≈ 0.0054). That is an artefact of over-resolved data: re-truncated to what v1 needs (L ≈ 32), ρ = 1/70 is
     optimal again, and R1's parameters are within 0.1–0.2 orders of the optimum.
   - Support needed for two orders of headroom (T/e ≥ 2), from re-truncated candidates (`rho_retrunc.py`,
     `v2_support.py`):

     | Theorem and checker | Truncation L | v terms (half lattice) |
     |---|---:|---:|
     | v0 (R1 today) | 88 | 4.2k |
     | v1, landed checker | ≈ 33 | |
     | v1 with P1 | 32 | about 0.5k |
     | SHARP-PLUS's v2 mirror with P1 | **17–18** | about 160 |

     At L = 18, v2 gives T/e +3.0 at ρ = 1/70.
   - Under v1 the exact symmetries hardly matter, and v2 should keep it that way (§7). The time scale c moves T/e
     by only +0.10 orders between c = 1.9 and c = 30 once μ is retuned, and the action scale λ settles at 1.
     Under v0 they mattered: CONSTANTS-STUDY's P4 time rescaling was +0.4 orders.
7. **Kernel (§4).** After the D34 packing fix, the dominant cost is `Slp.compose`: the whole 887-slot program, run
   three times per torus. At a 10⁻²⁵ threshold (L ≈ 33) packed products fall about 20× and are one declaration
   each, while compose falls only about 8×. Every kernel lever touches SO-owned code and is proposed only. The
   largest, compose pruning plus sharing, is 4.6× on compose ops. It can also be implemented *outside* the SO
   paths inside the new certifier (§6, package C7).
8. **Package split (§6).** Seven packages under `KAM/CertificateSharp/`, on top of SHARP-A8's
   `AposterioriEngine`:
   - C1 corner bounds;
   - C2 certified frequency data;
   - C3 ball trig primitive and split H bounds;
   - C4 frame-object majorants;
   - C5 measured step 0;
   - C6 engine v2 interface;
   - C7 shared and pruned compose.

## 1. Inventory of `checkTorusCertificate`

The certifier is `KAM/Certificate/Defs.lean:293-295`. The hypotheses are assembled in `Soundness.lean:33-54` and fed
to `g1_explicit` at `:62-74`. Conventions:
- the norm on ℂⁿ × ℂⁿ is the max norm;
- matrix norms are maximum row sums;
- T_ρ = {|Im θ_i| < ρ};
- `IsDiophantine γ τ ω` means γ/|k|₁^τ ≤ |k·ω| for k ≠ 0 (`KAM/Frozen/Defs/IsDiophantine.lean:24`).

The model calculus is `CertModel` (`Model/Basic.lean:78-104`). A model is a polynomial plus a sup radius, and its sup
bound is `supBound` = (2π)^deg (Σ_k (|Re c_k| + |Im c_k|) w^{|k|₁} + rad), with w ≥ e^{2πρ}.

### 1.1 What each sub-check proves and how

| Sub-check | `G1Hyps` fields (soundness lemma) | Bound used |
|---|---|---|
| `checkStatic` (`Defs.lean:220`) | hn, hτ, positivity, orderings, hs1, hsσ, hγ, hγγbar, he0; with the box also hωstar, hν1, hν2 (`Sound/Static.lean:99,130`) | exact ℚ. ‖ω*‖ ≥ L = max_i(\|c_i\| − r_i) |
| (structural) | hK, hKp, hKr (`Sound/Static.lean:152`); hopen, htransl, hholo, hper, hreal (`ham_structural`) | law-free |
| `checkHamBounds` (`:237`) | hbd (`Sound/Ham.lean:81`) | ball arithmetic of the order-3 jet program over all of D = T_{ρ_H} × polydisc at once (`Expr/Ball.lean:155-199`): one complex ball per slot; characters are the discs (0, w_H^{\|k\|}), so a cosine mode is bounded by w_H^{\|k\|} and not by cosh. The five sums of \|re\|+\|im\|+r are bridged by `NormBridge`. Σ_a\|∂_aH\| (= ‖Dh‖), max_a (= ‖X_h‖) and the row sums (= ‖DX_h‖) are exact; Σ_bc\|T_abc\| and Σ_ab\|∂_a∂_bH\| over-estimate the bilinear norms |
| `checkEmbedding` (`:243`) | hball, hDK (`Sound/Embedding.lean:96`) | ι_i = min(sup\|U_i\|, ρ Σ_j sup\|∂_jU_i\|); action discs; DK row sums Σ_j \|DK_rj\|_w (ℓ¹) |
| `checkInvariance` (`:254`) | hE (`Sound/Invariance.lean:142`) | `Slp.compose` replays the jet on Fourier models along K, with character and exp witnesses; each of the 2n rows of X_H∘K − DK(sω) gets `supBound` ≤ e |
| `checkEnergy` (`:263`) | hEn (`Sound/Energy.lean:104`) | zero mode ± radius |
| `checkGram` (`:270`) | hG (`Sound/Gram.lean:27`) | approximate inverse B (a Fourier polynomial); δ = row sums of the sups of I − BG, β = row sums of \|B_ij\|_w; β/(1 − δ) (`MatrixInv.lean`) |
| `checkTorsion` (`:275`) | hTu, hTb (`Sound/Torsion.lean:68`) | entrywise models of the bordered torsion (keys [4,0..10]); average = zero modes, with radii in R; constant witness S; ‖S‖/(1 − δ_T) |
| `checkSmallness` (`:285`) | hC1, hdisp (`Sound/Smallness.lean:27`) | exact ℚ mirrors `isoC1Q`, `isoC2Q`. For n = 2, τ = 1, c_R = max(1, cohConst) = 1, so they are exact |
| (outside the Bool) | `IsDiophantine` | `QuadraticDiophantine.lean`: γ = 1/21 for (ν±, 1) by the algebraic norm; 1/42 in the rotated frame by `DiophantineTransfer` (factor 2) |

### 1.2 Looseness measured on R1

Sampled sups are taken on the distinguished boundary of the polystrip, with FFT grids of 1024 × 256 (2048 × 512 for
the residual). The "corner" column is proposal P1 (§2.1). The time scale is c = 237/125 where it matters. The two
tori agree to the digits shown unless both are given.

| Quantity | Hypothesis | Landed checker | Corner (P1) | True (sampled sup) | Checker / true |
|---|---|---:|---:|---:|---:|
| D²H sum (sets M) | hbd | 2.0205 | 1.9862 (cosh) | 1.9857 | 1.017 |
| \|D²X_H\| row sum | hbd | 1.5645 | 1.1340 (cosh) | 1.1277 | 1.39 |
| \|Dh\|, \|X_h\|, \|DX_h\| | hbd | 1.980, 1.896, 1.896 | 1.978, 1.896, 1.896 | 1.975, 1.896, 1.896 | 1.00 |
| ‖DK‖ (σK − μ) | hDK | 1.3604 | 1.3026 | 1.3025 | 1.044 |
| ι₁ (Im of the angle displacement) | hball | 0.00515 | 0.00515 | 0.00427 | 1.21 (only enters ρ_H) |
| ‖G⁻¹‖ (σB − μ) | hG | 1.9799 | 1.8332 | 1.8331 | 1.080 |
| ‖⟨T_bord⟩⁻¹‖ (c = 1) | hTb | 1.022493 | – | 1.022493 | 1.000 |
| invariance e, lower (c × max row) | hE | 2.010e-78 | 8.78e-79 | 5.56e-79 | 3.61 |
| invariance e, upper | hE | 3.919e-78 | 1.996e-78 | 1.960e-78 | 2.00 |
|   polynomial part R3 alone, lower / upper | | ℓ¹/sup 4.28 / 2.13 | corner/sup 1.73 / 1.02 | | |
| energy \|⟨H∘K⟩ − E₀\| | hEn | 7.4e-81 | | | not binding |
| γ (rotated frame) | IsDiophantine | 1/42 = 0.023810 | | 0.024620 (exact) | 0.967 |

The pilot's θ frame at ρ = 1/200 shows the same pattern:
- Gram inverse: the pilot's entrywise adj/det route gives 3.544, the approximate-inverse ℓ¹ gives 2.466, the corner
  bound gives 2.2998, and the sup is 2.2987.
- DK: 1.6795, 1.5990, 1.5989.
- The torsion inverse, 2.718 and 2.850, is exact.

Notes:
- The exp-witness part of e, the term e^{2B}(ε₀ + (1/2+ρ)Σr_j)·w^{|s|}, is 13 % (lower) and 11 % (upper) of the corner
  value, and it is not improved by P1. It shrinks with a better witness and is SO-owned.
- The residual's ℓ² norm on the distinguished torus, which is what Parseval-type estimates consume, is 3–5× below its
  sup: 0.32 and 0.39 of it for the lower torus, 0.19 for the upper. It is a lever only for the theorem (§7).

### 1.3 Looseness on the toys (`certificates/so-toys/`, SO-TOYGEN)

- **T2, T3, TR** have polynomial Hamiltonians and flat tori (U ≡ 0, A constant):
  - every model is exact (radius 0), ‖DK‖ = 1, the Gram check has β = 1 and δ = 0, and the torsion inverse is
    exact;
  - the ball pass is exact for polynomials;
  - the invariance error is 2r₀ by construction (the frequency box width), so its bound is tight;
  - nothing is loose. The toys exercise the code paths, not the sharpness.
- **T2d** (H = J + (p²/2)·N/N, N = 3 + cos 2πq) shows the **dependency problem**:
  - ∂³_q(N·N⁻¹) ≡ 0, but the ball pass bounds ‖D²X_H‖ by 1522.6, so M = 1598.8 against a true value of about 2;
  - under v0, whose constants are polynomials in the single size 𝔪 with exponent up to 37, this is about 37·log₁₀ 800
    ≈ 107 orders;
  - the regenerated T2d (`summary.json`) avoids it by putting a 10³⁰ constant in N.
  - Lesson: for rational Hamiltonians the ball pass needs a centred form (mean-value form around the centre),
    subdivision, or the simplification N·N⁻¹ → 1 at compile time (§2.4). For the lunar H, a trigonometric
    polynomial, the only loss is the disc-versus-cosh bound.

### 1.4 What the theorem derives instead of checking (v1, at R1, c = 237/125)

The sharp v1 theorem derives these from (M, σK, σB, σT) (`KAM/Sharp/Constants.lean`,
`KAM/Iso/Sharp/Constants.lean`). The measured values come from `scripts/certifier/v2_majorants.py`.

| Object | v1 derives | Measured sup on T_ρ | Ratio |
|---|---|---:|---:|
| \|Lᵀ\| | 2nσK = 5.24 | 1.33 | 3.9 |
| \|N\| | σKσB = 2.41 | 1.35 | 1.8 |
| \|Nᵀ\| | 2nσKσB = 9.63 | 1.38 | 7.0 |
| sup\|T\| (2×2 block, strip) | H_T = 4nMσK²σB² + 1 = 93.1 | 3.60 (real torus 3.56) | 26 |
| \|ω\| | Θ = 2nσKσB(M+1) = 28.8 | 1.896 | 15 |
| \|D²X_H\| | M = 1.99 | 1.13 | 1.8 |

These are the gains SHARP-PLUS's L1 harvests; its own mirror uses the same objects (`r1_norms.py`). §2.7 gives the
cost of certifying them.

## 2. Tighter rigorous majorants

### 2.1 P1: the corner (vertex) bound, recommended

**Statement.** Let f = Σ_k c_k e_k + R with sup_{T_ρ}|R| ≤ r. For θ = x + iy ∈ T_ρ:

  |f(θ)| ≤ Σ_k |c_k| e^{−2π k·y} + r =: Φ(y) + r ≤ max_{σ∈{±1}ⁿ} Σ_k |c_k| e^{2πρ σ·k} + r.

**Proof.** Φ is a sum of exponentials of linear forms, so it is convex on the box [−ρ, ρ]ⁿ, and its maximum is at a
vertex. Concretely:
- with the product weights λ_σ(y) = Π_i (1 + σ_i y_i/ρ)/2, which are nonnegative and sum to 1, the vector y equals
  Σ_σ λ_σ(−σρ) componentwise;
- convexity of exp in one variable at a time gives e^{−2πk·y} ≤ Σ_σ λ_σ e^{2πρσ·k};
- sum over k.

The same argument bounds a row sum Σ_j |f_j(θ)| ≤ max_σ Σ_j Σ_k |c_{jk}| e^{2πρσ·k} + Σ_j r_j, which is the form the
DK, Gram δ and β, and torsion radius checks need.

**Symmetry.** If f is real on reals, then c_{−k} = conj(c_k), so Φ(σ) = Φ(−σ) and 2^{n−1} vertices suffice.

**Comparison with the landed bound.** The landed bound charges every coefficient its worst vertex at once:
w^{|k|₁} = max_σ e^{2πρσ·k}. The corner bound commits to one vertex for the whole sum. For anisotropic supports
the gain is up to 2^{n−1}: the lunar support is elongated in ψ, with |k| ≤ 190 and |l| ≤ 50.

**Measured** (§1.2):
- e: 2.0–2.3× smaller;
- DK and Gram inverse: exactly the sup to 4–5 digits, because their coefficient phases align at a real point;
- ι: unchanged.

Gain at the fixed R1 package (`optimize.py ladder`):

| Step, R1 package, lower / upper | v0 T/e | v1 T/e | v1 + L2 (emulated) |
|---|---:|---:|---:|
| landed checker | +2.76 / +2.47 | +52.80 / +52.51 | +57.71 / +57.42 |
| + corner bound on e | +3.12 / +2.76 | +53.16 / +52.80 | +58.07 / +57.71 |
| + corner bound on every model (σK, σB, ι) | +3.12 / +2.76 | +53.62 / +53.26 | +58.41 / +58.06 |
| + cosh trigonometric primitive (§2.4) | +3.39 / +3.04 | +53.65 / +53.29 | +58.42 / +58.07 |
| + certified γ* (§2.5) | +3.45 / +3.09 | +53.71 / +53.35 | +58.42 / +58.07 |
| + sampled sup, P2 (§2.2) | +3.65 / +3.11 | +53.91 / +53.36 | +58.62 / +58.07 |

Under v0, the one size 𝔪 is set by M (2.0205 > σB), so the corner bound on σB does not help, while the cosh
primitive does. Under v1, σK has elasticity −11.3 and σB −7.5 (`thresholds.py` at R1), so a 4 % and an 8 % gain
matter.

**Lean.** About 600–900 lines in `KAM/CertificateSharp/Corner/`:
- `CertWeight2`, a weight with both w ≥ e^{2πρ} and w̲ ≤ e^{2πρ}. The lower bound comes from the Taylor partial sum,
  all terms positive. Upper bounds of e^{−2πρm} are w̲^{−m};
- `weightedNormCornerUp` and `CertModel.supBoundCorner`;
- the vertex lemma, by induction on n with `Fin.cons`, from the two-point convexity e^{at} ≤ ((1+t/ρ)/2)e^{aρ} +
  ((1−t/ρ)/2)e^{−aρ};
- the row-sum version;
- corner variants of the embedding, invariance and Gram checks and the torsion radius, reusing the landed model
  construction and replacing only the final `supBound` comparison.

The soundness proofs are near-copies of `Sound/{Embedding,Invariance,Gram,Torsion}`. Each uses
`CertModel.norm_le_supBound` (`Model/Basic.lean:172`) at a handful of sites, and the corner lemma has the same
shape.

**Kernel.** 2^{n−1} weighted sums per bounded model instead of 1, with no product. This is negligible: the bounded
models are the final rows, not the factors.

### 2.2 P2: maximum principle on the distinguished boundary plus sampling, not recommended

**Soundness.**
- *Reduction to the distinguished boundary.* A Fourier polynomial f is entire, and in each variable separately,
  z_i = e^{2πiθ_i}, it is a Laurent polynomial on an annulus. By the maximum modulus principle one variable at a
  time (or Phragmén–Lindelöf on vertical strips, in Mathlib as `PhragmenLindelof.vertical_strip`), sup_{T̄_ρ}|f| is
  attained on the distinguished boundary {|Im θ_i| = ρ for all i}. That boundary is 2ⁿ real tori, or 2^{n−1} up to
  conjugation for real-on-reals f.
- *Row sums.* Σ_j |f_j(θ)| = sup_{|a_j| ≤ 1} |Σ_j a_j f_j(θ)|, and each a-combination is holomorphic, so row sums
  reduce the same way.
- *Interpolation on each torus.*
  - First order: |f(x)| ≤ max_grid|f| + (h/2)Σ_i sup|∂_i f|.
  - Second order: with ∇f evaluated at the grid points, the error is (h²/8)Σ sup|∂²f|.
  - The derivative sups can be crude weighted ℓ¹ norms.
- *Alternative.* For a trigonometric polynomial of degree D_i in variable i on a grid N_i > πD_i/ε, Bernstein's
  inequality gives sup ≤ max_grid/(1 − Σ_i πD_i/N_i). Bernstein is not in Mathlib.

**Measured gain beyond P1:**
- e: +0.20 orders on the lower torus, +0.01 on the upper;
- σK and σB: none, since P1 is already at the sup.

**Cost.**
- The residual has about 10⁴ terms of degree (190, 50). A 1 % interpolation error needs grids of about 4096 × 1024
  even at second order. That is 4·10⁶ points per torus: about 4·10¹⁰ term evaluations directly, or a kernel FFT on
  balls with its own correctness proof.
- Lean: 1.5–3k lines (polystrip maximum principle, grid interpolation, evaluation or FFT soundness).
- It pays only for objects whose coefficient phases do not align at a real point, i.e. the residual, and there P1
  already recovers two thirds to all of the excess.

**Verdict.** Not recommended. If a theorem ever consumes an ℓ² error (§7), P2 is moot anyway.

### 2.3 Matrix inverses: approximate inverse and Neumann in the actual norm

- **The Gram inverse.** The landed `gramCheck` already uses an approximate inverse B (a Fourier polynomial witness)
  and a pointwise Neumann bound ‖G⁻¹(θ)‖ ≤ ‖B(θ)‖/(1 − ‖I − B(θ)G(θ)‖).
  - The loss is entirely in the norm of B: row sums of entrywise ℓ¹ give 1.9799 against a sup of 1.8331.
  - With P1 for β and δ (same B, same products) the bound is 1.8332. Nothing more is available: δ = 2.5·10⁻¹².
  - The pilot's other route, entrywise adj(G)/det(G) with a reciprocal witness of det G, loses 54 % (3.544 against
    2.299) and should never be used.
- **The averaged torsion.** The hypothesis is on the inverse of a constant matrix. The landed Neumann check with a
  constant witness S is exact to 10⁻¹⁰ (radii 4·10⁻¹¹), so there is nothing to gain.
- **One structural remark (§1, inventory agent).** The certified radius ‖G⁻¹ − B‖ ≤ δβ/(1 − δ) is a bound on a row
  sum, but it is put on every entry of the G⁻¹ model in `torsionModels`, an n-fold overcount, and pushed through
  about ten matrix products. This is harmless at δ = 10⁻¹², but a v2 hypothesis on ‖G⁻¹ − B‖ would want the
  entrywise P1 bound of I − BG instead.

### 2.4 Ball-arithmetic primitives

- **Trigonometric primitive.** `Slp.balls` compiles cos(s·Q) to (χ_s + χ_{−s})/2 with |χ_s| ≤ w_H^{|s|₁}. A primitive
  |cos z|, |sin z| ≤ cosh(Im z) ≤ cosh(2π|s|₁ρ_H) gives:
  - D²H sum 2.0205 → 1.9862 (M);
  - |D²X_H| 1.5645 → 1.1340.
  - Gain: +0.03 orders under v1, +0.28 under v0 (M binds 𝔪 there), and 39 % on M₂ if v2 separates it.
  - The gain depends on the frame. In the θ frame the forcing modes have |s|₁ up to 9, and the disc bound inflates
    M from 2.96 to 4.12 (+39 %, c = 5/4, ρ = 1/160).
  - Lean: a new `Slp.ballsTrig` in `KAM/CertificateSharp/Ham/` with its soundness, about 250–400 lines. The landed
    `Expr/Ball.lean` is SO-owned and is not touched.
- **Dependency problem** (T2d). Remedies for rational Hamiltonians, in order of cost:
  - compile-time simplification (N·N⁻¹, common subexpressions);
  - a mean-value (centred) form f(D) ⊆ f(z₀) + Df(D)·(D − z₀);
  - subdivision of the action discs.

  The lunar client does not need any of them.

### 2.5 Certified Diophantine constants

**Quadratic irrationals (exact).** Take ω = (α, 1) with Aα² + Bα + C = 0 and conjugate α′.
- For k ≠ 0, |k₁α + k₂|·|k₁α′ + k₂| = |N(k)|/|A| ≥ 1/|A|. So x := |k·ω| < g/|k|₁ forces
  x ≥ 1/(|A|(g/|k₁| + |k₁|Δ)) with Δ = |α − α′|.
- Hence |k|₁x ≥ (|k₁|(1+|α|) − x)/(|A|(g/|k₁| + |k₁|Δ)), which increases to (1+|α|)/(|A|Δ).
- The certificate enumerates |k₁| < K₀ (for each k₁, only the two k₂ nearest to −k₁α) and checks the tail inequality
  at K₀. The certified γ is the true infimum up to the enclosure of α.

Lunar results (`smalldiv.py`):

| Frame | Infimum γ* | Attained at | Proved | Tail limit | K₀ |
|---|---|---|---|---|---|
| θ, (ν±, 1) | 0.049239 | k = (1, −1) | 1/21 = 0.047619 | 0.883 / 0.905 | 2 |
| rotated, (ν±−1, 1) | 0.024620 = 1/(40+g) | k = (1, 0) | 1/42 (transfer) | 0.458 | 2 |

Gain +0.058 orders on γ⁴. Lean: about 250–350 lines, generalizing `QuadraticDiophantine.lean` (it already has the
norm argument) with the finite enumeration by `decide`. The transfer lemma is no longer needed, since the rotated
frame is certified directly.

**Cubic irrationals (good bounds).** For the test vector (x/2, x²/2, 1/2), x = ∛2, τ = 2 (`CubicDiophantine.lean`,
proved γ = 1/12):
- With γ₀ = k₂ + k₀x + k₁x², N(γ₀) = γ₀|γ₀′|² ∈ ℤ∖0 and γ₀′ = γ₀ + L(k₀, k₁), where
  L = k₀(x′ − x) + k₁(x′² − x²).
- So |k|₁²|k·ω| ≥ F(k₀:k₁) − o(1) with F = (|k₀| + |k₁| + |k₀x + k₁x²|)²/(2|L|²), homogeneous of degree 0.
- min F = **0.3378**, attained in the direction k₀/k₁ = −x. Unit powers of ℤ[∛2] approach that direction, so this is
  also the asymptotic infimum.
- Enumeration over |k₀|, |k₁| ≤ 150 gives 0.3412, at k = (100, −80, 1).
- Certified: γ = 0.3378(1 − ε) from the direction bound (a piecewise-quadratic positivity certificate with x in a
  rational box) plus a finite enumeration where the o(1) terms exceed ε. That is **4.05× the proved 1/12**, worth
  **+2.4 orders on γ⁴** for an n = 3 client.
- Lean: about 400–600 lines. The landed proof uses the cruder adjugate bound |Q| < 6|k|₁².

### 2.6 Exact small-divisor sums S(ω, δ) for v2 lever L2

**Definition.** Following the brief, S(ω, δ) = Σ_{k≠0} |k·ω|⁻² e^{−2πδ|k|₁}; SHARP-PLUS writes the same sum with
e^{−4πδ|k|₁}. The frequency-specific cohomological constant comes from Bessel/Parseval on the 2ⁿ corner tori and
Cauchy–Schwarz:

  ‖u‖_{r−δ} ≤ Γ_spec(δ)‖g‖_r,  Γ_spec(δ) = (2π)⁻¹ 2^{n/2} S(ω, 2δ)^{1/2},

against v1's Γ_R(δ) = c_R γ⁻¹ δ^{−τ}, with c_R = `cohConstR 2 1` = 0.3163.

**Kernel-evaluable bound** (n = 2, ω = (α, 1) after scaling):
- S ≤ 2Li₂(q) + 2Σ_{1≤k₁≤K} q^{k₁} R(k₁) + tail, with q = e^{−2πδ};
- R(k₁) = Σ_l q^{|l|}/(k₁α + l)² ≤ q^{|l_A|}/x² + q^{|l_B|}/(1−x)² + π²/3, with x = frac(k₁α) and l_A, l_B the two
  near-resonant l. This costs +0.4 % at δ₀(R1) against the exact sum. Dropping the weights on the two near terms as
  well would cost +5 %, because |l_A| ≈ 0.025 k₁ is not small;
- tail ≤ Σ_{m>K} 4m³q^m/γ*², with e^{−2πδK} ≤ e^{−40}.
- Each term needs a certified frac(k₁α): an interval enclosure of α of width ≪ γ*/K², about 40–50 bits, from the
  frequency box.
- Cost: K = O(1/δ) rational operations, about 1.3k rows at δ₀(R1) and 4.2·10⁴ at δ₀/32. A stage list for
  δ_s = δ₀2^{−s}, s < 6, is trivial for the kernel.
- Lean: about 300–500 lines (the sum bound and its rational evaluation). The consumer, a δ-dependent constant in
  the small-divisor data, is theorem-side and SHARP-PLUS's job.

**Numbers on R1** (rotated ω′, unscaled; the ratio is invariant under time scaling):

| δ | 0.0005 | 0.001 | 0.0024 (δ₀) | 0.005 | 0.01 | 0.02 |
|---|---:|---:|---:|---:|---:|---:|
| S(ω′, 2δ) | 5.83e5 | 1.46e5 | 2.65e4 | 7.91e3 | 4.39e3 | 3.42e3 |
| Γ_R/Γ_spec, γ = 1/42 | 109 | 109 | **107** | 94 | 63 | 36 |
| Γ_R/Γ_spec, γ = γ* | 106 | 106 | 103 | 91 | 61 | 35 |
| Parseval-generic/Γ_spec | 6603 | 3296 | 1345 | 567 | 190 | 54 |

As a c_R-equivalent: c_R,eff = Γ_spec γ δ = 0.00296 at δ₀, against 0.3163. SHARP-PLUS's `c_freq` gives 0.00298, and
its 10⁻⁶ ray box enclosure gives the same digits. If every Γ in v1 were replaced, the gain would be
−3.9·log₁₀(1/107) ≈ +7.9 orders (c_R elasticity −3.9). In the L2-emulated v1 it is +4.9: other branches (sum, ν)
take over. SHARP-PLUS's staged mirror, with frequency-specific data for 5 stages, gives +2.7 (A5 → A6).

### 2.7 Majorants for the v2 hypotheses: what each costs in the kernel

| v2 hypothesis (SHARP-PLUS) | Object the checker already builds | Extra kernel work | Lean (new) | Measured on R1 |
|---|---|---|---|---|
| separate M₀ ≥ \|X_h\|, M₁ ≥ \|DX_h\|, M₂ ≥ \|D²X_h\| (+ \|Dh\|, \|D²h\|) | the five sums of `hamBoundsOk` | none: compare each with its own rational | 100–200 | 1.896, 1.896, 1.134 (cosh) / 1.565 (disc), 1.978, 1.986 |
| \|Lᵀ\| | DK models (`dkModels`) | column-sum corner pass | 80 | 1.33 |
| \|N\|, \|Nᵀ\| | N models, key [4,0] | row- and column-sum corner passes | 150 | 1.35, 1.38 |
| sup\|T\| on T_ρ | T models, key [4,8] | entrywise corner pass (now only averaged) | 150 | 3.60 |
| \|ω\| ≤ σω\|ω*\| | frequency box | none | 30 | 1.896 |
| Γ_s, s < k (L2) | – | §2.6, O(1/δ_s) | 300–500 | §2.6 |
| step-0 objects (L6): η^N, η^L, u^N = R η^N, ⟨T u^N⟩, ξ^L, ΔK₀, ∂_ωξ, Ω_K, E_sym, E_red | frame models (N, B, T, L) and the invariance rows E | about 20 products (frame model ≤ 1k terms) × (E model ≈ 10⁴ terms) at low precision (60–100 bits relative); one coefficient-wise division by 2πi k·ω per cohomological solve (certified \|k·ω\| from the box); averages are zero modes | 1.5–2.5k | §2.7.1 |

#### 2.7.1 How large the step-0 objects are

`step0_coh.py` takes the action rows g of the R1 invariance error (c = 1) and computes the zero-average solution u of
ω′·∂u = g, using u_k = g_k/(2πi k·ω′). It compares u on T_{ρ−δ₀} with the two a-priori bounds.

| Torus, row | sup\|g\| | \|u\|_{ρ−δ₀} (corner) | Γ_spec sup\|g\| | Γ_R sup\|g\| | Γ_R/measured | Γ_spec/measured |
|---|---:|---:|---:|---:|---:|---:|
| lower P1 | 2.34e-79 | 6.15e-82 | 1.22e-77 | 1.30e-75 | 10^6.33 | 10^4.30 |
| lower P2 | 5.77e-80 | 2.70e-82 | 3.01e-78 | 3.22e-76 | 10^6.08 | 10^4.05 |
| upper P1 | 9.17e-79 | 1.45e-81 | 4.79e-77 | 5.12e-75 | 10^6.55 | 10^4.52 |
| upper P2 | 2.23e-79 | 5.10e-82 | 1.16e-77 | 1.24e-75 | 10^6.39 | 10^4.36 |

The step-0 right-hand sides are low-degree frame matrices times E, so these are orders of magnitude, not the exact
step-0 values. SHARP-PLUS's `step0_actual.py` computes the actual iso step. The mechanism is robust:
- the residual of a truncated candidate lives at the truncation edge;
- there e^{−2πδ₀|k|} ≈ e^{−2.6}, and the divisors |k·ω′| are typically 0.2–5, not γ/|k|.

The second solve (ξ^L) has a right-hand side T u^N + …, again at the edge. Its average ⟨T u^N⟩ only sees the
low-frequency tail of u^N.

**Kernel.** The products in the last table row are the same type as the torsion stage at cfgLow, and they are
cheaper if the factors are first rounded to ~2⁻⁶⁰ relative (proposal K-e in §4). The cost is about 0.1–1 CPU-h per
torus at L = 88 and about 0.01–0.1 at L ≈ 33.

## 3. The free-parameter optimizer (`scripts/certifier/optimize.py`)

### 3.1 Method

**Free parameters.** These are exact symmetries or certificate choices, so the theorem is unchanged:
- **frame** A ∈ GL(2, ℤ), relative to the rotated frame: Q̃ = AQ, P̃ = λA^{−T}P, θ̃ = Aθ (the torus angles must
  follow Q for K̃ to stay primary);
- **action scale** λ;
- **time scale** c: H̃ = cλH(A⁻¹Q̃, AᵀP̃/λ), which is conformally symplectic with factor λ, so the flow is
  conjugate;
- **strip width** ρ and ρ∞ = ρ/1000;
- **margin** μ;
- **ray scalar** s, with ν = (s−1)|ω*|(1 − 10⁻⁹) and σω = 2.

Frames are enumerated with entries in [−2, 2] modulo signed row permutations, which are symplectic and
norm-preserving: 13 classes. The θ frame is A = [[1, 1], [0, 1]].

**Norm oracle** (`scripts/certifier/lunar_oracle.py`). It reports every hypothesis quantity in the frame and in
three regimes:
- `l1`: the landed checker. This uses its disc trig bound and the proved γ: 1/42 rotated, 1/21 θ, other frames by
  the transfer factor;
- `corner`: P1, cosh primitive, certified γ*;
- `sup`: P2 sampled sup × 1.01, cosh, γ*.

The oracle reproduces SO-GEN2's enclosures exactly: σK − μ 1.3604, Gram 1.97994, M₁ 1.047601 (cosh) and 2.0205 (disc,
the Lean D²H sum), torsion 1.022493, η₃ 1.0603e-78.

**Theorems:**
- v0, v1 (iso and fixed) from `thresholds.py`;
- **v1L2**: v1 with c_R → c_R,eff(δ₀) = Γ_spec(δ₀)γδ₀. This is an estimate of L2 assuming the ratio Γ_R/Γ_spec is
  flat for δ ≤ δ₀, which holds in §2.6 to 2 %. It is not a theorem mirror;
- **v2**: SHARP-PLUS's `thresholds_v2.py` (variant A7, iso, k = 5), through `scripts/certifier/v2_adapter.py`.

**Search:**
- stage A ranks all frames under v1/corner;
- stage B uses fine grids on the top three frames plus the rotated and θ frames: 7 λ × 18 ρ × 12 μ × 22 c × 3 s;
- stage C refines each optimum by coordinates, then re-optimizes in the `sup` regime from the corner optimum.

**Objective:** log₁₀ T − log₁₀ e for the fixed candidate data. The truncation is that of the emitted R1
certificates; §4 converts T/e into support.

### 3.2 Validation (reproduction mode)

| Package | Reference | Optimizer |
|---|---:|---:|
| P0 pilot (θ, m = 4, ρ = 1/200, μ = 1/1000, ν = 1/4), v0 | −99.87 (CONSTANTS-STUDY) | −99.874 |
| R1 of CONSTANTS-STUDY (m = 39/20, c = 7/4), v0 | −74.51 | −74.509 |
| R1 emitted (m = 1987/1000, c = 237/125), v0 | −74.67, T/e +3.03 (`lower_rot.json`) | −74.669; oracle norms with cosh M (as `rot_norms.py`) −74.66, T/e +3.03 |
| R1 package with the Lean M = 2.03 (`KAM/SpinOrbit/LunarParams.lean`), v0 | – | −74.94, T/e +2.76 |
| R1 package, v1 iso | −24.98 (`thresholds.py`, norms 1.05 × sup) | −24.90 (oracle ℓ¹ norms, disc M = 2.0205) |

Note: the Lean R1 parameters `lunarR1` set M = 203/100, above the checker's D²H sum of 2.0205, so their one-size 𝔪
is 2.03, not 1.987. Under v0 that costs 0.27 orders against the emitted JSON's package. Against the certified error
budgets (4.03e-78 and 7.84e-78) there are still 2.2–2.5 orders of slack, so this is a remark, not a defect.

### 3.3 Results

Best package per theorem and regime, emitted candidates (L = 88), both tori (`optimize.py search`). Every optimum
is in the **rotated frame**. Stage A, v1 with corner bounds, ranks the frames:

| Frame | Best T/e |
|---|---:|
| rotated | +55.38 |
| [[1,−1],[0,1]] | +52.23 |
| θ | +52.05 |
| [[1,0],[1,−1]] | +52.02 |
| [[1,1],[1,0]] | +51.59 |
| entries ±2 | ≤ +48.4 |
| [[1,2],[1,1]]-type | ≤ +45.7 |

| Theorem / regime | Lower: T/e at R1 → optimum | Upper: T/e at R1 → optimum | Optimum (lower) |
|---|---|---|---|
| v0 / ℓ¹ (landed) | +2.76 → **+2.95** | +2.47 → **+2.68** | c 1.72, ρ 0.0147, μ 0.0060, λ 0.90 |
| v0 / corner | +3.45 → **+4.56** | +3.09 → **+4.16** | c 1.64, ρ 0.0161, μ 0.0057, λ 0.95 |
| v0 / sup | +3.65 → **+4.58** | +3.11 → **+4.00** | c 1.64, ρ 0.0153, μ 0.0057 |
| v1 / ℓ¹ (landed) | +52.80 → **+54.84** | +52.51 → **+54.81** | c 30, ρ 0.0052, μ 0.00018, λ 1 |
| v1 / corner | +53.71 → **+55.44** | +53.35 → **+55.38** | c 30, ρ 0.0054, μ 0.00018 |
| v1 / sup | +53.91 → **+55.62** | +53.36 → **+55.32** | c 30, ρ 0.0057, μ 0.00018 |
| v1L2 (emulated) / ℓ¹ | +57.71 → **+60.76** | +57.42 → **+60.72** | c 63, ρ 0.0052, μ 0.0078, s−1 10⁻⁴ |
| v1L2 / corner | +58.42 → **+61.26** | +58.07 → **+61.20** | c 63, ρ 0.0054, μ 0.0078 |
| v2 (SHARP-PLUS A7) / corner | +66.92 (log₁₀T −11.18; c = 7/4) → **+68.92** | not run | c 4.8, ρ 0.0060, μ 1/160 (`v2opt`, coordinate search) |

In the "at R1" column, the ℓ¹ entries are the landed checker at the R1 package; the corner and sup entries include
the cosh primitive and γ* (the ladder of §2.1).

### 3.4 Reading the optimum

- **Frame and action scale.** The rotated frame (owner ruling O5) is optimal among all 13 classes, by 3.2 orders
  over the next one. The action scale λ stays within 0.9–1.05 and gains nothing. Under v1, λ > 1 shrinks the Gram
  inverse but raises the torsion inverse and the D²H action block; under v0 the one size 𝔪 is pinned by M ≥ c,
  which comes from the linear part of H′.
- **Time scale.** Under v1 the optimum's c ≈ 30 is a flat direction: at fixed ρ, T/e moves by +0.10 from c = 1.9 to
  c = 120 once μ ∝ 1/c is retuned. Profile at ρ = 0.0054, corner regime:

  | c | 1.9 | 4 | 8 | 16 | 30 | 60 | 120 |
  |---|---:|---:|---:|---:|---:|---:|---:|
  | v1 T/e | +55.34 | +55.39 | +55.42 | +55.43 | +55.44 | +55.44 | +55.44 |
  | v1L2 T/e | +60.63 | +60.88 | +61.05 | +61.16 | +61.22 | +61.26 | +61.27 |

  So the R1 choice c = 237/125 loses only 0.1 orders under v1. A large c with a tiny μ, which the downstream
  barrier and confinement statements may dislike, is not worth it.
- **Strip width: the one real gain at L = 88, and an artefact of over-resolved data.** At fixed L = 88 the optimum
  moves from ρ = 1/70 to ρ ≈ 0.0054 (+1.6 orders at c = 1.9). The candidate's error sits at the truncation edge,
  |k| ≈ 170, where the weight e^{2πρ|k|} falls faster than v1's threshold, which goes like δ₀⁴ ∝ ρ⁴.
- **The support-sized candidate.** Once the candidate is re-truncated to what v1 needs (`rho_retrunc.py`), ρ = 1/70
  is optimal again: T/e at L = 32 is +1.30, +1.72, +2.18, +2.41, **+2.50**, +2.36, +1.64 and +0.52 for
  ρ = 0.004, 0.0054, 0.008, 0.0107, **1/70**, 0.02, 0.03 and 0.04 (lower torus, corner regime, μ optimized; same
  shape at L = 28, 36 and on the upper torus).
- **Under v2** (SHARP-PLUS's mirror, A7) the picture is the same:
  - at fixed ρ = 1/70 the time scale is worth +0.05 (c = 7/4 → 2.9);
  - the +2.0 of the coordinate search is again the small-ρ artefact of the L = 88 data;
  - my corner-regime norms give log₁₀T = −11.18 at the R1-like package, against −11.37 in SHARP-PLUS's own run with
    1.05 × sup norms. The difference is the 5 % margin, worth 0.2 orders.
- **μ and s.** Under v1, μ ≈ 0.0008 at c = 1.9 is +0.04 over R1's 1/160. In the L2 emulation the sum and ν branches
  bind, so μ ≈ 0.008–0.05 and s − 1 = 10⁻⁴ are preferred.
- **Support (the real deliverable).** Under v1 the R1 parameters (rotated frame, ρ = 1/70, c ≈ 1.9, μ ≈ 1/160 or
  smaller) are already within 0.1–0.2 orders of optimal for a support-sized certificate. With two orders of
  headroom, T/e ≥ 2:

  | Checker | T/e at L = 32 (lower / upper) | Truncation needed |
  |---|---|---:|
  | corner (P1) | +2.50 / +2.60 | L = 32 |
  | landed ℓ¹ | +1.62 / +1.74 | L ≈ 33 |
  | landed v0 | | L = 88 |

  That is 7.5× fewer terms and about 60× fewer E×E pairs than R1 (§4.1). Each further order of T/e is about 1.1
  digits.
- **Support under v2** (`v2_support.py`; corner regime, c = 7/4, μ = 1/160, lower / upper; the v2 threshold is
  −11.57, −11.18 and −10.85 at ρ = 0.01, 1/70 and 0.02, independent of L):

  | L | T/e at ρ = 0.01 | ρ = 1/70 | ρ = 0.02 |
  |---:|---:|---:|---:|
  | 16 | +1.15 / +1.08 | +1.38 / +1.33 | +1.45 / +1.42 |
  | 18 | +2.80 / +2.73 | **+3.04 / +2.96** | +3.12 / +3.03 |
  | 20 | +4.72 / +4.86 | +4.90 / +5.02 | +4.90 / +4.99 |
  | 24 | +8.34 / +8.39 | +8.45 / +8.51 | +8.33 / +8.40 |

  So v2 needs L ≈ 17–18 digits (≈ 160 v half-lattice terms, ≈ 330 E terms, ≈ 84 bits). Under v1 the same
  candidates have T/e between −12 and −5. At that size every product is a single small declaration: the kernel
  questions of D34 disappear, and the compose cost (§4.2) scales down by about (18/88)² ≈ 1/24 in terms.
- **Under v0** (the sealed theorem the SO track uses today), the parameters matter more:
  - with the landed checker, re-optimizing adds +0.2 (ρ ≈ 0.0147, c ≈ 1.72, λ ≈ 0.9);
  - with P1 and the cosh primitive, the one size 𝔪 drops from 2.02 to 1.84 (σB binds), giving T/e +4.56 / +4.16 against
    +2.76 / +2.47, **+1.7 to +1.8 orders**;
  - that is about 2 digits of L (88 → 86) under the theorem in force today.

## 4. Kernel efficiency (D34 and the SO replay studies)

Sources: SO-REPLAY, SO-REPLAY2, SO-ADVCOUNT, SO-DATA-1, SO-GEN2, the OVERNIGHT log of `main`
(`/home/scott/KAM-dev/docs/campaign/OVERNIGHT.md`, cited as OVN:line), and a read of `KAM/Certificate/Poly/*`
before SO-PACKFIX. Measured numbers are marked as measured; the rest is extrapolated.

### 4.1 From threshold to support (measured)

- The exact residual in the rotated frame (ρ = 1/70, c = 237/125, the worse torus) fits log₁₀(cη) ≈ −0.909·L + 2.60
  over L = 20–92, with L the truncation in digits.
- The smallest admissible truncation L_min satisfies cη ≤ T/2. SO-GEN2's convention adds two orders:
  L_h ≈ (4.6 − log₁₀T)/0.909. This reproduces SO-GEN2's L_min = 86 and L_h = 88 at 10⁻⁷⁵.
- Each order of T/e gained by the checker is worth **1.1 digits of L**.

Sizes:

| log₁₀T | L_h | bits S | v half / full | E terms | E×E pairs | packed window (rel.) | terms (rel.) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| −75 | 88 | 318 | 4233 / 8466 | 8322 | 6.9e7 | 1 | 1 |
| −50 | 61 | 228 | 1944 / 3888 | 3821 | 1.5e7 | 0.33 | 0.46 |
| −35 | 44 | 171 | 949 / 1898 | 1904 | 3.6e6 | 0.13 | 0.23 |
| −25 | 33 | 134 | 522 / 1044 | 1038 | 1.1e6 | 0.049 | 0.125 |
| −15 | 22 | 98 | 214 / 428 | 425 | 1.8e5 | 0.017 | 0.051 |
| −11 (v2 mirror) | 17–18 | ≈ 84 | ≈ 160 / 320 | ≈ 330 | ≈ 1.1e5 | ≈ 0.01 | ≈ 0.04 |

### 4.2 Where the kernel time goes

- **Packed products after the D34 fix.** Model only, not yet re-measured: 2.5–7.5 CPU-h per torus at L = 88
  (OVN:1197-1206), against 50–85 as landed.
- **`Slp.compose`.**
  - It evaluates all 887 jet ops, 675 of which carry models (`Expr/Compose.lean:180-187`).
  - It is called three times per torus: invariance, energy and torsion.
  - Measured 35–95 s and 0.7–0.9 GB per op on an 8.5k-term model (OVN:1149, 1156).
  - Extrapolated: 20–53 CPU-h per torus at L = 88.
- **Products with an 8.3–8.7k-term factor.** 63 of 129 products have one, because cfgLow factors are not trimmed
  (`Gram.lean:115-124`, `Torsion/Models.lean:155-165`). The three products that genuinely need full precision are
  the energy p̃·p̃ and the two witness residuals.
- **At 10⁻²⁵** (L ≈ 33): packed products are about 20× cheaper and fit in one declaration each, with no sharding,
  while compose is only about 8× cheaper.

Per-torus projections:

| log₁₀T | Packed, after the fix | Compose as landed | Compose pruned and shared |
|---:|---:|---:|---:|
| −75 | 2.5–7.5 CPU-h | 20–53 | 4.3–11.7 |
| −25 | 0.12–0.37 | 2.5–6.7 | 0.5–1.5 |

### 4.3 Levers (all touch SO-owned code unless noted: proposals only)

| # | Lever | Gain | Basis | Cost |
|---|---|---|---|---|
| K-a | Support sized to the threshold. R1 already uses L = 88; v1 allows L ≈ 33 | 64× fewer pairs, 20× fewer window bits | measured | regeneration only |
| K-g1 | Compose only the slots each check needs; share one compose between invariance and energy | 2025 → 445 heavy ops (**4.6×**); removes A0·A0 from invariance | measured on the jet | 300–600 lines. **Can live in `KAM/CertificateSharp`** (C7): a pruned program and its denotation lemma, without touching `Expr/` |
| K-g2 | One `gramCheck` result shared by `checkGram` and `checkTorsion` | −9 heavy products | analysis | about 100 lines, proofs only. **Can live in CertificateSharp** (C7) |
| K-e | Round cfgLow factors to ~72 bits before the Gram and torsion products | 63 → 3 heavy products; 5–9× at L ≥ 40; little at L ≤ 30 | model | 500–900 lines; new `ModelConfig` field (signed type: owner approval) |
| K-b | Parity: real-on-reals data with k ↦ −k symmetry; check half the output shards | about 2× (the re/im 4× is already taken) | analysis | 400–700 lines; half-lattice models 2–4k |
| K-c | Packing: the D34 fix, then a mask-and-compare slot check (a fixed number of GMP ops per window) and a per-row geometric `remainderBound` (`MulPacked.lean:209-213` builds a ~45-kbit number per slot) | 50–85 → 2.5–7.5 CPU-h; the rest unmeasured | measured / model / read | in progress (D34); 200–500 lines each |
| K-g4 | Weight table: `weightTermUp` recomputes w^{\|k\|₁} per term, ~23 kbit at the box edge | unmeasured; SO-MALG reported weights dominate (OVN:905) | read | 200–400 lines |
| K-d | Anisotropic supports or strips | box shear ≤ 4 %; anisotropic strips ≤ +5 orders, > 5k lines | measured / study | not recommended |
| K-f | Direct residual instead of composition | 6–10× on invariance, but Hamiltonian-specific, which breaks the black box; generic fusion about 2× | analysis | 1.5–3k lines |

The checker-side levers of §2 also act here:
- P1 is worth +0.86 to +0.88 orders under v1 at the support-sized truncations (L = 28–36, `rho_retrunc.py`), i.e.
  one digit of L (33 → 32);
- L2 and L6 (theorem side) are worth tens of orders, i.e. tens of digits of L.

## 5. Ranked levers

All gains are on R1, in orders of T/e, under v1 unless stated. Lean lines are new code under
`KAM/CertificateSharp/`, except where the lever is theorem-side.

| Rank | Lever | Gain on R1 | Lean cost | Kernel cost | Owner |
|---|---|---|---|---|---|
| 0 | **The sharp theorem itself** (v0 → v1 → v2; SHARP-A1..A8, SHARP-PLUS) | v1 +50 orders, v2 a further +13.7 (threshold 10^−74.9 → 10^−24.9 → 10^−11.2); support 88 → 32 → 17–18 digits | in progress | – | theorem packages |
| 1 | **L6 measured step 0** (theorem: SHARP-PLUS; checker: C5) | step-0 solves are 10^6.1–10^6.5 below the a-priori bound; tens of orders (SHARP-PLUS quantifies) | checker 1.5–2.5k; theorem: SHARP-PLUS | about 20 low-precision products: 0.1–1 CPU-h at L = 88, ≤ 0.1 at L ≈ 33 | SHARP-PLUS + C5 |
| 2 | **L2 frequency-specific small divisors** (checker: C2) | Γ 107× smaller at δ₀; +2.7 in SHARP-PLUS's staged mirror, +4.9 to +7.9 in the v1 emulation | checker 300–500 | O(1/δ_s) rational ops, trivial | SHARP-PLUS + C2 |
| 3 | **L1 measured frame majorants** (checker: C3, C4) | factors 1.8–26 on derived objects; +4.1 in SHARP-PLUS's mirror (A0 → A2, iso) | checker 400–700 | none (corner passes on existing models) | SHARP-PLUS + C3/C4 |
| 4 | **Optimizer** (free parameters) | v1: +2.0 / +2.3 at L = 88 (strip width), but ≤ 0.2 for a support-sized certificate (R1 is near-optimal); v0: +0.2 (landed), +1.7 with P1 | 0 | 0 (regeneration) | SO (proposal) |
| 5 | **P1 corner bounds** (C1) | +0.75 to +0.82 at fixed R1 (e +0.29/+0.36; σK, σB +0.46); +0.86 to +0.88 at the support-sized L ≈ 32 (one digit of L) | 600–900 | negligible | C1 |
| 6 | Cosh primitive in the ball pass (C3) | +0.03 (v1), +0.28 (v0); 39 % on M₂ (v2) | 250–400 | negligible | C3 |
| 7 | Certified quadratic γ* (C2) | +0.06; cubic test vector +2.4 (n = 3 clients) | 250–350; cubic 400–600 | trivial | C2 |
| 8 | Kernel K-g1 + K-g2 (compose pruning and sharing) | 4.6× on compose ops (the dominant kernel cost after D34) | 400–700 (C7) | – | C7 / SO |
| 9 | Kernel K-e, K-b, K-c, K-g4 | 2–9× each on products and weights | 200–900 each | – | SO (proposal) |
| 10 | P2 grid and maximum principle | +0.01 to +0.20 beyond P1 | 1.5–3k | heavy for the residual | not recommended |
| – | Gram/torsion inverses beyond P1 | 0 (P1 reaches the sup; torsion exact) | – | – | – |

## 6. Package split for `KAM/CertificateSharp/`

The split builds on SHARP-A8, whose tree is `Engine.lean`, `SharpEngine.lean`, `Sharp.lean`,
`Constants{,Q,Dom}.lean` and `Tests/Margin.lean`. SHARP-A8 provides:
- `AposterioriEngine`: a threshold test plus soundness to `IG1Body`;
- `checkTorusCertificateWith E`, with every landed sub-check unchanged;
- the old and sharp instances.

The packages below add sharper sub-checks with the same contracts (each still proves its `G1Hyps` field), and an
engine interface for v2's extra certified data. No landed file is edited; `KAM/Certificate/**` is imported read-only.

| Package | Content (files) | Depends on | Lines | Model |
|---|---|---|---:|---|
| **C1 Corner bounds** | `Corner/Weight.lean` (`CertWeight2`, lower exp bound), `Corner/SupBound.lean` (vertex lemma, `supBoundCorner`, row sums), `Checks/{Embedding,Invariance,Gram,Torsion}Corner.lean` (corner variants of the four checks, contracts identical to `Sound/*`), `CornerCertifier.lean` (`checkTorusCertificateCorner E`, its soundness; the A8 engine for smallness), `Tests/Corner*.lean` (toys; a non-flat test model where corner < ℓ¹) | A8 `Engine` | 900–1300 | Sonnet |
| **C2 Certified frequency data** | `Freq/QuadraticExact.lean` (finite enumeration plus norm tail; instance: both lunar frequencies in both frames), `Freq/CubicDirection.lean` (optional, n = 3), `Freq/SmallDivisorSum.lean` (rational upper bound of S(ω, δ) from a frequency box; the stage list Γ_s) | – | 700–1300 | Sonnet (cubic: Opus) |
| **C3 Ball primitives and split H bounds** | `Ham/BallsTrig.lean` (cosh primitive, soundness against `HamExpr.eval`), `Ham/SplitBounds.lean` (M₀, M₁, M₂, M_dh, M_D2H as five rationals) | – | 350–600 | Sonnet |
| **C4 Frame-object majorants** | `Frame/Majorants.lean`: \|Lᵀ\|, \|N\|, \|Nᵀ\|, sup\|T\| on T_ρ from `dkModels`/`torsionModels` with corner passes; \|ω\| from the box | C1 | 400–600 | Sonnet |
| **C6 Engine v2 interface** | `EngineV2.lean`: `CertData` (the certified record: M's, majorants, Γ_s, step-0 bounds) and `AposterioriEngineV2` whose soundness consumes `CertData` facts (never conclusion-shaped: each field is a bound on an explicit object); the A8 engines as instances (`CertData` ignored), regression by `rfl` | A8; SHARP-PLUS signatures | 300–500 | Opus |
| **C5 Measured step 0** | `Step0/Coh.lean` (cohomological solve on models: coefficient division with certified \|k·ω\| ≥ ε_k from the box, radius propagation), `Step0/Objects.lean` (η^N, η^L, u^N, averages, ξ^L, ΔK₀, ∂_ωξ, Ω_K, E_sym, E_red as models; low precision), `Step0/Check.lean` (bounds into `CertData`) | C1, C4, C6, SHARP-PLUS L6 statement | 1.5–2.5k | Opus |
| **C7 Pruned and shared compose** | `Kernel/Prune.lean` (slice of an `Slp` program to the wanted slots; denotation lemma), `Kernel/Shared.lean` (one compose for invariance and energy, one `gramCheck` for Gram and torsion; contracts reused) | – | 400–700 | Sonnet |

**Order.**
- C1, C2, C3 and C7 are independent and can start now.
- C4 needs C1.
- C6 waits for SHARP-PLUS's v2 signatures (`APOST-SHARP-V2-SIGNATURES.lean.txt`).
- C5 needs C1, C4, C6 and the L6 statement.

C1 alone gives a certifier with +0.8 orders on R1 under v1. C1 + C2 + C3 + C4 + C6 give every input of SHARP-PLUS's
L1 and L2. Kernel tests stay on toys, with one small non-flat model test in C1, as SHARP-A8 does.

**Hard-rule notes.**
- Every package is additive (LOCAL-COMMON).
- The new sub-checks are proved against the same frozen hypotheses: no conclusion-shaped premise.
- The vertex lemma and the maximum-principle lemma, if ever done, are general analysis and belong under
  `KAM/CertificateSharp/Corner/`, not in `KAM/Certificate/`.

## 7. Coordination with SHARP-PLUS

- **Hypotheses the checker can certify cheaply** (§2.7):
  - separate M₀, M₁, M₂, \|Dh\|, \|D²h\| (free);
  - \|Lᵀ\|, \|N\|, \|Nᵀ\|, sup\|T\| on T_ρ, \|ω\| (free, given C1);
  - Γ_s for a finite stage list (O(1/δ_s));
  - step-0 objects (about 20 low-precision products).
- **ℓ² errors.** A theorem input "corner-ℓ² norm of E" would be 3–5× below the sup (§1.2). It is exactly what the
  Parseval route consumes at step 0, and it is trivial to certify: Σ|c_k|²e^{4πρσ·k} per vertex. It is worth a
  look only if L6 does not already absorb step 0.
- **Homogeneity.** Time scaling (c) and action scaling (λ) are exact symmetries.
  - v1 is nearly invariant under them: +0.10 orders over c ∈ [1.9, 120] when μ ∝ 1/c is retuned (§3.4). The
    residual non-invariance comes from the absorption γδ^j ≤ γ̄, the "+1" in Θ = 2nσKσB(M+1) and the fixed μ
    budgets.
  - The L2-emulated v1 moves by +0.6 over the same range, because its binding branch is the μ-budget sum.
  - A design rule worth stating in APOST-SHARP-V2: each hypothesis carries its physical dimension and the threshold
    is dimensionless. Then a certificate can never lose by a bad choice of units, and the optimizer's c and λ axes
    disappear.
- **Optimizer hook.** `optimize.py --v2` and `v2_adapter.py` evaluate SHARP-PLUS's mirror on any package. When the
  mirror freezes, re-run §3 under it.

## 8. Uncertainties and caveats

- **Double precision.** The `sup` regime is a sampled sup, and the corner regime is computed in floats from exact
  coefficients rounded to doubles. A certificate would carry rigorous rational versions, which differ in the 10th
  digit.
- **One candidate.** All lunar numbers are for one candidate (truncation 88 digits). The optimizer does not
  re-truncate; §4.1 maps T/e to support.
- **Approximate witness part in other frames.** The exp-witness part of e in frames other than the rotated one uses
  the base frame's witness bound at the frame's ℓ¹ weights. This is an approximation, about 12 % of e.
- **v1L2 is an emulation, not a theorem.** SHARP-PLUS's staged mirror is the reference: +2.7, not +4.9 to +7.9.
- **The v2 mirror is in progress.** Its numbers are those of `thresholds_v2.py` on branch `sharp-plus` on
  30 October 2026, which may change.
- **Lean line counts** are estimates from the sizes of the landed analogues: `Model/Basic.lean` 217,
  `Sound/Embedding.lean` 164, `QuadraticDiophantine.lean` 263, `Gram.lean` 585.
- **Kernel numbers** (§4) are the SO studies' measurements and their extrapolations. SO-PACKFIX was being re-measured
  at the time.

## 9. Reproduction

All commands run from the worktree root with `python3 -I`. CACHE is any scratch directory: the first call builds the
exact residuals, about 40 s per torus.

```
python3 -I scripts/certifier/measure_residual.py lower        # l1 / corner / l2 / sampled sup of the residual rows
python3 -I scripts/certifier/smalldiv.py                      # Diophantine infima, S(omega, delta), Gamma ratios
python3 -I scripts/certifier/lunar_oracle.py CACHE            # norm oracle validation (rotated and theta frames)
python3 -I scripts/certifier/v2_majorants.py CACHE            # |L^T|, |N|, |N^T|, sup |T|, |omega| vs v1-derived
python3 -I scripts/certifier/step0_coh.py CACHE               # cohomological solve of the residual vs a-priori bounds
python3 -I scripts/certifier/optimize.py --cache CACHE reproduce
python3 -I scripts/certifier/optimize.py --cache CACHE ladder --which lower
python3 -I scripts/certifier/optimize.py --cache CACHE search --which lower --json OUT
python3 -I scripts/certifier/optimize.py --cache CACHE v2opt --which lower     # needs the sharp-plus mirror
python3 -I scripts/certifier/rho_retrunc.py CACHE 28 32 36    # rho at the v1 support (re-truncated candidates)
python3 -I scripts/certifier/v2_support.py CACHE 16 18 20 24  # truncation needed by the v2 mirror
```

The v2 mirror is found through the environment variable `KAM_V2_DIR` (default: the `sharp-plus` worktree's
`scripts/apost_sharp`).
