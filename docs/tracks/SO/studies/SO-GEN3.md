# SO-GEN3: lunar tori for a band below 3 % under the sharp certifier

Branch `inp-sogen3`. Python, data and Markdown only; no Lean file touched or built.

## Interim answer (30 October 2026; quick study, numbers to be replaced by the full study below)

**Yes: a band below 2.9 % looks certifiable.** All tori up to N = 65 exist on the full seven-term model, their
Fourier decay barely changes, and the sharp threshold sits about 25.5 orders below 1, so each torus needs only about
38–40 digits and roughly 1–2k terms. With the old certifier, R1 needed 88 digits and 8.5k terms.

| N | converged | lower torus p range | upper torus p range | **band max\|p−1\|** | gap between tori | k-decay (digits/mode) | width ρ_ψ | log10 thr/c (sharp, ρ = 1/70) | L (digits) | v half / E terms (proj.) |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---|
| 40 (R1) | ref. | 0.9676–0.9821 | 1.0179–1.0324 | 3.24 % | 0.0358 | 0.61 | 0.18 | −25.11 | ~38 | 704 / 1406 (measured, 440-bit data) |
| 50 | yes | 0.97099–0.98774 | 1.01227–1.02901 | **2.901 %** | 0.0245 | 0.52 | 0.19 | −25.48 | ~38 | ~820 / ~1650 |
| 55 | yes | 0.97185–0.98993 | 1.01008–1.02814 | **2.815 %** | 0.0202 | 0.48 | 0.18 | −25.64 | ~38–39 | ~890 / ~1770 |
| 60 | yes | 0.97245–0.99173 | 1.00828–1.02754 | **2.755 %** | 0.0166 | 0.45 | 0.17 | −25.79 | ~39 | ~960 / ~1910 |
| 65 | yes | 0.97287–0.99322 | 1.00678–1.02713 | **2.713 %** | 0.0136 | 0.42 | 0.16 | −25.92 | ~39–40 | ~1020 / ~2040 |

**How each column was obtained.**
- **(a) Convergence.** Double continuation in ε (40 steps) plus Newton–GMRES on a 256×64 grid
  (`g3_double.py`; `model.py` now reads `SO_N`). Every run converged, with final projected residual 3–8e-14 and
  4–7 min per torus. ν± = 1 ± 1/(N+g) = 1 ± (2N−1−√5)/D, D = ((2N−1)²−5)/2.
- **(b) The band.** It is the max of |p − 1| on the grid of the numerical torus. disp is about 1e-14 relative
  (see (d)), so it is negligible. The two tori are symmetric to 1e-5. The separatrix floor is 2.62 %.
  - The N = 50 band of 2.901 % only touches 2.9 %.
  - **Below 2.9 % needs N ≥ 51 or so. N = 55 gives 2.82 %, N = 60 gives 2.76 %, N = 65 gives 2.71 %.**
- **(c) Width and decay.** I fitted max_l |b_{k,l}| against |k|.
  - The ψ-decay slows only mildly, from 0.61 digits per mode (N = 40) to 0.42 (N = 65).
  - So the width in ψ is about 0.16–0.19 in every case. The φ-decay is unchanged at about 2 digits per mode.
  - The certificate strip ρ = 1/70 ≈ 0.014 is far inside the width for every N. Analyticity is not the
    constraint.
- **(d) Threshold.** This is an exact transcription of the landed `sharpTest` (`sharp_q.py`, from
  `ConstantsQ.lean`; at the landed R1 it gives 10^−27.89) at an R2-like package (`g3_package.py`):
  - M = c × 1.0657 (the landed D²H sum per unit c);
  - σK, σB, σT from SO-GEN2's measured ‖DK‖ = 1.3604, ‖G⁻¹‖ = 1.9799, ‖avg⁻¹‖ = 1.0225/c, each plus μ;
  - μ = 1/160, ρ∞ = ρ/1000, ν = 1e-6;
  - γ = γ̄ = c/((N+1)s). The binding mode is k = (1, 0), with γ((ν−1, 1)) = 1/(N+g) > 1/(N+1); R1's 1/42 is the
    N = 40 case.

  The quantity that matters is threshold/c, because err ≈ c·η. It is flat for c ≥ 4, with active branch E. The
  displacement coefficient is about 10^12, so disp ≈ 1e-14 at err = 1e-26.
- **Digits and terms.** On R1, SO-GEN2 measured c·η ≈ 10^(−L+10.3) at truncation 10^−L. With 2 orders of headroom
  that gives L ≈ 38 (N = 50) to 40 (N = 65), and about 3.33L + 24 ≈ 150–160 bits. The term counts are N = 40's
  measured counts at L = 38, scaled by the ratio of ψ-decay rates.

**Plausibility.** Every number in (d) depends on majorants measured on the N = 40 tori. The D²H, DK and Gram
values should change little, because the tori differ by less than 1 % in p and the decay is similar, but they still
have to be re-enclosed.

Against R1 under the old certifier (88 digits, 4.2k / 8.3k terms, about 70M product pairs), N = 55–65 needs:
- about 40 digits;
- about 1–2k terms;
- about 3–4M pairs, roughly 20× fewer.

Even at N = 65, the certificate should be **much cheaper than the R1 certificate the SO track already sized**.

**Caveats (interim).**
- All counts are projections, not measured truncations.
- The width uses a 256×64 double grid with a noise floor of about 1e-17.
- The η–L offset of 10.3 may grow by about 1 digit at N = 65, because the cutoff shell sits at larger |k|.
- The package uses N = 40 majorants.
- Each new N needs its own Diophantine lemma (γ = 1/(N+1) in the rotated frame).

**Interim recommendation.** Primary **N = 55 (2.82 %)**; stretch N = 60 (2.76 %). N = 50 gives 2.90 % and does
not clear "below 2.9 %".
