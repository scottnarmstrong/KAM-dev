# E1 report: Hénon–Heiles producer (B3-PRODUCER)

Chain: 3 steps (generators of degree 3..5) with Lie orders L = [5, 2, 2]; model H = I₁ − (√2/2)I₂ + q₁²q₂ − q₂³/3; coefficients in ℚ(√2); all arithmetic exact (`fractions.Fraction`).

## Verdict

* **checkOscChain premises (all conjuncts, η_j = 10⁻¹⁹ literal, a = (81·10⁻⁶)², b = 10⁻⁸, T = 10¹⁰): PASS** — the producer side is **GO**.
* **`oscillatorChain_physical` at the literal physical box a′ = (1/12500)²: NO-GO as the Lean theorem is stated.** Failing: hs3 (s + tail)^2 <= a. This is a structural conflict between the hypotheses `hs1 : 2a′ ≤ s²` and `hs3 : (s+tail)² ≤ a`, not a numerical loss of the producer (see "Structural finding").

## Key numbers

* tail = Σ ε_kδ_k = 7.379850e-08; d = 2.090000e-11 (≤ 10⁻¹⁰: yes); r = 1.414300e-04; δc = 2.000000e-05; ε_b = 1.000000e-12
* η_j target 10⁻¹⁹; minimal feasible η_j (j=0,1) = 4.478189e-20, 4.478987e-20  (margin factor 2.2)
* contributions to η_j: residual supBound({I_j,P}, r) = 1.400683e-21 (j=0), 1.408669e-21 (j=1); Lie tail 2rΣB_k/(L_k!δc) = 4.338120e-20
  * step 1: B_1/L_1! = 9.752883e-25  → 2r·B/δc = 1.379350e-23
  * step 2: B_2/L_2! = 3.066326e-21  → 2r·B/δc = 4.336705e-20
  * step 3: B_3/L_3! = 2.546933e-26  → 2r·B/δc = 3.602128e-25
* final: a + ηT + d = 7.581900e-09 < 1.01e-8; 2d + ηT = 1.041800e-09 ≤ 1.2e-9

## Per-step data

| step | deg χ | #χ | #Q_k | L_k | ρ_k | δ_k | ε_k | ε_kδ_k | small-field m_k |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 3 | 5 | 80 | 5 | 1.615040e-04 | 1.475520e-07 | 1/2 | 7.377600e-08 | 7.377573e-08 |
| 2 | 4 | 8 | 182 | 2 | 1.614310e-04 | 4.400000e-11 | 1/2 | 2.200000e-11 | 2.188409e-11 |
| 3 | 5 | 14 | 454 | 2 | 1.614310e-04 | 1.000000e-12 | 1/2 | 5.000000e-13 | 6.430446e-14 |

Term counts: H 6, Nact 27, P 440 (lowest degree 6). Nact quartic part: (0, 2): (0 + 5/12*r2), (1, 1): (-4/7 + -1*r2), (2, 0): (0 + 13/28*r2) (in I-exponents; matches N₄ = 13√2/28 I₁² − (√2+4/7) I₁I₂ + 5√2/12 I₂²).

## Why three steps

With only χ₃, χ₄ the residual P starts in degree 5 and supBound({I_j,P}, r) ≈ 2.5·10⁻¹⁸ > 10⁻¹⁹ (the plan's predicted bottleneck); χ₅ lifts P to degree 6 and the residual drops to ≈ 1.3·10⁻²¹. See `twostep/E1-report.md` (same script, L = [5, 3], χ₅ omitted).

## Every premise (exact; margin = (rhs−lhs)/|rhs| for ≤,<)

| # | premise | Lean ref | status | lhs | rhs | margin |
|---|---|---|---|---|---|---|
| 1 | cartFitsB H,Nact,P (n=2) | KAM/EffectiveStability/OscillatorChainCheck.lean:103 | ok | all exponent keys have length 2n = 4 (n = 2) |  |  |
| 2 | cartActOnly Nact | KAM/EffectiveStability/OscillatorChainCheck.lean:103 | ok | Nact has b = [] on every monomial |  |  |
| 3 | step1 delta>0 | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 1.475520e-07 | 0 | 1.476e-07 |
| 4 | step1 0<=eps<=1/2 | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 5.000000e-01 | 5.000000e-01 | 0.000e+00 |
| 5 | step1 1<=order | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 5 | 1 | 4.000e+00 |
| 6 | step1 supBound(dq_i chi) <= eps*delta (max over i) | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 4.652305e-08 | 7.377600e-08 | 3.694e-01 |
| 7 | step1 supBound(dp_i chi) <= eps*delta (max over i) | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 7.377573e-08 | 7.377600e-08 | 3.611e-06 |
| 8 | step1 cartEqCheck(cartLieSum chi Q_0 L=5) out | KAM/EffectiveStability/OscillatorChainCheck.lean:69 | ok | 80 monos | 80 monos |  |
| 9 | step2 delta>0 | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 4.400000e-11 | 0 | 4.400e-11 |
| 10 | step2 0<=eps<=1/2 | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 5.000000e-01 | 5.000000e-01 | 0.000e+00 |
| 11 | step2 1<=order | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 2 | 1 | 1.000e+00 |
| 12 | step2 supBound(dq_i chi) <= eps*delta (max over i) | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 2.091097e-11 | 2.200000e-11 | 4.950e-02 |
| 13 | step2 supBound(dp_i chi) <= eps*delta (max over i) | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 2.188409e-11 | 2.200000e-11 | 5.269e-03 |
| 14 | step2 cartEqCheck(cartLieSum chi Q_1 L=2) out | KAM/EffectiveStability/OscillatorChainCheck.lean:69 | ok | 182 monos | 182 monos |  |
| 15 | step3 delta>0 | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 1.000000e-12 | 0 | 1.000e-12 |
| 16 | step3 0<=eps<=1/2 | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 5.000000e-01 | 5.000000e-01 | 0.000e+00 |
| 17 | step3 1<=order | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 2 | 1 | 1.000e+00 |
| 18 | step3 supBound(dq_i chi) <= eps*delta (max over i) | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 6.430446e-14 | 5.000000e-13 | 8.714e-01 |
| 19 | step3 supBound(dp_i chi) <= eps*delta (max over i) | KAM/EffectiveStability/OscillatorChainCheck.lean:52 | ok | 6.098610e-14 | 5.000000e-13 | 8.780e-01 |
| 20 | step3 cartEqCheck(cartLieSum chi Q_2 L=2) out | KAM/EffectiveStability/OscillatorChainCheck.lean:69 | ok | 454 monos | 454 monos |  |
| 21 | final cartEqCheck(Q_m, cartAdd (cartActSubst Nact) P) | KAM/EffectiveStability/OscillatorChainCheck.lean:69 | ok | Q_m 454 monos | Nact(I)+P |  |
| 22 | dom step3 i=0: r + tail_after + delta < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:86 | ok | 1.414300e-04 | 1.614310e-04 | 1.239e-01 |
| 23 | dom step3 i=0: r + dc + tail_after + delta/2 < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:87 | ok | 1.614300e-04 | 1.614310e-04 | 6.191e-06 |
| 24 | dom step3 i=1: r + tail_after + delta < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:86 | ok | 1.414300e-04 | 1.614310e-04 | 1.239e-01 |
| 25 | dom step3 i=1: r + dc + tail_after + delta/2 < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:87 | ok | 1.614300e-04 | 1.614310e-04 | 6.191e-06 |
| 26 | dom step2 i=0: r + tail_after + delta < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:86 | ok | 1.414300e-04 | 1.614310e-04 | 1.239e-01 |
| 27 | dom step2 i=0: r + dc + tail_after + delta/2 < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:87 | ok | 1.614300e-04 | 1.614310e-04 | 6.055e-06 |
| 28 | dom step2 i=1: r + tail_after + delta < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:86 | ok | 1.414300e-04 | 1.614310e-04 | 1.239e-01 |
| 29 | dom step2 i=1: r + dc + tail_after + delta/2 < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:87 | ok | 1.614300e-04 | 1.614310e-04 | 6.055e-06 |
| 30 | dom step1 i=0: r + tail_after + delta < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:86 | ok | 1.415776e-04 | 1.615040e-04 | 1.234e-01 |
| 31 | dom step1 i=0: r + dc + tail_after + delta/2 < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:87 | ok | 1.615038e-04 | 1.615040e-04 | 1.248e-06 |
| 32 | dom step1 i=1: r + tail_after + delta < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:86 | ok | 1.415776e-04 | 1.615040e-04 | 1.234e-01 |
| 33 | dom step1 i=1: r + dc + tail_after + delta/2 < rho | KAM/EffectiveStability/OscillatorChainCheck.lean:87 | ok | 1.615038e-04 | 1.615040e-04 | 1.248e-06 |
| 34 | 0 < dc | KAM/EffectiveStability/OscillatorChainCheck.lean:105 | ok | 2.000000e-05 | 0 | 2.000e-05 |
| 35 | 0 < epsb | KAM/EffectiveStability/OscillatorChainCheck.lean:105 | ok | 1.000000e-12 | 0 | 1.000e-12 |
| 36 | 0 <= T | KAM/EffectiveStability/OscillatorChainCheck.lean:105 | ok | 1.000000e+10 | 0 | 1.000e+10 |
| 37 | j=0: 0 <= r | KAM/EffectiveStability/OscillatorChainCheck.lean:107 | ok | 1.414300e-04 | 0 | 1.414e-04 |
| 38 | j=0: 2(b+epsb) <= r^2 | KAM/EffectiveStability/OscillatorChainCheck.lean:107 | ok | 2.000200e-08 | 2.000244e-08 | 2.224e-05 |
| 39 | j=0: 0 <= eta | KAM/EffectiveStability/OscillatorChainCheck.lean:108 | ok | 1.000000e-19 | 0 | 1.000e-19 |
| 40 | j=0: supBound(bracket(I_j,P)) <= eta - 2 r B/dc   [res=1.401e-21, lieTail=4.338e-20] | KAM/EffectiveStability/OscillatorChainCheck.lean:109-110 | ok | 1.400683e-21 | 5.661880e-20 | 9.753e-01 |
| 41 | j=0: a + T eta < b | KAM/EffectiveStability/OscillatorChainCheck.lean:111 | ok | 7.561000e-09 | 1.000000e-08 | 2.439e-01 |
| 42 | j=1: 0 <= r | KAM/EffectiveStability/OscillatorChainCheck.lean:107 | ok | 1.414300e-04 | 0 | 1.414e-04 |
| 43 | j=1: 2(b+epsb) <= r^2 | KAM/EffectiveStability/OscillatorChainCheck.lean:107 | ok | 2.000200e-08 | 2.000244e-08 | 2.224e-05 |
| 44 | j=1: 0 <= eta | KAM/EffectiveStability/OscillatorChainCheck.lean:108 | ok | 1.000000e-19 | 0 | 1.000e-19 |
| 45 | j=1: supBound(bracket(I_j,P)) <= eta - 2 r B/dc   [res=1.409e-21, lieTail=4.338e-20] | KAM/EffectiveStability/OscillatorChainCheck.lean:109-110 | ok | 1.408669e-21 | 5.661880e-20 | 9.751e-01 |
| 46 | j=1: a + T eta < b | KAM/EffectiveStability/OscillatorChainCheck.lean:111 | ok | 7.561000e-09 | 1.000000e-08 | 2.439e-01 |
| 47 | phys j=0: hs0 0 <= s | KAM/EffectiveStability/OscillatorChainPhysical.lean:171 | ok | 1.131400e-04 | 0 | 1.131e-04 |
| 48 | phys j=0: hs1 2a' <= s^2 | KAM/EffectiveStability/OscillatorChainPhysical.lean:171 | ok | 1.280000e-08 | 1.280066e-08 | 5.153e-05 |
| 49 | phys j=1: hs0 0 <= s | KAM/EffectiveStability/OscillatorChainPhysical.lean:171 | ok | 1.131400e-04 | 0 | 1.131e-04 |
| 50 | phys j=1: hs1 2a' <= s^2 | KAM/EffectiveStability/OscillatorChainPhysical.lean:171 | ok | 1.280000e-08 | 1.280066e-08 | 5.153e-05 |
| 51 | phys hs2 step1 j=0: s + c + delta < rho   (c=0.000e+00) | KAM/EffectiveStability/OscillatorChainPhysical.lean:34 | ok | 1.132876e-04 | 1.615040e-04 | 2.985e-01 |
| 52 | phys hs2 step1 j=1: s + c + delta < rho   (c=0.000e+00) | KAM/EffectiveStability/OscillatorChainPhysical.lean:34 | ok | 1.132876e-04 | 1.615040e-04 | 2.985e-01 |
| 53 | phys hs2 step2 j=0: s + c + delta < rho   (c=7.378e-08) | KAM/EffectiveStability/OscillatorChainPhysical.lean:34 | ok | 1.132138e-04 | 1.614310e-04 | 2.987e-01 |
| 54 | phys hs2 step2 j=1: s + c + delta < rho   (c=7.378e-08) | KAM/EffectiveStability/OscillatorChainPhysical.lean:34 | ok | 1.132138e-04 | 1.614310e-04 | 2.987e-01 |
| 55 | phys hs2 step3 j=0: s + c + delta < rho   (c=7.380e-08) | KAM/EffectiveStability/OscillatorChainPhysical.lean:34 | ok | 1.132138e-04 | 1.614310e-04 | 2.987e-01 |
| 56 | phys hs2 step3 j=1: s + c + delta < rho   (c=7.380e-08) | KAM/EffectiveStability/OscillatorChainPhysical.lean:34 | ok | 1.132138e-04 | 1.614310e-04 | 2.987e-01 |
| 57 | phys j=0: hs3 (s + tail)^2 <= a | KAM/EffectiveStability/OscillatorChainPhysical.lean:172 | **FAIL** | 1.281736e-08 | 6.561000e-09 | -9.536e-01 |
| 58 | phys j=1: hs3 (s + tail)^2 <= a | KAM/EffectiveStability/OscillatorChainPhysical.lean:172 | **FAIL** | 1.281736e-08 | 6.561000e-09 | -9.536e-01 |
| 59 | phys j=0: hd tail(2r+tail) <= d | KAM/EffectiveStability/OscillatorChainPhysical.lean:173 | ok | 2.088009e-11 | 2.090000e-11 | 9.526e-04 |
| 60 | phys j=1: hd tail(2r+tail) <= d | KAM/EffectiveStability/OscillatorChainPhysical.lean:173 | ok | 2.088009e-11 | 2.090000e-11 | 9.526e-04 |
| 61 | d <= 1e-10 | plan 4 | ok | 2.090000e-11 | 1.000000e-10 | 7.910e-01 |
| 62 | conclusion: a + eta T + d < 101e-10 | KAM/EffectiveStability/OscillatorChainPhysical.lean:173 | ok | 7.581900e-09 | 1.010000e-08 | 2.493e-01 |
| 63 | conclusion: 2d + eta T <= 12e-10 | KAM/EffectiveStability/OscillatorChainPhysical.lean:173 | ok | 1.041800e-09 | 1.200000e-09 | 1.318e-01 |

## Structural finding (hs1 vs hs3)

`oscillatorChain_physical` takes box radii `s` with `hs1 : 2a′ ≤ s²` (so each coordinate |q_j|,|p_j| ≤ s) and requires `hs3 : (s + tail)² ≤ a`. For a′ = (1/12500)² = 6.4·10⁻⁹ this forces s² ≥ 1.28·10⁻⁸, hence a ≥ 1.28·10⁻⁸ — **greater than the literal chart bound a = (81·10⁻⁶)² = 6.561·10⁻⁹ and even than the final bound 1.01·10⁻⁸**. So the literal acceptance target cannot be reached through `oscillatorChain_physical` as stated, for any producer data: the factor 2 is lost in passing from the action ball {(q²+p²)/2 ≤ a′} to the coordinate box |q|,|p| ≤ s. B3-READY ("`(s+tail)² ≤ a` requires tail ≤ 1·10⁻⁶") assumed s = √a′ (the Euclidean radius), which the Lean hypotheses do not allow.
* needed by the box version: (s+tail)² = 1.281736e-08 vs a = 6.561000e-09.
* with the Euclidean (circle) estimate the literal target WOULD hold: (√a′ + tail)² = 6.411813e-09 ≤ a = 6.561000e-09 (yes); a Lean refinement of hs1/hs3 to the circle (displacement ≤ √2·tail per action plane) removes the conflict. Not done here (no Lean edits allowed).
* box-version variant (NOT the acceptance target, a′ reduced; everything else unchanged): with a = 8.9·10⁻⁹ (so a + ηT = 9.9·10⁻⁹ < b and a + ηT + d < 1.01·10⁻⁸), s = 9.426601e-05, the admissible physical box is a′ ≤ 4.443041e-09, i.e. √a′ ≈ 6.6656e-05 instead of 8.0000e-05 (a factor 1.200 smaller).

## Resource use of this run

* normal-form construction CPU 0.13 s; whole script CPU 0.29 s; peak RSS 14.6 MiB (script-measured; the systemd/`time -v` figures are in `E1-run.log`).
