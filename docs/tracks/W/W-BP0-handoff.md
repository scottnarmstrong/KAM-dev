# Handoff: W-BP0 (track W, blueprint Part 0 and milestone W0)

(Copied from the writer's working handoff. Note from delta audit 2: the rebuilt blueprint PDF *was* committed, in dbec57c.)

Branch `w`, commit `fd2c7ec`. Source and design work only: no `.lean` file, manifest, graph, `sources.json` or existing
blueprint was touched. Nothing is frozen or approved.

## Files
- `blueprint-W/preamble.tex`, `blueprint.tex`, `.gitignore`, `blueprint.pdf` (12 pp., latexmk -pdf: 0 errors,
  0 undefined references, 0 overfull boxes)
- `blueprint-W/parts/w0-conventions.tex`: PDE, basis, `ℓ^{a,p}`, two-sided spaces, reconstruction `U_m,V_m`, `H`,
  `G_q`, equations, complex coordinates, actions/angles, period-one convention, table vs P96-W.
- `blueprint-W/parts/w0-normalization.tex`: milestone W0, deliverables (a)–(f), ledger.
- `blueprint-W/parts/w-headline.tex`: W-NLW2, PROPOSED, with all definitions.
- `blueprint-W/PLAN.md`: W0–W8, W0 nodes (written) and W1 nodes (PLANNED) with dependency edges; normalization rulings.
- `scripts/wave/w0_checks.py`: sympy/numpy checks, recorded output at the end of the file.
- `docs/tracks/W/errata-check-W0.md`: errata verdicts.

## Approach and results (labels in blueprint-W)
- (a) `bpW:w0n:pde-equiv`: coefficient system ⇔ classical PDE (both directions). Force identity
  `U_m(q)³ = Σ √λ_l G_q(q)_l φ_l` proved. **Proved**; external fact: `L²` completeness of sines.
- (b) `bpW:w0n:cubic-bound`: `G_q = T(q,q,q)` with `T` a bounded trilinear map `ℓ^{a,p} → ℓ^{a,p+1}` (any `a ≥ 0`, `p ≥ ½`).
  For `a = p = 1`: `‖G_q(q)‖_{1,2} ≤ C_m ‖q‖³_{1,1}` with `C_m = 8(1+2ζ(3))/π ≈ 8.67`, **uniform in m > 0**.
  Analyticity comes from multilinearity, so no "componentwise analytic + bounded" principle is needed. **Proved**, with the
  explicit algebra constant `K_s = 2^s (1+2ζ(2s))^{1/2}` (`bpW:w0n:algebra`).
- (c) `bpW:w0n:quartic-coeff`: `g_ijkl = (1/2π)([i+l=j+k]+[i+k=j+l]+[i+j=k+l] − [i=j+k+l] − … )`, plus a signed form
  used in (b). **Proved**.
- (d) `bpW:w0n:AB`: `A_ii = 9/(8πλ_i²)`, `A_12 = B_ji = 3/(2πλ_iλ_j)`, `⟨G⟩ = (3/16π)(4(Σ I/λ)² − Σ I²/λ²)`.
  New lemma `bpW:w0n:nonres`: for every `m > 0` and all indices, a quartic monomial with `g ≠ 0` is resonant only if it is
  `|z_a|²|z_b|²`. So resonant projection = angle average. `bpW:w0n:formal-birkhoff`: formal Lie transform (**proved
  formally**). The analytic map and remainder are W3 (cites P96-W Main Prop. and Lemma 4).
- (e) `bpW:w0n:nondeg`: `det A = −63/(64π²(1+m)(4+m))`, (A₂) and (A₃) for `J = {1,2}` and every `m > 0`. Self-contained
  proof specializing P96-W Lemma 6. **Proved**. Remark `bpW:w0n:kappa`: `κ = 2` unchanged.
- (f) `bpW:w0n:duffing`: Lindstedt shift `3εa²/(8λ)`, `ε = 3/(2π)`, equals `A_jj I_j`. **Proved**. Numerically, the ratio
  of the integrated shift to `A_11 I` goes to 1 (0.99976, 0.99987, 0.99998 at the smallest amplitude for m = 0.1, 1, 10).
- Cited, not proved here: P96-W Lemma 4 (quantitative divisors), analytic Birkhoff map (W3).
- Source-proof expansion (not a gap, Revision 1): P96-W Lemma 1. SOURCE_GAP marks: P96-W p. 280 `√2` (N-1).

## Errata verdicts (details in docs/tracks/W/errata-check-W0.md)
- **E-PDE-W-1: CONFIRMED, MODIFIED.** The error is two separate factor-4 slips on p. 282. Line 1 lacks the `¼` from
  `q = (z+z̄)/√2`, and line 2 (`Σ' G w⁴`) drops the `¼` of (9). The p. 284 count is right for the printed line 2, and
  correct values = printed/16. The error propagates to pp. 290–291 (`A`, `B`, `v`). Lemmas 5–6 are scale-invariant, so
  they still hold.
- **E-PDE-W-2: CONFIRMED, MODIFIED.** The recovery on p. 290 needs `√2`. The `I = ½|z|²` of p. 287 conflicts with
  `α = λ` (p. 290) and with the form on p. 281. New sub-items: under p. 287's `I`, `A = Ḡ` needs a factor 4; p. 276 uses a
  third convention `I = q²+p²`; and the flow `e^{iωt}` is time-reversed relative to `ż = −iλz`.
- **E-PDE-KP-1: CONFIRMED.** Under KP96's own form `(i/2)dq∧dq̄`, the action is `I = |q|²/2`, so `A = 4Ḡ = (4−δ)/π`.
  Remark 2 on p. 5 inherits the error.
- **E-PDE-KP-2: CONFIRMED** as a premise gap: `m = −9`, `l = e_3` gives `λ_3 = 0`; more generally `m = −a²` or
  `m = −(a²+b²)/2`. A gauge repair is plausible but not certified; it does not affect track W.
- **New:** N-1 P96-W p. 280: `‖Sq‖_{a,s+½} ≤ ‖q‖` is false for every `m > 0` (operator norm exactly `√2`; corrected in Revision 1, W-A1).
  N-2 KP96 p. 13: same `√2` pattern. N-3 P96-W p. 282: typographical parenthesization of `Ḡ_ij`.
- Deviations introduced: pure cubic, `J = {1,2}`, `a = p = 1`, period-one angles, standard actions `|z|²`, the
  normalization repair, and a Borel density-one set without stability or Whitney regularity (already in the report's
  §4 list).

## Checks run
- `python3 scripts/wave/w0_checks.py` → exit 0, ALL CHECKS PASS (output below).
- `latexmk -pdf blueprint.tex` in blueprint-W → rc 0. `grep undefined|Overfull|^! blueprint.log` → empty.
- `python3 -IB scripts/check_lean_modules.py --root .` → PASS (417 Lean files). The full `scripts/lint_sources.sh` was
  not run: its `abi_hashes` stage invokes Lean, and this package touched no Lean. No `#print axioms` (no Lean results).
- `git diff --cached --check` → clean.

## Uncertainties / open questions for the owner
1. Adopt the normalization rulings in `blueprint-W/PLAN.md` as track-W conventions?
2. The proof of (A₃) and the nonresonance lemma are new (not copied); they deserve an independent audit.
3. The KP96 journal printing has not been compared with author version 2.1.
4. `bpW:w0n:pde-equiv(i)` assumes `C¹` into `ℓ^{1,0}` and continuity into `ℓ^{1,1}`. W2 must verify that the KAM torus
   orbit supplies this (the source works with real-analytic curves).

## Script output
```
== 1. quartic sine integrals ==
[PASS] closed form of g_ijkl vs exact symbolic integral, sorted (i,j,k,l) in {1..3}^4: mismatches []
[PASS] closed form vs exact quadrature for all ordered (i,j,k,l) in {1..12}^4: max error 1.7e-16
[PASS] g_iiii = 3/(2 pi)
[PASS] g_iijj = 1/pi (i != j)
[PASS] g_1113 = -1/(2 pi) (a non-resonant quartic term)
[PASS] selection rule: g_ijkl = 0 unless +-i+-j+-k+-l = 0 (indices <= 8)
[PASS] P96-W (11) agrees with g/(sqrt(lambda^4)) for i,j <= 6
== 2. coordinates ==
[PASS] (phi, I) -> (q,p) = (sqrt(2I) cos phi, -sqrt(2I) sin phi) has Jacobian det 1, i.e. dq^dp = dphi^dI: det = 1
[PASS] I = (q^2+p^2)/2 on that chart
[PASS] z = (q+ip)/sqrt2 = sqrt(I) e^{-i phi}, |z|^2 = I
[PASS] q' = lam p, p' = -lam q  =>  z' = -i lam z
[PASS] i dz^dzbar = dq^dp: i*det = 1
== 3. averaged quartic term: twist A and coupling B ==
[PASS] <G>(I) = 1/2 sum_{i,j} A_ij I_i I_j with A_ii = 9/(8 pi lam_i^2), A_ij = 3/(2 pi lam_i lam_j) (modes 1..4)
   A = Matrix([[9/(8*pi*(m + 1)), 3/(2*pi*sqrt(m**2 + 5*m + 4))], [3/(2*pi*sqrt(m**2 + 5*m + 4)), 9/(8*pi*(m + 4))]])
   B (rows j = 3..4, cols i = 1,2) = Matrix([[3/(2*pi*sqrt(m**2 + 10*m + 9)), 3/(2*pi*sqrt(m**2 + 13*m + 36))], [3/(2*pi*sqrt(m**2 + 17*m + 16)), 3/(2*pi*sqrt(m**2 + 20*m + 64))]])
[PASS] B_ji = 3/(2 pi lam_j lam_i) for normal j, tangential i = coefficient of I_i Z_j in <G>
   det A = -63/(64*pi**2*(m + 1)*(m + 4))
[PASS] det A = -63/(64 pi^2 (1+m)(4+m))
[PASS] A = 3/(8 pi) D (4 * 11^T - Id) D
[PASS] det A has no zero for m > 0 (numerator constant, denominator positive)
== 4. P96-W printed quartic chain (E-PDE-W-1) ==
[PASS] printed Gbar_ij / A_ij = 16 for all i, j: ratios {16}
[PASS] q^4 with q = (z+zbar)/sqrt2 has |z|^4-coefficient 6/4 (so (1/4) G q^4 -> (1/16) G (z+zbar)^4)
[PASS] p.284 counting 24 G_iijj, 12 G_iiii reproduces the printed Gbar
[PASS] with the correct prefactor 1/16: (1/16)*(24 G_iijj, 12 G_iiii) = A
[PASS] p.287 convention I = |z|^2/2 would turn Gbar = 1/2 sum Gbar |z|^2|z|^2 into 1/2 <(4 Gbar) I, I>
== 5. nondegeneracy for J = {1,2} ==
[PASS] (A3) affine non-identity, m = 0.1: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 1.181e-01
[PASS] (A3) affine non-identity, m = 1.0: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 1.044e-01
[PASS] (A3) affine non-identity, m = 10.0: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 2.304e-02
[PASS] (A3) affine non-identity, m = 43.0: min over |k_i|<=12, normal modes 3..40, of max(|const|,|linear|): 1.095e-02
[PASS] (A2) <l,beta> != 0: min |lam_a +- lam_b|, |lam_a| over 3<=a<b<=200, m = 0.1
== 6. quartic nonresonance: sigma.lambda = 0 with g != 0 only for pairings ==
[PASS] m = 0.01: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.105e-07
[PASS] m = 0.1: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.104e-06
[PASS] m = 1.0: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.098e-05
[PASS] m = 10.0: min |sum sigma_t lam_(i_t)| over non-trivial sign patterns, indices <= 30, g != 0: 4.033e-04
== 7. one-mode Duffing consistency ==
[PASS] Lindstedt shift with eps = g_jjjj = 3/(2pi) equals A_jj I_j
[PASS] m = 0.1, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16): 0.99623 0.99905 0.99976
[PASS] m = 1.0, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16): 0.99792 0.99948 0.99987
[PASS] m = 10.0, mode 1: (omega_numeric - lam) / (A_11 I) -> 1 as amplitude halves (printed P96-W value would give 1/16): 0.99962 0.99991 0.99998
== 8. cubic gradient bound ||G_q(q)||_{1,2} <= C ||q||_{1,1}^3,  C = 8(1+2 zeta(3))/pi ==
   C = 8.668505
[PASS] max over 60 random trials of ||G_q||_{1,2} / ||q||_{1,1}^3 <= C: max ratio 2.9836
[PASS] gradient of 1/4 int U^4 = trilinear sum with g_ijkl (quadrature vs closed form)
== 9. errata spot checks ==
[PASS] P96-W p.280: ||S e_1||^2_{0,1/2} = 2/sqrt(1+m) > 1 = ||e_1||^2_{0,0} at m = 1 (printed inequality fails): 1.4142
[PASS] E-PDE-KP-2: NLS lambda_3 = 9 + m = 0 at m = -9
[PASS] E-PDE-KP-1: KP96 (5)-(6) dynamics give omega = lam + 4 Gbar I with I = |q|^2/2
[PASS] KP96 Lemma 4 Gbar_ij = (4 - delta_ij)/(4 pi) is the resonant part of (7)

ALL CHECKS PASS
```

## Revision 1 (audit W-BP0-audit-1)
- **W-A1** fixed: `docs/tracks/W/errata-check-W0.md:136–141` (sup_j j/λ_j = 1; operator norm exactly √2 for every m > 0;
  printed bound fails for every m > 0; N-1 verdict kept); `blueprint-W/parts/w0-normalization.tex:159–162`; this handoff line 49.
- **W-A2** fixed: `blueprint-W/parts/w-headline.tex:7–9` (called "the D30 first headline (a declared weakening of P96-W's
  Main Theorem for J = {1,2})"), `:61–64` new conclusion (6) family injectivity, `:79–81` (proved in W8, cites P96-W
  pp. 272–273, 288–289), `:91–101` Remark "Declared weakenings" (Lipschitz Cantor-manifold regularity deferred with
  Whitney regularity and stability, D30 Q3). `blueprint-W/PLAN.md:43,95–98` (W8 proves injectivity).
- **W-A3** fixed: `blueprint-W/PLAN.md:77` (`r ≥ 0`; general `(1+m)^{max(r,0)/2}`), `:79` (`s > 1/2` in w1:young),
  `:81` (`a ≥ 0, p ≥ 1/2` for the trilinear theorem). (`w0-normalization.tex:26` already had `r ≥ 0`.)
- **W-A4** fixed: `scripts/wave/w0_checks.py:10–15` header. Working command: `python3 scripts/wave/w0_checks.py` (from repo
  root) → exit 0, `ALL CHECKS PASS` (rerun 2026-10-28; recorded output unchanged). `python3 -I …` still fails with
  `ModuleNotFoundError: No module named 'sympy'` (sympy only in user site, excluded by -I); the header gives the
  isolated fallback that appends the user site.
- **W-A5** fixed: `blueprint-W/parts/w0-normalization.tex:211–215` (Lemma 1 relabelled "expansion/strengthening of the
  source proof", no longer SOURCE_GAP), ledger `:426–427`; `blueprint-W/PLAN.md:67–68`.
- **W-S1 → N-4 CONFIRMED** (`errata-check-W0.md:152–157`): P96-W p. 278 second line of u_tt display prints `+λ_j²q_j`;
  (6)–(7) give `−λ_j²q_j`; next line already `−Au`. Verified on 200-dpi image (PDF p. 11).
- **W-S2 → N-5 CONFIRMED** (`errata-check-W0.md:159–166`): KP96 p. 13 `∂G/∂q̄_j = ∫ f(|u|²)uφ_j` misses factor ½
  given (5) `G = ½∫g(|u|²)`; p. 11 Lemma 1 computation is consistent with the correct value. Verified on 200-dpi image.
- Checks: `latexmk -pdf blueprint.tex` rc 0, 0 errors, 0 undefined refs, 13 pages (the earlier "12 pp." was wrong).
  Script rerun above. Recompiled PDF not committed (per brief: never PDFs). No Lean touched; no frozen files.
- Ledger request for orchestrator: add N-4, N-5; amend N-1 description.
