# B3 readiness: the Hénon–Heiles instance, ready to start when the owner says go

Status (2026-11-03, kam-b1, overnight D71): **plan only. Nothing has been run.** B3 stays OFF until the owner approves the
pilot target (plan §4 "A first instance with literal acceptance criteria", §8 item 2). The checker side is complete on main
(B2, B4): `checkOscChain_sound` and `oscillatorChain_physical`. One prerequisite Lean package remains (step 0 below).

## Target theorem (plan §4, exact literals)

Model (CL20 Appendix B, **not** its Table-1 model): `H(q,p) = I₁ − (√2/2) I₂ + q₁² q₂ − q₂³/3`, with `I_j = (q_j² + p_j²)/2`.
The literal statement, to be frozen only if the owner approves its exact text:

```text
henonHeiles_confinement : ∀ z₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ),
  (∀ j, oscillatorAction z₀.2 z₀.1 j ≤ (1/12500)^2) →
  ∃ T₁ > 10^10, ∃ z, z 0 = z₀ ∧ (Hamiltonian equation of H on Ioo (−T₁) T₁) ∧ (uniqueness as in B1-E) ∧
    ∀ t, |t| ≤ 10^10 → ∀ j, oscillatorAction (z t).2 (z t).1 j < 101/10^10 ∧
      |oscillatorAction (z t).2 (z t).1 j − oscillatorAction z₀.2 z₀.1 j| ≤ 12/10^10
```

It follows from `oscillatorChain_physical` with the plan's chart literals:
- `a_j = (81/10⁶)²`, `b_j = 10⁻⁸`, `η_j ≤ 10⁻¹⁹`, `T = 10¹⁰`, `d_j ≤ 10⁻¹⁰`.
- Then `a + ηT + d ≤ 7.661·10⁻⁹ < 101·10⁻¹⁰` and `2d + ηT ≤ 1.2·10⁻⁹ = 12·10⁻¹⁰`.
- Physical box `a' = (1/12500)²`: `(s + tail)² ≤ a` requires `tail ≤ 1·10⁻⁶`.
  **Deviation (11-03 09:21, OD-B18):** wrong as stated. `oscillatorChain_physical`'s `hs1 : 2a′ ≤ s²` (coordinate
  box) and `hs3 : (s+tail)² ≤ a` force a ≥ 2a′ > (81·10⁻⁶)², for any data. Fix: the disc variant
  `oscillatorChain_physical_disc` (`a′ ≤ σ²`, `(σ+tail)² ≤ a`); literal target then holds with tail ≈ 7.4·10⁻⁸.
- `d ≥ tail(2r + tail)` with `r ≥ √(2(b+εb)) ≈ 1.415·10⁻⁴` requires `tail ≲ 3.5·10⁻⁷`.

Here `tail = Σ ε_k δ_k` is the chain displacement.

## Step 0: prerequisite Lean package (OD-B16)

`H` has the coefficient `√2/2`, and the frequency ratio `1 : √2/2` is essential, so no rational rescaling removes it. The
landed `CartPoly` has exact ℚ coefficients, so **an exact ℚ(√2) coefficient layer is needed first**:
- coefficients `a + b√2` with `a b : ℚ`, exact ring operations, and decidable equality on pairs;
- `cartEval` into ℝ through `a + b·Real.sqrt 2`;
- majorants through a rational `√2 ≤ 141422/100000`, with absolute value `|a + b√2| ≤ |a| + |b|·1.41422`;
- either generalizing `Poly/*` over a coefficient class, or duplicating it as `Poly2/*`, plus the chain checker over it.

Estimate: 0.8–1.5k Lean lines, two packages, about 2–4 prover-hours with the present pipeline, and audited like B2.
Alternative: a ℚ-coefficient HH variant with a rational frequency ratio. It is rejected, because it is resonant and
changes the model.

## Step 1: producer (untrusted; Python with exact arithmetic over ℚ(√2), plan §6.2 E0/E1)

1. Reuse the plan's E0 scout:
   - solve the degree-3 and degree-4 homological equations over ℚ(√2), real Cartesian coordinates;
   - generators `χ₃` (5 monomials) and `χ₄` (8 monomials);
   - normal form `N₄ = (13√2/28) I₁² − (√2 + 4/7) I₁I₂ + (5√2/12) I₂²`, as an action-only polynomial.
   - Measured: 1.6 CPU s, 0.65 GiB.
2. Build the `OscChainCert` data:
   - `steps = [χ₃-step, χ₄-step]`, each with its Lie order `L_k`;
   - exact intermediate polynomials `Q_k = LieSum(χ_k, Q_{k-1}, L_k)`, truncated, with the discarded terms moved into the
     final residual `P`;
   - per-step radii `ρ_k, δ_k, ε_k`, chosen so that `Σ ε_k δ_k ≤ 3·10⁻⁷`;
   - Cauchy radius `δc`, action radii `r_j`, and the B1-E data `a, b, η, εb, T`.
   - All numbers are exact rationals or ℚ(√2) values, so certificate replay is exact.
3. **E1 go/no-go:** evaluate `checkOscChain` in Python with exact rationals before any Lean run.
   - **Go** if every check passes with `η ≤ 10⁻¹⁹`.
   - **No-go** otherwise: report which contribution fails. It is either the residual majorant `supBound({I_j,P})` or the
     Lie tails `2 r_j Σ B_k/(L_k! δc)`. Never silently shrink the box.
   - Expected bottleneck: the degree-5 residual at radius `r ≈ 1.4·10⁻⁴` gives `r⁵ ≈ 5.6·10⁻²⁰` times coefficient
     sums. This is borderline. A third step (`χ₅`, degree-5 normalization, the plan's "step three") or a slightly smaller
     `b` may be needed. Both are producer choices, and the literal acceptance target stays fixed.
   - Budget: under 1 CPU-hour and 3.5 GB (plan §6.2).

## Step 2: kernel replay and the literal theorem (Lean)

- **Certificate as a Lean literal:** `def hhCert : OscChainCert 2 := …`, tens to low hundreds of monomials with large exact
  rationals.
- **Check:** `hhCert_check : checkOscChain hhCert = true := by decide +kernel`. Expected seconds to minutes. Measure it
  (plan §6.2 E2): stop above 6 GB, at a default-heartbeat failure, or after 45 CPU min, and split into shards if
  needed. The smoke certificates checked in 19–78 ms.
- **Assembly:** `henonHeiles_confinement` from `oscillatorChain_physical` (via `checkOscChain_sound`) plus the arithmetic
  above (`norm_num`), and the identification of `cartEval H` with the literal HH formula.
- **Placement:** an opt-in application library (`KAMHenonHeiles`, AGENTS rule 8 / D51), built only through
  `scripts/prebuild_heavy.py --lib`. It is not in core.
- **Estimate:** 0.5–1k Lean lines; replay CPU under 1 h expected (plan §4 row "B3": 5–30 replay CPU-h was the conservative
  allocation).

## What the owner needs to approve

1. The pilot target: exact model, box, time and bounds above (§8 item 2).
2. OD-B16: build the ℚ(√2) coefficient layer (default) rather than change the model.
3. Whether to freeze `henonHeiles_confinement` after it is proved, as the plan §2.4 "one literal application theorem".
