# Track W, W0: independent check of the candidate PDE errata

Package W-BP0, 28 October 2026. This note re-derives, from each source's own definitions, the four candidate errata of
[`docs/explorations/pde-kam-and-leapfrogging.md`](../../explorations/pde-kam-and-leapfrogging.md) §4, trying to refute
each. It records verdicts for the orchestrator; it does not edit `docs/errata/ledger.json`. Every scanned formula below
was read on a page image (P96-W at 100–110 dpi). KP96 is the born-digital author version 2.1; its pages were also read
as images. Mechanical checks are in [`scripts/wave/w0_checks.py`](../../../scripts/wave/w0_checks.py), sections 4 and 9.

Locators: P96-W printed page = PDF page + 267. KP96 = author pages.

Conventions used for the re-derivation (fixed in `blueprint-W/parts/w0-conventions.tex`): `q_j = sqrt(λ_j) x_j`,
`p_j = y_j / sqrt(λ_j)` for `u = Σ x_j φ_j`, `u_t = Σ y_j φ_j`; `H = ½ Σ λ_j (q_j² + p_j²) + ¼ ∫ u⁴`; Hamilton's equations
`q̇ = ∂H/∂p`, `ṗ = −∂H/∂q` (P96-W pp. 277, 280 use the same).

## Summary

| ID | Location | Verdict |
|---|---|---|
| E-PDE-W-1 | P96-W p. 282 (expansion), p. 284 (`Ḡ_ij`), pp. 290–291 (`A`, `B`, `v`) | **CONFIRMED, MODIFIED** (localized to two separate factor-4 slips) |
| E-PDE-W-2 | P96-W p. 290 (recovery), p. 287 vs pp. 281/290 (actions), p. 287/289 (rotation sign) | **CONFIRMED, MODIFIED** (one more sub-item: `A = Ḡ` on p. 290 needs `4Ḡ` under p. 287's `I`) |
| E-PDE-KP-1 | KP96 p. 16 (and p. 5, Remark 2) | **CONFIRMED** |
| E-PDE-KP-2 | KP96 Theorem 1 p. 5 vs Lemma 6 p. 20 | **CONFIRMED** (premise gap; a gauge repair is plausible but not certified) |
| N-1 (new) | P96-W p. 280, proof of Lemma 3 | new, constants only |
| N-2 (new) | KP96 p. 13, proof of Lemma 3 | new, constants only |
| N-3 (new) | P96-W p. 282 (Main Proposition) | new, typographical |

None of these affects the qualitative existence theorem for `J = {1,2}`, `m > 0`: every nondegeneracy condition used
is invariant under a common positive rescaling of `(A, B)` and of `I`, and time reversal maps solutions to solutions
(`H` is even in `p`). They do affect every printed constant, frequency shift, and the action/amplitude dictionary.

## E-PDE-W-1: quartic normalization in the Birkhoff calculation

**Printed.** (9), p. 280: `G = ¼ ∫ |u|⁴ dx = ¼ Σ G_ijkl q_i q_j q_k q_l`; (10), p. 281:
`G_ijkl = (λ_iλ_jλ_kλ_l)^{-1/2} ∫ φ_iφ_jφ_kφ_l`; (11): `G_iijj = (1/2π)(2+δ_ij)/(λ_iλ_j)`. p. 281:
`z_j = (q_j + i p_j)/√2`. p. 282, proof of the Main Proposition:
"`H = Σ λ_j z_j z̄_j + ¼ Σ G_ijkl (z_i + z̄_i)···(z_l + z̄_l) = Σ λ_j w_j w_{−j} + Σ' G_ijkl w_i w_j w_k w_l`".
p. 282 statement and p. 284: `Ḡ_ij = 24 G_iijj = (24/π)(1/λ_iλ_j)` for `i ≠ j`, `12 G_iiii = (18/π)(1/λ_iλ_j)` for
`i = j`, `Ḡ = ½ Σ Ḡ_ij |z_i|²|z_j|²`.

**Re-derivation.** (10)–(11) are correct: `∫φ_i²φ_j² = 1/π` (`i≠j`), `∫φ_i⁴ = 3/(2π)` (blueprint Lemma
`bpW:w0n:quartic-coeff`; script §1). Since `q_j = (z_j + z̄_j)/√2`, `q_iq_jq_kq_l = ¼ Π(z+z̄)`, so the first line must
read `(1/16) Σ G_ijkl (z_i+z̄_i)···`. The second line, with `w_{±j}` and `G_{i...l} = G_{|i|...|l|}`, is an identity
`Σ_{i,j,k,l ≥ 1} G Π(w_i + w_{−i}) = Σ' G w w w w`; so whatever prefactor the first line has, the second must keep. The
printed second line has none. The multiplicity count of p. 284 is correct *for the printed second line*: the
coefficient of `|z_i|⁴` in `Σ' G w⁴` is `C(4,2) G_iiii = 6 G_iiii`, giving `Ḡ_ii = 12 G_iiii`, and that of
`|z_i|²|z_j|²` is `4! G_iijj = 24 G_iijj`. With the correct `1/16`, the same count gives
`Ḡ_ii = (3/4) G_iiii = 9/(8πλ_i²)` and `Ḡ_ij = (3/2) G_iijj = 3/(2πλ_iλ_j)`.

Independent cross-check by averaging (blueprint Theorem `bpW:w0n:AB`): with `q = √(2I) cos φ`, `⟨q⁴⟩ = 3I²/2`,
`⟨q_i²q_j²⟩ = I_iI_j`, so `⟨G⟩ = (3/16π)(4(Σ I_j/λ_j)² − Σ I_j²/λ_j²)`; the coefficients of `½⟨AI,I⟩` are the ones
above. One-mode Duffing check: the Lindstedt shift of `ẍ + λ²x + (3/2π)x³ = 0` is `9I/(8πλ²)` with `I = λa²/2`, and a
numerical integration reproduces it to 4–5 digits (script §7); the printed value predicts a shift 16 times larger.

**Refutation attempts.** (i) Could P96-W's `I` or `z` differ so that `16` is absorbed? No: `Ḡ` is written in `|z|²` with
the p. 281 `z`, and the comparison above is made in exactly those variables. (ii) Could `Σ'` carry an implicit
normalization? It is defined on p. 282 only as the sum over all nonzero integers, with no weight. (iii) Could `G`
in (9) be meant without the `¼`? (9) displays `¼` on both sides, consistent with `g(u) = u⁴/4` and (8).

**Verdict: CONFIRMED, MODIFIED.** The report's "requires 1/16 in both the expanded polynomial and the signed-index sum"
is correct; the precise localization is two independent slips: line 1 lacks the `(1/√2)⁴ = ¼` from the coordinate
change, and line 2 drops the `¼` of (9). The defect propagates unchanged to p. 290 (`A = (Ḡ_ij)_{i,j≤n}`,
`B = (Ḡ_ij)_{j≤n<i}`) and p. 291 (`B_ij = Ḡ_ij = 24/π · λ_i^{-1}λ_j^{-1}`, `v = (24/π)(λ_1^{-1}, ..., λ_n^{-1})`).
Correct values: `A_ii = 9/(8πλ_i²)`, `A_ij = B_ji = 3/(2πλ_iλ_j)`, `v = (3/2π)(λ_1^{-1}, ...)`. Consequences: Lemmas 5–6
(pp. 291–293) are scale invariant and remain valid (their proofs multiply `A` by `π/6`, which becomes `8π/3`); the
asymptotic exponent `κ = 2` (p. 291) is unchanged.

## E-PDE-W-2: real/complex recovery, actions, rotation sign

**Printed.** p. 281: `z_j = (q_j + i p_j)/√2`, symplectic form `i Σ dz_j ∧ dz̄_j`, `H = Σ λ_j |z_j|² + ...`. p. 287:
`I = ½(|z_1|², ..., |z_n|²)`, `Z = ½(|z_{n+1}|², ...)`, `Λ = ⟨α, I⟩ + ⟨β, Z⟩`, `Q = ½⟨AI, I⟩ + ⟨BI, Z⟩`, equations of
motion `ż̃_j = i(α + AI + Bᵀz)_j z̃_j`, tori `{|z̃_j|² = 2I_j}`. p. 289 Remark 1 and p. 290: flows
`Ψ(e^{iω(I)t} v₀)`. p. 290: "Their real imaginary parts, `q = Re z` and `p = Im z`, solve the equations of motion";
`α = (λ_1, ..., λ_n)`, `A = (Ḡ_ij)`. p. 276 (introduction, heuristic): `H = ½ Σ λ_j I_j + Σ A_ij I_i I_j + ...` with
`I_j = q_j² + p_j²`.

**Re-derivation.** (a) From p. 281, `q = √2 Re z`, `p = √2 Im z`; p. 290's `q = Re z`, `p = Im z` is off by `√2`.
(b) `i dz ∧ dz̄ = dq ∧ dp` (checked, script §2), so the canonical action of mode `j` is `(q_j² + p_j²)/2 = |z_j|²`,
and `Λ = Σ λ_j |z_j|² = ⟨λ, |z|²⟩`. With p. 287's `I = ½|z|²`, `Λ = ⟨2λ, I⟩`, contradicting `α = λ` on p. 290. (c)
New sub-item: with `I = ½|z|²`, `Ḡ = ½ Σ Ḡ_ij |z_i|²|z_j|² = ½⟨(4Ḡ) I, I⟩`, so p. 290's `A = Ḡ` also needs a factor 4
under p. 287's convention (the same slip as E-PDE-KP-1; independent of the factor 16 above). (d) p. 276 uses a third
normalization `I_j = q_j² + p_j²` (where `½ Σ λ_j I_j` is right). (e) Rotation sign: the source's own field (p. 280,
`X_G = Σ(∂_p G ∂_q − ∂_q G ∂_p)`) gives `q̇ = λp`, `ṗ = −λq`, hence `ż = −iλz`, whereas pp. 287–290 use `ż = iωz`, i.e. the
time-reversed flow.

**Refutation attempts.** Could p. 287 belong to the abstract Cantor Manifold Theorem with its own coordinates? The
section opens "In a neighbourhood of the origin in `ℓ^{a,s}` we consider `H = Λ + Q + R`" in the same `z`, and p. 290
applies it with `α = λ` without a coordinate change; KP96 p. 16 has the same `I = ½|q|²` but there the symplectic form
is `(i/2) Σ dq ∧ dq̄` and `Λ = ½ Σ λ |q|²`, so that convention is consistent in KP96 and was carried into P96-W without
the factor change. The `√2` in (a) cannot be absorbed: p. 290 refers back to (8) "in real coordinates".

**Verdict: CONFIRMED, MODIFIED** (sub-items (c), (d) added). Harmless for existence (scale invariance; `H(q,−p) = H(q,p)`
makes time reversal a symmetry, mapping `z ↦ z̄`), but the action normalization, frequency shift `AI`, and the
recovery map must be taken from the blueprint, not from P96-W.

## E-PDE-KP-1: KP96 author version, normal-form rewrite

**Printed.** KP96 (5), p. 11: `H = ½ Σ λ_j |q_j|² + ½ ∫ g(|Sq|²)`, symplectic structure `(i/2) Σ dq_j ∧ dq̄_j`, (6)
`q̇_j = 2i ∂H/∂q̄_j`. (7), p. 13: `G = ¼ ∫ |u|⁴ = ¼ Σ G_ijkl q_i q_j q̄_k q̄_l`, `G_ijij = (2 + δ_ij)/(2π)`. Lemma 4,
p. 14: `Ḡ = ½ Σ Ḡ_ij |q_i|²|q_j|²`, `Ḡ_ij = (4 − δ_ij)/(4π)`. p. 16: `H∘Γ = ⟨λ, I⟩ + ½⟨AI, I⟩ + K`,
`I_j = ½|q_j|²`, `A_ij = Ḡ_ij`. p. 5, Remark 2: `ω(I) = λ_J + AI + O(‖I‖²)`, `A_ij = (4 − δ_ij)/(4π)`.

**Re-derivation.** Lemma 4 is correct: the resonant part of (7) is `¼(Σ (3/2π)|q_i|⁴ + Σ_{i≠j} (2/π)|q_i|²|q_j|²)`
(two orderings `(i,j,i,j), (i,j,j,i)` per ordered pair), i.e. `Ḡ_ii = 3/(4π)`, `Ḡ_ij = 1/π`. With `(i/2) dq ∧ dq̄ = dx ∧ dy`
(`q = x + iy`) the canonical action is `|q|²/2`, consistent with `⟨λ, I⟩ = ½ Σ λ |q|²`. Then
`½ Σ Ḡ_ij |q_i|²|q_j|² = ½ Σ Ḡ_ij (2I_i)(2I_j) = ½⟨(4Ḡ) I, I⟩`. Directly from (6):
`q̇_k = i(λ_k + 2 Σ_j Ḡ_kj |q_j|²) q_k = i(λ_k + 4 Σ_j Ḡ_kj I_j) q_k` (script §9). So `A = 4Ḡ = (4 − δ_ij)/π`.

**Refutation attempt.** If KP96's actions were `|q|²`, then `⟨λ, I⟩` would be `Σ λ|q|²`, twice `Λ` in (5). No consistent
reading makes both `⟨λ, I⟩ = Λ` and `A = Ḡ` true.

**Verdict: CONFIRMED** (also Remark 2, p. 5, inherits the factor). Scale invariant in Lemma 6 (p. 20), so Theorem 1 is
unaffected. Agreement with the journal printing remains unverified (no journal copy pinned).

## E-PDE-KP-2: pure-normal nonresonance for unrestricted mass

**Printed.** Theorem 1, p. 5: "for all `m ∈ ℝ`, all `n ∈ ℕ` and all `J`". Lemma 6, p. 20: "Clearly, `⟨l, β⟩ ≠ 0` for
`1 ≤ |l| ≤ 2`", with `β = (λ_{n+1}, λ_{n+2}, ...)` after renumbering and `λ_j = j² + m` (NLS).

**Re-derivation.** For `J = {1,2}`, `m = −9`, `l = e_3`: `⟨l, β⟩ = λ_3 = 9 + m = 0`. More generally `λ_a = 0` at
`m = −a²` and `λ_a + λ_b = 0` at `m = −(a² + b²)/2`, `a, b ∉ J`. Condition (A₂) of Theorem 2 therefore fails for these
masses, and Lemma 6's "clearly" is false for them.

**Refutation attempt.** NLS has the gauge symmetry `u ↦ e^{-ict}u`, which shifts `m ↦ m + c` and adds `c` to every
frequency; a gauge reduction to `m > 0` is the natural repair, but transporting the Cantor family, its frequencies'
Diophantine property (`ω + c(1,...,1)` need not stay Diophantine), and the statement's "linearly stable" requires an
argument the paper does not give.

**Verdict: CONFIRMED** as a premise-attachment gap for the masses listed; not a counterexample to Theorem 1. Track W
(`m > 0`, wave) is unaffected: `λ_j = sqrt(j² + m) > 0` is strictly increasing, so (A₂) holds (blueprint Theorem
`bpW:w0n:nondeg` (ii)).

## New items

**N-1 (P96-W p. 280, proof of Lemma 3).** Printed: "`u = Sq` is in `W^{a,s+σ}` with `‖u‖_{a,s+σ} ≤ ‖q‖_{a,s}` for
`m ≥ 0`", `σ = ½`, in the two-sided norm of p. 279. With `F q = (2π)^{-1/2} Σ c_j e^{ijx}`, the odd extension of `u`
has `c_{±j} = ∓ i q_j / sqrt(λ_j)`, so `‖u‖²_{a,s+½} = 2 Σ_{j≥1} (j/λ_j) j^{2s} e^{2ja} |q_j|² ≤ 2‖q‖²_{a,s}`. For
`q = e_1`, `a = s = 0`, `m = 1`: `‖u‖² = 2/√2 > 1 = ‖q‖²`. Since `sup_{j≥1} j/λ_j = lim_j j/sqrt(j²+m) = 1`
(not `1/sqrt(1+m)`), the operator norm of `q ↦ Sq` is exactly `√2` for every fixed `m > 0` (approached along
`q = e_j`, `j → ∞`), and the printed norm-one bound fails for EVERY `m > 0` (e.g. `m = 3`, `q = e_2`: squared ratio
`4/sqrt(7) ≈ 1.512`). (Revision 1: an earlier draft wrongly claimed a threshold `m ≥ 3`; corrected per audit W-A1.)
Constant only; the conclusion
`‖G_q‖_{a,s+1} = O(‖q‖³)` stands (the companion inequality `‖G_q‖_{a,s+1} ≤ ‖f(u)‖_{a,s+σ}` is true:
`|⟨f, φ_j⟩| = |f̂_j|`, and the sum over `j ≥ 1` is at most `½‖f‖²`). The blueprint's Theorem `bpW:w0n:cubic-bound`
carries the `√2`.

**N-2 (KP96 p. 13, proof of Lemma 3).** Same pattern: "`u = Sq` is in `W^{a,p}` with `‖u‖_{a,p} = ‖q‖_{a,p}`"; the
two-sided norm of the odd extension is `√2 ‖q‖_{a,p}`. Constant only. (Text layer of the born-digital PDF.)

**N-3 (P96-W p. 282).** The Main Proposition prints `Ḡ_ij = (6/π)·(4 − δ_ij/λ_iλ_j)`; p. 284 shows the intended
`(6/π)(4 − δ_ij)/(λ_iλ_j)`. Typographical, superseded by E-PDE-W-1 in any case.

**N-4 (P96-W p. 278, proof of Lemma 1, second line of the `u_tt` display; audit item W-S1).** Printed:
`u_tt = Σ (1/√λ_j)(λ_j² q_j − √λ_j ⟨f(u), φ_j⟩) φ_j`. By (6), p. 277, `q̇_j = λ_j p_j`, `ṗ_j = −λ_j q_j − ∂G/∂q_j`,
and (7), p. 278, `∂G/∂q_j = λ_j^{-1/2}⟨f(u),φ_j⟩`, so `q̈_j = −λ_j² q_j − √λ_j ⟨f(u),φ_j⟩`: the `λ_j² q_j` term needs
a minus sign. The next printed line (`−Σ (q_j/√λ_j) Aφ_j − …`, then `−Au − …`) already has the correct sign, so the
slip is local. Verified on a 200-dpi page image (PDF p. 11). The blueprint's proof of `bpW:w0n:pde-equiv` uses the
correct sign. **Verdict: CONFIRMED** (sign typo; no downstream effect).

**N-5 (KP96 author v2.1 p. 13, first display in the proof of Lemma 3; audit item W-S2).** Printed:
`∂G/∂q̄_j = ∫_0^π f(|u|²) u φ_j dx`, `u = Sq`. From (5), p. 11, `G = ½∫ g(|Sq|²)` with `g' = f`; since
`∂|u|²/∂q̄_j = u φ_j` (real `φ_j`), `∂G/∂q̄_j = ½∫ f(|u|²) u φ_j dx`. In the cubic case (7), `G = ¼∫|u|⁴`, the same
factor ½ is missing. The Lemma 1 computation on p. 11 is consistent with the correct value (`iq̇_j = −2∂H/∂q̄_j =
−(λ_j q_j + ∫ f(|u|²)uφ_j)`), so the slip is local to this display and affects only the gradient formula's constant, not
the smoothing claim. Verified on a 200-dpi page image. Not propagated into W's force interface. **Verdict: CONFIRMED**
(factor-2 typo).

**Remark (not an erratum).** P96-W Lemma 6, p. 293, second branch (`|⟨w, l⟩| ≥ (4n−1)/(4n−4)` "implies
`|⟨w,l⟩| = λ_1^{-1} + λ_ν^{-1}`") is vacuous when `1 ∈ J`; for `J = {1,2}` only the first branch occurs. The blueprint
gives a self-contained proof of (A₃) for `J = {1,2}`.
