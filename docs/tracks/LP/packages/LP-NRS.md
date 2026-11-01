# Package LP-NRS: the scale choice (37) and the exponential horizon (MAIN L13 lines 444–458, L12 scaling)

Wave 2. Prover brief: `/root/code/KAM-inp/.drafts/briefs/lp-prover.md` (hard rules, capped wrappers, handoff).
This is pure scalar arithmetic with no analysis and no dynamics. It discharges the numeric premises of
`KAM.Nekhoroshev.ExtNFHyp` and `KAM.Nekhoroshev.nonresonant` for the Lemma-13 route with `p = 2`.

## Source

`docs/tracks/LP/source/MAIN.md` Lemma 13, lines 444–458 ((37) and the choice of `κ₁`, `μ₀`), and (38); Lemma 12
(lines 381–428) for the shape `K = ⌊κ μ^{-a}⌋ ≥ κ μ^{-a}/2` and `c`. Read with `source/AMENDMENTS.md`:
- **N6:** stopped radius `r = D₀√μ`, improvement to `r/2`.
- **N4:** (35) is not a dependency.

Engine numerics, read them literally:
- `KAM/Nekhoroshev/Partial/Setting.lean`: `ExtNFHyp` fields `divisor_size : K*L*b.rB ≤ α/p`,
  `slow : b.SL s` (`64*π*k*s*b.rB ≤ b.w^2`), `cutoff : 6 ≤ 2*π*K*s`.
- `KAM/Nekhoroshev/Partial/Nonresonant.lean:341`: `hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K)`, and the time bound
  `|t1| ≤ s*b.rB/(5*ε)*exp((2*π*K*s)/6)`.
- `conjExp p = p/(p-1)`, so `conjExp 2 = 2`.

## Owned files

`KAM/Planetary/StrongAMD/NonresonantScale.lean` (split with a facade if needed). Nothing else. Import only Mathlib
and the engine's `Setting` modules (for `conjExp`, `PartialBlock.SL` if you state through them).

## Theorems

Data: `γ τ L M₂ D₀ s w ρ : ℝ`, all positive except `0 ≤ L`, and `k : ℕ` with `1 ≤ k`. Write
`a := 1 / (2 * (τ + 1))` and, for `μ > 0`:
- `K μ := (⌊κ * μ ^ (-a)⌋₊ : ℝ)`;
- `r μ := D₀ * √μ`;
- `α μ := γ / (2π) * (K μ) ^ (-τ)`;
- `ε μ := M₂ * μ`.

1. **Scale theorem** (`lp_scale_choice` or a better distinctive name). `∃ κ μ₀ c T₀ > 0`, with `κ, c, T₀`
   depending only on the data (the binder order shows it: they are chosen before `μ`), such that for every
   `0 < μ ≤ μ₀`:
   - (a) `1 ≤ K μ` and `κ * μ^(-a) / 2 ≤ K μ ≤ κ * μ^(-a)`;
   - (b) `K μ * L * r μ ≤ α μ / 2` (`divisor_size`, `p = 2`);
   - (c) `ε μ ≤ α μ * r μ / (2^7 * conjExp 2 * K μ)` (`hsmall`);
   - (d) `64 * π * k * s * r μ ≤ w^2` (`SL`);
   - (e) `6 ≤ 2 * π * K μ * s` (`cutoff`);
   - (f) `r μ ≤ ρ` (the action tube fits in the analytic domain; `ρ` stands for `r_*` and `4 r_g`);
   - (g) `T₀ * exp (c * μ^(-a)) ≤ s * r μ / (5 * ε μ) * exp (2 * π * K μ * s / 6)`.
   MAIN route: `L D₀ κ^{τ+1} ≤ γ/(4π)` and `M₂ κ^{τ+1} ≤ γ D₀/(512π)` give (b), (c), using
   `a(τ+1) = 1/2` and `K ≤ κ μ^{-a}`. Then decrease `μ₀` for (a), (d), (e), (f) and `μ ≤ 1`.
   Take `c = π s κ / 6` and `T₀ = s D₀ / (5 M₂)`, or any explicit positive choice.
2. **Diophantine to engine nonresonance at the centre** (scalar form). If `γ * |k|₁^{-τ} ≤ |k · ω|` for every
   `0 ≠ k ∈ ℤⁿ`, then for every `0 ≠ k` with `|k|₁ ≤ K` (`K ≥ 1`): `γ / (2π) * K^{-τ} ≤ |k · (ω / (2π))|`.
   This is the radian-to-period-one conversion of MAIN (5). State it with `Fin n → ℤ`, an explicit `ℓ¹` mode
   size, and a real dot product. The engine's `IsNonresonant` form (`zBall`, `dotC`, `freq`) is for package
   LP-NRR; if `zBall`'s norm is not `ℓ¹`, report it.
3. **Exponent corollary.** For `τ = n − 1/2`, `a = 1/(2n+1)`.

## Checks and stop condition

- `lp_build.sh` on the module.
- `lp_lint.sh` exits 0.
- `main_shortname_check.py` exits 0.
- `#print axioms` of items 1–3.

Stop when done or blocked: report, never add a hypothesis silently. Expected size 300–700 lines. `Real.rpow`
and `Nat.floor` estimates should be focused lemmas; avoid `nlinarith` on large goals (see the lean-learnings
skill if available).

## Handoff

`docs/tracks/LP/audits/LP-NRS-handoff.md` (committed, with AUDIT FOCUS) and `.drafts/handoff-LP-NRS.md`, then
`touch .drafts/READY-LP-NRS`.
