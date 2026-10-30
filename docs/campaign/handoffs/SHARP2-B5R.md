# SHARP2-B5R handoff: the engine with schedule ratio `a` and decay bound `ȳ`

## Files (`KAM/Sharp2/`)
- `EngineRatioArith.lean` (~150 lines): `xSeqR` (signature verbatim), `xSeqR_nonneg`, `xSeqR_tail`
  (`X_s ≤ X_k ȳ^{s-k}` from `a^p Q_∞ X_k ≤ ȳ`), `partial_sum_leR`
  (`∑_{t<n} a_t X_t ≤ ∑_{t<k} a_t X_t + A X_k/(1-ȳ)`), `summable_mul_decayR`.
- `EngineRatio.lean` (~380): `bite0R`, `biteSR`, `stripSR`, `stageBallR` (verbatim), `stageIterR`,
  schedule lemmas (`bite0R_pos`, `biteSR_pos/_le`, `three_bite0R_le`, `stripSR_eq/_gt/_succ/_zero`),
  and `StageScheme.converge_ratio` (signature verbatim, only line wraps).
- `EngineRatioInst.lean` (~115): `bite0R_two`, `biteSR_two`, `stripSR_two`, `xSeqR_two` and
  `StageScheme.converge_checked_of_ratio`: B5's `converge_checked` derived from `converge_ratio` at
  `a = 2`, `ȳ = 1/2` (so it is an instance). `converge_checked` itself is untouched (merged, used downstream).

## Approach
B5's proof with `2 → a`, `1/2 → ȳ`, reusing its structure (explicit data `X_s`, `β_s`, `m_s`, `μ_s`,
induction for `Adm`, `KAM.Apost.lim_*` for the limit). Changes beyond the substitution:
- Tail sums use the geometric series `∑ ȳ^j ≤ 1/(1-ȳ)`, which gives exactly the `/(1-ȳ)` terms of
  `stageBallR` and `hJ3`.
- **Derivative Cauchy margin.** B5 used `KAM.cauchy_strip` with `δ = 3δ_s` on the strip `r_{s+1}`, and
  `r_{s+1} - 3δ_s = ρ∞ + 3δ_s(2-a)/(a-1)` which is `< ρ∞` for `a > 2`. I use the margin
  `3δ_s/(a-1)` instead (`r_{s+1} - ρ∞ ≥ 3δ_{s+1}a/(a-1) = 3δ_s/(a-1)` exactly), so the derivative
  increments are bounded by `n(a-1)/(3δ_s) · CDK_s δ_s X_s = (n(a-1)/3) CDK_s X_s`, still summable.
  For `a = 2` this is B5's. The signature (no derivative bound in the conclusion) is unaffected.

## Checks
- `nice -n 5 lake build KAM.Sharp2.EngineRatioInst` (builds all three): success, no heartbeat options.
- `lint_sources.sh`: module check PASS; `KAM.lean` flagged >1500 lines (generated root, pre-existing)
  and the known ABI-scratch failure (missing `FixedSunPlanetaryKAM.olean`). Nothing on the new files.
- Signature probe (`.drafts/b5rprobe.lean`): the verbatim `converge_ratio` statement elaborates and is
  closed by `apply StageScheme.converge_ratio <;> assumption`. (The three primed abbrev copies in the
  probe only complain `noncomputable`; the `example`s checking them equal to the real ones by `rfl`
  are fine.)
- `#print axioms` of `converge_ratio`, `converge_checked_of_ratio`, `xSeqR_tail`, `partial_sum_leR`,
  `summable_mul_decayR`: all `[propext, Classical.choice, Quot.sound]`.
- `KAM.lean` regenerated with `python3 -I scripts/gen_root_imports.py`.

## Uncertainties / errata
- No false signature: `converge_ratio` is provable as signed (it carries B5's `hnn`, `hcondT`,
  `hball`). `pinf` is taken `0` as in B5. `κ` is an arbitrary real; `1 < a` is used for positivity of
  `a^p`, the schedule and the Cauchy margin.
- The instance statement `converge_checked_of_ratio` restates `converge_checked` (same distinct
  hypotheses); I did not change `converge_checked` to call it, to stay additive.
