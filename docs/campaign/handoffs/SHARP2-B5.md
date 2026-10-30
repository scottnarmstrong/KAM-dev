# SHARP2-B5 handoff: the stage-dependent engine

## DESIGN SIGNAL: the signed `StageScheme.converge` is not provable as written

The definitions `StageScheme`, `StageConsts`, `StageScheme.IsNewton`, `xSeq` are delivered verbatim
(`KAM/Sharp2/Engine.lean`, `EngineArith.lean`; `xSeq` lives in `EngineArith`, imported by `Engine`).
The theorem `StageScheme.converge` is **false** as stated: it omits hypotheses of the blueprint
(J1)–(J3) and of the step. I did not add them silently: the corrected theorem is
`StageScheme.converge_checked` (distinct name), below. Counterexamples to the signed statement
(all with `n` arbitrary, `kpre = 0`, `k = 0`/`1`):

1. **Ball budget.** No hypothesis controls the `< β` premise of `IsNewton.step`
   (`CDK μ/(γ δ^κ) < β`), while `β₀` is arbitrary. State `α = ℝ × ℝ` (remaining ball, current error),
   `tor x = (θ, 0)`, `par = 0`, `Adm r β μ m (b, μ') := β = b ∧ μ = μ' ∧ 0 < b ∧ 0 ≤ μ`,
   `step r δ (b, μ') = (b - μ'/(γ δ^κ), μ'²/(γ δ^{κ+1}))`, `C δ = (Q = 1, cond = True, CDK = 1, Cp = 0)`.
   Then `IsNewton` holds, and `htail`, `hJ1`, `hJ3` are trivial. Take `μ₀` with `hJ2`
   (`2^{κ+1} X₀ ≤ 1/2`) and `β₀ = μ₀/(2γδ₀^κ)`. The first iterate has remaining ball `< 0`, so the
   conclusion `∀ s, ∃ r β μ m, Adm … (iterate s)` fails at `s = 1`.
2. **Tail step conditions.** `hJ1` only covers `s < kpre`; the blueprint's (J1) also asks the tail
   conditions at `X_k`, and they must persist along `X_s ≤ X_k`, which is not true for an arbitrary
   `cond : ℝ → Prop`. Counterexample: `cond := False`, `Ctail.cond := False` (so `IsNewton.step` and
   `htail` hold vacuously), `α = ℕ`, `Adm … x := x = 0`, `step x = x + 1`, `x₀ = 0`: the conclusion
   fails at `s = 1`.
3. **Signs.** (J3) bounds the *total* `m₀ + Σ_{s<k} ϱ_s w_s X_s + 2ϱ_∞ w_∞ X_k ≤ σ`, but the step needs
   the partial sums `≤ σ` at every stage; with `ϱ_s w_s` of mixed sign in the prefix (`+5` then `-5`)
   the first partial sum can exceed `σ`. Nonnegativity of `rate * wt` (and of `CDK`, `Q`, used for the
   summability and the sign of `X_s`) is needed. All real constants of the design are nonnegative.

## Delivered

- `KAM/Sharp2/EngineArith.lean`: `xSeq`, `xSeq_nonneg`, `xSeq_tail` (`X_s ≤ X_k/2^{s-k}` from
  `2^{κ+1}Q_∞X_k ≤ 1/2`), `partial_sum_le` (critical sums `∑_{t<N} a_t X_t ≤ ∑_{t<k} a_t X_t + 2 A X_k`),
  `summable_mul_decay`.
- `KAM/Sharp2/Engine.lean`: the verbatim structures; the schedule (`bite0`, `biteS`, `stripS`, with
  `stripS_succ`, `stripS_gt`, …); `stageIter`; `stageBall`; and
  **`StageScheme.converge_checked`**: the hypotheses of `converge` plus exactly three more,
  - `hnn`: `0 ≤ Q`, `0 ≤ CDK`, `0 ≤ rate * wt` for every bite `δ ≤ δ₀`;
  - `hcondT`: `Ctail.cond X` for `0 ≤ X ≤ X_k`;
  - `hball`: `stageBall … < β₀` (`∑_{s<k} CDK_s δ_s X_s + 2 CDK_∞ δ_k X_k < β₀`);

  conclusion: that of `converge` (`∃ Kinf pinf, differentiable, primary, real on reals, ∀ s admissible
  with `ρ∞ < r` and caps `≤ σ`, uniform convergence) **plus** the closeness
  `∀ θ ∈ T_{ρ∞}, ‖Kinf θ − tor x₀ θ‖ ≤ stageBall …` (which B6 needs).
  `pinf` is unconstrained in the signature (taken `0`); no parameter limit is proved (the
  `Cp` bound is stated by the scheme but not summed here).

Proof: the explicit data `X_s`, `β_s = β₀ − Σ CDK δ X`, `m_s`, `μ_s = X_s γ δ_s^{κ+1}` make the step
hypotheses (conditions, ball, caps) independent of the iteration; induction gives `Adm` at every
stage; the limit uses `KAM.Apost.lim_k/lim_dk/lim_holo/lim_primary/lim_close`; the derivative
increments (not in the signature's step) come from Cauchy on the difference
(`KAM.cauchy_strip` with `δ = 3δ_s`; `T_{ρ∞} ⊆ T_{r_{s+1} − 3δ_s}` exactly), with
`n d_s/(3 δ_s) = (n/3) CDK_s X_s` summable.

## Checks
- `nice -n 5 lake build KAM.Sharp2.Engine`: success, no heartbeat options.
- `lint_sources.sh`: nothing on `KAM/Sharp2`; only the known ABI-scratch failure.
- `#print axioms` of `xSeq_nonneg`, `xSeq_tail`, `partial_sum_le`, `summable_mul_decay`,
  `StageScheme.converge_checked`: `[propext, Classical.choice, Quot.sound]`. `KAM.lean` regenerated.
- Signature check: the four definitions elaborate verbatim (`#check` in `.drafts/ax.lean`);
  `converge` cannot be closed (design signal above), so the probe closes `converge_checked` instead.

## For the orchestrator
Replace the signature of `StageScheme.converge` by `converge_checked`'s (or add the three hypotheses to
the blueprint's proposition and `bp:p2s2:engine`): B6 then supplies `hnn` (the constants are
nonnegative), `hcondT` (conditions are `X ≤ ·`), `hball` (the ball budget `4 CDK ... < μ` of
`routeBOk`). Also `κ` is arbitrary real in the statement; nothing here needs `κ + 1 ≥ 0`.
