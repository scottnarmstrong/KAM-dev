# W5-STEP handoff — PARTIAL (not ready for audit as a whole)

Branch `inp-wpj`, stacked on W4-HOMOLOGICAL (audit-target commit `82d8325d`). Source:
`blueprint-W/parts/w5-kamstep.tex`. All modules below build at default heartbeats (`w_build.sh`), no `sorry`, no
axioms, `w_lint.sh` exit 0; `#print axioms` of every main result listed: propext, Classical.choice, Quot.sound only.

## Landed (modules under `KAM/Wave/`)

| Module | Content | Blueprint label |
|---|---|---|
| `KamStep/Phase.lean` | `StepPhase r`: Banach carrier on `KamPhase` with norm `kamNorm r` | setting |
| `KamStep/Omega.lean` | symplectic form `stepSymp`, bound `(4π+1) r²` (sharper than `(4π+2) r²`), antisymmetry, nondegeneracy | `omega` |
| `KamStep/Class.lean` | `IsSmoothing`, uniqueness of the field, `FamBound` (λ-norm as a conjunction), `FamBound.mono`, `lamProd_bound` | `class`, `lambda-product` (arithmetic core) |
| `Homological/*` (W4 refactor) | W4 with general `p_+` (`pb`), `j^{1/2}` tail; general declarations carry `_gen`; `PPlusOne.lean` restores the old names at `p_+ = p+1` | `w4-general` |
| `KamStep/LatticeBN.lean` | `waveBN` (`B^♮_σ`), `waveBNconst` (`b^♮(τ) = 4(C_0+C_2+C_{2τ}+C_{2τ+2})`), `waveBW_le_waveBN`, `waveBN_le : B^♮_σ ≤ b^♮ σ^{-(2τ+4)}` | `w4-modified` (iii), step `m-const` |
| `KamStep/Data.lean` | step constants `stepC1, stepT, stepCF, stepC0, stepC2` and modified `stepTn, stepCFn, stepC0n, stepC2n`, `stepMF`; positivity; `stepMF_le_of_small` (smallness ⇒ `M_F ≤ ση²/16`); `stepMF_margins` (`M_F ≤ σ/1024`, `M_F/(σ/4) ≤ 1/256`, `16M_F/σ ≤ η²`); `stepSolve_bound`, `stepSolve_bound_mod` (`3C₁B_σ/α · 3ε ≤ M_F`, both cases); `stepEstimate_arith` (`896ηε + 168 c ε²/(ασ^tη²) ≤ C₂(...)`) | `data`, `solve` (arithmetic), `step` (st-1/st-2 arithmetic) |
| `KamStep/Divisors.lean` | `stepDivisors` (divisor lower bounds after the step, `HomMelnikov` data), `stepFreqHyp` (the frequency hypothesis `bpW:w5:freq` is stable with `M₀+3ε`, `M_ω+6πε/λ`, `M_Ω+3ε/λ`), helper `homPairL_sub_le`, `waveA_le_of_modeSize_le` | `step` (iii), (iv) |
| `KamStep/Flow.lean` | `stepDomain ρ s r'`, openness, `stepDomain_margin` (ball `B(w,σ/2) ⊂ D(s-σ,r)` for `w ∈ D(s-2σ,r/2)`), **`stepFlowHyp`**: `FlowHyp X V U M (σ/4)` on `StepPhase r` with the concrete A.4 margins (so all landed `KAM/Wave/Analytic/Flow` lemmas apply), `stepImage_mem` (`φ^t(D(s-5σ,ηr)) ⊂ D(s-4σ,2ηr)`) | `flow` (margins, image, hypotheses) |

## Not done
* `w4-modified` (i), (ii), m-act (operator estimate for `∂_θ Q_F : ℓ_p → ℓ_{p_+}`), the modified `Q`-division; only the
  lattice constant (iii) is done. Design: the `p_+`-weighted matrix of `Q_F` is the Hadamard image of the `p+1`-matrix
  with multiplier `d'_{ij} = I^{-c} d_{ij}` (`c = p+1-p_+`, `I = i+2`); `HomHadamardBound` applies with
  `|d'_{ij}| ≤ A_k/(α̂|i-j|)` since `β ≤ c`.
* `taylor` (Lemma Taylor: components of `R`, scaling `S_t`, Cauchy estimates, constants 3 and 128).
* `solve` proper (the objects `F, N̂, â₀` for the Taylor polynomial and the field/λ-bounds; only constants done),
  `flow` (ii): `|φ^t - id|^λ ≤ 2M_F` and derivative bounds (Cauchy on balls); the existence/holomorphy/Lipschitz-in-ξ
  conclusions follow from the landed lemmas applied through `stepFlowHyp` but the `p_+`-smoothing and the λ-norm
  statements are not written; reality/equivariance (iv).
* `flow-calc` (continuity, variational equation, symplecticity, inverse, transport, time derivative via W4 Lie (iv)).
* `new-ham` (expansion with the triangle integral, field of `P_+`, weak conjugacy), `pullback` (constant 7),
  `commutator` (`24 ε M_F/(ση²)`), and the step theorem `bpW:w5:step` (i)–(v). No Lean statement of `bpW:w5:step` exists.
  The arithmetic closing it is `stepEstimate_arith`; the analytic content of (i), (ii), (v) is missing.
* Action–angle and initial perturbation were out of scope (need W3).

## Design notes
* `FamBound`/`IsSmoothing` in `Class.lean` are the setting for λ-norms and smoothing Hamiltonians.
* Carrier of the flow: `StepPhase r` with fields at weight `p` (norm `|·|_{p,r}`); smoothing is expressed by the
  weight of the representative.
* Lean pitfalls: `Π`, `α₊`, `ω₊` are not valid identifiers; `U` must live in `StepPhase r` (use
  `stepDomain r (s-2σ) (r/2)`, not `stepDomain (r/2) …`); `nlinarith` in big contexts needs split-out facts.

## Blueprint defects / deviations
* Omega bound: `(4π+1)r²` proved (stronger than the blueprint's `(4π+2)r²`).
* `stepImage_mem` needs `σ ≤ 1` (the blueprint step `f-image` uses the numerical smallness only); harmless since
  `σ ≤ 1/4` in step data.
