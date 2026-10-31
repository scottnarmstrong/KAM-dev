# W5-STEP handoff — PARTIAL (not ready for audit as a whole)

Branch `inp-wpj`, stacked on W4-HOMOLOGICAL (99206c49). Source: `blueprint-W/parts/w5-kamstep.tex`.

## Status
Landed and built (default heartbeats, no overrides, files < 1500 lines):

| Module | Content | Blueprint label |
|---|---|---|
| `KAM/Wave/KamStep/Phase.lean` | `StepPhase r`: Banach carrier on `KamPhase` with the `kamNorm r` norm (needed to instantiate the `KAM/Wave/Analytic/Flow` lemmas) | setting |
| `KAM/Wave/KamStep/Omega.lean` | symplectic form `stepSymp` at weights (q,q'), bound `‖ϖ(W,W')‖ ≤ (4π+1) r² |W|_r |W'|_r` (sharper than the blueprint's `(4π+2)r²`), antisymmetry, nondegeneracy | `bpW:w5:omega` |
| `KAM/Wave/KamStep/Class.lean` | `IsSmoothing` (P with Fréchet derivative `ϖ(X,·)`), uniqueness of the field, `FamBound` (λ-norm as a conjunction ε₀+λε₁ ≤ ε), `FamBound.mono`, `lamProd_bound` | `bpW:w5:class`, `bpW:w5:lambda-product` (arithmetic core) |

## Not done
`w4-general`, `w4-modified` (m-act, m-const), `taylor`, `flow` (A.4 margins, `FlowHyp` on `StepPhase`), `solve`, `data`
(constants t=2τ+4, c_F, c₀, C₂=896+168c_F; modified t♮=2τ+5, C♮₂), `flow-calc`, `new-ham`, `pullback`, `commutator`,
and the step theorem `bpW:w5:step`. Action-angle/initial were out of scope.
No `bpW:w5:step` statement exists in Lean yet.

## Design notes for the continuation
- **Main blocker (decision needed):** W4 hard-codes p̄ = p+1 (`homWt a (p+1)` in `homLamD`, `homNormalEntry`,
  `HomTaylor`). `w4-general` needs p₊ ∈ [p+½, p+1] and the j^{1/2} frequency hypothesis (5). Either parametrize the
  ~25 W4 files by `pb`, or first deliver the step for p₊ = p+1. Not started.
- Pairing at different weights: `stepPairCLM ha hqq'` needs `0 ≤ a`, `0 ≤ q+q'`; fields of smoothing Hamiltonians live
  at weight p₊, test vectors at p.
- Decouple pullback/commutator/step from the flow by a "flow data" structure carrying the flow-lemma conclusions.
- Lean pitfalls: `Π` is a reserved token; split real inequalities out of big contexts (nlinarith/`set` timeouts);
  `w_build.sh` exits 1 on success, check "Build completed successfully".

## Checks
`w_lint.sh` exit 0 at commit 9fad71be; `w_build.sh` of `KAM.Wave.KamStep.Class` succeeded. No `sorry`, no axioms
added (axioms: see below).

## Errata / deviations
- `(4π+2)r²` in the omega bound is true but not sharp; Lean proves `(4π+1)r²` (stronger, no deviation in use).
- `#print axioms` of `norm_stepSymp_le`, `stepSymp_nondeg`, `isSmoothing_unique_apply`, `lamProd_bound`: propext, Classical.choice, Quot.sound only.
