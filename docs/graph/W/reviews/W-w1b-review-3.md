# W-w1b delta review

Reviewer: sol-delta3-W-w1b (sol-delta3-W-batch; independent, refute-first).

Verdict: **FAIL**.

Scope: only records still PROPOSED in the current packet, under REVIEW-BRIEF rule 9 and the final SPEC change-log entry (inp merge, corpus re-pin, writer revisions r2). Previously REVIEWED records are context only. All six CORPUS.sha256 entries verified OK. No git, Lean, lake or lint was run.

## Nodes

| id | verdict | spans or reason |
|---|---|---|
| stepW:w1:flowlim | FAIL | Missing direct dependency on stepW:w1:flowlip: uniqueness on B(w,delta) at w1-sequences.tex L903-L904 consumes its L-Lipschitz bound, which discharges the ODE uniqueness premise. |
| stepW:w1:shift | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L1014-L1016 |
| bpW:w1:fourier-shift | PASS | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-shift@L967-L973; blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-shift@L975-L996 |
| stepW:w1:fshift-one | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-one@L976-L981 |
| stepW:w1:fshift-iter | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-iter@L982-L991 |
| stepW:w1:fshift-end | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-end@L992-L995 |

## Coverage

| id | verdict | spans |
|---|---|---|
| bpW:w1:fourier-shift | PASS | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-shift@L967-L973 |
| stepW:w1:fshift-one | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-one@L976-L981 |
| stepW:w1:fshift-iter | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-iter@L982-L991 |
| stepW:w1:fshift-end | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:fshift-end@L992-L995 |
| w1-sequences:source-L997 | PASS | blueprint-W/parts/w1-sequences.tex#source@L997-L998 |

All other coverage items PASS within this delta scope; already REVIEWED items are not re-adjudicated.

## Findings and source checks

The new Fourier-shift lemma and its three steps match L967-L996. The rectangle is inside the open strip even for negative tau; periodicity cancels the vertical integrals. The coordinatewise construction keeps y(z) in T_s, and integer k_r makes the exponential periodic. The external rectangle item supplies Fubini. The final exponential sign is correct: I_n = exp(2 pi k.eta) times the shifted coefficient. The K source note is provenance.

Shifted coefficients applies this lemma with F = H and arbitrary eta inside the strip; its old SOURCE_GAP and K:step:p1:dec-shift dependency are correctly absent. The limit step's integral passage edge is correct, and uniform-limit supplies convergence of derivatives on interior balls; picardholo supplies their common bound. Its remaining missing Lipschitz-premise edge is specified below.

## Complete replacement: stepW:w1:flowlim

```text
NODE: stepW:w1:flowlim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L901-L906
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L901-L906
CONTRACT_ID: stepW:w1:flowlim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the iterates converge uniformly to phi, a C^1 solution of the integral equation; uniqueness among solutions in V; phi^t holomorphic with the derivative bound; this proves (i), (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:flowlip, stepW:w1:picard, bpW:w1:ext-ode, bpW:w1:uniform-limit, stepW:w1:picardholo, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L902-L902 | geometric convergence of the iterates
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L903-L903 | uniqueness of ODE solutions for Lipschitz fields
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L905-L905 | holomorphy of the uniform limit
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L905-L905 | holomorphy and bounds of the iterates
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L902-L903 | uniform convergence of the Picard integrands permits passage to the limit under the Bochner integral
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L903-L904 | the L-Lipschitz bound on B(w,delta) discharges the ODE uniqueness premise
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta-W-w1b+sol-delta3-W-w1b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint defects

None newly identified in the reviewed delta. Findings above concern graph records; they do not reopen the repaired source gaps or assert Lean proof status.
