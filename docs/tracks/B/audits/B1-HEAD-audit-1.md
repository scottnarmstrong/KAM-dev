# B1-HEAD independent package audit 1

**Verdict: PASS WITH NOTES for B1-T and B1-E as ordinary Track B implementations.** No blocking proof, signature, premise, carrier, or hygiene defect found. This is not a freeze or seal: no Track B anchor or registered provider exists yet, and exact-text owner approval remains outside this audit. Note N1 below is a documentation correction.

## Scope and identities

Audited worktree: `/root/code/KAM-inp-b1head`; HEAD `d6bd181f8f963522dfea054f3b178f9acf267533`; comparison branch `inp` at `23830ca29dc7fe4069aa560eb2b004e6a0af223a`. Initial worktree status was clean. Review used `git diff inp...HEAD`: four new Lean modules (472 lines total) and `docs/tracks/B/audits/B1-HEAD-handoff.md`, with no other changes.

Read the package audit brief, AGENTS.md, PLAN.md, DECISIONS.md, B1 common and HEAD briefs, handoff AUDIT FOCUS, SPEC, FREEZE-PROPOSAL, OWNER-DECISIONS, elaboration draft, statement review, program-B plan §§2 and 7, all four implementations, and the relevant CORE/TRANSFER/ODE implementations and frozen definitions. The Track B focus specializes the generic I/N/P brief: the controlling statements are the two ordinary proposals, not unrelated frozen I/N/P theorem anchors. There is no `docs/tracks/B/statement.md`; SPEC and FREEZE-PROPOSAL supply that role. CORE/TRANSFER audit reports are not present in this worktree's audit directory; their handoffs are present. Their prior PASS WITH NOTES status is supplied by the HEAD focus; the dependency argument below was inspected directly.

The user's exact report path overrides the generic brief's main-worktree output instruction. Only this report is a repository edit. Temporary probes and logs use `.lake/abi-scratch/` and are removed after recording their results. No state-changing git command, generated-root repair, frozen edit, or dependency edit was performed.

| Audited object | SHA-256 |
|---|---|
| `KAM/EffectiveStability/Torus.lean` | `9e73b438fd8434f49738000839dfdd5cbdbf893304163acdeb10d2fae9468199` |
| `KAM/EffectiveStability/Oscillator.lean` | `8d774e2373768ac2af9d6561f87289394ec94a6f4cbf1b2c8670b493a7ee151e` |
| `KAM/EffectiveStability/ObservableTransfer.lean` | `70b58880f938d6a5e16f38de582c755a2562ee0d4010dbb58fb8613b31585965` |
| `KAM/EffectiveStability/Examples.lean` | `eaf7c540a1ec2a92d6e651a8517b7513437e6833f275d22398b6357d22908e69` |
| `docs/tracks/B/freeze/elaboration-draft-1.lean.txt` | `6f31e39200df4055bdee568d8a28fba6a7f14b8a7052e46234460fd05a52f13a` |
| `docs/tracks/B/FREEZE-PROPOSAL.md` | `7a60eed881badabfa9edb8640d2eb17ee1deedda71e1383abf0e3d560e7d581b` |

## Declaration and definition review

Every declaration below is in namespace `KAM.EffectiveStability`; these are all six new public declarations.

| Node | Lean declaration and location | Verdict | Reason |
|---|---|---|---|
| B1-T | `torus_confinement`, `Torus.lean:35` | PASS WITH NOTES | Exact proposed text; derives chart lifetime and drift, transports to physical dynamics, and proves uniqueness in all V. Ordinary proposal status and N1 apply. |
| B1-E | `oscillator_confinement`, `Oscillator.lean:36` | PASS WITH NOTES | Exact proposed text; compact Cartesian continuation, correct action bracket and zero-action behavior; same status note. |
| B1-transfer/T | `torus_observable_transfer`, `ObservableTransfer.lean:27` | PASS | All headline premises and conclusions retained, with exactly the specified static observable premise and bound on the same existential solution. |
| B1-transfer/E | `oscillator_observable_transfer`, `ObservableTransfer.lean:77` | PASS | Same, using `oscClosed b` and `L.mulVec (oscAct w)`; no radius/action normalization change. |
| B1 edge/T | `torus_confinement_example`, `Examples.lean:26` | PASS | Actually calls B1-T with identity chart, integrable quadratic H, zero R and η, a=1, b=2, ε=1, V=univ. Any T≥0 and admissible initial point. |
| B1 edge/E | `oscillator_confinement_example`, `Examples.lean:42` | PASS | Actually calls B1-E with harmonic H, identity chart, zero R and η, a=0, b=1, ε=1, initial origin. Nonnegative action plus the level bound gives exactly zero action. |

**Definition classification:** no new `def`, `abbrev`, `structure`, instance, or carrier is introduced by this diff. Local `D`, solution functions and proof-local values denote the stated chart domains or transported solutions, with no fallback behavior. Reused domain helpers are literal set-builders; `oscAct w` is the frozen `oscillatorAction w.2 w.1`, not an alternative action. Frozen field/form/action bodies were read: `X_H=(∂₂H,−∂₁H)`, `ω(v,w)=Σ(v₂w₁−v₁w₂)`, `I_j=(p_j²+q_j²)/2`. Their use agrees with SPEC.

No conclusion-shaped assumption appears. In particular, headline hypotheses mention neither a solution nor a confinement/lifetime predicate. Corollary `hA` is a static approximation on the whole closed chart region, not a dynamical estimate assumed along the unknown orbit. Both corollaries keep arbitrary finite `m,n`, the same matrix coefficients and errors, and exactly `2*d i + |t|*Σj |L i j|*η j`; no hidden constant or larger dependence is introduced.

## Exact statement identity and application probes

A Python extraction compared bytes from the last declaration docstring opener before each theorem through the complete `:= by`, without normalization:

```text
torus_confinement BYTE_IDENTICAL True bytes 2576
  sha256 703d6f0ba7f1983a746f8ad1dae4f1dfdff0341f8b4db0f009bf2f24d7b11cbc
oscillator_confinement BYTE_IDENTICAL True bytes 3011
  sha256 567adf71c2bc3b92e4ddb3f1ba51d4da3db41504f2ac5c611cda8cbade6fea87
```

The scratch module copied each draft declaration under `audit_torus_confinement` / `audit_oscillator_confinement`, replacing its draft proof by the corresponding actual export applied to **every explicit binder in order**. The torus body used:

```lean
exact torus_confinement a b η ε T hε hT hη hmargin V hV H hH Ψ Ψinv
  hΨ hΨV hΨsymp hΨinv N R hR hRper hHΨ hRη w₀ hw₀
```

The oscillator body used the same ordered list with `hRper` omitted. Each additionally passed `example : type_of% @<actual export> := @<audit copy>`. Both draft-shaped bodies and both full type assignments elaborated. These check the application discipline relevant to a future seal, without claiming a current provider/frozen equality. The probe also instantiated both published examples at `n=1,T=0` (torus initial point zero), and printed axioms of all six exports. Exit 0, no warnings or errors.

## Trace of the existence and confinement argument

1. **Torus periodicity is derived on an open domain.** `Torus.lean:63-72` defines D=cyl(b+ε), proves openness and K=H∘Ψ of class C² using the stated image inclusion, hence X_K of class C¹. Lines 73-81 derive K(x+angleShift k)=K(x) from translation invariance of D, `hHΨ` at both points, unchanged action coordinates, and `hRper`. Lines 82-92 establish a neighborhood equality of the translated K with K, then use `fderiv_comp_add_right` and `EventuallyEq.fderiv_eq`. Thus all components of X_K are periodic. No physical H/V periodicity or chart equivariance is silently assumed.
2. **Only the remainder drives drift.** `Torus.lean:94-104` obtains an eventual decomposition from the open D, and differentiability of K and R there; `fderiv_angle_eq_of_eventuallyEq` differentiates K−R along the angle line, never N. The negative sign in the action velocity disappears under absolute value. `Oscillator.lean:73-114` identifies `{|oscAct|≤b}` with `oscClosed b` by nonnegativity, supplies its compactness and inclusion in D, and uses `fderiv_oscAct` plus `bracket_action_eq_of_eventuallyEq`. The resulting bracket is exactly q_j∂p_jR−p_j∂q_jR. Cancellation uses a rotation curve and differentiability of K−R, including at zero action; it does not differentiate N.
3. **The engines produce the orbit.** B1-T calls `exists_confined_solution_periodic` at `Torus.lean:105`; B1-E calls `exists_confined_solution_compact` at `Oscillator.lean:115`. The supplied premises are open-domain C¹ regularity, periodicity or compactness/inclusion, derivative bounds on the stopped region, strict margins, and the original initial data. `ChartFlow.lean:97,134` first invokes `gen_maximal`. Its `exists_confined_aux` at lines 33-80 derives stopped-region bounds via `firstExit_box_of_deriv`, not an assumed orbit bound. In `FirstExit.lean:31-120` the supremum of safe forward times belongs to the closed safe set by continuity; drift plus the strict margin puts it strictly inside every face and extends safety, a contradiction. Lines 124-149 handle negative time by reflection. The stopped bound is used only on `uIcc 0 t` and follows from actual derivatives by the mean-value estimate.
4. **Continuation is not assumed by the headlines.** Under a hypothetical finite maximal endpoint within ±T, the first-exit estimate confines the entire relevant half-interval. `ChartFlow.lean:106-109,141-144` then discharges the auxiliary continuation implications with `gen_continuation_compact` or `gen_continuation_periodic`. This contradicts that endpoint and yields real T₁>T inside the maximal interval. Only the action box is claimed compact for the torus, never the lifted cylinder. For oscillators the compact set is Cartesian `oscClosed b`. Neither engine assumes existence on the requested interval. The argument allows T=0 and η=0 without division by either.
5. **Physical transport and full uniqueness.** `Torus.lean:108-126` and `Oscillator.lean:118-135` transport z=Ψ∘w by `hasDerivAt_comp_chart`, using actual differentiability and symplecticity on D. The uniqueness call is `gen_uniqueness_inter` with field X_H, W=V, J₁=the arbitrary order-connected I containing 0, and J₂=Ioo(−T₁,T₁). H is C² on open V, so X_H is C¹ there. The competing solution need not lie in the chart image. Bounds include |t|=T because T<T₁. The sole left-inverse premise yields Ψinv(z t)=w t and Ψ(Ψinv(z t))=z t on this range.
6. **Transfer and examples.** Each corollary obtains the headline's very same T₁,z and preserves its initial value, equation, uniqueness and chart bounds. The strict margin and hT/hη place both w₀ and Ψinv(z t) in the static hA region; the latter image is rewritten using the proved chart identity. `observable_transfer_bound` then gives the displayed estimate. The examples supply every headline premise with concrete smooth Hamiltonians and satisfiable data. Their exported types deliberately retain only initial data and action conclusions, but their proofs do instantiate the full dynamical results. Both cover backward time through |t|, arbitrary finite T≥0, and in particular T=0.

## Hygiene and mechanical evidence

All Lean/Lake commands below ran serially under the following wrapper, denoted W:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1
```

Build commands were W followed by `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b1head <module>`, one module per invocation in the order below. The gate additionally invokes `nice -n 5 lake build`. No core root or opt-in application target was requested.

| Module | Exact build output after slot acquisition | Exit |
|---|---|---|
| `KAM.EffectiveStability.Torus` | `Build completed successfully (2875 jobs).` | 0 |
| `KAM.EffectiveStability.Oscillator` | `Build completed successfully (2875 jobs).` | 0 |
| `KAM.EffectiveStability.ObservableTransfer` | `Build completed successfully (2877 jobs).` | 0 |
| `KAM.EffectiveStability.Examples` | `Build completed successfully (2877 jobs).` | 0 |

No warning was emitted. Builds reused the worktree's existing build snapshot.

Probe command: `W lake env lean .lake/abi-scratch/B1HeadAudit.lean` (exit 0). Exact axiom output:

```text
'KAM.EffectiveStability.torus_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillator_confinement' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torus_observable_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillator_observable_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torus_confinement_example' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.oscillator_confinement_example' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation (exit 0):

```sh
W lake env leanchecker --verbose KAM.EffectiveStability.Torus \
  KAM.EffectiveStability.Oscillator KAM.EffectiveStability.ObservableTransfer \
  KAM.EffectiveStability.Examples
```

Exact output:

```text
replaying KAM.EffectiveStability.Examples
replaying KAM.EffectiveStability.ObservableTransfer
replaying KAM.EffectiveStability.Oscillator
replaying KAM.EffectiveStability.Torus
```

The replay process environment was checked directly: `LEAN_NUM_THREADS=1`; LEAN_PATH resolves project modules through `/root/code/KAM-inp-b1head/.lake/build/lib/lean`, following only dependency-package paths and preceding the toolchain path. No other project checkout shadows these modules.

The four files have 136,146,132,58 lines respectively, all with copyright, `module`, public imports, module docstring and `@[expose] public noncomputable section`. All ambient phase types are the required finite function products. No forbidden proof escape or resource override appears in the new code. Transitive project-import traversal found 38 modules, no provider and no frozen theorem anchor; all 20 reachable manifest entries are SEALED definitions. In particular, no DRAFT_SORRY theorem can supply a hidden proof premise.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md lakefile.lean` produced no output (exit 0). `git diff --check inp...HEAD` produced no output (exit 0).

Lint command: `W sh scripts/lint_sources.sh`. Result recorded below after completion.

## Notes, suspected defects and deviations

**N1 — nonblocking inherited-regularity wording, already present outside the diff.** `docs/tracks/B/FREEZE-PROPOSAL.md:144-146` says “with no differentiability of `N` at 0 assumed (it is inherited from `K - R`).” The parenthetical can incorrectly assert differentiability of N at zero. What is differentiable is the composition N∘I=K−R on the Cartesian chart. For n=1, Ψ=id, R=0, N(J)=|J₀| and H(w)=I₀(w), one has N(I(w))=I₀(w) smooth everywhere, while N is not differentiable at the zero action. These data satisfy the oscillator premises with a=0,b=1,ε=1,η=0 and initial origin. Replace the parenthetical by “the composition `N ∘ I = K - R` is differentiable on the chart domain; differentiability of `N` itself is not asserted.” This is the same distinction already corrected in OWNER-DECISIONS OD-B2 and the headline docstrings by STATEMENT-REVIEW-1 C1. No Lean statement or proof needs changing.

No new pinned-paper defect was discovered by this implementation audit. The pre-existing source candidates listed in FREEZE-PROPOSAL §5 / program-B plan §9 remain carried findings, not newly verified paper errata here: CL20 harmonic/degree +2 indexing, its ν₂ asymptotic, BFN16's repeated initial point, and GLS17's λ₅ and quadratic index. The actual B1 premises use the entire remainder and squared-action normalization; none of those unrelated candidates is used in this package's proof. The present review introduces no mathematical deviation. Existing OD-B2/B3/B4/B6 generalizations remain explicit (weaker regularity premises, left inverse, symmetric lifetime, n=0 allowed).

Uncertainty is limited to future exact-text approval and migration to providers/anchors, not an unpaid inequality or missing proof step in these ordinary theorems. A future freeze/seal must run its own manifest and provider checks; this report supplies implementation evidence only.
