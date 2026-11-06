Audited commit `6e0c92d1a2337b9badd48aeca17c1a960b07883e`; SHA256: `KAM/EffectiveStability/SJSU/Confinement/Shift.lean` = `091bbbaefe5d1eed8bb170332af529703d610afdfed61370bf01ebfa33689e0b`; `KAM/EffectiveStability/SJSU/Confinement/Statement.lean` = `c299fe7725047a0d453e54cd7d3abea244d15e8f4f6e1413a2febb9b54aeb1db`; `KAM/EffectiveStability/Tube/Check/Center.lean` = `35e50b78dfebf895f16785b381fec161b40043031264b96c72328fe5b4078b00`; `KAM/EffectiveStability/Tube/Check/Deriv.lean` = `6bb8b5378b69c6fb03005edd8fe009ac1362bcd554da7e9f48c1888d9e28d965`.

**Verdict: PASS WITH NOTES for N5b-Assembly Phase B (i)–(iii).** No blocking statement,
hypothesis, numerical-feasibility, or proof defect found in these four files. Both conditional lemmas
conclude exactly D76 for its exact initial-state hypothesis. This is an audit of the delivered
conditional assembly, not closure of `sjsu_secular_confinement_proof` or certification of N5a/N7.

Read the package audit protocol, worker rules, brief, Phase-B handoff, AGENTS, PLAN, DECISIONS,
the route and gates, proposal draft v2, and the actual generic consumer. Inspected SJSU/Ham and
SJSU/Model only for the definitions/interfaces consumed here. Phase A is contextual reuse, with
the Deriv docstring correction explicitly included in this audit. Other workers' untracked
Ham/Engine/Poly/ledger files are outside this package review.

## Findings and scope notes

**N1 — Nonblocking outstanding supplier attachment; no conclusion-shaped hypothesis.**
Locations: `Statement.lean:62–84,124–135,155–159` and
`docs/explorations/sjsu-g2-handoffs/N5b-Assembly.md:9–15`.

Quoted premises include
`sjsu18O2 (rotMap sjsuV (polar y)) = h (shiftChart sjsuB y)`,
`|reducedBracket (f j) h (u, φ)| ≤ η j`, and
`|f j (u, φ) - ct j - u j| ≤ ε j`.
These are legitimate static identity and numerical enclosure obligations. Neither theorem
assumes existence, uniqueness, trajectory confinement, a frontier separation theorem, or the
D76 eccentricity conclusion along a trajectory. The handoff correctly says the ordinary theorem
is still unavailable. No correction is required for the audited phase. For completion, N5a must
provide the exact `h` with `hHh` and joint `hhd`; N7 must attach actual observables, their periodicity
and differentiability, bracket and face certificates, and partial bounds. Do not replace exact `h`
by a truncated model in `hHh`, or treat the numerical evidence below as those Lean certificates.

`of_obs` derives the centre error from the face bound and proved `|u(z*)| ≤ sjsuMu`; it does not
assume or numerically replace `f(tubeChart z*)`. Its stronger face budget is feasible, as checked
below. If N7 changes/prunes/rounds the supplied observables, it must recheck the budgets for that
exact data.

**Audit-1 N1 resolved.** Location: `Tube/Check/Deriv.lean:35–38`.
The corrected text says “the inverse of the polar derivative at `polarInv w`” and explicitly warns
that it is not the derivative of the discontinuous arg lift on `q = 0`, `p < 0`.
`git diff HEAD^ HEAD -- <Deriv path>` contains only this docstring replacement. Independent
differentiation of `q = -sqrt(2I) sin θ`, `p = sqrt(2I) cos θ` gives
`dI = q dq + p dp`, `dθ = (q dp - p dq)/(q²+p²)`, agreeing with the formula and the local-inverse
interpretation. No additional fix is needed.

## Exact target and consumed interfaces

Compared `Statement.lean:85–103` and `136–154` with the theorem block of proposal draft v2:
both `hz₀` and the entire conclusion match after removing whitespace. A fresh Lean scratch
also states two application theorems with the **proposal's own** `hz₀` and conclusion copied
independently, and applies each audited lemma directly.

This checks the following without weakening any quantifier:

- Carrier `(Fin 3 → ℝ) × (Fin 3 → ℝ)`, order `(η, ξ)`; all six nominal decimals verbatim;
  closed sup-norm box of radius `10⁻⁶`, including its boundary.
- `∃ T₁ > 5·10⁹`, a real-time Cartesian solution through `z₀`, and `HasDerivAt` on
  `Set.Ioo (-T₁) T₁` for the exact development `sjsu18O2`.
- Uniqueness against every real-time Cartesian solution on every order-connected interval through
  zero, on its overlap with that open interval. The competing solution has no extra tube premise.
- Bounds for all `|t| ≤ 5·10⁹`, including both endpoints, all three planet indices, the exact
  `oscillatorAction (z t).2 (z t).1`, all reference-action decimals, and the interval vectors
  `[0.026,0.062]`, `[0.009,0.085]`, `[0.006,0.063]`.

`Statement.lean:104–117` uses the sup-metric closed-ball equivalence with the same decimals;
`sjsu_hG` fixes the formerly generic predicate to the explicit two eccentricity inequalities.
There is no residual arbitrary predicate in the conclusion. `chartGamma_sjsuV` uses the proved
entrywise equality with N6's matrix, preserving rows/columns and planet indices. The formula is
`|Σ_k V_jk sqrt(I_k) exp(i φ_k)|²` with phases `(φ₀,φ₁,0)`: the common phase cancels, and the
polar `sqrt(2)` cancels the oscillator-action divisor two. Thus N6's enclosure is about the
original Cartesian observable, not a modal action substituted for it.

`Shift.lean:46` identifies `sjsuB` and N6's centre by `rfl`. `Center.lean:27–85` proves its range
from the actual amplitude sum, then N6's checked Lipschitz sums. The exceptional zero mode
has `modeK 0 0 k = 0`; otherwise integrality gives `|m₁|+|m₂| ≥ 1`. This handles negative,
zero, repeated, and empty mode lists without a missing constant-mode contribution.
The bounds give
`bmin ≈ (2.6279463e-4, 6.1908603e-4, 2.3366014e-5) > ρ = 2e-6`.
Every action in the full closed tube is strictly positive. In particular, neither the static
enclosure box nor its Cartesian realization is empty or forced onto zero modes.

`Shift.lean:69–101` proves smoothness for an arbitrary finite polynomial term list and applies
it to the consumed model definition. The body matches the proposal's `Re Σ c zᵃ z̄ᵇ`,
`z = (ξ-iη)/sqrt(2)`, without altering a source coefficient or adding a Hamiltonian hypothesis.
This checks regularity of the consumed development definition, not N5a's separate data-recovery
or transformed-Hamiltonian package.

## Hypothesis review and numerical usability

| Inputs | Why they are admissible and usable |
|---|---|
| `hHh`, `hhd` | Static pullback identity on all positive actions and joint differentiability on the closed tube box. The tube's positive action margin permits the square-root Hamiltonian there. Exact charge invariance is N5a's remaining structural identity obligation. |
| `hfper`, `hfd` | Integer `2π` periodicity in both reduced angles and global differentiability of the explicit observable function. Finite Fourier–Taylor observables satisfy these even outside the action box; no global arg differentiability is requested. |
| `hη`, `hTη` | Pointwise absolute reduced bracket and a scalar time margin on a nonempty static box, with all angles quantified. The sign is `Σ_a(D_a f h_φa - f_φa D_a h)`, `D_a = ∂u_a-∂u_2`, consistent with `(İ,θ̇)=(h_θ,-h_I)`. |
| `hface`, `hc`, `hερ` | Static closeness to `ct+u_j`, centre error, and a face budget. `of_obs` proves `hc` with `γ_j=ε_j+sjsuMu`; these do not presume any confinement conclusion. |
| `hN`, `hAb`, `ha`, `hab`, `hβ`, `hμ`, `hμρ` | Explicit matrix, mode, shift derivative, and nominal-point bounds. `of_obs` supplies N5c's proved constants. The initial ball is nonempty and has positive mode lower bounds. |
| `hFu`, `hFφ`, `hLF` | Coordinate derivative bounds on the whole static box and an explicit chart Lipschitz budget. N5c supplies the scalar ceiling calculation; the actual observable derivative attachment remains visible. |
| `z₀`, `hz₀` | Exactly D76's initial state and box, not an extra source or dynamical premise. The nominal state itself satisfies the box hypothesis. |

For `hHh` there is no incompatible global regularity demand: a total tube Hamiltonian can be
evaluated using angles `(φ₀,φ₁,0)` and actions `u+B(φ)`; its differentiability is required only
where those actions are positive. Observable `hfd` concerns a finite polynomial/trigonometric
function, with no square-root or angle-branch singularity. `Fin 2.castSucc` selects modes 0 and 1,
and the reference mode in `D_a` is 2. Periodicity supports local inverse transport at arg cuts.

Fresh exact-`Fraction` calculations are in `.drafts/g2/scratch/audit/N5b-2-numerical.py` and
`N5b-2-numerical.log`. They inspect all **965,745** coefficient entries of F-v1 (165 u-slots per
observable), using `ρ=2e-6`. For each observable choose `ct` as its zero-u, zero-Fourier coefficient.
Bound `f_j-ct-u_j` by subtracting those two coefficients **before** taking the weighted absolute
sum. The two derivative sums use weights `m_l ρ^(|m|-1)` and `|k_b|ρ^|m|` respectively.
All comparisons below were exact rational comparisons; displayed numbers are rounded.

| j | Face bound `ε_j` | Slack `ρ-δ-2ε_j-μ` | Ceiling-based `chartLip*r` | `μ+Lu_j*r` |
|---|---:|---:|---:|---:|
| 0 | 3.54588394e-7 | 2.89823212e-7 | 9.03122208e-8 | 7.30562629e-8 |
| 1 | 4.23248897e-7 | 1.52502206e-7 | 1.18510287e-7 | 9.68371263e-8 |
| 2 | 1.86920550e-7 | 6.25158900e-7 | 2.39217043e-8 | 1.96649743e-8 |

All 15 literal partial sums are at most `0.95` times their respective `sjsuFuMax`/`sjsuFphiMax`
ceilings. All face slacks are strictly positive. The last two columns satisfy respectively
`≤ δ/2 = 5e-7` and `< ρ = 2e-6`; the fixed hLF choice is therefore feasible for these literals.
These checks reproduce the phase-1 worst face error about `0.423δ` and are consistent with
SR-7's Lipschitz margin; the chart bound here uses a different valid majorant from SR-7.

For the time margin, phase-1 rates `(6.71,3.06,7.42)e-20` give
`Tη ≈ (3.355,1.53,3.71)e-10`, far below `5e-7`. A common literal `η=1e-18` still gives
`Tη=5e-9`, a factor 100 below the threshold. The common literal `ε=4.5e-7` exceeds all
three freshly computed face bounds and gives `δ+2ε+1e-9=1.901e-6<2e-6`.
Both scalar examples are also included in the Lean scratch. The phase-1 bracket results
establish numerical headroom, not N7's missing kernel certificate.

## Fresh validation

Built each audited module once, sequentially, with the required serialized/capped wrapper:

| Exact command (`.drafts/g2/g2lake` prefix) | Output; exit status |
|---|---|
| `build KAM.EffectiveStability.SJSU.Confinement.Shift` | `Build completed successfully (2814 jobs).`; 0 |
| `build KAM.EffectiveStability.SJSU.Confinement.Statement` | `Build completed successfully (9125 jobs).`; 0 |
| `build KAM.EffectiveStability.Tube.Check.Center` | `Build completed successfully (1994 jobs).`; 0 |
| `build KAM.EffectiveStability.Tube.Check.Deriv` | `Build completed successfully (2788 jobs).`; 0 |

Statement replayed the existing unused-section-variable warning at `KAM/ODE/Exit.lean:36`.
There were no warnings in the audited files and no default-heartbeat failures or overrides.

Ran one scratch module:

```text
.drafts/g2/g2lake env lean .drafts/g2/scratch/audit/N5b-2-Axioms.lean
exit 0
```

Both applications with the independently copied D76 type elaborated, and both literal scalar
margin examples passed. All **18** public theorems declared in the four audited files report
exactly `[propext, Classical.choice, Quot.sound]`. In particular, this includes
`sjsu_secular_confinement_of_checks`, `sjsu_secular_confinement_of_obs`, `sjsu_hG`, all shift and
Hamiltonian smoothness lemmas, both centre-range lemmas, and the four public derivative lemmas.
Full output: `.drafts/g2/scratch/audit/N5b-2-axioms.log`. No `sorryAx` or other axiom appears.

Module headers, `module`, public imports, docstrings, public sections, exposed definitions,
and ambient Fin-function types pass inspection. A fresh code-mask scan finds no `sorry`, `admit`,
`axiom`, `unsafe`, `opaque`, any `set_option`, `EuclideanSpace`, `native_decide`, or `sorryAx`.
Line counts: Shift **105**, Statement **163**, Center **87**, Deriv **142**; maximum **163**.
There are no unexempted lines over 100 characters in these four files.

Ran `.drafts/g2/lint_noabi.sh` **once**, as required by the worker-rule replacement for
`scripts/lint_sources.sh`; `abi_hashes` was skipped. It completed with **exit 1**. Full output:
`.drafts/g2/scratch/audit/N5b-2-lint.log`. Exact terminal results include:

```text
Lean lines over 100 characters: [36 locations outside the four audited files]
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (18423 Lean files, 0 comparator configurations)
Ran 29 tests in 4.665s
OK
Ran 8 tests in 0.008s
OK
FROZEN-ANCHOR GUARD OK
```

The bracketed width count summarizes the actual list, which names SJSU/Ham, SJSU/Model data
parts, Tube/Engine, and Tube/Poly. No diagnostic names an audited file. This is not a green
repository lint: the unrelated width violations and stale generated root remain for their
owners/orchestrator. No repair or root regeneration was performed. The frozen-anchor guard
did finish successfully in this audit; no ABI-hash check was run or claimed.

`git status --short -- <package paths>` and `git diff HEAD -- <package paths>` were empty;
the four audited SHA256 values were rechecked unchanged after the builds. Only this report and
the explicitly required/permitted audit scratch artifacts were written. No package source,
handoff, generated root, frozen file, or manifest was edited; no commit/push/branch operation
was performed.

During the final lint wait, shared HEAD advanced to
`552c0c5338ed7f75202f6b2aa50afc46a50c5e13`. The intervening commit adds only the other
package's `docs/explorations/sjsu-g2-handoffs/FREEZE-PREP.md`; none of the four audited files
changed. The first-line commit and hashes remain the audited source scope.

## Evidence boundary, uncertainties, errata

The Phase-B docstrings and handoff accurately distinguish proved assembly/shift/regularity from
remaining N5a and N7 inputs. No suspected pinned-source erratum or mathematical deviation was
found; the known earlier example-interval error is avoided by using D76's corrected intervals.
The full D76 ordinary theorem remains unpaid precisely at the source identity/regularity and
literal observable/rate/face/partial attachments listed in N1. The audit does not assert joint
satisfiability already proved in Lean before those suppliers land.

Supplementary source identities: proposal draft v2 SHA256
`bb10fff984271f398baf149b964234779d126641f2f4d522b580ed8a5a9744f4`;
gates SHA256 `46192e0cfe2ed6504441cb828c8dc3f16f7b461c3ebf279bf73652531506aec1`;
Phase-B handoff SHA256 `2d11e315b5d5991f43d201eda30b52c367f6db2519f04358d74dcab68f84b52c`;
F-v1 SHA256 `40cf26e2a1f669a36cd13d86891f18620089f04c2e3a198afdb03f6670d1c825`.

READY g2-audit-n5b-2
